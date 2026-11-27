/*
 * Library book issue & reservation system  (v2, hardened)
 *
 * Build : gcc -std=c11 -Wall -Wextra -O2 -o library library.c
 * Run   : ./library            (first run asks you to create the first staff account)
 * Check : ./library --selftest (verifies the built-in SHA-256 / PBKDF2 code)
 *
 * What changed compared with v1 (see the notes in the chat for the reasoning):
 *  - Roles + sessions: anonymous / student / staff, enforced inside every action.
 *  - Per-user salted PBKDF2-HMAC-SHA256 password hashes, hidden input, lockout,
 *    forced password change for temporary passwords, idle session timeout.
 *  - No hard-coded admin password; first run creates the first staff account.
 *  - Hold lifecycle: WAITING -> READY (copy held, expires) -> collected or expired.
 *  - Due dates, fines, loan limit, renewals (blocked when others are waiting).
 *  - Audit log of every sensitive action.
 *  - One data file, written atomically (temp file + fsync + rename), versioned,
 *    checksummed, endian-independent, validated on load; refuses to start on
 *    corruption instead of overwriting.
 *  - Recovery: every staff account gets a one-time recovery code (shown once,
 *    stored only as a salted hash, rate-limited, replaced after use). Staff can
 *    also reset each other's passwords.
 *  - Dynamic arrays (no 100 book / 500 loan caps), checked allocation and I/O.
 *  - EOF-safe and overflow-safe input; no system() call; single-instance lock.
 *
 * NOTE: this is still a single-machine console program. Anyone who can read the
 * data directory or replace the binary is outside what it can defend against.
 * For real deployments move the logic behind a server and a database.
 */

#ifndef _WIN32
#define _POSIX_C_SOURCE 200809L
#else
#define _CRT_RAND_S
#define _CRT_SECURE_NO_WARNINGS
#endif

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <ctype.h>
#include <stdint.h>
#include <stdarg.h>
#include <errno.h>
#include <limits.h>
#include <time.h>

#ifdef _WIN32
#include <windows.h>
#include <direct.h>
#include <io.h>
#include <conio.h>
#include <fcntl.h>
#include <share.h>
#include <sys/stat.h>
#else
#include <unistd.h>
#include <fcntl.h>
#include <signal.h>
#include <termios.h>
#include <sys/stat.h>
#include <sys/types.h>
#endif

/* ------------------------------------------------------------------ */
/* Configuration                                                       */
/* ------------------------------------------------------------------ */
#define TITLE_LEN 100
#define AUTHOR_LEN 60
#define NAME_LEN 80
#define SECRET_MAX 72
#define SALT_LEN 16
#define HASH_LEN 32
#define PBKDF_ITER 200000u      /* raise over time; each account stores its own count */

#define MIN_STUDENT_SECRET 6
#define MIN_STAFF_SECRET 10
#define MAX_FAILED 5            /* failed logins before an account is locked */
#define MAX_GLOBAL_FAILS 10     /* failed logins before the program quits */
#define LOCK_SECONDS 300
#define SESSION_TIMEOUT 300     /* idle seconds before automatic logout */

#ifndef LOAN_SECONDS
#define LOAN_SECONDS (14L * 86400L)
#endif
#ifndef HOLD_SECONDS
#define HOLD_SECONDS (3L * 86400L)
#endif
#define MAX_LOANS_PER_STUDENT 3
#define MAX_RENEWALS 2
#define FINE_PER_DAY 2          /* currency units per overdue day */
#define MAX_COPIES 10000

#define DATA_DIR "data"
#define DATA_FILE DATA_DIR "/library.dat"
#define DATA_TMP DATA_DIR "/library.dat.tmp"
#define AUDIT_FILE DATA_DIR "/audit.log"
#define LOCK_FILE DATA_DIR "/.lock"
#define FORMAT_VERSION 3u       /* v2 files are still readable */

#define RECOVERY_CODE_LEN 20    /* 20 symbols x 5 bits = 100 bits of randomness */
#define RECOVERY_LOCK_SECONDS 900

/* ------------------------------------------------------------------ */
/* Types and global state                                              */
/* ------------------------------------------------------------------ */
typedef enum { ROLE_NONE = 0, ROLE_STUDENT, ROLE_STAFF } Role;

typedef struct Hold {
    int studentId;
    int ready;                  /* 0 = waiting in queue, 1 = copy set aside */
    time_t createdAt, readyAt, expiresAt;
    struct Hold *next;
} Hold;

typedef struct {
    int id;
    char title[TITLE_LEN];
    char author[AUTHOR_LEN];
    int total;
    int available;              /* copies free on the shelf (not loaned, not held) */
    Hold *front, *rear;         /* FIFO queue; READY holds are always a prefix */
} Book;

typedef struct {
    int studentId, bookId;
    time_t issuedAt, dueAt;
    int renewals;
} Loan;

typedef struct {
    int id;
    char name[NAME_LEN];
    uint32_t iter;
    uint8_t salt[SALT_LEN];
    uint8_t hash[HASH_LEN];
    int failed;
    time_t lockedUntil;
    int mustChange;
    /* staff recovery code (hash only; the code itself is never stored) */
    int hasRecovery;
    uint32_t recIter;
    uint8_t recSalt[SALT_LEN];
    uint8_t recHash[HASH_LEN];
    int recFailed;
    time_t recLockedUntil;
} Account;

static Book *books;      static size_t nBooks, capBooks;
static Loan *loans;      static size_t nLoans, capLoans;
static Account *students; static size_t nStudents, capStudents;
static Account *staff;   static size_t nStaff, capStaff;

static Role role = ROLE_NONE;
static int userId = 0;
static time_t lastActive = 0;
static int globalFails = 0;

static time_t now(void) { return time(NULL); }

static void copyStr(char *dst, size_t size, const char *src) {
    size_t l = strlen(src);
    if (l >= size) l = size - 1;
    memcpy(dst, src, l);
    dst[l] = '\0';
}

static void secureZero(void *p, size_t n) {
    volatile uint8_t *v = (volatile uint8_t *)p;
    while (n--) *v++ = 0;
}

static int ctEqual(const uint8_t *a, const uint8_t *b, size_t n) {
    uint8_t d = 0;
    for (size_t i = 0; i < n; i++) d |= (uint8_t)(a[i] ^ b[i]);
    return d == 0;
}

/* ------------------------------------------------------------------ */
/* SHA-256, HMAC, PBKDF2 (self-contained; libsodium/Argon2id is better */
/* if you can add a dependency)                                        */
/* ------------------------------------------------------------------ */
typedef struct { uint32_t h[8]; uint64_t len; uint8_t buf[64]; size_t n; } Sha;

static const uint32_t K256[64] = {
    0x428a2f98,0x71374491,0xb5c0fbcf,0xe9b5dba5,0x3956c25b,0x59f111f1,0x923f82a4,0xab1c5ed5,
    0xd807aa98,0x12835b01,0x243185be,0x550c7dc3,0x72be5d74,0x80deb1fe,0x9bdc06a7,0xc19bf174,
    0xe49b69c1,0xefbe4786,0x0fc19dc6,0x240ca1cc,0x2de92c6f,0x4a7484aa,0x5cb0a9dc,0x76f988da,
    0x983e5152,0xa831c66d,0xb00327c8,0xbf597fc7,0xc6e00bf3,0xd5a79147,0x06ca6351,0x14292967,
    0x27b70a85,0x2e1b2138,0x4d2c6dfc,0x53380d13,0x650a7354,0x766a0abb,0x81c2c92e,0x92722c85,
    0xa2bfe8a1,0xa81a664b,0xc24b8b70,0xc76c51a3,0xd192e819,0xd6990624,0xf40e3585,0x106aa070,
    0x19a4c116,0x1e376c08,0x2748774c,0x34b0bcb5,0x391c0cb3,0x4ed8aa4a,0x5b9cca4f,0x682e6ff3,
    0x748f82ee,0x78a5636f,0x84c87814,0x8cc70208,0x90befffa,0xa4506ceb,0xbef9a3f7,0xc67178f2
};

#define ROR(x, n) (((x) >> (n)) | ((x) << (32 - (n))))

static void shaBlock(uint32_t h[8], const uint8_t b[64]) {
    uint32_t w[64], v[8];
    for (int i = 0; i < 16; i++)
        w[i] = ((uint32_t)b[4*i] << 24) | ((uint32_t)b[4*i+1] << 16) |
               ((uint32_t)b[4*i+2] << 8) | (uint32_t)b[4*i+3];
    for (int i = 16; i < 64; i++) {
        uint32_t s0 = ROR(w[i-15], 7) ^ ROR(w[i-15], 18) ^ (w[i-15] >> 3);
        uint32_t s1 = ROR(w[i-2], 17) ^ ROR(w[i-2], 19) ^ (w[i-2] >> 10);
        w[i] = w[i-16] + s0 + w[i-7] + s1;
    }
    memcpy(v, h, sizeof v);
    for (int i = 0; i < 64; i++) {
        uint32_t S1 = ROR(v[4], 6) ^ ROR(v[4], 11) ^ ROR(v[4], 25);
        uint32_t ch = (v[4] & v[5]) ^ (~v[4] & v[6]);
        uint32_t t1 = v[7] + S1 + ch + K256[i] + w[i];
        uint32_t S0 = ROR(v[0], 2) ^ ROR(v[0], 13) ^ ROR(v[0], 22);
        uint32_t mj = (v[0] & v[1]) ^ (v[0] & v[2]) ^ (v[1] & v[2]);
        uint32_t t2 = S0 + mj;
        v[7] = v[6]; v[6] = v[5]; v[5] = v[4]; v[4] = v[3] + t1;
        v[3] = v[2]; v[2] = v[1]; v[1] = v[0]; v[0] = t1 + t2;
    }
    for (int i = 0; i < 8; i++) h[i] += v[i];
}

static void shaInit(Sha *s) {
    static const uint32_t iv[8] = {0x6a09e667,0xbb67ae85,0x3c6ef372,0xa54ff53a,
                                   0x510e527f,0x9b05688c,0x1f83d9ab,0x5be0cd19};
    memcpy(s->h, iv, sizeof iv);
    s->len = 0;
    s->n = 0;
}

static void shaUpdate(Sha *s, const void *data, size_t len) {
    const uint8_t *p = (const uint8_t *)data;
    s->len += len;
    while (len) {
        size_t c = 64 - s->n;
        if (c > len) c = len;
        memcpy(s->buf + s->n, p, c);
        s->n += c; p += c; len -= c;
        if (s->n == 64) { shaBlock(s->h, s->buf); s->n = 0; }
    }
}

static void shaFinal(Sha *s, uint8_t out[32]) {
    uint64_t bits = s->len * 8;
    uint8_t pad = 0x80, zero = 0, lb[8];
    shaUpdate(s, &pad, 1);
    while (s->n != 56) shaUpdate(s, &zero, 1);
    for (int i = 0; i < 8; i++) lb[i] = (uint8_t)(bits >> (56 - 8 * i));
    shaUpdate(s, lb, 8);
    for (int i = 0; i < 8; i++) {
        out[4*i]   = (uint8_t)(s->h[i] >> 24);
        out[4*i+1] = (uint8_t)(s->h[i] >> 16);
        out[4*i+2] = (uint8_t)(s->h[i] >> 8);
        out[4*i+3] = (uint8_t)(s->h[i]);
    }
}

static void hmacSha256(const uint8_t *key, size_t klen, const uint8_t *msg, size_t mlen, uint8_t out[32]) {
    uint8_t k[64], pad[64], inner[32];
    Sha s;
    memset(k, 0, sizeof k);
    if (klen > 64) { shaInit(&s); shaUpdate(&s, key, klen); shaFinal(&s, k); }
    else if (klen) memcpy(k, key, klen);
    for (int i = 0; i < 64; i++) pad[i] = k[i] ^ 0x36;
    shaInit(&s); shaUpdate(&s, pad, 64); shaUpdate(&s, msg, mlen); shaFinal(&s, inner);
    for (int i = 0; i < 64; i++) pad[i] = k[i] ^ 0x5c;
    shaInit(&s); shaUpdate(&s, pad, 64); shaUpdate(&s, inner, 32); shaFinal(&s, out);
    secureZero(k, sizeof k);
}

/* PBKDF2-HMAC-SHA256, single 32-byte output block. */
static void pbkdf2(const char *pw, const uint8_t *salt, size_t saltLen, uint32_t iter, uint8_t out[HASH_LEN]) {
    uint8_t msg[SALT_LEN + 4], u[32], t[32];
    size_t pl = strlen(pw);
    if (saltLen > SALT_LEN) saltLen = SALT_LEN;
    memcpy(msg, salt, saltLen);
    msg[saltLen] = 0; msg[saltLen+1] = 0; msg[saltLen+2] = 0; msg[saltLen+3] = 1;
    hmacSha256((const uint8_t *)pw, pl, msg, saltLen + 4, u);
    memcpy(t, u, 32);
    for (uint32_t i = 1; i < iter; i++) {
        hmacSha256((const uint8_t *)pw, pl, u, 32, u);
        for (int j = 0; j < 32; j++) t[j] ^= u[j];
    }
    memcpy(out, t, 32);
    secureZero(u, sizeof u);
    secureZero(t, sizeof t);
}

static int randomBytes(void *buf, size_t n) {
#ifdef _WIN32
    uint8_t *p = (uint8_t *)buf;
    for (size_t i = 0; i < n; i += sizeof(unsigned int)) {
        unsigned int v;
        size_t c = n - i < sizeof v ? n - i : sizeof v;
        if (rand_s(&v) != 0) return 0;
        memcpy(p + i, &v, c);
    }
    return 1;
#else
    FILE *f = fopen("/dev/urandom", "rb");
    size_t got;
    if (!f) return 0;
    got = fread(buf, 1, n, f);
    fclose(f);
    return got == n;
#endif
}

static void toHex(const uint8_t *d, size_t n, char *out) {
    static const char *hx = "0123456789abcdef";
    for (size_t i = 0; i < n; i++) { out[2*i] = hx[d[i] >> 4]; out[2*i+1] = hx[d[i] & 15]; }
    out[2*n] = '\0';
}

static int selfTest(void) {
    uint8_t d[32];
    char hex[65];
    Sha s;
    int bad = 0;
    shaInit(&s); shaUpdate(&s, "abc", 3); shaFinal(&s, d); toHex(d, 32, hex);
    if (strcmp(hex, "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad")) { puts("SHA-256 FAILED"); bad = 1; }
    pbkdf2("password", (const uint8_t *)"salt", 4, 1, d); toHex(d, 32, hex);
    if (strcmp(hex, "120fb6cffcf8b32c43e7225256c4f837a86548c92ccc35480805987cb70be17b")) { puts("PBKDF2 c=1 FAILED"); bad = 1; }
    pbkdf2("password", (const uint8_t *)"salt", 4, 2, d); toHex(d, 32, hex);
    if (strcmp(hex, "ae4d0c95af6b46d32d0adff928f06dd02a303f8ef3c251dfd6e2d85a95474c43")) { puts("PBKDF2 c=2 FAILED"); bad = 1; }
    puts(bad ? "Self-test FAILED" : "Self-test passed");
    return bad;
}

/* ------------------------------------------------------------------ */
/* Input helpers: EOF-safe, overflow-safe, hidden password entry       */
/* ------------------------------------------------------------------ */
#ifndef _WIN32
static struct termios savedTerm;
static volatile sig_atomic_t echoOff = 0;
static void onSigint(int sig) {
    (void)sig;
    if (echoOff) tcsetattr(STDIN_FILENO, TCSANOW, &savedTerm);
    _exit(130);
}
#endif

/* Returns 0 on EOF. Discards the rest of an over-long line so it cannot
 * leak into the next prompt. An over-long line yields an empty string. */
static int readRaw(char *buf, size_t size) {
    size_t len;
    if (!fgets(buf, (int)size, stdin)) { buf[0] = '\0'; return 0; }
    len = strlen(buf);
    if (len > 0 && buf[len - 1] == '\n') {
        buf[--len] = '\0';
        if (len > 0 && buf[len - 1] == '\r') buf[--len] = '\0';
    } else {
        int c, overflow = 0;
        while ((c = getchar()) != '\n' && c != EOF) overflow = 1;
        if (overflow) { printf("Input too long.\n"); buf[0] = '\0'; }
    }
    return 1;
}

static void quitOnEof(void) {
    printf("\nInput closed. Exiting.\n");
    exit(0);
}

static void readLine(const char *prompt, char *buf, size_t size) {
    printf("%s", prompt);
    fflush(stdout);
    if (!readRaw(buf, size)) quitOnEof();
}

static void readSecret(const char *prompt, char *buf, size_t size) {
    int ok;
    printf("%s", prompt);
    fflush(stdout);
#ifdef _WIN32
    if (_isatty(_fileno(stdin))) {
        size_t i = 0;
        int c;
        while ((c = _getch()) != '\r' && c != '\n') {
            if (c == 3) exit(130);
            if (c == '\b') { if (i) i--; continue; }
            if (i + 1 < size) buf[i++] = (char)c;
        }
        buf[i] = '\0';
        printf("\n");
        return;
    }
    ok = readRaw(buf, size);
#else
    {
        struct termios nw;
        int tty = isatty(STDIN_FILENO) && tcgetattr(STDIN_FILENO, &savedTerm) == 0;
        if (tty) {
            nw = savedTerm;
            nw.c_lflag &= ~(tcflag_t)ECHO;
            echoOff = 1;
            tcsetattr(STDIN_FILENO, TCSANOW, &nw);
        }
        ok = readRaw(buf, size);
        if (tty) { tcsetattr(STDIN_FILENO, TCSANOW, &savedTerm); echoOff = 0; printf("\n"); }
    }
#endif
    if (!ok) quitOnEof();
}

static int readInt(const char *prompt) {
    char line[64];
    for (;;) {
        char *end;
        long v;
        readLine(prompt, line, sizeof line);
        errno = 0;
        v = strtol(line, &end, 10);
        if (line[0] != '\0' && end != line) {
            while (isspace((unsigned char)*end)) end++;
            if (*end == '\0' && errno == 0 && v >= 0 && v <= INT_MAX) return (int)v;
        }
        printf("Invalid input. Please enter a non-negative whole number.\n");
    }
}

/* Non-empty, printable text only (also prevents log injection). */
static int readText(const char *prompt, char *buf, size_t size) {
    readLine(prompt, buf, size);
    if (buf[0] == '\0') { printf("This field cannot be empty.\n"); return 0; }
    for (const unsigned char *p = (const unsigned char *)buf; *p; p++)
        if (*p < 32 || *p == 127) { printf("Control characters are not allowed.\n"); return 0; }
    return 1;
}

static int containsCI(const char *hay, const char *needle) {
    size_t n = strlen(needle);
    if (n == 0) return 1;
    for (; *hay; hay++) {
        size_t i = 0;
        while (i < n && hay[i] && tolower((unsigned char)hay[i]) == tolower((unsigned char)needle[i])) i++;
        if (i == n) return 1;
    }
    return 0;
}

static const char *fmtDate(time_t t, char *buf, size_t n) {
    struct tm *tmv = localtime(&t);
    if (!tmv || !strftime(buf, n, "%Y-%m-%d", tmv)) copyStr(buf, n, "?");
    return buf;
}

/* ------------------------------------------------------------------ */
/* Data access helpers                                                 */
/* ------------------------------------------------------------------ */
static int growArray(void *arrp, size_t *cap, size_t elem) {
    void **pp = (void **)arrp;
    size_t nc = *cap ? *cap * 2 : 16;
    void *t = realloc(*pp, nc * elem);
    if (!t) return 0;
    *pp = t;
    *cap = nc;
    return 1;
}

static Book *pushBook(void) {
    Book *b;
    if (nBooks == capBooks && !growArray(&books, &capBooks, sizeof *books)) return NULL;
    b = &books[nBooks++];
    memset(b, 0, sizeof *b);
    return b;
}

static Loan *pushLoan(void) {
    Loan *l;
    if (nLoans == capLoans && !growArray(&loans, &capLoans, sizeof *loans)) return NULL;
    l = &loans[nLoans++];
    memset(l, 0, sizeof *l);
    return l;
}

static Account *pushAccount(Account **arr, size_t *n, size_t *cap) {
    Account *a;
    if (*n == *cap && !growArray(arr, cap, sizeof **arr)) return NULL;
    a = &(*arr)[(*n)++];
    memset(a, 0, sizeof *a);
    return a;
}

static Book *findBook(int id) {
    for (size_t i = 0; i < nBooks; i++) if (books[i].id == id) return &books[i];
    return NULL;
}

static Account *findAccount(Account *arr, size_t n, int id) {
    for (size_t i = 0; i < n; i++) if (arr[i].id == id) return &arr[i];
    return NULL;
}

static Account *findStudent(int id) { return findAccount(students, nStudents, id); }

static int findLoanIndex(int sid, int bid) {
    for (size_t i = 0; i < nLoans; i++)
        if (loans[i].studentId == sid && loans[i].bookId == bid) return (int)i;
    return -1;
}

static int countStudentLoans(int sid) {
    int c = 0;
    for (size_t i = 0; i < nLoans; i++) if (loans[i].studentId == sid) c++;
    return c;
}

static int countBookLoans(int bid) {
    int c = 0;
    for (size_t i = 0; i < nLoans; i++) if (loans[i].bookId == bid) c++;
    return c;
}

static Hold *findHold(const Book *b, int sid) {
    for (Hold *p = b->front; p; p = p->next) if (p->studentId == sid) return p;
    return NULL;
}

static int countWaiting(const Book *b) {
    int c = 0;
    for (const Hold *p = b->front; p; p = p->next) if (!p->ready) c++;
    return c;
}

static int countReady(const Book *b) {
    int c = 0;
    for (const Hold *p = b->front; p; p = p->next) if (p->ready) c++;
    return c;
}

static Hold *enqueueHold(Book *b, int sid, int ready, time_t created, time_t readyAt, time_t expires) {
    Hold *h = (Hold *)calloc(1, sizeof *h);
    if (!h) return NULL;
    h->studentId = sid; h->ready = ready;
    h->createdAt = created; h->readyAt = readyAt; h->expiresAt = expires;
    if (!b->rear) b->front = b->rear = h;
    else { b->rear->next = h; b->rear = h; }
    return h;
}

static void removeHold(Book *b, int sid) {
    Hold *cur = b->front, *prev = NULL;
    while (cur) {
        if (cur->studentId == sid) {
            if (prev) prev->next = cur->next; else b->front = cur->next;
            if (b->rear == cur) b->rear = prev;
            free(cur);
            return;
        }
        prev = cur;
        cur = cur->next;
    }
}

static void clearQueue(Book *b) {
    while (b->front) { Hold *t = b->front; b->front = t->next; free(t); }
    b->rear = NULL;
}

static void freeAll(void) {
    for (size_t i = 0; i < nBooks; i++) clearQueue(&books[i]);
    free(books); free(loans); free(students); free(staff);
    books = NULL; loans = NULL; students = NULL; staff = NULL;
}

static int nextId(const Account *arr, size_t n, int base) {
    int id = base;
    for (size_t i = 0; i < n; i++) if (arr[i].id >= id) id = arr[i].id + 1;
    return id;
}

/* ------------------------------------------------------------------ */
/* Audit log                                                           */
/* ------------------------------------------------------------------ */
static void audit(const char *action, const char *fmt, ...) {
    static int warned = 0;
    FILE *f = fopen(AUDIT_FILE, "a");
    char ts[32], actor[32];
    time_t t = now();
    struct tm *tmv = localtime(&t);
    va_list ap;
    if (!f) {
        if (!warned) { warned = 1; printf("WARNING: cannot write the audit log.\n"); }
        return;
    }
    if (!tmv || !strftime(ts, sizeof ts, "%Y-%m-%dT%H:%M:%S", tmv)) copyStr(ts, sizeof ts, "?");
    if (role == ROLE_STAFF) snprintf(actor, sizeof actor, "staff:%d", userId);
    else if (role == ROLE_STUDENT) snprintf(actor, sizeof actor, "student:%d", userId);
    else copyStr(actor, sizeof actor, "anon");
    fprintf(f, "%s | %s | %s | ", ts, actor, action);
    va_start(ap, fmt);
    vfprintf(f, fmt, ap);
    va_end(ap);
    fputc('\n', f);
    fclose(f);
}

/* ------------------------------------------------------------------ */
/* Persistence: one file, serialised field by field, checksummed       */
/* ------------------------------------------------------------------ */
typedef struct { uint8_t *d; size_t n, cap; int err; } Buf;

static void bPut(Buf *b, const void *p, size_t n) {
    if (b->err) return;
    if (b->n + n > b->cap) {
        size_t nc = b->cap ? b->cap : 4096;
        uint8_t *t;
        while (nc < b->n + n) nc *= 2;
        t = (uint8_t *)realloc(b->d, nc);
        if (!t) { b->err = 1; return; }
        b->d = t; b->cap = nc;
    }
    memcpy(b->d + b->n, p, n);
    b->n += n;
}
static void bU32(Buf *b, uint32_t v) {
    uint8_t t[4] = {(uint8_t)v, (uint8_t)(v >> 8), (uint8_t)(v >> 16), (uint8_t)(v >> 24)};
    bPut(b, t, 4);
}
static void bU64(Buf *b, uint64_t v) {
    uint8_t t[8];
    for (int i = 0; i < 8; i++) t[i] = (uint8_t)(v >> (8 * i));
    bPut(b, t, 8);
}
static void bFixed(Buf *b, const char *s, size_t fixed) {
    uint8_t t[128];
    size_t l = strlen(s);
    memset(t, 0, sizeof t);
    if (l >= fixed) l = fixed - 1;
    memcpy(t, s, l);
    bPut(b, t, fixed);
}

typedef struct { const uint8_t *d; size_t n, pos; int err; } Rd;

static void rGet(Rd *r, void *out, size_t n) {
    if (r->err || r->n - r->pos < n) { r->err = 1; memset(out, 0, n); return; }
    memcpy(out, r->d + r->pos, n);
    r->pos += n;
}
static uint32_t rU32(Rd *r) {
    uint8_t t[4];
    rGet(r, t, 4);
    return (uint32_t)t[0] | ((uint32_t)t[1] << 8) | ((uint32_t)t[2] << 16) | ((uint32_t)t[3] << 24);
}
static uint64_t rU64(Rd *r) {
    uint8_t t[8];
    uint64_t v = 0;
    rGet(r, t, 8);
    for (int i = 0; i < 8; i++) v |= (uint64_t)t[i] << (8 * i);
    return v;
}
static void rFixed(Rd *r, char *dst, size_t fixed) {
    rGet(r, dst, fixed);
    dst[fixed - 1] = '\0';
}

static void writeAccount(Buf *b, const Account *a) {
    bU32(b, (uint32_t)a->id);
    bFixed(b, a->name, NAME_LEN);
    bU32(b, a->iter);
    bPut(b, a->salt, SALT_LEN);
    bPut(b, a->hash, HASH_LEN);
    bU32(b, (uint32_t)a->failed);
    bU64(b, (uint64_t)a->lockedUntil);
    bU32(b, (uint32_t)a->mustChange);
    bU32(b, (uint32_t)a->hasRecovery);
    bU32(b, a->recIter);
    bPut(b, a->recSalt, SALT_LEN);
    bPut(b, a->recHash, HASH_LEN);
    bU32(b, (uint32_t)a->recFailed);
    bU64(b, (uint64_t)a->recLockedUntil);
}

static void readAccount(Rd *r, Account *a, uint32_t ver) {
    a->id = (int)rU32(r);
    rFixed(r, a->name, NAME_LEN);
    a->iter = rU32(r);
    rGet(r, a->salt, SALT_LEN);
    rGet(r, a->hash, HASH_LEN);
    a->failed = (int)rU32(r);
    a->lockedUntil = (time_t)(int64_t)rU64(r);
    a->mustChange = (int)rU32(r);
    if (ver >= 3) {
        a->hasRecovery = (int)rU32(r);
        a->recIter = rU32(r);
        rGet(r, a->recSalt, SALT_LEN);
        rGet(r, a->recHash, HASH_LEN);
        a->recFailed = (int)rU32(r);
        a->recLockedUntil = (time_t)(int64_t)rU64(r);
    }
}

static int fsyncFile(FILE *f) {
#ifdef _WIN32
    return _commit(_fileno(f));
#else
    return fsync(fileno(f));
#endif
}

static int replaceFile(const char *from, const char *to) {
#ifdef _WIN32
    return MoveFileExA(from, to, MOVEFILE_REPLACE_EXISTING | MOVEFILE_WRITE_THROUGH) != 0;
#else
    int dfd;
    if (rename(from, to) != 0) return 0;
    dfd = open(DATA_DIR, O_RDONLY);
    if (dfd >= 0) { fsync(dfd); close(dfd); }
    return 1;
#endif
}

static int writeFileAtomic(const uint8_t *d, size_t n) {
    FILE *f;
    int ok;
#ifdef _WIN32
    f = fopen(DATA_TMP, "wb");
#else
    int fd = open(DATA_TMP, O_WRONLY | O_CREAT | O_TRUNC, 0600);
    if (fd < 0) return 0;
    f = fdopen(fd, "wb");
    if (!f) { close(fd); return 0; }
#endif
    if (!f) return 0;
    ok = fwrite(d, 1, n, f) == n && fflush(f) == 0 && fsyncFile(f) == 0;
    if (fclose(f) != 0) ok = 0;
    if (!ok || !replaceFile(DATA_TMP, DATA_FILE)) { remove(DATA_TMP); return 0; }
    return 1;
}

static int saveAll(void) {
    Buf b;
    uint8_t digest[32];
    Sha s;
    uint32_t nHolds = 0;
    int ok;
    memset(&b, 0, sizeof b);
    for (size_t i = 0; i < nBooks; i++)
        for (Hold *h = books[i].front; h; h = h->next) nHolds++;

    bPut(&b, "LIBR", 4);
    bU32(&b, FORMAT_VERSION);
    bU32(&b, (uint32_t)nBooks);
    bU32(&b, (uint32_t)nStudents);
    bU32(&b, (uint32_t)nStaff);
    bU32(&b, (uint32_t)nLoans);
    bU32(&b, nHolds);
    for (size_t i = 0; i < nStudents; i++) writeAccount(&b, &students[i]);
    for (size_t i = 0; i < nStaff; i++) writeAccount(&b, &staff[i]);
    for (size_t i = 0; i < nBooks; i++) {
        bU32(&b, (uint32_t)books[i].id);
        bFixed(&b, books[i].title, TITLE_LEN);
        bFixed(&b, books[i].author, AUTHOR_LEN);
        bU32(&b, (uint32_t)books[i].total);
        bU32(&b, (uint32_t)books[i].available);
    }
    for (size_t i = 0; i < nLoans; i++) {
        bU32(&b, (uint32_t)loans[i].studentId);
        bU32(&b, (uint32_t)loans[i].bookId);
        bU64(&b, (uint64_t)loans[i].issuedAt);
        bU64(&b, (uint64_t)loans[i].dueAt);
        bU32(&b, (uint32_t)loans[i].renewals);
    }
    for (size_t i = 0; i < nBooks; i++)
        for (Hold *h = books[i].front; h; h = h->next) {
            bU32(&b, (uint32_t)books[i].id);
            bU32(&b, (uint32_t)h->studentId);
            bU32(&b, (uint32_t)h->ready);
            bU64(&b, (uint64_t)h->createdAt);
            bU64(&b, (uint64_t)h->readyAt);
            bU64(&b, (uint64_t)h->expiresAt);
        }
    if (b.err) { free(b.d); return 0; }
    shaInit(&s); shaUpdate(&s, b.d, b.n); shaFinal(&s, digest);
    bPut(&b, digest, 32);
    ok = !b.err && writeFileAtomic(b.d, b.n);
    free(b.d);
    return ok;
}

static void commit(void) {
    if (!saveAll()) printf("WARNING: could not save data to disk! Do not close the program until this is fixed.\n");
}

static int validateLoaded(void) {
    for (size_t i = 0; i < nBooks; i++) {
        Book *b = &books[i];
        int loansN = countBookLoans(b->id), ready = countReady(b), waiting = countWaiting(b);
        if (b->id <= 0 || b->total <= 0 || b->available < 0 || findBook(b->id) != b) {
            printf("Data error: invalid or duplicate book %d.\n", b->id); return 0;
        }
        if (b->available + loansN + ready != b->total) {
            printf("Data error: copy counts do not add up for book %d.\n", b->id); return 0;
        }
        if (b->available > 0 && waiting > 0) {
            printf("Data error: book %d has free copies but a waiting list.\n", b->id); return 0;
        }
    }
    for (size_t i = 0; i < nStudents; i++)
        if (students[i].id <= 0 || findStudent(students[i].id) != &students[i]) {
            printf("Data error: invalid or duplicate student id.\n"); return 0;
        }
    for (size_t i = 0; i < nStaff; i++)
        if (staff[i].id <= 0 || findAccount(staff, nStaff, staff[i].id) != &staff[i]) {
            printf("Data error: invalid or duplicate staff id.\n"); return 0;
        }
    for (size_t i = 0; i < nLoans; i++) {
        Book *b = findBook(loans[i].bookId);
        if (!b || !findStudent(loans[i].studentId) ||
            findLoanIndex(loans[i].studentId, loans[i].bookId) != (int)i || findHold(b, loans[i].studentId)) {
            printf("Data error: loan %zu is inconsistent.\n", i); return 0;
        }
    }
    return 1;
}

static int loadAll(void) {
    FILE *f = fopen(DATA_FILE, "rb");
    uint8_t *d = NULL, digest[32];
    long sz;
    Rd r;
    Sha s;
    char magic[4];
    uint32_t nb, ns, nst, nl, nh, ver;
    int ok = 0;

    if (!f) {
        if (errno == ENOENT) return 1;          /* fresh start */
        perror("Cannot open data file");
        return 0;
    }
    if (fseek(f, 0, SEEK_END) != 0 || (sz = ftell(f)) < 0 || sz > (256L << 20) || fseek(f, 0, SEEK_SET) != 0) {
        fclose(f); printf("Data error: cannot determine file size.\n"); return 0;
    }
    d = (uint8_t *)malloc((size_t)sz + 1);
    if (!d || fread(d, 1, (size_t)sz, f) != (size_t)sz) {
        printf("Data error: cannot read data file.\n"); free(d); fclose(f); return 0;
    }
    fclose(f);
    if (sz < 64) { printf("Data error: file too short.\n"); free(d); return 0; }
    shaInit(&s); shaUpdate(&s, d, (size_t)sz - 32); shaFinal(&s, digest);
    if (!ctEqual(digest, d + sz - 32, 32)) { printf("Data error: checksum mismatch (file damaged or edited).\n"); free(d); return 0; }

    r.d = d; r.n = (size_t)sz - 32; r.pos = 0; r.err = 0;
    rGet(&r, magic, 4);
    ver = rU32(&r);
    if (memcmp(magic, "LIBR", 4) != 0 || (ver != 2 && ver != 3)) { printf("Data error: unknown file format.\n"); free(d); return 0; }
    nb = rU32(&r); ns = rU32(&r); nst = rU32(&r); nl = rU32(&r); nh = rU32(&r);

    for (uint32_t i = 0; i < ns && !r.err; i++) {
        Account *a = pushAccount(&students, &nStudents, &capStudents);
        if (!a) { r.err = 1; break; }
        readAccount(&r, a, ver);
    }
    for (uint32_t i = 0; i < nst && !r.err; i++) {
        Account *a = pushAccount(&staff, &nStaff, &capStaff);
        if (!a) { r.err = 1; break; }
        readAccount(&r, a, ver);
    }
    for (uint32_t i = 0; i < nb && !r.err; i++) {
        Book *b = pushBook();
        if (!b) { r.err = 1; break; }
        b->id = (int)rU32(&r);
        rFixed(&r, b->title, TITLE_LEN);
        rFixed(&r, b->author, AUTHOR_LEN);
        b->total = (int)rU32(&r);
        b->available = (int)rU32(&r);
    }
    for (uint32_t i = 0; i < nl && !r.err; i++) {
        Loan *l = pushLoan();
        if (!l) { r.err = 1; break; }
        l->studentId = (int)rU32(&r);
        l->bookId = (int)rU32(&r);
        l->issuedAt = (time_t)(int64_t)rU64(&r);
        l->dueAt = (time_t)(int64_t)rU64(&r);
        l->renewals = (int)rU32(&r);
    }
    for (uint32_t i = 0; i < nh && !r.err; i++) {
        int bid = (int)rU32(&r), sid = (int)rU32(&r), ready = (int)rU32(&r);
        time_t c = (time_t)(int64_t)rU64(&r), ra = (time_t)(int64_t)rU64(&r), ex = (time_t)(int64_t)rU64(&r);
        Book *b = r.err ? NULL : findBook(bid);
        if (!b || !findStudent(sid) || findHold(b, sid) || (ready != 0 && ready != 1) ||
            !enqueueHold(b, sid, ready, c, ra, ex)) r.err = 1;
    }
    if (r.err || r.pos != r.n) printf("Data error: file is truncated, malformed or has trailing data.\n");
    else ok = validateLoaded();
    free(d);
    return ok;
}

/* ------------------------------------------------------------------ */
/* Credentials and sessions                                            */
/* ------------------------------------------------------------------ */
static int setSecret(Account *a, const char *secret) {
    if (!randomBytes(a->salt, SALT_LEN)) return 0;
    a->iter = PBKDF_ITER;
    pbkdf2(secret, a->salt, SALT_LEN, a->iter, a->hash);
    return 1;
}

static int verifySecret(const Account *a, const char *secret) {
    uint8_t h[HASH_LEN];
    int ok;
    pbkdf2(secret, a->salt, SALT_LEN, a->iter ? a->iter : PBKDF_ITER, h);
    ok = ctEqual(h, a->hash, HASH_LEN);
    secureZero(h, sizeof h);
    return ok;
}

static int promptNewSecret(char *out, size_t size, size_t minLen, const char *label) {
    char again[SECRET_MAX];
    readSecret(label, out, size);
    if (strlen(out) < minLen) {
        printf("Must be at least %zu characters.\n", minLen);
        secureZero(out, size);
        return 0;
    }
    readSecret("Repeat: ", again, sizeof again);
    if (strcmp(out, again) != 0) {
        printf("Entries do not match.\n");
        secureZero(out, size);
        secureZero(again, sizeof again);
        return 0;
    }
    secureZero(again, sizeof again);
    return 1;
}

static int createAccountWithSecret(Account **arr, size_t *n, size_t *cap, int base,
                                   const char *name, const char *secret, int mustChange) {
    int id = nextId(*arr, *n, base);
    Account *a = pushAccount(arr, n, cap);
    if (!a) { printf("Out of memory.\n"); return 0; }
    a->id = id;
    copyStr(a->name, sizeof a->name, name);
    a->mustChange = mustChange;
    if (!setSecret(a, secret)) {
        (*n)--;
        printf("Could not obtain secure random data.\n");
        return 0;
    }
    return id;
}

static int createAccount(Account **arr, size_t *n, size_t *cap, int base, const char *name,
                         const char *label, size_t minLen, int mustChange) {
    char s[SECRET_MAX];
    int id;
    if (!promptNewSecret(s, sizeof s, minLen, label)) return 0;
    id = createAccountWithSecret(arr, n, cap, base, name, s, mustChange);
    secureZero(s, sizeof s);
    return id;
}

static void forceChange(Account *a, size_t minLen) {
    char s[SECRET_MAX];
    printf("You must choose a new password before continuing.\n");
    for (;;) {
        if (!promptNewSecret(s, sizeof s, minLen, "New password: ")) continue;
        if (verifySecret(a, s)) { printf("The new password must differ from the old one.\n"); secureZero(s, sizeof s); continue; }
        if (setSecret(a, s)) break;
        printf("Could not obtain secure random data.\n");
        secureZero(s, sizeof s);
    }
    secureZero(s, sizeof s);
    a->mustChange = 0;
    commit();
    audit("PASSWORD_CHANGED", "forced");
}

/* ---- Recovery codes ------------------------------------------------ */

/* Make a fresh recovery code for a staff account, store only its hash,
 * save, and show the code exactly once. Any previous code stops working. */
static void issueRecoveryCode(Account *a) {
    static const char alpha[] = "ABCDEFGHJKLMNPQRSTUVWXYZ23456789";   /* 32 symbols, no I/O/0/1 */
    uint8_t rnd[RECOVERY_CODE_LEN], salt[SALT_LEN];
    char code[RECOVERY_CODE_LEN + 1], tmp[8];
    if (!randomBytes(rnd, sizeof rnd) || !randomBytes(salt, sizeof salt)) {
        printf("Could not obtain secure random data; no recovery code was created.\n");
        return;
    }
    for (int i = 0; i < RECOVERY_CODE_LEN; i++) code[i] = alpha[rnd[i] & 31];   /* 256 % 32 == 0: unbiased */
    code[RECOVERY_CODE_LEN] = '\0';
    memcpy(a->recSalt, salt, SALT_LEN);
    a->recIter = PBKDF_ITER;
    pbkdf2(code, a->recSalt, SALT_LEN, a->recIter, a->recHash);
    a->hasRecovery = 1;
    a->recFailed = 0;
    a->recLockedUntil = 0;
    commit();                                   /* save BEFORE showing, so the code is valid */
    audit("RECOVERY_CODE_ISSUED", "staff=%d", a->id);
    printf("\n*** RECOVERY CODE for staff ID %d (shown only once) ***\n    ", a->id);
    for (int i = 0; i < RECOVERY_CODE_LEN; i++) {
        putchar(code[i]);
        if (i % 5 == 4 && i < RECOVERY_CODE_LEN - 1) putchar('-');
    }
    printf("\nWrite it down and keep it offline (not on this computer). It resets your password\n"
           "once; after use a new code is issued and this one stops working.\n");
    secureZero(rnd, sizeof rnd);
    secureZero(code, sizeof code);
    readLine("Press Enter once you have stored it: ", tmp, sizeof tmp);
}

/* Upper-case, drop dashes/spaces, require exactly RECOVERY_CODE_LEN symbols. */
static int normalizeCode(const char *in, char *out) {
    size_t n = 0;
    for (; *in; in++) {
        if (*in == '-' || isspace((unsigned char)*in)) continue;
        if (n >= RECOVERY_CODE_LEN) return 0;
        out[n++] = (char)toupper((unsigned char)*in);
    }
    out[n] = '\0';
    return n == RECOVERY_CODE_LEN;
}

static void recoverStaffPassword(void) {
    static const uint8_t dummySalt[SALT_LEN] = {0};
    char raw[SECRET_MAX], code[RECOVERY_CODE_LEN + 1], s[SECRET_MAX];
    uint8_t h[HASH_LEN];
    Account *a;
    time_t t = now();
    int id, ok, usable;

    if (globalFails >= MAX_GLOBAL_FAILS) {
        printf("Too many failed attempts. Exiting.\n");
        audit("RECOVERY_ABORT", "too many failures");
        exit(1);
    }
    id = readInt("Staff ID: ");
    readSecret("Recovery code: ", raw, sizeof raw);
    if (!normalizeCode(raw, code)) code[0] = '\0';
    secureZero(raw, sizeof raw);
    a = findAccount(staff, nStaff, id);
    usable = a && a->hasRecovery;
    /* Always hash, so timing does not reveal which IDs exist or have codes. */
    pbkdf2(code, usable ? a->recSalt : dummySalt, SALT_LEN, usable && a->recIter ? a->recIter : PBKDF_ITER, h);
    ok = usable && ctEqual(h, a->recHash, HASH_LEN) && a->recLockedUntil <= t;
    secureZero(code, sizeof code);
    secureZero(h, sizeof h);

    if (!ok) {
        globalFails++;
        if (usable && a->recLockedUntil <= t && ++a->recFailed >= MAX_FAILED) {
            a->recFailed = 0;
            a->recLockedUntil = t + RECOVERY_LOCK_SECONDS;
            audit("RECOVERY_LOCKOUT", "staff=%d", id);
        }
        if (a) commit();
        audit("RECOVERY_FAIL", "staff=%d", id);
        printf("Invalid staff ID or recovery code (or recovery is temporarily locked).\n");
        return;
    }
    globalFails = 0;
    printf("Recovery code accepted. Choose a new password.\n");
    for (;;) {
        if (!promptNewSecret(s, sizeof s, MIN_STAFF_SECRET, "New password: ")) continue;
        if (setSecret(a, s)) break;
        printf("Could not obtain secure random data.\n");
        secureZero(s, sizeof s);
    }
    secureZero(s, sizeof s);
    a->mustChange = 0;
    a->failed = 0;
    a->lockedUntil = 0;
    audit("RECOVERY_USED", "staff=%d", id);
    commit();
    printf("Password reset. The recovery code you just used is now void; here is a new one.\n");
    issueRecoveryCode(a);
    printf("You can now log in with the new password.\n");
}

static void logout(void) {
    role = ROLE_NONE;
    userId = 0;
}

static void login(Role r) {
    Account *arr = r == ROLE_STAFF ? staff : students;
    size_t n = r == ROLE_STAFF ? nStaff : nStudents;
    static const uint8_t dummySalt[SALT_LEN] = {0};
    char secret[SECRET_MAX];
    uint8_t h[HASH_LEN];
    Account *a;
    time_t t;
    int id, ok;

    if (globalFails >= MAX_GLOBAL_FAILS) {
        printf("Too many failed logins. Exiting.\n");
        audit("LOGIN_ABORT", "too many failures");
        exit(1);
    }
    id = readInt(r == ROLE_STAFF ? "Staff ID: " : "Student ID: ");
    readSecret("Password: ", secret, sizeof secret);
    a = findAccount(arr, n, id);
    t = now();
    /* Always run the hash, even for unknown IDs, so timing does not reveal valid IDs. */
    pbkdf2(secret, a ? a->salt : dummySalt, SALT_LEN, a && a->iter ? a->iter : PBKDF_ITER, h);
    ok = a && ctEqual(h, a->hash, HASH_LEN) && a->lockedUntil <= t;
    secureZero(secret, sizeof secret);
    secureZero(h, sizeof h);

    if (!ok) {
        globalFails++;
        if (a && a->lockedUntil <= t && ++a->failed >= MAX_FAILED) {
            a->failed = 0;
            a->lockedUntil = t + LOCK_SECONDS;
            audit("LOCKOUT", "%s id=%d", r == ROLE_STAFF ? "staff" : "student", id);
        }
        if (a) commit();
        audit("LOGIN_FAIL", "%s id=%d", r == ROLE_STAFF ? "staff" : "student", id);
        printf("Invalid ID or password (or the account is temporarily locked).\n");
        return;
    }
    globalFails = 0;
    a->failed = 0;
    a->lockedUntil = 0;
    role = r;
    userId = id;
    lastActive = t;
    audit("LOGIN", "ok");
    printf("Welcome, %s.\n", a->name);
    if (a->mustChange) forceChange(a, r == ROLE_STAFF ? MIN_STAFF_SECRET : MIN_STUDENT_SECRET);
    else commit();
    if (r == ROLE_STAFF && !a->hasRecovery) {
        printf("\nYour account has no recovery code yet. Creating one now.\n");
        issueRecoveryCode(a);
    }
}

static Account *currentAccount(void) {
    return role == ROLE_STAFF ? findAccount(staff, nStaff, userId) : findStudent(userId);
}

static void changeOwnPassword(void) {
    Account *a = currentAccount();
    char cur[SECRET_MAX], s[SECRET_MAX];
    size_t minLen = role == ROLE_STAFF ? MIN_STAFF_SECRET : MIN_STUDENT_SECRET;
    if (!a) return;
    readSecret("Current password: ", cur, sizeof cur);
    if (!verifySecret(a, cur)) {
        secureZero(cur, sizeof cur);
        audit("PASSWORD_CHANGE_FAIL", "wrong current password");
        printf("Current password is incorrect.\n");
        return;
    }
    secureZero(cur, sizeof cur);
    if (!promptNewSecret(s, sizeof s, minLen, "New password: ")) return;
    if (!setSecret(a, s)) { printf("Could not obtain secure random data.\n"); secureZero(s, sizeof s); return; }
    secureZero(s, sizeof s);
    commit();
    audit("PASSWORD_CHANGED", "self");
    printf("Password changed.\n");
}

static int require(Role needed) {
    if (role == needed) return 1;
    printf("Not permitted. This action needs %s login.\n", needed == ROLE_STAFF ? "staff" : "student");
    audit("DENIED", "needed role %d", (int)needed);
    return 0;
}

static int requireLogin(void) {
    if (role != ROLE_NONE) return 1;
    printf("Please log in first.\n");
    return 0;
}

/* Students always act as themselves; staff name the student they act for. */
static int targetStudent(void) {
    if (role == ROLE_STUDENT) return userId;
    return readInt("Student ID: ");
}

/* ------------------------------------------------------------------ */
/* Core library logic                                                  */
/* ------------------------------------------------------------------ */

/* A copy of this book has just become free (returned, hold expired or
 * cancelled). Give it to the first waiting student as a READY hold, or put
 * it back on the shelf. */
static void releaseCopy(Book *b) {
    Hold *w = NULL;
    for (Hold *p = b->front; p; p = p->next) if (!p->ready) { w = p; break; }
    if (w) {
        Account *s = findStudent(w->studentId);
        char d[16];
        w->ready = 1;
        w->readyAt = now();
        w->expiresAt = w->readyAt + HOLD_SECONDS;
        audit("HOLD_READY", "book=%d student=%d", b->id, w->studentId);
        printf("Copy of \"%s\" is now on hold for student %d (%s). Collect by %s.\n",
               b->title, w->studentId, s ? s->name : "?", fmtDate(w->expiresAt, d, sizeof d));
    } else {
        b->available++;
    }
}

static void processExpiry(void) {
    time_t t = now();
    int changed = 0;
    for (size_t i = 0; i < nBooks; i++) {
        Book *b = &books[i];
        for (;;) {
            Hold *p;
            int sid;
            for (p = b->front; p; p = p->next) if (p->ready && p->expiresAt <= t) break;
            if (!p) break;
            sid = p->studentId;
            removeHold(b, sid);
            audit("HOLD_EXPIRED", "book=%d student=%d", b->id, sid);
            printf("Hold expired: student %d did not collect \"%s\".\n", sid, b->title);
            releaseCopy(b);
            changed = 1;
        }
    }
    if (changed) commit();
}

static long overdueDays(time_t due, time_t t) {
    return t > due ? (long)((t - due + 86399) / 86400) : 0;
}

static void issueBook(void) {
    int sid, bid, li;
    Account *s;
    Book *b;
    Hold *h;
    Loan *l;
    char d[16];
    if (!require(ROLE_STAFF)) return;
    sid = readInt("Student ID: ");
    bid = readInt("Book ID: ");
    s = findStudent(sid);
    b = findBook(bid);
    if (!s || !b) { printf("Student or book not found.\n"); return; }
    if (findLoanIndex(sid, bid) >= 0) { printf("This student already has this book.\n"); return; }
    if (countStudentLoans(sid) >= MAX_LOANS_PER_STUDENT) { printf("Loan limit (%d) reached.\n", MAX_LOANS_PER_STUDENT); return; }
    h = findHold(b, sid);
    if (h && !h->ready) { printf("Student is still waiting in the queue; no copy is ready for them.\n"); return; }
    if (!h && b->available <= 0) { printf("No copy is free on the shelf. The student can reserve it.\n"); return; }
    l = pushLoan();
    if (!l) { printf("Out of memory.\n"); return; }
    l->studentId = sid; l->bookId = bid;
    l->issuedAt = now();
    l->dueAt = l->issuedAt + LOAN_SECONDS;
    l->renewals = 0;
    li = (int)(l - loans);
    if (h) removeHold(b, sid);          /* held copy becomes the loan; shelf count unchanged */
    else b->available--;
    audit("ISSUE", "book=%d student=%d due=%ld%s", bid, sid, (long)loans[li].dueAt, h ? " (from hold)" : "");
    commit();
    printf("Issued \"%s\" to %s. Due %s.\n", b->title, s->name, fmtDate(loans[li].dueAt, d, sizeof d));
}

static void returnBook(void) {
    int sid, bid, li;
    Book *b;
    long days;
    if (!require(ROLE_STAFF)) return;
    sid = readInt("Student ID returning the book: ");
    bid = readInt("Book ID: ");
    b = findBook(bid);
    li = findLoanIndex(sid, bid);
    if (!b || li < 0) { printf("No matching active loan.\n"); return; }
    days = overdueDays(loans[li].dueAt, now());
    memmove(&loans[li], &loans[li + 1], (nLoans - (size_t)li - 1) * sizeof *loans);
    nLoans--;
    audit("RETURN", "book=%d student=%d overdueDays=%ld", bid, sid, days);
    printf("Book returned.\n");
    if (days > 0) printf("OVERDUE by %ld day(s). Fine due: %ld.\n", days, days * FINE_PER_DAY);
    releaseCopy(b);
    commit();
}

static void reserveBook(void) {
    int sid, bid, pos = 0;
    Account *s;
    Book *b;
    if (!requireLogin()) return;
    sid = targetStudent();
    bid = readInt("Book ID: ");
    s = findStudent(sid);
    b = findBook(bid);
    if (!s || !b) { printf("Student or book not found.\n"); return; }
    if (findLoanIndex(sid, bid) >= 0) { printf("This student already has this book on loan.\n"); return; }
    if (findHold(b, sid)) { printf("This student already has a reservation for this book.\n"); return; }
    if (b->available > 0) { printf("A copy is on the shelf. Ask staff to issue it instead.\n"); return; }
    if (!enqueueHold(b, sid, 0, now(), 0, 0)) { printf("Out of memory.\n"); return; }
    for (Hold *p = b->front; p; p = p->next) if (!p->ready) { pos++; if (p->studentId == sid) break; }
    audit("RESERVE", "book=%d student=%d", bid, sid);
    commit();
    printf("Reserved \"%s\" for %s. Queue position: %d.\n", b->title, s->name, pos);
}

static void cancelReservation(void) {
    int sid, bid, wasReady;
    Book *b;
    Hold *h;
    if (!requireLogin()) return;
    sid = targetStudent();
    bid = readInt("Book ID: ");
    b = findBook(bid);
    h = b ? findHold(b, sid) : NULL;
    if (!h) { printf("No matching reservation.\n"); return; }
    wasReady = h->ready;
    removeHold(b, sid);
    audit("CANCEL_HOLD", "book=%d student=%d wasReady=%d", bid, sid, wasReady);
    printf("Reservation cancelled.\n");
    if (wasReady) releaseCopy(b);       /* pass the set-aside copy on */
    commit();
}

static void renewLoan(void) {
    int sid, bid, li;
    Book *b;
    char d[16];
    if (!requireLogin()) return;
    sid = targetStudent();
    bid = readInt("Book ID: ");
    b = findBook(bid);
    li = findLoanIndex(sid, bid);
    if (!b || li < 0) { printf("No matching loan.\n"); return; }
    if (now() > loans[li].dueAt) { printf("Overdue loans cannot be renewed. Please return the book.\n"); return; }
    if (loans[li].renewals >= MAX_RENEWALS) { printf("Renewal limit (%d) reached.\n", MAX_RENEWALS); return; }
    if (countWaiting(b) > 0) { printf("Cannot renew: other students are waiting for this book.\n"); return; }
    loans[li].dueAt += LOAN_SECONDS;
    loans[li].renewals++;
    audit("RENEW", "book=%d student=%d", bid, sid);
    commit();
    printf("Renewed. New due date: %s.\n", fmtDate(loans[li].dueAt, d, sizeof d));
}

/* ------------------------------------------------------------------ */
/* Views                                                               */
/* ------------------------------------------------------------------ */
static void displayBooks(void) {
    if (nBooks == 0) { printf("No books have been added yet.\n"); return; }
    printf("\n%-6s %-30s %-20s %5s %8s %7s\n", "ID", "Title", "Author", "Total", "On shelf", "Waiting");
    printf("-----------------------------------------------------------------------------\n");
    for (size_t i = 0; i < nBooks; i++)
        printf("%-6d %-30.30s %-20.20s %5d %8d %7d\n", books[i].id, books[i].title, books[i].author,
               books[i].total, books[i].available, countWaiting(&books[i]));
}

static void searchBooks(void) {
    char q[TITLE_LEN];
    char *end;
    long idq;
    int found = 0;
    if (!readText("Search (title, author or book ID): ", q, sizeof q)) return;
    idq = strtol(q, &end, 10);
    printf("\n%-6s %-30s %-20s %8s\n", "ID", "Title", "Author", "On shelf");
    for (size_t i = 0; i < nBooks; i++) {
        int byId = *end == '\0' && end != q && idq == books[i].id;
        if (byId || containsCI(books[i].title, q) || containsCI(books[i].author, q)) {
            printf("%-6d %-30.30s %-20.20s %8d\n", books[i].id, books[i].title, books[i].author, books[i].available);
            found++;
        }
    }
    if (!found) printf("No matches.\n");
}

static void viewWaitingList(void) {
    int bid, pos = 0;
    Book *b;
    char d[16];
    if (!require(ROLE_STAFF)) return;
    bid = readInt("Book ID: ");
    b = findBook(bid);
    if (!b) { printf("Book not found.\n"); return; }
    printf("\nQueue for \"%s\" (ID %d)\n", b->title, b->id);
    printf("%-10s %-12s %-24s %s\n", "Status", "Student ID", "Name", "Expires");
    for (Hold *p = b->front; p; p = p->next) {
        Account *s = findStudent(p->studentId);
        char status[16];
        if (p->ready) copyStr(status, sizeof status, "READY");
        else snprintf(status, sizeof status, "#%d", ++pos);
        printf("%-10s %-12d %-24.24s %s\n", status, p->studentId, s ? s->name : "?",
               p->ready ? fmtDate(p->expiresAt, d, sizeof d) : "-");
    }
    if (!b->front) printf("Queue is empty.\n");
}

static void displayLoans(void) {
    time_t t = now();
    char d[16];
    if (!require(ROLE_STAFF)) return;
    if (nLoans == 0) { printf("No books are currently issued.\n"); return; }
    printf("\n%-10s %-24s %-6s %-26s %-11s %s\n", "Student", "Name", "Book", "Title", "Due", "Status");
    for (size_t i = 0; i < nLoans; i++) {
        Account *s = findStudent(loans[i].studentId);
        Book *b = findBook(loans[i].bookId);
        long od = overdueDays(loans[i].dueAt, t);
        printf("%-10d %-24.24s %-6d %-26.26s %-11s ", loans[i].studentId, s ? s->name : "?", loans[i].bookId,
               b ? b->title : "?", fmtDate(loans[i].dueAt, d, sizeof d));
        if (od > 0) printf("OVERDUE %ld day(s), fine %ld\n", od, od * FINE_PER_DAY);
        else printf("ok\n");
    }
}

static void displayStudents(void) {
    if (!require(ROLE_STAFF)) return;
    if (nStudents == 0) { printf("No students registered.\n"); return; }
    printf("\n%-12s %s\n", "Student ID", "Name");
    for (size_t i = 0; i < nStudents; i++) printf("%-12d %s\n", students[i].id, students[i].name);
}

static void myAccount(void) {
    time_t t = now();
    char d[16];
    int any = 0, pos;
    if (!require(ROLE_STUDENT)) return;
    printf("\nYour loans:\n");
    for (size_t i = 0; i < nLoans; i++) {
        Book *b;
        long od;
        if (loans[i].studentId != userId) continue;
        b = findBook(loans[i].bookId);
        od = overdueDays(loans[i].dueAt, t);
        printf("  [%d] %-30.30s due %s", loans[i].bookId, b ? b->title : "?", fmtDate(loans[i].dueAt, d, sizeof d));
        if (od > 0) printf("  OVERDUE %ld day(s), fine %ld", od, od * FINE_PER_DAY);
        printf("\n");
        any = 1;
    }
    if (!any) printf("  (none)\n");
    printf("Your reservations:\n");
    any = 0;
    for (size_t i = 0; i < nBooks; i++) {
        Hold *h = findHold(&books[i], userId);
        if (!h) continue;
        any = 1;
        if (h->ready) printf("  [%d] %-30.30s READY - collect by %s\n", books[i].id, books[i].title, fmtDate(h->expiresAt, d, sizeof d));
        else {
            pos = 0;
            for (Hold *p = books[i].front; p; p = p->next) if (!p->ready) { pos++; if (p == h) break; }
            printf("  [%d] %-30.30s waiting, position %d\n", books[i].id, books[i].title, pos);
        }
    }
    if (!any) printf("  (none)\n");
}

/* ------------------------------------------------------------------ */
/* Staff administration                                                */
/* ------------------------------------------------------------------ */
static void addBook(void) {
    char title[TITLE_LEN], author[AUTHOR_LEN];
    int copies, id = 101;
    Book *b;
    if (!require(ROLE_STAFF)) return;
    if (!readText("Title: ", title, sizeof title)) return;
    if (!readText("Author: ", author, sizeof author)) return;
    copies = readInt("Number of copies: ");
    if (copies < 1 || copies > MAX_COPIES) { printf("Copies must be between 1 and %d.\n", MAX_COPIES); return; }
    for (size_t i = 0; i < nBooks; i++) if (books[i].id >= id) id = books[i].id + 1;
    b = pushBook();
    if (!b) { printf("Out of memory.\n"); return; }
    b->id = id;
    copyStr(b->title, sizeof b->title, title);
    copyStr(b->author, sizeof b->author, author);
    b->total = b->available = copies;
    audit("ADD_BOOK", "id=%d copies=%d", id, copies);
    commit();
    printf("Book added with ID %d.\n", id);
}

static void registerStudent(void) {
    char name[NAME_LEN];
    int id;
    if (!require(ROLE_STAFF)) return;
    if (!readText("Student name: ", name, sizeof name)) return;
    id = createAccount(&students, &nStudents, &capStudents, 1001, name,
                       "Temporary password for the student: ", MIN_STUDENT_SECRET, 1);
    if (!id) return;
    audit("REGISTER_STUDENT", "id=%d", id);
    commit();
    printf("Student registered with ID %d. They must change the password at first login.\n", id);
}

static void resetStudentPassword(void) {
    int id;
    Account *a;
    char s[SECRET_MAX];
    if (!require(ROLE_STAFF)) return;
    id = readInt("Student ID: ");
    a = findStudent(id);
    if (!a) { printf("Student not found.\n"); return; }
    if (!promptNewSecret(s, sizeof s, MIN_STUDENT_SECRET, "Temporary password: ")) return;
    if (!setSecret(a, s)) { printf("Could not obtain secure random data.\n"); secureZero(s, sizeof s); return; }
    secureZero(s, sizeof s);
    a->mustChange = 1; a->failed = 0; a->lockedUntil = 0;
    audit("RESET_PASSWORD", "student=%d", id);
    commit();
    printf("Password reset. The student must change it at next login.\n");
}

static void addStaff(void) {
    char name[NAME_LEN];
    int id;
    if (!require(ROLE_STAFF)) return;
    if (!readText("New staff member name: ", name, sizeof name)) return;
    id = createAccount(&staff, &nStaff, &capStaff, 1, name, "Temporary password: ", MIN_STAFF_SECRET, 1);
    if (!id) return;
    audit("ADD_STAFF", "id=%d", id);
    commit();
    printf("Staff account created with ID %d (password change required at first login).\n", id);
}

static void regenerateRecoveryCode(void) {
    Account *a;
    char cur[SECRET_MAX];
    if (!require(ROLE_STAFF)) return;
    a = currentAccount();
    if (!a) return;
    readSecret("Current password (to confirm it is you): ", cur, sizeof cur);
    if (!verifySecret(a, cur)) {
        secureZero(cur, sizeof cur);
        audit("RECOVERY_REGEN_FAIL", "wrong password");
        printf("Current password is incorrect.\n");
        return;
    }
    secureZero(cur, sizeof cur);
    issueRecoveryCode(a);               /* the old code stops working immediately */
}

static void resetStaffPassword(void) {
    int id;
    Account *a;
    char s[SECRET_MAX];
    if (!require(ROLE_STAFF)) return;
    id = readInt("Staff ID to reset: ");
    if (id == userId) { printf("Use \"Change my password\" for your own account.\n"); return; }
    a = findAccount(staff, nStaff, id);
    if (!a) { printf("Staff member not found.\n"); return; }
    if (!promptNewSecret(s, sizeof s, MIN_STAFF_SECRET, "Temporary password: ")) return;
    if (!setSecret(a, s)) { printf("Could not obtain secure random data.\n"); secureZero(s, sizeof s); return; }
    secureZero(s, sizeof s);
    a->mustChange = 1; a->failed = 0; a->lockedUntil = 0;
    audit("RESET_STAFF_PASSWORD", "staff=%d", id);
    commit();
    printf("Password reset. They must change it at next login.\n");
}

static void loadDemoData(void) {
    char s[SECRET_MAX];
    static const char *names[3] = {"Aarav", "Diya", "Kabir"};
    if (!require(ROLE_STAFF)) return;
    if (nBooks || nStudents) { printf("Demo data can only be loaded into an empty catalogue.\n"); return; }
    if (!promptNewSecret(s, sizeof s, MIN_STUDENT_SECRET, "Temporary password for the 3 demo students: ")) return;
    for (int i = 0; i < 3; i++)
        if (!createAccountWithSecret(&students, &nStudents, &capStudents, 1001, names[i], s, 1)) break;
    secureZero(s, sizeof s);
    for (int i = 0; i < 2; i++) {
        Book *b = pushBook();
        if (!b) break;
        b->id = 101 + i;
        copyStr(b->title, sizeof b->title, i == 0 ? "Data Structures in C" : "Programming in C");
        copyStr(b->author, sizeof b->author, i == 0 ? "A. Author" : "B. Author");
        b->total = b->available = i == 0 ? 2 : 1;
    }
    audit("DEMO_DATA", "loaded");
    commit();
    printf("Demo data loaded: students 1001-1003, books 101-102. Issue both copies of 101, then reserve it.\n");
}

static void firstRunSetup(void) {
    if (nStaff > 0) return;
    printf("\nFirst run: no staff account exists yet. Create the first one.\n");
    for (;;) {
        char name[NAME_LEN];
        int id;
        if (!readText("Staff name: ", name, sizeof name)) continue;
        id = createAccount(&staff, &nStaff, &capStaff, 1, name, "Choose a staff password: ", MIN_STAFF_SECRET, 0);
        if (!id) continue;
        audit("FIRST_STAFF", "id=%d", id);
        commit();
        printf("Staff account created. Your staff ID is %d.\n", id);
        issueRecoveryCode(findAccount(staff, nStaff, id));
        return;
    }
}

/* ------------------------------------------------------------------ */
/* Menus                                                               */
/* ------------------------------------------------------------------ */
static int readChoice(void) {
    int c = readInt("Enter choice: ");
    time_t t = now();
    processExpiry();        /* the user may have sat at the prompt for a long time */
    if (role != ROLE_NONE && t - lastActive > SESSION_TIMEOUT) {
        printf("\nSession expired due to inactivity. Please log in again.\n");
        audit("LOGOUT", "idle timeout");
        logout();
        return -1;
    }
    lastActive = t;
    return c;
}

static void anonymousMenu(void) {
    int c;
    printf("\n=============== MAIN MENU ===============\n");
    printf("1. Browse books\n2. Search books\n3. Student login\n4. Staff login\n"
           "5. Forgot staff password (recovery code)\n0. Exit\n");
    c = readChoice();
    switch (c) {
        case 1: displayBooks(); break;
        case 2: searchBooks(); break;
        case 3: login(ROLE_STUDENT); break;
        case 4: login(ROLE_STAFF); break;
        case 5: recoverStaffPassword(); break;
        case 0: printf("Goodbye.\n"); exit(0);
        default: printf("Invalid choice.\n");
    }
}

static void studentMenu(void) {
    int c;
    printf("\n=============== STUDENT MENU ===============\n");
    printf("1. Browse books\n2. Search books\n3. Reserve a book\n4. Cancel my reservation\n"
           "5. My loans and reservations\n6. Renew a loan\n7. Change password\n0. Log out\n");
    c = readChoice();
    switch (c) {
        case 1: displayBooks(); break;
        case 2: searchBooks(); break;
        case 3: reserveBook(); break;
        case 4: cancelReservation(); break;
        case 5: myAccount(); break;
        case 6: renewLoan(); break;
        case 7: changeOwnPassword(); break;
        case 0: audit("LOGOUT", "user"); logout(); break;
        case -1: break;
        default: printf("Invalid choice.\n");
    }
}

static void staffMenu(void) {
    int c;
    printf("\n=============== STAFF MENU ===============\n");
    printf("1. Browse books\n2. Search books\n3. Issue book / hand over held copy\n4. Return book\n"
           "5. Reserve for a student\n6. Cancel a reservation or hold\n7. View a book's queue\n"
           "8. Issued books and overdue\n9. Add book\n10. Register student\n11. Reset student password\n"
           "12. List students\n13. Add staff account\n14. Change my password\n15. Load demo data\n16. Regenerate my recovery code\n"
           "17. Reset another staff member's password\n0. Log out\n");
    c = readChoice();
    switch (c) {
        case 1: displayBooks(); break;
        case 2: searchBooks(); break;
        case 3: issueBook(); break;
        case 4: returnBook(); break;
        case 5: reserveBook(); break;
        case 6: cancelReservation(); break;
        case 7: viewWaitingList(); break;
        case 8: displayLoans(); break;
        case 9: addBook(); break;
        case 10: registerStudent(); break;
        case 11: resetStudentPassword(); break;
        case 12: displayStudents(); break;
        case 13: addStaff(); break;
        case 14: changeOwnPassword(); break;
        case 15: loadDemoData(); break;
        case 16: regenerateRecoveryCode(); break;
        case 17: resetStaffPassword(); break;
        case 0: audit("LOGOUT", "user"); logout(); break;
        case -1: break;
        default: printf("Invalid choice.\n");
    }
}

/* ------------------------------------------------------------------ */
/* Startup                                                             */
/* ------------------------------------------------------------------ */
static int ensureDataDir(void) {
#ifdef _WIN32
    return _mkdir(DATA_DIR) == 0 || errno == EEXIST;
#else
    return mkdir(DATA_DIR, 0700) == 0 || errno == EEXIST;
#endif
}

/* Only one running copy may touch the data (the lock vanishes if we crash). */
static int acquireLock(void) {
#ifdef _WIN32
    int fd;
    if (_sopen_s(&fd, LOCK_FILE, _O_RDWR | _O_CREAT, _SH_DENYRW, _S_IREAD | _S_IWRITE) != 0) return 0;
    return 1;
#else
    struct flock fl;
    int fd = open(LOCK_FILE, O_RDWR | O_CREAT, 0600);
    if (fd < 0) return 0;
    memset(&fl, 0, sizeof fl);
    fl.l_type = F_WRLCK;
    fl.l_whence = SEEK_SET;
    if (fcntl(fd, F_SETLK, &fl) != 0) { close(fd); return 0; }
    return 1;                           /* fd stays open for the life of the process */
#endif
}

int main(int argc, char **argv) {
    if (argc > 1 && strcmp(argv[1], "--selftest") == 0) return selfTest();
    atexit(freeAll);
#ifndef _WIN32
    signal(SIGINT, onSigint);
#endif
    if (!ensureDataDir()) { perror("Cannot create data directory"); return 1; }
    if (!acquireLock()) { printf("Another instance is already running (or the data directory is not writable).\n"); return 1; }
    if (!loadAll()) {
        printf("Refusing to start so the existing data is not overwritten. Restore from backup or inspect %s.\n", DATA_FILE);
        return 1;
    }
    printf("==============================================\n");
    printf("   LIBRARY ISSUE & RESERVATION SYSTEM\n");
    printf("==============================================\n");
    firstRunSetup();
    for (;;) {
        processExpiry();
        if (role == ROLE_STAFF) staffMenu();
        else if (role == ROLE_STUDENT) studentMenu();
        else anonymousMenu();
    }
}
