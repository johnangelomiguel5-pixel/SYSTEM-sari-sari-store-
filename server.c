#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <errno.h>
#include <limits.h>
#include <math.h>
#include <ctype.h>
#include <stdarg.h>
#include <openssl/crypto.h>
#include <openssl/evp.h>
#include <openssl/rand.h>
#include <openssl/ssl.h>
#include <openssl/err.h>
#include <openssl/bio.h>
#ifndef _WIN32
#include <fcntl.h>
#endif
#include "mongoose.h"
#include "sqlite3.h"
#include "hpdf.h"

#define MAX_PRODUCTS 1000
#define NAME_LEN 100
#define CATEGORY_LEN 50
#define LOW_STOCK_LIMIT 5
#define PUBLIC_DIR "public/"
#define MAX_HISTORY_LINES 100
#define DATABASE_FILE "inventory.db"
#define PDF_REPORT_FILE "stock_history_report.pdf"
#define DEBUG_MODE 1

// Limits used by product validation (backend is the source of truth).
#define MAX_PRICE 1000000.0
#define MAX_STOCK 1000000

#if DEBUG_MODE
#define DEBUG_LOG(...)       \
    do                       \
    {                        \
        printf("[DEBUG] ");  \
        printf(__VA_ARGS__); \
        printf("\n");        \
    } while (0)
#else
#define DEBUG_LOG(...) \
    do                 \
    {                  \
    } while (0)
#endif

typedef struct
{
    int id;
    char name[NAME_LEN];
    char category[CATEGORY_LEN];
    double price;
    int stock;
} Product;

Product products[MAX_PRODUCTS] = {
    {101, "Pancit Canton", "Food", 15.00, 20},
    {102, "Coca-Cola", "Drinks", 75.00, 10},
    {103, "Piattos", "Snacks", 25.00, 3},
    {104, "Safeguard", "Personal Care", 30.00, 12}};
int product_count = 4;

static sqlite3 *db = NULL;
// =========================
// SESSIONS (per-browser, not global)
// =========================
// A single shared "session_active" flag would mean one person logging in
// unlocks the site for every visitor, on every device, until the server
// restarts. Instead, each successful login gets its own random token,
// handed to that browser as a cookie -- only requests carrying a valid,
// unexpired token are treated as logged in.
//
// Sessions are long-lived but never permanent:
//   * SESSION_IDLE_SECONDS  - a session survives this long without use, and
//                             every request slides the window forward, so
//                             normal use never forces a re-login.
//   * SESSION_MAX_SECONDS   - hard cap from the moment of login. After this
//                             the user must log in again no matter what.
//   * Logout, a password change and a password reset all revoke sessions
//     immediately (see destroy_session / destroy_user_sessions).
#define MAX_SESSIONS 200
#define SESSION_TOKEN_LEN 33                       // 32 hex chars + null
#define SESSION_IDLE_SECONDS (30 * 24 * 60 * 60)   // 30 days of inactivity
#define SESSION_MAX_SECONDS (90 * 24 * 60 * 60)    // 90 days absolute

typedef struct
{
    char token[SESSION_TOKEN_LEN];
    char username[100];
    time_t expires; // idle expiry (slides forward on use)
    time_t created; // used for the absolute lifetime cap
    int in_use;
} Session;

static Session sessions[MAX_SESSIONS];

static int db_execute(const char *sql)
{
    char *error_message = NULL;
    int rc = sqlite3_exec(db, sql, NULL, NULL, &error_message);
    if (rc != SQLITE_OK)
    {
        printf("[ERROR] SQLite: %s\n", error_message ? error_message : "Unknown error");
        sqlite3_free(error_message);
        return 0;
    }
    return 1;
}

// Generates a random session token as hex text. Returns 0 if the system
// random number generator fails (the caller must then refuse to log in).
static int generate_session_token(char *out)
{
    unsigned char raw[16];
    if (RAND_bytes(raw, sizeof(raw)) != 1)
        return 0;
    for (int i = 0; i < 16; i++)
        sprintf(out + i * 2, "%02x", raw[i]);
    return 1;
}

static int session_is_alive(const Session *s, time_t now)
{
    return s->in_use && s->expires >= now && s->created + SESSION_MAX_SECONDS >= now;
}

// Starts a session for username and returns its token, or NULL on failure.
// If every slot is busy the session closest to expiring is evicted, so a
// login never fails just because old sessions are still waiting to expire.
static const char *create_session(const char *username)
{
    time_t now = time(NULL);
    int slot = -1;

    for (int i = 0; i < MAX_SESSIONS; i++)
    {
        if (!session_is_alive(&sessions[i], now))
        {
            slot = i;
            break;
        }
    }

    if (slot < 0)
    {
        slot = 0;
        for (int i = 1; i < MAX_SESSIONS; i++)
            if (sessions[i].expires < sessions[slot].expires)
                slot = i;
    }

    if (!generate_session_token(sessions[slot].token))
        return NULL;

    snprintf(sessions[slot].username, sizeof(sessions[slot].username), "%s", username);
    sessions[slot].created = now;
    sessions[slot].expires = now + SESSION_IDLE_SECONDS;
    sessions[slot].in_use = 1;
    return sessions[slot].token;
}

// Pulls "session=<token>" out of the Cookie header, if present.
static int get_cookie_value(struct mg_http_message *hm, const char *name, char *out, size_t out_size)
{
    struct mg_str *cookie_header = mg_http_get_header(hm, "Cookie");
    if (!cookie_header)
        return 0;

    struct mg_str cookie = mg_http_get_header_var(*cookie_header, mg_str(name));
    if (cookie.len == 0 || cookie.len >= out_size)
        return 0;

    memcpy(out, cookie.buf, cookie.len);
    out[cookie.len] = '\0';
    return 1;
}

// Returns the logged-in username for this specific request, or NULL if
// this particular browser has no valid session. A valid session is
// extended (sliding expiry) up to the absolute SESSION_MAX_SECONDS cap.
static const char *current_user(struct mg_http_message *hm)
{
    char token[SESSION_TOKEN_LEN];
    if (!get_cookie_value(hm, "session", token, sizeof(token)))
        return NULL;

    time_t now = time(NULL);

    for (int i = 0; i < MAX_SESSIONS; i++)
    {
        if (sessions[i].in_use && strcmp(sessions[i].token, token) == 0)
        {
            if (!session_is_alive(&sessions[i], now))
            {
                sessions[i].in_use = 0;
                return NULL;
            }

            time_t slid = now + SESSION_IDLE_SECONDS;
            time_t cap = sessions[i].created + SESSION_MAX_SECONDS;
            sessions[i].expires = slid < cap ? slid : cap;
            return sessions[i].username;
        }
    }
    return NULL;
}

static void destroy_session(const char *token)
{
    for (int i = 0; i < MAX_SESSIONS; i++)
    {
        if (sessions[i].in_use && strcmp(sessions[i].token, token) == 0)
        {
            sessions[i].in_use = 0;
            return;
        }
    }
}

// Revokes every session belonging to a user (used after a password change
// or reset, so a stolen/old session cannot outlive the old password).
static void destroy_user_sessions(const char *username)
{
    for (int i = 0; i < MAX_SESSIONS; i++)
        if (sessions[i].in_use && strcmp(sessions[i].username, username) == 0)
            sessions[i].in_use = 0;
}

// Cookie attributes shared by login. HttpOnly keeps scripts away from the
// token, SameSite=Lax stops other websites from making this browser send
// the cookie on cross-site POSTs, and Max-Age makes it survive a browser
// restart (the server still enforces the real limits above).
#define SESSION_COOKIE_ATTRS "; Path=/; HttpOnly; SameSite=Lax"

#define PASSWORD_SALT_SIZE 16
#define PASSWORD_HASH_SIZE 32
#define PASSWORD_ITERATIONS 100000

static void bytes_to_hex(const unsigned char *bytes, int length, char *hex)
{
    int i;
    for (i = 0; i < length; i++)
    {
        sprintf(hex + (i * 2), "%02x", bytes[i]);
    }
    hex[length * 2] = '\0';
}

// (Two now-removed globals used to live here -- password_hash[300] and
// salt_hex[...]. They shadowed local buffers of the same name inside
// hash_password(), verify_password(), and init_database() and were never
// actually used themselves, so they've been deleted as dead code.)

static int hash_password(const char *password, char *result, int result_size, char *salt_hex_out, int salt_hex_out_size)
{
    unsigned char salt[PASSWORD_SALT_SIZE];
    unsigned char hash[PASSWORD_HASH_SIZE];
    char salt_hex[PASSWORD_SALT_SIZE * 2 + 1];
    char hash_hex[PASSWORD_HASH_SIZE * 2 + 1];

    if (RAND_bytes(salt, sizeof(salt)) != 1)
    {
        DEBUG_LOG("ERROR: Could not generate password salt.");
        return 0;
    }

    if (PKCS5_PBKDF2_HMAC(password, -1, salt, sizeof(salt), PASSWORD_ITERATIONS, EVP_sha256(), sizeof(hash), hash) != 1)
    {
        DEBUG_LOG("ERROR: Could not generate password hash.");
        return 0;
    }

    bytes_to_hex(salt, sizeof(salt), salt_hex);
    bytes_to_hex(hash, sizeof(hash), hash_hex);

    snprintf(result, result_size, "pbkdf2$sha256$%d$%s$%s", PASSWORD_ITERATIONS, salt_hex, hash_hex);

    if (salt_hex_out != NULL && salt_hex_out_size > 0)
    {
        snprintf(salt_hex_out, salt_hex_out_size, "%s", salt_hex);
    }

    return 1;
}

static int verify_password(const char *password, const char *stored_hash)
{
    int iterations;
    char salt_hex[PASSWORD_SALT_SIZE * 2 + 1] = {0};
    char hash_hex[PASSWORD_HASH_SIZE * 2 + 1] = {0};
    unsigned char salt[PASSWORD_SALT_SIZE];
    unsigned char expected_hash[PASSWORD_HASH_SIZE];
    unsigned char actual_hash[PASSWORD_HASH_SIZE];
    int i;

    // Check the stored password hash format.
    if (sscanf(stored_hash, "pbkdf2$sha256$%d$%32[0-9a-fA-F]$%64[0-9a-fA-F]",
               &iterations, salt_hex, hash_hex) != 3 ||
        iterations < 1 || iterations > 1000000 ||
        strlen(salt_hex) != PASSWORD_SALT_SIZE * 2 ||
        strlen(hash_hex) != PASSWORD_HASH_SIZE * 2)
    {
        DEBUG_LOG("ERROR: Invalid stored password format.");
        return 0;
    }

    for (i = 0; i < PASSWORD_SALT_SIZE; i++)
    {
        unsigned int value;
        if (sscanf(salt_hex + (i * 2), "%2x", &value) != 1)
            return 0;
        salt[i] = (unsigned char)value;
    }

    for (i = 0; i < PASSWORD_HASH_SIZE; i++)
    {
        unsigned int value;
        if (sscanf(hash_hex + (i * 2), "%2x", &value) != 1)
            return 0;
        expected_hash[i] = (unsigned char)value;
    }

    if (PKCS5_PBKDF2_HMAC(password, -1, salt, sizeof(salt), iterations, EVP_sha256(), sizeof(actual_hash), actual_hash) != 1)
    {
        DEBUG_LOG("ERROR: Could not verify password.");
        return 0;
    }

    return CRYPTO_memcmp(actual_hash, expected_hash, PASSWORD_HASH_SIZE) == 0;
}

// =========================
// PASSWORD POLICY
// =========================
// Enforced by the backend for every new password (reset, change, first-run
// admin). The HTML forms repeat the rules for user feedback only.
#define PASSWORD_MIN_LENGTH 16
#define PASSWORD_MAX_LENGTH 128

// Returns 1 if the password meets the policy. Otherwise returns 0 and, when
// message is not NULL, fills it with a clear explanation of what is missing.
static int validate_password_policy(const char *password, char *message, size_t message_size)
{
    int has_upper = 0, has_lower = 0, has_digit = 0, has_special = 0;
    size_t length = strlen(password);

    for (size_t i = 0; i < length; i++)
    {
        unsigned char ch = (unsigned char)password[i];
        if (ch >= 'A' && ch <= 'Z')
            has_upper = 1;
        else if (ch >= 'a' && ch <= 'z')
            has_lower = 1;
        else if (ch >= '0' && ch <= '9')
            has_digit = 1;
        else if (ch > 32 && ch < 127) // printable ASCII that is not a letter/digit
            has_special = 1;
    }

    int long_enough = length >= PASSWORD_MIN_LENGTH;
    int short_enough = length <= PASSWORD_MAX_LENGTH;

    if (long_enough && short_enough && has_upper && has_lower && has_digit && has_special)
        return 1;

    if (message && message_size > 0)
    {
        if (!short_enough)
        {
            snprintf(message, message_size,
                     "Password is too long (maximum %d characters).", PASSWORD_MAX_LENGTH);
        }
        else
        {
            snprintf(message, message_size,
                     "Password is not strong enough. Still missing:%s%s%s%s%s",
                     long_enough ? "" : " at least 16 characters;",
                     has_upper ? "" : " an uppercase letter (A-Z);",
                     has_lower ? "" : " a lowercase letter (a-z);",
                     has_digit ? "" : " a number (0-9);",
                     has_special ? "" : " a special character (! @ # $ % ^ & *);");
        }
    }
    return 0;
}

// Builds a random 20-character password that satisfies the policy. Used
// only for the very first admin account when no password was configured.
static int generate_strong_password(char *out, size_t out_size)
{
    static const char upper[] = "ABCDEFGHJKLMNPQRSTUVWXYZ";
    static const char lower[] = "abcdefghijkmnopqrstuvwxyz";
    static const char digits[] = "23456789";
    static const char special[] = "!@#$%^&*";
    static const char all[] =
        "ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz23456789!@#$%^&*";
    const int length = 20;
    unsigned char raw[40];

    if (out_size < (size_t)length + 1 || RAND_bytes(raw, sizeof(raw)) != 1)
        return 0;

    // One guaranteed character of each class, then fill with the full set.
    out[0] = upper[raw[0] % (sizeof(upper) - 1)];
    out[1] = lower[raw[1] % (sizeof(lower) - 1)];
    out[2] = digits[raw[2] % (sizeof(digits) - 1)];
    out[3] = special[raw[3] % (sizeof(special) - 1)];
    for (int i = 4; i < length; i++)
        out[i] = all[raw[i] % (sizeof(all) - 1)];

    // Shuffle (Fisher-Yates) so the guaranteed characters are not always first.
    for (int i = length - 1; i > 0; i--)
    {
        unsigned char r;
        if (RAND_bytes(&r, 1) != 1)
            return 0;
        int j = r % (i + 1);
        char tmp = out[i];
        out[i] = out[j];
        out[j] = tmp;
    }
    out[length] = '\0';
    return 1;
}

static int parse_int_value(const char *text, int *value)
{
    char *end = NULL;
    long parsed;
    if (text == NULL || *text == '\0')
        return 0;
    errno = 0;
    parsed = strtol(text, &end, 10);
    if (errno == ERANGE || end == text || *end != '\0' || parsed < INT_MIN || parsed > INT_MAX)
        return 0;
    *value = (int)parsed;
    return 1;
}

static int parse_double_value(const char *text, double *value)
{
    char *end = NULL;
    double parsed;
    if (text == NULL || *text == '\0')
        return 0;
    errno = 0;
    parsed = strtod(text, &end);
    if (errno == ERANGE || end == text || *end != '\0' || !isfinite(parsed))
        return 0;
    *value = parsed;
    return 1;
}

// True if the given table already has the given column (used by migrations).
static int column_exists(const char *table, const char *column)
{
    char sql[100];
    int found = 0;
    sqlite3_stmt *st = NULL;

    snprintf(sql, sizeof(sql), "PRAGMA table_info(%s);", table);
    if (sqlite3_prepare_v2(db, sql, -1, &st, NULL) != SQLITE_OK)
        return 0;

    while (sqlite3_step(st) == SQLITE_ROW)
    {
        const unsigned char *name = sqlite3_column_text(st, 1);
        if (name && strcmp((const char *)name, column) == 0)
        {
            found = 1;
            break;
        }
    }
    sqlite3_finalize(st);
    return found;
}

// Conservative email check: one '@', something on both sides, a dot in the
// domain, and no whitespace/control characters or <> (so the value can be
// used safely inside SMTP commands and mail headers).
static int is_valid_email(const char *email)
{
    size_t len = strlen(email);
    const char *at = NULL;

    if (len < 5 || len > 200)
        return 0;

    for (size_t i = 0; i < len; i++)
    {
        unsigned char ch = (unsigned char)email[i];
        if (ch <= 32 || ch >= 127 || ch == '<' || ch == '>' || ch == ',' || ch == ';' || ch == '"')
            return 0;
        if (ch == '@')
        {
            if (at != NULL)
                return 0;
            at = &email[i];
        }
    }

    if (at == NULL || at == email || at[1] == '\0')
        return 0;

    const char *dot = strchr(at, '.');
    return dot != NULL && dot > at + 1 && dot[1] != '\0';
}

static int init_database(void)
{
    int rc = sqlite3_open(DATABASE_FILE, &db);
    if (rc != SQLITE_OK)
    {
        printf("[ERROR] Could not open %s: %s\n", DATABASE_FILE, sqlite3_errmsg(db));
        if (db)
            sqlite3_close(db);
        db = NULL;
        return 0;
    }

    const char *create_products_sql =
        "CREATE TABLE IF NOT EXISTS products (id INTEGER PRIMARY KEY,name TEXT NOT NULL,category TEXT NOT NULL,price REAL NOT NULL,stock INTEGER NOT NULL);";
    const char *create_history_sql =
        "CREATE TABLE IF NOT EXISTS stock_history (history_id INTEGER PRIMARY KEY AUTOINCREMENT,timestamp TEXT NOT NULL,product_id INTEGER NOT NULL,product_name TEXT NOT NULL,old_stock INTEGER NOT NULL,new_stock INTEGER NOT NULL);";

    if (!db_execute(create_products_sql) || !db_execute(create_history_sql))
    {
        sqlite3_close(db);
        db = NULL;
        return 0;
    }

    // Create the users table with a separate salt column.
    const char *sql_users =
        "CREATE TABLE IF NOT EXISTS users ("
        "id INTEGER PRIMARY KEY AUTOINCREMENT,"
        "username TEXT UNIQUE NOT NULL,"
        "password_hash TEXT NOT NULL,"
        "salt TEXT NOT NULL,"
        "recovery_pin_hash TEXT"
        ");";

    if (!db_execute(sql_users))
    {
        sqlite3_close(db);
        db = NULL;
        return 0;
    }

    /*
     * Upgrade existing databases.
     * If recovery_pin_hash does not exist yet, add it.
     */
    sqlite3_stmt *column_stmt = NULL;

    const char *check_column_sql =
        "PRAGMA table_info(users);";

    int recovery_pin_exists = 0;

    if (sqlite3_prepare_v2(db, check_column_sql, -1, &column_stmt, NULL) == SQLITE_OK)
    {

        while (sqlite3_step(column_stmt) == SQLITE_ROW)
        {

            const unsigned char *column_name =
                sqlite3_column_text(column_stmt, 1);

            if (column_name &&
                strcmp((const char *)column_name, "recovery_pin_hash") == 0)
            {

                recovery_pin_exists = 1;
                break;
            }
        }

        sqlite3_finalize(column_stmt);
    }

    if (!recovery_pin_exists)
    {

        const char *add_column_sql =
            "ALTER TABLE users ADD COLUMN recovery_pin_hash TEXT;";

        if (!db_execute(add_column_sql))
        {
            printf("[ERROR] Could not add recovery PIN column.\n");
            sqlite3_close(db);
            db = NULL;
            return 0;
        }

        DEBUG_LOG("Added recovery_pin_hash column to users table.");
    }
    else
    {
        DEBUG_LOG("recovery_pin_hash column already exists.");
    }

    DEBUG_LOG("Users table ready.");

    // ---- Migration: email column (used by the email password recovery) ----
    if (!column_exists("users", "email"))
    {
        if (!db_execute("ALTER TABLE users ADD COLUMN email TEXT;"))
        {
            printf("[ERROR] Could not add email column.\n");
            sqlite3_close(db);
            db = NULL;
            return 0;
        }
        DEBUG_LOG("Added email column to users table.");
    }

    // ---- Migration: password reset tokens ----
    // Only a SHA-256 hash of each token is stored, never the token itself.
    // used_at is set when a token is consumed (or replaced by a newer one).
    if (!db_execute(
            "CREATE TABLE IF NOT EXISTS password_resets ("
            "id INTEGER PRIMARY KEY AUTOINCREMENT,"
            "user_id INTEGER NOT NULL,"
            "token_hash TEXT NOT NULL UNIQUE,"
            "created_at INTEGER NOT NULL,"
            "expires_at INTEGER NOT NULL,"
            "used_at INTEGER"
            ");"))
    {
        sqlite3_close(db);
        db = NULL;
        return 0;
    }

    // ---- The old 6-digit recovery PIN is retired ----
    // The column stays (we never drop columns from an existing database) but
    // every stored PIN hash is cleared so the PIN can no longer be used.
    db_execute("UPDATE users SET recovery_pin_hash = NULL WHERE recovery_pin_hash IS NOT NULL;");

    DEBUG_LOG("Users table ready.");

    const char *admin_username = "admin";
    sqlite3_stmt *user_stmt = NULL;
    int user_count = 0;

    const char *check_user_sql = "SELECT COUNT(*) FROM users;";

    if (sqlite3_prepare_v2(db, check_user_sql, -1, &user_stmt, NULL) != SQLITE_OK)
    {
        printf("[ERROR] Could not check users table: %s\n", sqlite3_errmsg(db));
        sqlite3_close(db);
        db = NULL;
        return 0;
    }

    if (sqlite3_step(user_stmt) == SQLITE_ROW)
    {
        user_count = sqlite3_column_int(user_stmt, 0);
    }

    sqlite3_finalize(user_stmt);
    user_stmt = NULL;

    // First run only: create the admin account. The initial password must
    // satisfy the same strong-password policy as every other password. It
    // comes from SARI_ADMIN_PASSWORD, or a random one is generated and
    // printed once. Existing accounts in an existing database are untouched.
    if (user_count == 0)
    {
        char admin_password[PASSWORD_MAX_LENGTH + 1];
        char policy_message[300];
        int generated = 0;
        const char *configured = getenv("SARI_ADMIN_PASSWORD");

        if (configured != NULL && configured[0] != '\0')
        {
            if (validate_password_policy(configured, policy_message, sizeof(policy_message)))
            {
                snprintf(admin_password, sizeof(admin_password), "%s", configured);
            }
            else
            {
                printf("[WARNING] SARI_ADMIN_PASSWORD was ignored. %s\n", policy_message);
                configured = NULL;
            }
        }

        if (configured == NULL || configured[0] == '\0')
        {
            if (!generate_strong_password(admin_password, sizeof(admin_password)))
            {
                printf("[ERROR] Could not generate an admin password.\n");
                sqlite3_close(db);
                db = NULL;
                return 0;
            }
            generated = 1;
        }

        char password_hash[300];
        char salt_hex[PASSWORD_SALT_SIZE * 2 + 1];

        if (!hash_password(
                admin_password,
                password_hash,
                sizeof(password_hash),
                salt_hex,
                sizeof(salt_hex)))
        {
            DEBUG_LOG("ERROR: Could not hash admin password.");
            sqlite3_close(db);
            db = NULL;
            return 0;
        }

        // Insert the admin username, password hash, and salt.
        const char *insert_user_sql =
            "INSERT INTO users (username, password_hash, salt) VALUES (?, ?, ?);";

        if (sqlite3_prepare_v2(db, insert_user_sql, -1, &user_stmt, NULL) != SQLITE_OK)
        {
            printf("[ERROR] Could not prepare admin account: %s\n", sqlite3_errmsg(db));
            sqlite3_close(db);
            db = NULL;
            return 0;
        }

        sqlite3_bind_text(user_stmt, 1, admin_username, -1, SQLITE_STATIC);
        sqlite3_bind_text(user_stmt, 2, password_hash, -1, SQLITE_TRANSIENT);
        sqlite3_bind_text(user_stmt, 3, salt_hex, -1, SQLITE_TRANSIENT);

        rc = sqlite3_step(user_stmt);

        if (rc != SQLITE_DONE)
        {
            printf("[ERROR] Could not create admin account.\n");
            printf("[ERROR] SQLite code: %d\n", rc);
            printf("[ERROR] SQLite message: %s\n", sqlite3_errmsg(db));
            sqlite3_finalize(user_stmt);
            sqlite3_close(db);
            db = NULL;
            return 0;
        }

        sqlite3_finalize(user_stmt);
        user_stmt = NULL;
        DEBUG_LOG("Default admin account created.");

        if (generated)
        {
            printf("\n[SETUP] First run: admin account created.\n");
            printf("[SETUP]   Username: %s\n", admin_username);
            printf("[SETUP]   Password: %s\n", admin_password);
            printf("[SETUP] Write this down now - it is shown only once.\n\n");
        }
    }
    else
    {
        DEBUG_LOG("Admin account already exists.");
    }

    // Optional: attach the recovery email to the admin account. Reset links
    // are only ever sent to the address stored here.
    const char *admin_email = getenv("SARI_ADMIN_EMAIL");
    if (admin_email != NULL && admin_email[0] != '\0')
    {
        if (!is_valid_email(admin_email))
        {
            printf("[WARNING] SARI_ADMIN_EMAIL is not a valid email address; ignored.\n");
        }
        else if (sqlite3_prepare_v2(db, "UPDATE users SET email = ? WHERE username = ?;", -1, &user_stmt, NULL) == SQLITE_OK)
        {
            sqlite3_bind_text(user_stmt, 1, admin_email, -1, SQLITE_STATIC);
            sqlite3_bind_text(user_stmt, 2, admin_username, -1, SQLITE_STATIC);
            sqlite3_step(user_stmt);
            sqlite3_finalize(user_stmt);
            user_stmt = NULL;
            DEBUG_LOG("Admin recovery email set from SARI_ADMIN_EMAIL.");
        }
    }

    DEBUG_LOG("SQLite database opened: %s", DATABASE_FILE);
    return 1;
}

static int save_products(void)
{
    if (!db)
        return 0;
    if (!db_execute("BEGIN TRANSACTION;"))
        return 0;
    if (!db_execute("DELETE FROM products;"))
    {
        db_execute("ROLLBACK;");
        return 0;
    }

    const char *sql = "INSERT INTO products (id, name, category, price, stock) VALUES (?, ?, ?, ?, ?);";
    sqlite3_stmt *stmt = NULL;
    int rc = sqlite3_prepare_v2(db, sql, -1, &stmt, NULL);

    if (rc != SQLITE_OK)
    {
        printf("[ERROR] SQLite prepare failed: %s\n", sqlite3_errmsg(db));
        db_execute("ROLLBACK;");
        return 0;
    }

    for (int i = 0; i < product_count; i++)
    {
        Product *p = &products[i];
        sqlite3_bind_int(stmt, 1, p->id);
        sqlite3_bind_text(stmt, 2, p->name, -1, SQLITE_TRANSIENT);
        sqlite3_bind_text(stmt, 3, p->category, -1, SQLITE_TRANSIENT);
        sqlite3_bind_double(stmt, 4, p->price);
        sqlite3_bind_int(stmt, 5, p->stock);

        rc = sqlite3_step(stmt);
        sqlite3_reset(stmt);

        if (rc != SQLITE_DONE)
        {
            printf("[ERROR] SQLite insert failed: %s\n", sqlite3_errmsg(db));
            sqlite3_finalize(stmt);
            db_execute("ROLLBACK;");
            return 0;
        }
    }

    sqlite3_finalize(stmt);
    if (!db_execute("COMMIT;"))
        return 0;

    DEBUG_LOG("save_products(): wrote %d products to SQLite", product_count);
    return 1;
}

static int load_products(void)
{
    if (!db)
        return 0;

    const char *sql = "SELECT id, name, category, price, stock FROM products ORDER BY id;";
    sqlite3_stmt *stmt = NULL;
    int rc = sqlite3_prepare_v2(db, sql, -1, &stmt, NULL);

    if (rc != SQLITE_OK)
    {
        printf("[ERROR] Could not prepare product SELECT: %s\n", sqlite3_errmsg(db));
        return 0;
    }

    product_count = 0;

    while ((rc = sqlite3_step(stmt)) == SQLITE_ROW && product_count < MAX_PRODUCTS)
    {
        Product *p = &products[product_count];
        p->id = sqlite3_column_int(stmt, 0);
        snprintf(p->name, sizeof(p->name), "%s", (const char *)sqlite3_column_text(stmt, 1));
        snprintf(p->category, sizeof(p->category), "%s", (const char *)sqlite3_column_text(stmt, 2));
        p->price = sqlite3_column_double(stmt, 3);
        p->stock = sqlite3_column_int(stmt, 4);
        product_count++;
    }

    sqlite3_finalize(stmt);

    if (rc != SQLITE_DONE)
    {
        printf("[ERROR] Could not read products: %s\n", sqlite3_errmsg(db));
        return 0;
    }

    if (product_count == 0)
    {
        Product defaults[] = {
            {101, "Pancit Canton", "Food", 15.00, 20},
            {102, "Coca-Cola", "Drinks", 75.00, 10},
            {103, "Piattos", "Snacks", 25.00, 3},
            {104, "Safeguard", "Personal Care", 30.00, 12}};

        int default_count = (int)(sizeof(defaults) / sizeof(defaults[0]));
        for (int i = 0; i < default_count; i++)
            products[i] = defaults[i];
        product_count = default_count;
        DEBUG_LOG("load_products(): using default products");

        if (!save_products())
            return 0;
    }

    DEBUG_LOG("load_products(): loaded %d products from SQLite", product_count);
    return 1;
}

static void log_stock_change(int id, const char *name, int old_stock, int new_stock)
{
    if (!db)
        return;

    time_t now = time(NULL);
    char timestamp[20];
    strftime(timestamp, sizeof(timestamp), "%Y-%m-%d %H:%M:%S", localtime(&now));

    const char *sql =
        "INSERT INTO stock_history (timestamp, product_id, product_name, old_stock, new_stock) VALUES (?, ?, ?, ?, ?);";

    sqlite3_stmt *stmt = NULL;
    int rc = sqlite3_prepare_v2(db, sql, -1, &stmt, NULL);

    if (rc != SQLITE_OK)
    {
        printf("[ERROR] Could not prepare stock history INSERT: %s\n", sqlite3_errmsg(db));
        return;
    }

    sqlite3_bind_text(stmt, 1, timestamp, -1, SQLITE_TRANSIENT);
    sqlite3_bind_int(stmt, 2, id);
    sqlite3_bind_text(stmt, 3, name, -1, SQLITE_TRANSIENT);
    sqlite3_bind_int(stmt, 4, old_stock);
    sqlite3_bind_int(stmt, 5, new_stock);

    rc = sqlite3_step(stmt);

    if (rc != SQLITE_DONE)
    {
        printf("[ERROR] Could not save stock history: %s\n", sqlite3_errmsg(db));
    }

    sqlite3_finalize(stmt);
}

typedef struct
{
    const char *key;
    const char *value;
} TemplateVar;

// =========================
// GROWABLE STRING + TEMPLATE HELPERS
// =========================
// The original code built pages in fixed-size buffers (8000, 10000 bytes...)
// that silently cut off long product lists. These helpers grow as needed.
typedef struct
{
    char *data;
    size_t len;
    size_t cap;
} StrBuf;

static void sb_init(StrBuf *sb)
{
    sb->data = NULL;
    sb->len = 0;
    sb->cap = 0;
}

static int sb_reserve(StrBuf *sb, size_t extra)
{
    if (sb->data != NULL && sb->len + extra + 1 <= sb->cap)
        return 1;

    size_t new_cap = sb->cap ? sb->cap : 1024;
    while (new_cap < sb->len + extra + 1)
        new_cap *= 2;

    char *p = realloc(sb->data, new_cap);
    if (!p)
        return 0;
    sb->data = p;
    sb->cap = new_cap;
    return 1;
}

static int sb_append_n(StrBuf *sb, const char *text, size_t n)
{
    if (!sb_reserve(sb, n))
        return 0;
    memcpy(sb->data + sb->len, text, n);
    sb->len += n;
    sb->data[sb->len] = '\0';
    return 1;
}

static int sb_append(StrBuf *sb, const char *text)
{
    return sb_append_n(sb, text, strlen(text));
}

static int sb_appendf(StrBuf *sb, const char *fmt, ...)
{
    va_list ap, ap2;
    va_start(ap, fmt);
    va_copy(ap2, ap);
    int n = vsnprintf(NULL, 0, fmt, ap);
    va_end(ap);

    if (n < 0 || !sb_reserve(sb, (size_t)n))
    {
        va_end(ap2);
        return 0;
    }
    vsnprintf(sb->data + sb->len, (size_t)n + 1, fmt, ap2);
    va_end(ap2);
    sb->len += (size_t)n;
    return 1;
}

// Hands the buffer to the caller (who must free() it); never returns NULL.
static char *sb_take(StrBuf *sb)
{
    char *result = sb->data;
    if (!result)
        result = calloc(1, 1);
    sb_init(sb);
    return result;
}

static void sb_free(StrBuf *sb)
{
    free(sb->data);
    sb_init(sb);
}

// Escapes text for safe use inside HTML (text and quoted attributes).
static void html_escape(const char *in, char *out, size_t out_size)
{
    size_t j = 0;
    for (size_t i = 0; in[i] && j + 7 < out_size; i++)
    {
        const char *rep =
            in[i] == '&' ? "&amp;" : in[i] == '<' ? "&lt;"
                                 : in[i] == '>'   ? "&gt;"
                                 : in[i] == '"'   ? "&quot;"
                                 : in[i] == '\''  ? "&#39;"
                                                  : NULL;
        if (rep)
        {
            strcpy(&out[j], rep);
            j += strlen(rep);
        }
        else
            out[j++] = in[i];
    }
    out[j] = '\0';
}

// Appends HTML-escaped text to a StrBuf.
static void sb_append_escaped(StrBuf *sb, const char *text)
{
    char buf[800];
    html_escape(text ? text : "", buf, sizeof(buf));
    sb_append(sb, buf);
}

// Reads a whole file from public/ into a new heap buffer (free() it).
static char *load_template(const char *filename)
{
    char path[256];
    snprintf(path, sizeof(path), "%s%s", PUBLIC_DIR, filename);

    FILE *f = fopen(path, "rb");
    if (!f)
    {
        DEBUG_LOG("load_template(): could not open %s", path);
        return NULL;
    }

    fseek(f, 0, SEEK_END);
    long size = ftell(f);
    fseek(f, 0, SEEK_SET);
    if (size < 0)
    {
        fclose(f);
        return NULL;
    }

    char *buf = malloc((size_t)size + 1);
    if (!buf)
    {
        fclose(f);
        return NULL;
    }

    size_t got = fread(buf, 1, (size_t)size, f);
    fclose(f);
    buf[got] = '\0';
    return buf;
}

// Same substitution as render_template(), but the result is allocated to fit
// (free() it). Substituted values are never re-scanned for {{keys}}.
static char *render_alloc(const char *tmpl, const TemplateVar *vars, int var_count)
{
    StrBuf out;
    sb_init(&out);
    const char *src = tmpl;

    while (*src)
    {
        int matched = 0;

        if (src[0] == '{' && src[1] == '{')
        {
            for (int i = 0; i < var_count; i++)
            {
                size_t key_len = strlen(vars[i].key);
                if (strncmp(src, vars[i].key, key_len) == 0)
                {
                    sb_append(&out, vars[i].value ? vars[i].value : "");
                    src += key_len;
                    matched = 1;
                    break;
                }
            }
        }

        if (!matched)
        {
            sb_append_n(&out, src, 1);
            src++;
        }
    }
    return sb_take(&out);
}

// Loads a template file, fills it in, and returns the result (free() it),
// or NULL if the template is missing.
static char *render_file(const char *filename, const TemplateVar *vars, int var_count)
{
    char *tmpl = load_template(filename);
    if (!tmpl)
        return NULL;
    char *out = render_alloc(tmpl, vars, var_count);
    free(tmpl);
    return out;
}

// Case-insensitive helpers used by product search and category filtering.
static int ci_cmp(const char *a, const char *b)
{
    while (*a && *b)
    {
        int ca = tolower((unsigned char)*a);
        int cb = tolower((unsigned char)*b);
        if (ca != cb)
            return ca - cb;
        a++;
        b++;
    }
    return tolower((unsigned char)*a) - tolower((unsigned char)*b);
}

static int ci_contains(const char *haystack, const char *needle)
{
    size_t needle_len = strlen(needle);
    if (needle_len == 0)
        return 1;

    for (; *haystack; haystack++)
    {
        size_t i = 0;
        while (i < needle_len && haystack[i] &&
               tolower((unsigned char)haystack[i]) == tolower((unsigned char)needle[i]))
            i++;
        if (i == needle_len)
            return 1;
    }
    return 0;
}

// Removes leading/trailing whitespace in place.
static void trim_in_place(char *text)
{
    size_t start = 0;
    size_t n = strlen(text);

    while (text[start] && isspace((unsigned char)text[start]))
        start++;
    while (n > start && isspace((unsigned char)text[n - 1]))
        n--;

    memmove(text, text + start, n - start);
    text[n - start] = '\0';
}

// =========================
// PAGE SENDERS
// =========================

static void send_html(struct mg_connection *c, int status, const char *html)
{
    mg_http_reply(c, status, "Content-Type: text/html; charset=utf-8\r\n", "%s", html);
}

static void send_page(struct mg_connection *c, int status, const char *title, const char *body_html)
{
    TemplateVar vars[] = {{"{{TITLE}}", title}, {"{{BODY}}", body_html}};
    char *html = render_file("page.html", vars, 2);

    if (!html)
    {
        mg_http_reply(c, 500, "Content-Type: text/plain\r\n", "Missing page.html template");
        return;
    }

    send_html(c, status, html);
    free(html);
}

static void send_static_page(struct mg_connection *c, const char *title, const char *filename)
{
    char *body = load_template(filename);
    if (!body)
    {
        mg_http_reply(c, 500, "Content-Type: text/plain\r\n", "Missing %s", filename);
        return;
    }
    send_page(c, 200, title, body);
    free(body);
}

// Shows a short result page. Title and message are HTML-escaped here, so
// callers may pass text that includes user input.
static void send_message(struct mg_connection *c, int status, const char *title, const char *message, const char *link_url, const char *link_text)
{
    char safe_title[400];
    char safe_message[1200];
    html_escape(title, safe_title, sizeof(safe_title));
    html_escape(message, safe_message, sizeof(safe_message));

    // The message page gets a coloured box: red for errors, green otherwise.
    TemplateVar vars[] = {
        {"{{TITLE}}", safe_title},
        {"{{MESSAGE}}", safe_message},
        {"{{LINK_URL}}", link_url},
        {"{{LINK_TEXT}}", link_text},
        {"{{KIND}}", status >= 400 ? "message-error" : "message-ok"}};

    char *body = render_file("message.html", vars, 5);
    if (!body)
    {
        mg_http_reply(c, 500, "Content-Type: text/plain\r\n", "Missing message.html");
        return;
    }

    send_page(c, status, safe_title, body);
    free(body);
}

static void serve_css(struct mg_connection *c, struct mg_http_message *hm)
{
    (void)hm;
    char *css = load_template("style.css");
    if (!css)
    {
        mg_http_reply(c, 404, "Content-Type: text/plain\r\n", "style.css not found");
        return;
    }
    mg_http_reply(c, 200, "Content-Type: text/css; charset=utf-8\r\n", "%s", css);
    free(css);
}

static void serve_image(struct mg_connection *c, struct mg_http_message *hm)
{
    mg_http_serve_file(c, hm, "public/IMAHE/images2.jpg", NULL);
}

static Product *find_product(int id)
{
    for (int i = 0; i < product_count; i++)
        if (products[i].id == id)
            return &products[i];
    return NULL;
}
// =========================
// GENERATE NEXT PRODUCT ID
// =========================

// Finds the highest product ID currently in the inventory
// and generates the next ID automatically.
static int get_next_product_id(void)
{
    int highest_id = 100;

    // Check all products currently loaded in memory.
    for (int i = 0; i < product_count; i++)
    {
        if (products[i].id > highest_id)
        {
            highest_id = products[i].id;
        }
    }

    // Return the next product ID.
    return highest_id + 1;
}

// =========================
// PDF ERROR HANDLER
// =========================

// Handles errors that happen while creating the PDF.
static void pdf_error_handler(HPDF_STATUS error_no,
                              HPDF_STATUS detail_no,
                              void *user_data)
{
    // Prevent unused parameter warnings.
    (void)user_data;

    // Display the PDF error information in the terminal.
    printf("PDF Error: error_no=%04X detail_no=%u\n",
           (unsigned int)error_no,
           (unsigned int)detail_no);
}

// =========================
// DATE RANGE (for the stock history PDF)
// =========================
// Stock history timestamps are stored as "YYYY-MM-DD HH:MM:SS" in the
// server's local time (see log_stock_change). The selected range is
// compared against those same local-time strings, so there is no timezone
// conversion that could shift a record into the wrong day. "From" starts at
// 00:00:00 on the first day and "To" ends at 23:59:59 on the last day, so
// both selected days are fully included.

typedef struct
{
    int active;         // 0 = no filter (every record)
    char from[11];      // YYYY-MM-DD
    char to[11];        // YYYY-MM-DD
    char from_ts[20];   // YYYY-MM-DD 00:00:00
    char to_ts[20];     // YYYY-MM-DD 23:59:59
    char label[120];    // text shown to the user and in the PDF
} DateRange;

static const char *MONTH_NAMES[] = {
    "January", "February", "March", "April", "May", "June", "July",
    "August", "September", "October", "November", "December"};

static int days_in_month(int year, int month)
{
    static const int days[] = {31, 28, 31, 30, 31, 30, 31, 31, 30, 31, 30, 31};
    if (month == 2 && ((year % 4 == 0 && year % 100 != 0) || year % 400 == 0))
        return 29;
    return days[month - 1];
}

// Strictly validates "YYYY-MM-DD" (a real calendar date, years 2000-2100).
static int parse_iso_date(const char *text, int *year, int *month, int *day)
{
    if (strlen(text) != 10 || text[4] != '-' || text[7] != '-')
        return 0;

    for (int i = 0; i < 10; i++)
    {
        if (i == 4 || i == 7)
            continue;
        if (text[i] < '0' || text[i] > '9')
            return 0;
    }

    *year = atoi(text);
    *month = atoi(text + 5);
    *day = atoi(text + 8);

    if (*year < 2000 || *year > 2100 || *month < 1 || *month > 12)
        return 0;
    return *day >= 1 && *day <= days_in_month(*year, *month);
}

// Reads ?from=...&to=... from the request. Returns 1 on success (range is
// filled in; range->active is 0 when neither date was supplied). Returns 0
// and sets *error for anything invalid.
static int parse_report_range(struct mg_http_message *hm, DateRange *range, const char **error)
{
    char from[40] = "";
    char to[40] = "";
    int fy, fm, fd, ty, tm, td;

    memset(range, 0, sizeof(*range));

    int has_from = mg_http_get_var(&hm->query, "from", from, sizeof(from)) > 0;
    int has_to = mg_http_get_var(&hm->query, "to", to, sizeof(to)) > 0;

    if (!has_from && !has_to)
    {
        snprintf(range->label, sizeof(range->label), "All records");
        return 1;
    }

    if (!has_from || !has_to)
    {
        *error = "Please choose both a start date and an end date.";
        return 0;
    }

    if (!parse_iso_date(from, &fy, &fm, &fd))
    {
        *error = "The start date is not a valid date. Use the format YYYY-MM-DD.";
        return 0;
    }

    if (!parse_iso_date(to, &ty, &tm, &td))
    {
        *error = "The end date is not a valid date. Use the format YYYY-MM-DD.";
        return 0;
    }

    // Both strings are zero-padded YYYY-MM-DD, so strcmp orders them by date.
    if (strcmp(to, from) < 0)
    {
        *error = "The end date cannot be earlier than the start date.";
        return 0;
    }

    range->active = 1;
    // Both dates were validated above as exactly 10 characters.
    snprintf(range->from, sizeof(range->from), "%.10s", from);
    snprintf(range->to, sizeof(range->to), "%.10s", to);
    snprintf(range->from_ts, sizeof(range->from_ts), "%.10s 00:00:00", from);
    snprintf(range->to_ts, sizeof(range->to_ts), "%.10s 23:59:59", to);
    snprintf(range->label, sizeof(range->label), "%s %d, %d to %s %d, %d",
             MONTH_NAMES[fm - 1], fd, fy, MONTH_NAMES[tm - 1], td, ty);
    return 1;
}

// =========================
// GENERATE STOCK HISTORY PDF
// =========================

// Copies text for the PDF: standard PDF fonts only cover basic Latin, so any
// other byte becomes '?', and long names are shortened to fit their column.
static void pdf_safe_text(const char *in, char *out, size_t max_chars)
{
    size_t j = 0;
    size_t len = strlen(in);
    int truncate = len > max_chars;
    size_t limit = truncate ? max_chars - 3 : len;

    for (size_t i = 0; i < limit; i++)
    {
        unsigned char ch = (unsigned char)in[i];
        out[j++] = (ch >= 32 && ch < 127) ? (char)ch : '?';
    }
    if (truncate)
    {
        out[j++] = '.';
        out[j++] = '.';
        out[j++] = '.';
    }
    out[j] = '\0';
}

// Draws the column headings of the history table at height y.
static void pdf_draw_table_header(HPDF_Page page, HPDF_Font font, float y)
{
    HPDF_Page_BeginText(page);
    HPDF_Page_SetFontAndSize(page, font, 9);
    HPDF_Page_TextOut(page, 50, y, "Date & Time");
    HPDF_Page_TextOut(page, 165, y, "ID");
    HPDF_Page_TextOut(page, 200, y, "Product");
    HPDF_Page_TextOut(page, 370, y, "Old");
    HPDF_Page_TextOut(page, 420, y, "New");
    HPDF_Page_TextOut(page, 470, y, "Change");
    HPDF_Page_EndText(page);
}

// Prepares the stock history query, restricted to range when it is active.
// For the filtered form the two timestamps are bound as parameters 1 and 2.
static sqlite3_stmt *prepare_history_query(const char *select_list, const char *order_by, const DateRange *range)
{
    char sql[400];
    sqlite3_stmt *stmt = NULL;

    snprintf(sql, sizeof(sql), "SELECT %s FROM stock_history %s %s;",
             select_list,
             range->active ? "WHERE timestamp >= ?1 AND timestamp <= ?2" : "",
             order_by);

    if (sqlite3_prepare_v2(db, sql, -1, &stmt, NULL) != SQLITE_OK)
    {
        printf("Failed to prepare stock history query: %s\n", sqlite3_errmsg(db));
        return NULL;
    }

    if (range->active)
    {
        sqlite3_bind_text(stmt, 1, range->from_ts, -1, SQLITE_STATIC);
        sqlite3_bind_text(stmt, 2, range->to_ts, -1, SQLITE_STATIC);
    }
    return stmt;
}

// Creates a PDF report containing the stock history records inside range
// (or all records when the range is not active). Only reads the history
// table - nothing is modified. Returns 1 on success.
static int generate_stock_history_pdf(const DateRange *range, int *record_count_out)
{
    // Count first, so the total can be printed in the report header.
    int total = 0;
    sqlite3_stmt *count_stmt = prepare_history_query("COUNT(*)", "", range);
    if (!count_stmt)
        return 0;
    if (sqlite3_step(count_stmt) == SQLITE_ROW)
        total = sqlite3_column_int(count_stmt, 0);
    sqlite3_finalize(count_stmt);

    sqlite3_stmt *stmt = prepare_history_query(
        "timestamp, product_id, product_name, old_stock, new_stock",
        "ORDER BY history_id ASC", range);
    if (!stmt)
        return 0;

    // Create a new PDF document.
    HPDF_Doc pdf = HPDF_New(pdf_error_handler, NULL);
    if (!pdf)
    {
        printf("Failed to create PDF document.\n");
        sqlite3_finalize(stmt);
        return 0;
    }

    HPDF_Page page = HPDF_AddPage(pdf);
    HPDF_Page_SetSize(page, HPDF_PAGE_SIZE_A4, HPDF_PAGE_PORTRAIT);
    float page_height = HPDF_Page_GetHeight(page);

    HPDF_Font title_font = HPDF_GetFont(pdf, "Helvetica-Bold", NULL);
    HPDF_Font normal_font = HPDF_GetFont(pdf, "Helvetica", NULL);

    // Report title and description.
    HPDF_Page_BeginText(page);
    HPDF_Page_SetFontAndSize(page, title_font, 18);
    HPDF_Page_TextOut(page, 50, page_height - 50, "Sari-Sari Store - Stock History Report");
    HPDF_Page_EndText(page);

    char line[200];
    char range_text[160];
    pdf_safe_text(range->label, range_text, 120);

    HPDF_Page_BeginText(page);
    HPDF_Page_SetFontAndSize(page, normal_font, 9);
    HPDF_Page_TextOut(page, 50, page_height - 70, "Stock changes recorded by the inventory system.");
    HPDF_Page_EndText(page);

    // The selected date range is always printed on the report.
    HPDF_Page_BeginText(page);
    HPDF_Page_SetFontAndSize(page, title_font, 10);
    snprintf(line, sizeof(line), "Date range: %s", range_text);
    HPDF_Page_TextOut(page, 50, page_height - 88, line);
    HPDF_Page_EndText(page);

    time_t now = time(NULL);
    char generated[40];
    strftime(generated, sizeof(generated), "%Y-%m-%d %H:%M:%S", localtime(&now));

    HPDF_Page_BeginText(page);
    HPDF_Page_SetFontAndSize(page, normal_font, 9);
    snprintf(line, sizeof(line), "Records: %d    Generated: %s (server local time)", total, generated);
    HPDF_Page_TextOut(page, 50, page_height - 102, line);
    HPDF_Page_EndText(page);

    float y = page_height - 130;
    pdf_draw_table_header(page, title_font, y);
    y -= 20;

    int history_count = 0;

    while (sqlite3_step(stmt) == SQLITE_ROW)
    {
        const char *timestamp = (const char *)sqlite3_column_text(stmt, 0);
        int product_id = sqlite3_column_int(stmt, 1);
        const char *product_name = (const char *)sqlite3_column_text(stmt, 2);
        int old_stock = sqlite3_column_int(stmt, 3);
        int new_stock = sqlite3_column_int(stmt, 4);

        char id_text[20], old_text[20], new_text[20], change_text[20];
        char name_text[64];

        snprintf(id_text, sizeof(id_text), "%d", product_id);
        snprintf(old_text, sizeof(old_text), "%d", old_stock);
        snprintf(new_text, sizeof(new_text), "%d", new_stock);
        snprintf(change_text, sizeof(change_text), "%+d", new_stock - old_stock);
        pdf_safe_text(product_name ? product_name : "", name_text, 36);

        // Start a new page when this one is full.
        if (y < 60)
        {
            page = HPDF_AddPage(pdf);
            HPDF_Page_SetSize(page, HPDF_PAGE_SIZE_A4, HPDF_PAGE_PORTRAIT);
            page_height = HPDF_Page_GetHeight(page);
            y = page_height - 50;
            pdf_draw_table_header(page, title_font, y);
            y -= 20;
        }

        HPDF_Page_BeginText(page);
        HPDF_Page_SetFontAndSize(page, normal_font, 8);
        HPDF_Page_TextOut(page, 50, y, timestamp ? timestamp : "");
        HPDF_Page_TextOut(page, 165, y, id_text);
        HPDF_Page_TextOut(page, 200, y, name_text);
        HPDF_Page_TextOut(page, 370, y, old_text);
        HPDF_Page_TextOut(page, 420, y, new_text);
        HPDF_Page_TextOut(page, 470, y, change_text);
        HPDF_Page_EndText(page);

        y -= 16;
        history_count++;
    }

    sqlite3_finalize(stmt);

    if (history_count == 0)
    {
        HPDF_Page_BeginText(page);
        HPDF_Page_SetFontAndSize(page, normal_font, 10);
        HPDF_Page_TextOut(page, 50, y,
                          range->active ? "No stock history records were found in this date range."
                                        : "No stock history records found.");
        HPDF_Page_EndText(page);
    }

    HPDF_STATUS save_status = HPDF_SaveToFile(pdf, PDF_REPORT_FILE);
    HPDF_Free(pdf);

    if (save_status != HPDF_OK)
    {
        printf("Failed to save PDF report.\n");
        return 0;
    }

    printf("Stock history PDF created: %s (%d records, %s)\n",
           PDF_REPORT_FILE, history_count, range->label);

    if (record_count_out)
        *record_count_out = history_count;
    return 1;
}

// =========================
// STOCK HISTORY PDF ROUTE
// =========================

// GET /generate-stock-history-pdf?from=YYYY-MM-DD&to=YYYY-MM-DD
// With no dates it produces the full report (the original behaviour).
static void route_stock_history_pdf(struct mg_connection *c,
                                    struct mg_http_message *hm)
{
    DateRange range;
    const char *error = NULL;

    if (!parse_report_range(hm, &range, &error))
    {
        send_message(c, 400, "Invalid date range", error, "/stock-history#report", "Choose dates again");
        return;
    }

    int count = 0;
    if (!generate_stock_history_pdf(&range, &count))
    {
        send_message(c, 500, "Report failed",
                     "The stock history PDF could not be created. Check the server terminal for details.",
                     "/stock-history#report", "Return");
        return;
    }

    char count_text[40];
    char safe_range[300];
    snprintf(count_text, sizeof(count_text), "%d", count);
    html_escape(range.label, safe_range, sizeof(safe_range));

    TemplateVar vars[] = {{"{{RANGE}}", safe_range}, {"{{COUNT}}", count_text}};
    char *html = render_file("stock_history_report.html", vars, 2);
    if (!html)
    {
        mg_http_reply(c, 500, "Content-Type: text/plain\r\n",
                      "Stock history PDF was generated, but the report page could not be opened.");
        return;
    }

    send_html(c, 200, html);
    free(html);
}

// =========================
// SERVE STOCK HISTORY PDF
// =========================

// Sends the generated PDF file to the browser.
static void serve_stock_history_pdf(struct mg_connection *c,
                                    struct mg_http_message *hm)
{

    // Prevent unused parameter warning.
    (void)hm;

    // Set the PDF file type and project folder.
    struct mg_http_serve_opts opts = {
        .mime_types = "pdf=application/pdf",
        .root_dir = "."};

    // Send the PDF file to the browser.
    mg_http_serve_file(c, hm, PDF_REPORT_FILE, &opts);
}

static void format_history_row(StrBuf *out, const char *timestamp, int id, const char *name, int old_stock, int new_stock)
{
    const char *badge_class;
    const char *arrow;
    if (new_stock == 0 && old_stock > 0)
    {
        badge_class = "badge-red";
        arrow = "&#8595;";
    }
    else if (new_stock < old_stock)
    {
        badge_class = "badge-orange";
        arrow = "&#8595;";
    }
    else
    {
        badge_class = "badge-green";
        arrow = "&#8593;";
    }

    // data-label lets the stylesheet turn each row into a labelled card on
    // small screens (pure CSS, no JavaScript).
    sb_append(out, "<tr><td data-label=\"Date\">");
    sb_append_escaped(out, timestamp);
    sb_appendf(out, "</td><td data-label=\"ID\">%d</td><td data-label=\"Product\" class=\"cell-name\">", id);
    sb_append_escaped(out, name);
    sb_appendf(out,
               "</td><td data-label=\"Old Stock\">%d</td><td data-label=\"New Stock\">%d</td>"
               "<td data-label=\"Change\"><span class=\"badge %s\">%s %d</span></td></tr>",
               old_stock, new_stock, badge_class, arrow, new_stock - old_stock);
}

// Returns the latest MAX_HISTORY_LINES history rows as HTML (free() it).
static char *build_stock_history_rows(void)
{
    StrBuf rows;
    sb_init(&rows);

    const char *sql =
        "SELECT timestamp, product_id, product_name, old_stock, new_stock FROM stock_history ORDER BY history_id DESC LIMIT ?;";

    sqlite3_stmt *stmt = NULL;
    int rc = sqlite3_prepare_v2(db, sql, -1, &stmt, NULL);

    if (rc != SQLITE_OK)
    {
        printf("[ERROR] Could not read stock history: %s\n", sqlite3_errmsg(db));
        sb_append(&rows, "<tr><td colspan='6'>Could not load stock history.</td></tr>");
        return sb_take(&rows);
    }

    sqlite3_bind_int(stmt, 1, MAX_HISTORY_LINES);
    int line_count = 0;

    while ((rc = sqlite3_step(stmt)) == SQLITE_ROW)
    {
        const char *timestamp = (const char *)sqlite3_column_text(stmt, 0);
        int id = sqlite3_column_int(stmt, 1);
        const char *name = (const char *)sqlite3_column_text(stmt, 2);
        int old_stock = sqlite3_column_int(stmt, 3);
        int new_stock = sqlite3_column_int(stmt, 4);

        format_history_row(&rows, timestamp ? timestamp : "", id, name ? name : "", old_stock, new_stock);
        line_count++;
    }

    sqlite3_finalize(stmt);

    if (rc != SQLITE_DONE)
    {
        printf("[ERROR] Could not finish stock history query: %s\n", sqlite3_errmsg(db));
    }

    if (line_count == 0)
    {
        sb_append(&rows, "<tr><td colspan='6'>No stock changes recorded yet.</td></tr>");
    }

    return sb_take(&rows);
}

// Sends login.html completely as-is -- no page.html shell, no sidebar,
// since login.html is already a full standalone <html> document and an
// unauthenticated visitor should never see the app's nav anyway.
// Fills in {{ERROR}} (failed login) and {{NOTICE}} (e.g. password updated).
static void login_page(struct mg_connection *c, const char *error_message, const char *notice)
{
    TemplateVar vars[] = {{"{{ERROR}}", error_message}, {"{{NOTICE}}", notice}};
    char *html = render_file("login.html", vars, 2);

    if (!html)
    {
        mg_http_reply(c, 500, "Content-Type: text/plain\r\n", "Missing login.html");
        return;
    }

    send_html(c, 200, html);
    free(html);
}

// Renders one of the standalone recovery pages (forgot / reset / change).
// token is only ever a 64-character hex string (validated by the callers).
static void auth_page(
    struct mg_connection *c,
    const char *filename,
    const char *error_message,
    const char *notice,
    const char *token)
{
    char safe_error[600];
    char safe_notice[600];
    char safe_token[100];

    html_escape(error_message ? error_message : "", safe_error, sizeof(safe_error));
    html_escape(notice ? notice : "", safe_notice, sizeof(safe_notice));
    html_escape(token ? token : "", safe_token, sizeof(safe_token));

    TemplateVar vars[] = {
        {"{{ERROR}}", safe_error},
        {"{{NOTICE}}", safe_notice},
        {"{{TOKEN}}", safe_token}};

    char *html = render_file(filename, vars, 3);
    if (!html)
    {
        mg_http_reply(c, 500, "Content-Type: text/plain\r\n", "Missing %s", filename);
        return;
    }

    send_html(c, 200, html);
    free(html);
}

// =========================
// PASSWORD RECOVERY (email link)
// =========================
//
// The recovery flow is split into four independent parts:
//
//   1. token generation   create_reset_token()
//   2. token verification find_valid_reset_token()
//   3. password reset     route_reset_password_post()
//   4. email delivery     deliver_reset_email() -> smtp_send_mail()
//
// Only a SHA-256 hash of each token is stored in the database. A token is
// 256 bits of OpenSSL random data, valid for RESET_TOKEN_LIFETIME_SECONDS,
// and can be used exactly once.

#define RESET_TOKEN_BYTES 32
#define RESET_TOKEN_HEX_LEN (RESET_TOKEN_BYTES * 2)
#define RESET_TOKEN_LIFETIME_SECONDS (30 * 60) // 30 minutes
#define RESET_REQUEST_COOLDOWN_SECONDS 60      // one email per account per minute

// ---- 4a. SMTP client (OpenSSL only, no extra libraries) ----
//
// Configured with environment variables (see the README section at the end
// of the report):
//   SARI_SMTP_HOST      mail server, e.g. smtp.gmail.com
//   SARI_SMTP_PORT      587 (STARTTLS, default) or 465 (implicit TLS)
//   SARI_SMTP_SECURITY  "starttls" or "tls" (default: tls for 465, else starttls)
//   SARI_SMTP_USER / SARI_SMTP_PASS   login (an app password for Gmail)
//   SARI_SMTP_FROM      sender address (defaults to SARI_SMTP_USER)
//   SARI_SMTP_CA_FILE   optional CA bundle if the system one is not found
// The server certificate and hostname are always verified.

#define SMTP_TIMEOUT_SECONDS 10

typedef struct
{
    char host[256];
    char port[8];
    int implicit_tls;
    char user[256];
    char pass[256];
    char from[256];
    char ca_file[512];
} SmtpConfig;

// Reads the SMTP settings. Returns 0 when SARI_SMTP_HOST is not set.
static int smtp_load_config(SmtpConfig *cfg)
{
    const char *host = getenv("SARI_SMTP_HOST");
    const char *port = getenv("SARI_SMTP_PORT");
    const char *security = getenv("SARI_SMTP_SECURITY");
    const char *user = getenv("SARI_SMTP_USER");
    const char *pass = getenv("SARI_SMTP_PASS");
    const char *from = getenv("SARI_SMTP_FROM");
    const char *ca = getenv("SARI_SMTP_CA_FILE");

    memset(cfg, 0, sizeof(*cfg));
    if (host == NULL || host[0] == '\0')
        return 0;

    snprintf(cfg->host, sizeof(cfg->host), "%s", host);
    snprintf(cfg->port, sizeof(cfg->port), "%s", (port && port[0]) ? port : "587");
    snprintf(cfg->user, sizeof(cfg->user), "%s", user ? user : "");
    snprintf(cfg->pass, sizeof(cfg->pass), "%s", pass ? pass : "");
    snprintf(cfg->from, sizeof(cfg->from), "%s", (from && from[0]) ? from : cfg->user);
    snprintf(cfg->ca_file, sizeof(cfg->ca_file), "%s", ca ? ca : "");

    if (security && security[0])
        cfg->implicit_tls = (strcmp(security, "tls") == 0);
    else
        cfg->implicit_tls = (strcmp(cfg->port, "465") == 0);
    return 1;
}

// Reads one SMTP reply line (up to CRLF) one byte at a time.
static int smtp_read_line(BIO *io, char *line, size_t size)
{
    size_t n = 0;
    while (n + 1 < size)
    {
        char ch;
        if (BIO_read(io, &ch, 1) != 1)
            return 0;
        if (ch == '\n')
            break;
        if (ch != '\r')
            line[n++] = ch;
    }
    line[n] = '\0';
    return 1;
}

// Reads a (possibly multi-line) reply and returns its 3-digit code, or -1.
static int smtp_read_reply(BIO *io)
{
    char line[1024];
    for (int guard = 0; guard < 50; guard++)
    {
        if (!smtp_read_line(io, line, sizeof(line)) || strlen(line) < 4)
            return -1;
        if (!isdigit((unsigned char)line[0]) || !isdigit((unsigned char)line[1]) || !isdigit((unsigned char)line[2]))
            return -1;
        if (line[3] == ' ')
            return atoi(line);
        if (line[3] != '-')
            return -1;
    }
    return -1;
}

static int smtp_send_raw(BIO *io, const char *text)
{
    size_t len = strlen(text);
    size_t sent = 0;
    while (sent < len)
    {
        int n = BIO_write(io, text + sent, (int)(len - sent));
        if (n <= 0)
            return 0;
        sent += (size_t)n;
    }
    return BIO_flush(io) > 0;
}

// Sends "command\r\n" and checks that the reply code is the expected one.
static int smtp_command(BIO *io, const char *command, int expected)
{
    char line[1200];
    snprintf(line, sizeof(line), "%s\r\n", command);
    if (!smtp_send_raw(io, line))
        return 0;
    int code = smtp_read_reply(io);
    if (code != expected)
    {
        DEBUG_LOG("SMTP: unexpected reply %d to '%.12s'", code, command);
        return 0;
    }
    return 1;
}

// Puts the connected socket back into blocking mode (OpenSSL leaves it
// non-blocking after the timed connect) and adds read/write timeouts so a
// silent mail server can never freeze the shop's server for long.
static void smtp_set_timeouts(BIO *conn)
{
    int fd = (int)BIO_get_fd(conn, NULL);
    if (fd < 0)
        return;
#ifdef _WIN32
    u_long blocking = 0;
    ioctlsocket((SOCKET)fd, FIONBIO, &blocking);
    DWORD tv = SMTP_TIMEOUT_SECONDS * 1000;
    setsockopt((SOCKET)fd, SOL_SOCKET, SO_RCVTIMEO, (const char *)&tv, sizeof(tv));
    setsockopt((SOCKET)fd, SOL_SOCKET, SO_SNDTIMEO, (const char *)&tv, sizeof(tv));
#else
    int flags = fcntl(fd, F_GETFL, 0);
    if (flags >= 0)
        fcntl(fd, F_SETFL, flags & ~O_NONBLOCK);
    struct timeval tv;
    tv.tv_sec = SMTP_TIMEOUT_SECONDS;
    tv.tv_usec = 0;
    setsockopt(fd, SOL_SOCKET, SO_RCVTIMEO, &tv, sizeof(tv));
    setsockopt(fd, SOL_SOCKET, SO_SNDTIMEO, &tv, sizeof(tv));
#endif
}

// Opens a TCP connection with a connect timeout.
static BIO *smtp_connect(const SmtpConfig *cfg)
{
    char target[300];
    snprintf(target, sizeof(target), "%s:%s", cfg->host, cfg->port);

    BIO *conn = BIO_new_connect(target);
    if (!conn)
        return NULL;

    BIO_set_nbio(conn, 1);
    time_t deadline = time(NULL) + SMTP_TIMEOUT_SECONDS;

    while (BIO_do_connect(conn) <= 0)
    {
        if (!BIO_should_retry(conn) || time(NULL) > deadline)
        {
            BIO_free_all(conn);
            return NULL;
        }

        int fd = (int)BIO_get_fd(conn, NULL);
        if (fd >= 0)
        {
            fd_set write_set;
            struct timeval tv;
            FD_ZERO(&write_set);
            FD_SET((unsigned)fd, &write_set);
            tv.tv_sec = 1;
            tv.tv_usec = 0;
            select(fd + 1, NULL, &write_set, NULL, &tv);
        }
    }

    BIO_set_nbio(conn, 0);
    smtp_set_timeouts(conn);
    return conn;
}

// Wraps the connection in TLS and verifies the server certificate + hostname.
// Takes ownership of conn: it is freed here if TLS cannot be started, so the
// caller must not use or free conn afterwards.
static BIO *smtp_start_tls(SSL_CTX *ctx, BIO *conn, const char *host)
{
    BIO *ssl_bio = BIO_new_ssl(ctx, 1);
    if (!ssl_bio)
    {
        BIO_free_all(conn);
        return NULL;
    }

    SSL *ssl = NULL;
    BIO_get_ssl(ssl_bio, &ssl);
    if (!ssl)
    {
        BIO_free_all(ssl_bio);
        BIO_free_all(conn);
        return NULL;
    }

    SSL_set_tlsext_host_name(ssl, host);
    SSL_set1_host(ssl, host);

    BIO *io = BIO_push(ssl_bio, conn);
    if (BIO_do_handshake(io) <= 0)
    {
        DEBUG_LOG("SMTP: TLS handshake failed (certificate or hostname not accepted).");
        BIO_free_all(io);
        return NULL;
    }
    return io;
}

// Sends one plain-text email. Returns 1 only if the server accepted it.
// Blocks for at most a few seconds per step (SMTP_TIMEOUT_SECONDS).
static int smtp_send_mail(const SmtpConfig *cfg, const char *to, const char *subject, const char *body)
{
    int ok = 0;
    SSL_CTX *ctx = NULL;
    BIO *io = NULL;
    char command[1200];

    ctx = SSL_CTX_new(TLS_client_method());
    if (!ctx)
        return 0;
    SSL_CTX_set_min_proto_version(ctx, TLS1_2_VERSION);
    SSL_CTX_set_verify(ctx, SSL_VERIFY_PEER, NULL);
    if (cfg->ca_file[0])
    {
        if (SSL_CTX_load_verify_locations(ctx, cfg->ca_file, NULL) != 1)
        {
            DEBUG_LOG("SMTP: could not load SARI_SMTP_CA_FILE.");
            SSL_CTX_free(ctx);
            return 0;
        }
    }
    else
    {
        SSL_CTX_set_default_verify_paths(ctx);
    }

    BIO *conn = smtp_connect(cfg);
    if (!conn)
    {
        DEBUG_LOG("SMTP: could not connect to %s:%s", cfg->host, cfg->port);
        SSL_CTX_free(ctx);
        return 0;
    }

    if (cfg->implicit_tls)
    {
        io = smtp_start_tls(ctx, conn, cfg->host);
        conn = NULL; // owned by io (or already freed)
        if (!io)
        {
            SSL_CTX_free(ctx);
            return 0;
        }
    }
    else
    {
        io = conn;
    }

    // Greeting, then EHLO.
    if (smtp_read_reply(io) != 220 || !smtp_command(io, "EHLO sari-sari-store.local", 250))
        goto done;

    if (!cfg->implicit_tls)
    {
        // Upgrade the plain connection to TLS before any credentials are sent.
        if (!smtp_command(io, "STARTTLS", 220))
            goto done;
        io = smtp_start_tls(ctx, conn, cfg->host);
        conn = NULL; // owned by io (or already freed)
        if (!io)
            goto done;
        if (!smtp_command(io, "EHLO sari-sari-store.local", 250))
            goto done;
    }

    if (cfg->user[0])
    {
        // AUTH PLAIN: base64("\0user\0password")
        unsigned char auth[600];
        char encoded[900];
        size_t ulen = strlen(cfg->user), plen = strlen(cfg->pass);
        if (ulen + plen + 2 > sizeof(auth))
            goto done;
        auth[0] = 0;
        memcpy(auth + 1, cfg->user, ulen);
        auth[1 + ulen] = 0;
        memcpy(auth + 2 + ulen, cfg->pass, plen);
        int enc_len = EVP_EncodeBlock((unsigned char *)encoded, auth, (int)(ulen + plen + 2));
        encoded[enc_len] = '\0';
        snprintf(command, sizeof(command), "AUTH PLAIN %s", encoded);
        int auth_ok = smtp_command(io, command, 235);
        OPENSSL_cleanse(auth, sizeof(auth));
        OPENSSL_cleanse(encoded, sizeof(encoded));
        OPENSSL_cleanse(command, sizeof(command));
        if (!auth_ok)
            goto done;
    }

    snprintf(command, sizeof(command), "MAIL FROM:<%s>", cfg->from);
    if (!smtp_command(io, command, 250))
        goto done;
    snprintf(command, sizeof(command), "RCPT TO:<%s>", to);
    if (!smtp_command(io, command, 250))
        goto done;
    if (!smtp_command(io, "DATA", 354))
        goto done;

    {
        // Build the message. Every line ends in CRLF; a line that begins with
        // '.' gets a second '.' (SMTP dot-stuffing).
        char date[64];
        unsigned char id_raw[8];
        char id_hex[17];
        time_t now = time(NULL);
        strftime(date, sizeof(date), "%a, %d %b %Y %H:%M:%S +0000", gmtime(&now));
        if (RAND_bytes(id_raw, sizeof(id_raw)) != 1)
            goto done;
        bytes_to_hex(id_raw, sizeof(id_raw), id_hex);

        StrBuf msg;
        sb_init(&msg);
        sb_appendf(&msg, "From: Sari-Sari Store <%s>\r\n", cfg->from);
        sb_appendf(&msg, "To: <%s>\r\n", to);
        sb_appendf(&msg, "Subject: %s\r\n", subject);
        sb_appendf(&msg, "Date: %s\r\n", date);
        sb_appendf(&msg, "Message-ID: <%s@sari-sari-store.local>\r\n", id_hex);
        sb_append(&msg, "MIME-Version: 1.0\r\nContent-Type: text/plain; charset=UTF-8\r\n\r\n");

        const char *p = body;
        while (*p)
        {
            const char *eol = strchr(p, '\n');
            size_t line_len = eol ? (size_t)(eol - p) : strlen(p);
            if (*p == '.')
                sb_append(&msg, ".");
            sb_append_n(&msg, p, line_len);
            sb_append(&msg, "\r\n");
            p += line_len + (eol ? 1 : 0);
        }
        sb_append(&msg, ".\r\n");

        int sent = msg.data && smtp_send_raw(io, msg.data);
        sb_free(&msg);
        if (!sent || smtp_read_reply(io) != 250)
            goto done;
    }

    ok = 1;
    smtp_command(io, "QUIT", 221);

done:
    if (io)
        BIO_free_all(io);
    else if (conn)
        BIO_free_all(conn);
    SSL_CTX_free(ctx);
    return ok;
}

// ---- 4b. delivery layer: decides how a reset link reaches the user ----
//
// Returns 1 if the message was handed to a mail server (or, in development
// mode, written to the server console).
static int deliver_reset_email(const char *to, const char *username, const char *link)
{
    SmtpConfig cfg;
    char body[900];

    snprintf(body, sizeof(body),
             "Hello,\n"
             "\n"
             "We received a request to reset the password for the Sari-Sari Store\n"
             "inventory account \"%s\".\n"
             "\n"
             "Open this link to choose a new password (valid for %d minutes, one use only):\n"
             "\n"
             "%s\n"
             "\n"
             "If you did not ask for this, you can ignore this email. Your password\n"
             "will not change.\n",
             username, RESET_TOKEN_LIFETIME_SECONDS / 60, link);

    if (!smtp_load_config(&cfg))
    {
        // Development mode: no mail server configured. The link goes to the
        // server console ONLY (never to the browser), so a developer can still
        // test the flow. Configure SARI_SMTP_HOST to send real email.
        printf("\n[EMAIL - DEV MODE] SARI_SMTP_HOST is not set, so no email was sent.\n");
        printf("[EMAIL - DEV MODE] Reset link for '%s' <%s>:\n  %s\n\n", username, to, link);
        return 1;
    }

    if (cfg.from[0] == '\0' || !is_valid_email(cfg.from))
    {
        printf("[ERROR] SARI_SMTP_FROM / SARI_SMTP_USER is missing or not a valid email address.\n");
        return 0;
    }

    int ok = smtp_send_mail(&cfg, to, "Reset your Sari-Sari Store password", body);
    if (ok)
        DEBUG_LOG("Password reset email sent for '%s'.", username);
    else
        printf("[ERROR] Could not send the password reset email (check SARI_SMTP_* settings).\n");
    return ok;
}

// ---- 1. token generation ----

static void sha256_hex(const char *text, char *out_hex)
{
    unsigned char digest[EVP_MAX_MD_SIZE];
    unsigned int digest_len = 0;
    EVP_Digest(text, strlen(text), digest, &digest_len, EVP_sha256(), NULL);
    bytes_to_hex(digest, (int)digest_len, out_hex);
}

// A valid token is exactly 64 hexadecimal characters.
static int is_valid_token_format(const char *token)
{
    if (strlen(token) != RESET_TOKEN_HEX_LEN)
        return 0;
    for (int i = 0; i < RESET_TOKEN_HEX_LEN; i++)
        if (!isxdigit((unsigned char)token[i]))
            return 0;
    return 1;
}

// Creates a fresh token for user_id, stores only its hash, and invalidates
// the user's earlier unused tokens. token_out receives the plain token
// (65 bytes) which exists only in memory and in the emailed link.
static int create_reset_token(int user_id, char *token_out)
{
    unsigned char raw[RESET_TOKEN_BYTES];
    char hash_hex[65];
    time_t now = time(NULL);

    if (RAND_bytes(raw, sizeof(raw)) != 1)
        return 0;
    bytes_to_hex(raw, sizeof(raw), token_out);
    sha256_hex(token_out, hash_hex);

    sqlite3_stmt *stmt = NULL;

    // Housekeeping: forget tokens that expired more than a day ago.
    if (sqlite3_prepare_v2(db, "DELETE FROM password_resets WHERE expires_at < ?;", -1, &stmt, NULL) == SQLITE_OK)
    {
        sqlite3_bind_int64(stmt, 1, (sqlite3_int64)now - 24 * 60 * 60);
        sqlite3_step(stmt);
        sqlite3_finalize(stmt);
    }

    // Only the newest link works: retire this user's older unused tokens.
    if (sqlite3_prepare_v2(db, "UPDATE password_resets SET used_at = ? WHERE user_id = ? AND used_at IS NULL;", -1, &stmt, NULL) == SQLITE_OK)
    {
        sqlite3_bind_int64(stmt, 1, (sqlite3_int64)now);
        sqlite3_bind_int(stmt, 2, user_id);
        sqlite3_step(stmt);
        sqlite3_finalize(stmt);
    }

    if (sqlite3_prepare_v2(db, "INSERT INTO password_resets (user_id, token_hash, created_at, expires_at) VALUES (?, ?, ?, ?);", -1, &stmt, NULL) != SQLITE_OK)
        return 0;
    sqlite3_bind_int(stmt, 1, user_id);
    sqlite3_bind_text(stmt, 2, hash_hex, -1, SQLITE_STATIC);
    sqlite3_bind_int64(stmt, 3, (sqlite3_int64)now);
    sqlite3_bind_int64(stmt, 4, (sqlite3_int64)now + RESET_TOKEN_LIFETIME_SECONDS);
    int ok = sqlite3_step(stmt) == SQLITE_DONE;
    sqlite3_finalize(stmt);

    OPENSSL_cleanse(raw, sizeof(raw));
    return ok;
}

// ---- 2. token verification ----

// Looks the token up by its hash. Succeeds only for a token that exists,
// has not been used, and has not expired.
static int find_valid_reset_token(const char *token, int *user_id_out, char *username_out, size_t username_size)
{
    char hash_hex[65];
    int found = 0;

    if (!is_valid_token_format(token))
        return 0;
    sha256_hex(token, hash_hex);

    sqlite3_stmt *stmt = NULL;
    const char *sql =
        "SELECT r.user_id, u.username FROM password_resets r "
        "JOIN users u ON u.id = r.user_id "
        "WHERE r.token_hash = ? AND r.used_at IS NULL AND r.expires_at >= ?;";

    if (sqlite3_prepare_v2(db, sql, -1, &stmt, NULL) != SQLITE_OK)
        return 0;
    sqlite3_bind_text(stmt, 1, hash_hex, -1, SQLITE_STATIC);
    sqlite3_bind_int64(stmt, 2, (sqlite3_int64)time(NULL));

    if (sqlite3_step(stmt) == SQLITE_ROW)
    {
        *user_id_out = sqlite3_column_int(stmt, 0);
        const unsigned char *name = sqlite3_column_text(stmt, 1);
        snprintf(username_out, username_size, "%s", name ? (const char *)name : "");
        found = 1;
    }
    sqlite3_finalize(stmt);
    return found;
}

// ---- routes ----

static void route_forgot_password_get(
    struct mg_connection *c,
    struct mg_http_message *hm)
{
    (void)hm;
    auth_page(c, "forgot-password.html", "", "", "");
}

// Builds the public link that is emailed. SARI_BASE_URL should be the address
// users type into their browser, e.g. http://localhost:8080
static void build_reset_link(const char *token, char *out, size_t out_size)
{
    const char *base = getenv("SARI_BASE_URL");
    char base_clean[200];

    snprintf(base_clean, sizeof(base_clean), "%s", (base && base[0]) ? base : "http://localhost:8080");
    size_t n = strlen(base_clean);
    while (n > 0 && base_clean[n - 1] == '/')
        base_clean[--n] = '\0';

    snprintf(out, out_size, "%s/reset-password?token=%s", base_clean, token);
}

// POST /forgot-password
// The visitor always sees the SAME message, whether or not an account
// matched, so this page cannot be used to discover which usernames or email
// addresses exist.
static void route_forgot_password_post(
    struct mg_connection *c,
    struct mg_http_message *hm)
{
    static const char *GENERIC_NOTICE =
        "If an account matches what you entered, a password reset link has been "
        "sent to its registered email address. The link works once and expires "
        "in 30 minutes.";

    char identifier[300];
    identifier[0] = '\0';

    if (mg_http_get_var(&hm->body, "identifier", identifier, sizeof(identifier)) <= 0)
    {
        auth_page(c, "forgot-password.html", "Please enter your username or email address.", "", "");
        return;
    }
    trim_in_place(identifier);
    if (identifier[0] == '\0')
    {
        auth_page(c, "forgot-password.html", "Please enter your username or email address.", "", "");
        return;
    }

    sqlite3_stmt *stmt = NULL;
    const char *sql =
        "SELECT id, username, email FROM users "
        "WHERE username = ?1 COLLATE NOCASE OR email = ?1 COLLATE NOCASE LIMIT 1;";

    if (sqlite3_prepare_v2(db, sql, -1, &stmt, NULL) != SQLITE_OK)
    {
        DEBUG_LOG("ERROR: Could not prepare recovery lookup: %s", sqlite3_errmsg(db));
        auth_page(c, "forgot-password.html", "Something went wrong. Please try again later.", "", "");
        return;
    }
    sqlite3_bind_text(stmt, 1, identifier, -1, SQLITE_STATIC);

    int user_id = 0;
    char username[100] = "";
    char email[250] = "";
    int found = 0;

    if (sqlite3_step(stmt) == SQLITE_ROW)
    {
        const unsigned char *u = sqlite3_column_text(stmt, 1);
        const unsigned char *e = sqlite3_column_text(stmt, 2);
        user_id = sqlite3_column_int(stmt, 0);
        snprintf(username, sizeof(username), "%s", u ? (const char *)u : "");
        snprintf(email, sizeof(email), "%s", e ? (const char *)e : "");
        found = 1;
    }
    sqlite3_finalize(stmt);

    if (!found)
    {
        DEBUG_LOG("Password recovery requested for an unknown account.");
    }
    else if (email[0] == '\0' || !is_valid_email(email))
    {
        // Logged for the store owner only; the visitor still sees the generic message.
        DEBUG_LOG("Password recovery requested for '%s', but no valid email is on file.", username);
    }
    else
    {
        // Allow one reset email per account per minute (stops mail flooding).
        sqlite3_int64 last_request = 0;
        if (sqlite3_prepare_v2(db, "SELECT COALESCE(MAX(created_at), 0) FROM password_resets WHERE user_id = ?;", -1, &stmt, NULL) == SQLITE_OK)
        {
            sqlite3_bind_int(stmt, 1, user_id);
            if (sqlite3_step(stmt) == SQLITE_ROW)
                last_request = sqlite3_column_int64(stmt, 0);
            sqlite3_finalize(stmt);
        }

        if ((sqlite3_int64)time(NULL) - last_request < RESET_REQUEST_COOLDOWN_SECONDS)
        {
            DEBUG_LOG("Password recovery for '%s' skipped: requested too recently.", username);
        }
        else
        {
            char token[RESET_TOKEN_HEX_LEN + 1];
            char link[400];

            if (create_reset_token(user_id, token))
            {
                build_reset_link(token, link, sizeof(link));
                deliver_reset_email(email, username, link);
                OPENSSL_cleanse(token, sizeof(token));
                OPENSSL_cleanse(link, sizeof(link));
            }
            else
            {
                DEBUG_LOG("ERROR: Could not create a password reset token.");
            }
        }
    }

    auth_page(c, "forgot-password.html", "", GENERIC_NOTICE, "");
}

// GET /reset-password?token=...   (the link from the email)
static void route_reset_password_get(
    struct mg_connection *c,
    struct mg_http_message *hm)
{
    char token[200];
    int user_id;
    char username[100];

    token[0] = '\0';
    mg_http_get_var(&hm->query, "token", token, sizeof(token));

    if (!find_valid_reset_token(token, &user_id, username, sizeof(username)))
    {
        auth_page(c, "forgot-password.html",
                  "This reset link is invalid or has expired. Please request a new one.", "", "");
        return;
    }

    auth_page(c, "reset-password.html", "", "", token);
}

// POST /reset-password: verify the token again, enforce the password policy,
// store the new hash, and burn the token.
static void route_reset_password_post(
    struct mg_connection *c,
    struct mg_http_message *hm)
{
    char token[200];
    char new_password[200];
    char confirm_password[200];
    char policy_message[300];
    char username[100];
    int user_id = 0;

    token[0] = '\0';
    new_password[0] = '\0';
    confirm_password[0] = '\0';

    mg_http_get_var(&hm->body, "token", token, sizeof(token));

    if (!find_valid_reset_token(token, &user_id, username, sizeof(username)))
    {
        auth_page(c, "forgot-password.html",
                  "This reset link is invalid or has expired. Please request a new one.", "", "");
        return;
    }

    if (mg_http_get_var(&hm->body, "new_password", new_password, sizeof(new_password)) <= 0 ||
        mg_http_get_var(&hm->body, "confirm_password", confirm_password, sizeof(confirm_password)) <= 0)
    {
        auth_page(c, "reset-password.html", "Please enter and confirm your new password.", "", token);
        return;
    }

    if (strcmp(new_password, confirm_password) != 0)
    {
        auth_page(c, "reset-password.html", "Passwords do not match.", "", token);
        return;
    }

    if (!validate_password_policy(new_password, policy_message, sizeof(policy_message)))
    {
        auth_page(c, "reset-password.html", policy_message, "", token);
        return;
    }

    char new_password_hash[400];
    char new_salt_hex[100];

    if (!hash_password(new_password, new_password_hash, sizeof(new_password_hash),
                       new_salt_hex, sizeof(new_salt_hex)))
    {
        DEBUG_LOG("ERROR: Could not hash new password.");
        auth_page(c, "reset-password.html", "Could not set the new password. Please try again.", "", token);
        return;
    }

    // Update the password and retire the token in one transaction, so a
    // token can never be reused even if something fails half-way.
    char token_hash[65];
    sha256_hex(token, token_hash);

    int ok = db_execute("BEGIN;");
    sqlite3_stmt *stmt = NULL;

    if (ok)
    {
        ok = sqlite3_prepare_v2(db, "UPDATE users SET password_hash = ?, salt = ? WHERE id = ?;", -1, &stmt, NULL) == SQLITE_OK;
        if (ok)
        {
            sqlite3_bind_text(stmt, 1, new_password_hash, -1, SQLITE_STATIC);
            sqlite3_bind_text(stmt, 2, new_salt_hex, -1, SQLITE_STATIC);
            sqlite3_bind_int(stmt, 3, user_id);
            ok = sqlite3_step(stmt) == SQLITE_DONE;
            sqlite3_finalize(stmt);
        }
    }

    if (ok)
    {
        // Retire this token and any other outstanding ones for the account.
        ok = sqlite3_prepare_v2(db, "UPDATE password_resets SET used_at = ? WHERE user_id = ? AND used_at IS NULL;", -1, &stmt, NULL) == SQLITE_OK;
        if (ok)
        {
            sqlite3_bind_int64(stmt, 1, (sqlite3_int64)time(NULL));
            sqlite3_bind_int(stmt, 2, user_id);
            ok = sqlite3_step(stmt) == SQLITE_DONE;
            sqlite3_finalize(stmt);
        }
    }

    if (ok)
        ok = db_execute("COMMIT;");
    else
        db_execute("ROLLBACK;");

    OPENSSL_cleanse(new_password, sizeof(new_password));
    OPENSSL_cleanse(confirm_password, sizeof(confirm_password));

    if (!ok)
    {
        auth_page(c, "reset-password.html", "Could not update the password. Please try again.", "", token);
        return;
    }

    // Anyone logged in with the old password is signed out.
    destroy_user_sessions(username);
    DEBUG_LOG("Password successfully reset for: %s", username);

    mg_http_reply(c, 302, "Location: /login?reset=1\r\n", "");
}

// =========================
// CHANGE PASSWORD (logged-in users)
// =========================

static void change_password_result(struct mg_connection *c, int status, const char *message)
{
    char safe[700];
    html_escape(message, safe, sizeof(safe));

    char *form = load_template("change_password.html");
    if (!form)
    {
        mg_http_reply(c, 500, "Content-Type: text/plain\r\n", "Missing change_password.html");
        return;
    }

    TemplateVar vars[] = {{"{{ERROR}}", safe}};
    char *body = render_alloc(form, vars, 1);
    send_page(c, status, "Change Password", body);
    free(form);
    free(body);
}

static void route_change_password_get(struct mg_connection *c, struct mg_http_message *hm)
{
    (void)hm;
    change_password_result(c, 200, "");
}

static void route_change_password_post(struct mg_connection *c, struct mg_http_message *hm)
{
    const char *username = current_user(hm);
    char current_password[200] = "";
    char new_password[200] = "";
    char confirm_password[200] = "";
    char policy_message[300];
    char stored_hash[400] = "";

    if (!username)
    {
        mg_http_reply(c, 302, "Location: /login\r\n", "");
        return;
    }

    if (mg_http_get_var(&hm->body, "current_password", current_password, sizeof(current_password)) <= 0 ||
        mg_http_get_var(&hm->body, "new_password", new_password, sizeof(new_password)) <= 0 ||
        mg_http_get_var(&hm->body, "confirm_password", confirm_password, sizeof(confirm_password)) <= 0)
    {
        change_password_result(c, 400, "Please fill in all three password fields.");
        return;
    }

    sqlite3_stmt *stmt = NULL;
    if (sqlite3_prepare_v2(db, "SELECT password_hash FROM users WHERE username = ?;", -1, &stmt, NULL) != SQLITE_OK)
    {
        change_password_result(c, 500, "Database error. Please try again.");
        return;
    }
    sqlite3_bind_text(stmt, 1, username, -1, SQLITE_STATIC);
    if (sqlite3_step(stmt) == SQLITE_ROW)
    {
        const unsigned char *h = sqlite3_column_text(stmt, 0);
        snprintf(stored_hash, sizeof(stored_hash), "%s", h ? (const char *)h : "");
    }
    sqlite3_finalize(stmt);

    if (stored_hash[0] == '\0' || !verify_password(current_password, stored_hash))
    {
        change_password_result(c, 400, "Your current password is not correct.");
        return;
    }

    if (strcmp(new_password, confirm_password) != 0)
    {
        change_password_result(c, 400, "The new passwords do not match.");
        return;
    }

    if (!validate_password_policy(new_password, policy_message, sizeof(policy_message)))
    {
        change_password_result(c, 400, policy_message);
        return;
    }

    char new_hash[400];
    char new_salt[100];
    if (!hash_password(new_password, new_hash, sizeof(new_hash), new_salt, sizeof(new_salt)))
    {
        change_password_result(c, 500, "Could not set the new password.");
        return;
    }

    if (sqlite3_prepare_v2(db, "UPDATE users SET password_hash = ?, salt = ? WHERE username = ?;", -1, &stmt, NULL) != SQLITE_OK)
    {
        change_password_result(c, 500, "Database error. Please try again.");
        return;
    }
    sqlite3_bind_text(stmt, 1, new_hash, -1, SQLITE_STATIC);
    sqlite3_bind_text(stmt, 2, new_salt, -1, SQLITE_STATIC);
    sqlite3_bind_text(stmt, 3, username, -1, SQLITE_STATIC);
    int ok = sqlite3_step(stmt) == SQLITE_DONE;
    sqlite3_finalize(stmt);

    OPENSSL_cleanse(current_password, sizeof(current_password));
    OPENSSL_cleanse(new_password, sizeof(new_password));
    OPENSSL_cleanse(confirm_password, sizeof(confirm_password));

    if (!ok)
    {
        change_password_result(c, 500, "Could not update the password.");
        return;
    }

    // Sign out every session (including this one) so the new password is
    // required everywhere.
    char user_copy[100];
    snprintf(user_copy, sizeof(user_copy), "%s", username);
    destroy_user_sessions(user_copy);

    mg_http_reply(c, 302,
                  "Set-Cookie: session=deleted; Path=/; Max-Age=0\r\nLocation: /login?changed=1\r\n", "");
}

static void route_login_get(struct mg_connection *c, struct mg_http_message *hm)
{
    char flag[10];
    const char *error_message = "";
    const char *notice = "";

    if (mg_http_get_var(&hm->query, "error", flag, sizeof(flag)) > 0)
        error_message = "Invalid username or password.";
    else if (mg_http_get_var(&hm->query, "reset", flag, sizeof(flag)) > 0)
        notice = "Your password was updated. Please log in with your new password.";
    else if (mg_http_get_var(&hm->query, "changed", flag, sizeof(flag)) > 0)
        notice = "Your password was changed. Please log in again.";

    login_page(c, error_message, notice);
}

static void login_process(struct mg_connection *c, struct mg_http_message *hm)
{
    char username[100];
    char password[200];
    sqlite3_stmt *stmt = NULL;
    char stored_hash[400];

    username[0] = '\0';
    password[0] = '\0';

    if (mg_http_get_var(&hm->body, "username", username, sizeof(username)) <= 0)
    {
        mg_http_reply(c, 302, "Location: /login\r\n", "");
        return;
    }

    if (mg_http_get_var(&hm->body, "password", password, sizeof(password)) <= 0)
    {
        mg_http_reply(c, 302, "Location: /login\r\n", "");
        return;
    }

    const char *sql = "SELECT password_hash FROM users WHERE username = ?;";

    if (sqlite3_prepare_v2(db, sql, -1, &stmt, NULL) != SQLITE_OK)
    {
        DEBUG_LOG("ERROR: Could not prepare login query: %s", sqlite3_errmsg(db));
        mg_http_reply(c, 500, "Content-Type: text/plain\r\n", "Database error.");
        return;
    }

    sqlite3_bind_text(stmt, 1, username, -1, SQLITE_STATIC);

    if (sqlite3_step(stmt) == SQLITE_ROW)
    {
        const unsigned char *hash = sqlite3_column_text(stmt, 0);

        if (hash != NULL)
        {
            snprintf(stored_hash, sizeof(stored_hash), "%s", (const char *)hash);

            if (verify_password(password, stored_hash))
            {
                const char *token = create_session(username);
                DEBUG_LOG("Successful login: %s", username);
                sqlite3_finalize(stmt);

                if (!token)
                {
                    mg_http_reply(c, 500, "Content-Type: text/plain\r\n",
                                  "Too many active sessions, try again later.");
                    return;
                }

                char cookie_header[250];
                snprintf(cookie_header, sizeof(cookie_header),
                         "Set-Cookie: session=%s" SESSION_COOKIE_ATTRS "; Max-Age=%d\r\nLocation: /\r\n",
                         token, SESSION_MAX_SECONDS);
                mg_http_reply(c, 302, cookie_header, "");
                return;
            }
        }
    }

    sqlite3_finalize(stmt);

    DEBUG_LOG("Failed login attempt: %s", username);
    mg_http_reply(c, 302, "Location: /login?error=1\r\n", "");
}

static void route_login_post(struct mg_connection *c, struct mg_http_message *hm)
{
    login_process(c, hm);
}

// =========================
// LOGOUT
// =========================
static void logout(struct mg_connection *c, struct mg_http_message *hm)
{
    char token[SESSION_TOKEN_LEN];
    if (get_cookie_value(hm, "session", token, sizeof(token)))
    {
        destroy_session(token);
    }
    mg_http_reply(c, 302,
                  "Set-Cookie: session=deleted; Path=/; Max-Age=0\r\nLocation: /login\r\n", "");
}

static void show_main_menu(struct mg_connection *c)
{
    int low_stock_count = 0;
    int total_units = 0;
    double total_value = 0.0;

    for (int i = 0; i < product_count; i++)
    {
        total_units += products[i].stock;
        total_value += products[i].price * products[i].stock;
        if (products[i].stock <= LOW_STOCK_LIMIT)
            low_stock_count++;
    }

    char total_products_str[20];
    char low_stock_str[20];
    char total_value_str[40];
    char total_units_str[20];

    snprintf(total_products_str, sizeof(total_products_str), "%d", product_count);
    snprintf(low_stock_str, sizeof(low_stock_str), "%d", low_stock_count);
    snprintf(total_value_str, sizeof(total_value_str), "%.2f", total_value);
    snprintf(total_units_str, sizeof(total_units_str), "%d", total_units);

    char *history_rows = build_stock_history_rows();

    TemplateVar vars[] = {
        {"{{TOTAL_PRODUCTS}}", total_products_str},
        {"{{LOW_STOCK_COUNT}}", low_stock_str},
        {"{{TOTAL_VALUE}}", total_value_str},
        {"{{TOTAL_UNITS}}", total_units_str},
        {"{{STOCK_HISTORY}}", history_rows}};

    char *body = render_file("menu.html", vars, 5);
    free(history_rows);

    if (!body)
    {
        mg_http_reply(c, 500, "Content-Type: text/plain\r\n", "Missing menu.html");
        return;
    }

    send_page(c, 200, "Sari-Sari Store Inventory", body);
    free(body);
}

static void add_product_page(struct mg_connection *c)
{
    send_static_page(c, "Add Product", "add_form.html");
}

// =========================
// PRODUCT VALIDATION (shared by Add and Edit)
// =========================

// Checks and cleans the submitted product fields. name/category/price_str/
// stock_str are trimmed in place. Returns NULL when everything is valid
// (price and stock are then filled in), otherwise a user-friendly message.
static const char *validate_product_fields(char *name, char *category, char *price_str, char *stock_str, double *price, int *stock)
{
    trim_in_place(name);
    trim_in_place(category);
    trim_in_place(price_str);
    trim_in_place(stock_str);

    if (name[0] == '\0')
        return "Product name cannot be empty.";
    if (strlen(name) >= NAME_LEN)
        return "Product name is too long (maximum 99 characters).";
    if (category[0] == '\0')
        return "Category cannot be empty.";
    if (strlen(category) >= CATEGORY_LEN)
        return "Category is too long (maximum 49 characters).";

    for (const char *p = name; *p; p++)
        if (iscntrl((unsigned char)*p))
            return "Product name contains invalid characters.";
    for (const char *p = category; *p; p++)
        if (iscntrl((unsigned char)*p))
            return "Category contains invalid characters.";

    if (!parse_double_value(price_str, price))
        return "Price must be a valid number.";
    if (!parse_int_value(stock_str, stock))
        return "Stock must be a valid whole number.";
    if (*price < 0)
        return "Price cannot be negative.";
    if (*price > MAX_PRICE)
        return "Price is too large.";
    if (*stock < 0)
        return "Stock cannot be negative.";
    if (*stock > MAX_STOCK)
        return "Stock is too large.";

    // Keep prices to whole centavos (and turn -0.0 into 0.0).
    *price = floor(*price * 100.0 + 0.5) / 100.0 + 0.0;
    return NULL;
}

// =========================
// ADD PRODUCT
// =========================

static void add_product(struct mg_connection *c, struct mg_http_message *hm)
{

    // Check if the inventory has reached its maximum capacity.
    if (product_count >= MAX_PRODUCTS)
    {
        send_message(c, 400, "Error", "Inventory is full.", "/add", "Return");
        return;
    }

    // Create variables for the product information.
    char name[300];
    char category[300];
    char price_str[60];
    char stock_str[40];

    // Get the product information from the submitted form.
    // Product ID is NOT requested because it is generated automatically.
    if (mg_http_get_var(&hm->body, "name", name, sizeof(name)) <= 0 ||
        mg_http_get_var(&hm->body, "category", category, sizeof(category)) <= 0 ||
        mg_http_get_var(&hm->body, "price", price_str, sizeof(price_str)) <= 0 ||
        mg_http_get_var(&hm->body, "stock", stock_str, sizeof(stock_str)) <= 0)
    {

        send_message(c, 400, "Error", "All fields are required.", "/add", "Return");
        return;
    }

    double price;
    int stock;

    const char *problem = validate_product_fields(name, category, price_str, stock_str, &price, &stock);
    if (problem)
    {
        send_message(c, 400, "Error", problem, "/add", "Return");
        return;
    }

    // Generate the product ID automatically.
    int id = get_next_product_id();

    // Add the new product to the products array.
    Product *p = &products[product_count++];

    // Assign the automatically generated ID.
    p->id = id;

    // Copy the product name safely.
    strncpy(p->name, name, NAME_LEN - 1);
    p->name[NAME_LEN - 1] = '\0';

    // Copy the category safely.
    strncpy(p->category, category, CATEGORY_LEN - 1);
    p->category[CATEGORY_LEN - 1] = '\0';

    // Store the price and stock.
    p->price = price;
    p->stock = stock;

    // Save the new product to SQLite.
    if (!save_products())
    {
        product_count--;

        send_message(c, 500, "Error",
                     "Could not save the product to the database.",
                     "/add", "Return");
        return;
    }

    // Record the new product in stock history.
    log_stock_change(p->id, p->name, 0, p->stock);

    // Tell the user the product was added successfully.
    send_message(c, 200,
                 "Product added successfully!",
                 "The product has been added to the inventory.",
                 "/", "Return to Dashboard");
}

// =========================
// PRODUCT LIST: search, category filter, selection
// =========================

// Collects the distinct category names (case-insensitive), sorted A-Z.
// The returned array must be free()d. Count is stored in *count_out.
static char (*collect_categories(int *count_out))[CATEGORY_LEN]
{
    char (*cats)[CATEGORY_LEN] = malloc((size_t)MAX_PRODUCTS * CATEGORY_LEN);
    int count = 0;

    *count_out = 0;
    if (!cats)
        return NULL;

    for (int i = 0; i < product_count; i++)
    {
        int seen = 0;
        for (int k = 0; k < count && !seen; k++)
            seen = ci_cmp(cats[k], products[i].category) == 0;
        if (!seen && count < MAX_PRODUCTS)
            snprintf(cats[count++], CATEGORY_LEN, "%s", products[i].category);
    }

    // Simple insertion sort - there are never many categories.
    for (int i = 1; i < count; i++)
    {
        char tmp[CATEGORY_LEN];
        int j = i - 1;
        snprintf(tmp, sizeof(tmp), "%s", cats[i]);
        while (j >= 0 && ci_cmp(cats[j], tmp) > 0)
        {
            memcpy(cats[j + 1], cats[j], CATEGORY_LEN);
            j--;
        }
        snprintf(cats[j + 1], CATEGORY_LEN, "%s", tmp);
    }

    *count_out = count;
    return cats;
}

// GET /products?q=<text>&category=<name>&select=all
//   q / category narrow the list. "select=all" ticks every product that is
//   currently shown (so "Select all" always means the filtered list, never
//   hidden products). Plain HTML: no JavaScript is needed.
static void view_products(struct mg_connection *c, struct mg_http_message *hm)
{
    char q[100] = "";
    char category[CATEGORY_LEN * 2] = "";
    char select_flag[16] = "";

    mg_http_get_var(&hm->query, "q", q, sizeof(q));
    mg_http_get_var(&hm->query, "category", category, sizeof(category));
    mg_http_get_var(&hm->query, "select", select_flag, sizeof(select_flag));
    trim_in_place(q);
    trim_in_place(category);
    int select_all = strcmp(select_flag, "all") == 0;

    // ---- category drop-down ----
    int cat_count = 0;
    char (*cats)[CATEGORY_LEN] = collect_categories(&cat_count);
    StrBuf options;
    sb_init(&options);
    for (int i = 0; i < cat_count; i++)
    {
        sb_append(&options, "<option value=\"");
        sb_append_escaped(&options, cats[i]);
        sb_append(&options, ci_cmp(cats[i], category) == 0 ? "\" selected>" : "\">");
        sb_append_escaped(&options, cats[i]);
        sb_append(&options, "</option>");
    }
    free(cats);

    // ---- product rows ----
    StrBuf rows;
    sb_init(&rows);
    int shown = 0;

    for (int i = 0; i < product_count; i++)
    {
        Product *p = &products[i];

        if (category[0] && ci_cmp(p->category, category) != 0)
            continue;
        if (q[0] && !ci_contains(p->name, q))
            continue;

        shown++;
        sb_appendf(&rows,
                   "<tr><td data-label=\"Select\" class=\"col-check\">"
                   "<input type=\"checkbox\" name=\"id\" value=\"%d\"%s aria-label=\"Select product %d\"></td>"
                   "<td data-label=\"ID\">%d</td><td data-label=\"Name\" class=\"cell-name\">",
                   p->id, select_all ? " checked" : "", p->id, p->id);
        sb_append_escaped(&rows, p->name);
        sb_append(&rows, "</td><td data-label=\"Category\">");
        sb_append_escaped(&rows, p->category);
        sb_appendf(&rows, "</td><td data-label=\"Price\">&#8369;%.2f</td><td data-label=\"Stock\">%d%s</td>",
                   p->price, p->stock,
                   p->stock <= LOW_STOCK_LIMIT ? " <span class=\"badge badge-orange\">Low</span>" : "");
        sb_appendf(&rows,
                   "<td data-label=\"Actions\" class=\"cell-actions\">"
                   "<a class=\"btn btn-small\" href=\"/edit?id=%d\">Edit</a> "
                   "<a class=\"btn btn-small btn-danger-outline\" href=\"/delete-selected?id=%d\">Delete</a></td></tr>",
                   p->id, p->id);
    }

    if (shown == 0)
        sb_append(&rows, "<tr><td colspan=\"7\" class=\"empty-row\">No products match your search or category.</td></tr>");

    // ---- links that keep the current filter ----
    char enc_q[400], enc_cat[800];
    size_t enc_q_len = mg_url_encode(q, strlen(q), enc_q, sizeof(enc_q));
    size_t enc_cat_len = mg_url_encode(category, strlen(category), enc_cat, sizeof(enc_cat));
    if (enc_q_len == 0) enc_q[0] = '\0';
    if (enc_cat_len == 0) enc_cat[0] = '\0';

    char select_url[1400], clear_url[1400];
    snprintf(clear_url, sizeof(clear_url), "/products?q=%s&amp;category=%s", enc_q, enc_cat);
    snprintf(select_url, sizeof(select_url), "/products?q=%s&amp;category=%s&amp;select=all", enc_q, enc_cat);

    char safe_q[400];
    char shown_str[20], total_str[20], plural[2] = "";
    html_escape(q, safe_q, sizeof(safe_q));
    snprintf(shown_str, sizeof(shown_str), "%d", shown);
    snprintf(total_str, sizeof(total_str), "%d", product_count);
    if (shown != 1)
        strcpy(plural, "s");

    TemplateVar vars[] = {
        {"{{Q}}", safe_q},
        {"{{CATEGORY_OPTIONS}}", options.data ? options.data : ""},
        {"{{SHOWN}}", shown_str},
        {"{{TOTAL}}", total_str},
        {"{{PLURAL}}", plural},
        {"{{SELECT_ALL_URL}}", select_url},
        {"{{CLEAR_URL}}", clear_url},
        {"{{ROWS}}", rows.data ? rows.data : ""}};

    char *body = render_file("products.html", vars, 8);
    sb_free(&options);
    sb_free(&rows);

    if (!body)
    {
        mg_http_reply(c, 500, "Content-Type: text/plain\r\n", "Missing products.html");
        return;
    }

    send_page(c, 200, "View Products", body);
    free(body);
}

static void view_stock_history(struct mg_connection *c)
{
    char *rows = build_stock_history_rows();

    TemplateVar vars[] = {{"{{ROWS}}", rows}};
    char *body = render_file("stock_history.html", vars, 1);
    free(rows);

    if (!body)
    {
        mg_http_reply(c, 500, "Content-Type: text/plain\r\n", "Missing stock_history.html");
        return;
    }

    send_page(c, 200, "Stock History", body);
    free(body);
}

static void search_product_page(struct mg_connection *c)
{
    send_static_page(c, "Search Product", "search_form.html");
}

static void search_product(struct mg_connection *c, struct mg_http_message *hm)
{
    char id_str[20];

    if (mg_http_get_var(&hm->query, "id", id_str, sizeof(id_str)) <= 0)
    {
        search_product_page(c);
        return;
    }

    int id;
    if (!parse_int_value(id_str, &id))
    {
        send_message(c, 400, "Invalid Product ID", "Enter a numeric product ID.", "/search", "Search Again");
        return;
    }
    Product *p = find_product(id);

    if (p == NULL)
    {
        send_message(c, 404, "Product Not Found", "No product with that ID exists.", "/search", "Search Again");
        return;
    }

    char safe_name[700];
    char safe_category[700];
    char id_out[20];
    char price_out[30];
    char stock_out[20];

    html_escape(p->name, safe_name, sizeof(safe_name));
    html_escape(p->category, safe_category, sizeof(safe_category));

    snprintf(id_out, sizeof(id_out), "%d", p->id);
    snprintf(price_out, sizeof(price_out), "%.2f", p->price);
    snprintf(stock_out, sizeof(stock_out), "%d", p->stock);

    TemplateVar vars[] = {
        {"{{ID}}", id_out}, {"{{NAME}}", safe_name}, {"{{CATEGORY}}", safe_category}, {"{{PRICE}}", price_out}, {"{{STOCK}}", stock_out}};

    char *body = render_file("search_result.html", vars, 5);
    if (!body)
    {
        mg_http_reply(c, 500, "Content-Type: text/plain\r\n", "Missing search_result.html");
        return;
    }

    send_page(c, 200, "Product Found", body);
    free(body);
}

static void update_stock_page(struct mg_connection *c)
{
    send_static_page(c, "Update Stock", "update_form.html");
}

static void update_stock(struct mg_connection *c, struct mg_http_message *hm)
{
    char id_str[20];
    char stock_str[20];

    if (mg_http_get_var(&hm->body, "id", id_str, sizeof(id_str)) <= 0 ||
        mg_http_get_var(&hm->body, "stock", stock_str, sizeof(stock_str)) <= 0)
    {
        send_message(c, 400, "Error", "Please enter all required fields.", "/update", "Return");
        return;
    }

    int id;
    if (!parse_int_value(id_str, &id))
    {
        send_message(c, 400, "Invalid Product ID", "Enter a numeric product ID.", "/update", "Return");
        return;
    }
    Product *p = find_product(id);

    if (p == NULL)
    {
        send_message(c, 404, "Product Not Found", "", "/update", "Return");
        return;
    }

    int stock;
    if (!parse_int_value(stock_str, &stock))
    {
        send_message(c, 400, "Error", "Stock must be a valid whole number.", "/update", "Return");
        return;
    }

    if (stock < 0)
    {
        send_message(c, 400, "Error", "Stock cannot be negative.", "/update", "Return");
        return;
    }

    int old_stock = p->stock;
    p->stock = stock;

    if (!save_products())
    {
        p->stock = old_stock;
        send_message(c, 500, "Error", "Could not save the stock update.", "/update", "Return");
        return;
    }

    log_stock_change(p->id, p->name, old_stock, p->stock);

    char msg[100];
    snprintf(msg, sizeof(msg), "The new stock quantity is %d.", p->stock);

    send_message(c, 200, "Stock updated successfully!", msg, "/products", "View Products");
}

// =========================
// EDIT PRODUCT (name, price, category, stock)
// =========================

// GET /edit?id=N - the form, pre-filled with the product's current values.
static void route_edit_get(struct mg_connection *c, struct mg_http_message *hm)
{
    char id_str[20];
    int id;

    if (mg_http_get_var(&hm->query, "id", id_str, sizeof(id_str)) <= 0 || !parse_int_value(id_str, &id))
    {
        send_message(c, 400, "Invalid Product ID", "Choose a product from the product list.", "/products", "View Products");
        return;
    }

    Product *p = find_product(id);
    if (p == NULL)
    {
        send_message(c, 404, "Product Not Found", "No product with that ID exists.", "/products", "View Products");
        return;
    }

    char id_out[20], price_out[40], stock_out[20];
    char safe_name[700], safe_category[700];
    snprintf(id_out, sizeof(id_out), "%d", p->id);
    snprintf(price_out, sizeof(price_out), "%.2f", p->price);
    snprintf(stock_out, sizeof(stock_out), "%d", p->stock);
    html_escape(p->name, safe_name, sizeof(safe_name));
    html_escape(p->category, safe_category, sizeof(safe_category));

    // Existing categories are offered as suggestions (typing a new one is fine).
    int cat_count = 0;
    char (*cats)[CATEGORY_LEN] = collect_categories(&cat_count);
    StrBuf options;
    sb_init(&options);
    for (int i = 0; i < cat_count; i++)
    {
        sb_append(&options, "<option value=\"");
        sb_append_escaped(&options, cats[i]);
        sb_append(&options, "\"></option>");
    }
    free(cats);

    TemplateVar vars[] = {
        {"{{ID}}", id_out}, {"{{NAME}}", safe_name}, {"{{CATEGORY}}", safe_category},
        {"{{PRICE}}", price_out}, {"{{STOCK}}", stock_out},
        {"{{CATEGORY_OPTIONS}}", options.data ? options.data : ""}};

    char *body = render_file("edit_form.html", vars, 6);
    sb_free(&options);

    if (!body)
    {
        mg_http_reply(c, 500, "Content-Type: text/plain\r\n", "Missing edit_form.html");
        return;
    }

    send_page(c, 200, "Edit Product", body);
    free(body);
}

// POST /edit - validates every field on the server, then saves. Only a real
// stock change is written to the stock history; renaming a product or
// changing its price/category must not look like a stock movement.
static void edit_product(struct mg_connection *c, struct mg_http_message *hm)
{
    char id_str[20];
    char name[300], category[300], price_str[60], stock_str[40];
    int id;
    char back_url[40];

    if (mg_http_get_var(&hm->body, "id", id_str, sizeof(id_str)) <= 0 || !parse_int_value(id_str, &id))
    {
        send_message(c, 400, "Invalid Product ID", "Choose a product from the product list.", "/products", "View Products");
        return;
    }

    snprintf(back_url, sizeof(back_url), "/edit?id=%d", id);

    Product *p = find_product(id);
    if (p == NULL)
    {
        send_message(c, 404, "Product Not Found", "No product with that ID exists.", "/products", "View Products");
        return;
    }

    if (mg_http_get_var(&hm->body, "name", name, sizeof(name)) <= 0)
        name[0] = '\0'; // validate_product_fields() reports "name cannot be empty"
    if (mg_http_get_var(&hm->body, "category", category, sizeof(category)) <= 0)
        category[0] = '\0';
    if (mg_http_get_var(&hm->body, "price", price_str, sizeof(price_str)) <= 0)
        price_str[0] = '\0';
    if (mg_http_get_var(&hm->body, "stock", stock_str, sizeof(stock_str)) <= 0)
        stock_str[0] = '\0';

    double price;
    int stock;
    const char *problem = validate_product_fields(name, category, price_str, stock_str, &price, &stock);
    if (problem)
    {
        send_message(c, 400, "Could not update product", problem, back_url, "Back to the edit form");
        return;
    }

    Product before = *p;

    // Lengths were checked by validate_product_fields().
    snprintf(p->name, sizeof(p->name), "%.*s", NAME_LEN - 1, name);
    snprintf(p->category, sizeof(p->category), "%.*s", CATEGORY_LEN - 1, category);
    p->price = price;
    p->stock = stock;

    if (!save_products())
    {
        *p = before;
        send_message(c, 500, "Error", "Could not save the changes to the database.", back_url, "Back to the edit form");
        return;
    }

    if (before.stock != p->stock)
        log_stock_change(p->id, p->name, before.stock, p->stock);

    send_message(c, 200, "Product updated successfully!",
                 "The product details have been saved.", "/products", "View Products");
}

// =========================
// DELETE PRODUCTS (one, several, or all shown)
// =========================

static void delete_product_page(struct mg_connection *c)
{
    send_static_page(c, "Delete Product", "delete_form.html");
}

// Reads every "id=<number>" pair from a form body or query string (the same
// name can appear many times, once per ticked checkbox). Duplicates are
// ignored. *invalid is set if any value is not a proper number or there are
// more IDs than the inventory can hold.
static int parse_selected_ids(struct mg_str text, int *ids, int max_ids, int *invalid)
{
    int count = 0;
    size_t i = 0;
    *invalid = 0;

    while (i < text.len)
    {
        size_t start = i;
        while (i < text.len && text.buf[i] != '&')
            i++;
        size_t pair_len = i - start;
        if (i < text.len)
            i++; // skip '&'

        const char *pair = text.buf + start;
        if (pair_len < 3 || pair[0] != 'i' || pair[1] != 'd' || pair[2] != '=')
            continue;

        char value[24];
        size_t value_len = pair_len - 3;
        int id;
        if (value_len == 0 || value_len >= sizeof(value))
        {
            *invalid = 1;
            continue;
        }
        memcpy(value, pair + 3, value_len);
        value[value_len] = '\0';

        if (!parse_int_value(value, &id))
        {
            *invalid = 1;
            continue;
        }

        int duplicate = 0;
        for (int k = 0; k < count && !duplicate; k++)
            duplicate = ids[k] == id;
        if (duplicate)
            continue;

        if (count >= max_ids)
        {
            *invalid = 1;
            break;
        }
        ids[count++] = id;
    }
    return count;
}

// Shared by "Delete" on a single row, "Delete selected", and the old
// delete-by-ID form. Nothing is deleted until the user presses the
// confirmation button, and the server re-checks every ID itself: if any
// selected ID does not exist, nothing at all is deleted.
static void delete_products_request(struct mg_connection *c, struct mg_http_message *hm, int from_post)
{
    int ids[MAX_PRODUCTS];
    int invalid = 0;
    int count = parse_selected_ids(from_post ? hm->body : hm->query, ids, MAX_PRODUCTS, &invalid);

    if (invalid)
    {
        send_message(c, 400, "Invalid selection", "The product selection was not valid. Nothing was deleted.", "/products", "Back to products");
        return;
    }

    if (count == 0)
    {
        send_message(c, 400, "Nothing selected", "Please tick at least one product to delete.", "/products", "Back to products");
        return;
    }

    // Every ID must match a real product.
    for (int k = 0; k < count; k++)
    {
        if (find_product(ids[k]) == NULL)
        {
            send_message(c, 404, "Product Not Found",
                         "One or more selected products do not exist. Nothing was deleted.",
                         "/products", "Back to products");
            return;
        }
    }

    char confirm[10] = "";
    int confirmed = from_post &&
                    mg_http_get_var(&hm->body, "confirm", confirm, sizeof(confirm)) > 0 &&
                    strcmp(confirm, "1") == 0;

    if (!confirmed)
    {
        // Step 1: ask "Are you sure?" and list exactly what will be removed.
        StrBuf list, hidden;
        sb_init(&list);
        sb_init(&hidden);

        for (int k = 0; k < count; k++)
        {
            Product *p = find_product(ids[k]);
            sb_appendf(&list, "<li><span class=\"confirm-id\">#%d</span> ", p->id);
            sb_append_escaped(&list, p->name);
            sb_append(&list, " <span class=\"muted\">(");
            sb_append_escaped(&list, p->category);
            sb_appendf(&list, ", stock %d)</span></li>", p->stock);
            sb_appendf(&hidden, "<input type=\"hidden\" name=\"id\" value=\"%d\">", p->id);
        }

        char count_str[20];
        snprintf(count_str, sizeof(count_str), "%d", count);

        TemplateVar vars[] = {
            {"{{COUNT}}", count_str},
            {"{{PLURAL}}", count == 1 ? "" : "s"},
            {"{{LIST}}", list.data ? list.data : ""},
            {"{{HIDDEN}}", hidden.data ? hidden.data : ""}};

        char *body = render_file("delete_confirm.html", vars, 4);
        sb_free(&list);
        sb_free(&hidden);

        if (!body)
        {
            mg_http_reply(c, 500, "Content-Type: text/plain\r\n", "Missing delete_confirm.html");
            return;
        }
        send_page(c, 200, "Confirm Delete", body);
        free(body);
        return;
    }

    // Step 2: confirmed. Work on a copy so everything can be undone if the
    // database write fails.
    Product *backup = malloc(sizeof(products));
    if (!backup)
    {
        send_message(c, 500, "Error", "Not enough memory to delete safely.", "/products", "Back to products");
        return;
    }
    memcpy(backup, products, sizeof(products));
    int backup_count = product_count;

    // Remember what is deleted so it can be logged after the save succeeds.
    Product *deleted = malloc(sizeof(Product) * (size_t)count);
    if (!deleted)
    {
        free(backup);
        send_message(c, 500, "Error", "Not enough memory to delete safely.", "/products", "Back to products");
        return;
    }
    int deleted_count = 0;
    int kept = 0;

    for (int i = 0; i < product_count; i++)
    {
        int selected = 0;
        for (int k = 0; k < count && !selected; k++)
            selected = products[i].id == ids[k];

        if (selected)
            deleted[deleted_count++] = products[i];
        else
            products[kept++] = products[i];
    }
    product_count = kept;

    if (!save_products())
    {
        memcpy(products, backup, sizeof(products));
        product_count = backup_count;
        free(backup);
        free(deleted);
        send_message(c, 500, "Error", "Could not save the deleted product state. Nothing was deleted.", "/products", "Back to products");
        return;
    }

    // Same stock-history entry the single delete always wrote.
    for (int k = 0; k < deleted_count; k++)
        log_stock_change(deleted[k].id, deleted[k].name, deleted[k].stock, 0);

    free(backup);
    free(deleted);

    char msg[100];
    if (deleted_count == 1)
        snprintf(msg, sizeof(msg), "1 product has been removed.");
    else
        snprintf(msg, sizeof(msg), "%d products have been removed.", deleted_count);

    send_message(c, 200, "Product deleted successfully!", msg, "/products", "View Products");
}

// POST /delete (the original "delete by ID" form) now uses the same safe flow.
static void delete_product(struct mg_connection *c, struct mg_http_message *hm)
{
    delete_products_request(c, hm, 1);
}

static void route_delete_selected_get(struct mg_connection *c, struct mg_http_message *hm)
{
    delete_products_request(c, hm, 0);
}

static void route_delete_selected_post(struct mg_connection *c, struct mg_http_message *hm)
{
    delete_products_request(c, hm, 1);
}

static void check_low_stock(struct mg_connection *c)
{
    StrBuf rows;
    sb_init(&rows);
    int found = 0;

    for (int i = 0; i < product_count; i++)
    {
        if (products[i].stock <= LOW_STOCK_LIMIT)
        {
            sb_appendf(&rows, "<tr><td data-label=\"ID\">%d</td><td data-label=\"Name\" class=\"cell-name\">", products[i].id);
            sb_append_escaped(&rows, products[i].name);
            sb_appendf(&rows, "</td><td data-label=\"Stock\">%d</td></tr>", products[i].stock);
            found = 1;
        }
    }

    if (!found)
    {
        sb_append(&rows, "<tr><td colspan='3' class=\"empty-row\">No low stock products.</td></tr>");
    }

    char limit_str[10];
    snprintf(limit_str, sizeof(limit_str), "%d", LOW_STOCK_LIMIT);

    TemplateVar vars[] = {{"{{LIMIT}}", limit_str}, {"{{ROWS}}", rows.data ? rows.data : ""}};
    char *body = render_file("low_stock.html", vars, 2);
    sb_free(&rows);

    if (!body)
    {
        mg_http_reply(c, 500, "Content-Type: text/plain\r\n", "Missing low_stock.html");
        return;
    }

    send_page(c, 200, "Low Stock", body);
    free(body);
}

static int is_post(struct mg_http_message *hm)
{
    return hm->method.len == 4 && strncmp(hm->method.buf, "POST", 4) == 0;
}

typedef void (*handler_fn)(struct mg_connection *, struct mg_http_message *);

static void route_home(struct mg_connection *c, struct mg_http_message *hm)
{
    (void)hm;
    show_main_menu(c);
}
static void route_add_get(struct mg_connection *c, struct mg_http_message *hm)
{
    (void)hm;
    add_product_page(c);
}
static void route_products(struct mg_connection *c, struct mg_http_message *hm)
{
    view_products(c, hm);
}
static void route_stock_history(struct mg_connection *c, struct mg_http_message *hm)
{
    (void)hm;
    view_stock_history(c);
}
static void route_update_get(struct mg_connection *c, struct mg_http_message *hm)
{
    (void)hm;
    update_stock_page(c);
}
static void route_delete_get(struct mg_connection *c, struct mg_http_message *hm)
{
    (void)hm;
    delete_product_page(c);
}
static void route_low_stock(struct mg_connection *c, struct mg_http_message *hm)
{
    (void)hm;
    check_low_stock(c);
}

typedef struct
{
    const char *uri;
    handler_fn get_handler;
    handler_fn post_handler;
    int is_public; // 1 = reachable without being logged in
} Route;

static Route routes[] = {
    {"/login", route_login_get, route_login_post, 1},

    // Password recovery by emailed link (the old recovery-PIN routes are gone).
    {"/forgot-password",
     route_forgot_password_get,
     route_forgot_password_post,
     1},

    {"/reset-password",
     route_reset_password_get,
     route_reset_password_post,
     1},

    {"/change-password", route_change_password_get, route_change_password_post, 0},

    {"/logout", logout, NULL, 1},

    {"/", route_home, NULL, 0},
    {"/style.css", serve_css, NULL, 1},
    {"/IMAHE/images2.jpg", serve_image, NULL, 1},
    {"/add", route_add_get, add_product, 0},
    {"/products", route_products, NULL, 0},
    {"/stock-history", route_stock_history, NULL, 0},
    {"/generate-stock-history-pdf", route_stock_history_pdf, NULL, 0},
    {"/stock_history_report.pdf", serve_stock_history_pdf, NULL, 0},
    {"/search", search_product, NULL, 0},
    {"/update", route_update_get, update_stock, 0},
    {"/edit", route_edit_get, edit_product, 0},
    {"/delete", route_delete_get, delete_product, 0},
    {"/delete-selected", route_delete_selected_get, route_delete_selected_post, 0},
    {"/low-stock", route_low_stock, NULL, 0}};

static void fn(struct mg_connection *c, int ev, void *ev_data)
{
    if (ev != MG_EV_HTTP_MSG)
        return;

    struct mg_http_message *hm = (struct mg_http_message *)ev_data;

    for (size_t i = 0; i < sizeof(routes) / sizeof(routes[0]); i++)
    {
        if (mg_strcmp(hm->uri, mg_str(routes[i].uri)) == 0)
        {
            DEBUG_LOG("ROUTE: matched %s (%s)", routes[i].uri, is_post(hm) ? "POST" : "GET");

            // Each request carries its own session cookie, so this check
            // is per-browser, not a single global switch for the server.
            if (!routes[i].is_public && current_user(hm) == NULL)
            {
                DEBUG_LOG("ACCESS DENIED: User is not logged in.");
                mg_http_reply(c, 302, "Location: /login\r\n", "");
                return;
            }

            if (is_post(hm) && routes[i].post_handler != NULL)
            {
                routes[i].post_handler(c, hm);
            }
            else if (routes[i].get_handler != NULL)
            {
                routes[i].get_handler(c, hm);
            }
            else
            {
                mg_http_reply(c, 405, "Content-Type: text/plain\r\n", "Method not allowed");
            }

            return;
        }
    }

    DEBUG_LOG("ROUTE: no match for requested URI");

    send_message(c, 404, "404 - Page Not Found", "", "/", "Return to Main Menu");
}

int main(void)
{
    struct mg_mgr mgr;

    // Flush each line right away so messages show up in a redirected log too.
    setvbuf(stdout, NULL, _IOLBF, 0);

    DEBUG_LOG("Server starting...");

    if (!init_database())
    {
        printf("[ERROR] Database initialization failed. Server will not start.\n");
        return 1;
    }

    if (!load_products())
    {
        printf("[ERROR] Could not load products from SQLite.\n");
        sqlite3_close(db);
        db = NULL;
        return 1;
    }

    mg_mgr_init(&mgr);

    if (mg_http_listen(&mgr, "http://0.0.0.0:8080", fn, NULL) == NULL)
    {
        printf("[ERROR] Could not start the HTTP server on port 8080.\n");
        mg_mgr_free(&mgr);
        sqlite3_close(db);
        db = NULL;
        return 1;
    }

    printf("C server is running!\n");
    printf("Open: http://localhost:8080\n");

    while (1)
    {
        mg_mgr_poll(&mgr, 1000);
    }

    mg_mgr_free(&mgr);
    sqlite3_close(db);
    db = NULL;

    return 0;
}