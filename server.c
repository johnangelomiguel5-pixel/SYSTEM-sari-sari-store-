#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <errno.h>
#include <limits.h>
#include <math.h>
#include <openssl/crypto.h>
#include <openssl/evp.h>
#include <openssl/rand.h>
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
#define MAX_SESSIONS 50
#define SESSION_TOKEN_LEN 33          // 32 hex chars + null
#define SESSION_LIFETIME_SECONDS 3600 // 1 hour

typedef struct
{
    char token[SESSION_TOKEN_LEN];
    char username[100];
    time_t expires;
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

// Generates a random session token as hex text.
static void generate_session_token(char *out)
{
    unsigned char raw[16];
    RAND_bytes(raw, sizeof(raw));
    for (int i = 0; i < 16; i++)
        sprintf(out + i * 2, "%02x", raw[i]);
}

// Starts a session for username and returns its token, or NULL if the
// session table is full (very unlikely at 50 slots for a school project).
static const char *create_session(const char *username)
{
    for (int i = 0; i < MAX_SESSIONS; i++)
    {
        if (!sessions[i].in_use || sessions[i].expires < time(NULL))
        {
            generate_session_token(sessions[i].token);
            snprintf(sessions[i].username, sizeof(sessions[i].username), "%s", username);
            sessions[i].expires = time(NULL) + SESSION_LIFETIME_SECONDS;
            sessions[i].in_use = 1;
            return sessions[i].token;
        }
    }
    return NULL;
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
// this particular browser has no valid session.
static const char *current_user(struct mg_http_message *hm)
{
    char token[SESSION_TOKEN_LEN];
    if (!get_cookie_value(hm, "session", token, sizeof(token)))
        return NULL;

    for (int i = 0; i < MAX_SESSIONS; i++)
    {
        if (sessions[i].in_use && strcmp(sessions[i].token, token) == 0)
        {
            if (sessions[i].expires < time(NULL))
            {
                sessions[i].in_use = 0;
                return NULL;
            }
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

    const char *admin_username = "admin";
    const char *admin_password = "admin123";
    const char *admin_recovery_pin = "123456";
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

    // Create the default admin password hash and separate salt.
    if (user_count == 0)
    {
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
    }
    else
    {
        DEBUG_LOG("Admin account already exists.");

        /*
         * Set the recovery PIN only if the admin account
         * does not already have one.
         *
         * The PIN is hashed using the same PBKDF2-SHA256
         * system used for passwords.
         */
        const char *check_pin_sql =
            "SELECT recovery_pin_hash FROM users WHERE username = ?;";

        if (sqlite3_prepare_v2(db, check_pin_sql, -1, &user_stmt, NULL) != SQLITE_OK)
        {
            printf("[ERROR] Could not check recovery PIN: %s\n",
                   sqlite3_errmsg(db));
            sqlite3_close(db);
            db = NULL;
            return 0;
        }

        sqlite3_bind_text(
            user_stmt,
            1,
            admin_username,
            -1,
            SQLITE_STATIC);

        int has_recovery_pin = 0;

        if (sqlite3_step(user_stmt) == SQLITE_ROW)
        {
            const unsigned char *existing_pin =
                sqlite3_column_text(user_stmt, 0);

            if (existing_pin != NULL &&
                strlen((const char *)existing_pin) > 0)
            {
                has_recovery_pin = 1;
            }
        }

        sqlite3_finalize(user_stmt);
        user_stmt = NULL;

        /*
         * Only create the PIN if one does not already exist.
         * This means the PIN does NOT expire and is NOT replaced
         * every time the server starts.
         */
        if (!has_recovery_pin)
        {
            char recovery_pin_hash[300];

            if (!hash_password(
                    admin_recovery_pin,
                    recovery_pin_hash,
                    sizeof(recovery_pin_hash),
                    NULL,
                    0))
            {
                DEBUG_LOG("ERROR: Could not hash recovery PIN.");
                sqlite3_close(db);
                db = NULL;
                return 0;
            }

            const char *update_pin_sql =
                "UPDATE users "
                "SET recovery_pin_hash = ? "
                "WHERE username = ?;";

            if (sqlite3_prepare_v2(
                    db,
                    update_pin_sql,
                    -1,
                    &user_stmt,
                    NULL) != SQLITE_OK)
            {
                printf("[ERROR] Could not prepare recovery PIN update: %s\n",
                       sqlite3_errmsg(db));
                sqlite3_close(db);
                db = NULL;
                return 0;
            }

            sqlite3_bind_text(
                user_stmt,
                1,
                recovery_pin_hash,
                -1,
                SQLITE_TRANSIENT);

            sqlite3_bind_text(
                user_stmt,
                2,
                admin_username,
                -1,
                SQLITE_STATIC);

            rc = sqlite3_step(user_stmt);

            if (rc != SQLITE_DONE)
            {
                printf("[ERROR] Could not save recovery PIN.\n");
                printf("[ERROR] SQLite message: %s\n",
                       sqlite3_errmsg(db));

                sqlite3_finalize(user_stmt);
                sqlite3_close(db);
                db = NULL;
                return 0;
            }

            sqlite3_finalize(user_stmt);
            user_stmt = NULL;

            DEBUG_LOG("Recovery PIN initialized.");
        }
        else
        {
            DEBUG_LOG("Recovery PIN already exists.");
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

static int read_file(const char *filename, char *out, size_t out_size)
{
    char path[256];
    snprintf(path, sizeof(path), "%s%s", PUBLIC_DIR, filename);

    FILE *f = fopen(path, "rb");
    if (!f)
    {
        DEBUG_LOG("read_file(): could not open %s", path);
        return -1;
    }

    size_t n = fread(out, 1, out_size - 1, f);
    out[n] = '\0';
    fclose(f);
    return (int)n;
}

typedef struct
{
    const char *key;
    const char *value;
} TemplateVar;

static void render_template(const char *tmpl, const TemplateVar *vars, int var_count, char *out, size_t out_size)
{
    size_t written = 0;
    const char *src = tmpl;

    while (*src && written + 1 < out_size)
    {
        int matched = 0;

        for (int i = 0; i < var_count; i++)
        {
            size_t key_len = strlen(vars[i].key);
            if (strncmp(src, vars[i].key, key_len) == 0)
            {
                size_t val_len = strlen(vars[i].value);
                if (val_len > out_size - written - 1)
                    val_len = out_size - written - 1;
                memcpy(out + written, vars[i].value, val_len);
                written += val_len;
                src += key_len;
                matched = 1;
                break;
            }
        }

        if (!matched)
            out[written++] = *src++;
    }
    out[written] = '\0';
}

static void send_page(struct mg_connection *c, int status, const char *title, const char *body_html)
{
    char shell[2000];
    char final_html[30000];

    if (read_file("page.html", shell, sizeof(shell)) < 0)
    {
        mg_http_reply(c, 500, "Content-Type: text/plain\r\n", "Missing page.html template");
        return;
    }

    TemplateVar vars[] = {{"{{TITLE}}", title}, {"{{BODY}}", body_html}};
    render_template(shell, vars, 2, final_html, sizeof(final_html));
    mg_http_reply(c, status, "Content-Type: text/html\r\n", "%s", final_html);
}

static void send_static_page(struct mg_connection *c, const char *title, const char *filename)
{
    char body[4000];
    if (read_file(filename, body, sizeof(body)) < 0)
    {
        mg_http_reply(c, 500, "Content-Type: text/plain\r\n", "Missing %s", filename);
        return;
    }
    send_page(c, 200, title, body);
}

static void send_message(struct mg_connection *c, int status, const char *title, const char *message, const char *link_url, const char *link_text)
{
    char tmpl[1000];
    char body[2000];

    if (read_file("message.html", tmpl, sizeof(tmpl)) < 0)
    {
        mg_http_reply(c, 500, "Content-Type: text/plain\r\n", "Missing message.html");
        return;
    }

    TemplateVar vars[] = {
        {"{{TITLE}}", title}, {"{{MESSAGE}}", message}, {"{{LINK_URL}}", link_url}, {"{{LINK_TEXT}}", link_text}};

    render_template(tmpl, vars, 4, body, sizeof(body));
    send_page(c, status, title, body);
}

static void serve_css(struct mg_connection *c, struct mg_http_message *hm)
{
    (void)hm;
    char css[15000];
    if (read_file("style.css", css, sizeof(css)) < 0)
    {
        mg_http_reply(c, 404, "Content-Type: text/plain\r\n", "style.css not found");
        return;
    }
    mg_http_reply(c, 200, "Content-Type: text/css\r\n", "%s", css);
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
// GENERATE STOCK HISTORY PDF
// =========================

// Creates a PDF report containing the stock history records.
static int generate_stock_history_pdf(void)
{

    // Create a new PDF document.
    HPDF_Doc pdf = HPDF_New(pdf_error_handler, NULL);

    // Check if the PDF document was created successfully.
    if (!pdf)
    {
        printf("Failed to create PDF document.\n");
        return 0;
    }

    // Create the first A4 page.
    HPDF_Page page = HPDF_AddPage(pdf);

    // Set the page to A4 portrait orientation.
    HPDF_Page_SetSize(page, HPDF_PAGE_SIZE_A4, HPDF_PAGE_PORTRAIT);

    // Get the page dimensions.
    float page_width = HPDF_Page_GetWidth(page);
    float page_height = HPDF_Page_GetHeight(page);

    // Load the standard Helvetica fonts.
    HPDF_Font title_font = HPDF_GetFont(pdf, "Helvetica-Bold", NULL);
    HPDF_Font normal_font = HPDF_GetFont(pdf, "Helvetica", NULL);

    // Draw the report title.
    HPDF_Page_BeginText(page);
    HPDF_Page_SetFontAndSize(page, title_font, 18);
    HPDF_Page_TextOut(page, 50, page_height - 50,
                      "Sari-Sari Store - Stock History Report");
    HPDF_Page_EndText(page);

    // Draw the report description.
    HPDF_Page_BeginText(page);
    HPDF_Page_SetFontAndSize(page, normal_font, 9);
    HPDF_Page_TextOut(page, 50, page_height - 70,
                      "Stock changes recorded by the inventory system.");
    HPDF_Page_EndText(page);

    // Open the stock history query.
    sqlite3_stmt *stmt = NULL;

    const char *sql =
        "SELECT timestamp, product_id, product_name, old_stock, new_stock "
        "FROM stock_history "
        "ORDER BY history_id ASC;";

    // Prepare the SQLite statement.
    if (sqlite3_prepare_v2(db, sql, -1, &stmt, NULL) != SQLITE_OK)
    {

        printf("Failed to prepare stock history PDF query: %s\n",
               sqlite3_errmsg(db));

        HPDF_Free(pdf);
        return 0;
    }

    // Starting vertical position for the table.
    float y = page_height - 110;

    // Column positions.
    float x_date = 50;
    float x_id = 165;
    float x_product = 200;
    float x_old = 370;
    float x_new = 420;
    float x_change = 470;

    // Draw the table header.
    HPDF_Page_BeginText(page);
    HPDF_Page_SetFontAndSize(page, title_font, 9);

    HPDF_Page_TextOut(page, x_date, y, "Date & Time");
    HPDF_Page_TextOut(page, x_id, y, "ID");
    HPDF_Page_TextOut(page, x_product, y, "Product");
    HPDF_Page_TextOut(page, x_old, y, "Old");
    HPDF_Page_TextOut(page, x_new, y, "New");
    HPDF_Page_TextOut(page, x_change, y, "Change");

    HPDF_Page_EndText(page);

    // Move below the table header.
    y -= 20;

    // Count the number of records.
    int history_count = 0;

    // Read every stock history record.
    while (sqlite3_step(stmt) == SQLITE_ROW)
    {

        // Get values from the current SQLite row.
        const char *timestamp =
            (const char *)sqlite3_column_text(stmt, 0);

        int product_id =
            sqlite3_column_int(stmt, 1);

        const char *product_name =
            (const char *)sqlite3_column_text(stmt, 2);

        int old_stock =
            sqlite3_column_int(stmt, 3);

        int new_stock =
            sqlite3_column_int(stmt, 4);

        // Calculate the stock change.
        int change = new_stock - old_stock;

        // Create text buffers for numeric values.
        char id_text[20];
        char old_text[20];
        char new_text[20];
        char change_text[20];

        snprintf(id_text, sizeof(id_text), "%d", product_id);
        snprintf(old_text, sizeof(old_text), "%d", old_stock);
        snprintf(new_text, sizeof(new_text), "%d", new_stock);
        snprintf(change_text, sizeof(change_text), "%+d", change);

        // Check if there is enough space for another row.
        if (y < 60)
        {

            // Create a new page.
            page = HPDF_AddPage(pdf);

            // Set the new page to A4 portrait.
            HPDF_Page_SetSize(page,
                              HPDF_PAGE_SIZE_A4,
                              HPDF_PAGE_PORTRAIT);

            // Get the new page height.
            page_height = HPDF_Page_GetHeight(page);

            // Reset the vertical position.
            y = page_height - 50;

            // Draw the table header again.
            HPDF_Page_BeginText(page);
            HPDF_Page_SetFontAndSize(page, title_font, 9);

            HPDF_Page_TextOut(page, x_date, y, "Date & Time");
            HPDF_Page_TextOut(page, x_id, y, "ID");
            HPDF_Page_TextOut(page, x_product, y, "Product");
            HPDF_Page_TextOut(page, x_old, y, "Old");
            HPDF_Page_TextOut(page, x_new, y, "New");
            HPDF_Page_TextOut(page, x_change, y, "Change");

            HPDF_Page_EndText(page);

            y -= 20;
        }

        // Draw the current stock history row.
        HPDF_Page_BeginText(page);
        HPDF_Page_SetFontAndSize(page, normal_font, 8);

        HPDF_Page_TextOut(page, x_date, y,
                          timestamp ? timestamp : "");

        HPDF_Page_TextOut(page, x_id, y, id_text);

        HPDF_Page_TextOut(page, x_product, y,
                          product_name ? product_name : "");

        HPDF_Page_TextOut(page, x_old, y, old_text);
        HPDF_Page_TextOut(page, x_new, y, new_text);
        HPDF_Page_TextOut(page, x_change, y, change_text);

        HPDF_Page_EndText(page);

        // Move down to the next row.
        y -= 16;

        // Increase the record counter.
        history_count++;
    }

    // Finish the SQLite query.
    sqlite3_finalize(stmt);

    // Show a message when there are no history records.
    if (history_count == 0)
    {

        HPDF_Page_BeginText(page);
        HPDF_Page_SetFontAndSize(page, normal_font, 10);

        HPDF_Page_TextOut(page, 50, y,
                          "No stock history records found.");

        HPDF_Page_EndText(page);
    }

    // Save the PDF to the project folder.
    HPDF_STATUS save_status =
        HPDF_SaveToFile(pdf, PDF_REPORT_FILE);

    // Free the PDF document from memory.
    HPDF_Free(pdf);

    // Check whether saving was successful.
    if (save_status != HPDF_OK)
    {

        printf("Failed to save PDF report.\n");
        return 0;
    }

    // Report success in the terminal.
    printf("Stock history PDF created: %s\n",
           PDF_REPORT_FILE);

    return 1;
}

// =========================
// STOCK HISTORY PDF ROUTE
// =========================

// Handles the request to generate the stock history PDF.
static void route_stock_history_pdf(struct mg_connection *c,
                                    struct mg_http_message *hm)
{

    // Generate the PDF report first.
    if (generate_stock_history_pdf())
    {

        // Open the HTML report result page.
        FILE *file = fopen("public/stock_history_report.html", "rb");

        // Check if the HTML file was found.
        if (file == NULL)
        {

            // Show an error if the HTML page cannot be opened.
            mg_http_reply(
                c,
                500,
                "Content-Type: text/plain\r\n",
                "Stock history PDF was generated, "
                "but the report HTML page could not be opened.");

            return;
        }

        // Find the size of the HTML file.
        fseek(file, 0, SEEK_END);
        long file_size = ftell(file);
        fseek(file, 0, SEEK_SET);

        // Allocate memory for the HTML page.
        char *html = malloc((size_t)file_size + 1);

        // Check whether memory was allocated successfully.
        if (html == NULL)
        {

            // Close the file before returning.
            fclose(file);

            // Report the memory error.
            mg_http_reply(
                c,
                500,
                "Content-Type: text/plain\r\n",
                "Failed to allocate memory for the report page.");

            return;
        }

        // Read the HTML file into memory.
        size_t bytes_read =
            fread(html, 1, (size_t)file_size, file);

        // Close the HTML file.
        fclose(file);

        // Add the string terminator.
        html[bytes_read] = '\0';

        // Send the HTML page to the browser.
        mg_http_reply(
            c,
            200,
            "Content-Type: text/html; charset=utf-8\r\n",
            "%s",
            html);

        // Free the HTML memory.
        free(html);
    }
    else
    {

        // PDF generation failed.
        mg_http_reply(
            c,
            500,
            "Content-Type: text/plain\r\n",
            "Failed to generate stock history PDF. "
            "Check the server terminal for more information.");
    }

    // Prevent unused parameter warning.
    (void)hm;
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

static void html_escape(const char *in, char *out, size_t out_size)
{
    size_t j = 0;
    for (size_t i = 0; in[i] && j + 6 < out_size; i++)
    {
        const char *rep =
            in[i] == '&' ? "&amp;" : in[i] == '<' ? "&lt;"
                                 : in[i] == '>'   ? "&gt;"
                                 : in[i] == '"'   ? "&quot;"
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

static void format_history_row(const char *timestamp, int id, const char *name, int old_stock, int new_stock, char *out, size_t out_size)
{
    char safe_name[300];
    html_escape(name, safe_name, sizeof(safe_name));

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

    snprintf(out, out_size,
             "<tr><td>%s</td><td>%d</td><td>%s</td><td>%d</td><td>%d</td><td><span class=\"badge %s\">%s %d</span></td></tr>",
             timestamp, id, safe_name, old_stock, new_stock, badge_class, arrow, new_stock - old_stock);
}

static void build_stock_history_rows(char *rows, size_t rows_size)
{
    rows[0] = '\0';

    const char *sql =
        "SELECT timestamp, product_id, product_name, old_stock, new_stock FROM stock_history ORDER BY history_id DESC LIMIT ?;";

    sqlite3_stmt *stmt = NULL;
    int rc = sqlite3_prepare_v2(db, sql, -1, &stmt, NULL);

    if (rc != SQLITE_OK)
    {
        printf("[ERROR] Could not read stock history: %s\n", sqlite3_errmsg(db));
        strncat(rows, "<tr><td colspan='6'>Could not load stock history.</td></tr>", rows_size - strlen(rows) - 1);
        return;
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

        char row[600];
        format_history_row(timestamp ? timestamp : "", id, name ? name : "", old_stock, new_stock, row, sizeof(row));
        strncat(rows, row, rows_size - strlen(rows) - 1);
        line_count++;
    }

    sqlite3_finalize(stmt);

    if (rc != SQLITE_DONE)
    {
        printf("[ERROR] Could not finish stock history query: %s\n", sqlite3_errmsg(db));
    }

    if (line_count == 0)
    {
        strncat(rows, "<tr><td colspan='6'>No stock changes recorded yet.</td></tr>", rows_size - strlen(rows) - 1);
    }
}

// Sends login.html completely as-is -- no page.html shell, no sidebar,
// since login.html is already a full standalone <html> document and an
// unauthenticated visitor should never see the app's nav anyway.
// Fills in {{ERROR}} so a failed login attempt can actually show a message.
static void login_page(struct mg_connection *c, const char *error_message)
{
    char tmpl[4000];
    char body[4200];

    if (read_file("login.html", tmpl, sizeof(tmpl)) < 0)
    {
        mg_http_reply(c, 500, "Content-Type: text/plain\r\n", "Missing login.html");
        return;
    }

    TemplateVar vars[] = {{"{{ERROR}}", error_message}};
    render_template(tmpl, vars, 1, body, sizeof(body));
    mg_http_reply(c, 200, "Content-Type: text/html\r\n", "%s", body);
}

static void recovery_page(
    struct mg_connection *c,
    const char *filename,
    const char *error_message,
    const char *username,
    const char *pin)
{
    char tmpl[7000];
    char body[8000];

    char safe_username[300];
    char safe_pin[100];

    html_escape(
        username ? username : "",
        safe_username,
        sizeof(safe_username));

    html_escape(
        pin ? pin : "",
        safe_pin,
        sizeof(safe_pin));

    if (read_file(filename, tmpl, sizeof(tmpl)) < 0)
    {
        mg_http_reply(
            c,
            500,
            "Content-Type: text/plain\r\n",
            "Missing %s",
            filename);
        return;
    }

    TemplateVar vars[] =
        {
            {"{{ERROR}}", error_message ? error_message : ""},
            {"{{USERNAME}}", safe_username},
            {"{{PIN}}", safe_pin}};

    render_template(
        tmpl,
        vars,
        3,
        body,
        sizeof(body));

    mg_http_reply(
        c,
        200,
        "Content-Type: text/html\r\n",
        "%s",
        body);
}

// =========================
// PASSWORD RECOVERY
// =========================

static void route_forgot_password_get(
    struct mg_connection *c,
    struct mg_http_message *hm)
{
    (void)hm;

    recovery_page(
        c,
        "forgot-password.html",
        "",
        "",
        "");
}

static void route_forgot_password_post(
    struct mg_connection *c,
    struct mg_http_message *hm)
{
    char username[100];
    sqlite3_stmt *stmt = NULL;

    username[0] = '\0';

    if (mg_http_get_var(
            &hm->body,
            "username",
            username,
            sizeof(username)) <= 0)
    {
        recovery_page(
            c,
            "forgot-password.html",
            "Please enter your username.",
            "",
            "");
        return;
    }

    const char *sql =
        "SELECT recovery_pin_hash "
        "FROM users "
        "WHERE username = ?;";

    if (sqlite3_prepare_v2(
            db,
            sql,
            -1,
            &stmt,
            NULL) != SQLITE_OK)
    {
        DEBUG_LOG(
            "ERROR: Could not prepare recovery username query: %s",
            sqlite3_errmsg(db));

        mg_http_reply(
            c,
            500,
            "Content-Type: text/plain\r\n",
            "Database error.");
        return;
    }

    sqlite3_bind_text(
        stmt,
        1,
        username,
        -1,
        SQLITE_STATIC);

    if (sqlite3_step(stmt) == SQLITE_ROW)
    {
        const unsigned char *pin_hash =
            sqlite3_column_text(stmt, 0);

        if (pin_hash != NULL &&
            strlen((const char *)pin_hash) > 0)
        {
            sqlite3_finalize(stmt);

            recovery_page(
                c,
                "recovery-pin.html",
                "",
                username,
                "");

            return;
        }
    }

    sqlite3_finalize(stmt);

    recovery_page(
        c,
        "forgot-password.html",
        "Username not found or recovery PIN is not configured.",
        username,
        "");
}

static void route_verify_recovery_pin(
    struct mg_connection *c,
    struct mg_http_message *hm)
{
    char username[100];
    char pin[100];

    sqlite3_stmt *stmt = NULL;
    char stored_pin_hash[400];

    username[0] = '\0';
    pin[0] = '\0';
    stored_pin_hash[0] = '\0';

    if (mg_http_get_var(
            &hm->body,
            "username",
            username,
            sizeof(username)) <= 0)
    {
        recovery_page(
            c,
            "forgot-password.html",
            "Invalid recovery request.",
            "",
            "");
        return;
    }

    if (mg_http_get_var(
            &hm->body,
            "pin",
            pin,
            sizeof(pin)) <= 0)
    {
        recovery_page(
            c,
            "recovery-pin.html",
            "Please enter your recovery PIN.",
            username,
            "");
        return;
    }

    const char *sql =
        "SELECT recovery_pin_hash "
        "FROM users "
        "WHERE username = ?;";

    if (sqlite3_prepare_v2(
            db,
            sql,
            -1,
            &stmt,
            NULL) != SQLITE_OK)
    {
        DEBUG_LOG(
            "ERROR: Could not prepare PIN query: %s",
            sqlite3_errmsg(db));

        mg_http_reply(
            c,
            500,
            "Content-Type: text/plain\r\n",
            "Database error.");
        return;
    }

    sqlite3_bind_text(
        stmt,
        1,
        username,
        -1,
        SQLITE_STATIC);

    if (sqlite3_step(stmt) == SQLITE_ROW)
    {
        const unsigned char *hash =
            sqlite3_column_text(stmt, 0);

        if (hash != NULL)
        {
            snprintf(
                stored_pin_hash,
                sizeof(stored_pin_hash),
                "%s",
                (const char *)hash);
        }
    }

    sqlite3_finalize(stmt);

    if (stored_pin_hash[0] == '\0' ||
        !verify_password(pin, stored_pin_hash))
    {
        DEBUG_LOG(
            "Failed recovery PIN attempt for: %s",
            username);

        recovery_page(
            c,
            "recovery-pin.html",
            "Incorrect recovery PIN.",
            username,
            "");

        return;
    }

    DEBUG_LOG(
        "Successful recovery PIN verification for: %s",
        username);

    /*
     * The PIN is intentionally passed to the next step.
     * The final password-change request verifies it again
     * before changing the password.
     */
    recovery_page(
        c,
        "reset-password.html",
        "",
        username,
        pin);
}

static void route_reset_password(
    struct mg_connection *c,
    struct mg_http_message *hm)
{
    char username[100];
    char pin[100];
    char new_password[200];
    char confirm_password[200];

    sqlite3_stmt *stmt = NULL;

    char stored_pin_hash[400];
    char new_password_hash[400];
    char new_salt_hex[100];

    username[0] = '\0';
    pin[0] = '\0';
    new_password[0] = '\0';
    confirm_password[0] = '\0';

    stored_pin_hash[0] = '\0';
    new_password_hash[0] = '\0';
    new_salt_hex[0] = '\0';

    if (mg_http_get_var(
            &hm->body,
            "username",
            username,
            sizeof(username)) <= 0)
    {
        recovery_page(
            c,
            "forgot-password.html",
            "Invalid recovery request.",
            "",
            "");
        return;
    }

    if (mg_http_get_var(
            &hm->body,
            "pin",
            pin,
            sizeof(pin)) <= 0)
    {
        recovery_page(
            c,
            "recovery-pin.html",
            "Invalid recovery request.",
            username,
            "");
        return;
    }

    if (mg_http_get_var(
            &hm->body,
            "new_password",
            new_password,
            sizeof(new_password)) <= 0)
    {
        recovery_page(
            c,
            "reset-password.html",
            "Please enter a new password.",
            username,
            pin);
        return;
    }

    if (mg_http_get_var(
            &hm->body,
            "confirm_password",
            confirm_password,
            sizeof(confirm_password)) <= 0)
    {
        recovery_page(
            c,
            "reset-password.html",
            "Please confirm your new password.",
            username,
            pin);
        return;
    }

    if (strlen(new_password) == 0)
    {
        recovery_page(
            c,
            "reset-password.html",
            "Password cannot be empty.",
            username,
            pin);
        return;
    }

    if (strcmp(new_password, confirm_password) != 0)
    {
        recovery_page(
            c,
            "reset-password.html",
            "Passwords do not match.",
            username,
            pin);
        return;
    }

    /*
     * Verify the recovery PIN again before changing
     * the password. This prevents someone from modifying
     * the hidden username field and bypassing the PIN.
     */
    const char *pin_sql =
        "SELECT recovery_pin_hash "
        "FROM users "
        "WHERE username = ?;";

    if (sqlite3_prepare_v2(
            db,
            pin_sql,
            -1,
            &stmt,
            NULL) != SQLITE_OK)
    {
        DEBUG_LOG(
            "ERROR: Could not prepare final PIN query: %s",
            sqlite3_errmsg(db));

        mg_http_reply(
            c,
            500,
            "Content-Type: text/plain\r\n",
            "Database error.");
        return;
    }

    sqlite3_bind_text(
        stmt,
        1,
        username,
        -1,
        SQLITE_STATIC);

    if (sqlite3_step(stmt) == SQLITE_ROW)
    {
        const unsigned char *hash =
            sqlite3_column_text(stmt, 0);

        if (hash != NULL)
        {
            snprintf(
                stored_pin_hash,
                sizeof(stored_pin_hash),
                "%s",
                (const char *)hash);
        }
    }

    sqlite3_finalize(stmt);
    stmt = NULL;

    if (stored_pin_hash[0] == '\0' ||
        !verify_password(pin, stored_pin_hash))
    {
        recovery_page(
            c,
            "recovery-pin.html",
            "Recovery PIN verification failed.",
            username,
            "");
        return;
    }

    /*
     * Generate a completely new password hash and salt.
     * The recovery PIN remains unchanged.
     */
    if (!hash_password(
            new_password,
            new_password_hash,
            sizeof(new_password_hash),
            new_salt_hex,
            sizeof(new_salt_hex)))
    {
        DEBUG_LOG(
            "ERROR: Could not hash new password.");

        mg_http_reply(
            c,
            500,
            "Content-Type: text/plain\r\n",
            "Could not create new password.");
        return;
    }

    const char *update_sql =
        "UPDATE users "
        "SET password_hash = ?, salt = ? "
        "WHERE username = ?;";

    if (sqlite3_prepare_v2(
            db,
            update_sql,
            -1,
            &stmt,
            NULL) != SQLITE_OK)
    {
        DEBUG_LOG(
            "ERROR: Could not prepare password update: %s",
            sqlite3_errmsg(db));

        mg_http_reply(
            c,
            500,
            "Content-Type: text/plain\r\n",
            "Database error.");
        return;
    }

    sqlite3_bind_text(
        stmt,
        1,
        new_password_hash,
        -1,
        SQLITE_TRANSIENT);

    sqlite3_bind_text(
        stmt,
        2,
        new_salt_hex,
        -1,
        SQLITE_TRANSIENT);

    sqlite3_bind_text(
        stmt,
        3,
        username,
        -1,
        SQLITE_STATIC);

    int rc = sqlite3_step(stmt);

    if (rc != SQLITE_DONE)
    {
        DEBUG_LOG(
            "ERROR: Could not update password: %s",
            sqlite3_errmsg(db));

        sqlite3_finalize(stmt);

        mg_http_reply(
            c,
            500,
            "Content-Type: text/plain\r\n",
            "Could not update password.");
        return;
    }

    sqlite3_finalize(stmt);

    DEBUG_LOG(
        "Password successfully reset for: %s",
        username);

    /*
     * Recovery PIN is intentionally NOT changed or deleted.
     * It can be used again later.
     */
    mg_http_reply(
        c,
        302,
        "Location: /login\r\n",
        "");
}
static void route_login_get(struct mg_connection *c, struct mg_http_message *hm)
{
    char error_flag[10];
    const char *error_message = "";

    if (mg_http_get_var(&hm->query, "error", error_flag, sizeof(error_flag)) > 0)
    {
        error_message = "Invalid username or password.";
    }

    login_page(c, error_message);
}

static void login_process(struct mg_connection *c, struct mg_http_message *hm)
{
    char username[100];
    char password[100];
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

                char cookie_header[100];
                snprintf(cookie_header, sizeof(cookie_header),
                         "Set-Cookie: session=%s; Path=/; HttpOnly\r\nLocation: /\r\n", token);
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

    char total_products_str[10];
    char low_stock_str[10];
    char total_value_str[30];
    char total_units_str[10];

    snprintf(total_products_str, sizeof(total_products_str), "%d", product_count);
    snprintf(low_stock_str, sizeof(low_stock_str), "%d", low_stock_count);
    snprintf(total_value_str, sizeof(total_value_str), "%.2f", total_value);
    snprintf(total_units_str, sizeof(total_units_str), "%d", total_units);

    static char history_rows[10000];
    build_stock_history_rows(history_rows, sizeof(history_rows));

    char tmpl[15000];
    static char body[30000];

    if (read_file("menu.html", tmpl, sizeof(tmpl)) < 0)
    {
        mg_http_reply(c, 500, "Content-Type: text/plain\r\n", "Missing menu.html");
        return;
    }

    TemplateVar vars[] = {
        {"{{TOTAL_PRODUCTS}}", total_products_str},
        {"{{LOW_STOCK_COUNT}}", low_stock_str},
        {"{{TOTAL_VALUE}}", total_value_str},
        {"{{TOTAL_UNITS}}", total_units_str},
        {"{{STOCK_HISTORY}}", history_rows}};

    render_template(tmpl, vars, 5, body, sizeof(body));
    send_page(c, 200, "Sari-Sari Store Inventory", body);
}

static void add_product_page(struct mg_connection *c)
{
    send_static_page(c, "Add Product", "add_form.html");
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
    char name[NAME_LEN];
    char category[CATEGORY_LEN];
    char price_str[30];
    char stock_str[20];

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

    // Create variables for the converted numeric values.
    int stock;
    double price;

    // Validate the price and stock values.
    if (!parse_double_value(price_str, &price) ||
        !parse_int_value(stock_str, &stock))
    {

        send_message(c, 400, "Error",
                     "Price and stock must be valid numbers.",
                     "/add", "Return");
        return;
    }

    // Generate the product ID automatically.
    int id = get_next_product_id();

    // Prevent negative price and stock values.
    if (stock < 0 || price < 0)
    {
        send_message(c, 400, "Error",
                     "Price and stock cannot be negative.",
                     "/add", "Return");
        return;
    }

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

static void view_products(struct mg_connection *c)
{
    char rows[8000] = "";

    for (int i = 0; i < product_count; i++)
    {
        char safe_name[300];
        char safe_category[200];
        char row[600];

        html_escape(products[i].name, safe_name, sizeof(safe_name));
        html_escape(products[i].category, safe_category, sizeof(safe_category));

        snprintf(row, sizeof(row), "<tr><td>%d</td><td>%s</td><td>%s</td><td>%.2f</td><td>%d</td></tr>",
                 products[i].id, safe_name, safe_category, products[i].price, products[i].stock);

        strncat(rows, row, sizeof(rows) - strlen(rows) - 1);
    }

    char tmpl[2000];
    char body[10000];

    if (read_file("products.html", tmpl, sizeof(tmpl)) < 0)
    {
        mg_http_reply(c, 500, "Content-Type: text/plain\r\n", "Missing products.html");
        return;
    }

    TemplateVar vars[] = {{"{{ROWS}}", rows}};
    render_template(tmpl, vars, 1, body, sizeof(body));
    send_page(c, 200, "View Products", body);
}

static void view_stock_history(struct mg_connection *c)
{
    static char rows[8000];
    build_stock_history_rows(rows, sizeof(rows));

    char tmpl[2000];
    char body[10000];

    if (read_file("stock_history.html", tmpl, sizeof(tmpl)) < 0)
    {
        mg_http_reply(c, 500, "Content-Type: text/plain\r\n", "Missing stock_history.html");
        return;
    }

    TemplateVar vars[] = {{"{{ROWS}}", rows}};
    render_template(tmpl, vars, 1, body, sizeof(body));
    send_page(c, 200, "Stock History", body);
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

    char safe_name[300];
    char safe_category[200];
    char id_out[20];
    char price_out[30];
    char stock_out[20];

    html_escape(p->name, safe_name, sizeof(safe_name));
    html_escape(p->category, safe_category, sizeof(safe_category));

    snprintf(id_out, sizeof(id_out), "%d", p->id);
    snprintf(price_out, sizeof(price_out), "%.2f", p->price);
    snprintf(stock_out, sizeof(stock_out), "%d", p->stock);

    char tmpl[1000];
    char body[2000];

    if (read_file("search_result.html", tmpl, sizeof(tmpl)) < 0)
    {
        mg_http_reply(c, 500, "Content-Type: text/plain\r\n", "Missing search_result.html");
        return;
    }

    TemplateVar vars[] = {
        {"{{ID}}", id_out}, {"{{NAME}}", safe_name}, {"{{CATEGORY}}", safe_category}, {"{{PRICE}}", price_out}, {"{{STOCK}}", stock_out}};

    render_template(tmpl, vars, 5, body, sizeof(body));
    send_page(c, 200, "Product Found", body);
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

static void delete_product_page(struct mg_connection *c)
{
    send_static_page(c, "Delete Product", "delete_form.html");
}

static void delete_product(struct mg_connection *c, struct mg_http_message *hm)
{
    char id_str[20];

    if (mg_http_get_var(&hm->body, "id", id_str, sizeof(id_str)) <= 0)
    {
        send_message(c, 400, "Error", "Product ID is required.", "/delete", "Return");
        return;
    }

    int id;
    if (!parse_int_value(id_str, &id))
    {
        send_message(c, 400, "Invalid Product ID", "Enter a numeric product ID.", "/delete", "Return");
        return;
    }
    int index = -1;

    for (int i = 0; i < product_count; i++)
    {
        if (products[i].id == id)
        {
            index = i;
            break;
        }
    }

    if (index == -1)
    {
        send_message(c, 404, "Product Not Found", "The product does not exist.", "/delete", "Return");
        return;
    }

    Product deleted = products[index];

    for (int i = index; i < product_count - 1; i++)
        products[i] = products[i + 1];

    product_count--;

    if (!save_products())
    {
        for (int i = product_count; i > index; i--)
            products[i] = products[i - 1];
        products[index] = deleted;
        product_count++;
        send_message(c, 500, "Error", "Could not save the deleted product state.", "/delete", "Return");
        return;
    }

    log_stock_change(deleted.id, deleted.name, deleted.stock, 0);

    char msg[100];
    snprintf(msg, sizeof(msg), "Product ID %d has been removed.", id);

    send_message(c, 200, "Product deleted successfully!", msg, "/products", "View Products");
}

static void check_low_stock(struct mg_connection *c)
{
    char rows[4000] = "";
    int found = 0;

    for (int i = 0; i < product_count; i++)
    {
        if (products[i].stock <= LOW_STOCK_LIMIT)
        {
            char safe_name[300];
            char row[400];
            html_escape(products[i].name, safe_name, sizeof(safe_name));
            snprintf(row, sizeof(row), "<tr><td>%d</td><td>%s</td><td>%d</td></tr>", products[i].id, safe_name, products[i].stock);
            strncat(rows, row, sizeof(rows) - strlen(rows) - 1);
            found = 1;
        }
    }

    if (!found)
    {
        strncat(rows, "<tr><td colspan='3'>No low stock products.</td></tr>", sizeof(rows) - strlen(rows) - 1);
    }

    char limit_str[10];
    snprintf(limit_str, sizeof(limit_str), "%d", LOW_STOCK_LIMIT);

    char tmpl[1000];
    char body[5200];

    if (read_file("low_stock.html", tmpl, sizeof(tmpl)) < 0)
    {
        mg_http_reply(c, 500, "Content-Type: text/plain\r\n", "Missing low_stock.html");
        return;
    }

    TemplateVar vars[] = {{"{{LIMIT}}", limit_str}, {"{{ROWS}}", rows}};
    render_template(tmpl, vars, 2, body, sizeof(body));
    send_page(c, 200, "Low Stock", body);
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
    (void)hm;
    view_products(c);
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

    {"/forgot-password",
     route_forgot_password_get,
     route_forgot_password_post,
     1},

    {"/verify-recovery-pin",
     NULL,
     route_verify_recovery_pin,
     1},

    {"/reset-password",
     NULL,
     route_reset_password,
     1},

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
    {"/delete", route_delete_get, delete_product, 0},
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