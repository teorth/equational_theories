#include <stdio.h>
#include <stdlib.h>
#include <stdbool.h>
#include <string.h>
#include <inttypes.h>
#include "header.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdbool.h>
#include <openssl/md5.h>

extern FunctionPtr* functions;
extern int* nvar_list;
extern void setup();


bool check_rule(int nvar, FunctionPtr fn, int* table) {
    int max_combinations = 1 << (2 * nvar);

    #if N == 4
    if (!fn(table, 0x6789)) {
      return false;
    }
    #endif

    for (int combination = 0; combination < max_combinations; combination++) {
      #if N == 3
      if ((combination & (combination>>1)) & 0x5555555) continue;
      #endif
      #if N == 2
      if ((combination) & 0xaaaaaaa) continue;
      #endif
      fflush(stdout);
        if (!fn(table, combination)) {
            return false;
        }
    }
    
    return true;
}

bool next_table(int* table) {
    for (int i = TABLE_SIZE - 1; i >= 0; i--) {
        if (table[i] < N - 1) {
            table[i]++;
            return true;
        }
        table[i] = 0;
    }
    return false; // No more tables
}

void print_table(int* table) {
    for (int i = 0; i < N; i++) {
        for (int j = 0; j < N; j++) {
            printf("%d ", table[i * N + j]);
        }
        printf("\n");
    }
    printf("\n");
}


void initialize_random_table(int* table) {
    for (int i = 0; i < TABLE_SIZE; i++) {
        table[i] = rand() % N;
    }
}


#define HASH_TABLE_SIZE 10000019 // A prime number larger than MAX_TABLES


void md5_hash(int *array, int size, char *output) {
    MD5_CTX ctx;
    unsigned char digest[MD5_DIGEST_LENGTH];
    
    MD5_Init(&ctx);
    MD5_Update(&ctx, array, size * sizeof(int));
    MD5_Final(digest, &ctx);
    
    for (int i = 0; i < MD5_DIGEST_LENGTH; i++) {
        sprintf(&output[i*2], "%02x", (unsigned int)digest[i]);
    }
}

typedef struct {
    char hash[33];
    int table_number;
    int count;
    bool occupied;
} HashTableEntry;

unsigned long hash_function(const char *str) {
    unsigned long hash = 5381;
    int c;
    while ((c = *str++))
        hash = ((hash << 5) + hash) + c; // hash * 33 + c
    return hash;
}

int find_or_insert(HashTableEntry *hash_table, const char *hash, int table_number) {
    unsigned long index = hash_function(hash) % HASH_TABLE_SIZE;
    int original_index = index;
    
    while (hash_table[index].occupied) {
        if (strcmp(hash_table[index].hash, hash) == 0) {
  	    hash_table[index].count += 1;
            return hash_table[index].table_number; // Hash already exists
        }
        index = (index + 1) % HASH_TABLE_SIZE;
        if (index == original_index) {
            fprintf(stderr, "Hash table is full\n");
            exit(1);
        }
    }
    
    // Insert new entry
    strcpy(hash_table[index].hash, hash);
    hash_table[index].table_number = table_number;
    hash_table[index].count = 0;
    hash_table[index].occupied = true;
    return -1; // Indicates a new entry
}

void skip_to_table(int *table, int64_t target_index) {
    for (int64_t i = 0; i < target_index; i++) {
        next_table(table);
    }
}

int main(int argc, char *argv[]) {
    if (argc != 3) {
        fprintf(stderr, "Usage: %s <start_index> <end_index>\n", argv[0]);
        return 1;
    }

    int64_t start_index = atoll(argv[1]);
    int64_t end_index = atoll(argv[2]);

    if (start_index < 0 || end_index < start_index) {
        fprintf(stderr, "Invalid start or end index\n");
        return 1;
    }

    setup();
    int table[TABLE_SIZE] = {0}; // Start with all zeros
    int ok[NUM_FUNCTIONS];
    int ok_count;
    char filename[100];
    char hash[33]; // 32 characters for MD5 hash + null terminator
    FILE *file;

    // Initialize hash table
    HashTableEntry *hash_table = calloc(HASH_TABLE_SIZE, sizeof(HashTableEntry));
    if (hash_table == NULL) {
        fprintf(stderr, "Memory allocation failed\n");
        return 1;
    }

    int unique_count = 0;

    // Skip to the start index
    skip_to_table(table, start_index);

    for (int64_t table_count = start_index; table_count <= end_index; table_count++) {
        ok_count = 0;
        for (int i = 0; i < NUM_FUNCTIONS; i++) {
            if (check_rule(nvar_list[i], functions[i], table)) {
                ok[ok_count++] = i;
            }
        }

        // Generate MD5 hash of ok array
        md5_hash(ok, ok_count, hash);

        // Check if we've seen this hash before and insert if new
        int existing_table = find_or_insert(hash_table, hash, table_count);

        if (existing_table == -1) {
            // New unique hash
            unique_count++;

            // Create a new file with the hash as the name
            snprintf(filename, sizeof(filename), "tables/table_%s.txt", hash);
            file = fopen(filename, "w");
            if (file == NULL) {
                fprintf(stderr, "Error opening file %s\n", filename);
                free(hash_table);
                exit(1);
            }

            fprintf(file, "Table %ld [", table_count);
            for (int j = 0; j < ok_count; j++) {
                fprintf(file, "%d", ok[j]);
                if (j < ok_count - 1) fprintf(file, ", ");
            }
            fprintf(file, "]\n");

            fclose(file);
        }

        if (table_count < end_index && !next_table(table)) {
            fprintf(stderr, "Reached end of tables before end_index\n");
            break;
        }
    }

    printf("Processed tables from %ld to %ld\n", start_index, end_index);
    printf("Unique hashes: %d\n", unique_count);

    // Dump the table-hash pairs
    snprintf(filename, sizeof(filename), "table_hash_pairs_%ld.txt", start_index);
    file = fopen(filename, "w");
    if (file == NULL) {
        fprintf(stderr, "Error opening table_hash_pairs.txt\n");
        free(hash_table);
        return 1;
    }

    for (int i = 0; i < HASH_TABLE_SIZE; i++) {
        if (hash_table[i].occupied) {
            fprintf(file, "Table %d: %s %d\n", hash_table[i].table_number,
		    hash_table[i].hash,
		    hash_table[i].count);
        }
    }

    fclose(file);
    free(hash_table);

    return 0;
}
