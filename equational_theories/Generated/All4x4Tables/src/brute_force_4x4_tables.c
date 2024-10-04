#include <stdio.h>
#include <stdlib.h>
#include <stdbool.h>
#include <string.h>
#include <omp.h>
#include <stdint.h>
#include "header.h"

extern FunctionPtr* functions;
extern int* nvar_list;
extern void setup();

#define TABLE_SIZE (N * N)
#define BITS_PER_WORD 64
#define WORD_COUNT ((NUM_FUNCTIONS + BITS_PER_WORD - 1) / BITS_PER_WORD)
#define BLOOM_SIZE (1<<28)
#define BLOOM_WORDS (BLOOM_SIZE / BITS_PER_WORD)
#define NUM_PROBES 16
#define NUM_THREADS 1

volatile uint64_t unique_tables_found = 0;

typedef uint64_t word_t;

bool check_rule(int nvar, FunctionPtr fn, int* table) {
    int max_combinations = 1 << (2 * nvar);

    if (!fn(table, 0x2345)) {
      return false;
    }
    
    for (int combination = 0; combination < max_combinations; combination += 1) {
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

void print_result(int* table, word_t* ok, int ok_count) {
    printf("Table:\n");
    for (int i = 0; i < N; i++) {
        for (int j = 0; j < N; j++) {
            printf("%d ", table[i * N + j]);
        }
        printf("\n");
    }
    printf("\nSatisfied equations: ");
    bool first = true;
    for (int i = 0; i < NUM_FUNCTIONS; i++) {
        if ((ok[i / BITS_PER_WORD] >> (i % BITS_PER_WORD)) & 1) {
            if (!first) {
                printf(", ");
            }
            printf("%d", i);
            first = false;
        }
    }
    printf("\n\n");
}

uint64_t hash_function(word_t* ok, int seed) {
    uint64_t hash = seed;
    for (int i = 0; i < WORD_COUNT; i++) {
        hash ^= ok[i];
        hash *= 0x5bd1e995;
        hash ^= hash >> 15;
    }
    return hash;
}

bool check_and_set_bloom(word_t* bloom_filter, word_t* ok) {
    bool seen = true;
    for (int i = 0; i < NUM_PROBES; i++) {
        uint64_t hash = hash_function(ok, i) % BLOOM_SIZE;
        uint64_t word_index = hash / BITS_PER_WORD;
        uint64_t bit_index = hash % BITS_PER_WORD;
        
        if (!(bloom_filter[word_index] & (1ULL << bit_index))) {
            seen = false;
            bloom_filter[word_index] |= (1ULL << bit_index);
        }
    }
    return seen;
}

void start_table_at_index(int* table, uint64_t index) {
    for (uint64_t i = 0; i < index; i++) {
        next_table(table);
    }
}


int main() {
    setup();
    word_t* bloom_filter = malloc(sizeof(word_t)*BLOOM_WORDS);

    // Calculate total number of tables: N^(N*N)
    uint64_t total_tables = 1;
    for (int i = 0; i < TABLE_SIZE; i++) {
        total_tables *= N;
    }
    uint64_t tables_per_thread = total_tables / NUM_THREADS;

    #pragma omp parallel num_threads(NUM_THREADS)
    {
        int thread_id = omp_get_thread_num();
        uint64_t start_index = thread_id * tables_per_thread;
        uint64_t end_index = (thread_id == NUM_THREADS - 1) ? total_tables : (thread_id + 1) * tables_per_thread;
        uint64_t tables_to_check = end_index - start_index;
        uint64_t progress_step = tables_to_check / 1000; // 0.1% of tables for this thread

        int table[TABLE_SIZE] = {0};
        word_t ok[WORD_COUNT];
        int ok_count;

        // Brute force skip to the starting table
        start_table_at_index(table, start_index);

        for (uint64_t current_index = start_index; current_index < end_index/100000; current_index++) {
            ok_count = 0;
            memset(ok, 0, sizeof(ok)); // Reset all words

	    size_t main_loop_end = NUM_FUNCTIONS - (NUM_FUNCTIONS % BITS_PER_WORD);

	    // Main loop processing BITS_PER_WORD functions at a time
	    for (size_t i = 0; i < main_loop_end; i += BITS_PER_WORD) {
	      unsigned long long temp = 0;
    
	      for (int j = 0; j < BITS_PER_WORD; j++) {
		temp |= (unsigned long long)check_rule(nvar_list[i+j], functions[i+j], table) << j;
	      }

	      ok[i / BITS_PER_WORD] = temp;
	      ok_count += __builtin_popcountll(temp);
	    }

	    // Handle remaining functions
	    unsigned long long temp = 0;
	    for (size_t i = main_loop_end; i < NUM_FUNCTIONS; i++) {
	      temp |= (unsigned long long)check_rule(nvar_list[i], functions[i], table) << (i % BITS_PER_WORD);
	    }

	    if (main_loop_end < NUM_FUNCTIONS) {
	      ok[main_loop_end / UNROLL_FACTOR] = temp;
	      ok_count += __builtin_popcountll(temp);
	    }

            if (ok_count > 0 && !check_and_set_bloom(bloom_filter, ok)) {
                #pragma omp atomic
                unique_tables_found++;

                #pragma omp critical
                {
                    print_result(table, ok, ok_count);
                }
            }

            // Progress reporting
            if ((current_index - start_index + 1) % progress_step == 0) {
            #pragma omp critical
	    {
                int progress = (int)((current_index - start_index + 1) * 100 / tables_to_check);
                printf("ThreadID %d: status: %d%%\n", thread_id, progress);
	    }
            }

            // Thread 0 reports additional statistics
            if (thread_id == 0 && (current_index - start_index + 1) % progress_step == 0) {
                double bloom_filter_fullness = 0;
                for (int i = 0; i < BLOOM_WORDS; i++) {
                    bloom_filter_fullness += __builtin_popcountll(bloom_filter[i]);
                }
                bloom_filter_fullness /= BLOOM_SIZE;

            #pragma omp critical
	    {
                printf("Thread 0 Report:\n");
                printf("  Unique tables found: %lu\n", unique_tables_found);
                printf("  Bloom filter fullness: %.2f%%\n", bloom_filter_fullness * 100);
	    }
            }

            if (!next_table(table)) {
                break;
            }
        }
    }

    return 0;
}
