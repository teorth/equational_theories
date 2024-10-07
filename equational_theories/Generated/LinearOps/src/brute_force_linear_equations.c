#include <stdio.h>
#include <stdlib.h>
#include <stdbool.h>
#include <string.h>
#include <omp.h>
#include <math.h>
#include <stdint.h>
#include "header.h"

extern FunctionPtr* functions;
extern int* nvar_list;
extern void setup();

#define USED_EQUATIONS 4694
//397

#define TABLE_SIZE (N * N)
#define BITS_PER_WORD 64
//#define WORD_COUNT ((NUM_FUNCTIONS + BITS_PER_WORD - 1) / BITS_PER_WORD)
#define WORD_COUNT ((USED_EQUATIONS + BITS_PER_WORD - 1) / BITS_PER_WORD)
#define BLOOM_SIZE (1<<28)
#define BLOOM_WORDS (BLOOM_SIZE / BITS_PER_WORD)
#define NUM_PROBES 8
#define NUM_THREADS 176


volatile uint64_t unique_tables_found = 0;

typedef uint64_t word_t;


bool check_rule(int nvar, FunctionPtr fn, int pk, int inv, int a, int b) {
    int v1, v2, v3, v4, v5, v6;

    switch (nvar) {
        case 1:
            for (v1 = 0; v1 < pk; v1++) {
                if (!fn(pk, inv, a, b, v1, 0, 0, 0, 0, 0)) return false;
            }
            break;

        case 2:
            for (v1 = 0; v1 < pk; v1++) {
                for (v2 = 0; v2 < pk; v2++) {
                    if (!fn(pk, inv, a, b, v1, v2, 0, 0, 0, 0)) return false;
                }
            }
            break;

        case 3:
            for (v1 = 0; v1 < pk; v1++) {
                for (v2 = 0; v2 < pk; v2++) {
                    for (v3 = 0; v3 < pk; v3++) {
                        if (!fn(pk, inv, a, b, v1, v2, v3, 0, 0, 0)) return false;
                    }
                }
            }
            break;

        case 4:
            for (v1 = 0; v1 < pk; v1++) {
                for (v2 = 0; v2 < pk; v2++) {
                    for (v3 = 0; v3 < pk; v3++) {
                        for (v4 = 0; v4 < pk; v4++) {
                            if (!fn(pk, inv, a, b, v1, v2, v3, v4, 0, 0)) return false;
                        }
                    }
                }
            }
            break;

        case 5:
            for (v1 = 0; v1 < pk; v1++) {
                for (v2 = 0; v2 < pk; v2++) {
                    for (v3 = 0; v3 < pk; v3++) {
                        for (v4 = 0; v4 < pk; v4++) {
                            for (v5 = 0; v5 < pk; v5++) {
                                if (!fn(pk, inv, a, b, v1, v2, v3, v4, v5, 0)) return false;
                            }
                        }
                    }
                }
            }
            break;

        case 6:
            for (v1 = 0; v1 < pk; v1++) {
                for (v2 = 0; v2 < pk; v2++) {
                    for (v3 = 0; v3 < pk; v3++) {
                        for (v4 = 0; v4 < pk; v4++) {
                            for (v5 = 0; v5 < pk; v5++) {
                                for (v6 = 0; v6 < pk; v6++) {
                                    if (!fn(pk, inv, a, b, v1, v2, v3, v4, v5, v6)) return false;
                                }
                            }
                        }
                    }
                }
            }
            break;

        default:
            // Handle invalid nvar values
            return false;
    }

    return true;
}


// Function to check if a number is prime
bool is_prime(int n) {
    // Handle edge cases
    if (n <= 1) {
        return false;
    }
    if (n <= 3) {
        return true;
    }
    // If the number is divisible by 2 or 3, it is not prime
    if (n % 2 == 0 || n % 3 == 0) {
        return false;
    }
    // Check from 5 to sqrt(n) in steps of 6 (i and i+2)
    for (int i = 5; i * i <= n; i += 6) {
        if (n % i == 0 || n % (i + 2) == 0) {
            return false;
        }
    }
    return true;
}

// Function to check if a number is a prime power
bool is_prime_power(int n) {
    if (n < 2) return false;
    for (int base = 2; base <= (int)sqrt(n); base++) {
        int power = 2;
        while (1) {
            int value = (int)pow(base, power);
            if (value == n) return is_prime(base);
            if (value > n || value < 0) break; // value < 0 handles overflow cases
            power++;
        }
    }
    return is_prime(n);
}

// Function to find the next prime power greater than n
int next_prime_power(int n) {
    n++;
    while (!is_prime_power(n)) {
        n++;
    }
    return n;
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

//int unsolved[USED_EQUATIONS] = {474-1, 2126-1, 1076-1, 2531-1, 1133-1, 1167-1, 1659-1, 1661-1, 1485-1, 481-1, 3161-1, 1648-1, 1924-1, 2712-1, 1701-1, 1839-1, 511-1, 3116-1, 1443-1, 2093-1, 1692-1, 1895-1, 477-1, 1112-1, 2460-1, 3150-1, 854-1, 1110-1, 2497-1, 65-1, 73-1, 261-1, 274-1, 680-1, 707-1, 2940-1, 2947-1, 1523-1, 2132-1, 504-1, 1117-1, 1289-1, 1722-1, 1925-1, 2338-1, 2538-1, 3143-1, 3588-1, 3994-1, 713-1, 2856-1, 883-1, 917-1, 2710-1, 2744-1, 1086-1, 2541-1, 704-1, 1518-1, 2054-1, 2903-1, 3342-1, 4167-1, 118-1, 229-1, 1431-1, 1526-1, 2040-1, 2101-1, 115-1, 219-1, 476-1, 503-1, 907-1, 1447-1, 2056-1, 2700-1, 3069-1, 3076-1, 1519-1, 2128-1, 1630-1, 1633-1, 1681-1, 1833-1, 1884-1, 1958-1, 1113-1, 1515-1, 1729-1, 1898-1, 2038-1, 2534-1, 3549-1, 3917-1, 464-1, 706-1, 1276-1, 1437-1, 1441-1, 1516-1, 2037-1, 2070-1, 2091-1, 2291-1, 3103-1, 3308-1, 4158-1, 714-1, 1323-1, 2304-1, 2507-1, 63-1, 124-1, 206-1, 271-1, 1491-1, 2061-1, 467-1, 670-1, 677-1, 879-1, 906-1, 1728-1, 1841-1, 2504-1, 2647-1, 2650-1, 2866-1, 2910-1, 2937-1, 3140-1, 3352-1, 3475-1, 3545-1, 3555-1, 3888-1, 4164-1, 3862-1, 3862-1, 3456-1, 1832-1, 1629-1, 3253-1, 4065-1, 1426-1, 2035-1, 411-1, 3050-1, 817-1, 2644-1, 614-1, 1020-1, 2441-1, 2847-1, 4435-1, 1223-1, 2238-1, 3319-1, 3522-1, 3915-1, 4118-1, 8-1, 23-1, 47-1, 151-1, 255-1, 3457-1, 3877-1, 4268-1, 4587-1, 99-1, 203-1, 307-1, 359-1, 3511-1, 3955-1, 1657-1, 1860-1, 4380-1, 1519-1, 2128-1, 1055-1, 1429-1, 2124-1, 2452-1, 1701-1, 1839-1, 1630-1, 1633-1, 1681-1, 1833-1, 1884-1, 1958-1, 152-1, 166-1, 1096-1, 1427-1, 1481-1, 1483-1, 1492-1, 1634-1, 1656-1, 1660-1, 1668-1, 1721-1, 1837-1, 1851-1, 2051-1, 2087-1, 3460-1, 3520-1, 3524-1, 3527-1, 3659-1, 3897-1, USED_EQUATIONS2-1, 4006-1, 4040-1, 4314-1, 4315-1, 4606-1, 4615-1, 513-1, 1035-1, 1428-1, 2050-1, 2443-1, 3079-1, 3519-1, 3925-1, 4269-1, 4584-1, 1133-1, 1167-1, 1659-1, 1661-1, 1485-1, 477-1, 1112-1, 2460-1, 3150-1, 1523-1, 2132-1, 883-1, 917-1, 2710-1, 2744-1, 1113-1, 1515-1, 1729-1, 1898-1, 2038-1, 2534-1, 714-1, 1323-1, 2304-1, 2507-1, 3-1, 125-1, 167-1, 168-1, 222-1, 326-1, 375-1, 910-1, 1025-1, 1085-1, 1316-1, 1479-1, 1480-1, 1484-1, 1488-1, 1496-1, 1631-1, 1655-1, 1695-1, 1847-1, 1897-1, 2041-1, 2052-1, 2088-1, 2089-1, 2446-1, 2467-1, 2737-1, 3258-1, 3458-1, 3512-1, 3513-1, 3521-1, 3523-1, 3525-1, 3715-1, 3722-1, 3867-1, 3918-1, 3935-1, 3952-1, 3989-1, 3993-1, 4067-1, 4273-1, 4470-1, 4588-1, 1486-1, 2126-1, 481-1, 3161-1, 1648-1, 1924-1, 511-1, 3116-1, 1692-1, 1895-1, 65-1, 73-1, 261-1, 274-1, 680-1, 707-1, 2940-1, 2947-1, 504-1, 1117-1, 1289-1, 1722-1, 1925-1, 2338-1, 2538-1, 3143-1, 3588-1, 3994-1, 1086-1, 2541-1, 118-1, 229-1, 1431-1, 1526-1, 2040-1, 2101-1, 3549-1, 3917-1, 63-1, 124-1, 206-1, 271-1, 1491-1, 2061-1, 107-1, 205-1, 211-1, 413-1, 414-1, 416-1, 466-1, 473-1, 880-1, 1023-1, 1045-1, 1075-1, 1109-1, 1248-1, 1251-1, 1313-1, 1478-1, 1482-1, 1489-1, 1647-1, 1685-1, 1922-1, 2036-1, 2098-1, 2125-1, 2240-1, 2246-1, 2266-1, 2294-1, 2444-1, 2449-1, 2457-1, 2459-1, 2462-1, 2530-1, 2707-1, 3055-1, 3056-1, 3065-1, 3066-1, 3068-1, 3139-1, 3316-1, 3472-1, 3878-1, 4128-1, 4270-1, 4590-1};

void print_result(int pk, int a, int b, word_t* ok, int ok_count) {
  printf("Variables %d %d %d", pk, a, b);
    printf("\nSatisfied equations: ");
    bool first = true;
    for (int i = 0; i < USED_EQUATIONS; i++) {
        if ((ok[i / BITS_PER_WORD] >> (i % BITS_PER_WORD)) & 1) {
            if (!first) {
                printf(", ");
            }
            //printf("%d", unsolved[i]);
            printf("%d", i);
            first = false;
        }
    }
    printf("\n\n");
    fflush(stdout);
}

/*
int64_t mod(int64_t x, int64_t q, int64_t y) {
  return x%y;
}

int64_t MOD2(int64_t x, int64_t inv, int64_t pk) {
  const uint64_t reciprocal = inv;  // Precomputed value (2^32 / 47)
  printf("input %ld %ld\n", x, reciprocal);
  x = abs(x);
  int64_t product = ((u_int64_t)x * reciprocal) >> 32;  // Multiply and shift
  int64_t out = x - product * pk;  // Correct the result
  printf("Out %ld %ld\n", out, mod(x, 0, pk));
  return out == pk ? 0 : out;
}
*/

int main() {
    setup();
    word_t* bloom_filter = malloc(sizeof(word_t)*BLOOM_WORDS);

    /*
    int inverse_for_div = (int)((1L << 32) / (long)11);    
    printf("check_rule(%d, %d, %d, %d, %d, %d)\n", nvar_list[473], 0, 11, inverse_for_div, 10, 2);
    printf("%d\n", check_rule(nvar_list[473], my, 11, inverse_for_div, 10, 2));

    exit(0);
    //*/

    {


	int current_prime_power = 2;

	while (current_prime_power < 320) {
	  printf("Loop %d\n", current_prime_power);
	  #pragma omp parallel for schedule(dynamic)
	  //for (int const_a = 0; const_a < current_prime_power; const_a++) {
	  //for (int const_b = 0; const_b < current_prime_power; const_b++) {
	  for (int dual = 0; dual < current_prime_power*current_prime_power; dual++) {
	  //for (int dual = 123; dual < 144; dual++) {

	    int inverse_for_div = (int)((1L << 32) / (long)current_prime_power);
	    
	    int const_a = dual/current_prime_power;
	    int const_b = dual%current_prime_power;

	    #pragma omp critical
	    {
	      //printf("Try %d %d %d (from %d)\n", current_prime_power, const_a, const_b, dual);
	    }

	    
	      word_t ok[WORD_COUNT];
	      int ok_count;
	      ok_count = 0;
	      memset(ok, 0, sizeof(ok)); // Reset all words

	      size_t main_loop_end = USED_EQUATIONS - (USED_EQUATIONS % BITS_PER_WORD);

	      // Main loop processing BITS_PER_WORD functions at a time
	      for (size_t i = 0; i < main_loop_end; i += BITS_PER_WORD) {
		unsigned long long temp = 0;
		
		for (int j = 0; j < BITS_PER_WORD; j++) {
		  //bool bit_ok = check_rule(nvar_list[unsolved[i+j]], functions[unsolved[i+j]], current_prime_power, inverse_for_div, const_a, const_b);
		  bool bit_ok = check_rule(nvar_list[i+j], functions[i+j], current_prime_power, inverse_for_div, const_a, const_b);		  
		  temp |= (unsigned long long)bit_ok << j;
		}
		
		ok[i / BITS_PER_WORD] = temp;
		ok_count += __builtin_popcountll(temp);
	      }
	      
	      // Handle remaining functions
	      unsigned long long temp = 0;
	      for (size_t i = main_loop_end; i < USED_EQUATIONS; i++) {
		//temp |= (unsigned long long)check_rule(nvar_list[unsolved[i]], functions[unsolved[i]], current_prime_power, inverse_for_div, const_a, const_b) << (i % BITS_PER_WORD);
		temp |= (unsigned long long)check_rule(nvar_list[i], functions[i], current_prime_power, inverse_for_div, const_a, const_b) << (i % BITS_PER_WORD);
	      }


	      if (main_loop_end < NUM_FUNCTIONS) {
		ok[main_loop_end / BITS_PER_WORD] = temp;
		ok_count += __builtin_popcountll(temp);
	      }

	      /*
              #pragma omp critical
	      {
		printf("OK %d: ", ok_count);
		for (int i = 0; i < WORD_COUNT; i++) {
		  printf("%lx ", ok[i]);
		}
		printf("\n");
	      }
	      */
	      
	      if (ok_count > 0 && !check_and_set_bloom(bloom_filter, ok)) {
#pragma omp atomic
                unique_tables_found++;

#pragma omp critical
                {
		  print_result(current_prime_power, const_a, const_b, ok, ok_count);
                }
	      }


	    #pragma omp critical
	    {
	      //printf("Done %d %d %d (from %d)\n", current_prime_power, const_a, const_b, dual);
	    }
	      /*
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
	      */
	      

	  }
	  
	  current_prime_power = next_prime_power(current_prime_power);
	}
    }

    return 0;
}
