#!/usr/bin/env python3

import sys
import numpy as np

if len(sys.argv) != 2:
    print("Provide the size of the magmas you want to process as an argument.")
    sys.exit(1)
N = int(sys.argv[1])

def to_table(packed_int):
    global N
    # Ensure the input is treated as an unsigned 64-bit integer
    packed_int = packed_int & 0xFFFFFFFFFFFFFFFF

    # Create the NxN table
    table = [[0 for _ in range(N)] for _ in range(N)]

    # Fill the table
    for i in range(N):
        for j in range(N):
            # Extract log2(K) bits for each cell, ensuring values in 0..K-1 range
            cell_value = (packed_int // (N ** (i * N + j))) % N
            table[i][j] = cell_value

    # Convert to numpy array and return flipped
    return np.array(table)[::-1, ::-1]


for line in open(f"data/covering_set_{N}x{N}.txt"):
    if 'Table' not in line: continue
    line = line.strip()
    parts = line.split('[')
    table_num = int(parts[0].split()[1])
    funcs_where_true = np.array(list(map(int, parts[1].strip(' ]').split(", "))))+1
    
    print("Table", to_table(table_num).tolist())
    print("Proves", list(funcs_where_true))
    print()
