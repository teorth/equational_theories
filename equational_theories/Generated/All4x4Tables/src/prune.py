import numpy as np
import os
import random

def parse_line(line):
    # Extract the list from the line using string manipulation
    try:
        return list(map(int, line.split('[')[1].split(']')[0].split(', ')))
    except:
        print("Failed on", line)
        return [0]

def prune_rows(lines, matrix_size=4696):
    matrix = np.zeros((matrix_size, matrix_size), dtype=bool)

    random.shuffle(lines)
    keep = []
    for i,line in enumerate(lines):
        L = parse_line(line)
        L_array = np.array(L)
        
        # Create a boolean mask for elements not in L
        mask = np.ones(matrix_size, dtype=bool)
        mask[L_array] = False
        
        # Use advanced indexing to set values
        if np.any(matrix[L_array[:, None], mask] == 0):
            matrix[L_array[:, None], mask] = True
            keep.append(line)
                
    return matrix, keep

def trim(lines):
    """
    Compute an approximate covering set. Each table gives a set of refutations. 
    Repeatedly do the following:
      1. Randomly shuffle the table order
      2. Process the tables in linear order and drop those that don't add new rules
      3. Any time it doesn't improve things, increment a counter
      4. If we've made no progress 10 times, then call it "good enough"
    """
    print("Start with", len(lines))
    matrix, lines = prune_rows(lines)
    identity_count = 0
    while identity_count < 10:
        print("Current round", len(lines), np.mean(matrix))
        matrix2, lines2 = prune_rows(lines)
        assert np.all(matrix2 == matrix)
        if len(lines2) == len(lines):
            identity_count += 1
        lines = lines2
    return matrix, lines

print("Reading files...")
lines = []
fp = "tables"
for f in os.listdir(fp):
    lines.extend(open(os.path.join(fp,f)).readlines())

print("Trimming...")
matrix, lines = trim(lines)

print("Covering set")
for line in lines:
    print(line)
    
