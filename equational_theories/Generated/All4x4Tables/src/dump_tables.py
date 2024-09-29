import numpy as np

def to_table(packed_int):
    # Ensure the input is treated as an unsigned 64-bit integer
    packed_int = packed_int & 0xFFFFFFFFFFFFFFFF

    # Create the 4x4 table
    table = [[0 for _ in range(4)] for _ in range(4)]

    # Fill the table
    for i in range(4):
        for j in range(4):
            # Extract 2 bits for each cell
            cell_value = (packed_int >> (2 * (i * 4 + j))) & 0b11
            table[i][j] = cell_value

    # Print the table
    return np.array(table)[::-1,::-1]

for line in open("data/covering_set.txt"):
    if 'Table' not in line: continue
    line = line.strip()
    parts = line.split('[')
    table_num = int(parts[0].split()[1])
    funcs_where_true = np.array(list(map(int, parts[1].strip(' ]').split(", "))))+1
    
    print("Table", to_table(table_num).tolist())
    print("Proves", list(funcs_where_true))
    print()
