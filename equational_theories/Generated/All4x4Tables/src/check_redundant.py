import numpy as np
def parse_line(line):
    # Extract the list from the line using string manipulation
    try:
        return list(map(int, line.split('[')[1].split(']')[0].split(', ')))
    except:
        print("Failed on", line)
        return [0]

def prune_rows(matrix, lines, matrix_size=4696):
    useless = 0
    
    for i,line in enumerate(lines):
        L = parse_line(line)
        L_array = np.array(L)
        
        # Create a boolean mask for elements not in L
        mask = np.ones(matrix_size, dtype=bool)
        mask[L_array] = False
        
        # Use advanced indexing to set values
        if np.any(matrix[L_array[:, None], mask] == 0):
            matrix[L_array[:, None], mask] = True
        else:
            useless += 1
            
                
    return matrix, useless


def load(fpath):
    lines = []
    for line in open(fpath):
        if 'Proves' not in line:
            continue
        lines.append(line)
    return lines

for fp1 in ['../data/refutations2x2.txt',
           '../data/refutations3x3.txt',
           '../data/refutations4x4.txt']:
    for fp2 in ['../data/refutations2x2.txt',
               '../data/refutations3x3.txt',
               '../data/refutations4x4.txt']:
        if fp1 == fp2: continue
        matrix = np.zeros((4696, 4696), dtype=bool)
        matrix, useless = prune_rows(matrix, load(fp1))
        assert useless == 0
        init_found = np.sum(matrix)
        matrix, useless = prune_rows(matrix, load(fp2))
        after_found = np.sum(matrix)
        print("When going from", fp1, "to", fp2)
        print("The number of solved equtions goes from", init_found, "to", after_found,
              "for a delta of", after_found-init_found)
        print("And", fp2, "has", useless, '/', len(load(fp2)), "already covered magmas")
        print()
              
        
    
           
