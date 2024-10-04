import numpy as np
import json
import argparse
import subprocess
from collections import defaultdict
from scipy.sparse import csr_matrix
from scipy.sparse.csgraph import connected_components
from itertools import combinations

def load_data_from_lean():
    try:
        result = subprocess.run(["lake", "exe", "extract_implications", "outcomes"], 
                                capture_output=True, text=True, check=True)
        return json.loads(result.stdout)
    except subprocess.CalledProcessError as e:
        return None

def preprocess_data(data):
    outcomes = data['outcomes']
    reorder = data['equations']
    order = [int(x[8:]) for x in reorder]
    
    ids = ["explicit_conjecture_false", "explicit_conjecture_true",
           "explicit_proof_false", "explicit_proof_true",
           "implicit_conjecture_false", "implicit_conjecture_true",
           "implicit_proof_false", "implicit_proof_true", "unknown"]
    ids = {x: i for i, x in enumerate(ids)}


    n = 4694
    r = np.zeros((n, n))
    for i, row in enumerate(outcomes):
        for j, col in enumerate(row):
            if order[i] <= 4694 and order[j] <= 4694:
                r[order[i]-1, order[j]-1] = ids[col]
    
    ok = (r == 1) | (r == 3) | (r == 5) | (r == 7)
    no = (r == 0) | (r == 2) | (r == 4) | (r == 6)
    matrix = ok + no * 2
    
    return matrix

def find_most_useful_implication(matrix, k, one_per_equiv_class=True):
    n = matrix.shape[0]
    known_implications = csr_matrix((matrix == 1).astype(int))
    n_components, labels = connected_components(known_implications, directed=True, connection='strong')
    component_sizes = np.bincount(labels)
    component_to_nodes = [np.where(labels == i)[0] for i in range(n_components)]
    
    component_pairs = sorted(
        combinations(range(n_components), 2),
        key=lambda pair: component_sizes[pair[0]] * component_sizes[pair[1]],
        reverse=True
    )
    
    top_implications = []
    
    for comp1, comp2 in component_pairs:
        nodes1 = component_to_nodes[comp1]
        nodes2 = component_to_nodes[comp2]
        submatrix = matrix[np.ix_(nodes1, nodes2)]
        unknown_mask = (submatrix == 0)
        
        if np.any(unknown_mask):
            unknown_indices = np.argwhere(unknown_mask)
            value = component_sizes[comp1] * component_sizes[comp2]
            
            for i, j in unknown_indices:
                actual_i, actual_j = nodes1[i], nodes2[j]
                top_implications.append(((actual_i, actual_j), value))
                
                if len(top_implications) == k:
                    return top_implications
                
                if one_per_equiv_class:
                    break
    
    return top_implications

def main():
    parser = argparse.ArgumentParser(description="Find the most useful implications in a matrix.")
    parser.add_argument("--topk", type=int, default=1, help="Return the k best theorems to prove")
    parser.add_argument("--one-per-equiv", action="store_true", help="Return only one per equivalence class")
    parser.add_argument("--load-cache", type=str, help="Load output from the cache file")
    parser.add_argument("--save-cache", type=str, help="Save the output to a cache file")
    
    args = parser.parse_args()
    
    if args.load_cache:
        with open(args.load_cache, 'rb') as f:
            matrix = np.load(f)
    else:
        data = load_data_from_lean()
        if data is None:
            return
        matrix = preprocess_data(data)
        
        if args.save_cache:
            with open(args.save_cache, 'wb') as f:
                np.save(f, matrix)
    
    implications = find_most_useful_implication(matrix, args.topk, args.one_per_equiv)
    
    print("EquationA", "EquationB", "ValueOfAImpliesB")
    for (a, b), value in implications:
        print(a+1, b+1, value)

if __name__ == "__main__":
    main()
