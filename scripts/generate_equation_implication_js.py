import json
import os
import sys

#"""
f = json.load(open(sys.argv[1]))

outcomes = f['outcomes']

ids = ["explicit_conjecture_false",
       "explicit_conjecture_true",
       "explicit_proof_false",
       "explicit_proof_true",
       "implicit_conjecture_false",
       "implicit_conjecture_true",
       "implicit_proof_false",
       "implicit_proof_true",
       "unknown"]

ids = {x: i for i,x in enumerate(ids)}

reorder = f['equations']
order = [int(x[8:]) for x in reorder]
            

#print(ids)

# Initialize a 4694x4694 matrix with zeros using list comprehensions
n = [[0 for _ in range(4694)] for _ in range(4694)]

for i, row in enumerate(outcomes):
    for j, col in enumerate(row):
        if order[i] <= 4694 and order[j] <= 4694:
            n[order[i] - 1][order[j] - 1] = ids[col]

def rle_encode(data):
    if not data:
        return []

    encoded = []
    count = 1
    current = data[0]

    for item in data[1:]:
        if item == current:
            count += 1
        else:
            encoded.extend((current, count))
            current = item
            count = 1

    encoded.extend((current, count))
    return encoded

def find_equivalence_classes_fast(implications):
    # Convert implications to adjacency matrix
    # Assuming implications is a list of lists or similar iterable structure
    n_nodes = len(implications)
    adj_matrix = [[False for _ in range(n_nodes)] for _ in range(n_nodes)]

    for i in range(n_nodes):
        for j in range(n_nodes):
            if implications[i][j] in {1, 3, 5, 7}:
                adj_matrix[i][j] = True

    # Set diagonal to True (each node implies itself)
    for i in range(n_nodes):
        adj_matrix[i][i] = True

    # Keep only mutual implications
    for i in range(n_nodes):
        for j in range(n_nodes):
            if adj_matrix[i][j] and adj_matrix[j][i]:
                adj_matrix[i][j] = True
            else:
                adj_matrix[i][j] = False

    # Find equivalence classes
    unassigned = set(range(n_nodes))
    equivalence_classes = []

    while unassigned:
        node = unassigned.pop()
        # Find all nodes connected to 'node'
        equivalence_class = set()
        for j in range(n_nodes):
            if adj_matrix[node][j]:
                equivalence_class.add(j)
        equivalence_classes.append(sorted(equivalence_class))
        unassigned -= equivalence_class

    return equivalence_classes

if not os.path.exists("home_page/implications"):
    os.mkdir("home_page/implications")
        
sys.stdout = open("home_page/implications/implications.js","w")

flattened_list = [item for sublist in n for item in sublist]
encoded = rle_encode(flattened_list)
print("var arr = ",encoded)

eqs = []
N = 0
for line in open("equational_theories/AllEquations.lean"):
    if ':=' in line:
        N += 1
        eqs.append("Equation"+str(N)+"["+line.split(":=")[1].strip()+"]")
print("var equations = ", eqs);

special = []
for line in open("equational_theories/Equations.lean"):
    if line.startswith("equation") and ':=' in line:
        special.append(line.split()[1])
print("var special = ", special)

print("var equiv = " + str(find_equivalence_classes_fast(n)))

print("var duals = ", open("data/duals.json").read())

