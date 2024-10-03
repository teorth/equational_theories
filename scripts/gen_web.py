import json
import numpy as np
#"""
f = json.load(open("../out.json"))

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

r = np.zeros((4694, 4694))
for i,row in enumerate(outcomes):
    for j,col in enumerate(row):
        r[order[i]-1, order[j]-1] = ids[col]

np.save('/tmp/a.npy', r)
#"""

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

n = np.array(np.load("/tmp/a.npy"), dtype=np.uint8)

from PIL import Image
#n = n!=8
#n = n[:, np.argsort(np.sum(n, 0))]
#n = n[np.argsort(np.sum(n, 1)), :]
#Image.fromarray(255*np.array(n, dtype=np.uint8)).save("a.png")
#exit(0)


print("var arr = ",rle_encode(n.flatten().tolist()));

eqs = []
N = 0
for line in open("../equational_theories/AllEquations.lean"):
    if ':=' in line:
        N += 1
        eqs.append("Equation"+str(N)+"["+line.split(":=")[1].strip()+"]")
print("var equations = ", eqs);

special = []
for line in open("../equational_theories/Equations.lean"):
    if line.startswith("abbrev Equation"):
        special.append(line.split()[1])
print("var special = ", special)
