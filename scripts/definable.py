import json
import numpy as np

with open('imps.json', 'r') as file:
    imps_data = json.load(file)["implications"] #Don't need the non-implications

with open('./data/duals.json', 'r') as file:
    duals_data = json.load(file)

N_eq=4694

#Store the implications as (4694+1)x(4694+1) array of bools. The extra 1 is to avoid array indexing
#accidents here, since all our other data is 1-indexed
imp_mat = np.eye(1+N_eq, dtype=np.bool)
for imp in imps_data:
    lhs = int(imp["lhs"][len("Equation"):])
    rhs = int(imp["rhs"][len("Equation"):])
    if lhs >= N_eq or rhs >= N_eq: #skip sporadics
        continue
    imp_mat[lhs,rhs] = True

#Given an array of relations, get the transitive closure and equivalence class list
def close_and_get_equivs(rel_mat):
    #Compute the transitive closure by repeated squaring
    orig_mat = [0]
    while np.sum(orig_mat) != np.sum(rel_mat):
        orig_mat = rel_mat
        rel_mat = np.dot(rel_mat, rel_mat)
        print(".")
    #Compute equivalence classes
    equivs_rels = rel_mat * rel_mat.T
    #Compute which are equivalence representatives
    is_equivs_rels = np.where(np.sum(np.triu(equivs_rels,k=1),axis=0) == 0)[0][1:]
    return (rel_mat, equivs_rels, is_equivs_rels)

#Compute equivalence classes
imp_mat, equivs_imps, is_equivs_imps = close_and_get_equivs(imp_mat)
print(len(is_equivs_imps), "equivalence classes when implications are considered")

### Term structural implications
termstruct_mat = np.copy(imp_mat)

#All duals are term-structural for each other
for (eq, eq_dual) in duals_data:
    termstruct_mat[eq, eq_dual] = True
    termstruct_mat[eq_dual, eq] = True

#Compute the closure and equivalence classes
termstruct_mat, equivs_termstruct, is_equivs_termstruct = close_and_get_equivs(termstruct_mat)
print(len(is_equivs_termstruct), "equivalence classes when term structural relations are considered")


#### Term definable implications
termdef_mat = np.copy(termstruct_mat)

#The left projection law is term definable from anything
termdef_mat[1:,4] = True

#Equation46_termDefinableFrom_equalShape (constant law)
for lhs in [40,4276,4308,4336,4355]:
    termdef_mat[lhs,46] = True

#Equation43_termDefinableFrom_swapped_args (commutative law)
for lhs in [40,4343,4293,4321]:
    termdef_mat[lhs,43] = True

#Tarski 543: Commutative and associative laws are term definable from 543
termdef_mat[543,43] = True
termdef_mat[543,4512] = True

#Compute the closure and equivalence classes
termdef_mat, equivs_termdef, is_equivs_termdef = close_and_get_equivs(termdef_mat)
print(len(is_equivs_termdef), "equivalence classes when term definable relations are considered")



#### Structural implications
struct_mat = np.copy(termstruct_mat)

#Tarski 543: Commutative and associative laws are structural from 543
struct_mat[543,43] = True
struct_mat[543,4512] = True

#Compute the closure and equivalence classes
struct_mat, equivs_struct, is_equivs_struct = close_and_get_equivs(struct_mat)
print(len(is_equivs_struct), "equivalence classes when structural relations are considered")


#### Definable implications
def_mat = struct_mat + termdef_mat

def_mat, equivs_def, is_equivs_def = close_and_get_equivs(def_mat)
print(len(is_equivs_def), "equivalence classes when definable relations are considered")
