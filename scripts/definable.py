from pathlib import Path
import json
import numpy as np

ROOT = Path(__file__).resolve().parents[1]
BOOL = np.bool_


def close_and_get_equivs(rel_mat):
    # Compute the transitive closure by repeated squaring
    orig_mat = [0]
    while np.sum(orig_mat) != np.sum(rel_mat):
        orig_mat = rel_mat
        rel_mat = np.dot(rel_mat.astype(np.uint8), rel_mat.astype(np.uint8)) != 0
        print(".")
    # Compute equivalence classes
    equivs_rels = rel_mat * rel_mat.T
    # Compute which are equivalence representatives
    is_equivs_rels = np.where(np.sum(np.triu(equivs_rels, k=1), axis=0) == 0)[0][1:]
    return (rel_mat, equivs_rels, is_equivs_rels)


def load_implication_matrix():
    with open(ROOT / "imps.json", "r") as file:
        imps_data = json.load(file)["implications"]

    with open(ROOT / "data/duals.json", "r") as file:
        duals_data = json.load(file)

    with open(ROOT / "data/equations.txt", "r") as file:
        N_eq = sum(1 for line in file if line.strip())

    imp_mat = np.eye(1 + N_eq, dtype=BOOL)
    for imp in imps_data:
        lhs = int(imp["lhs"][len("Equation") :])
        rhs = int(imp["rhs"][len("Equation") :])
        if lhs > N_eq or rhs > N_eq:
            continue
        imp_mat[lhs, rhs] = True
    return imp_mat, duals_data, N_eq


def main():
    imp_mat, duals_data, N_eq = load_implication_matrix()
    del N_eq

    imp_mat, equivs_imps, is_equivs_imps = close_and_get_equivs(imp_mat)
    print(len(is_equivs_imps), "equivalence classes when implications are considered")

    termstruct_mat = np.copy(imp_mat)
    for eq, eq_dual in duals_data:
        termstruct_mat[eq, eq_dual] = True
        termstruct_mat[eq_dual, eq] = True

    termstruct_mat, equivs_termstruct, is_equivs_termstruct = close_and_get_equivs(
        termstruct_mat
    )
    print(
        len(is_equivs_termstruct),
        "equivalence classes when term structural relations are considered",
    )

    termdef_mat = np.copy(termstruct_mat)
    termdef_mat[1:, 4] = True
    for lhs in [40, 4276, 4308, 4336, 4355]:
        termdef_mat[lhs, 46] = True
    for lhs in [40, 4343, 4293, 4321]:
        termdef_mat[lhs, 43] = True
    termdef_mat[543, 43] = True
    termdef_mat[543, 4512] = True

    termdef_mat, equivs_termdef, is_equivs_termdef = close_and_get_equivs(termdef_mat)
    print(
        len(is_equivs_termdef),
        "equivalence classes when term definable relations are considered",
    )

    struct_mat = np.copy(termstruct_mat)
    struct_mat[543, 43] = True
    struct_mat[543, 4512] = True
    struct_mat, equivs_struct, is_equivs_struct = close_and_get_equivs(struct_mat)
    print(
        len(is_equivs_struct),
        "equivalence classes when structural relations are considered",
    )

    def_mat = struct_mat + termdef_mat
    def_mat, equivs_def, is_equivs_def = close_and_get_equivs(def_mat)
    print(len(is_equivs_def), "equivalence classes when definable relations are considered")


if __name__ == "__main__":
    main()
