#!/usr/bin/env python3

import utils
import os

equations_txt = open("equations.txt", "r").read().split("\n")[:-1]


def get_eq():
    """
    Parse the data out of the equations.txt file and turn it into trees
    """
    fns = []
    for eq in equations_txt:
        eq = eq.split("∀")[1]
        variables, eq = eq.split(":")
        variables = variables.strip().split()
        rule = eq.split(",")[1]
        fns.append((variables, utils.make_tree(rule)))

    return fns


equations = get_eq()

did = {}
remap_to_rule = {}

for i, (v_a, a) in enumerate(equations):
    print(i)
    for j, (v_b, b) in enumerate(equations):
        if i == j:
            continue

        remap = {}
        for chr1, chr2 in zip(str(a), str(b)):
            if chr1 != chr2:
                remap[chr1] = chr2
        if "(" in remap or " " in remap or ")" in remap:
            continue

        a_rename = a.rename(remap)
        if not utils.is_same_under_rewriting(a_rename, b):
            continue

        remapk = tuple(sorted(remap.items()))
        if remapk not in remap_to_rule:
            remap_to_rule[remapk] = []
        oo = (
            f"@[equational_result]\ntheorem Equation{i+1}_implies_Equation{j+1} (G : Type*) [Magma G] (h : Equation{i+1} G) : Equation{j+1} G := λ "
            + " ".join(v_b)
            + " => h "
            + " ".join([remap.get(x) or x for x in v_a])
        )
        remap_to_rule[remapk].append(oo)


if not os.path.exists("theorems"):
    os.makedirs("theorems")

for rule, outs in remap_to_rule.items():
    fname = "theorems/Rewrite_" + "_".join([f"{k}{v}" for k, v in rule]) + ".lean"
    proofs = "\n".join(outs)
    proofs = (
        """import Mathlib.Tactic
import equational_theories.Equations.All
import equational_theories.Magma

namespace SimpleRewrites

"""
        + proofs
        + "\nend SimpleRewrites"
    )
    open(fname, "w").write(proofs)
