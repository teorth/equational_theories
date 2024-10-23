#!/usr/bin/env python3

import subprocess
import random
from tqdm import tqdm
import time
from generate_eqs_list import *
import re

random.seed(17)

# with open('conjectures.json') as fs:
#   problems = json.load(fs)

# problems = problems['implications']

with open("impl.csv") as fs:
    problems = [
        {
            "lhs": "Equation" + x.split(",")[0],
            "rhs": "Equation" + x.strip().split(",")[1],
        }
        for x in fs
    ]

print(len(problems))

BVARS = "XYZWUV"


def format_expr2(expr):
    if isinstance(expr, int):
        return BVARS[expr]
    return f"mul({format_expr2(expr[0])}, {format_expr2(expr[1])})"


def format_eq(eq):
    v = ""
    for i in BVARS[: count_vars(eq)]:
        v += f"! [{i}] : "
    return f"{v}{format_expr2(eq[0])} = {format_expr2(eq[1])}"


def encode_problem(problem):
    assumption, goal = (
        eqs[int(problem["lhs"].split("n")[1]) - 1],
        eqs[int(problem["rhs"].split("n")[1]) - 1],
    )
    return f"fof(lhs, axiom, {format_eq(assumption)}).\nfof(rhs, conjecture, {format_eq(goal)}).\n"


def natural_sort(l):
    convert = lambda text: int(text) if text.isdigit() else text.lower()
    alphanum_key = lambda key: [convert(c) for c in re.split("([0-9]+)", key)]
    return sorted(l, key=alphanum_key)


def leanifyS(statement):
    statement = re.sub("mul", "", statement)
    statement = re.sub(",", " ◇ ", statement)
    statement = re.sub("!=", "≠", statement)
    variables = natural_sort({x for x in re.findall("\w+", statement) if "sK" not in x})
    variables = f'({" ".join(variables)} : G) ' if variables else ""
    return f"{variables}: {statement}"


def leanifyP(proof):
    sr = re.match(r"superposition (\d+),(\d+)", proof)
    if sr is not None:
        return f"superpose eq{sr[2]} eq{sr[1]}"
    sr = re.match(r"backward demodulation (\d+),(\d+)", proof)
    if sr is not None:
        return f"superpose eq{sr[2]} eq{sr[1]}"
    sr = re.match(r"forward demodulation (\d+),(\d+)", proof)
    if sr is not None:
        return f"superpose eq{sr[2]} eq{sr[1]}"
    raise NotImplementedError(proof)


def leanify(proof, problem):
    assumption, goal = (
        eqs[int(problem["lhs"].split("n")[1]) - 1],
        eqs[int(problem["rhs"].split("n")[1]) - 1],
    )
    output = (
        f'@[equational_result]\ntheorem {problem["lhs"]}_implies_{problem["rhs"]} '
        f'(G : Type*) [Magma G] (h : {problem["lhs"]} G) : {problem["rhs"]} G := by\n'
    )
    output += "  by_contra nh\n  simp only [not_forall] at nh\n"
    output += f'  obtain ⟨{", ".join("sK" + str(i) for i in range(count_vars(goal)))}, nh⟩ := nh\n'
    for eqnum, statement, proof in re.findall(r"(\d+)\. ([^[]+) \[([^\]]+)\]", proof):
        # print(eqnum, statement, proof)
        if proof.startswith("X") or proof.startswith("skolemisation"):
            continue
        if proof.startswith("cnf transformation"):
            if "!=" in statement:
                output += f"  have eq{eqnum} {leanifyS(statement)} := mod_symm nh\n"
            else:
                output += f"  have eq{eqnum} {leanifyS(statement)} := mod_symm (h ..)\n"
            continue
        if statement == "$false":
            sr = re.match(r"subsumption resolution (\d+),(\d+)", proof)
            if sr is not None:
                output += f"  subsumption eq{sr[1]} eq{sr[2]}\n\n"
                continue
            sr = re.match(r"trivial inequality removal (\d+)", proof)
            if sr is not None:
                output += f"  subsumption eq{sr[1]} rfl\n\n"
                continue
            sr = re.match(r"equality resolution (\d+)", proof)
            if sr is not None:
                output += f"  subsumption eq{sr[1]} rfl\n\n"
                continue
            print(output)
            raise NotImplementedError(proof)
        else:
            output += f"  have eq{eqnum} {leanifyS(statement)} := {leanifyP(proof)} -- {proof}\n"
    return output


dpind = 1
proofs = open(f"equational_theories/Generated/VampireProven/Proofs{dpind}.lean", "w")
print(
    """import equational_theories.Superposition
import equational_theories.Equations.All
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.ByContra
""",
    file=proofs,
)
length = 0
proof_list = open("equational_theories/Generated/VampireProven.lean", "a")
print(
    f"import equational_theories.Generated.VampireProven.Proofs{dpind}", file=proof_list
)

for problem in tqdm(problems):
    pr = encode_problem(problem)

    start_time = time.perf_counter()
    # print(problem)
    # print(pr)
    out = subprocess.check_output(
        ["~/Downloads/vampire", "--proof_extra", "full", "/proc/self/fd/0", "-t", "1"],
        input=pr.encode(),
    ).decode()
    lean_proof = leanify(out, problem)
    print(lean_proof, file=proofs)
    length += lean_proof.count("\n") + 2
    if length >= 2500:
        length = 0
        proofs.close()
        dpind += 1
        proofs = open(
            f"equational_theories/Generated/VampireProven/Proofs{dpind}.lean", "w"
        )
        print(
            """import equational_theories.Superposition
import equational_theories.Equations.All
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.ByContra
""",
            file=proofs,
        )
        print(
            f"import equational_theories.Generated.VampireProven.Proofs{dpind}",
            file=proof_list,
        )

# json.dump(remaining, open('remaining.json', 'w'))
