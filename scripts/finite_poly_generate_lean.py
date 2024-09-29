#! /usr/bin/env python3

import ast
import re

#
# This script reads the file `finite_poly_refutations.txt` and turns each line into a
# a file `equational_theories/Generated/FinitePoly/Refutation<n>.lean`
#


# we have 4694 equations
full = set(list(range(4694)))

def parse_row(row):
    if not row.startswith("'(") or "seen" in row: return
    _, eq, nums = row.split("'")
    data = set(ast.literal_eval(nums.strip()))
    # the numbers are off by one, the offcial equations list is 1-indexed
    satisfied = [i+1 for i in range(4694) if i in data]
    refuted = [i+1 for i in range(4694) if i not in data]

    # we turn the equation as printed in the refutation file into a valid lean expression,
    # and a pretty version of it for the name. We also remove trivial factors and summands
    m = re.match(r"\((.*)\) % (.*)", eq)
    div = int(m.group(2))

    summands = m.group(1).split(" + ")
    summands = [ s.removeprefix("1 * ") for s in summands if not s.startswith("0 * ") ]
    poly = " + ".join(summands) if summands else "0"

    pretty_eq = poly
    pretty_eq = pretty_eq.replace("**2", "²")
    poly = poly.replace("x**2", "x*x").replace("y**2", "y*y")
    return {"raw": row, "poly": poly, "pretty_eq": pretty_eq, "div": div, "satisfied": satisfied, "refuted": refuted}

def generate_lean(data):
    raw = data["raw"]
    poly = data["poly"]
    pretty_eq = data["pretty_eq"]
    div = data["div"]
    satisfied = data["satisfied"]
    refuted = data["refuted"]

    name = f"FinitePoly {pretty_eq} % {div}"
    satname= lambda i: f"{name} satisfies Equation{i}"
    refname= lambda i: f"{name} refutes Equation{i}"

    out = f"""
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following refutation as produced by
random generation of polynomials:
{raw}-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «{name}» : Magma (Fin {div}) where
  op := memoFinOp fun x y => {poly}

/-! The facts -/
theorem «Facts from {name}» :
  ∃ (G : Type) (_ : Magma G), Facts G {satisfied} {refuted} :=
    ⟨Fin {div}, «{name}», by decideFin!⟩
"""
    return out


with open("data/finite_poly_refutations.txt") as f:
    with open("equational_theories/Generated/FinitePoly.lean", "w") as main:
      lines = f.readlines()
      for i, line in enumerate(lines):
          leanfile = f"equational_theories/Generated/FinitePoly/Refutation{i}.lean"
          data = parse_row(line)
          if data and data["div"] < 5:
            print(f"Writing {leanfile}")
            main.write(f"import equational_theories.Generated.FinitePoly.Refutation{i}\n")
            with open(leanfile, "w") as f:
                  f.write(generate_lean(data))
