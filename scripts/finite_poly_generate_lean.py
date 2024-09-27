#! /usr/bin/env python3

import ast
import re

#
# This script reads the file `finite_poly_refutations.txt` and turns each line into a
# a file `equational_theories/FinitePoly/Refutation<n>.lean`
#


# we have 4694 equations
full = set(list(range(4694)))

def generate_lean(refutation_line):
    _, eq, nums = refutation_line.split("'")
    data = set(ast.literal_eval(nums.strip()))
    # the numbers are off by one, the offcial equations list is 1-indexed
    satisfied = [i+1 for i in range(4694) if i in data]
    refuted = [i+1 for i in range(4694) if i not in data]

    # we turn the equation as printed in the refutation file into a valid lean expression,
    # and a pretty version of it for the name. We also remove trivial factors and summands
    m = re.match(r"\((.*)\) % (.*)", eq)
    div = int(m.group(2))

    summands = m.group(1).split(" + ")
    summands = [ s.replace("1 * ","") for s in summands if not s.startswith("0 * ") ]
    poly = " + ".join(summands) if summands else "0"

    pretty_eq = poly
    pretty_eq = pretty_eq.replace("**2", "²")
    poly = poly.replace("x**2", "x*x").replace("y**2", "y*y")

    name = f"FinitePoly {pretty_eq}"
    satname= lambda i: f"{name} satisfies Equation{i}"
    refname= lambda i: f"{name} refutes Equation{i}"

    out = """
import equational_theories.FinitePoly.Common
import equational_theories.FinitePoly.DecideBang
"""

    out += f"""
/-!
This file is generated from the following refutation as produced by
random generation of polynomials:
{refutation_line}
-/
"""

    out += f"""
-- The magma definition
def «{name}» : Magma (Fin {div}) where
  op x y := {poly}
"""

    out += f"""
/-! The satisfied equations -/
"""
    for eq in satisfied:
      out += f"""
theorem «{satname(eq)}» :
  @Equation{eq} _ «{name}» := by unfold Equation{eq}; decide!

"""

    out += f"""
/-! The refuted equations -/
    """
    for eq in refuted:
      out += f"""
theorem «{refname(eq)}» :
  ¬ @Equation{eq} _ «{name}» := by unfold Equation{eq}; decide!

"""

    if False: # turn generation of implications on and off here
      # Do we really want to write all of these out?
      out += f"""
  /-! The antiimplications -/
  """

      for seq in satisfied:
        for req in refuted:
          out += f"""
  theorem Equation{seq}_not_implies_Equation{req} :
    ∃ (G: Type) (_: Magma G), Equation{seq} G ∧ ¬ Equation{req} G :=
      ⟨_, _, «{satname(seq)}», «{refname(req)}» ⟩
  """

    return out


with open("data/finite_poly_refutations.txt") as f:
    lines = f.readlines()
    for i, line in enumerate(lines):
        leanfile = f"equational_theories/FinitePoly/Refutation{i}.lean"
        print(f"Writing {leanfile}")
        with open(leanfile, "w") as f:
            if not "seen" in line:
                f.write(generate_lean(line))
