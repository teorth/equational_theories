# This code is based on `equational_theories/Generated/VampireProven/src/vampire_proofs.py`

#!/usr/bin/env python3

import json
import sys
import re
import itertools

def natural_sort(l):
    convert = lambda text: int(text) if text.isdigit() else text.lower()
    alphanum_key = lambda key: [convert(c) for c in re.split("([0-9]+)", key)]
    return sorted(l, key=alphanum_key)

def flatten(S):
    if S == []:
        return S
    if isinstance(S[0], list):
        return flatten(S[0]) + flatten(S[1:])
    return S[:1] + flatten(S[1:])

def flatten_and_count_unique(nested_array):
    unique_elements = set(flatten(nested_array))
    return len(unique_elements)

def leanifyS(statement):
    statement = re.sub("mul", "", statement)
    statement = re.sub(",", " ◇ ", statement)
    statement = re.sub("!=", "≠", statement)
    variables = natural_sort({x for x in re.findall(r"\w+", statement) if "sK" not in x})
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

def leanify(json, vampire_output):
    output = f'@[equational_result]\ntheorem Finite.Equation{json["hypothesis_num"]}_implies_Equation{json["goal_num"]} (G : Type*) [Magma G]'
    if json["finite"]:
        output += " [Finite G]"

    output += f' (h : Equation{json["hypothesis_num"]} G) : Equation{json["goal_num"]} G := by\n'
    output += "  by_contra nh\n  simp only [not_forall] at nh\n"
    output += f'  obtain ⟨{", ".join("sK" + str(i) for i in range(flatten_and_count_unique(json["goal_eq"])))}, nh⟩ := nh\n'
    eqnum_to_axiom = {}
    for eqnum, statement, proof in re.findall(r"(\d+)\. (.+) \[([^\]]+)\]", vampire_output):
        #print(eqnum, "//", statement, "//", proof)
        if proof.startswith("X") or proof.startswith("skolemisation"):
            continue
        if proof.startswith("input("):
            if proof.startswith("input(axiom) "):
                eqnum_to_axiom[eqnum] = proof[len('input(axiom) '):].strip()
            continue

        if proof.startswith("negated conjecture") or proof.startswith("ennf transformation") or proof.startswith("choice axiom"):
            continue

        if proof.startswith("rectify"):
            sr = re.match(r"rectify (\d+)", proof)
            if sr is None:
                raise Exception("Unexpected")
            eqnum_to_axiom[eqnum] = eqnum_to_axiom[sr[1]]
            continue
        if proof.startswith("cnf transformation"):
            if "!=" in statement:
                output += f"  have eq{eqnum} {leanifyS(statement)} := mod_symm nh\n"
            else:
                sr = re.match(r"cnf transformation (\d+)", proof)
                if sr is None:
                    raise Exception("Unexpected")
                axiom_name = eqnum_to_axiom[sr[1]]
                if axiom_name is None:
                    raise Exception("Failed to map cnf transformation to axiom")

                if axiom_name == "hypothesis":
                    output += f"  have eq{eqnum} {leanifyS(statement)} := mod_symm (h ..)\n"
                else:
                    output += json["axioms"][axiom_name]["proof"].replace("REPLACE", f"eq{eqnum}")
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
            output += f"  have eq{eqnum} {leanifyS(statement)} := {leanifyP(proof)}\n" #  -- {proof}\n"
    return output

if len(sys.argv) < 2:
    print("Usage: python process.py <tptp 1> [tptp 2] ...")
    sys.exit(1)

print("""import equational_theories.Equations.All
import equational_theories.MagmaOp
import equational_theories.Superposition
import Mathlib.Data.Set.Finite
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.ByContra

set_option linter.unusedVariables false
""")

for arg in sys.argv[1:]:
    try: 
        with open(arg, 'r') as f:
            first_line = f.readline()
            if not first_line.startswith('% JSON: '):
                print(first_line)
                print(f"Error: The first line of {arg} does not start with '% JSON: '")
                sys.exit(1)
            json_str = first_line[len('% JSON: '):].strip()
            json_data = json.loads(json_str)
            with open(arg + ".out", 'r') as f2:
                out = f2.read()

                sr = re.search(r"Termination reason: (.+)", out)
                if sr is None:
                    raise Exception("No termination reason in output?")

                if sr[1] == "Refutation":
                    print(leanify(json_data, out))
                else:
                    print(f"{arg} termination reason: {sr[1]}", file=sys.stderr)
    except json.JSONDecodeError as e:
        print(f"Error: JSON parsing failed: {e}")
        sys.exit(1)
