#! /usr/bin/env python3

from collections import defaultdict
import ast
import re
import json
import itertools
from pathlib import Path

#
# This script reads the file `../data/refutations.txt` and turns each line into a
# a file `equational_theories/Generated/{parent_name}/Refutation<n>.lean`
#
# It also takes `../data/implications.json` into account and prunes entries based on the implications
# therein.
#

dir = Path(__file__).parent.parent
parent_name = dir.name

# we have 4694 equations
full = range(1,4694+1)

with open(f"{dir}/../All4x4Tables/data/implications.json") as f:
  implications = json.load(f)["implications"]
implications = [ (int(i["lhs"].removeprefix("Equation")), int(i["rhs"].removeprefix("Equation"))) for i in implications ]

print("Number of implications:", len(implications))

def transitive_closure(pairs):
    pairs_idx = defaultdict(list)
    for a, b in pairs:
        pairs_idx[a].append(b)
    closure = set()
    new_pairs = set(pairs)
    while new_pairs:
        (a,b) = new_pairs.pop()
        closure.add((a, b))
        for c in pairs_idx[b]:
          if (a, c) not in closure:
            new_pairs.add((a, c))
    return closure

closure = transitive_closure(implications)
print(f"Size of transitive closure: {len(closure)}")

impliedBy = { i : set() for i in full }
implying = { j : set() for j in full }
for (a,b) in closure:
    if a in full and b in full:
        impliedBy[a].add(b)
        implying[b].add(a)

def parse_row(row):
    assert len(row) == 3
    assert row[0].startswith("Table ")
    table = row[0].removeprefix("Table ").strip()
    assert row[1].startswith("Proves ")
    satisfied = set(ast.literal_eval(row[1].removeprefix("Proves ")))
    refuted = {i for i in range(1,4694+1) if i not in satisfied}
    div = len(ast.literal_eval(row[0].removeprefix("Table ")))

    return {"table": table, "div": div, "satisfied": satisfied, "refuted": refuted}


stats = {
  "total" : 0,
  "removed_by_implication": 0,
  "removed_by_covering": 0,
}

notImpliedBy = { i : set() for i in full }
notImplying = { j : set() for j in full }

def prune_row(data):
    stats["total"] += len(data["satisfied"]) + len(data["refuted"])

    # prune by implications
    satisfied = set()
    for i in data["satisfied"]:
        # already implied
        if implying[i].intersection(satisfied):
          continue
        # remove all implied by this
        satisfied = satisfied - impliedBy[i]
        satisfied.add(i)
    refuted = set()
    for i in data["refuted"]:
        # already ruled out
        if impliedBy[i].intersection(refuted):
          continue
        # remove all that this is ruling out
        refuted = refuted - implying[i]
        refuted.add(i)
    stats["removed_by_implication"] += len(data["satisfied"]) + len(data["refuted"]) - len(satisfied) - len(refuted)

    # prune by earlier examples
    satisfied_ = {i for i in satisfied if refuted - notImpliedBy[i] }
    refuted_   = {j for j in refuted   if satisfied - notImplying[j] }

    stats["removed_by_covering"] += len(satisfied) + len(refuted) - len(satisfied_) - len(refuted_)
    satisfied, refuted = satisfied_, refuted_

    for i in satisfied:
      for j in refuted:
        notImpliedBy[i].add(j)
        notImplying[j].add(i)

    data["satisfied"] = sorted(satisfied)
    data["refuted"] = sorted(refuted)
    return data

def generate_lean(data):
    table = data["table"]
    div = data["div"]
    satisfied = data["satisfied"]
    refuted = data["refuted"]

    atable = table.replace("[", "#[")

    name = f"FinitePoly {table}"
    satname= lambda i: f"{name} satisfies Equation{i}"
    refname= lambda i: f"{name} refutes Equation{i}"

    out = f"""
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
{table}
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «{name}» : Magma (Fin {div}) where
  op := memoFinOp fun x y => {table}[x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from {name}» :
  ∃ (G : Type) (_ : Magma G), Facts G {satisfied} {refuted} :=
    ⟨Fin {div}, «{name}», by decideFin!⟩
"""
    return out


with open(f"{dir}/data/refutations.txt") as f:
    with open(f"{dir.parent}/FinSearch.lean", "w") as main:
      lines = [line for line in f.readlines() if not line.startswith("--")]
      # the format is groups-of-three-lines-based
      lines = [lines[i:i + 3] for i in range(0, len(lines), 3)]
      refutation_id = 0
      for line in lines:
          leanfile = f"{dir}/theorems/Refutation{refutation_id}.lean"
          data = parse_row(line)
          if data:
             data = prune_row(data)
          if data and data["satisfied"] and data["refuted"]:
            print(f"Writing {leanfile}")
            main.write(f"import equational_theories.Generated.{parent_name}.theorems.Refutation{refutation_id}\n")
            with open(leanfile, "w") as f:
                  f.write(generate_lean(data))
            refutation_id += 1


total = stats["total"]
removed_by_implication = stats["removed_by_implication"]
removed_by_covering = stats["removed_by_covering"]
remaining = total - removed_by_implication - removed_by_covering

percentage_removed_by_implication = (removed_by_implication / total) * 100 if total > 0 else 0
percentage_removed_by_covering = (removed_by_covering / total) * 100 if total > 0 else 0

print(f"Out of {total} facts to check, pruning by implication removed " +
  f"{removed_by_implication} facts ({percentage_removed_by_implication:.2f}%) to check, " +
  f"pruning by covering removed {removed_by_covering} facts ({percentage_removed_by_covering:.2f}%), " +
  f"leaving {remaining} facts to check.")
