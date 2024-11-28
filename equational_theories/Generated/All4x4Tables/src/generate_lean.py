#!/usr/bin/env python3

from collections import defaultdict
import ast
import json
from pathlib import Path

#
# This script reads the file `../data/refutations.txt` and turns each line into a
# a file `equational_theories/Generated/All4x4Tables/Refutation<n>.lean`
#
# It also takes `../data/implications.json` into account and prunes entries based on the implications
# therein.
#

dir = Path(__file__).parent.parent

# we have 4694 equations
full = range(1, 4694 + 1)

with open(f"{dir}/data/implications.json", encoding='utf-8') as f:
    implications = json.load(f)["implications"]
implications = [
    (int(i["lhs"].removeprefix("Equation")), int(i["rhs"].removeprefix("Equation")))
    for i in implications
]

print("Number of implications:", len(implications))


def transitive_closure(pairs):
    pairs_idx = defaultdict(list)
    for a, b in pairs:
        pairs_idx[a].append(b)
    closure = set()
    new_pairs = set(pairs)
    while new_pairs:
        (a, b) = new_pairs.pop()
        closure.add((a, b))
        for c in pairs_idx[b]:
            if (a, c) not in closure:
                new_pairs.add((a, c))
    return closure


closure = transitive_closure(implications)
print(f"Size of transitive closure: {len(closure)}")

impliedBy = {i: set() for i in full}
implying = {j: set() for j in full}
for a, b in closure:
    if a in full and b in full:
        impliedBy[a].add(b)
        implying[b].add(a)


def parse_row(row):
    if len(row) == 2:
        # parse dump_tables rows
        assert row[0].startswith("Table ")
        table = row[0].removeprefix("Table ").strip()
        assert row[1].startswith("Proves ")
        satisfied = set(ast.literal_eval(row[1].removeprefix("Proves ")))
        refuted = {i for i in range(1, 4694 + 1) if i not in satisfied}
        div = 4  # hardcoded
        return {"table": table, "div": div, "satisfied": satisfied, "refuted": refuted}
    elif len(row) == 3:
        # parse make-plan rows
        assert row[0].startswith("Magma ")
        table = row[0].removeprefix("Magma ").strip()
        assert row[1].startswith("Satisfies ")
        assert row[2].startswith("Refutes ")
        satisfied = set(ast.literal_eval(row[1].removeprefix("Satisfies ")))
        refuted = set(ast.literal_eval(row[2].removeprefix("Refutes ")))
        div = table.count("[") - 1
        assert div > 0
        return {"table": table, "div": div, "satisfied": satisfied, "refuted": refuted}
    else:
        assert len(row) == 2 or len(row) == 3


stats = {
    "total": 0,
    "removed_by_implication": 0,
    "removed_by_covering": 0,
}

notImpliedBy = {i: set() for i in full}
notImplying = {j: set() for j in full}


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
    stats["removed_by_implication"] += (
        len(data["satisfied"]) + len(data["refuted"]) - len(satisfied) - len(refuted)
    )

    # prune by earlier examples
    satisfied_ = {i for i in satisfied if refuted - notImpliedBy[i]}
    refuted_ = {j for j in refuted if satisfied - notImplying[j]}

    stats["removed_by_covering"] += (
        len(satisfied) + len(refuted) - len(satisfied_) - len(refuted_)
    )
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

    table.replace("[", "#[")

    name = f"FinitePoly {table}"

    out = f"""
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
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
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G {satisfied} {refuted} :=
    ⟨Fin {div}, «{name}», Finite.of_fintype _, by decideFin!⟩
"""
    return out


def create_rows(f):
    first_line = f.readline().strip()
    all_rows = []
    row = []
    if not first_line.startswith("Plan"):
        # processing a dump_tables output file
        print("Reading dump_tables output...")
        if first_line.startswith("Table") or first_line.startswith("Proves"):
            row.append(first_line)
        for line in f:
            line = line.strip()
            if line.startswith("Table") or line.startswith("Proves"):
                row.append(line)
            if len(row) == 2:
                all_rows.append(row)
                row = []
    else:
        # processing a make-plan output file
        print("Reading make-plan output...")
        for line in f:
            line = line.strip()
            if (
                line.startswith("Magma")
                or line.startswith("Satisfies")
                or line.startswith("Refutes")
            ):
                row.append(line)
            if len(row) == 3:
                all_rows.append(row)
                row = []
    return all_rows


rows = create_rows(open(f"{dir}/data/plan.txt", encoding='utf-8'))
with open(f"{dir.parent}/All4x4Tables.lean", "w", encoding='utf-8') as main:
    for i, row in enumerate(rows):
        leanfile = f"{dir}/Refutation{i}.lean"
        data = parse_row(row)
        if data:
            data = prune_row(data)
            print(f"Writing {leanfile}")
            main.write(
                f"import equational_theories.Generated.All4x4Tables.Refutation{i}\n"
            )
            open(leanfile, "w", encoding='utf-8').write(generate_lean(data))

total = stats["total"]
removed_by_implication = stats["removed_by_implication"]
removed_by_covering = stats["removed_by_covering"]
remaining = total - removed_by_implication - removed_by_covering

percentage_removed_by_implication = (
    (removed_by_implication / total) * 100 if total > 0 else 0
)
percentage_removed_by_covering = (removed_by_covering / total) * 100 if total > 0 else 0

print(
    f"Out of {total} facts to check, pruning by implication removed "
    + f"{removed_by_implication} facts ({percentage_removed_by_implication:.2f}%) to check, "
    + f"pruning by covering removed {removed_by_covering} facts ({percentage_removed_by_covering:.2f}%), "
    + f"leaving {remaining} facts to check."
)
