#!/usr/bin/env python3

import re
import json
import itertools
from generate_eqs_list import *


def eval_expr(expr, assgn, m):
    if isinstance(expr, int):
        return assgn[expr]
    return m[eval_expr(expr[0], assgn, m)][eval_expr(expr[1], assgn, m)]


def satisfies_eq(eq, m):
    for assgn in itertools.product(range(len(m)), repeat=count_vars(eq)):
        if eval_expr(eq[0], assgn, m) != eval_expr(eq[1], assgn, m):
            return False
    return True


expr = re.compile(r"memoFinOp fun x y => (.+)\[x\.val]!\[y\.val]!")

for filename in (
    "equational_theories/Generated/VampireProven/Disproofs1.lean",
    "equational_theories/Generated/VampireProven/Disproofs2.lean",
):
    for line in open(filename, "r"):
        m = expr.findall(line)
        if not m:
            continue
        assert len(m) == 1
        m = json.loads(m[0])
        satisfies = []
        for i, eq in enumerate(eqs):
            if satisfies_eq(eq, m):
                satisfies.append(i + 1)
        print("Table", json.dumps(m, separators=(",", ":")))
        print("Proves", json.dumps(satisfies, separators=(",", ":")))
        print()
