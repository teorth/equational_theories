#!/usr/bin/env python3

import ast

# we have 4694 equations
full = set(list(range(4694)))

seen = {}


def gen(refutation_line):
    if "'" not in refutation_line:
        return
    _, eq, nums = refutation_line.split("'")
    data = set(ast.literal_eval(nums.strip()))

    satisfied = [i + 1 for i in range(4694) if i in data]
    refuted = [i + 1 for i in range(4694) if i not in data]

    for i, sat_eq in enumerate(satisfied):
        for i, refuted_eq in enumerate(refuted):
            str = f"{sat_eq},{refuted_eq}"
            if str not in seen:
                print(f"{sat_eq},{refuted_eq}")
                seen[str] = True


with open("refutations.txt") as f:
    lines = f.readlines()
    for i, line in enumerate(lines):
        if "seen" not in line:
            gen(line)
