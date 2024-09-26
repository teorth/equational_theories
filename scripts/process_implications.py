#! /usr/bin/env python3

from collections import defaultdict
import os
from random import sample
import re
from sys import argv


def transitive_closure(pairs):
    closure = set(pairs) | {(a, a) for a in universe}
    last_round = closure
    while True:
        new_pairs = set()
        for a, b in last_round:
            for c, d in pairs:
                if b == c:
                    new_pairs.add((a, d))
        for a, b in pairs:
            for c, d in last_round:
                if b == c:
                    new_pairs.add((a, d))
        new_pairs = new_pairs - closure
        if not new_pairs:
            break
        closure |= new_pairs
        last_round = new_pairs
    return closure


def get_unknown_implications(universe, known_implies, known_not_implies):
    all_implications = transitive_closure(known_implies)

    fwd_implications = defaultdict(set)
    bwd_implications = defaultdict(set)
    for a, b in all_implications:
        fwd_implications[a].add(b)
        bwd_implications[b].add(a)

    all_negative_implications = set(
        (c, d)
        for a, b in known_not_implies
        for c in fwd_implications[a]
        for d in bwd_implications[b]
    )

    return set((a, b) for a in universe for b in universe) - all_implications - all_negative_implications


def parse_proofs_file(file_name):
    # This code is buggy: it doesn't verify that the proofs are correct.
    universe = []
    true_statements = []
    known_implies, known_not_implies = [], []
    for line in open(file_name):
        if m := re.match(r'def (Equation\d+) ', line):
            universe.append(m.group(1))
        if m := re.match(r'theorem (Equation\d+)_implies_(Equation\d) ', line):
            known_implies.append((m.group(1), m.group(2)))
        if m := re.match(r'theorem (Equation\d+)_not_implies_(Equation\d) ', line):
            known_not_implies.append((m.group(1), m.group(2)))
        if m := re.match(r'theorem (Equation\d+)_true ', line):
            true_statements.append(m.group(1))
    known_implies.extend((a, x) for a in universe for x in true_statements)
    return universe, known_implies, known_not_implies


try:
    file_name = argv[1]
    assert os.path.exists(file_name)
except:
    print('Usage: python process_implications.py <file_name.lean>')
    exit(1)


universe, known_implies, known_not_implies = parse_proofs_file(file_name)

# Missing proofs in Equational/Basic.lean:

# known_implies.extend([
#     ('Equation3', 'Equation8'),
#     ('Equation9', 'Equation10'),
# ])
# known_not_implies.extend([
#     ('Equation4', 'Equation6'),
#     ('Equation4', 'Equation10'),
#     ('Equation6', 'Equation10'),
#     ('Equation7', 'Equation4'),
# ])


all_unknown = get_unknown_implications(universe, known_implies, known_not_implies)

print(f'Found {len(all_unknown)} unknown implications')
if all_unknown:
    k = min(10, len(all_unknown))
    if k < len(all_unknown):
        print('Sample of', k, 'unknown implications:')
    for a, b in sample(list(all_unknown), k):
        print(f'{a} => {b}')
