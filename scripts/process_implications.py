#! /usr/bin/env python

"""
Example usage:

```sh
$ lake exe extract_implications | python scripts/process_implications.py
```
"""

from collections import defaultdict
import json
import os
from random import sample
import re
from sys import argv, stdin
import networkx as nx


def transitive_closure(pairs):
    pairs_idx = defaultdict(list)
    for a, b in pairs:
        pairs_idx[a].append(b)
    new_pairs = closure = set(pairs)
    while new_pairs:
        new_pairs = {
            (a, c)
            for a, b in new_pairs
            for c in pairs_idx[b]
        } - closure
        closure |= new_pairs
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

def parse_proofs_file_internal(universe, known_implies, known_not_implies, equations_file, file_name):
    # This code is buggy: it doesn't verify that the proofs are correct.
    # It is also extremely sensitive to formatting of the proof types. There's
    # probably a way to get this directly from Lean.
    if equations_file != None:
        for line in open(equations_file):
            if m := re.match(r'abbrev\s+(Equation\d+)\s+', line):
                universe.add(m.group(1))
                known_implies.add((m.group(1), m.group(1)))

    for line in open(file_name):
        if m := re.match(r'theorem\s+.*\[Magma\s+G\]\s*:\s*(Equation\d+)\s*G\s*:=', line):
            universe.add(m.group(1))
            for eq in universe:
                known_implies.add((eq, m.group(1)))
        elif m := re.match(r'theorem\s+.*\[Magma\s+G\]\s*\(.\s*:\s*(Equation\d+)\s+G\)\s*:\s*(Equation\d+)\s+G\s*:=', line):
            universe.add(m.group(1))
            universe.add(m.group(2))
            known_implies.add((m.group(1), m.group(2)))
        elif m := re.match(r'theorem\s+.*:\s*∃.*\(_:\s*Magma\s+G\),\s*(Equation\d+)\s+G\s*∧\s*¬\s*(Equation\d+)\s+G\s*:=', line):
            universe.add(m.group(1))
            universe.add(m.group(2))
            known_not_implies.add((m.group(1), m.group(2)))
    return universe, known_implies, known_not_implies

def parse_proofs_file(equations_file, file_name):
    universe = set()
    known_implies, known_not_implies = set(), set()
    parse_proofs_file_internal(universe, known_implies, known_not_implies, equations_file, file_name)
    return universe, known_implies, known_not_implies

def parse_proofs_files(equations_file, files):
    universe = set()
    known_implies, known_not_implies = set(), set()
    for file_name in files:
        parse_proofs_file_internal(universe, known_implies, known_not_implies, equations_file, file_name)
    return universe, known_implies, known_not_implies

def parse_extracted_implications():
    output = json.load(stdin)
    print(f'Parsed {len(output["unconditionals"])} unconditionals, {len(output["implications"])} implications, {len(output["facts"])} facts')

    universe = set()
    universe.update(output['unconditionals'])
    universe.update(implication[side] for implication in output['implications'] for side in ['lhs', 'rhs'])
    universe.update(eq for example in output['facts'] for status in ['satisfied', 'refuted'] for eq in example[status])

    known_implies = set()
    known_implies.update((eq, eq) for eq in universe)
    known_implies.update((implication['lhs'], implication['rhs']) for implication in output['implications'])
    known_implies.update((eq, ueq) for eq in universe for ueq in output['unconditionals'])

    G = nx.DiGraph()
    G.add_nodes_from(universe)
    G.add_edges_from(known_implies)

    comp_names = {}
    names = set()
    for comp in nx.strongly_connected_components(G):
        name = f'Equation{min(int(eq[8:]) for eq in comp)}'
        names.add(name)
        for eq in comp:
            comp_names[eq] = name
    assert 'Equation2' in names
    print(f'Processing {len(names)} equivalence classes of {len(universe)} laws')

    all_implications = transitive_closure(known_implies)
    all_implications = {(lhs, rhs) for lhs, rhs in all_implications if lhs in names and rhs in names}
    print('All implications:', len(all_implications))

    fwd_implications = {eq: set() for eq in names}
    bwd_implications = {eq: set() for eq in names}
    for a, b in all_implications:
        fwd_implications[a].add(b)
        bwd_implications[b].add(a)

    all_negative_implications = set()
    for example in output['facts']:
        pos = {succ for eq in example['satisfied'] for succ in fwd_implications[comp_names[eq]]}
        neg = {pred for eq in example['refuted'] for pred in bwd_implications[comp_names[eq]]}
        all_negative_implications.update((p, n) for p in pos for n in neg)
    print('All negative implications:', len(all_negative_implications))

    missing_implications = set((a, b) for a in names for b in names) - all_implications - all_negative_implications
    print(f'Missing implications: {len(missing_implications)}')
    irreducible = missing_implications
    irreducible = {
        (lhs, rhs) for lhs, rhs in irreducible
        if all((pred, rhs) not in irreducible for pred in bwd_implications[lhs] if pred != lhs)
    }
    irreducible = {
        (lhs, rhs) for lhs, rhs in irreducible
        if all((lhs, succ) not in irreducible for succ in fwd_implications[rhs] if succ != rhs)
    }
    print(f'Irreducible missing implications: {len(irreducible)}')

    for lhs, rhs in sorted(irreducible, key=lambda x: (int(x[0][8:]), int(x[1][8:]))):
        print(lhs, '=>', rhs)

if __name__ == '__main__':
    if len(argv) == 1:
        parse_extracted_implications()
        exit()

    try:
        file_name = argv[1]
        assert os.path.exists(file_name)
    except:
        print('Usage: python process_implications.py <file_name.lean>')
        exit(1)

    equations_file = os.path.join(os.path.dirname(file_name), "Equations.lean")
    universe, known_implies, known_not_implies = parse_proofs_file(None, file_name)

    all_unknown = get_unknown_implications(universe, known_implies, known_not_implies)

    print(f'Found {len(all_unknown)} unknown implications')
    if all_unknown:
        k = min(10, len(all_unknown))
        if k < len(all_unknown):
            print('Sample of', k, 'unknown implications:')
        for a, b in sample(list(all_unknown), k):
            print(f'{a} => {b}')
