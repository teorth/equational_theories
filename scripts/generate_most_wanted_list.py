#!/usr/bin/env python3

"""
Example usage:

```sh
$ python scripts/generate_most_wanted_list.py equational_theories/Subgraph.lean
$ less most_wanted.md
```
"""

from process_implications import *
from itertools import product
from datetime import datetime

def close(known_implies):
    # copilot wrote this
    new_pairs = closure = set(known_implies)
    while new_pairs:
        new_pairs = {
            (a, d)
            for a, b in new_pairs
            for c, d in known_implies
            if b == c
        } - closure
        closure |= new_pairs
    return closure

if __name__ == '__main__':
    try:
        file_name = argv[1]
        assert os.path.exists(file_name)
    except:
        print('Usage: python generate_most_wanted_list.py <file_name.lean>')
        exit(1)


    universe, known_implies, known_not_implies = parse_proofs_file(file_name)
    known_implies = close(known_implies)

    ascendants = defaultdict(int) # equation -> equations it's implied by
    descendants = defaultdict(int) # equation -> equations it implies
    for a, b in known_implies:
        if a != b:
            descendants[a] += 1
            ascendants[b] += 1


    edge_value = {} # (a, b) -> value of the a->b implication
    for a, b in product(universe, universe):
        if (a,b) in known_implies or (a,b) in known_not_implies:
            continue

        # This doesn't work with cycles
        v = ascendants[a] + descendants[b]
        # speed things up by not recording explicitly zero-value edges
        if v > 0:
            edge_value[(a,b)] = v

    with open('most_wanted.md', 'w+') as fh:
        fh.write(f"# Most Wanted list of implications as of ({datetime.now().strftime('%Y-%m-%d %H:%M:%S')})" + "\n\n")
        for a,b in sorted(edge_value, key=lambda ab:edge_value[ab], reverse=True):
            fh.write(f"* `{a}` -> `{b}` (implied by {ascendants[a]} -> implies {descendants[b]} = {edge_value[(a,b)]})"+'\n')
