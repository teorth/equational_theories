#! /usr/bin/env python3

"""
Example usage:

```sh
$ pip install pillow
$ python scripts/generate_image.py equational_theories/Basic.lean --close --filter
$ open equational_theories/Basic.png
```
"""

from process_implications import *
from PIL import Image  # pip install pillow

############################################

def name_to_ind(name):
    return int(name.removeprefix('Equation'))

UNKNOWN_COLOR = (0, 0, 0)
KNOWN_IMPLIES_COLOR = (0, 255, 0)
KNOWN_NOT_IMPLIES_COLOR = (255, 0, 0)

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
        print('Usage: python process_implications.py <file_name.lean>')
        exit(1)

    universe, known_implies, known_not_implies = parse_proofs_file(file_name)

    if '--close' in argv:
        known_implies = close(known_implies)

    inds = {e: name_to_ind(e) for e in universe}
    if '--filter' in argv:
        inds = {kv[0]: i for i, kv in enumerate(sorted(inds.items(), key=lambda kv: kv[1]))}
    min_ind = min(inds.values())
    max_ind = max(inds.values())
    size = max_ind - min_ind + 1
    def ind(name):
        return inds[name] - min_ind

    data = [UNKNOWN_COLOR] * (size * size)
    for known in known_implies:
        a, b = known
        data[ind(a) * size + ind(b)] = KNOWN_IMPLIES_COLOR
    for known in known_not_implies:
        a, b = known
        data[ind(a) * size + ind(b)] = KNOWN_NOT_IMPLIES_COLOR

    img = Image.new('RGB', (size, size))
    img.putdata(data)
    output_file = file_name.removesuffix('.lean') + '.png'
    img.save(output_file)
