#! /usr/bin/env python3

"""
Example usage:

```sh
$ python scripts/generate_image.py equational_theories/Basic.lean
$ open equational_theories/Basic.png
```
"""

from process_implications import *
from PIL import Image  # pip install pillow

############################################

def name_to_ind(name):
    return int(name.removeprefix('Equation'))

UNKNOWN_COLOR = (0, 0, 0)
KNOWN_IMPLIES_COLOR = (255, 0, 0)
KNOWN_NOT_IMPLIES_COLOR = (0, 255, 0)

if __name__ == '__main__':
    try:
        file_name = argv[1]
        assert os.path.exists(file_name)
    except:
        print('Usage: python process_implications.py <file_name.lean>')
        exit(1)


    universe, known_implies, known_not_implies = parse_proofs_file(file_name)
    # all_unknown = get_unknown_implications(universe, known_implies, known_not_implies)

    inds = [name_to_ind(e) for e in universe]
    min_ind = min(inds)
    max_ind = max(inds)
    size = max_ind - min_ind + 1
    def ind(name):
        return name_to_ind(name) - min_ind

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
