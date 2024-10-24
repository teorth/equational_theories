#!/usr/bin/env python3

"""
Example usage:

```sh
$ pip install pillow
$ python scripts/generate_image.py equational_theories/Subgraph.lean --close --filter
$ open equational_theories/Subgraph.png
$ python scripts/generate_image.py equational_theories/Generated/TrivialBruteforce/theorems/Apply.lean --close --filter --equations equational_theories/Equations/Basic.lean
$ python scripts/generate_image.py equational_theories/Generated/ equational_theories/Subgraph.lean --output equational_theories/Subgraph.png
```
"""

from process_implications import *
from PIL import Image  # pip install pillow
import glob

############################################


def name_to_ind(name):
    return int(name.removeprefix("Equation"))


UNKNOWN_COLOR = (0, 0, 0)
KNOWN_IMPLIES_COLOR = (0, 255, 0)
KNOWN_NOT_IMPLIES_COLOR = (255, 0, 0)


def append_dict(d, a, b):
    if a in d:
        d[a].append(b)
        d[a].sort()
    else:
        d[a] = [b]


def close(known_implies):
    # copilot wrote this
    closure2 = {}
    for a, b in known_implies:
        append_dict(closure2, a, b)
    new_pairs2 = {}
    for a, b in known_implies:
        append_dict(new_pairs2, b, a)

    new_pairs = closure = set(known_implies)
    while new_pairs:
        print(f"current closure is size {len(closure)}")
        new_pairs = {
            (a, d) for a, b in new_pairs for c, d in known_implies if b == c
        } - closure
        print(f"found {len(new_pairs)} pairs for the closure")
        closure |= new_pairs
    return closure


def print_usage():
    print(
        "Usage: python process_implications.py <file_name.lean> [--close] [--filter] [--output <filename.png>] [--equations <equations.lean> ...]"
    )


if __name__ == "__main__":
    close_implies = False
    filter_universe = False
    equations_files = []
    output_file = None
    files = []
    try:
        i = 1
        while i < len(argv):
            current_arg = argv[i]
            if "--close" == current_arg:
                close_implies = True
                i += 1
            elif "--filter" == current_arg:
                filter_universe = True
                i += 1
            elif "--equations" == current_arg:
                equations_files.append(argv[i + 1])
                i += 2
            elif "--output" == current_arg:
                output_file = argv[i + 1]
                i += 2
            else:
                if os.path.isdir(current_arg):
                    for file_name in glob.glob(
                        current_arg + "/**/*.lean", recursive=True
                    ):
                        files.append(file_name)
                elif os.path.isfile(current_arg):
                    files.append(current_arg)
                else:
                    assert False

                i += 1
    except Exception as e:
        print(e)
        print_usage()
        exit(1)

    if len(files) == 0:
        print_usage()
        exit(1)

    if output_file is None:
        output_file = files[0].removesuffix(".lean") + ".png"

    print("Reading implications and contrimplications")
    universe, known_implies, known_not_implies = parse_proofs_files(
        equations_files, files
    )
    print(
        f"Found {len(known_implies)} implications, and {len(known_not_implies)} contrimplications."
    )
    if close_implies:
        print("Calculating closure")
        known_implies = close(known_implies)

    inds = {e: name_to_ind(e) for e in universe}
    if filter_universe:
        print("Filtering to universe")
        inds = {
            kv[0]: i for i, kv in enumerate(sorted(inds.items(), key=lambda kv: kv[1]))
        }
    min_ind = min(inds.values())
    max_ind = max(inds.values())
    size = max_ind - min_ind + 1

    def ind(name):
        return inds[name] - min_ind

    print("Building picture")
    data = [UNKNOWN_COLOR] * (size * size)
    for known in known_implies:
        a, b = known
        data[ind(a) * size + ind(b)] = KNOWN_IMPLIES_COLOR
    for known in known_not_implies:
        a, b = known
        data[ind(a) * size + ind(b)] = KNOWN_NOT_IMPLIES_COLOR

    img = Image.new("RGB", (size, size))
    img.putdata(data)
    img.save(output_file)
