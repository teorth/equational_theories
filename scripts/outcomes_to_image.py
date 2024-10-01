#! /usr/bin/env python3

"""
Generates a png image to visualize the output of `extract_implications outcomes`.

Example usage:

$ lake exe extract_implications outcomes equational_theories.Subgraph > /tmp/subgraph.json
$ python scripts/outcomes_to_image.py /tmp/subgraph.json --outfile subgraph.png
"""

import argparse
import json
import os
from PIL import Image  # pip install pillow

def name_to_id(name):
    return int(name.removeprefix('Equation'))

def outcome_to_color(outcome) :
    if outcome == "explicit_proof_true":
        return (0, 192, 255)
    elif outcome == "implicit_proof_true":
        return (0, 96, 128)
    elif outcome == "explicit_conjecture_true":
        return (102, 255, 0)
    elif outcome == "implicit_conjecture_true":
        return (0, 128, 0)
    elif outcome == "unknown":
        return (0, 0, 0)
    elif outcome == "explicit_conjecture_false":
        return (255, 221, 85)
    elif outcome == "implicit_conjecture_false":
        return (170, 136, 0)
    elif outcome == "explicit_proof_false":
        return (255, 72, 72)
    elif outcome == "implicit_proof_false":
        return (128, 0, 0)
    else:
        raise Exception("unknown outcome: " + outcome)

if __name__ == '__main__':
    parser = argparse.ArgumentParser(description="render an image")
    parser.add_argument("file",
                        help="json file containing output of `lake exe extract_implications outcomes")
    parser.add_argument("--outfile",
                        type=str, default=None,
                        help="name of output file")
    args = parser.parse_args()

    outfile = args.outfile
    if outfile is None:
        outfile = os.path.splitext(args.file)[0] + ".png"

    with open(args.file, 'r') as f:
        data = json.load(f)

    outcomes = data["outcomes"]
    eqs = data["equations"]

    size = len(eqs)
    print("size = ", size)

    # construct map from equation ID to its index in eqs.
    reverse_map = dict()
    for ii, eq in enumerate(eqs):
        reverse_map[name_to_id(eq)] = ii

    img = Image.new('RGB', (size, size))
    pixels = img.load()
    for ii, row in enumerate(outcomes):
        for jj, outcome in enumerate(row):
            i_idx = reverse_map[ii+1]
            j_idx = reverse_map[jj+1]
            if ii == jj:
                # always true.
                pixels[i_idx, j_idx] = outcome_to_color("implicit_proof_true")
            else :
                pixels[i_idx, j_idx] = outcome_to_color(outcome)
    img.save(outfile)
    print("saved to " + outfile)
