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
    parser.add_argument("--scale",
                        type=int, default=1,
                        help="integer scale factor")

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

    # We want to canonicalize the ordering of the rows and columns, using the ordering
    # on equation numbers. We need to account for the fact that there may be gaps
    # between equation numbers (e.g. if we only include Subgraph.lean).

    # `matrixidx` is an index into the `eqs` array or `outcomes` matrix.
    # `imageidx` is an index in image pixel coordinates
    # `eqid` is an Equation number.

    eqid_from_matrixidx = list(map(name_to_id, eqs))
    imageidx_from_eqid = dict()
    for imageidx, eqid in enumerate(eqid_from_matrixidx):
        imageidx_from_eqid[eqid] = imageidx

    img = Image.new('RGB', (size, size))
    pixels = img.load()
    for ii, row in enumerate(outcomes):
        for jj, outcome in enumerate(row):
            ii_eqidx = eqid_from_matrixidx[ii]
            ii_imageidx = imageidx_from_eqid[ii_eqidx]
            jj_eqidx = eqid_from_matrixidx[jj]
            jj_imageidx = imageidx_from_eqid[jj_eqidx]
            pixels[ii_imageidx, jj_imageidx] = outcome_to_color(outcome)

    if args.scale != 1:
        new_size = (size * args.scale, size * args.scale)
        img = img.resize(new_size, Image.NEAREST)
    img.save(outfile)
    print("saved to " + outfile)
