#!/usr/bin/env python3

import argparse
import json
import os

def make_progress_badge(ratio):
    percent = f"{ratio:.1%}"
    return f'<svg xmlns="http://www.w3.org/2000/svg" xmlns:xlink="http://www.w3.org/1999/xlink" width="100" height="20" role="img" aria-label="Progress: {percent}"><title>Progress: {percent}</title><linearGradient id="s" x2="0" y2="100%"><stop offset="0" stop-color="#bbb" stop-opacity=".1"/><stop offset="1" stop-opacity=".1"/></linearGradient><clipPath id="r"><rect width="100" height="20" rx="3" fill="#fff"/></clipPath><g clip-path="url(#r)"><rect width="59" height="20" fill="#555"/><rect x="59" width="41" height="20" fill="#007ec6"/><rect width="100" height="20" fill="url(#s)"/></g><g fill="#fff" text-anchor="middle" font-family="Verdana,Geneva,DejaVu Sans,sans-serif" text-rendering="geometricPrecision" font-size="110"><text aria-hidden="true" x="305" y="150" fill="#010101" fill-opacity=".3" transform="scale(.1)" textLength="490">Progress</text><text x="305" y="140" transform="scale(.1)" fill="#fff" textLength="490">Progress</text><text aria-hidden="true" x="790" y="150" fill="#010101" fill-opacity=".3" transform="scale(.1)" textLength="330">{percent}</text><text x="790" y="140" transform="scale(.1)" fill="#fff" textLength="330">{percent}</text></g></svg>'

if __name__ == '__main__':
    parser = argparse.ArgumentParser(description="generate the dashboard markdown")
    parser.add_argument("hist_file",
                        help="json file containing output of `lake exe extract_implications outcomes --hist")
    parser.add_argument("--out_file",
                        default="home_page/dashboard/index.md",
                        help="markdown file to pass to jekyll")
    parser.add_argument("--badge_file",
                        default="home_page/dashboard/progress_badge.svg",
                        help="path to create the progress badge for the Github repo")

    args = parser.parse_args()
    with open(args.hist_file, 'r') as f:
        data = json.load(f)

    explicit_proof_true = data.get('explicit_proof_true', 0)
    implicit_proof_true = data.get('implicit_proof_true', 0)
    explicit_proof_false = data.get('explicit_proof_false', 0)
    implicit_proof_false = data.get('implicit_proof_false', 0)
    explicit_conjecture_true = data.get('explicit_conjecture_true', 0)
    implicit_conjecture_true = data.get('implicit_conjecture_true', 0)
    explicit_conjecture_false = data.get('explicit_conjecture_false', 0)
    implicit_conjecture_false = data.get('implicit_conjecture_false', 0)
    unknown = data.get('unknown', 0);
    proved_total = explicit_proof_true + implicit_proof_true + explicit_proof_false + implicit_proof_false
    conjectured_total = explicit_conjecture_true + implicit_conjecture_true + explicit_conjecture_false + implicit_conjecture_false

    total = proved_total + conjectured_total + unknown

    directory = os.path.dirname(args.out_file)
    if not os.path.exists(directory):
        os.makedirs(directory)

    outfile = open(args.out_file, 'w')

    outfile.write("\n")
    ratio = proved_total / total
    outfile.write(f"The implication graph is **{ratio:.3%}** complete.\n\n")

    outfile.write(
        """An implication is *explicitly true* or *explicitly false* if we directly have
           a proof of the corresponding proposition in Lean. It is *implicitly true* or
           *implicitly false* if the proposition follows by taking the reflexive transitive
           closure of explicitly proven implications.\n\n""")
    outfile.write("Our current counts of implications in each of those categories are:\n\n")
    outfile.write("| explicitly true | implicitly true | explicitly false | implicitly false | no proof |\n")
    outfile.write("| -- | -- | -- | -- | -- |\n")
    outfile.write("| {} | {} | {} | {} | {} |\n".format(
        explicit_proof_true, implicit_proof_true, explicit_proof_false,
        implicit_proof_false, conjectured_total + unknown))
    outfile.write("\n")


    outfile.write("\nThe _no proof_ column above represents work that we still need to do.\n")
    outfile.write("Among the _no proof_ implications, we have the following conjecture counts:\n\n")
    outfile.write("| explicitly true | implicitly true | explicitly false | implicitly false | no conjecture |\n")
    outfile.write("| -- | -- | -- | -- | -- |\n")
    outfile.write("| {} | {} | {} | {} | {} |\n".format(
        explicit_conjecture_true, implicit_conjecture_true, explicit_conjecture_false,
        implicit_conjecture_false, unknown))
    outfile.write("\n")
    ratio = (proved_total + conjectured_total) / total
    outfile.write(f"The implication graph is **{ratio:.3%}** complete if we include conjectures.\n\n")

    open(args.badge_file, 'w').write(make_progress_badge(ratio))
