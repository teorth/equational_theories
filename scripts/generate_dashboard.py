#!/usr/bin/env python3

import argparse
import json
import os
import subprocess


def make_progress_badge(ratio):
    percent = f"{ratio:.5%}"
    return f'<svg xmlns="http://www.w3.org/2000/svg" xmlns:xlink="http://www.w3.org/1999/xlink" width="124" height="20" role="img" aria-label="Progress: {percent}"><title>Progress: {percent}</title><linearGradient id="s" x2="0" y2="100%"><stop offset="0" stop-color="#bbb" stop-opacity=".1"/><stop offset="1" stop-opacity=".1"/></linearGradient><clipPath id="r"><rect width="124" height="20" rx="3" fill="#fff"/></clipPath><g clip-path="url(#r)"><rect width="57" height="20" fill="#555"/><rect x="57" width="67" height="20" fill="#007ec6"/><rect width="124" height="20" fill="url(#s)"/></g><g fill="#fff" text-anchor="middle" font-family="Verdana,Geneva,DejaVu Sans,sans-serif" text-rendering="geometricPrecision" font-size="110"><text aria-hidden="true" x="295" y="150" fill="#010101" fill-opacity=".3" transform="scale(.1)" textLength="470">Progress</text><text x="295" y="140" transform="scale(.1)" fill="#fff" textLength="470">Progress</text><text aria-hidden="true" x="895" y="150" fill="#010101" fill-opacity=".3" transform="scale(.1)" textLength="570">{percent}</text><text x="895" y="140" transform="scale(.1)" fill="#fff" textLength="570">{percent}</text></g></svg>'


def process_hist(data):
    explicit_proof_true = data.get("explicit_proof_true", 0)
    implicit_proof_true = data.get("implicit_proof_true", 0)
    explicit_proof_false = data.get("explicit_proof_false", 0)
    implicit_proof_false = data.get("implicit_proof_false", 0)
    explicit_conjecture_true = data.get("explicit_conjecture_true", 0)
    implicit_conjecture_true = data.get("implicit_conjecture_true", 0)
    explicit_conjecture_false = data.get("explicit_conjecture_false", 0)
    implicit_conjecture_false = data.get("implicit_conjecture_false", 0)
    unknown = data.get("unknown", 0)
    proved_total = (
        explicit_proof_true
        + implicit_proof_true
        + explicit_proof_false
        + implicit_proof_false
    )
    conjectured_total = (
        explicit_conjecture_true
        + implicit_conjecture_true
        + explicit_conjecture_false
        + implicit_conjecture_false
    )

    total = proved_total + conjectured_total + unknown

    ratio = proved_total / total
    conjecture_ratio = (proved_total + conjectured_total) / total

    proof_table = "| explicitly true | implicitly true | explicitly false | implicitly false | no proof |\n"
    proof_table += "| -- | -- | -- | -- | -- |\n"
    proof_table += "| {:,} | {:,} | {:,} | {:,} | {:,} |\n\n".format(
        explicit_proof_true,
        implicit_proof_true,
        explicit_proof_false,
        implicit_proof_false,
        conjectured_total + unknown,
    )

    conjecture_table = "| explicitly true | implicitly true | explicitly false | implicitly false | no conjecture |\n"
    conjecture_table += "| -- | -- | -- | -- | -- |\n"
    conjecture_table += "| {:,} | {:,} | {:,} | {:,} | {:,} |\n\n".format(
        explicit_conjecture_true,
        implicit_conjecture_true,
        explicit_conjecture_false,
        implicit_conjecture_false,
        unknown,
    )

    return {
        "ratio": ratio,
        "conjecture_ratio": conjecture_ratio,
        "proof_table": proof_table,
        "conjecture_table": conjecture_table,
    }


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="generate the dashboard markdown")
    parser.add_argument(
        "graph_info",
        help="file containing markdown of graph info from generate_dashboard_graph_info.rb",
    )
    parser.add_argument(
        "--out_file",
        default="home_page/dashboard/index.md",
        help="markdown file to pass to jekyll",
    )
    parser.add_argument(
        "--badge_file",
        default="home_page/dashboard/progress_badge.svg",
        help="path to create the progress badge for the Github repo",
    )

    args = parser.parse_args()

    directory = os.path.dirname(args.out_file)
    if not os.path.exists(directory):
        os.makedirs(directory)

    print("extracting histogram...")
    hist_command = [
        os.path.expanduser("~/.elan/bin/lake"),
        "exe",
        "extract_implications",
        "outcomes",
        "equational_theories",
        "--hist",
    ]
    hist_result = subprocess.run(
        hist_command, capture_output=True, text=True, check=True
    )
    print(hist_command)
    print(hist_result.stdout)
    hist_result_finite = subprocess.run(
        hist_command + ["--finite-only"], capture_output=True, text=True, check=True
    )
    print(hist_command + ["--finite-only"])
    print(hist_result_finite.stdout)

    print("generating markdown...")
    hist_general = process_hist(json.loads(hist_result.stdout))
    hist_finite = process_hist(json.loads(hist_result_finite.stdout))

    outfile = open(args.out_file, "w")

    outfile.write("\n")
    outfile.write(
        f"The implication graph is **{hist_general['ratio']:.5%}** complete.\n\n"
    )

    outfile.write(
        """An implication is considered *explicitly true* or *explicitly false* if we have a proof
           of the corresponding proposition formalised in Lean. It is *implicitly true* or
           *implicitly false* if the proposition can be derived by taking the reflexive transitive
           closure of explicitly proven implications.\n\n"""
    )
    outfile.write(
        "Our current counts of implications in each of those categories are:\n\n"
    )
    outfile.write(hist_general["proof_table"])

    outfile.write(
        "\nThe _no proof_ column above represents work that we still need to do.\n"
    )
    outfile.write(
        "Among the _no proof_ implications, we have the following conjecture counts:\n\n"
    )
    outfile.write(hist_general["conjecture_table"])
    outfile.write(
        f"The implication graph is **{hist_general['conjecture_ratio']:.5%}** complete if we include conjectures.\n\n"
    )

    outfile.write("## Finite graph\n\n")
    outfile.write("Some implications are true specifically only for finite magmas.\n\n")
    outfile.write(
        f"The finite implication graph is **{hist_finite['ratio']:.5%}** complete.\n\n"
    )
    outfile.write(hist_finite["proof_table"])
    outfile.write(
        f"The finite implication graph is **{hist_finite['conjecture_ratio']:.5%}** complete if we include conjectures.\n\n"
    )
    outfile.write(hist_finite["conjecture_table"])

    with open(args.graph_info, "r") as f:
        outfile.write(f.read())

    outfile.write(
        """## Raw data

The following compressed JSON blobs contain the raw data generated by project tooling. Note that the exported data includes conjectures.

General graph:

- [extract_implications --json]({{site.url}}/raw_data/general.json.gz)
- [extract_implications --json --closure --only-implications]({{site.url}}/raw_data/general_implications_closure.json.gz)
- [extract_implications raw --full-entries]({{site.url}}/raw_data/general_raw_full_entries.json.gz)
- [extract_implications outcomes]({{site.url}}/raw_data/general_outcomes.json.gz)

Finite graph:

- [extract_implications --json --finite-only]({{site.url}}/raw_data/finite.json.gz)
- [extract_implications --json --closure --only-implications --finite-only]({{site.url}}/raw_data/finite_implicatons_closure.json.gz)
- [extract_implications raw --full-entries --finite-only]({{site.url}}/raw_data/finite_raw_full_entries.json.gz)
- [extract_implications outcomes --finite-only]({{site.url}}/raw_data/finite_outcomes.json.gz)
\n\n"""
    )

    outfile.write("""
## Progress visualization

The image below visualizes the full implication graph from the
Equational Theories Project.

Each pixel indicates the relationship between two laws: A blue pixel means the
first (horizontal coordinate) implies the second (vertical). Red means it does
not. Bright colors mark explicit proofs or countermodels; darker shades mean
the result follows indirectly. Click to magnify or select implications.

\n\n""")
    outfile.write('<div id="progress-status"></div>\n')
    outfile.write('<div id="progress-container" style="width:700px;height:700px;position:relative;background:white;"></div>\n')
    outfile.write("""
<script src="{{site.url}}/progresswidget/progresswidget.js"></script>
<script>
progresswidget({
  container: 'progress-container',
  statusbar: 'progress-status',
  small: '{{site.url}}/progresswidget/thumbnail.jpg',
  full: '{{site.url}}/dashboard/outcomes.png',
  eqdb: '{{site.url}}/fme/eqdb.json'
});
</script>
\n\n"""
    )
    open(args.badge_file, "w").write(make_progress_badge(hist_general["ratio"]))
