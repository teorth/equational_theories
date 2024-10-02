import argparse
import json

if __name__ == '__main__':
    parser = argparse.ArgumentParser(description="generate the dashboard markdown")
    parser.add_argument("hist_file",
                        help="json file containing output of `lake exe extract_implications outcomes --hist")
    parser.add_argument("--out_file",
                        default="home_page/dashboard.md",
                        help="markdown file to pass to jekyll")

    args = parser.parse_args()
    with open(args.hist_file, 'r') as f:
        data = json.load(f)

    explicit_proof_true = data['explicit_proof_true']
    implicit_proof_true = data['implicit_proof_true']
    explicit_proof_false = data['explicit_proof_false']
    implicit_proof_false = data['implicit_proof_false']
    unknown = data['unknown'];
    known_total = explicit_proof_true + implicit_proof_true + explicit_proof_false + implicit_proof_false
    total = known_total + unknown

    outfile = open(args.out_file, 'w')
    outfile.write("\n")
    outfile.write("Implication counts (see [this github issue](https://github.com/teorth/equational_theories/issues/29) for an explanation):\n\n")
    outfile.write("| explicitly true | implicitly true | explicitly false | implicitly false | unknown |\n")
    outfile.write("| -- | -- | -- | -- | -- |\n")
    outfile.write("| {} | {} | {} | {} | {} |\n".format(
        explicit_proof_true, implicit_proof_true, explicit_proof_false,
        implicit_proof_false, unknown))
    outfile.write("\n")
    ratio = known_total / total
    outfile.write(f"**{ratio:.3%}** complete")

