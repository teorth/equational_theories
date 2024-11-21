# Finite Implication Search

This tool searches for finite implications by using Vampire and adding axioms for various facts that hold true in finite domains.

Note that if `generate_tptp.rb` is not passed any options, it can also be used to generate Lean proofs for ordinary implications in the general implication graph.

## Finite implication search methods

- Left and right inverses are interchangeable in finite domains. (Note that currently the inverses option only searches for inverses of the source of the implication, and not the destination. One has to manually check implications to the inverses of any destinations.)
- Injectivity bi-implies surjectivity (Note: you can add axioms to search with, but `process.py` can't generate the Lean proofs for the resulting hits.)
- A heuristic method to look for [proofs by periodicity](https://leanprover.zulipchat.com/#narrow/channel/458659-Equational/topic/Austin.20pairs/near/483445305).

See the options of `generate_tptp.rb`.

## Basic usage

### Step 1

First, we generate a directory full of TPTP files to pass to Vampire. These files include commented out JSON blobs that are used for proof generation later. The input is a CSV of implications to attempt.

```sh
lake exe extract_implications unknowns --proven --finite-only --duality | ruby -rjson -e 'JSON.parse($stdin.read).each { |s| puts s["lhs"][8,10] + "," + s["rhs"][8,10] }' | sort -u > unknowns.csv
cat unknowns.csv | ruby equational_theories/Generated/FiniteImplicationSearch/src/generate_tptp.rb --inverses finite_implications
```

This creates a directory `finite_implications/`.

### Step 2

Run Vampire, this generates `.p.out` files for every TPTP `.p` file.

```sh
find finite_implications -name \*.p | ruby -ne 'puts "vampire --output_axiom_names on --proof_extra full -t 0.5s #{$_.chomp} > #{$_.chomp}.out"' > /tmp/run.sh
bash /tmp/run.sh
```

Note that depending on the options used and the underlying implications, you may want to increase the timeout from 0.5s.

### Step 3

Post-process Vampire output:

```sh
python equational_theories/Generated/FiniteImplicationSearch/src/process.py finite_implications/*.p > Proofs1.lean
```

Then transitive reduction should be run.
