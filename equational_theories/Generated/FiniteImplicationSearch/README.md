# Finite Implication Search

This tool searches for finite implications by using Vampire and making use of the fact left and right inverses are interchangeable in finite domains.

## Step 1

First, we generate a directory full of TPTP files to pass to Vampire. These files include commented out JSON blobs that are used for proof generation later.

```sh
lake exe export_equations > equations.json
lake exe extract_implications unknowns --proven --finite-only --duality | ruby -rjson -e 'JSON.parse($stdin.read).each { |s| puts s["lhs"][8,10] + "," + s["rhs"][8,10] }' | sort -u > unknowns.csv
cat unknowns.csv | ruby equational_theories/Generated/FiniteImplicationSearch/src/generate_tptp.rb equations.json finite_implications
```

This creates a directory `finite_implications/`.

## Step 2

Run Vampire, this generates `.p.out` files for every TPTP `.p` file.

```sh
ls finite_implications/*.p | ruby -ne 'puts "vampire --output_axiom_names on --proof_extra full -t 0.4s #{$_.chomp} > #{$_.chomp}.out"' > /tmp/run.sh
bash /tmp/run.sh
```

## Step 3

Post-process Vampire output:

```sh
python equational_theories/Generated/FiniteImplicationSearch/src/process.py finite_implications/*.p > Proofs1.lean
```

Then transitive reduction should be run.
