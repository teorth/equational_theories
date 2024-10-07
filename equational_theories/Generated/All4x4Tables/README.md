# All 4x4 tables

The Lean proofs here refute every false implication between two equations that
has a counterexample in one of the following kinds of structures:

* every `2x2`, `3x3` or `4x4` magma,
* every cancellative `5x5` magma,
* a motley crew of other `5x5-13x13` finite magmas listed in `data/*.txt`.

Automated tools used to find these counterexamples include:

1. The `2x2-4x4` magmas are brute-forced by a C program and pruned by Python scripts.
2. The `5x5` cancellative magmas are generated using Mace4 and pruned using some Haskell tools.
3. Some magmas constructed by the Z3 solver, gathered from #308.
4. A number of magmas constructed by the Vampire theorem prover, gathered from #276.

# 2x2-4x4 magmas (brute-forcing)

**1.** Compile the brute force script by issuing `gcc -O3 equations.c brute_force_4x4_tables.c` in `src/`.

**2.** Run it over all `2^32` possible 4x4 tables:

```
mkdir tables
python3 drive_c_parallel.py # adjust how many cores you have as necessary
```

**3.** Prune the output to reduce redundant equations:
```
python3 prune.py > data/covering_set.txt
```

**4.** Dump each NxN table:
```
python3 dump_tables.py 2 > ../data/refutations2x2.txt
python3 dump_tables.py 3 > ../data/refutations3x3.txt
python3 dump_tables.py 4 > ../data/refutations4x4.txt
```

**5.** Optionally: generate the lean files
```
python3 generate_lean.py
```

The script in step 5 reads `data/implications.json` to prune the required `Fact`s
in the theorems. As new implications become known this file can be updated using
```
lake exe extract_implications  --json --only-implications equational_theories > equational_theories/Generated/All4x4Tables/data/implications.json
```
and the script re-run to further reduce the size of the theorems.

The brute-forcing takes a couple hundred CPU hours.


# 5x5 and above

Once the 4x4 and smaller magmas have been brute-forced and `refutationsNxN.txt`
generated, run the following bash scripts:
```
MACE4HOME=/path/to/mace4 ./generate_combined_refutations.sh
python3 generate_lean.py
```

These scripts do the following:

**1.** Use Mace4 to generate a list of all 5x5 cancellative magmas up to isomorphism.

**2.** Take the `refutationsNxN.txt` files obtained by brute-forcing, combine it with
the 5x5 cancellative magmas and a hand-curated list of other magmas, then use the
Haskell tools in `finite_magma_tools` to combine them into a shortlist of finite
magma refutations which optimally cover the same set of counterexamples
as all of these. These proofs are output into the `raw_lean_output/` directory.

**3.** Further prune the required `Fact`s using the known positive implications taken
from `implications.json`, and output the final set of Lean-checked proofs.

The Haskell tools require a working `cabal` installation, and the script needs
a compiled and working Prover9/Mace4 suite to generate the cancellative magmas.
Set the environmental variable `MACE4HOME` to point to the latter if not in your path.

# Statistics

Some information about the overlap between different magma sizes:

```
When going from ../data/refutations2x2.txt to ../data/refutations3x3.txt
The number of solved equations goes from 12567055 to 13602457 for a delta of 1035402
And ../data/refutations3x3.txt has 9 / 299 already covered magmas

When going from ../data/refutations2x2.txt to ../data/refutations4x4.txt
The number of solved equations goes from 12567055 to 13732566 for a delta of 1165511
And ../data/refutations4x4.txt has 7 / 515 already covered magmas

When going from ../data/refutations3x3.txt to ../data/refutations2x2.txt
The number of solved equations goes from 13345053 to 13602457 for a delta of 257404
And ../data/refutations2x2.txt has 8 / 10 already covered magmas

When going from ../data/refutations3x3.txt to ../data/refutations4x4.txt
The number of solved equations goes from 13345053 to 13760346 for a delta of 415293
And ../data/refutations4x4.txt has 100 / 515 already covered magmas

When going from ../data/refutations4x4.txt to ../data/refutations2x2.txt
The number of solved equations goes from 13732566 to 13732566 for a delta of 0
And ../data/refutations2x2.txt has 10 / 10 already covered magmas

When going from ../data/refutations4x4.txt to ../data/refutations3x3.txt
The number of solved equations goes from 13732566 to 13760346 for a delta of 27780
And ../data/refutations3x3.txt has 291 / 299 already covered magmas
```
