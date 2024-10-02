cd src

# Compile the brute force script
gcc -O3 equations.c brute_force_4x4_tables.c

# Run it over all 2**32 possible 4x4 tables
mkdir tables
python3 drive_c_parallel.py # adjust how many cores you have as necessary

# Prune the output to reduce redundant equations
python3 prune.py > data/covering_set.txt

# Dump the tables and split into files
python3 dump_tables.py > data/refutations.txt

# Generate the lean files
python3 generate_lean.py

This scripts also reads `data/implications.json`, to prune the resulting `Fact` in the theorems.
As new implications are known this file can be updated using
```
lake exe extract_implications  --json --only-implications equational_theories > equational_theories/Generated/All4x4Tables/data/implications.json
```
and the script re-run to redue the size of the theorems.
