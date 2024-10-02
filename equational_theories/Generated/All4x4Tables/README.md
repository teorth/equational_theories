# How to run this

```bash
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
```

# Statistics

Here's the overlap between different magma sizes

```
When going from ../data/refutations2x2.txt to ../data/refutations3x3.txt
The number of solved equtions goes from 12567055 to 13602457 for a delta of 1035402
And ../data/refutations3x3.txt has 9 / 299 already covered magmas

When going from ../data/refutations2x2.txt to ../data/refutations4x4.txt
The number of solved equtions goes from 12567055 to 13732566 for a delta of 1165511
And ../data/refutations4x4.txt has 7 / 515 already covered magmas

When going from ../data/refutations3x3.txt to ../data/refutations2x2.txt
The number of solved equtions goes from 13345053 to 13602457 for a delta of 257404
And ../data/refutations2x2.txt has 8 / 10 already covered magmas

When going from ../data/refutations3x3.txt to ../data/refutations4x4.txt
The number of solved equtions goes from 13345053 to 13760346 for a delta of 415293
And ../data/refutations4x4.txt has 100 / 515 already covered magmas

When going from ../data/refutations4x4.txt to ../data/refutations2x2.txt
The number of solved equtions goes from 13732566 to 13732566 for a delta of 0
And ../data/refutations2x2.txt has 10 / 10 already covered magmas

When going from ../data/refutations4x4.txt to ../data/refutations3x3.txt
The number of solved equtions goes from 13732566 to 13760346 for a delta of 27780
And ../data/refutations3x3.txt has 291 / 299 already covered magmas
```