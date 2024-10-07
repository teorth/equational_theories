# Brute Force Linear Ops

This code enumerates all linear operators `op(x,y) = a*x + b*y` via brute force.

First compile everything
```
gcc -O3 -c -o equations.o equations.c
gcc -O3 -g brute_force_linear_equations.c equations.o -fopenmp -lm
```

Then run the script
```
./a.out > log
python3 export.py
# output is in new.lean
```

This should generate refutations for ~13.3 million implications.
Many of these are covered by previous refutations, but a few are new.