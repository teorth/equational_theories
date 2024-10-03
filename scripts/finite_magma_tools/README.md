# Haskell Finite Magma Tools

This directory contains some Haskell utilities I wrote to help manage finite
magmas and find counterexamples to implications between equations.

If we construct an operator table of a small finite magma where equation X
holds but equations Y and Z fail, then we can conclude that X does not imply Y
and X does not imply Z.

The tools here aim to reduce redundancy in this process by optimizing the
selection and checking of finite magmas and equations.

## Build Instructions

To build these tools, you need a recent version of the Glasgow Haskell Compiler
and the build tool Cabal. You can then build and run the runutables directly:

```
cabal run make-plan < input.txt > output.txt
cabal run min-cover < input.txt > output.txt
cabal run gen-refutations < input.txt
cabal run parse-mace4 < input.txt > output.txt
```

## The tools

**make-plan**

Generates optimized proof plans from lists of finite magmas and the equations they
satisfy, using a cost model. The goal is to reduce the number of verifications
required by the Lean kernel while ensuring that all counterexamples of the original
list still remain covered.

Usage: `cabal run make-plan < input.txt > output.txt`


The input should be a list of finite magmas and the equations they satisfy,
as in e.g. `Generated/All4x4Tables`:

```
Table [[0,1],[1,0]]  // the operator table
Proves [1]           // list of equations that it satisfies
```

The output is an optimized plan with entries in the following format:

```
Magma [[0,1],[1,0]]  // the operator table for G
Satisfies [1,307]    // equations whose satisfaction we'll prove in G
Refutes [2]          // equations for which we'll find a counterexample in G
```


By default, all equations are checked. But sometimes you'll want to make a plan
for a restricted set of equations (e.g. a set pruned by equivalence). To focus
on specific equations modify the `equationsOfInterest` function in Main.hs.
The cost model can also be changed there.

**min-cover**

Finds a minimal subset of the given list of finite magmas and the equations they
satisfy which still provides counterexamples to the same set of potential
implications.

Usage: `cabal run min-cover < input.txt > output.txt`

The input can be in the same format as the output of make-plan or All4x4Tables.

Optimization is performed using an SMT solver. It is very slow for large equation
sets or many magmas, and it's not inteded to be used on full sets of either.
Instead, it's mostly a useful ingredient for other heuristics. Adjust
equationsOfInterest in the configuration section of Main.hs before running.
As an example, try `cabal run min-cover < examples/short_refutations.txt`.

**gen-refutations**

Generates Lean refutation files from the input plan. Each output file contains
the necessary Lean code to check the refutations, in the same format as used in
`All4x4Tables`.

Usage: `cabal run gen-refutations < input.txt`

The input should be the output from make-plan. The output will be `Refutation<n>.lean`
where each `<n>` corresponds to an input magma.

**parse-mace4**

Converts mace4 output files (pushed through get_interps) into make-plan's
output format.

Usage: `cabal run gen-refutations < input.txt`

The input file should contain only a list of interpretations. The `get-interps`
tool distributed with Mace4 is able to pre-process files in the required way.

You can supply the `-c /path/to/equations.txt` or `--check-equations` optional
argument: if supplied, the tool will check which of the equations in the given
text file hold in each magma, and output it in `All4x4Tables` format.

**Other tools**

More tools are on the way. The source code also has many utility functions
(parsers etc.) that might be useful when working with finite magmas. Drop into a
repl using `cabal repl make-plan` to try them.
