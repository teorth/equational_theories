This tool uses already proven implications to search from a given hypothesis by repeated substitutions from known implications. It uses a crude textual representation of equations, so it's limited in what forms of substitutions it can perform, and it's implementation makes it _much_ slower and less efficient than it could be. One advantage it has over my previous more naive brute-force methods, is that starting from a single hypothesis it can try to reach any (not-yet proven) goal, rather than working with a single goal at a time. Also, now that simple rewrites have discovered many simple implications, this tool can take 'larger' steps by leveraging known implications.

EquationSearch makes use of meet-in-the-middle graph search, where it searches outwards from all hypotheses in a given equivalence class/strongly connected component and from potential goals. Doing so reduces the search space, and the tool automatically adjusts search depth on the hypothesis-/goal- side depending on the number of hypotheses/goals and a configured branching factor.

Findings:
- Oct 1 2024: Run1 + Run2 generated ~500k new (transitive) implications.
- Oct 3 2024: Run3-7 generated ~150k new (transitive) implications.

1) Get the current implications graph

```sh
lake build
lake exe extract_implications --json equational_theories.Generated equational_theories.Subgraph > main_implications.json
cat main_implications.json | ruby -rjson -e 'JSON.parse($stdin.read)["implications"].each { |s| puts s["lhs"][8,10] + "," + s["rhs"][8,10] }' | sort -u > main_implications.csv
ruby scripts/transitive_reduction.rb main_implications.csv | sort -u > main_implications.reduced.csv
ruby scripts/transitive_closure.rb main_implications.reduced.csv > main_implications.closure.csv
```

2) Run the search

Note that there are some configuration options at the top of search.rb.

```sh
ruby equational_theories/Generated/EquationSearch/src/search.rb new_state.closure.csv REFUTATION_PAIRS.csv >> theorems.lean
```

3) Extract the new theorems you need to include

```sh
cat theorems.lean | ruby -ne 'puts "#{$1},#{$2}" if $_ =~ /Equation(\d+)_implies_Equation(\d+)/' | sort -u > new_theorems.csv
cat main_implications.csv new_theorems.csv | sort -u > new_state.csv
ruby scripts/transitive_reduction.rb new_state.csv | sort -u > new_state.reduced.csv
ruby scripts/transitive_closure.rb new_state.csv > new_state.closure.csv
comm -13 main_implications.csv new_state.reduced.csv > new_theorems_to_include.csv

ruby equational_theories/Generated/EquationSearch/src/print_specific_theorems.rb new_theorems_to_include.csv theorems.lean | grep -v "/-" > Theorems1.lean
```

4) Fix-up failures and clean-up proofs

EquationSearch should always compute a correct path of substitutions; however, it outputs `nth_rewrite`s that may be missing a required variable, or have the wrong index, e.g. `nth_rewrite 1 [eq158]` may need to be rewritten to `nth_rewrite 2 [eq158]` or `nth_rewrite 1 [eq158 x]` or even `nth_rewrite 3 [eq158 z x]`. The following script slowly goes through, trying to bruteforce any failures, and prints the successful theorems.

```sh
ruby equational_theories/Generated/EquationSearch/src/fixup_rewrites.rb Theorems1.lean > Theorems2.lean
```

The proofs include `sorry`s for known impliciations, the following script resolves them by graph search:

```sh
ruby equational_theories/Generated/EquationSearch/src/dont_be_sorry.rb Theorems2.lean main_implications.csv > Theorems3.lean
```

Some trivial clean-up.

```sh
cat Theorems3.lean | ruby -e 'puts $stdin.read.gsub("  symm\n  symm\n", "")' > Theorems4.lean
```
