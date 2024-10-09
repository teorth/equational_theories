# Working with the graph

The implication and non-implication graphs can be extracted from the current source state by making use of the `extract_implications` tool. See `lake exe extract_implications -h` for supported options.

## Transitive closure and transitive reduction

The [transitive closure](https://en.wikipedia.org/wiki/Transitive_closure#In_graph_theory) of the implication graph calculates the maximum reachable set from a given node, and the [transitive reduction](https://en.wikipedia.org/wiki/Transitive_reduction) calculates the minimal set of edges required to maintain reachability on the graph. Various implementations exist in Python ([closure](/scripts/process_implications.py) [reduction](/equational_theories/Generated/SimpleRewrites/src/find_redundant.py)), Ruby ([closure](/scripts/transitive_closure.rb) [reduction](/scripts/transitive_reduction.rb)), and Lean ([closure](/equational_theories/Closure.lean)).

## Reducing automated proofs of implications

Only the minimal required set of proofs should be submitted upstream. The minimal set can be calculated by computing `reduction(current implications ∪ new implications) - current implications`. Look at Steps 1 and 3 [here](/equational_theories/Generated/EquationSearch/README.md) for an example.

## Reducing automated proofs of implications

TODO
