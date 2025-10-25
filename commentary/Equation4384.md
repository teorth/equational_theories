This law is equivalent to the conjunction of [law 4380](https://teorth.github.io/equational_theories/implications/?4380) (equality of left and right cubes) and [law 4586](https://teorth.github.io/equational_theories/implications/?4586) (which states that `(x ◇ y) ◇ z` only depends on `x`).

This law implies that the squaring map `S: x ↦ x◇x`  `S(S(S(x))) = S(S(x))`.  The set of squares and the set of cubes are submagmas.

This law cannot hold in a non-trivial quasigroup.

The free magma on some set `Σ` of generators for this law consists of finite non-empty lists of elements of `Σ`, with the operation defined by `[s] ◇ [t, …, u] = [s, t, …, u]`, and `[s, …, t] ◇ _ = [s, s, s]` if the list in the first operand has at least two entries.
