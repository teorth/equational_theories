This law is equivalent to the conjunction of [law 385](https://teorth.github.io/equational_theories/implications/?385) `x ◇ y = (y ◇ x) ◇ y`, and the ["right-zero product" law 343](https://teorth.github.io/equational_theories/implications/?343) `x ◇ y = z ◇ (x ◇ y)` which states that all products are right zeros.

The set of squares coincides with the set of products and with the set of idempotent elements.

The free magma on some set `Σ` of generators for this law consists of finite non-empty lists of elements of `Σ` where the first and third entries cannot be equal, with the operation `[s, …, t] ◇ [u, …, v] = [u, …, v]` when the second operand has more than one item, and otherwise `[s, …, t] ◇ [u] = [s, …, t, u]` except in the special case `[s, t] ◇ [s] = [t, s]`.

In particular, the free magma with one generator `x` for this law is a two-element magma `{x,x◇x}`.

This law cannot hold in a non-trivial quasigroup.
