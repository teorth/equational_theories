This law is equivalent to the conjunction of [law 375](https://teorth.github.io/equational_theories/implications/?375) `x ◇ y = (x ◇ x) ◇ y` and the ["right-zero product" law 343](https://teorth.github.io/equational_theories/implications/?343) `x ◇ y = z ◇ (x ◇ y)` which states that all products are right zeros.

The set of squares coincides with the set of products and with the set of idempotent elements.

The free magma on some set `Σ` of generators for this law consists of finite non-empty lists of elements of `Σ` whose first two entries cannot be equal unless the list has length 2, with the operation `[s, …, t] ◇ [u, …, v] = [u, …, v]` when the second operand has more than one item, and `[s, s] ◇ [u] = [s, u]`, and otherwise `[s, …, t] ◇ [u] = [s, …, t, u]`.

In particular, the free magma with one generator `x` for this law is a two-element magma `{x,x◇x}`.

This law cannot hold in a non-trivial quasigroup.
