This law is equivalent to the conjunction of the [proto-unital law 378](https://teorth.github.io/equational_theories/implications/?378) `x ◇ y = (x ◇ y) ◇ y` which states that right multiplications are idempotent, and the ["right-zero product" law 343](https://teorth.github.io/equational_theories/implications/?343) `x ◇ y = z ◇ (x ◇ y)` which states that all products are right zeros.

The set of squares coincides with the set of products and with the set of idempotent elements.

The free magma on some set `Σ` of generators for this law consists of finite non-empty lists of elements of `Σ` with consecutive elements being distinct except the first two, with the operation `[s, …, t] ◇ [u, …, v] = [u, …, v]` when the second operand has more than one item, and otherwise `[s, …, t] ◇ [u] = [s, …, t, u]` for `t ≠ u`, and finally `[s, …, t] ◇ [t] = [s, …, t]`.

In particular, the free magma with one generator `x` for this law is a two-element magma `{x,x◇x}`.

This law cannot hold in a non-trivial quasigroup.
