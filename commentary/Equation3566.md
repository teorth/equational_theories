This law is equivalent to [law 333](https://teorth.github.io/equational_theories/implications/?333) (graphic property) together with [law 395](https://teorth.github.io/equational_theories/implications/?395) (dual of the reduction law).  The squaring map `S: x ↦ x ◇ x` is idempotent, namely `S(S(x)) = S(x)`.

The free magma on some set `S` of generators for this law consists of finite non-empty lists of elements of `S` whose last element does not appear elsewhere in the list except possibly in next-to-last position, with the product `[s, …, t] ◇ [v] = [t, v]`, and, when the second operand has more than one element, `[s, …, t] ◇ [u, …, v]` is `[t, u, …, v]` if `t≠v` and otherwise `[u, …, v]` if `t=v`.

In particular, the free magma with one generator `x` for this law is a two-element magma `{x,x◇x}`.

This law cannot hold in a non-trivial quasigroup.
