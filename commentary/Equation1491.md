## The "Obelix" equation

Closely related to the ["Asterix" equation, 65](https://teorth.github.io/equational_theories/implications/?65).  In particular, the "Asterix" and "Obelix" equations are equivalent for finite magmas or for quasigroups, but neither implies the other for [infinite ones](https://teorth.github.io/equational_theories/blueprint/infinite-magma-constructions-chapter.html#asterix-section).

A greedy translation-invariant construction of Obelix magmas is [given here](https://leanprover.zulipchat.com/#narrow/channel/458659-Equational/topic/Obelix.3A.20joining.20two.20approaches).

The free magma with one generator for this law is isomorphic to `ℤ/3ℤ` equipped with `x◇y = y+1`.  In particular, in any magma the squaring map `S: x ↦ x◇x` and cubing maps `B: x ↦ x◇(x◇x)` and `C: x ↦ (x◇x)◇x` are bijections of order 3 with `S(x) = C(x)` and `B(x) = S(S(x))` and `S(S(S(x))) = x`.

This law also implies that left multiplications are injective.

In a quasigroup this law is equivalent to the Asterix law 65, hence parastrophically equivalent to [law 4443](https://teorth.github.io/equational_theories/implications/?4443) in the sense that `◇` obeys the Obelix law if and only if the right division operation defined by `(x/y)◇y = x` obeys law 4443.  It cannot hold in a non-trivial group.
