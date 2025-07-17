## The "Asterix" equation

Closely related to the ["Obelix" equation, 1491](https://teorth.github.io/equational_theories/implications/?1491).  In particular, the "Asterix" and "Obelix" equations are equivalent for finite magmas, and more generally for left-quasigroups, but neither implies the other for [infinite ones](https://teorth.github.io/equational_theories/blueprint/infinite-magma-constructions-chapter.html#asterix-section).

This law implies that left multiplications are surjective.  A finite magma satisfying this law is thus a left quasigroup (bijective left multiplications).  This law also implies that the squaring map `S: x ↦ x◇x` and cubing maps `B: x ↦ x◇(x◇x)` and `C: x ↦ (x◇x)◇x` obey `x = S(B(x)) = C(B(x))` hence `S` and `C` are surjective and `B` injective.  This law together with associativity implies the right-projection [law 5](https://teorth.github.io/equational_theories/implications/?5), so the law cannot hold in any non-trivial group.

Examples of models include the linear model `x ◇ y = ω y` (in any field with a cube root of unity), or `x ◇ y = y + 1` (in `ℤ/3ℤ`).  The second model is the free magma with one generator for the Obelix equation, hence the (infinite) free magma of the Asterix equation has no finite quotient besides the trivial one and that 3-element magma.
