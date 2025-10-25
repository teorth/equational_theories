## The "Asterix" equation

Closely related to the ["Obelix" equation, 1491](https://teorth.github.io/equational_theories/implications/?1491).  In particular, the "Asterix" and "Obelix" equations are equivalent for finite magmas, and more generally for left-quasigroups, but neither implies the other for [infinite ones](https://teorth.github.io/equational_theories/blueprint/infinite-magma-constructions-chapter.html#asterix-section).

This law implies that left multiplications are surjective.  The Asterix law also implies that the squaring map `S: x ↦ x◇x` and cubing maps `B: x ↦ x◇(x◇x)` and `C: x ↦ (x◇x)◇x` satisfy `x = S(B(x)) = C(B(x))` hence `S` and `C` are surjective and `B` injective.

A finite magma satisfying this law is a left quasigroup (bijective left multiplications).  In a left quasigroup, this law holds if and only if the left division operation defined by `y◇(y:x) = x` satisfies the same law `x=y:(x:(y:x))`.  Law 65 is also parastrophically equivalent to [law 4443](https://teorth.github.io/equational_theories/implications/?4443) since in a right quasigroup, `◇` satisfies law 65 if and only if the right division operation defined by `(x/y)◇y=x` satisfies law 4443 `x/(y/x) = (y/x)/y`.  Among quasigroups (more generally if right multiplications are injective or surjective), this law implies the [idempotence law 3](https://teorth.github.io/equational_theories/implications/?3) `x=x◇x`.

This law together with associativity implies the right-projection [law 5](https://teorth.github.io/equational_theories/implications/?5), so the law cannot hold in any non-trivial group.

Examples of models include the linear model `x ◇ y = ω y` (in any field with a cube root of unity), or `x ◇ y = y + 1` (in `ℤ/3ℤ`).  The second model is the free magma with one generator for the Obelix equation, hence the (infinite) free magma of the Asterix equation has no finite quotient besides the trivial one and that 3-element magma.
