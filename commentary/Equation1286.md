## An equation with non-trivial linear models

Using the linear magma model `x ◇ y = ax + by`, we can produce a model of this law that contradicts [Equation 3](https://teorth.github.io/equational_theories/implications/?3) when `a+b ≠ 1`, `b^2=-a/(a^2+1)` and `b=(2a^2+1)/(a^5+a^3)`. This can be satisfied by taking `a` to be a root of `a^5+2a^4+3a^3+3a^2+a+1`.  For instance, working in `ℤ/pℤ`, one can take `(p,a,b) = (11,1,7)` or `(p,a,b) = (7,6,2)` (the latter is [known to be the smallest model](https://leanprover.zulipchat.com/#narrow/channel/458659-Equational/topic/Implication.20Statistics/near/480795569)).  See [this discussion](https://leanprover.zulipchat.com/#narrow/stream/458659-Equational/topic/An.20old.20new.20idea).

This law implies that left multiplications are surjective.
