## An Asterix-like equation

For finite magmas, or for quasigroups, [law 206](https://teorth.github.io/equational_theories/implications/?206) and law 1648 are equivalent.  Without such assumptions, neither implication holds.  By duality the same holds for [law 124](https://teorth.github.io/equational_theories/implications/?124) and [law 1924](https://teorth.github.io/equational_theories/implications/?1924).  Discussed in [this thread](https://leanprover.zulipchat.com/#narrow/stream/458659-Equational/topic/1076.20!.3D.3E.203) and [this thread](https://leanprover.zulipchat.com/#narrow/stream/458659-Equational/topic/1648.20!.3D.3E.20206).  For infinite magmas, the implication is false, with [one construction based on the infinite 3-regular tree](https://leanprover.zulipchat.com/#narrow/stream/458659-Equational/topic/1648.20!.3D.3E.20206/near/476985846).

A nice example of a translation-invariant magma obeying this equation is `x ◇ y = x - sgn(y-x)` on the integers.

The coefficients of the linearization `ax+by` of 1648 are the golden ratio.

This law implies that right multiplications are injective.
