## The "Dupont" equation

Closely related to the ["Dupond" equation, 1692](https://teorth.github.io/equational_theories/implications/?1692).  In particular, the two equations are equivalent for finite magmas, but [neither implies the other for infinite ones](https://teorth.github.io/equational_theories/blueprint/infinite-magma-constructions-chapter.html#dupont-section).  See [this discussion](https://leanprover.zulipchat.com/#narrow/stream/458659-Equational/topic/Proposed.20new.20target.3A.2063.20and.201692.20.28.22Dupont.20and.20Dupond.22.29).

This pair shares many similarities with the "Asterix" ([equation 65](https://teorth.github.io/equational_theories/implications/?65)) and "Obelix" ([equation 1491](https://teorth.github.io/equational_theories/implications/?1491)) pair.

The operation `x◆y = y◇(y◇x)` satisfies law 229, the dual of [law 118](https://teorth.github.io/equational_theories/implications/?118).  For finite magmas (or for quasigroups) the operation `◆` satisfies [law 125](https://teorth.github.io/equational_theories/implications/?125), and this defines a one-to-one correspondence between finite magmas (or quasigroups) satisfying law 63 and those satisfying law 125, with the inverse correspondence being to define `x◇y = (x◆y)◆x`.  Thus the inequivalent laws 63 and 125 share the same finite spectrum.

As observed by Belousov [1], in a quasigroup satisfying this law, the pair of equations `x◇y=a` and `x=y◇b` has a unique solution `x=b/a` and `y=(b/a)/b`, which means that the quasigroup is orthogonal to its (23)-parastrophe.  It is part of a collection of [seven laws](http://arxiv.org/abs/1509.00796) with similar properties.

[1]: V.D. Belousov. Parastrophic-orthogonal quasigroups. Translated from the 1983 Russian original. Quasigroups Relat. Syst., 13(1):25–72, 2005.
