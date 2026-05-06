The dual law 4658 `(x◇y)◇y = (y◇x)◇x` is the [Tanaka equation](http://arxiv.org/abs/2201.07009), also called quasi-commutativity in the context of implication algebras.

As [determined in this Zulip thread](https://leanprover.zulipchat.com/#narrow/channel/458659-Equational/topic/A.20single.20axiom.20for.20Boolean.20algebra/near/537281668), law 4658, together with law 2536 `x = (y◇((y◇x)◇z)) ◇ x` (dual to [law 1043](https://teorth.github.io/equational_theories/implications/?1043)), characterizes [implication algebras](https://www.jstor.org/stable/43679502), also called semi-Boolean algebras, which are semi-lattices whose ideals are Boolean algebras.  In other words, these two laws 2536 and 4658 generate the equational theory of the magma `{0,1}` with `1◇0=0` and other `x◇y=1`.  Any magma satisfying these two laws is a submagma of a power of that 2-element magma.

Quasigroups satisfying law 4658 are called ARO quasigroups [1] in reference to affine regular octagons.  They violate commutativity maximally in the sense that `x◇y=y◇x` only for `x=y`.  Hoops satisfying law 4658 are called [Wajsberg hoops](https://math.chapman.edu/~jipsen/structures/doku.php?id=wajsberg_hoops).

This law cannot hold in a non-trivial group.

This law states that the operation `x◆y = x◇(x◇y)` is commutative.

[1] Volenec, V., Kolar-Begovic, Z., and Kolar-Super, R. (2010). ARO-quasigroups. Quasigroups and related systems, 24(2), 213-228.
