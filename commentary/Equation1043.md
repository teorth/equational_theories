This law implies [law 10](https://teorth.github.io/equational_theories/implications/?10) `x = x◇(y◇x)`.  Squares are right-units ([law 11](https://teorth.github.io/equational_theories/implications/?11) `x = x◇(y◇y)` and left zeros ([law 360](https://teorth.github.io/equational_theories/implications/?360) `x◇x = (x◇x)◇y`).

In terms of the undirected graph implied by law 10, which connects `x` and `y` if `x=x◇y` (equivalently `y=y◇x`), this means that squares are connected to all vertices including themselves.

This law cannot hold in a (non-trivial) commutative magma or quasigroup.

The free magma with one generator `x` for this law is a two-element magma `{x,x◇x}`.

As [determined in this Zulip thread](https://leanprover.zulipchat.com/#narrow/channel/458659-Equational/topic/A.20single.20axiom.20for.20Boolean.20algebra/near/537281668), the dual law 2536 `x = (y◇((y◇x)◇z)) ◇ x`, together with the Tanaka law 4658 `(x◇y)◇y = (y◇x)◇x` (dual to [law 4293](https://teorth.github.io/equational_theories/implications/?4293)), characterizes [implication algebras](https://www.jstor.org/stable/43679502), also called semi-Boolean algebras, which are semi-lattices whose ideals are Boolean algebras.  In other words, these two laws 2536 and 4658 generate the equational theory of the magma `{0,1}` with `1◇0=0` and other `x◇y=1`.  Any magma satisfying these two laws is a submagma of a power of that 2-element magma.
