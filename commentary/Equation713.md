## A law for which greedy completion barely works

This is one of the laws where greedy completion has been shown (via extensive SAT-solver calculations) to work, but only barely.  As such, the proof of anti-implications from these laws is extremely lengthy, to the extent that Lean struggles to verify them.  See [this discussion](https://leanprover.zulipchat.com/#narrow/stream/458659-Equational/topic/1076.20!.3D.3E.203/near/476933251).

This law implies that left multiplications are surjective, hence finite magmas are left quasigroups (bijective left multiplications).  In left quasigroups, this law is equivalent to [law 11228](https://teorth.github.io/equational_theories/implications/?11228) `x = y ◇ ((y ◇ (y ◇ x)) ◇ (y ◇ x))`, whose free magma with one generator is `ℤ/3ℤ` equipped with `x ◇ y = y + 1`.  Hence the (infinite) free magma of the 713 equation has no finite quotient besides the trivial one and that 3-element magma.

In quasigroups, this law implies the [idempotence law 3](https://teorth.github.io/equational_theories/implications/?3) `x = x◇x`.  It cannot hold in a non-trivial group.
