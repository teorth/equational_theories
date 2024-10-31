This equation [admits an unusually large finite magma](https://leanprover.zulipchat.com/#narrow/channel/458659-Equational/topic/Outstanding.20equations.2C.20v1/near/478094170) (of order 12), that can be used to disprove some implications.  Magmas with this law are somewhat "mutable" in practice; one can modify a few entries of the multiplication table, and can sometimes add or remove some elements and still retain the law.

The free magma of this law, while not fully understood, has some useful properties, such as "unique factorization", that can be used to rule out some implications.  See [this chapter of the blueprint](https://teorth.github.io/equational_theories/blueprint/854-chapter.html).  A greedy algorithm that incorporates this unique factorization law and some other axioms seems to be promising.

Simple examples of such laws include left-absorptive magmas (with `x ◇ y = x`), as well as the cyclic group `ℤ/3ℤ` with `x ◇ y = x` for `y ≠ x` and `x ◇ x = x - 1`.
