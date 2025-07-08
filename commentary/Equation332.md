## A law from MathOverflow

[This response by pastebee](https://mathoverflow.net/a/450905/766) to a [MathOverflow question](https://mathoverflow.net/questions/450890/is-there-an-identity-between-the-commutative-identity-and-the-constant-identity) established that [law 387](https://teorth.github.io/equational_theories/implications/?387) (equivalent and dual to law 332) is strictly between the [constant law 46](https://teorth.github.io/equational_theories/implications/?46) and the [commutative law 43](https://teorth.github.io/equational_theories/implications/?43).

This law implies that the magma operation is commutative.  The squaring operation `x ↦ x◇x` is idempotent (namely `S(S(x)) = S(x)`) and the magma operation is characterized by its action on squares in the sense that `x◇y=(x◇x)◇(y◇y)`.  However, the set of squares is not necessarily stable under the magma operation.

This law cannot hold in a non-trivial group.

The free magma with one generator `x` for this law is a two-element magma `{x,x◇x}` with a constant law.
