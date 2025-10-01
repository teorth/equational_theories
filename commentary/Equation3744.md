## The 1978 Putnam "bypass law": pointed set fibrations on Cartesian products

Called the "bypass law" in the 1978 Putnam, which also introduced [Equation 381](https://teorth.github.io/equational_theories/implications/?381) and [Equation 3722](https://teorth.github.io/equational_theories/implications/?3722). Problem A4 of the 1978 Putnam asked to show (in our language) that [Equation 3744 implies Equations 3722 and 381](https://teorth.github.io/equational_theories/blueprint/implications-chapter.html#3744_implies_3722_381). 

This law is equivalent to the [law 381](https://teorth.github.io/equational_theories/implications/?381) `x◇y = (x◇z)◇y` and its dual law 329.  It is also equivalent to law 381 and the [associative law 4512](https://teorth.github.io/equational_theories/implications/?4512).  It implies exactly the laws whose left-hand side and right-hand side have the same first variable and the same last variable and the operation appears at least once on each side.  (In that respect it is analogous to [law 3634](https://teorth.github.io/equational_theories/implications/?3634).)  In particular this law implies that the squaring map `S: x ↦ x◇x` is idempotent, namely `S(S(x))=S(x)`.

The left cosets `x◇M = {x◇y|y∈M}` are pairwise equal or disjoint, and likewise for the right cosets.  The set of products `P = {x◇y|x,y∈M}` is isomorphic to a Cartesian product `S×T` of any of the left cosets with any of the right cosets, with the operation `(s,t)◇(u,v)=(s,v)` for `s,u∈S` and `t,v∈T`.  The whole magma is a fibration over `P` by pointed sets, with the projection `M → P` given by the squaring map `x ↦ x◇x`, which is a magma morphism.  In particular any magma satisfying this law is a submagma of a linear magma.

The free magma on some set `Σ` of generators for this law is `Σ ⊔ Σ×Σ`, with the magma operation `s◇t=(s,t)`, `s◇(t,u)=(s,u)`, `(s,t)◇u=(s,u)`, `(s,t)◇(u,v)=(s,v)`.

This law cannot hold in a non-trivial quasigroup.
