This law implies exactly the laws whose left-hand side and right-hand side have the same last two variables.  It is equivalent to the [associative law 4512](https://teorth.github.io/equational_theories/implications/?4512) together with the [law 343](https://teorth.github.io/equational_theories/implications/?343) `x◇y = z◇(x◇y)`.

A 3634-magma `M` is characterized by the set `P = {x◇y|x,y∈M}` (on which the operation reduces to right projection), and a collection of right-multiplication maps `R_x: P→P` for `x ∈ M∖P` with the compatibility condition that the image of each `R_x ∘ R_y` is a singleton, `{x◇y}`.

The free magma on some set `S` of generators for this law is `S ⊔ S×S`, with the magma operation `s◇t=(s,t)`, `s◇(t,u)=(t,u)`, `(s,t)◇u=(t,u)`, `(s,t)◇(u,v)=(u,v)`.
