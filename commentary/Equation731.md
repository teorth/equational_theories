This law implies that all left multiplications are bijective and all square to the same map, the left cubing map `B: x ↦ x◇(x◇x)` (namely `y◇(y◇x) = B(x)` for all `x,y`).  The squaring map `S: x ↦ x◇x` is such that `S(S(S(S(x)))) = S(x)`.  Left multiplications by any squares are equal, namely `S(y)◇x` does not depend on `y` and it is equal to the right cube `C(x) = (x◇x)◇x`.  In addition, `x = B(C(x)) = C(B(x)) = B(B(B(x))) = C(C(C(x)))`.  The set of squares `Q = im(S) ⊂ M` is a submagma.

Such a magma is equivalent to

- a cubing map `C: M→M` which is bijective of order 3 (`C(C(C(x)))=x`), describing left multiplication by squares,

- a subset `Q⊂M` of squares that is stable under `C`,

- a map `S: M∖Q → Q` that describes squares of non-squares, to be completed by `S(x) = C(x)` for `x∈Q`,

- for each non-square `x ∈ M∖Q`, a bijective left-multiplication map that squares to `C ∘ C`.
