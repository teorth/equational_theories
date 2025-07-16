## A law related to Boolean subgroups of the bijections

This law implies that left multiplications are bijective and commute.  The cubing maps `B: x ↦ (x◇x)◇x` and `C: x ↦ x◇(x◇x)` are bijections of order 3 and inverses of each other (`x = B(C(x)) = B(B(B(x)))`), and they commute with left multiplications (`B(x◇y) = x◇B(y)`).  The squaring map `S: x ↦ x◇x` is an endomorphism such that `S(S(S(S(x)))) = S(x)`.

The map `φ: (M,◇) → (Bij(M),∘)` from `M` to the group of bijections of `M` (equipped with composition), defined by setting `φ(x)` to be the bijection `y ↦ x ◇ C(y)`, is a magma morphism, namely, `x ◇ C(y ◇ C(z)) = (x ◇ y) ◇ C(z)`.  The image `G = φ(M)` consists of involutions, it is an abelian subgroup `G ⊂ Bij(M)` of exponent 2 which commutes with the `ℤ/3ℤ` subgroup `{id,B,C}`.  In particular, `φ` maps all squares to the identity, hence maps an element `x∈M` and `B(x)` and `C(x)` to the same bijection.

The submagma `φ⁻¹(id) = {x, ∀y x◇C(y)=y}` contains all squares, and on this submagma the operation `◇` is right-projection composed with `B`, namely `s◇t = B(t)` for all `s,t ∈ φ⁻¹(id)`.  The fibers `φ⁻¹(g)` for `g∈G` are in (non-canonical) bijection with each other: for any `x ∈ φ⁻¹(g)`, left multiplication by `x` is a bijection of `M` that interchanges `φ⁻¹(g)` and `φ⁻¹(id)`, and squares to `C`.

The left division operation defined by `x ◇ (x : y) = y` satisfies the same law, `x = y : (z : ((y : z) : x))`.  The operation `x ◆ y = x ◇ C(y)` satisfies the same law, with both cubing maps being equal to the identity, namely `x ◆ (x ◆ x) = x` and `(x ◆ x) ◆ x = x`.  Conversely, given an operation `◆` satisfying this law, one can twist by any `B` bijection of order 3 of each fiber to get an operation `x ◇ y = x ◆ B(y)` that satisfies the law.
