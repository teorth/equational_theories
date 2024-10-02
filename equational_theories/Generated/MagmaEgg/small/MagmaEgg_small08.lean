import equational_theories.AllEquations
import equational_theories.Magma

private def congr_op {G: Type _} [Magma G] {a b c d: G} (h1: a = b) (h2: c = d): a ∘ c = b ∘ d := by
  rw [h1, h2]
private abbrev T := @Eq.trans
private abbrev S := @Eq.symm
private abbrev R := @Eq.refl
private abbrev M := @Magma.op
private abbrev C := @congr_op

@[equational_result]
theorem Equation3804_implies_Equation4229 (G: Type _) [Magma G] (h: Equation3804 G) : Equation4229 G := fun x y z =>
  let v0 := M z z
  let v1 := M v0 y
  have h2 := R v1
  have h3 := h x y v0
  T (T (T (h x y x) (C (T (T h3 (h v1 (M x v0) v1)) (C (S h3) (T (C h2 (T (h v0 y v0) (C h2 (S (h z z z))))) (S (h v1 y v0))))) (h x x y))) (S (h (M y x) (M v1 y) (M x y)))) (S (h v1 x y))

@[equational_result]
theorem Equation4161_implies_Equation39 (G: Type _) [Magma G] (h: Equation4161 G) : Equation39 G := fun x y =>
  let v0 := M x x
  let v1 := M y x
  have h2 := R x
  have h3 := R v0
  T (T (T (T (h x x v0) (h (M v0 v0) x v1)) (C (C (C h2 (T (h v0 v0 y) (C (T (C (T (C (h x x v1) h3) (S (h v1 v0 x))) (R y)) (S (h x y v0))) h3))) (R v1)) h2)) (S (h (M (M x y) v0) x v1))) (S (h y x v0))

@[equational_result]
theorem Equation572_implies_Equation2373 (G: Type _) [Magma G] (h: Equation572 G) : Equation2373 G := fun x y z =>
  let v0 := M x z
  let v1 := M z v0
  let v2 := M y v1
  let v3 := M v2 y
  have h4 := R v3
  T (h x v2 x) (C (R v2) (T (C (T (T (h x z v3) (C (R z) (C h4 (C h4 (T (h v0 v1 v0) (C (R v1) (S (h z v0 v0)))))))) (S (h v1 z v3))) (R (M x (M x v2)))) (S (h y v1 x))))

@[equational_result]
theorem Equation1165_implies_Equation572 (G: Type _) [Magma G] (h: Equation1165 G) : Equation572 G := fun x y z =>
  let v0 := M z (M x y)
  let v1 := M y (M z v0)
  have h2 := R v0
  have h3 := R v1
  T (T (h x y v0) (C (R y) (C (T (T (T (C h2 (C (h y x z) (R x))) (S (h z v0 x))) (h z v0 v1)) (C h2 (C (T (C h3 (C (h v0 z y) (R z))) (S (h y v1 z))) h3))) h2))) (S (h v1 y v0))

@[equational_result]
theorem Equation1571_implies_Equation695 (G: Type _) [Magma G] (h: Equation1571 G) : Equation695 G := fun x y z =>
  let v0 := M z z
  let v1 := M v0 y
  let v2 := M x v1
  let v3 := M y v2
  have h4 := S (h z y v2)
  have h5 := h y z z
  T (T (h x y v1) (C (T (C h5 (C (R v0) h5)) (S (h v0 v0 (M z (M y z))))) (T (h v3 v3 (M y (M z v2))) (C h4 (C (R v3) h4))))) (S (h v3 z z))

@[equational_result]
theorem Equation2876_implies_Equation2673 (G: Type _) [Magma G] (h: Equation2876 G) : Equation2673 G := fun x y =>
  let v0 := M y y
  let v1 := M x y
  let v2 := M (M v1 v0) y
  have h3 := h v2 v0
  let v4 := M v0 v0
  have h5 := R y
  have h6 := h x v0
  T (T h6 (C (T (T (h (M (M x v4) v0) y) (C (T (T (C (S h6) h5) (h v1 y)) (C h3 h5)) h5)) (S (h (M (M v2 v4) v0) y))) (R v0))) (S h3)

@[equational_result]
theorem Equation3195_implies_Equation2180 (G: Type _) [Magma G] (h: Equation3195 G) : Equation2180 G := fun x y z =>
  let v0 := M x z
  have h1 := R v0
  have h2 := R y
  let v3 := M y z
  have h4 := R x
  let v5 := M y v0
  T (h x v0 v0) (C (T (T (T (T (C (T (C (C (T (h v0 v5 y) (C (S (h v5 y v0)) h2)) h1) h1) (S (h v0 y v0))) h4) (C (h v0 x z) h4)) (S (h z v0 x))) (h z v3 y)) (C (S (h v3 y z)) h2)) h1)

@[equational_result]
theorem Equation3810_implies_Equation3906 (G: Type _) [Magma G] (h: Equation3810 G) : Equation3906 G := fun x y z =>
  let v0 := M z z
  let v1 := M y v0
  let v2 := M x v0
  have h3 := h v0 x y
  T (T (T (T (T (h x x v0) (C h3 h3)) (S (h v1 v1 (M y x)))) (h v1 v1 v0)) (C (T (T (C (T (h z z z) (h v0 v0 x)) (h y v0 x)) (S (h (M x y) v2 v2))) (S (h v0 y x))) (R (M v0 v1)))) (S (h v1 y v0))

@[equational_result]
theorem Equation4176_implies_Equation4491 (G: Type _) [Magma G] (h: Equation4176 G) : Equation4491 G := fun x y z =>
  let v0 := M z x
  let v1 := M x v0
  let v2 := M y y
  let v3 := M y v2
  have h4 := R y
  T (T (T (T (h x v2 v3) (C (T (C (T (T (T (h v2 v3 y) (C (S (h y y v2)) h4)) (C (h y y y) h4)) (S (h y v2 y))) (R x)) (h v3 x v0)) (R v3))) (S (h v0 v1 v3))) (h v0 v1 z)) (C (S (h z x v0)) (R z))

@[equational_result]
theorem Equation4549_implies_Equation4365 (G: Type _) [Magma G] (h: Equation4549 G) : Equation4365 G := fun x y z w =>
  let v0 := M y z
  let v1 := M x v0
  let v2 := M z w
  have h3 := h x y z
  have h4 := h v0 y z
  T (T (T (T (T (T (T (T h3 (S (h v1 y z))) (C (T h3 (S h4)) (R v0))) (S (h x v0 v0))) (C (R x) (T h4 (S (h v2 y z))))) (h x v2 v0)) (C (T h4 (S h3)) (R v2))) (h v1 z w)) (S (h y z w))

@[equational_result]
theorem Equation556_implies_Equation3091 (G: Type _) [Magma G] (h: Equation556 G) : Equation3091 G := fun x y z =>
  let v0 := M x y
  let v1 := M v0 z
  let v2 := M v1 y
  let v3 := M v2 z
  have h4 := R z
  have h5 := R y
  have h6 := R v3
  T (T (h x v3 y) (C h6 (C h5 (C h6 (T (h v0 v3 z) (C h6 (T (C h4 (C h6 (T (h v1 z y) (C h4 (C h5 (T (C h4 (h v2 v3 z)) (S (h v3 z v3)))))))) (S (h y z v3))))))))) (S (h v3 v3 y))

@[equational_result]
theorem Equation684_implies_Equation1943 (G: Type _) [Magma G] (h: Equation684 G) : Equation1943 G := fun x y z =>
  let v0 := M x z
  have h1 := S (h z z v0)
  let v2 := M z (M (M z v0) v0)
  let v3 := M z (M (M z x) x)
  let v4 := M y z
  have h5 := h z z x
  T (h x z v2) (C (T (h z y z) (C (R y) (T (C (R z) (C (R v4) (T h5 (C h5 (R v3))))) (S (h v4 z v3))))) (C (R x) (T (C h1 (R v2)) h1)))

@[equational_result]
theorem Equation1699_implies_Equation2944 (G: Type _) [Magma G] (h: Equation1699 G) : Equation2944 G := fun x y z =>
  let v0 := M y x
  let v1 := M y v0
  let v2 := M (M v1 z) z
  let v3 := M (M y y) y
  let v4 := M v0 x
  T (T (h x v0 y) (C (T (T (T (T (h v4 v0 x) (C (T (S (h x y x)) (h x y y)) (R (M v4 x)))) (S (h v3 v0 x))) (h v3 v1 z)) (C (S (h v0 y y)) (R v2))) (R (M (M v0 y) y)))) (S (h v2 v0 y))

@[equational_result]
theorem Equation1726_implies_Equation3489 (G: Type _) [Magma G] (h: Equation1726 G) : Equation3489 G := fun x y z =>
  let v0 := M (M y z) z
  let v1 := M y v0
  let v2 := M x x
  have h3 := R v2
  have h4 := S (h v2 x x)
  let v5 := M (M v2 x) x
  T (T (T (h v2 x v5) (C h3 (T (C h4 (R v5)) h4))) (C h3 (T (h v2 v1 v0) (C (R (M v1 v1)) (C (S (h y x z)) (R v0)))))) (S (h v1 x v1))

@[equational_result]
theorem Equation1726_implies_Equation3692 (G: Type _) [Magma G] (h: Equation1726 G) : Equation3692 G := fun x y z =>
  let v0 := M z z
  have h1 := S (h v0 z x)
  let v2 := M (M v0 x) x
  have h3 := R (M y y)
  let v4 := M x x
  let v5 := M (M v4 x) x
  have h6 := R v5
  T (T (T (T (h v4 y v5) (C h3 (T (C (S (h v4 x x)) h6) (C (h v4 z x) h6)))) (S (h v0 y v5))) (h v0 y v2)) (C h3 (T (C h1 (R v2)) h1))

@[equational_result]
theorem Equation1967_implies_Equation562 (G: Type _) [Magma G] (h: Equation1967 G) : Equation562 G := fun x y z =>
  let v0 := M z x
  let v1 := M y v0
  let v2 := M z v1
  have h3 := R v2
  have h4 := S (h v2 v0 v1)
  have h5 := h x v1 z
  let v6 := M v1 v0
  T h5 (C (T (T (T (h v6 v6 (M v0 (M v1 v2))) (C (T (C (R v6) h4) (S h5)) h4)) (C (h x y z) h3)) (S (h y v1 z))) h3)

@[equational_result]
theorem Equation1993_implies_Equation1865 (G: Type _) [Magma G] (h: Equation1993 G) : Equation1865 G := fun x y z =>
  let v0 := M z z
  let v1 := M y y
  let v2 := M x v1
  let v3 := M v2 v0
  have h4 := h x v1 v0
  let v5 := M v0 v0
  let v6 := M v1 v5
  T (T (h x x v0) (C (R (M x v5)) (T (T (T (C (h x x y) h4) (S (h v6 v2 x))) (h v6 v2 z)) (C (R v3) (S h4))))) (S (h v3 x v0))

@[equational_result]
theorem Equation2577_implies_Equation2 (G: Type _) [Magma G] (h: Equation2577 G) : Equation2 G := fun x y =>
  have h0 := R x
  let v1 := M x (M (M y x) y)
  have h2 := S (h x x x)
  let v3 := M (M x x) x
  let v4 := M x v3
  T (T (h x y x) (C (C (R y) (T (T (T (h v3 v4 x) (C (T (C (R v4) h2) h2) h0)) (C (T (h x x y) (C (R v1) (h y x x))) h0)) (S (h (M (M x y) x) v1 x)))) h0)) (S (h y y x))

@[equational_result]
theorem Equation3131_implies_Equation572 (G: Type _) [Magma G] (h: Equation3131 G) : Equation572 G := fun x y z =>
  let v0 := M x y
  let v1 := M z v0
  let v2 := M z v1
  let v3 := M y v2
  have h4 := R v2
  have h5 := R v1
  T (T (T (h x v2 v2) (C (C (C (T (C (C (T (h z v1 z) (C (S (h v0 z z)) h5)) h5) (R x)) (S (h y x v1))) h4) h4) h4)) (C (C (C (T (h y v3 y) (C (S (h v2 y y)) (R v3))) h4) h4) h4)) (S (h v3 v2 v2))

@[equational_result]
theorem Equation4026_implies_Equation4146 (G: Type _) [Magma G] (h: Equation4026 G) : Equation4146 G := fun x y z =>
  let v0 := M x y
  let v1 := M x z
  let v2 := M v1 z
  let v3 := M v0 (M v0 y)
  have h4 := R v2
  let v5 := M v2 (M v2 z)
  T (T (T (T (h x y v0) (h v3 x v2)) (C (C h4 (T (h v2 x v5) (C (T (C (R v5) (S (h x z v2))) (S (h v1 z v2))) h4))) (R v3))) (S (h v3 v2 v2))) (S (h v2 y v0))

@[equational_result]
theorem Equation508_implies_Equation3895 (G: Type _) [Magma G] (h: Equation508 G) : Equation3895 G := fun x y z =>
  let v0 := M x x
  have h1 := S (h z z v0)
  have h2 := h v0 z x
  have h3 := R z
  have h4 := R y
  T (T h2 (C (T (h z y x) (C h4 (C h4 (T (C h3 h2) h1)))) (R (M z (M v0 v0))))) (C (R (M y (M y z))) (T (C h3 (T (T (C (R v0) (h v0 v0 x)) (S (h v0 v0 v0))) h2)) h1))

@[equational_result]
theorem Equation1724_implies_Equation4351 (G: Type _) [Magma G] (h: Equation1724 G) : Equation4351 G := fun x y z =>
  let v0 := M y y
  let v1 := M z v0
  have h2 := R v0
  let v3 := M x x
  let v4 := M x v0
  T (T (h v4 x v4) (C (R v3) (T (T (T (C (R (M v4 v4)) (C (h x y x) h2)) (S (h v0 v4 (M v3 x)))) (h v0 v1 (M v1 z))) (C (R (M v1 v1)) (C (S (h z y v0)) h2))))) (S (h v1 x v1))

@[equational_result]
theorem Equation1855_implies_Equation4597 (G: Type _) [Magma G] (h: Equation1855 G) : Equation4597 G := fun x y z =>
  let v0 := M x x
  let v1 := M v0 z
  have h2 := R (M z z)
  have h3 := R v0
  let v4 := M v0 y
  T (T (T (h v4 v4 z) (C (T (C (C h3 (h y x x)) (R (M v4 v4))) (S (h v0 (M y (M x y)) v4))) h2)) (C (T (h v0 (M z v1) v1) (C (C h3 (S (h z v0 x))) (R (M v1 v1)))) h2)) (S (h v1 v1 z))

@[equational_result]
theorem Equation2167_implies_Equation4458 (G: Type _) [Magma G] (h: Equation2167 G) : Equation4458 G := fun x y z =>
  have h0 := h z z y
  have h1 := S h0
  have h2 := R y
  have h3 := C (C h1 h2) h1
  let v4 := M z y
  let v5 := M v4 z
  have h6 := h y v5 v4
  T (T (T (C (T (h x v4 z) (C (R (M v5 x)) (T (C (C h0 h2) h0) (S h6)))) (C (T h6 h3) (R x))) (S (h y v5 x))) h6) h3

@[equational_result]
theorem Equation2958_implies_Equation2925 (G: Type _) [Magma G] (h: Equation2958 G) : Equation2925 G := fun x y z =>
  let v0 := M x z
  have h1 := R v0
  have h2 := S (h y x y)
  let v3 := M (M x (M x y)) y
  let v4 := M (M x (M x x)) x
  have h5 := h x x x
  T (h x x z) (C (T (T (T (C (C (T h5 (C (R v4) h5)) h1) (R x)) (S (h v0 v4 x))) (h v0 v3 y)) (C (C (T (C (R v3) h2) h2) h1) (R y))) (R z))

@[equational_result]
theorem Equation2958_implies_Equation4640 (G: Type _) [Magma G] (h: Equation2958 G) : Equation4640 G := fun x y z =>
  let v0 := M (M x (M x y)) y
  let v1 := M y z
  have h2 := R y
  have h3 := h y x y
  let v4 := M (M x (M x x)) x
  have h5 := h x x x
  T (T (T (C (C (T h5 (C (R v4) h5)) h2) (R x)) (S (h y v4 x))) (h y y z)) (C (T (C (C (T h3 (C (R v0) h3)) (R v1)) h2) (S (h v1 v0 y))) (R z))

@[equational_result]
theorem Equation3398_implies_Equation4673 (G: Type _) [Magma G] (h: Equation3398 G) : Equation4673 G := fun x y z =>
  let v0 := M x y
  let v1 := M x z
  let v2 := M v0 z
  have h3 := R v0
  let v4 := M z v2
  T (T (T (T (h v0 z z) (h z v4 v0)) (C h3 (T (C (R v4) (h z v0 v2)) (S (h v0 v2 v4))))) (C h3 (T (T (h v0 v2 x) (C (R x) (T (C (R v2) (h v0 x z)) (S (h x z v2))))) (h x v1 y)))) (S (h v1 y v0))

@[equational_result]
theorem Equation3755_implies_Equation329 (G: Type _) [Magma G] (h: Equation3755 G) : Equation329 G := fun x y z =>
  let v0 := M z y
  let v1 := M x v0
  let v2 := M y x
  have h3 := S (h y x y)
  have h4 := h x y z
  T (T (T (T (T (T h4 (h v2 v0 x)) (R (M (M v0 v2) v1))) (C (T (T (h v0 v2 (M x y)) (C (S h4) h3)) h3) (R v1))) (h v2 v1 (M v0 v0))) (C (S (h v0 x y)) (S (h v0 v0 x)))) (S (h x v0 v0))

@[equational_result]
theorem Equation3791_implies_Equation3729 (G: Type _) [Magma G] (h: Equation3791 G) : Equation3729 G := fun x y z =>
  let v0 := M z z
  let v1 := M y x
  T (T (h x y y) (h v1 (M y y) v0)) (C (T (C (T (T (T (h z z x) (h (M x z) (M z x) v0)) (C (S (h z x z)) (S (h x z z)))) (S (h x x z))) (R v1)) (S (h x y x))) (T (C (T (T (T (h y y z) (C (h z y z) (h y z z))) (S (h (M y z) (M z y) v0))) (S (h z z y))) (R v0)) (S (h z z z))))

@[equational_result]
theorem Equation4162_implies_Equation3994 (G: Type _) [Magma G] (h: Equation4162 G) : Equation3994 G := fun x y z =>
  let v0 := M x y
  let v1 := M z v0
  let v2 := M v1 z
  have h3 := R v2
  have h4 := R z
  have h5 := h x y v2
  let v6 := M (M y x) v2
  T (T (T h5 (h v6 v2 v2)) (C (C (T (T (T (h v2 v6 z) (C (C (S h5) h4) h4)) (C (h v0 z z) h4)) (S (h z v1 z))) h3) h3)) (S (h v1 z v2))

@[equational_result]
theorem Equation4182_implies_Equation3567 (G: Type _) [Magma G] (h: Equation4182 G) : Equation3567 G := fun x y z =>
  let v0 := M z x
  let v1 := M v0 z
  let v2 := M (M x x) x
  let v3 := M (M y v1) v1
  T (T (T (T (T (T (T (T (h x y v1) (h v3 x x)) (C (C (h x x x) (R x)) (R v3))) (S (h v3 v2 x))) (S (h v2 y v1))) (S (h y x x))) (h y x z)) (C (T (T (C (h x z x) (R z)) (S (h z v0 x))) (h z v0 z)) (R y))) (S (h y v1 z))

@[equational_result]
theorem Equation572_implies_Equation16 (G: Type _) [Magma G] (h: Equation572 G) : Equation16 G := fun x y =>
  let v0 := M y x
  let v1 := M y v0
  have h2 := S (h y v1 x)
  have h3 := R v1
  have h4 := C h3 (C (R x) (h y x y))
  have h5 := R y
  have h6 := h x y v1
  T (T h6 (C h5 (T (T (C h3 (T (T h4 h2) (h y v0 v0))) (S (h v0 v1 v0))) (C h5 (T h6 (C h5 (C h3 (T h4 h2)))))))) (S (h v1 y y))

@[equational_result]
theorem Equation928_implies_Equation1774 (G: Type _) [Magma G] (h: Equation928 G) : Equation1774 G := fun x y z =>
  let v0 := M y x
  let v1 := M (M y z) (M v0 z)
  have h2 := S (h v1 v0 x)
  let v3 := M v0 x
  have h4 := h x v0 x
  T (T (h x y x) (C (R y) (T (T (T (C (R v0) (C h4 h4)) (S (h v0 v0 (M v3 (M x x))))) (h v0 v0 (M v3 (M v1 x)))) (C (h v0 y z) (C h2 h2))))) (S (h v1 y v1))

@[equational_result]
theorem Equation1561_implies_Equation1793 (G: Type _) [Magma G] (h: Equation1561 G) : Equation1793 G := fun x y z =>
  let v0 := M z y
  let v1 := M v0 x
  let v2 := M y z
  let v3 := M v2 v1
  let v4 := M x v0
  have h5 := R v2
  T (T (h x y z) (C h5 (T (h v4 y z) (C h5 (T (C (R v4) (T (h v0 v2 v1) (C (R v3) (S (h v1 z y))))) (S (h v3 x v0))))))) (C h5 (T (C (h v2 x v0) (h v3 v0 x)) (S (h v1 v4 v3))))

@[equational_result]
theorem Equation3120_implies_Equation4458 (G: Type _) [Magma G] (h: Equation3120 G) : Equation4458 G := fun x y z =>
  let v0 := M y x
  let v1 := M (M z y) z
  have h2 := R v0
  have h3 := h y z v1
  have h4 := R y
  have h5 := R x
  T (C (T (T (h x v0 v0) (C (T (C (C (T (T (T (C (C h3 h5) h5) (S (h v1 v1 x))) (h v1 v1 y)) (C (C (S h3) h4) h4)) h2) h2) (S (h y y v0))) h2)) (C h3 h2)) h2) (S (h v1 v1 v0))

@[equational_result]
theorem Equation3145_implies_Equation246 (G: Type _) [Magma G] (h: Equation3145 G) : Equation246 G := fun x y z =>
  let v0 := M z z
  have h1 := R v0
  have h2 := R y
  have h3 := S (h v0 v0 v0)
  have h4 := C (h v0 z v0) h1
  have h5 := C (T h4 h3) h1
  have h6 := h v0 v0 y
  T (h x v0 v0) (C (T (T (S (h v0 z x)) h6) (C (T (C (T (T (T (T h5 h4) h3) h6) (C (C (T (T h5 h4) h3) h2) h1)) h2) (S (h y z v0))) h1)) (R x))

@[equational_result]
theorem Equation3791_implies_Equation4544 (G: Type _) [Magma G] (h: Equation3791 G) : Equation4544 G := fun x y z =>
  let v0 := M y z
  let v1 := M z y
  have h2 := h v1 x v0
  let v3 := M v1 x
  let v4 := M x v0
  let v5 := M v0 v1
  have h6 := h x v0 v1
  have h7 := h z z y
  T (T (T (T (T (T h6 (C (R v3) (S h7))) (C h2 (T (h z z z) (C h7 h7)))) (S (h v4 v5 v5))) (C h6 (h v0 v1 x))) (S (h v5 v4 v3))) (S h2)

@[equational_result]
theorem Equation3804_implies_Equation4491 (G: Type _) [Magma G] (h: Equation3804 G) : Equation4491 G := fun x y z =>
  let v0 := M y y
  let v1 := M z x
  let v2 := M x v0
  let v3 := M v1 v0
  T (T (T (h x v0 z) (C (T (T (T (T (h z v0 x) (h v2 v1 (M x x))) (C (S (h z x x)) (S (h x v0 x)))) (h v1 v2 v0)) (C (T (C (h y y y) (R v2)) (S (h x v0 v0))) (R v3))) (h x z v0))) (S (h (M v0 z) v3 v2))) (S (h v1 z v0))

@[equational_result]
theorem Equation4161_implies_Equation4367 (G: Type _) [Magma G] (h: Equation4161 G) : Equation4367 G := fun x y z w =>
  let v0 := M w z
  let v1 := M y v0
  let v2 := M z w
  let v3 := M z y
  let v4 := M y z
  T (T (T (h x v4 y) (C (T (S (h z y x)) (h z y y)) (R v4))) (S (h y v4 y))) (C (R y) (T (T (h y z v1) (C (T (T (h v3 v1 y) (C (T (S (h v0 y v3)) (h v0 y v2)) (R v1))) (S (h v2 v1 y))) (R z))) (S (h w z v1))))

@[equational_result]
theorem Equation844_implies_Equation11 (G: Type _) [Magma G] (h: Equation844 G) : Equation11 G := fun x y =>
  let v0 := M y y
  have h1 := h v0 y x
  have h2 := R v0
  let v3 := M v0 x
  have h4 := h v0 y v3
  let v5 := M x x
  have h6 := R v5
  T (h x v0 x) (C (R x) (T (C (T (C h2 h1) (S h4)) (T (T (h v5 y v3) (C h6 (S (h v0 x x)))) (C h6 (T h4 (C h2 (S h1)))))) (S (h v0 x v0))))

@[equational_result]
theorem Equation1571_implies_Equation11 (G: Type _) [Magma G] (h: Equation1571 G) : Equation11 G := fun x y =>
  let v0 := M y y
  let v1 := M x v0
  have h2 := S (h v0 x v0)
  have h3 := R v1
  let v4 := M v0 v0
  have h5 := S (h y x v0)
  T (T (h x v0 v0) (C (R v4) (T (T (T (C (R v0) (T (h v1 v1 (M x (M y v0))) (C h5 (C h3 h5)))) (S (h v1 y y))) (h v1 v1 (M x v4))) (C h2 (C h3 h2))))) (S (h v1 v0 v0))

@[equational_result]
theorem Equation1929_implies_Equation3286 (G: Type _) [Magma G] (h: Equation1929 G) : Equation3286 G := fun x y z =>
  let v0 := M z z
  let v1 := M y (M y v0)
  let v2 := M x x
  have h3 := R v2
  have h4 := R v0
  have h5 := h v0 y z
  have h6 := T h5 (C (R v1) h5)
  T (T (h v2 v0 x) (C (T (T (T (C h4 (T (C h6 h3) (S (h v0 v1 x)))) (C h6 h4)) (S (h v0 v1 z))) (h v0 y v1)) h3)) (S (h v1 v1 x))

@[equational_result]
theorem Equation1929_implies_Equation3692 (G: Type _) [Magma G] (h: Equation1929 G) : Equation3692 G := fun x y z =>
  let v0 := M z z
  let v1 := M x (M x v0)
  have h2 := R (M v0 v0)
  have h3 := R v1
  have h4 := h v0 x z
  T (T (T (T (h (M x x) v1 v0) (C (T (C h3 (S (h v0 x x))) (C h3 h4)) h2)) (S (h v0 v1 v0))) (h v0 v0 z)) (C (T (C (T h4 (C h3 (h v0 x y))) h2) (S (h (M y y) v1 v0))) (R v0))

@[equational_result]
theorem Equation3128_implies_Equation562 (G: Type _) [Magma G] (h: Equation3128 G) : Equation562 G := fun x y z =>
  let v0 := M z x
  let v1 := M y v0
  let v2 := M z v1
  let v3 := M y v2
  have h4 := R y
  T (T (T (h x v1 y) (C (C (T (C (C (T (h v1 v1 y) (C (T (T (S (h v0 y v1)) (h v0 v0 z)) (C (S (h x z v0)) (R z))) h4)) (R x)) h4) (S (h z x y))) (R v1)) h4)) (C (h v2 y v3) h4)) (S (h v3 v3 y))

@[equational_result]
theorem Equation3417_implies_Equation3588 (G: Type _) [Magma G] (h: Equation3417 G) : Equation3588 G := fun x y z =>
  let v0 := M x y
  let v1 := M v0 z
  let v2 := M z v1
  have h3 := R z
  have h4 := h x y v2
  let v5 := M v2 (M y x)
  have h6 := R v2
  T (T (T h4 (h v2 v5 v2)) (C h6 (C h6 (T (T (T (h v5 v2 z) (C h3 (C h3 (S h4)))) (C h3 (h z v0 z))) (S (h v1 z z)))))) (S (h z v1 v2))

@[equational_result]
theorem Equation3810_implies_Equation3414 (G: Type _) [Magma G] (h: Equation3810 G) : Equation3414 G := fun x y z =>
  let v0 := M x y
  let v1 := M z v0
  let v2 := M z z
  have h3 := h x y x
  have h4 := S h3
  let v5 := M x x
  T (T (T (T h3 (h v0 v5 v1)) (C (T (C (h z v0 z) (T (T (T (h x x x) (h v5 v5 v0)) (C h4 h4)) (h v0 v0 z))) (S (h v1 v2 v1))) (h v1 v0 z))) (S (h (M z v1) v2 v1))) (S (h z v1 z))

@[equational_result]
theorem Equation3996_implies_Equation41 (G: Type _) [Magma G] (h: Equation3996 G) : Equation41 G := fun x y z =>
  let v0 := M y z
  let v1 := M y v0
  let v2 := M v0 (M x v0)
  have h3 := T (T (T (R v2) (C (R v0) (T (h x v0 x) (S (h x x x))))) (h v0 (M x x) x)) (S (h v0 v1 x))
  have h4 := R z
  T (T (T (T (h x x v0) (h v2 x z)) (C (C h4 (C h3 h4)) h3)) (S (h (M v0 v1) y z))) (S (h y z v0))

@[equational_result]
theorem Equation1293_implies_Equation4182 (G: Type _) [Magma G] (h: Equation1293 G) : Equation4182 G := fun x y z =>
  let v0 := M y z
  let v1 := M (M v0 z) x
  have h2 := S (h v0 v0 x)
  let v3 := M (M (M v0 v0) x) x
  have h4 := R v3
  let v5 := M v1 x
  T (C (R x) (T (T (h y z v3) (C (R z) (T (C h2 h4) h2))) (C (T (h z v5 v3) (C (R v5) (T (C (T (C (S (h v0 z x)) h4) h2) h4) h2))) (R v0)))) (S (h v1 x v0))

@[equational_result]
theorem Equation1797_implies_Equation1816 (G: Type _) [Magma G] (h: Equation1797 G) : Equation1816 G := fun x y z w =>
  have h0 := h x z z
  have h1 := S h0
  let v2 := M z z
  let v3 := M v2 x
  have h4 := h v3 y z
  let v5 := M y z
  have h6 := R v5
  T (T (h x y z) (R (M v5 v3))) (C h6 (T (T (T h4 (C h6 h1)) (h (M v5 x) w z)) (C (R (M w z)) (T (C (R v2) (T (C h6 h0) (S h4))) h1))))

@[equational_result]
theorem Equation1977_implies_Equation1358 (G: Type _) [Magma G] (h: Equation1977 G) : Equation1358 G := fun x y z =>
  let v0 := M z x
  let v1 := M v0 z
  let v2 := M y (M v1 y)
  have h3 := h v0 y z
  let v4 := M y (M z y)
  T (T (h x y v0) (C (R (M y (M v0 y))) (T (T (T (T (h (M x v0) x v1) (C (R (M x (M v1 x))) (T (S (h v0 x z)) h3))) (S (h v4 x v1))) (h v4 y v1)) (C (R v2) (S h3))))) (S (h v2 y v0))

@[equational_result]
theorem Equation2170_implies_Equation1876 (G: Type _) [Magma G] (h: Equation2170 G) : Equation1876 G := fun x y z =>
  let v0 := M z y
  let v1 := M y z
  let v2 := M x v1
  let v3 := M v2 v0
  have h4 := R v3
  let v5 := M v1 x
  T (T (h x y z) (C (T (h v5 v0 v2) (C (T (C (T (h (M v0 v2) v3 v2) (C (S (h v2 v2 v0)) (T (C (h v2 z y) h4) (S (h v1 v0 v2))))) (R v5)) (S (h v1 x v1))) h4)) (R v0))) (S (h v3 y z))

@[equational_result]
theorem Equation2944_implies_Equation1943 (G: Type _) [Magma G] (h: Equation2944 G) : Equation1943 G := fun x y z =>
  let v0 := M x z
  let v1 := M y (M y z)
  let v2 := M v1 v0
  let v3 := M v1 v2
  have h4 := R z
  have h5 := S (h x x x)
  let v6 := M (M x (M x x)) x
  T (T (T (h x v6 z) (C (C (T (C (R v6) h5) h5) h4) h4)) (C (T (h v0 v1 z) (C (C (R v3) (h z y v2)) h4)) h4)) (S (h v2 v3 z))

@[equational_result]
theorem Equation3120_implies_Equation4640 (G: Type _) [Magma G] (h: Equation3120 G) : Equation4640 G := fun x y z =>
  have h0 := R z
  have h1 := S (h y x x)
  have h2 := R x
  let v3 := M x y
  let v4 := M v3 x
  have h5 := C (C (C (T (C (h x v3 v4) (R v4)) (S (h v3 v4 v4))) h2) h2) h2
  have h6 := h v4 x x
  T (T (T (T h6 h5) h1) (h y v4 z)) (C (C (T (C (R (M v4 y)) (T (T h6 h5) h1)) (S (h y x y))) h0) h0)

@[equational_result]
theorem Equation3131_implies_Equation26 (G: Type _) [Magma G] (h: Equation3131 G) : Equation26 G := fun x y =>
  let v0 := M x y
  let v1 := M v0 y
  have h2 := R y
  have h3 := R v1
  have h4 := S (h y v1 x)
  have h5 := C (C (h y x y) (R x)) h3
  have h6 := h x y v1
  T (T h6 (C (T (T (C (T (T h5 h4) (h y v0 v0)) h3) (S (h v0 v1 v0))) (C (T h6 (C (C (T h5 h4) h3) h2)) h2)) h2)) (S (h v1 y y))

@[equational_result]
theorem Equation3567_implies_Equation3331 (G: Type _) [Magma G] (h: Equation3567 G) : Equation3331 G := fun x y z =>
  let v0 := M y z
  let v1 := M z v0
  let v2 := M x v1
  let v3 := M (M v2 x) v2
  have h4 := R y
  T (T (T (T (h x y v2) (h y v3 y)) (C (R v3) (C (T (h y y v0) (C h4 (T (T (h (M v0 y) v0 z) (C (R v0) (C (S (h z z y)) (R z)))) (S (h z v0 z))))) h4))) (S (h v1 v3 y))) (S (h x v1 v2))

@[equational_result]
theorem Equation3791_implies_Equation3601 (G: Type _) [Magma G] (h: Equation3791 G) : Equation3601 G := fun x y z =>
  let v0 := M x y
  let v1 := M y x
  let v2 := M v1 z
  have h3 := h x y x
  let v4 := M x x
  T (T (T (T (T (T h3 (C (h x x x) (h y x x))) (S (h v4 v0 v4))) (h v4 v0 z)) (C (T (T (h z v4 v1) (C (R v2) (S h3))) (h v2 v0 z)) (h v0 z v2))) (S (h (M v0 z) (M v2 v0) (M z v2)))) (S (h z v2 v0))

@[equational_result]
theorem Equation3804_implies_Equation4461 (G: Type _) [Magma G] (h: Equation3804 G) : Equation4461 G := fun x y z =>
  let v0 := M z z
  let v1 := M v0 y
  let v2 := M y x
  let v3 := M v0 v2
  T (T (T (h x v2 v0) (h v3 (M x v0) v1)) (C (S (h x y v0)) (T (T (T (T (C (R v3) (T (h v0 y v0) (C (R v1) (S (h z z z))))) (S (h v1 v2 v0))) (C (h v0 y y) (h y x y))) (S (h v2 v1 (M y y)))) (S (h v0 x y))))) (S (h v0 y x))

@[equational_result]
theorem Equation3804_implies_Equation4640 (G: Type _) [Magma G] (h: Equation3804 G) : Equation4640 G := fun x y z =>
  let v0 := M x y
  let v1 := M y z
  have h2 := h x z y
  let v3 := M y x
  T (T (T (T (h v0 x y) (h v3 (M v0 y) v1)) (C (S (h v0 z y)) (T (T (h v3 v1 v0) (C (T (T (C (h x y y) (h y z y)) (S (h v1 v0 (M y y)))) (S h2)) (S (h x x y)))) (S (h x z x))))) (C (R (M v0 z)) h2)) (S (h v1 z v0))

@[equational_result]
theorem Equation4159_implies_Equation41 (G: Type _) [Magma G] (h: Equation4159 G) : Equation41 G := fun x y z =>
  let v0 := M y z
  let v1 := M (M z y) z
  have h2 := R v1
  let v3 := M x x
  have h4 := R x
  T (T (T (h x x z) (C (T (T (T (h v3 x v1) (C (T (C (T (h x v3 x) (C (S (h x x v3)) h4)) h4) (S (h x x x))) h2)) (h v3 v1 v0)) (C (C (S (h y z v3)) h2) (R v0))) (R z))) (S (h v1 v0 z))) (S (h y z v0))

@[equational_result]
theorem Equation4407_implies_Equation4680 (G: Type _) [Magma G] (h: Equation4407 G) : Equation4680 G := fun x y z w =>
  have h0 := h z y w
  let v1 := M y z
  let v2 := M x y
  have h3 := h y x v2
  have h4 := S (h y x z)
  T (T (T (T (T (T (T (T h4 (h y x (M v2 z))) (C (R v2) (T h4 h3))) (h v2 v2 x)) (C (T (S h3) (h y x v1)) (R x))) (S (h v1 v2 x))) (C (R v1) (T (S (h z y v2)) h0))) (S (h z y (M v1 w)))) h0

@[equational_result]
theorem Equation4545_implies_Equation4365 (G: Type _) [Magma G] (h: Equation4545 G) : Equation4365 G := fun x y z w =>
  have h0 := S (h y z w)
  let v1 := M z w
  let v2 := M y z
  have h3 := h v2 y z
  have h4 := h x y z
  T (T (T (T (T (T (T (T h4 (S (h (M x v2) y z))) (C (T h4 (S h3)) (R v2))) (S (h x v2 v2))) (C (R x) (T h3 (S (h v1 y z))))) (h x v1 v2)) (C (T (h v2 z w) h0) (R v1))) (h (M y v1) z w)) h0

@[equational_result]
theorem Equation556_implies_Equation775 (G: Type _) [Magma G] (h: Equation556 G) : Equation775 G := fun x y z =>
  let v0 := M z x
  let v1 := M z (M v0 y)
  let v2 := M y v1
  have h3 := R v0
  have h4 := R v2
  have h5 := R v1
  T (T (h x v1 z) (C h5 (C (R z) (C h5 (T (T (T (C (R x) (h z v0 x)) (S (h v0 x v0))) (h v0 v2 v0)) (C h4 (T (C h3 (C h4 (C h3 (h v0 z y)))) (S (h z v0 v2))))))))) (S (h v2 v1 z))

@[equational_result]
theorem Equation711_implies_Equation1699 (G: Type _) [Magma G] (h: Equation711 G) : Equation1699 G := fun x y z =>
  let v0 := M (M y z) z
  let v1 := M y x
  let v2 := M v1 v0
  let v3 := M v2 v0
  have h4 := R y
  have h5 := S (h x x x)
  let v6 := M x (M (M x x) x)
  T (T (T (h x y v6) (C h4 (C h4 (T (C h5 (R v6)) h5)))) (C h4 (T (h v1 y v0) (C h4 (C (h y v2 z) (R v3)))))) (S (h v2 y v3))

@[equational_result]
theorem Equation1710_implies_Equation2146 (G: Type _) [Magma G] (h: Equation1710 G) : Equation2146 G := fun x y z =>
  let v0 := M y y
  let v1 := M x z
  let v2 := M v0 z
  let v3 := M v2 v1
  let v4 := M v0 v3
  T (T (h x v0 z) (C (T (T (h (M v0 x) v1 x) (C (T (T (S (h z x y)) (h z v3 y)) (C (T (C (R v3) (h z z y)) (S (h v1 v2 z))) (R v4))) (R (M (M x x) v1)))) (S (h v4 v1 x))) (R (M (M z z) v0)))) (S (h v3 v0 z))

@[equational_result]
theorem Equation2196_implies_Equation4162 (G: Type _) [Magma G] (h: Equation2196 G) : Equation4162 G := fun x y z =>
  let v0 := M y x
  let v1 := M v0 z
  let v2 := M v1 z
  have h3 := h y x z
  let v4 := M (M x z) z
  let v5 := M x y
  T (T (h v5 y v1) (C (R (M (M y v1) v1)) (T (T (T (T (h (M v5 y) v0 x) (C (R (M (M v0 x) x)) (T (S (h y x y)) h3))) (S (h v4 v0 x))) (h v4 v0 z)) (C (R v2) (S h3))))) (S (h v2 y v1))

@[equational_result]
theorem Equation2515_implies_Equation2 (G: Type _) [Magma G] (h: Equation2515 G) : Equation2 G := fun x y =>
  have h0 := S (h y y y)
  have h1 := R y
  let v2 := M (M y y) y
  let v3 := M y v2
  let v4 := M (M x y) x
  let v5 := M x (M (M x x) x)
  T (T (T (h x x y) (C (T (C (T (h x x x) (C (R v5) (h x y y))) (R v4)) (S (h y v5 v4))) h1)) (C (T (h y v3 v2) (C (T (C (R v3) h0) h0) (R v2))) h1)) h0

@[equational_result]
theorem Equation3195_implies_Equation2373 (G: Type _) [Magma G] (h: Equation3195 G) : Equation2373 G := fun x y z =>
  have h0 := R y
  let v1 := M x z
  let v2 := M z v1
  let v3 := M y v2
  have h4 := R v1
  let v5 := M y v3
  T (T (T (h x v3 v1) (C (T (C (T (T (C (C (T (h v3 v5 y) (C (S (h v5 y v3)) h0)) h4) (R v3)) (S (h v1 y v3))) (h v1 x z)) (R x)) (S (h z v1 x))) h4)) (h v2 v3 y)) (C (S (h v3 y v2)) h0)

@[equational_result]
theorem Equation3370_implies_Equation4013 (G: Type _) [Magma G] (h: Equation3370 G) : Equation4013 G := fun x y z =>
  let v0 := M y z
  have h1 := R x
  let v2 := M y (M y y)
  let v3 := M v0 (M v0 x)
  T (T (T (T (T (T (T (T (h x y v0) (h y v3 y)) (h v3 v2 x)) (C (R v2) (C h1 (S (h x x v0))))) (S (h x v2 x))) (S (h y x y))) (h y x z)) (C h1 (T (T (C (R z) (h z y y)) (S (h v0 z y))) (h v0 z z)))) (S (h (M z v0) x z))

@[equational_result]
theorem Equation3370_implies_Equation4182 (G: Type _) [Magma G] (h: Equation3370 G) : Equation4182 G := fun x y z =>
  let v0 := M y z
  let v1 := M v0 z
  have h2 := R y
  let v3 := M y (M y y)
  let v4 := M v1 (M v1 x)
  T (T (T (T (T (T (h x y v1) (h y v4 y)) (C (R v4) (C h2 (h y y y)))) (S (h v3 v4 y))) (S (h x v3 v1))) (C (R x) (C h2 (T (h y y z) (C h2 (T (C (R z) (h z y y)) (S (h v0 z y)))))))) (S (h v1 x y))

@[equational_result]
theorem Equation3398_implies_Equation3737 (G: Type _) [Magma G] (h: Equation3398 G) : Equation3737 G := fun x y z =>
  let v0 := M x y
  let v1 := M y z
  let v2 := M x z
  have h3 := R v1
  have h4 := R v0
  let v5 := M y (M x v1)
  have h6 := h x y v1
  T (T (T (T h6 (h v1 v5 v0)) (C h4 (T (C (R v5) (C h3 h6)) (S (h v1 v1 v5))))) (C h4 (C h3 (T (h y z v2) (C (R v2) (S (h x y z))))))) (S (h v2 v1 v0))

@[equational_result]
theorem Equation3404_implies_Equation3903 (G: Type _) [Magma G] (h: Equation3404 G) : Equation3903 G := fun x y z =>
  let v0 := M z y
  let v1 := M y v0
  have h2 := R v0
  have h3 := R z
  let v4 := M v1 z
  T (T (T (T (T (h x x z) (C h3 (T (T (T (C (R x) (h z x v1)) (S (h v4 v1 x))) (h v4 v1 z)) (C h3 (S (h z z v1)))))) (S (h z z z))) (h z z v0)) (C h2 (C h3 (T (h v0 z v0) (C h2 (S (h y v0 z))))))) (S (h v1 z v0))

@[equational_result]
theorem Equation3563_implies_Equation41 (G: Type _) [Magma G] (h: Equation3563 G) : Equation41 G := fun x y z =>
  let v0 := M y z
  let v1 := M z v0
  let v2 := M v1 v0
  have h3 := R z
  have h4 := h z v0 x
  have h5 := T h4 (S (h v1 v0 x))
  T (T (T (T (T (T (h x x v0) (C (R x) (T (h (M x v0) v0 x) (S h4)))) (h x v1 z)) (C h5 (C (C h5 h3) h3))) (S (h z v2 z))) (R (M z v2))) (S (h y z v0))

@[equational_result]
theorem Equation3791_implies_Equation4679 (G: Type _) [Magma G] (h: Equation3791 G) : Equation4679 G := fun x y z =>
  let v0 := M x y
  let v1 := M y z
  have h2 := h z x y
  have h3 := S h2
  T (T (T (h v0 z x) (C (h x v0 v1) (T (T (T h2 (h v1 v0 (M v1 v0))) (C (T (C h3 (R v1)) (S (h x y z))) (T (C (R v0) h3) (S (h y z x))))) (h v0 v1 x)))) (S (h (M v0 v1) (M x v0) (M v1 x)))) (S (h v1 x v0))

@[equational_result]
theorem Equation4013_implies_Equation4200 (G: Type _) [Magma G] (h: Equation4013 G) : Equation4200 G := fun x y z =>
  let v0 := M z x
  let v1 := M v0 z
  let v2 := M v1 y
  let v3 := M v2 (M y v2)
  have h4 := R x
  T (T (T (T (h x y v2) (h v3 x x)) (C (C h4 (T (h x x v0) (C (T (T (h v0 (M x v0) z) (C (C (R z) (S (h z z x))) (R v0))) (S (h v0 z z))) h4))) (R v3))) (S (h v3 v1 x))) (S (h v1 y v2))

@[equational_result]
theorem Equation4087_implies_Equation369 (G: Type _) [Magma G] (h: Equation4087 G) : Equation369 G := fun x y z =>
  have h0 := R z
  let v1 := M x x
  have h2 := R v1
  have h3 := h x v1 x
  have h4 := h x x x
  have h5 := h x x z
  have h6 := h z v1 x
  T (T (T (T (T (T h3 (C (S h4) h2)) (C h5 h2)) (S h6)) (h z z v1)) (C (C (T (T (T h6 (C (S h5) h2)) (C h4 h2)) (S h3)) h2) h0)) (C (T (C (h x x y) h2) (S (h y v1 x))) h0)

@[equational_result]
theorem Equation1590_implies_Equation4200 (G: Type _) [Magma G] (h: Equation1590 G) : Equation4200 G := fun x y z =>
  let v0 := M z x
  let v1 := M v0 z
  let v2 := M v1 y
  let v3 := M v0 v2
  have h4 := h v3 z x
  T (T (h (M x y) v0 v2) (C (R v3) (C (R v2) (T (C (R v0) (C (R x) (T (T (h y v1 v0) (C (T (C (R v1) (C (R z) (h x z x))) (S (h (M x v0) v0 z))) h4)) (S (h (M z v3) x v0))))) (S h4))))) (S (h v2 v0 v2))

@[equational_result]
theorem Equation1707_implies_Equation2992 (G: Type _) [Magma G] (h: Equation1707 G) : Equation2992 G := fun x y z =>
  let v0 := M z y
  let v1 := M y v0
  let v2 := M v1 x
  have h3 := h x v1 v1
  let v4 := M (M v1 v1) v1
  T h3 (C (R v2) (T (T (h v4 v0 x) (C (T (C (h v0 y z) (T (T (h v4 v2 x) (C (T (S h3) (h x v1 x)) (R (M (M x v2) x)))) (S (h (M (M x v1) x) v2 x)))) (S (h (M v0 z) v1 x))) (R (M (M x v0) x)))) (S (h z v0 x))))

@[equational_result]
theorem Equation2399_implies_Equation4421 (G: Type _) [Magma G] (h: Equation2399 G) : Equation4421 G := fun x y z =>
  have h0 := R z
  have h1 := S (h y y x)
  let v2 := M x (M x y)
  let v3 := M y v2
  have h4 := R x
  have h5 := S (h v2 v2 x)
  let v6 := M v2 (M x (M x v2))
  T (T (T (T (h v2 x v6) (C (C h4 (T (C (R v6) h5) h5)) h4)) (S (h y x x))) (h y z v3)) (C (C h0 (T (C (R v3) h1) h1)) h0)

@[equational_result]
theorem Equation2755_implies_Equation1537 (G: Type _) [Magma G] (h: Equation2755 G) : Equation1537 G := fun x y z =>
  let v0 := M x z
  let v1 := M y y
  let v2 := M v1 (M z v0)
  have h3 := h v0 v0 v0
  let v4 := M v0 v0
  T (T (h x v1 v0) (C (C (R (M v1 v1)) (T (T (T (C h3 (R x)) (S (h z v4 x))) (h z v4 v2)) (C (T (C (R (M v4 v4)) (S (h v0 y z))) (S h3)) (R v2)))) (R v0))) (S (h v2 v1 v0))

@[equational_result]
theorem Equation2958_implies_Equation3120 (G: Type _) [Magma G] (h: Equation2958 G) : Equation3120 G := fun x y z =>
  have h0 := R z
  have h1 := R x
  have h2 := S (h y x y)
  let v3 := M (M x (M x y)) y
  let v4 := M (M x (M x x)) x
  let v5 := M x z
  have h6 := h x x x
  T (h x x z) (C (T (T (C (C (T h6 (C (R v4) h6)) (R v5)) h1) (S (h v5 v4 x))) (C (T (h x v3 y) (C (C (T (C (R v3) h2) h2) h1) (R y))) h0)) h0)

@[equational_result]
theorem Equation3804_implies_Equation4297 (G: Type _) [Magma G] (h: Equation3804 G) : Equation4297 G := fun x y z =>
  let v0 := M z z
  have h1 := S (h y v0 v0)
  let v2 := M y v0
  have h3 := h z z z
  have h4 := C h3 (R v2)
  let v5 := M x v0
  let v6 := M x y
  T (T (T (T (h x v6 v0) (C (T (h v0 v6 v2) (C (S (h x v0 y)) (T h4 h1))) (T (h x v0 v0) (C (S h3) (R v5))))) (S (h v0 v2 v5))) h4) h1

@[equational_result]
theorem Equation4481_implies_Equation4680 (G: Type _) [Magma G] (h: Equation4481 G) : Equation4680 G := fun x y z w =>
  let v0 := M x y
  let v1 := M v0 z
  have h2 := h y x z
  have h3 := h y x v0
  have h4 := S h3
  let v5 := M y z
  have h6 := S h2
  T (T (T (T (T (T (T (T h6 (h y x v1)) (C (R v0) (T h6 h3))) (h v0 v0 x)) (C (T h4 (h y x v5)) (R x))) (S (h v5 v0 x))) (C (R v5) (T h4 h2))) (S (h z y v1))) (h z y w)

@[equational_result]
theorem Equation3193_implies_Equation28 (G: Type _) [Magma G] (h: Equation3193 G) : Equation28 G := fun x y =>
  have h0 := R x
  have h1 := S (h y y x)
  have h2 := R y
  let v3 := M y x
  have h4 := S (h v3 v3 y)
  have h5 := R v3
  have h6 := h v3 y x
  have h7 := C (C (T (C (T (T (C h6 h5) h4) h6) h5) h4) h2) h2
  have h8 := h y v3 v3
  T (h x y y) (C (C (T (C (T (T (T (C (T h8 h7) h2) h1) h8) h7) h2) h1) h0) h0)

@[equational_result]
theorem Equation3211_implies_Equation26 (G: Type _) [Magma G] (h: Equation3211 G) : Equation26 G := fun x y =>
  let v0 := M x y
  let v1 := M v0 y
  have h2 := R v0
  have h3 := R v1
  have h4 := R y
  have h5 := C (C (S (h x x y)) h4) h3
  have h6 := h y v1 x
  T (T (h x v0 y) (C (T (T (T (S (h y x y)) h6) h5) (C (T (h v0 y v1) (C (T (C (C (C (T h6 h5) h3) h3) h2) (S (h v1 v0 v1))) h4)) h3)) h2)) (S (h v1 v0 y))

@[equational_result]
theorem Equation4197_implies_Equation4143 (G: Type _) [Magma G] (h: Equation4197 G) : Equation4143 G := fun x y z =>
  have h0 := R z
  have h1 := R y
  let v2 := M x z
  let v3 := M v2 y
  let v4 := M x v3
  have h5 := R v4
  T (h x y z) (C (C (T (T (T (h z x v4) (C (S (h v3 z x)) h5)) (C (C (T (h v2 y x) (C (T (C (T (h x v2 v3) (C (S (h y x v2)) (R v3))) h1) (S (h x v3 y))) (R x))) h0) h5)) (S (h x z v4))) h1) h0)

@[equational_result]
theorem Equation4210_implies_Equation3794 (G: Type _) [Magma G] (h: Equation4210 G) : Equation3794 G := fun x y z =>
  let v0 := M x y
  let v1 := M z y
  let v2 := M z x
  have h3 := R v0
  have h4 := R v2
  let v5 := M (M v2 y) x
  have h6 := h x y v2
  T (T (T (T h6 (h v5 v2 v0)) (C (T (C (C h6 h4) (R v5)) (S (h v2 v2 v5))) h3)) (C (C (T (h z x v1) (C (S (h x y z)) (R v1))) h4) h3)) (S (h v2 v1 v0))

@[equational_result]
theorem Equation684_implies_Equation1181 (G: Type _) [Magma G] (h: Equation684 G) : Equation1181 G := fun x y z =>
  let v0 := M z x
  have h1 := S (h y y v0)
  let v2 := M y (M (M y v0) v0)
  let v3 := M z v0
  let v4 := M x (M (M x x) x)
  have h5 := h x x x
  T (T (T (h x z x) (C (R z) (T (C (R x) (C (R v0) (T h5 (C h5 (R v4))))) (S (h v0 x v4))))) (h v3 y v2)) (C (R y) (C (R v3) (T (C h1 (R v2)) h1)))

@[equational_result]
theorem Equation1507_implies_Equation572 (G: Type _) [Magma G] (h: Equation1507 G) : Equation572 G := fun x y z =>
  let v0 := M x y
  let v1 := M z v0
  let v2 := M z v1
  let v3 := M y v2
  let v4 := M y (M y v3)
  let v5 := M v3 x
  T (T (T (T (h x v3 v1) (C (T (h v5 v3 y) (C (T (h (M v3 v5) v0 z) (C (S (h y x v3)) (R v2))) (R v4))) (R (M v1 (M v1 v3))))) (S (h v4 v3 v1))) (h v4 (M v3 y) v3)) (C (S (h y v3 y)) (S (h v2 y v3)))

@[equational_result]
theorem Equation1764_implies_Equation16 (G: Type _) [Magma G] (h: Equation1764 G) : Equation16 G := fun x y =>
  let v0 := M y x
  let v1 := M v0 y
  have h2 := h y y x
  have h3 := R x
  have h4 := R y
  have h5 := h v0 v0 v1
  have h6 := R v0
  have h7 := S h2
  T (h x (M v1 x) y) (C (T (T (C (C (C (T h5 (C h7 (C h7 h6))) h4) h3) h4) (C (C (C (T (C h2 (C h2 h6)) (S h5)) h4) h3) h2)) (S (h y v1 x))) (S (h v0 x y)))

@[equational_result]
theorem Equation2331_implies_Equation1316 (G: Type _) [Magma G] (h: Equation2331 G) : Equation1316 G := fun x y =>
  let v0 := M y x
  let v1 := M v0 y
  let v2 := M y (M v1 y)
  have h3 := h v2 y
  have h4 := R y
  have h5 := h x y
  T (T h5 (C (T (T (T (h (M y (M y (M x y))) y) (C (C h4 (C h4 (S h5))) h4)) (C (C h4 (T (T (T (h v0 y) (C (C h4 (C h4 (h v1 y))) h4)) (S (h (M y v2) y))) (C h4 h3))) h4)) (S (h (M y (M y (M v2 y))) y))) h4)) (S h3)

@[equational_result]
theorem Equation2714_implies_Equation1910 (G: Type _) [Magma G] (h: Equation2714 G) : Equation1910 G := fun x y z =>
  let v0 := M x z
  let v1 := M (M y v0) (M y z)
  have h2 := R z
  have h3 := S (h v1 x v0)
  let v4 := M x v0
  have h5 := h x x v0
  T (T (T (h x x z) (C (T (C (C h5 h5) (R v0)) (S (h v0 (M (M x x) v4) v0))) h2)) (C (T (h v0 (M (M x v1) v4) v0) (C (C h3 h3) (h v0 y z))) h2)) (S (h v1 v1 z))

@[equational_result]
theorem Equation2944_implies_Equation2335 (G: Type _) [Magma G] (h: Equation2944 G) : Equation2335 G := fun x y z =>
  let v0 := M x z
  let v1 := M (M y (M y v0)) z
  let v2 := M (M x (M x v1)) v1
  have h3 := R z
  have h4 := h v1 x v1
  have h5 := S (h x x x)
  let v6 := M (M x (M x x)) x
  T (T (T (h x v6 z) (C (C (T (C (R v6) h5) h5) h3) h3)) (C (T (h v0 y z) (C (T h4 (C (R v2) h4)) h3)) h3)) (S (h v1 v2 z))

@[equational_result]
theorem Equation2958_implies_Equation2522 (G: Type _) [Magma G] (h: Equation2958 G) : Equation2522 G := fun x y z =>
  let v0 := M x z
  let v1 := M v0 z
  have h2 := S (h y x y)
  let v3 := M (M x (M x y)) y
  let v4 := M (M x (M x x)) x
  have h5 := h x x x
  T (T (T (h x x z) (C (T (C (C (T h5 (C (R v4) h5)) (R v0)) (R x)) (S (h v0 v4 x))) (R z))) (h v1 v3 y)) (C (C (T (C (R v3) h2) h2) (R v1)) (R y))

@[equational_result]
theorem Equation3120_implies_Equation16 (G: Type _) [Magma G] (h: Equation3120 G) : Equation16 G := fun x y =>
  let v0 := M y x
  let v1 := M y v0
  have h2 := R v1
  have h3 := C (T (h y v1 v1) (C (S (h v0 y v1)) h2)) (R v0)
  have h4 := S (h v1 v0 y)
  have h5 := R y
  have h6 := C h3 h5
  T (T (h x y v1) (C (C (T (T (C (T (T (h v0 y y) (C (T (C h6 h5) h4) h5)) h6) h5) h4) h3) h2) h2)) (S (h v1 v0 v1))

@[equational_result]
theorem Equation3770_implies_Equation3601 (G: Type _) [Magma G] (h: Equation3770 G) : Equation3601 G := fun x y z =>
  let v0 := M y x
  let v1 := M v0 z
  let v2 := M z z
  let v3 := M v1 z
  have h4 := h y y x
  T (T (T (T (T (T (T (h x y x) (h v0 (M x x) v0)) (C (S (h y x x)) (S h4))) (h v0 (M y y) v1)) (C (T (C (T h4 (h v0 v0 z)) (h v0 z z)) (S (h v2 v1 v1))) (h v0 v1 z))) (S (h v3 v2 v1))) (R (M v3 v2))) (S (h z v1 z))

@[equational_result]
theorem Equation4095_implies_Equation4609 (G: Type _) [Magma G] (h: Equation4095 G) : Equation4609 G := fun x y z =>
  have h0 := h y x x
  have h1 := S h0
  have h2 := h (M x x) x x
  have h3 := h x x x
  have h4 := S h3
  have h5 := T h0 h4
  let v6 := M y y
  have h7 := T h3 h1
  have h8 := S h2
  T (T (T (C (T (T h3 h8) (C (T (T h3 h8) (C h7 h7)) h7)) (R y)) (S (h y v6 y))) (h y v6 z)) (C (T (T (C (T (T (C h5 h5) h2) h4) h5) h2) h1) (R z))

@[equational_result]
theorem Equation4197_implies_Equation3994 (G: Type _) [Magma G] (h: Equation4197 G) : Equation3994 G := fun x y z =>
  let v0 := M x y
  let v1 := M z v0
  let v2 := M v1 z
  have h3 := R v2
  let v4 := M z x
  T (T (T (h x y z) (h (M v4 y) z v2)) (C (C (C h3 (T (T (T (h v4 y v2) (C (C (C h3 (T (h z x v0) (C (S (h y z x)) (R v0)))) (R y)) h3)) (S (h (M (M y z) v0) y v2))) (S (h z v0 y)))) (R z)) h3)) (S (h v1 z v2))

@[equational_result]
theorem Equation572_implies_Equation4640 (G: Type _) [Magma G] (h: Equation572 G) : Equation4640 G := fun x y z =>
  let v0 := M y z
  let v1 := M v0 z
  have h2 := T (h z v1 z) (C (R v1) (S (h v0 z z)))
  have h3 := R v0
  have h4 := R y
  let v5 := M x y
  T (T (T (T (T (C (R v5) (h x y y)) (S (h y v5 y))) (h y v0 v0)) (C h3 (C h3 (T (C h3 (C h4 (C h4 h2))) (S (h v1 v0 y)))))) (C h3 (C h3 (C h3 h2)))) (S (h v1 v0 v0))

@[equational_result]
theorem Equation1430_implies_Equation152 (G: Type _) [Magma G] (h: Equation1430 G) : Equation152 G := fun x y =>
  let v0 := M x x
  have h1 := h x v0 (M x v0)
  have h2 := h x x x
  have h3 := R x
  have h4 := R v0
  let v5 := M x y
  let v6 := M v0 v0
  T (T (T h1 (C h4 (C h3 (S h2)))) (h v6 (M y y) (M y (M v5 v5)))) (C (S (h v0 x x)) (T (C (R v6) (S (h y v5 v5))) (C (T (C h4 (C h3 h2)) (S h1)) (R y))))

@[equational_result]
theorem Equation1577_implies_Equation4677 (G: Type _) [Magma G] (h: Equation1577 G) : Equation4677 G := fun x y z =>
  let v0 := M y x
  let v1 := M v0 z
  let v2 := M x v1
  let v3 := M x y
  let v4 := M v3 z
  let v5 := M x v4
  T (T (h v4 x x) (C (R (M x x)) (T (T (h (M x v5) v0 y) (C (R (M v0 y)) (T (T (T (S (h v5 y x)) (C (h x x y) (C (R v3) (h z x v0)))) (S (h v2 v3 (M x v0)))) (h v2 y x)))) (S (h (M x v2) v0 y))))) (S (h v1 x x))

