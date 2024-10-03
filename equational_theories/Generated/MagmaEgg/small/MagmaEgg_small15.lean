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
theorem Equation895_implies_Equation2146 (G: Type _) [Magma G] (h: Equation895 G) : Equation2146 G := fun x y z =>
  let v0 := M y y
  let v1 := M (M v0 z) (M x z)
  let v2 := M v1 x
  let v3 := M y x
  have h4 := h y v1 x
  have h5 := R v1
  have h6 := h v1 v0 x
  have h7 := h x x (M v3 (M x x))
  have h8 := h y x x
  have h9 := R x
  have h10 := S h8
  T (T (T (T (T h7 (C h9 (C h10 h10))) (h (M x v0) v1 v1)) (C h5 (T (T (C (C (T (C h9 (C h8 h8)) (S h7)) h5) (R (M v1 v1))) (C (S (h v0 x z)) (C h6 h6))) (S (h v0 v0 (M v2 (M v0 x))))))) (C h5 (C h4 h4))) (S (h v1 v1 (M v3 v2)))

@[equational_result]
theorem Equation1571_implies_Equation1673 (G: Type _) [Magma G] (h: Equation1571 G) : Equation1673 G := fun x y z =>
  let v0 := M z z
  let v1 := M v0 y
  let v2 := M x y
  let v3 := M v2 v1
  have h4 := h z v2 v1
  have h5 := R v3
  let v6 := M v3 z
  have h7 := h x v3 z
  have h8 := h x v2 v1
  have h9 := h v0 x y
  let v10 := M v3 (M z v0)
  have h11 := T (C (T h8 (C h5 (S h9))) (R v10)) (S (h z v3 v0))
  T (T (T (h x x v10) (C h11 (T (T (C (R x) h11) (C h7 (T (h z v3 z) (C (R v6) (T (T (C h5 h9) (S h8)) h7))))) (S (h v6 v6 (M v3 (M x z))))))) (C h4 (C h5 h4))) (S (h v3 v3 (M v2 (M z v1))))

@[equational_result]
theorem Equation2105_implies_Equation4106 (G: Type _) [Magma G] (h: Equation2105 G) : Equation4106 G := fun x y z =>
  let v0 := M x x
  let v1 := M (M y z) y
  let v2 := M z z
  have h3 := R v2
  have h4 := R v0
  have h5 := h v0 x x
  have h6 := R x
  have h7 := h x x x
  have h8 := S h7
  have h9 := h x v0 x
  let v10 := M v1 v1
  T (T (T (T h5 (C (C (T (C h7 h4) (S h9)) h6) h4)) (C (C (T (h x v0 z) (C h8 h3)) h6) h4)) (S (h v2 x x))) (C (T (T (h z y z) (C (T (h v1 v1 x) (C (C (T (T (T (h v10 x x) (C (C (T (C h7 (R v10)) (S (h x v0 v1))) h6) h4)) (C (C (T h9 (C h8 h4)) h6) h4)) (S h5)) (R v1)) h4)) h3)) (S (h v1 v0 z))) (R z))

@[equational_result]
theorem Equation2113_implies_Equation3959 (G: Type _) [Magma G] (h: Equation2113 G) : Equation3959 G := fun x y z =>
  let v0 := M x z
  let v1 := M y v0
  let v2 := M v1 z
  have h3 := h v0 v1 z
  have h4 := S (h v0 x y)
  have h5 := S (h v2 y z)
  let v6 := M y z
  let v7 := M x y
  have h8 := S (h z v0 v7)
  let v9 := M v0 v7
  T (T (T (h v7 (M (M x v0) y) v7) (C (T (T (T (T (C h4 (R v7)) (h v9 (M (M v0 z) v7) v9)) (C (T (C (T h8 (h z x y)) (R v9)) (S (h y v0 v7))) h8)) (h v6 (M (M y v2) z) v6)) (C (T (C h5 (R v6)) (S (h v0 y z))) h5)) h4)) (C (C h3 (R v2)) h3)) (S (h v2 (M (M v1 v0) z) v2))

@[equational_result]
theorem Equation3147_implies_Equation1673 (G: Type _) [Magma G] (h: Equation3147 G) : Equation1673 G := fun x y z =>
  let v0 := M z z
  let v1 := M v0 y
  have h2 := S (h y v0 y)
  have h3 := R y
  have h4 := h v0 z y
  have h5 := T (C h4 h3) h2
  have h6 := h x v0 x
  have h7 := R x
  have h8 := h v0 z x
  have h9 := R v0
  have h10 := h v0 v0 v0
  have h11 := h v0 z v0
  T (h x x v1) (C (C (T (C (T (T (C (T (T h6 (C (T (T (S h8) h10) (C (S h11) h9)) h7)) (C (C (T (h v0 z v1) (C (T (T (C (R (M v0 v0)) h5) (C (T (T (C h11 h9) (S h10)) h4) h3)) h2) h5)) h9) h7)) h7) (S (h v0 y x))) h8) h7) (S h6)) h5) (R v1))

@[equational_result]
theorem Equation3211_implies_Equation1467 (G: Type _) [Magma G] (h: Equation3211 G) : Equation1467 G := fun x y z =>
  let v0 := M y z
  let v1 := M z v0
  let v2 := M x y
  let v3 := M v2 v1
  have h4 := R v3
  have h5 := R x
  have h6 := R v0
  have h7 := h z y z
  have h8 := h y v0 z
  have h9 := C (T (C (C (C (C h5 (T h8 (C (S h7) h6))) (R v1)) h5) h5) (S (h x x v1))) (R y)
  have h10 := h y v3 x
  T (T (h x v2 y) (C (T (T (S (h y x y)) h10) (C (T (T (T (T h9 (h v2 v3 v1)) (C (S (h v1 v2 v1)) h4)) (C (T (C h7 h6) (S h8)) h4)) (C (T h10 (C h9 h4)) h4)) h4)) (R v2))) (S (h v3 v2 v3))

@[equational_result]
theorem Equation3211_implies_Equation4450 (G: Type _) [Magma G] (h: Equation3211 G) : Equation4450 G := fun x y z =>
  let v0 := M y z
  let v1 := M v0 z
  have h2 := R v0
  have h3 := R v1
  have h4 := R z
  let v5 := M y x
  have h6 := S (h y v5 x)
  have h7 := C (h x y x) (R v5)
  have h8 := T h7 h6
  have h9 := C (T (C (C (T (h v1 v1 y) (C (C (S (h y y z)) h3) h3)) h8) h8) (S (h y y v1))) h4
  have h10 := h z v1 (M x v5)
  T (T (T (T (T h7 h6) (h y v0 z)) (C (S (h z y z)) h2)) (C (T h10 (C (T (T h9 (h v0 z v1)) (C (T (C (C (C (T h10 (C h9 h3)) h3) h3) h2) (S (h v1 v0 v1))) h4)) h3)) h2)) (S (h v1 v0 z))

@[equational_result]
theorem Equation3404_implies_Equation3804 (G: Type _) [Magma G] (h: Equation3404 G) : Equation3804 G := fun x y z =>
  let v0 := M x y
  let v1 := M x z
  let v2 := M z y
  have h3 := S (h y v1 x)
  have h4 := R z
  have h5 := R y
  let v6 := M v2 z
  have h7 := h v0 x v1
  have h8 := R v0
  T (T (h x y v0) (C h8 (T (C h5 (T h7 (C (T (h x z v0) (C h8 (T (T (C h4 (T (T h7 (C (R v1) (T h3 (h y v1 z)))) (S (h v2 z v1)))) (C h4 (T (h v2 z y) (C h5 (T (T (T (C h4 (T (C h5 (h z y v2)) (S (h v6 v2 y)))) (S (h y v6 z))) (C h5 (T (h v2 z z) (C h4 (S (h y z z)))))) (S (h z z y))))))) (S (h z y z))))) h3))) (S (h v1 (M v0 v2) y))))) (S (h v2 v1 v0))

@[equational_result]
theorem Equation3791_implies_Equation3388 (G: Type _) [Magma G] (h: Equation3791 G) : Equation3388 G := fun x y z =>
  let v0 := M z y
  let v1 := M x v0
  have h2 := h z v1 x
  let v3 := M x x
  let v4 := M x z
  let v5 := M x y
  let v6 := M y x
  let v7 := M v0 v1
  let v8 := M v1 x
  let v9 := M z v1
  T (T (T (h x y v1) (h v8 (M y v1) v5)) (C (T (T (T (T (h v5 v8 v9) (C (T (T (T (h v9 v5 v1) (C (T (T (T (C (h x v0 v1) h2) (S (h v7 v4 v8))) (C (R v7) (h x z y))) (S (h v1 v6 v0))) (R (M v5 v1)))) (S (h v6 v5 v1))) (S (h x x y))) (S (h x z v1)))) (h v3 v4 v3)) (C (S (h x x x)) (S (h z x x)))) (S (h x z x))) (S (h v1 x y)))) (S h2)

@[equational_result]
theorem Equation3791_implies_Equation4146 (G: Type _) [Magma G] (h: Equation3791 G) : Equation4146 G := fun x y z =>
  let v0 := M x z
  let v1 := M v0 z
  let v2 := M y z
  let v3 := M z v1
  let v4 := M z v0
  let v5 := M v0 v0
  let v6 := M z x
  T (T (T (T (T (T (T (T (h x y z) (h v6 v2 (M x y))) (C (S (h y z x)) (S (h z x y)))) (h v2 v6 v1)) (C (R (M v1 v2)) (T (T (T (T (T (T (C (h z x z) (h v0 z z)) (S (h v0 v4 (M z z)))) (h v0 v4 v0)) (C (R v5) (S (h v0 x z)))) (h v5 (M v0 x) v4)) (C (T (T (C (h z v0 v0) (h v0 v0 z)) (S (h v5 v4 v1))) (S (h v0 z v0))) (S (h x z v0)))) (h v1 v0 z)))) (S (h v2 v3 v1))) (C (h y z v1) (h z v1 y))) (S (h v3 v2 (M v1 y)))) (S (h v1 y z))

@[equational_result]
theorem Equation3791_implies_Equation4369 (G: Type _) [Magma G] (h: Equation3791 G) : Equation4369 G := fun x y z =>
  let v0 := M y x
  let v1 := M z v0
  let v2 := M y z
  let v3 := M z v2
  have h4 := h z v0 y
  have h5 := h v0 y z
  have h6 := S h5
  have h7 := R v2
  let v8 := M v1 v2
  let v9 := M v2 y
  T (T (T (T (T (h x v2 y) (h v0 v9 (M x v2))) (C (S (h v2 y x)) (S (h y x v2)))) (h v9 v0 v1)) (C (T (T (T (C (T h4 (C h7 h5)) (h v2 y z)) (S (h v8 v3 v2))) (C (T (h v1 v2 v8) (C (T (C h6 (R v1)) (S (h y z v0))) (T (C h7 h6) (S h4)))) (R v3))) (S (h v1 z v2))) (R (M v0 v1)))) (S (h z v0 v1))

@[equational_result]
theorem Equation1059_implies_Equation378 (G: Type _) [Magma G] (h: Equation1059 G) : Equation378 G := fun x y =>
  let v0 := M (M x (M y x)) y
  let v1 := M x y
  have h2 := h y y (M x (M v1 x))
  have h3 := R y
  have h4 := h y x v1
  have h5 := T (C h3 (C h4 h3)) (S h2)
  have h6 := h x y v1
  have h7 := R x
  have h8 := h v1 y y
  have h9 := R v1
  have h10 := h y v1 y
  T (T (C (T h6 (C h7 (C (T (C h3 (C (T h8 (C h9 (C h5 h9))) h3)) (S h10)) h7))) h3) (h v0 y y)) (C (C (T (C h7 (C (T h10 (C h3 (C (T (C h9 (C (T h2 (C h3 (C (S h4) h3))) h9)) (S h8)) h3))) h7)) (S h6)) h3) (T (C h5 (R v0)) (S (h y x y))))

@[equational_result]
theorem Equation2956_implies_Equation166 (G: Type _) [Magma G] (h: Equation2956 G) : Equation166 G := fun x y =>
  have h0 := R x
  let v1 := M x x
  let v2 := M y x
  let v3 := M v2 v1
  let v4 := M x v1
  let v5 := M v4 x
  have h6 := h x x x
  have h7 := R v1
  have h8 := S (h v2 x x)
  let v9 := M v4 v2
  have h10 := C (C (T (C (R v9) h8) h8) h7) h7
  have h11 := h v1 v9 v2
  have h12 := S (h y x x)
  let v13 := M v4 y
  T (T (h x v13 y) (C (C (T (C (R v13) h12) h12) h0) h0)) (C (R v2) (T (h x v1 x) (C (T (C (C (T (T h11 h10) (C (R v3) (T h11 h10))) (T (C (C (T h6 (C (R v5) h6)) h0) h0) (S (h x v5 x)))) h0) (S (h x v3 v1))) h0)))

@[equational_result]
theorem Equation3131_implies_Equation1699 (G: Type _) [Magma G] (h: Equation3131 G) : Equation1699 G := fun x y z =>
  let v0 := M y z
  let v1 := M v0 z
  let v2 := M y x
  let v3 := M v2 v1
  have h4 := R y
  have h5 := R v3
  have h6 := R z
  have h7 := R v1
  have h8 := R v2
  have h9 := R v0
  T (T (h x y v3) (C (C (C (T (h v2 v3 z) (C (T (C (T (T (T (C (C (T (h v3 v2 v0) (C (C (T (C (C (T (h v2 v3 v2) (C (S (h v1 v2 v2)) h5)) h5) h9) (S (h z v0 v3))) h9) h8)) h8) h6) (S (h v0 z v2))) (h v0 v1 v0)) (C (T (T (S (h z v0 v0)) (h z v1 y)) (C (C (S (h z y z)) h4) h7)) h7)) h6) (S (h y z v1))) h5)) h5) h5) h4)) (S (h v3 y v3))

@[equational_result]
theorem Equation684_implies_Equation1793 (G: Type _) [Magma G] (h: Equation684 G) : Equation1793 G := fun x y z =>
  let v0 := M z y
  let v1 := M v0 x
  have h2 := R v1
  let v3 := M y (M (M y x) x)
  have h4 := h y y x
  have h5 := R y
  let v6 := M v0 (M v1 x)
  let v7 := M y v0
  have h8 := h v0 v0 x
  have h9 := R v0
  let v10 := M x (M (M x x) x)
  have h11 := h x x x
  T (T (h x v0 x) (C h9 (T (C (R x) (C h2 (T h11 (C h11 (R v10))))) (S (h v1 x v10))))) (C (T (h v0 y v0) (C h5 (T (T (T (C h9 (C (R v7) (T h8 (C h8 (R v6))))) (S (h v7 v0 v6))) (C h5 (C (R z) (T h4 (C h4 (R v3)))))) (S (h z y v3))))) h2)

@[equational_result]
theorem Equation949_implies_Equation962 (G: Type _) [Magma G] (h: Equation949 G) : Equation962 G := fun x y z =>
  let v0 := M x z
  let v1 := M z y
  let v2 := M v1 v0
  let v3 := M y v2
  have h4 := h v3 v0 v2
  have h5 := h z v1 v2
  have h6 := h z z x
  have h7 := R v0
  have h8 := h x v0 y
  T (T h8 (C h7 (T (T (T (T (T (h (M (M y x) (M v0 y)) z v0) (C (R z) (T (C (S h8) (C h6 h7)) (S (h (M v0 (M z x)) x z))))) (S h6)) h5) (C (R v1) (T (T (h (M (M v2 z) (M v1 v2)) v3 v1) (C (R v3) (T (C (S h5) (R (M v3 v1))) (S (h v2 z y))))) (C h4 (R v2))))) (S (h (M (M v2 v3) (M v0 v2)) v1 v0))))) (S h4)

@[equational_result]
theorem Equation1507_implies_Equation26 (G: Type _) [Magma G] (h: Equation1507 G) : Equation26 G := fun x y =>
  let v0 := M x y
  let v1 := M v0 y
  have h2 := h y v0 v1
  have h3 := S h2
  let v4 := M v1 v0
  let v5 := M y (M y v1)
  let v6 := M v1 v4
  have h7 := R (M x (M x v1))
  let v8 := M y x
  T (T (T (T (h x y v1) (C (T (T (T (T (h v8 y y) (C (T (h (M y v8) v0 x) (C (S (h y x y)) (T (T (T (h (M x (M x v0)) v1 x) (C (S (h y v0 x)) h7)) (C h2 h7)) (S (h v6 v1 x))))) (R (M y (M y y))))) (S (h v6 y y))) (h v6 v1 y)) (C h3 (R v5))) (R (M v1 (M v1 y))))) (S (h v5 y v1))) (h v5 v4 v1)) (C (S (h v0 v1 y)) h3)

@[equational_result]
theorem Equation1537_implies_Equation1061 (G: Type _) [Magma G] (h: Equation1537 G) : Equation1061 G := fun x y z =>
  let v0 := M z y
  let v1 := M y v0
  let v2 := M x (M v1 z)
  let v3 := M v2 v2
  have h4 := h z v1 y
  let v5 := M v1 v1
  have h6 := S (h v5 x v1)
  have h7 := R v1
  have h8 := C h7 h4
  let v9 := M x x
  have h10 := R v9
  T (T (h x v0 x) (C (R (M v0 v0)) (T (C (R x) (T (T (T (h v9 x v1) (C h10 (T (C h7 (S (h z x y))) h8))) h6) (C h7 (T (T (h v1 v1 v3) (C (R v5) (T (C (R v3) (C h7 (T (T (h v3 x v1) (C h10 (T (C h7 (S (h z v2 y))) h8))) h6))) (S (h v1 v2 v1))))) (S h4))))) (h v2 v2 v2)))) (S (h v2 v0 v3))

@[equational_result]
theorem Equation1537_implies_Equation1523 (G: Type _) [Magma G] (h: Equation1537 G) : Equation1523 G := fun x y z =>
  let v0 := M y y
  let v1 := M z z
  let v2 := M v0 (M x v1)
  have h3 := h y y y
  have h4 := S h3
  have h5 := R v0
  have h6 := h y y v0
  let v7 := M v2 v2
  have h8 := R v7
  have h9 := R y
  T (T (h x v2 v0) (C h8 (T (T (C h5 (C (R x) (T (T (h v0 v2 y) (C h8 (C h9 (T (T (T (C h5 h3) (S h6)) (h y z v0)) (C (R v1) h4))))) (S (h v1 v2 y))))) (h v2 y v2)) (C h5 (C (R v2) (T (T (h v7 x y) (C (R (M x x)) (C h9 (T (T (T (C h8 h3) (S (h y v2 v0))) h6) (C h5 h4))))) (S (h v0 x y)))))))) (S (h v2 v2 v0))

@[equational_result]
theorem Equation2105_implies_Equation2132 (G: Type _) [Magma G] (h: Equation2105 G) : Equation2132 G := fun x y z =>
  let v0 := M z z
  let v1 := M y y
  let v2 := M (M v1 x) v0
  have h3 := R v0
  have h4 := R y
  have h5 := h y y y
  have h6 := S h5
  have h7 := h y v1 z
  let v8 := M v2 v2
  T (T (h x v0 z) (C (T (T (C (C (T (T (h v0 y v0) (C (C (T (T (T (C h5 h3) (S h7)) (h y v1 y)) (C h6 (R v1))) h4) (R (M v0 v0)))) (S (h v1 y v0))) (R x)) h3) (h v2 v2 z)) (C (C (T (T (h v8 y x) (C (C (T (T (T (C h5 (R v8)) (S (h y v1 v2))) h7) (C h6 h3)) h4) (R (M x x)))) (S (h v0 y x))) (R v2)) h3)) h3)) (S (h v2 v0 z))

@[equational_result]
theorem Equation2196_implies_Equation4216 (G: Type _) [Magma G] (h: Equation2196 G) : Equation4216 G := fun x y z =>
  let v0 := M z y
  let v1 := M v0 z
  let v2 := M v1 x
  let v3 := M v2 x
  have h4 := h v0 z v2
  let v5 := M (M z v2) v2
  let v6 := M (M y v1) v1
  let v7 := M x y
  let v8 := M (M v7 z) z
  T (T (T (T (C (h x y v7) (h y v7 z)) (S (h v8 (M y v7) v7))) (h v8 x v2)) (C (R (M (M x v2) v2)) (T (T (T (T (C (R v8) (h x y v1)) (S (h v6 v7 z))) (h v6 v0 x)) (C (R (M (M v0 x) x)) (T (T (T (C (T (h v6 v0 z) (C (R (M v1 z)) (S (h z y v1)))) h4) (S (h v5 v1 z))) (h v5 v1 x)) (C (R v3) (S h4))))) (S (h v3 v0 x))))) (S (h v2 x v2))

@[equational_result]
theorem Equation2789_implies_Equation749 (G: Type _) [Magma G] (h: Equation2789 G) : Equation749 G := fun x y z =>
  let v0 := M x z
  let v1 := M v0 y
  let v2 := M z v1
  let v3 := M y v2
  have h4 := R v3
  have h5 := S (h y x v3)
  have h6 := R x
  have h7 := h x x v0
  T (T (h x v2 z) (C (C (R (M v2 z)) (T (T (T (C (C (T (h z x x) (C (T (C (C h7 h7) (R v0)) (S (h v0 (M (M x v0) (M x x)) v0))) h6)) (R v1)) h6) (S (h y v0 x))) (h y v3 v3)) (C (T (C (R (M v3 v3)) (T (C (T (h v3 (M (M x v3) (M x y)) v3) (C (C h5 h5) h4)) (R y)) (S (h v2 y y)))) (S (h v2 y v2))) h4))) (R z))) (S (h v3 v2 z))

@[equational_result]
theorem Equation492_implies_Equation14 (G: Type _) [Magma G] (h: Equation492 G) : Equation14 G := fun x y =>
  let v0 := M x y
  let v1 := M y v0
  have h2 := h y v0 v1
  have h3 := S h2
  have h4 := h v0 v1 y
  have h5 := h y v0 y
  have h6 := R v1
  have h7 := R y
  have h8 := h v1 y v1
  have h9 := R v0
  have h10 := C h9 (T h8 (C h7 (C h6 (C h6 (T (C h6 h5) (S h4))))))
  T (T (h x y v0) (C h7 (T (T (T (C (R x) (C h9 (T (C h9 (T h2 (C h9 (T (C h7 (C h6 (C h6 (T h4 (C h6 (S h5)))))) (S h8))))) (C h9 (T (T (T h10 h3) (h y v0 x)) (C h9 (S (h x y x)))))))) (S (h v0 x v0))) (h v0 v1 v0)) (C h6 (C h9 (C h9 (T h10 h3))))))) (S (h v1 y v0))

@[equational_result]
theorem Equation1577_implies_Equation3943 (G: Type _) [Magma G] (h: Equation1577 G) : Equation3943 G := fun x y z =>
  let v0 := M z z
  let v1 := M x v0
  let v2 := M v1 y
  let v3 := M v1 v2
  let v4 := M v0 v3
  have h5 := h v1 x v0
  let v6 := M x z
  let v7 := M v0 v1
  have h8 := h z x z
  have h9 := R v1
  have h10 := h y z z
  T (T (h (M x y) v0 v1) (C (R v7) (T (T (T (T (C (R v0) (T (C h9 (C (R x) h10)) (S (h (M z (M z y)) x v0)))) (S h10)) (h y v1 v1)) (C (R (M v1 v1)) (T (h v3 v1 v0) (C (T (C h9 (T (C h8 (T h8 (C (R v6) h5))) (S (h (M x v7) v6 v1)))) (S h5)) (R (M v1 v4)))))) (S (h v4 v1 v1))))) (S (h v2 v0 v1))

@[equational_result]
theorem Equation2170_implies_Equation4007 (G: Type _) [Magma G] (h: Equation2170 G) : Equation4007 G := fun x y z =>
  let v0 := M y x
  let v1 := M z v0
  let v2 := M v1 z
  have h3 := S (h v2 x y)
  have h4 := R v0
  let v5 := M x y
  let v6 := M v2 v5
  let v7 := M v5 v5
  have h8 := h v5 x y
  T (T (T h8 (C (T (h v7 x y) (C (T (C h8 (R v7)) (S (h v0 v5 v5))) h4)) h4)) (C (T (C (T (T (T (h v0 v5 v0) (C (T (T (S (h v0 x y)) (h v0 z v1)) (C (C (T (C (h z y x) (R v1)) (S (h v5 v0 z))) h4) (R v2))) (R (M v0 v5)))) (S (h v2 v5 v0))) (h v2 v2 v5)) (T (h v0 v5 v2) (C h3 (R v6)))) (S (h (M v5 v2) v6 v2))) h4)) h3

@[equational_result]
theorem Equation4122_implies_Equation4153 (G: Type _) [Magma G] (h: Equation4122 G) : Equation4153 G := fun x y z w u =>
  let v0 := M x z
  let v1 := M (M v0 w) u
  let v2 := M x x
  let v3 := M v2 v2
  have h4 := R v1
  have h5 := T (S (h x v2 y)) (h x v2 z)
  have h6 := T (T (T (T (h v2 y v1) (h (M v3 y) v1 v1)) (C (C (C h5 h5) h4) h4)) (S (h (M v3 z) v1 v1))) (S (h v2 z v1))
  let v7 := M v2 y
  let v8 := M v7 v7
  T (T (h x y v1) (h v7 v1 u)) (C (T (h v8 v1 w) (C (T (T (T (C (C (R v8) (T (C h6 h6) (S (h x z (M v2 z))))) h4) (S (h v7 v0 v1))) (C h6 (R v0))) (S (h x z v0))) (R w))) (R u))

@[equational_result]
theorem Equation492_implies_Equation43 (G: Type _) [Magma G] (h: Equation492 G) : Equation43 G := fun x y =>
  let v0 := M y x
  let v1 := M x y
  have h2 := h x y v1
  have h3 := S h2
  have h4 := h y v1 x
  have h5 := h x y x
  have h6 := R v1
  have h7 := R x
  have h8 := h v1 x v1
  have h9 := R y
  have h10 := C h9 (T (T (T (C h6 (C h6 (C h9 (T h2 (C h9 (T (C h7 (C h6 (C h6 (T h4 (C h6 (S h5)))))) (S h8))))))) (S (h v1 v1 y))) h8) (C h7 (C h6 (C h6 (T (C h6 h5) (S h4))))))
  have h11 := R v0
  have h12 := h y v0 v1
  T (C h7 (T h12 (C h11 (T (T (T h10 h3) (h x y v0)) (C h9 (T (C h7 (C h11 (C h11 (T h12 (C h11 (T h10 h3)))))) (S (h v0 x v0)))))))) (S (h v0 x y))

@[equational_result]
theorem Equation880_implies_Equation219 (G: Type _) [Magma G] (h: Equation880 G) : Equation219 G := fun x y =>
  let v0 := M x y
  let v1 := M v0 v0
  have h2 := h y v1
  have h3 := h x y
  have h4 := R v1
  let v5 := M x x
  have h6 := R v5
  have h7 := S h3
  have h8 := C (T h2 (C h4 (C h7 h7))) h6
  let v9 := M y v5
  let v10 := M x v9
  let v11 := M v10 v10
  have h12 := S (h v9 v11)
  have h13 := h x v9
  have h14 := C (R v11) (C h13 h13)
  T h13 (C (R v9) (T (T (T (T (h v11 v5) (C h6 (T (C (R (M v11 v5)) (T h14 h12)) (C (T (T h14 h12) h8) h8)))) (S (h (M v1 v5) v5))) (C h4 (C h3 h3))) (S h2)))

@[equational_result]
theorem Equation928_implies_Equation1152 (G: Type _) [Magma G] (h: Equation928 G) : Equation1152 G := fun x y z =>
  let v0 := M x y
  let v1 := M z v0
  let v2 := M v1 z
  let v3 := M y v2
  let v4 := M y v1
  have h5 := S (h v0 v1 x)
  let v6 := M v0 x
  have h7 := h y v0 x
  have h8 := R x
  T (T (h x v2 z) (C (R v2) (C (R (M v2 z)) (T (T (T (C h8 (T (h z y v1) (C (T (h y x y) (C h8 (T (C (R v0) (C h7 h7)) (S (h v0 v0 (M v6 (M y x))))))) (C (R v4) (T (C (R z) (T (h v1 v1 (M (M v1 x) v6)) (C (R v1) (C h5 h5)))) (S (h v0 z v0))))))) (S (h v4 x v0))) (C (R y) (h v1 v3 z))) (S (h (M v3 z) y v2)))))) (S (h v3 v2 z))

@[equational_result]
theorem Equation2170_implies_Equation1293 (G: Type _) [Magma G] (h: Equation2170 G) : Equation1293 G := fun x y z =>
  let v0 := M x y
  let v1 := M v0 z
  let v2 := M v1 z
  let v3 := M y v2
  have h4 := R v3
  let v5 := M v0 v3
  let v6 := M y x
  let v7 := M v2 y
  have h8 := R x
  let v9 := M v2 v3
  T (T (h x v0 v3) (C (T (T (T (C (C (T (h v0 v6 v1) (C (S (h v1 y x)) (S (h z x y)))) h4) h8) (C (T (T (h v9 v1 z) (C (T (C (h v2 y v2) (R v9)) (S (h v7 v3 v2))) (R (M z v1)))) (S (h y v1 z))) h8)) (h v6 v2 y)) (C (T (C (T (h v7 v3 v0) (C (S (h v0 y v2)) (R v5))) (R v6)) (S (h v5 x y))) h4)) (R (M v3 v0)))) (S (h v3 v0 v3))

@[equational_result]
theorem Equation3791_implies_Equation3591 (G: Type _) [Magma G] (h: Equation3791 G) : Equation3591 G := fun x y z =>
  let v0 := M x z
  let v1 := M v0 y
  let v2 := M v1 z
  let v3 := M z z
  let v4 := M z v1
  have h5 := h v1 x z
  have h6 := R v1
  let v7 := M v1 x
  let v8 := M v0 v1
  T (T (T (T (h x y z) (h (M z x) (M y z) v1)) (C (T (C h6 (h z x z)) (S (h y v3 v0))) (T (T (T (T (S (h z v0 y)) (h z v0 v1)) (h v2 v8 v4)) (C (R (M v4 v2)) (T (T (T (C (R v8) (T (T (h z v1 x) (h v0 v7 v4)) (C (S h5) (S (h x z v1))))) (S (h v1 v7 v0))) (C h6 h5)) (S (h y v4 v0))))) (S (h v2 y v4))))) (S (h v3 v2 y))) (S (h z v1 z))

@[equational_result]
theorem Equation3804_implies_Equation3385 (G: Type _) [Magma G] (h: Equation3804 G) : Equation3385 G := fun x y z =>
  let v0 := M y z
  let v1 := M x v0
  let v2 := M z x
  let v3 := M x v1
  let v4 := M x y
  have h5 := h x y x
  have h6 := h v4 (M x x) v1
  let v7 := M v4 v1
  have h8 := R v7
  have h9 := h x v0 x
  T (T (T (T (T (T (T h5 h6) (C (S h9) h8)) (h v1 v7 v1)) (C (T (T (C h9 h8) (S h6)) (S h5)) (R (M v1 v1)))) (C (T (T (h x y z) (C (h z y x) (h x z y))) (S (h v0 v2 v4))) (T (T (T (h v1 v1 x) (h v3 (M v1 x) v1)) (C (S (h v1 v0 x)) (R (M v3 v1)))) (S (h v3 v0 v1))))) (S (h v3 v2 v0))) (S (h z v1 x))

@[equational_result]
theorem Equation4197_implies_Equation3414 (G: Type _) [Magma G] (h: Equation4197 G) : Equation3414 G := fun x y z =>
  let v0 := M x y
  let v1 := M z v0
  have h2 := R v1
  have h3 := R z
  let v4 := M z v1
  have h5 := S (h v1 z v4)
  have h6 := R v4
  let v7 := M z x
  have h8 := C (C (C h6 (T (T (T (h v7 y v4) (C (C (C h6 (T (h z x v0) (C (S (h y z x)) (R v0)))) (R y)) h6)) (S (h (M (M y z) v0) y v4))) (S (h z v0 y)))) h3) h6
  have h9 := h (M v7 y) z v4
  have h10 := h x y z
  T (T (T (T (T (T h10 h9) h8) h5) (h v1 z v1)) (C (T (C (C (C h3 (T (T (T h10 h9) h8) h5)) h2) h3) (S (h (M v1 z) v1 z))) h2)) (S (h z v1 v1))

@[equational_result]
theorem Equation627_implies_Equation3457 (G: Type _) [Magma G] (h: Equation627 G) : Equation3457 G := fun x y =>
  let v0 := M x x
  let v1 := M v0 y
  have h2 := R v1
  let v3 := M v0 x
  let v4 := M y v3
  have h5 := h v0 y v4
  have h6 := S h5
  have h7 := R v4
  have h8 := h y x x
  have h9 := R v0
  have h10 := C h9 (C h9 (T h8 (C h8 h7)))
  have h11 := S (h x x x)
  let v12 := M x v3
  have h13 := R x
  have h14 := S h8
  T (T h5 (C h9 (C h9 (T (C h14 h7) h14)))) (C (T (C h13 (T (h x v0 v1) (C h13 (C (T (h x x v12) (C h13 (C h13 (T (C h11 (R v12)) h11)))) (T (T (C (T h10 h6) h2) h10) h6))))) (S (h x x v0))) h2)

@[equational_result]
theorem Equation696_implies_Equation2 (G: Type _) [Magma G] (h: Equation696 G) : Equation2 G := fun x y =>
  let v0 := M (M y y) y
  have h1 := h v0 x y
  have h2 := h (M v0 v0) x y
  have h3 := R x
  have h4 := h x x v0
  let v5 := M x x
  let v6 := M v5 x
  have h7 := h x x v6
  have h8 := S h7
  have h9 := h (M v6 v6) x x
  have h10 := C h3 h9
  have h11 := h v6 x x
  have h12 := T (T h11 h10) h8
  have h13 := R y
  T (T (T (T (T h7 (C h3 (S h9))) (S h11)) (h v6 y y)) (C h13 (T (T (C h12 (T (T h1 (C h3 h2)) (S h4))) (h v5 y x)) (C h13 (T (T (T (T (T (T (C (R v5) h12) h11) h10) h8) h4) (C h3 (S h2))) (S h1)))))) (S (h y y y))

@[equational_result]
theorem Equation2196_implies_Equation4182 (G: Type _) [Magma G] (h: Equation2196 G) : Equation4182 G := fun x y z =>
  have h0 := h x y z
  have h1 := S h0
  let v2 := M y z
  let v3 := M x y
  let v4 := M v2 z
  let v5 := M v3 x
  let v6 := M (M x v2) v2
  have h7 := h v4 v3 z
  let v8 := M (M v3 z) z
  have h9 := R v8
  let v10 := M v3 y
  T (h v3 y z) (C (R v4) (T (T (T (T (T (h v10 v4 x) (C (R (M (M v4 x) x)) (T (T (T (C (R v10) (T h7 (C h9 h1))) (S (h v8 x y))) (h v8 x v2)) (C (R v6) (T (C h9 h0) (S h7)))))) (S (h v6 v4 x))) (h v6 v5 x)) (C (T (C (R (M v5 x)) h0) (S (h v4 v3 x))) (S (h v3 x v2)))) h1))

@[equational_result]
theorem Equation2776_implies_Equation2722 (G: Type _) [Magma G] (h: Equation2776 G) : Equation2722 G := fun x y z =>
  let v0 := M y x
  let v1 := M v0 (M z y)
  have h2 := h v1 z v1
  let v3 := M v1 z
  have h4 := h z v0 v3
  have h5 := R v3
  let v6 := M (M v0 v3) (M z v0)
  have h7 := h x v1 v1
  let v8 := M (M v1 v1) (M x v1)
  have h9 := h x x z
  T h9 (C (T (T (T (T (T (h (M (M x z) (M x x)) z x) (C (T (T (T (C (C (h z y x) h7) (S h9)) (S (h v8 v1 x))) (h v8 v1 z)) (C (C h5 (S h7)) h4)) (R x))) (S (h v6 v3 x))) (h v6 v3 v1)) (C (T (C (C h5 h2) (S h4)) (S (h (M (M z v1) v3) v1 z))) (R v1))) (S h2)) (R z))

@[equational_result]
theorem Equation3211_implies_Equation43 (G: Type _) [Magma G] (h: Equation3211 G) : Equation43 G := fun x y =>
  have h0 := R x
  let v1 := M y x
  let v2 := M x y
  have h3 := S (h y v2 v1)
  have h4 := R v2
  have h5 := R y
  have h6 := R v1
  have h7 := h x y v1
  have h8 := h y v1 x
  have h9 := h x y x
  have h10 := h v1 x v1
  have h11 := C (T (T (T (C (C (C (T h8 (C (S h9) h6)) h6) h6) h0) (S h10)) (h v1 v1 y)) (C (C (C (T (C (T h10 (C (C (C (T (C h9 h6) (S h8)) h6) h6) h0)) h5) (S h7)) h5) h6) h6)) h5
  T (h v2 x y) (C (T (C (T (T (T (C (T (h v2 x v2) (C (C (C (T (C (T h7 h11) h4) h3) h4) h4) h0)) h5) (S (h x y v2))) h7) h11) h4) h3) h0)

@[equational_result]
theorem Equation1496_implies_Equation2146 (G: Type _) [Magma G] (h: Equation1496 G) : Equation2146 G := fun x y z =>
  let v0 := M y y
  let v1 := M v0 z
  let v2 := M x z
  let v3 := M v1 v2
  let v4 := M v3 (M v1 v1)
  let v5 := M x x
  have h6 := R (M v2 v5)
  have h7 := h z x v3
  let v8 := M v3 v3
  have h9 := h (M x v8) v2 x
  let v10 := M x v5
  T (T (h x x v3) (C (T (T (h v5 x x) (C (T (T (T (h v10 v2 x) (C (S (h z x x)) h6)) (C h7 h6)) (S h9)) (R v10))) (S (h v8 x x))) (T (T h9 (C (T (T (S h7) (h z v3 v1)) (C (T (C (R v3) (h z v0 y)) (S (h v2 v1 v0))) (R v4))) h6)) (S (h v4 v2 x))))) (S (h v3 v3 v1))

@[equational_result]
theorem Equation1561_implies_Equation3601 (G: Type _) [Magma G] (h: Equation1561 G) : Equation3601 G := fun x y z =>
  let v0 := M y x
  let v1 := M v0 z
  let v2 := M z v1
  have h3 := S (h v2 v1 z)
  let v4 := M v2 v2
  have h5 := R v4
  have h6 := h z x y
  have h7 := R v1
  let v8 := M x y
  have h9 := h v8 v0 z
  have h10 := C (T h9 (C h7 (S h6))) h5
  T (T (T (h v8 x y) (C (R v8) (T (C (T (h v8 v2 v2) (C h5 (T h10 h3))) (T (T (T (h v0 v8 z) (C (R (M v8 z)) (T (T (S (h z y x)) (h z z v1)) (C (R v2) (C (R z) (T (C h7 h6) (S h9))))))) (S (h v2 v8 z))) (h v2 v2 v2))) (S (h v4 v4 v2))))) h10) h3

@[equational_result]
theorem Equation2501_implies_Equation2 (G: Type _) [Magma G] (h: Equation2501 G) : Equation2 G := fun x y =>
  have h0 := R x
  let v1 := M x (M (M y y) x)
  let v2 := M x x
  let v3 := M v2 y
  have h4 := h x v3 y
  let v5 := M v2 x
  have h6 := h x v5 x
  have h7 := S h6
  let v8 := M x v5
  let v9 := M x (M (M v8 v8) x)
  let v10 := M x (M (M v1 v1) x)
  T (T (h x v10 x) (C (T (C (R v10) (T (T (T (h v5 v9 x) (C (T (T (T (C (R v9) h7) (S (h v8 x x))) (C h0 (C (C h6 h6) h0))) (C h0 (T (T (C (C h7 h7) h0) (h v5 x x)) (C (C h4 (T h7 h4)) h0)))) h0)) (S (h (M (M v3 v3) y) x x))) (S h4))) (S (h v1 x x))) h0)) (S (h y x x))

@[equational_result]
theorem Equation2707_implies_Equation115 (G: Type _) [Magma G] (h: Equation2707 G) : Equation115 G := fun x y =>
  let v0 := M x x
  let v1 := M v0 y
  let v2 := M y x
  let v3 := M v2 v2
  have h4 := h y v3
  have h5 := R v3
  have h6 := h x y
  have h7 := R v0
  have h8 := S h6
  have h9 := C h7 (T h4 (C (C h8 h8) h5))
  let v10 := M v1 x
  let v11 := M v10 v10
  have h12 := S (h v1 v11)
  have h13 := h x v1
  have h14 := C (C h13 h13) (R v11)
  T h13 (C (T (T (T (T (h v11 v0) (C (T (C (T h14 h12) (R (M v0 v11))) (C h9 (T (T h14 h12) h9))) h7)) (S (h (M v0 v3) v0))) (C (C h6 h6) h5)) (S h4)) (R v1))

@[equational_result]
theorem Equation2755_implies_Equation3161 (G: Type _) [Magma G] (h: Equation2755 G) : Equation3161 G := fun x y z =>
  let v0 := M y y
  let v1 := M v0 z
  let v2 := M v1 x
  let v3 := M v2 z
  have h4 := R v1
  have h5 := h z (M v1 v1) v0
  have h6 := R v0
  have h7 := h v1 v1 v1
  have h8 := C h6 (T (C h7 h6) (S h5))
  have h9 := C (S h7) h6
  let v10 := M v3 v3
  have h11 := C h6 (T h5 h9)
  T (T (h x v3 v1) (C (C (R v10) (T (h v2 v1 v3) (C (T (C (T (T (C h4 h11) (C h11 h8)) (S (h v0 y v1))) (T (T (T (C (h v3 v3 v3) (R v2)) (S (h z v10 v2))) h5) h9)) h8) (R v3)))) h4)) (S (h v3 v3 v1))

@[equational_result]
theorem Equation3385_implies_Equation4135 (G: Type _) [Magma G] (h: Equation3385 G) : Equation4135 G := fun x y z =>
  let v0 := M x y
  let v1 := M v0 z
  have h2 := R z
  let v3 := M v1 z
  have h4 := S (h z v1 v3)
  have h5 := R v3
  let v6 := M y z
  have h7 := C h5 (C h2 (C (T (T (T (h x v6 v3) (C h5 (C (R x) (C (T (h y z v0) (C (R v0) (S (h z x y)))) h5)))) (S (h x (M v0 (M z x)) v3))) (S (h v0 z x))) h5))
  have h8 := h z (M x v6) v3
  have h9 := h x y z
  have h10 := R v1
  T (T (T (T (T (T h9 h8) h7) h4) (h z v1 v1)) (C h10 (T (C h2 (C h10 (C (T (T (T h9 h8) h7) h4) h2))) (S (h v1 (M z v1) z))))) (S (h v1 z v1))

@[equational_result]
theorem Equation3791_implies_Equation3617 (G: Type _) [Magma G] (h: Equation3791 G) : Equation3617 G := fun x y z =>
  let v0 := M z x
  let v1 := M v0 y
  let v2 := M v1 v0
  let v3 := M x y
  have h4 := h y z x
  let v5 := M v0 v0
  have h6 := R v5
  have h7 := h x y z
  have h8 := S h7
  let v9 := M y z
  T (T (T (T (T (T h7 (h v0 v9 v0)) (C h6 (T (T (C h4 (h z x y)) (S (h v0 v9 v3))) h8))) (h v5 v3 (M v0 x))) (C (T (S (h x v0 v0)) (h x v0 z)) (T (T (T (T (S (h y v0 x)) (h y v0 v0)) (h v1 v5 v9)) (C (T (h v9 v1 v0) (C h8 (R v2))) (T (C h6 h4) (S (h v0 v3 v0))))) (S (h v2 v0 v3))))) (S (h (M v0 z) v2 v0))) (S (h z v1 v0))

@[equational_result]
theorem Equation3791_implies_Equation4424 (G: Type _) [Magma G] (h: Equation3791 G) : Equation4424 G := fun x y z =>
  let v0 := M z z
  let v1 := M y z
  let v2 := M x y
  let v3 := M y x
  have h4 := R v3
  let v5 := M z x
  let v6 := M v2 z
  T (T (T (T (h x v2 z) (h v5 v6 v2)) (C (T (S (h y z x)) (h y z v0)) (T (T (C (R v6) (T (T (T (h x y x) (C (T (T (T (h x x z) (C (h z x z) (h x z z))) (S (h (M x z) v5 v0))) (S (h z z x))) h4)) (h v0 v3 v0)) (C (S (h z z z)) (T (C h4 (T (T (T (h z z y) (h v1 (M z y) v0)) (C (S (h z y z)) (S (h y z z)))) (S (h y y z)))) (S (h x y y)))))) (S (h z v0 v2))) (h z v0 y)))) (S (h (M z v0) v1 (M v0 y)))) (S (h v0 y z))

@[equational_result]
theorem Equation627_implies_Equation152 (G: Type _) [Magma G] (h: Equation627 G) : Equation152 G := fun x y =>
  let v0 := M x y
  let v1 := M x x
  let v2 := M v1 v0
  have h3 := S (h v0 x x)
  let v4 := M v1 x
  let v5 := M v0 v4
  have h6 := R v1
  have h7 := C h6 (C h6 (T (C h3 (R v5)) h3))
  have h8 := h v1 v0 v5
  let v9 := M x v4
  have h10 := h x x x
  have h11 := R x
  have h12 := S (h y x x)
  let v13 := M y v4
  T (T (h x y v13) (C h11 (C h11 (T (C h12 (R v13)) h12)))) (C (T (h x x v1) (C h11 (T (C h11 (C (T (C h11 (C h11 (T h10 (C h10 (R v9))))) (S (h x x v9))) (T (T h8 h7) (C (T h8 h7) (R v2))))) (S (h x v1 v2))))) (R v0))

@[equational_result]
theorem Equation684_implies_Equation3417 (G: Type _) [Magma G] (h: Equation684 G) : Equation3417 G := fun x y z =>
  let v0 := M y x
  let v1 := M v0 x
  let v2 := M v0 (M v1 x)
  let v3 := M z v0
  have h4 := h v0 v0 x
  let v5 := M y v1
  have h6 := h y y x
  have h7 := R y
  let v8 := M x y
  let v9 := M v8 (M (M v8 x) x)
  let v10 := M y v8
  have h11 := h v8 v8 x
  T (T (T (h v8 y v8) (C h7 (T (T (T (C (R v8) (C (R v10) (T h11 (C h11 (R v9))))) (S (h v10 v8 v9))) (C h7 (C (R x) (T h6 (C h6 (R v5)))))) (S (h x y v5))))) (h v0 z v0)) (C (R z) (T (C (R v0) (C (R v3) (T h4 (C h4 (R v2))))) (S (h v3 v0 v2))))

@[equational_result]
theorem Equation887_implies_Equation481 (G: Type _) [Magma G] (h: Equation887 G) : Equation481 G := fun x y z =>
  let v0 := M z z
  let v1 := M y v0
  let v2 := M x v1
  let v3 := M y v2
  let v4 := M v3 v3
  have h5 := R v0
  have h6 := h y v0 (M v1 v1)
  have h7 := h v1 v1 v1
  have h8 := C (T (C h5 h7) (S h6)) h5
  have h9 := C h5 (S h7)
  have h10 := C (T h6 h9) h5
  have h11 := R v1
  T (T (h x v1 v3) (C h11 (C (T (h v2 v3 v1) (C (R v3) (T (C (T (T (T (C (R v2) (h v3 v3 v3)) (S (h y v2 v4))) h6) h9) (T (T (C h10 h11) (C h8 h10)) (S (h v0 v1 z)))) h8))) (R v4)))) (S (h v3 v1 v3))

@[equational_result]
theorem Equation2196_implies_Equation522 (G: Type _) [Magma G] (h: Equation2196 G) : Equation522 G := fun x y z =>
  let v0 := M x z
  let v1 := M z v0
  let v2 := M y v1
  let v3 := M y v2
  have h4 := S (h v3 x v2)
  let v5 := M v3 x
  have h6 := R v5
  have h7 := R v2
  have h8 := h x z v0
  have h9 := h y v1 v0
  have h10 := C (T h9 (C (S h8) h7)) h7
  let v11 := M (M v2 v1) v1
  T (T (T (T (h x v2 v1) (C (R v11) (T (C h8 h7) (S h9)))) (C (T (h v11 v3 v5) (C (T (C (T (T (C h10 h6) h4) h10) h6) h4) (S (h y v2 v1)))) (R y))) (h (M (M v3 y) y) (M v2 v3) v3)) (C (S (h y v2 v3)) (S (h v2 v3 y)))

@[equational_result]
theorem Equation2948_implies_Equation2 (G: Type _) [Magma G] (h: Equation2948 G) : Equation2 G := fun x y =>
  have h0 := R y
  let v1 := M y (M y y)
  have h2 := h v1 y x
  have h3 := R x
  have h4 := h (M v1 v1) y x
  have h5 := h x v1 x
  let v6 := M x x
  let v7 := M x v6
  have h8 := h x v7 x
  have h9 := S h8
  have h10 := h (M v7 v7) x x
  have h11 := C h10 h3
  have h12 := h v7 x x
  have h13 := T (T h12 h11) h9
  T (T (T (T (T h8 (C (S h10) h3)) (S h12)) (h v7 y y)) (C (T (T (C (T (T h2 (C h4 h3)) (S h5)) h13) (h v6 x y)) (C (T (T (T (T (T (T (C h13 (R v6)) h12) h11) h9) h5) (C (S h4) h3)) (S h2)) h0)) h0)) (S (h y y y))

@[equational_result]
theorem Equation3193_implies_Equation104 (G: Type _) [Magma G] (h: Equation3193 G) : Equation104 G := fun x y =>
  have h0 := R x
  have h1 := S (h y y x)
  have h2 := R y
  let v3 := M y x
  have h4 := S (h v3 v3 y)
  have h5 := R v3
  have h6 := h v3 y x
  have h7 := C (C (T (C (T (T (C h6 h5) h4) h6) h5) h4) h2) h2
  have h8 := h y v3 v3
  let v9 := M v3 x
  let v10 := M x v9
  have h11 := R v10
  have h12 := C (S (h v10 x v9)) h11
  have h13 := h v10 v10 x
  T (h x x v9) (C (T (C (C (T (T h13 h12) (C (T h13 h12) h11)) h0) h0) (S (h x v10 v10))) (T (h x y y) (C (C (T (C (T (T (T (C (T h8 h7) h2) h1) h8) h7) h2) h1) h0) h0)))

@[equational_result]
theorem Equation4101_implies_Equation369 (G: Type _) [Magma G] (h: Equation4101 G) : Equation369 G := fun x y z =>
  let v0 := M y y
  have h1 := h y v0 x
  have h2 := R v0
  have h3 := h x y y
  let v4 := M x x
  have h5 := R v4
  have h6 := R x
  have h7 := h y v0 y
  have h8 := h y y y
  have h9 := C (S (h x x x)) h5
  have h10 := h x v4 x
  T (T (T h10 h9) (h v4 z z)) (C (T (T (C (h z y y) h5) (C (R (M (M v0 z) y)) (T (T (T (T (T h10 h9) (h v4 v0 x)) (C (T (C (T (C (T h7 (C (S h8) h2)) h6) (C (T (T (T (C h8 h2) (S h7)) h1) (C (S h3) h2)) h6)) h5) (S (h x v4 v0))) h2)) (C h3 h2)) (S h1)))) (S (h y v0 z))) (R z))

@[equational_result]
theorem Equation684_implies_Equation1504 (G: Type _) [Magma G] (h: Equation684 G) : Equation1504 G := fun x y z =>
  have h0 := S (h z z x)
  let v1 := M z (M (M z x) x)
  have h2 := R y
  let v3 := M y x
  let v4 := M v3 x
  let v5 := M v3 (M v4 x)
  have h6 := h v3 v3 x
  let v7 := M x (M (M x x) x)
  have h8 := h x x x
  have h9 := T h8 (C h8 (R v7))
  have h10 := R v3
  have h11 := R x
  T (T (h x v3 x) (C h10 (T (C h11 (C (R v4) h9)) (S (h v4 x v7))))) (C h10 (T (T (T (C h10 (T (T (h x y x) (C h2 (T (C h11 (C h10 h9)) (S (h v3 x v7))))) (C h2 (T h6 (C h6 (R v5)))))) (S (h y v3 v5))) (h y z v1)) (C (R z) (C h2 (T (C h0 (R v1)) h0)))))

@[equational_result]
theorem Equation1507_implies_Equation3567 (G: Type _) [Magma G] (h: Equation1507 G) : Equation3567 G := fun x y z =>
  let v0 := M z x
  let v1 := M v0 z
  let v2 := M y v1
  let v3 := M v2 (M v2 v2)
  let v4 := M x y
  have h5 := h v1 y v4
  let v6 := M v4 (M v4 y)
  let v7 := M v1 y
  let v8 := M v1 v0
  T (T (T (T (T (C (T (h x v8 v1) (C (T (C (R v8) (h x z v0)) (S (h v0 v1 v0))) (S (h z v0 v1)))) (R y)) (h v7 v1 x)) (C (T (T (T (T (h (M v1 v7) v2 x) (C (T (S (h v1 y v1)) h5) (R (M x (M x v2))))) (S (h v6 v2 x))) (h v6 v2 v2)) (C (S h5) (R v3))) (R (M x (M x v1))))) (S (h v3 v1 x))) (h v3 (M v2 y) v2)) (C (S (h y v2 v2)) (S (h v1 y v2)))

@[equational_result]
theorem Equation2511_implies_Equation3091 (G: Type _) [Magma G] (h: Equation2511 G) : Equation3091 G := fun x y z =>
  let v0 := M x y
  let v1 := M (M v0 z) y
  let v2 := M v1 z
  have h3 := h v2 z v0
  have h4 := R v0
  have h5 := R x
  have h6 := h z x x
  have h7 := R v1
  have h8 := h x z v0
  T (T h8 (C (T (T (h (M z (M (M x z) v0)) v0 x) (C (C h4 (T (T (T (C (S h8) h5) (h (M x x) v1 x)) (C (C h7 (T (C (T (C (C h5 (T (T (T (h x y x) (C (C (R y) (C (h v0 z y) h5)) h5)) (S (h (M z v1) y x))) (C h6 h7))) h7) (S (h (M x (M (M z x) x)) x v1))) h5) (S h6))) h5)) (C h3 h5))) h5)) (S (h (M z (M (M v2 z) v0)) v0 x))) h4)) (S h3)

@[equational_result]
theorem Equation2958_implies_Equation3131 (G: Type _) [Magma G] (h: Equation2958 G) : Equation3131 G := fun x y z =>
  let v0 := M y x
  let v1 := M v0 z
  let v2 := M v1 z
  let v3 := M v2 y
  let v4 := M (M x (M x v2)) v2
  let v5 := M v2 v3
  have h6 := h v2 x v2
  let v7 := M (M x (M x v0)) v0
  have h8 := h v0 x v0
  have h9 := S (h y v2 y)
  let v10 := M v5 y
  T (T (h x v10 y) (C (T (T (T (T (C (T (C (R v10) h9) h9) (R x)) (h v0 v0 z)) (C (T (C (C (T h8 (C (R v7) h8)) (R v1)) (R v0)) (S (h v1 v7 v0))) (R z))) (h v2 v2 v3)) (C (T (C (C (T h6 (C (R v4) h6)) (R v5)) (R v2)) (S (h v5 v4 v2))) (R v3))) (R y))) (S (h v3 v2 y))

@[equational_result]
theorem Equation4176_implies_Equation3940 (G: Type _) [Magma G] (h: Equation4176 G) : Equation3940 G := fun x y z =>
  let v0 := M z y
  let v1 := M x v0
  have h2 := R y
  let v3 := M v1 z
  have h4 := R z
  let v5 := M x y
  have h6 := R x
  let v7 := M y v0
  T (T (h x y y) (C (T (T (T (T (T (T (T (C (T (T (h y y v1) (C (T (T (T (C (h y v1 z) h2) (S (h z v3 y))) (h z v3 z)) (C (S (h z v1 z)) h4)) (R v1))) (S (h z z v1))) h6) (C (T (h z z y) (C (T (T (T (C (h z y v0) h4) (S (h v0 v7 z))) (h v0 v7 x)) (C (S (h x y v0)) h6)) h2)) h6)) (S (h y v5 x))) (h y v5 z)) (C (S (h z x y)) h4)) (C (h z x v0) h4)) (R (M (M v3 v0) z))) (S (h v0 v1 z))) h2)) (S (h v1 z y))

@[equational_result]
theorem Equation1165_implies_Equation3567 (G: Type _) [Magma G] (h: Equation1165 G) : Equation3567 G := fun x y z =>
  let v0 := M z x
  let v1 := M y (M v0 z)
  have h2 := R z
  have h3 := R v1
  have h4 := h x y x
  have h5 := R y
  let v6 := M y x
  let v7 := M (M x v6) x
  have h8 := R x
  let v9 := M x y
  have h10 := S (h x y v9)
  let v11 := M v9 v6
  T (T (T (T (T (T (T (h v9 v11 y) (C (R v11) (C h10 h5))) (h (M v11 v9) y x)) (C h5 (C (T (C h8 h10) (C h8 h4)) h8))) (S (h v7 y x))) (h v7 y z)) (C h5 (C (T (T (C h2 (S h4)) (h v0 z v1)) (C h2 (C (T (C h3 (C (h z v0 y) (R v0))) (S (h y v1 v0))) h3))) h2))) (S (h v1 y z))

@[equational_result]
theorem Equation1507_implies_Equation4458 (G: Type _) [Magma G] (h: Equation1507 G) : Equation4458 G := fun x y z =>
  let v0 := M y x
  let v1 := M x v0
  let v2 := M v1 x
  let v3 := M z y
  let v4 := M v3 z
  let v5 := M v1 v4
  let v6 := M v1 (M v1 v1)
  let v7 := M v1 v5
  have h8 := h z v3 y
  let v9 := M y (M y v3)
  T (C (T (h x v1 v1) (C (R v2) (T (T (h v6 y x) (C (T (C (T (T (h y z x) (C (T (T (T (C h8 (h y z v3)) (S (h v9 v4 v3))) (h v9 v4 v1)) (C (S h8) (R v7))) (R (M x (M x z))))) (S (h v7 z x))) (R v6)) (S (h v5 v1 v1))) (T (h (M x (M x y)) v0 x) (C (S (h x y x)) (R (M x v1)))))) (S (h v4 v1 x))))) (h v0 x v1)) (S (h v4 v2 v1))

@[equational_result]
theorem Equation3298_implies_Equation3303 (G: Type _) [Magma G] (h: Equation3298 G) : Equation3303 G := fun x y z w =>
  have h0 := h w x x
  have h1 := S h0
  let v2 := M x x
  have h3 := C (R x) (R (M x v2))
  let v4 := M w w
  have h5 := h v4 x x
  have h6 := h x x x
  have h7 := T h6 h1
  have h8 := C h7 h7
  have h9 := S h6
  have h10 := R v2
  let v11 := M z v4
  have h12 := T h0 h9
  have h13 := C h12 h12
  have h14 := S h5
  T (h x y v11) (C (R y) (T (T (T (C (R v11) (T (T (T (h v11 x x) h14) h13) (C h10 (T (T (T h6 h3) h14) h13)))) (S (h w v11 v2))) (h w z v2)) (C (R z) (T (T (T (T (C h10 (T (T (T h8 h5) h3) h9)) h8) h5) h3) h1))))

@[equational_result]
theorem Equation4176_implies_Equation4497 (G: Type _) [Magma G] (h: Equation4176 G) : Equation4497 G := fun x y z =>
  have h0 := R x
  have h1 := R z
  let v2 := M y y
  let v3 := M x v2
  have h4 := h x x v2
  let v5 := M z z
  have h6 := R v2
  T (T (T (h x v2 v3) (C (T (C (T (h v2 v3 v2) (C (S (h v2 x v2)) h6)) h0) (S (h v2 v2 x))) (R v3))) (h (M v2 v2) v3 x)) (C (T (T (T (T (T (C (R (M v3 x)) (T (T (h v2 v2 z) (C (T (T (T (C (h v2 z z) h6) (S (h z v5 v2))) (h z v5 y)) (C (S (h y z z)) (R y))) h1)) (S (h y y z)))) (S h4)) (h x x x)) (C (T (C h4 h0) (S (h v2 v3 x))) h0)) (C (T (h v2 v3 z) (C (S (h z x v2)) h1)) h0)) (S (h z z x))) h0)

@[equational_result]
theorem Equation914_implies_Equation3906 (G: Type _) [Magma G] (h: Equation914 G) : Equation3906 G := fun x y z =>
  let v0 := M z z
  let v1 := M y v0
  let v2 := M x x
  let v3 := M v1 y
  have h4 := h v3 v2 v1
  let v5 := M v1 v1
  have h6 := R v0
  have h7 := R v2
  have h8 := R x
  have h9 := h x x x
  let v10 := M v2 v2
  have h11 := S (h v10 x v2)
  have h12 := C h8 (T h9 (C h9 (R v10)))
  T (T (T h12 h11) (C h7 (T (T (T (T (T (T (T h12 h11) (h v10 x x)) (C h8 (C (S h9) h7))) (C h8 (C (h x x v1) h7))) (S (h (M v2 v5) x x))) (C h7 (T (T (C (R v1) (C (h y v1 z) h6)) (S (h (M v3 v0) v1 z))) (C h4 h6)))) (S (h (M (M v2 v3) v5) v2 z))))) (S h4)

@[equational_result]
theorem Equation1384_implies_Equation31 (G: Type _) [Magma G] (h: Equation1384 G) : Equation31 G := fun x y =>
  let v0 := M y y
  let v1 := M v0 x
  let v2 := M v1 v1
  have h3 := h x v2 y
  have h4 := h x v1 y
  have h5 := R v2
  let v6 := M v2 x
  have h7 := R x
  have h8 := h v0 v0 v0
  have h9 := C h5 (S h4)
  have h10 := h x v0 v1
  let v11 := M v6 v0
  have h12 := h x v0 v0
  T h12 (C (R v0) (T (T (T (T (T (T (T (h (M (M (M v0 v0) x) v0) x y) (C h7 (T (C (S h12) h7) (C h10 h7)))) (S (h v11 x y))) (h v11 v1 y)) (C (R v1) (T (C (S h10) (C h8 h7)) (C (T (T h3 h9) (C h5 (T h3 h9))) (C (S h8) h7))))) (S (h v6 v1 v1))) (C h5 h4)) (S h3)))

@[equational_result]
theorem Equation2779_implies_Equation2474 (G: Type _) [Magma G] (h: Equation2779 G) : Equation2474 G := fun x y z =>
  let v0 := M y y
  let v1 := M v0 z
  let v2 := M x v1
  let v3 := M v2 z
  have h4 := h v3 y v1
  have h5 := R y
  have h6 := R v0
  let v7 := M x y
  let v8 := M v0 x
  have h9 := h x y v3
  T (T (T h9 (C (T (h (M (M y v3) (M x v3)) y y) (C (C h6 (S h9)) h5)) h5)) (C (T (T (T (T (h (M v8 y) y v0) (C (C (R (M y v0)) (T (C (C (R v8) (h y x y)) h6) (S (h (M v7 v0) v0 x)))) h5)) (S (h v7 y v0))) (C (T (T (h x v3 v1) (C (S (h v0 v2 z)) (R v3))) (C h6 h4)) h5)) (S (h (M (M y v1) (M v3 v1)) y y))) h5)) (S h4)

@[equational_result]
theorem Equation2925_implies_Equation2519 (G: Type _) [Magma G] (h: Equation2925 G) : Equation2519 G := fun x y z =>
  let v0 := M x z
  let v1 := M v0 y
  let v2 := M y v1
  have h3 := R y
  have h4 := R x
  have h5 := h v1 y x
  let v6 := M (M y (M v1 x)) y
  let v7 := M v2 z
  have h8 := R v7
  let v9 := M (M v7 v1) v7
  T (h x x z) (C (T (T (h (M (M x v0) x) x y) (C (C (T (C h4 (T (C (C (C h4 (h v0 v7 y)) h4) h3) (S (h v9 x y)))) (C h4 (T (T (h v9 x x) (C (C (C h4 (T (T (T (C (C (C h8 h5) h8) h4) (S (h v6 v7 x))) (h v6 y x)) (C (C (C h3 (S h5)) h3) h4))) h4) h4)) (S (h (M v2 y) x x))))) h4) h3)) (S (h v2 x y))) (R z))

