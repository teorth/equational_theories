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
theorem Equation3791_implies_Equation4162 (G: Type _) [Magma G] (h: Equation3791 G) : Equation4162 G := fun x y z =>
  let v0 := M y x
  let v1 := M v0 z
  let v2 := M x y
  have h3 := h x x y
  have h4 := h x y x
  let v5 := M x x
  T (T (T (T h4 (h v5 v0 v1)) (C (T (T (C (R v1) (T (T (h x x x) (C (T (T h3 (h v0 v2 v5)) (C (S h4) (S (h y x x)))) h3)) (S (h v0 v0 v2)))) (S (h z v0 v0))) (h z v0 v1)) (h v0 v1 z))) (S (h (M v0 v1) (M z v0) (M v1 z)))) (S (h v1 z v0))

@[equational_result]
theorem Equation3791_implies_Equation4515 (G: Type _) [Magma G] (h: Equation3791 G) : Equation4515 G := fun x y z =>
  let v0 := M x z
  let v1 := M y z
  let v2 := M z v0
  let v3 := M v0 v1
  let v4 := M v0 y
  T (T (T (h x v1 y) (h (M y x) (M v1 y) (M x v1))) (C (T (T (T (T (S (h v1 y x)) (h v1 y v0)) (h v3 (M y v0) v4)) (C (T (T (C (T (T (h v0 y z) (h v2 v1 v4)) (C (S (h y z v0)) (S (h z v0 y)))) (R v3)) (S (h v2 v0 v1))) (S (h v0 x z))) (S (h v0 v0 y)))) (S (h x v0 v0))) (S (h y x v1)))) (S (h v0 y x))

@[equational_result]
theorem Equation3940_implies_Equation3323 (G: Type _) [Magma G] (h: Equation3940 G) : Equation3323 G := fun x y z =>
  let v0 := M z z
  let v1 := M y v0
  have h2 := h x v1 z
  let v3 := M x (M z v1)
  let v4 := M y v1
  let v5 := M v3 (M v1 z)
  have h6 := R v4
  have h7 := h y v0 y
  T (T (T (T (T (T (h x y v4) (C (C (R x) (S h7)) h6)) (C (T (T h2 (h v3 z v1)) (C (R v5) h7)) h6)) (S (h v5 y v4))) (C (C (R v3) (S (h y z z))) (R y))) (S (h v3 z y))) (S h2)

@[equational_result]
theorem Equation522_implies_Equation3601 (G: Type _) [Magma G] (h: Equation522 G) : Equation3601 G := fun x y z =>
  let v0 := M y x
  let v1 := M v0 z
  let v2 := M z v1
  have h3 := R v2
  have h4 := h v0 v2 z
  have h5 := R v0
  have h6 := R x
  T (T (T (T (C h6 (T (h y x x) (C h6 (T (T (T (C h6 (C h6 h4)) (S (h v2 x v2))) (h v2 v0 v2)) (C h5 (C h5 (S h4))))))) (S (h v0 x v0))) h4) (C h3 (C h3 (C (R z) (T (h v1 v2 v2) (C h3 (S (h z v2 v1)))))))) (S (h v2 v2 z))

@[equational_result]
theorem Equation2105_implies_Equation3692 (G: Type _) [Magma G] (h: Equation2105 G) : Equation3692 G := fun x y z =>
  let v0 := M z z
  let v1 := M y y
  let v2 := M x x
  have h3 := R v2
  have h4 := R x
  have h5 := h x x x
  have h6 := S h5
  have h7 := R v1
  T (T (T (h v2 x x) (C (C (T (C h5 h3) (S (h x v2 x))) h4) h3)) (C (C (T (h x v2 v1) (C h6 (C h7 (T (T (h v1 x x) (C (T (C (T (C h5 h7) (S (h x v2 y))) h4) (C (T (h x v2 z) (C h6 (R v0))) h4)) h3)) (S (h v0 x x)))))) h4) h3)) (S (h (M v1 v0) x x))

@[equational_result]
theorem Equation2722_implies_Equation2776 (G: Type _) [Magma G] (h: Equation2722 G) : Equation2776 G := fun x y z =>
  let v0 := M y z
  let v1 := M x y
  let v2 := M v0 v1
  let v3 := M v2 z
  have h4 := R v0
  have h5 := R v2
  have h6 := h z y x
  T (T (h x v2 v0) (C (C (T (T (S h6) (h z y v3)) (C (C h4 (T (C (C h5 (T (h z v1 v0) (C (T (C (C (R v1) h6) h5) (S (h y x v2))) h4))) (R y)) (S (h v1 v0 y)))) (R v3))) (R (M v0 v2))) h4)) (S (h v3 v2 v0))

@[equational_result]
theorem Equation2789_implies_Equation1571 (G: Type _) [Magma G] (h: Equation2789 G) : Equation1571 G := fun x y z =>
  let v0 := M x z
  let v1 := M (M y z) (M y v0)
  let v2 := M x v0
  have h3 := h v1 x v0
  have h4 := S (h x x v0)
  T (T (h x v0 z) (C (C (R (M v0 z)) (T (T (T (C (T (h v0 (M v2 (M x x)) v0) (C (C h4 h4) (R v0))) (R x)) (S (h z x x))) (h z v1 v1)) (C (T (C (C h3 h3) (S (h v0 y z))) (S (h v0 (M v2 (M x v1)) v0))) (R v1)))) (R z))) (S (h v1 v0 z))

@[equational_result]
theorem Equation2958_implies_Equation4413 (G: Type _) [Magma G] (h: Equation2958 G) : Equation4413 G := fun x y z =>
  let v0 := M x (M x y)
  let v1 := M v0 y
  let v2 := M y z
  have h3 := R y
  have h4 := h y x y
  have h5 := R v1
  let v6 := M (M x (M x v0)) v0
  have h7 := h v0 x v0
  T (T (T (T (h v0 v0 y) (C (T (C (C (T h7 (C (R v6) h7)) h5) (R v0)) (S (h v1 v6 v0))) h3)) (S h4)) (h y y z)) (C (T (C (C (T h4 (C h5 h4)) (R v2)) h3) (S (h v2 v1 y))) (R z))

@[equational_result]
theorem Equation3120_implies_Equation4007 (G: Type _) [Magma G] (h: Equation3120 G) : Equation4007 G := fun x y z =>
  let v0 := M y x
  let v1 := M z v0
  let v2 := M v1 z
  have h3 := R v2
  have h4 := h v0 z v2
  have h5 := R y
  have h6 := R v0
  T (T (T (T (C (T (h x y y) (C (T (T (T (C (C h4 h5) h5) (S (h v2 v2 y))) (h v2 v2 v0)) (C (C (S h4) h6) h6)) h5)) h5) (S (h v0 v0 y))) h4) (C (C (C (T (h v1 v2 v2) (C (S (h z v1 v2)) h3)) (R z)) h3) h3)) (S (h v2 z v2))

@[equational_result]
theorem Equation3211_implies_Equation2573 (G: Type _) [Magma G] (h: Equation3211 G) : Equation2573 G := fun x y z =>
  have h0 := R z
  let v1 := M z x
  let v2 := M v1 y
  have h3 := R v2
  have h4 := h y v1 y
  have h5 := h v1 v2 y
  have h6 := T h5 (C (S h4) h3)
  let v7 := M y v2
  have h8 := R x
  T (T (h x z v1) (C (T (C (C (C (T (h z v7 x) (C (T (C (C (C (T (C h4 h3) (S h5)) h8) h8) h0) (S (h x z x))) (R v7))) h6) (R v1)) h8) (S (h v1 x v7))) h0)) (C h6 h0)

@[equational_result]
theorem Equation3591_implies_Equation4226 (G: Type _) [Magma G] (h: Equation3591 G) : Equation4226 G := fun x y z =>
  let v0 := M z z
  let v1 := M v0 x
  have h2 := h v1 y z
  let v3 := M (M v1 z) y
  let v4 := M v1 x
  let v5 := M (M z v1) v3
  have h6 := h v0 x x
  have h7 := R v4
  T (T (T (T (T (T (h x y v4) (C h7 (C (S h6) (R y)))) (C h7 (T (T h2 (h z v3 v1)) (C h6 (R v5))))) (S (h x v5 v4))) (C (R x) (C (S (h z x z)) (R v3)))) (S (h z v3 x))) (S h2)

@[equational_result]
theorem Equation3804_implies_Equation4325 (G: Type _) [Magma G] (h: Equation3804 G) : Equation4325 G := fun x y z =>
  let v0 := M z z
  have h1 := h y x x
  let v2 := M y x
  let v3 := M v2 v2
  let v4 := M x v2
  T (T (T (h x v2 v2) (h v3 v4 v2)) (C (T (C (T (h y x y) (C (R v2) (T (T (T (h y y z) (h (M z y) (M y z) v0)) (C (S (h y z z)) (S (h z y z)))) (S (h z z y))))) (R v4)) (S (h x v0 v2))) (T (T (C (R v3) h1) (S (h (M x x) v2 v2))) (S h1)))) (S (h y v0 x))

@[equational_result]
theorem Equation556_implies_Equation3128 (G: Type _) [Magma G] (h: Equation556 G) : Equation3128 G := fun x y z =>
  let v0 := M y x
  let v1 := M v0 z
  let v2 := M v1 y
  let v3 := M v2 z
  have h4 := R z
  have h5 := R y
  have h6 := R v3
  have h7 := R x
  T (T (h x v3 y) (C h6 (T (C h5 (C h6 (T (C h7 (T (h y z x) (C h4 (C h7 (T (C h4 (h v0 v1 z)) (S (h v1 z v1))))))) (S (h v0 x z))))) (C h5 (C h6 (T (h v0 v3 z) (C h6 (T (C h4 (C h6 (T (h v1 z y) (C h4 (C h5 (T (C h4 (h v2 v3 z)) (S (h v3 z v3)))))))) (S (h y z v3)))))))))) (S (h v3 v3 y))

@[equational_result]
theorem Equation695_implies_Equation1523 (G: Type _) [Magma G] (h: Equation695 G) : Equation1523 G := fun x y z =>
  let v0 := M z z
  let v1 := M v0 v0
  have h2 := h v0 v1 y
  have h3 := S h2
  let v4 := M y y
  have h5 := h v4 v0 z
  have h6 := R v1
  have h7 := h v0 v0 z
  have h8 := R v0
  T (h x v4 z) (C (R v4) (C (R x) (T (C (T h7 (C h8 (T (T (T (C h8 (C (T h2 (C h6 (S h5))) (T (h v0 v1 z) (C h6 (S h7))))) (S (h (M v1 v4) v0 v0))) (C h6 h5)) h3))) h5) h3)))

@[equational_result]
theorem Equation1537_implies_Equation2998 (G: Type _) [Magma G] (h: Equation1537 G) : Equation2998 G := fun x y z =>
  have h0 := R x
  have h1 := S (h z x y)
  let v2 := M y (M z y)
  have h3 := R v2
  let v4 := M x x
  have h5 := R v4
  have h6 := T (T (h v4 x v2) (C h5 (T (C h3 h1) (C h3 (h z v2 y))))) (S (h (M v2 v2) x v2))
  T (T (T (h x x v4) (C h5 (S (h x x x)))) (C h6 h0)) (C (C h3 (T (T (h v2 x v4) (C h5 (T (C h5 (C h3 h6)) (S (h v2 x v2))))) h1)) h0)

@[equational_result]
theorem Equation1707_implies_Equation692 (G: Type _) [Magma G] (h: Equation1707 G) : Equation692 G := fun x y z =>
  let v0 := M z y
  let v1 := M v0 z
  let v2 := M x v1
  let v3 := M y v2
  have h4 := h z v0 z
  let v5 := M (M z v0) z
  let v6 := M v2 x
  T (T (h x v2 v2) (C (T (T (h v6 z x) (C (T (T (T (C h4 (R v6)) (S (h v5 v1 x))) (h v5 v1 v3)) (C (S h4) (C (S (h v2 y z)) (R v3)))) (R (M (M x z) x)))) (S (h (M v2 v3) z x))) (R (M (M v2 v2) v2)))) (S (h v3 v2 v2))

@[equational_result]
theorem Equation1507_implies_Equation2180 (G: Type _) [Magma G] (h: Equation1507 G) : Equation2180 G := fun x y z =>
  let v0 := M x z
  let v1 := M y z
  let v2 := M v1 y
  let v3 := M v2 v0
  have h4 := R (M x (M x v0))
  let v5 := M v0 v3
  let v6 := M v0 v5
  let v7 := M v0 x
  T (T (h x v0 x) (C (T (T (h v7 v0 x) (C (T (T (T (h (M v0 v7) v0 x) (C (S (h z x v0)) h4)) (C (T (h z v3 v0) (C (T (C (R v3) (h z y v1)) (S (h v0 v2 v1))) (R v6))) h4)) (S (h v6 v0 x))) h4)) (S (h v5 v0 x))) h4)) (S (h v3 v0 x))

@[equational_result]
theorem Equation1537_implies_Equation2389 (G: Type _) [Magma G] (h: Equation1537 G) : Equation2389 G := fun x y z =>
  have h0 := R x
  let v1 := M z (M y z)
  have h2 := R v1
  have h3 := S (h y x z)
  let v4 := M x x
  have h5 := R v4
  have h6 := T (T (h v4 x v1) (C h5 (T (C h2 h3) (C h2 (h y v1 z))))) (S (h (M v1 v1) x v1))
  T (T (T (h x x v4) (C h5 (S (h x x x)))) (C h6 h0)) (C (C (T (T (h v1 x v4) (C h5 (T (C h5 (C h2 h6)) (S (h v1 x v1))))) h3) h2) h0)

@[equational_result]
theorem Equation1909_implies_Equation2 (G: Type _) [Magma G] (h: Equation1909 G) : Equation2 G := fun x y =>
  let v0 := M y y
  have h1 := R v0
  have h2 := h y x x
  let v3 := M x x
  have h4 := R v3
  let v5 := M y x
  have h6 := h v5 y y
  have h7 := R x
  let v8 := M v5 y
  have h9 := h v5 x y
  T (T (h x y x) (C (T (T (T (C (T (T h2 (C (C h7 h9) h4)) (S (h (M x v8) x v3))) h4) (S h9)) h6) (C (T (T (h (M y v8) x v0) (C (C h7 (S h6)) h4)) (S h2)) h1)) h1)) (S (h y y y))

@[equational_result]
theorem Equation2308_implies_Equation968 (G: Type _) [Magma G] (h: Equation2308 G) : Equation968 G := fun x y z =>
  let v0 := M z x
  let v1 := M z y
  let v2 := M v1 v0
  have h3 := h y y v0
  have h4 := R v0
  have h5 := h x (M y v2) v2
  have h6 := R v1
  have h7 := h x z v2
  T h7 (C (T (T (T (h (M z (M x (M z v2))) v1 v0) (C (T (C h6 (S h7)) (C h6 h5)) h4)) (C (T (T (C h6 (S h5)) (C (C (R z) h3) (R x))) (S (h (M y (M y (M y v0))) z x))) h4)) (S h3)) (R v2))

@[equational_result]
theorem Equation2554_implies_Equation2430 (G: Type _) [Magma G] (h: Equation2554 G) : Equation2430 G := fun x y z w =>
  let v0 := M w w
  let v1 := M z v0
  let v2 := M (M v0 z) v0
  have h3 := C (R w) (S (h w w x))
  let v4 := M (M w x) w
  have h5 := T (T (C (T (h z w v4) (C h3 (R z))) (R v0)) (h v2 w v4)) (C h3 (R v2))
  T (h x v1 y) (C (T (T (C h5 (R (M (M v1 y) v1))) (C (R (M v0 v2)) (C (T (C h5 (R y)) (S (h y v0 z))) (R v1)))) (S (h (M y v1) v0 z))) (R x))

@[equational_result]
theorem Equation627_implies_Equation308 (G: Type _) [Magma G] (h: Equation627 G) : Equation308 G := fun x y =>
  let v0 := M x y
  let v1 := M x v0
  have h2 := S (h v0 x x)
  let v3 := M (M x x) x
  let v4 := M v0 v3
  have h5 := R v1
  have h6 := S (h y x x)
  let v7 := M y v3
  have h8 := R x
  have h9 := T (h x y v7) (C h8 (C h8 (T (C h6 (R v7)) h6)))
  T (T (T (C h9 h8) (C h5 h9)) (C h5 (T (h v1 v0 v4) (C h5 (C h5 (T (C h2 (R v4)) h2)))))) (S (h v1 x v0))

@[equational_result]
theorem Equation962_implies_Equation949 (G: Type _) [Magma G] (h: Equation962 G) : Equation949 G := fun x y z =>
  let v0 := M y z
  let v1 := M z x
  let v2 := M v1 v0
  let v3 := M y v2
  have h4 := R v0
  have h5 := R v2
  have h6 := h y x z
  T (T (h x v0 v2) (C h4 (C (R (M v2 v0)) (T (T (S h6) (h y v3 z)) (C (R v3) (C (T (C (R z) (C (T (h y v0 v1) (C h4 (T (C h5 (C h6 (R v1))) (S (h z v2 x))))) h5)) (S (h v1 z v0))) h4)))))) (S (h v3 v0 v2))

@[equational_result]
theorem Equation978_implies_Equation3692 (G: Type _) [Magma G] (h: Equation978 G) : Equation3692 G := fun x y z =>
  let v0 := M y y
  let v1 := M z z
  let v2 := M v0 v1
  have h3 := S (h v0 v2 z)
  have h4 := h v0 v1 y
  have h5 := R v2
  have h6 := C h5 h4
  have h7 := R v0
  T (T (T (T (T (T (h (M x x) v2 z) (C h5 (S (h v0 v1 x)))) h6) h3) h4) (C (T (T (T (h v1 v2 z) (C h5 (S (h v0 v1 z)))) h6) h3) (R (M v0 v2)))) (C h7 (T (C h7 (T (h v2 v0 z) (C h7 (C (R v1) (T h6 h3))))) (S (h v1 v0 y))))

@[equational_result]
theorem Equation1090_implies_Equation3770 (G: Type _) [Magma G] (h: Equation1090 G) : Equation3770 G := fun x y z =>
  let v0 := M x z
  let v1 := M y z
  let v2 := M v1 v0
  have h3 := S (h v0 v2 x)
  let v4 := M (M v0 (M v2 x)) x
  have h5 := R v1
  have h6 := S (h z v1 x)
  let v7 := M (M z (M v1 x)) x
  T (C (R x) (T (T (h y v1 v7) (C h5 (T (C (C (R y) h6) (R v7)) h6))) (C (T (h v1 v2 v4) (C (R v2) (T (C (C h5 h3) (R v4)) h3))) (R z)))) (S (h v2 x z))

@[equational_result]
theorem Equation1507_implies_Equation492 (G: Type _) [Magma G] (h: Equation1507 G) : Equation492 G := fun x y z =>
  let v0 := M z (M z y)
  let v1 := M x v0
  let v2 := M y v1
  let v3 := M v1 v2
  have h4 := R (M x (M x v1))
  let v5 := M v1 v3
  let v6 := M v1 x
  T (T (h x v1 v2) (C (T (T (h v6 v1 x) (C (T (T (T (h (M v1 v6) v1 x) (C (S (h v0 x v1)) h4)) (C (T (h v0 v2 v1) (C (S (h v1 y z)) (R v5))) h4)) (S (h v5 v1 x))) h4)) (S (h v3 v1 x))) (R (M v2 (M v2 v1))))) (S (h v2 v1 v2))

@[equational_result]
theorem Equation1665_implies_Equation27 (G: Type _) [Magma G] (h: Equation1665 G) : Equation27 G := fun x y z =>
  let v0 := M x y
  let v1 := M v0 z
  let v2 := M (M v1 v1) v1
  let v3 := M v1 v2
  let v4 := M (M x v0) z
  have h5 := h v0 z x
  let v6 := M (M y x) x
  let v7 := M x v6
  T (T (T (h x y v7) (C (R v0) (C (T (C (R v7) (h x x y)) (S (h x v6 x))) (R y)))) (C h5 (T h5 (C (T (h v1 v2 v1) (C (R v3) (S (h v1 v1 v1)))) (R v4))))) (S (h v1 v4 v3))

@[equational_result]
theorem Equation1993_implies_Equation4497 (G: Type _) [Magma G] (h: Equation1993 G) : Equation4497 G := fun x y z =>
  have h0 := S (h x x y)
  let v1 := M z z
  let v2 := M y y
  let v3 := M x v2
  let v4 := M v1 v1
  let v5 := M v2 v4
  T (h v3 v5 v1) (C (T (C (T (T (T (h v5 (M v3 v2) v3) (C (S (h v3 v3 y)) (S (h v3 v2 v1)))) (C (h v3 v3 z) (h v3 v1 x))) (S (h (M v1 (M x x)) (M v3 v1) v3))) (R v4)) (S (h v1 v1 x))) (T (C (R v3) (T (h v5 v3 x) (C h0 (S (h x v2 v1))))) h0))

@[equational_result]
theorem Equation3791_implies_Equation3500 (G: Type _) [Magma G] (h: Equation3791 G) : Equation3500 G := fun x y z =>
  let v0 := M z z
  let v1 := M v0 y
  have h2 := h z z z
  have h3 := R v1
  T (T (T (T (T (T (T (h x x v0) (h (M v0 x) (M x v0) (M x x))) (C (S (h x v0 x)) (S (h v0 x x)))) (S (h v0 v0 x))) (C (T (T (T (h z z v1) (h (M v1 z) (M z v1) v0)) (C (S (h z v1 z)) (S (h v1 z z)))) (S (h v1 v1 z))) (T h2 (h v0 v0 y)))) (S (h v1 (M y v0) v1))) (C h3 (T (h y v0 v0) (C h3 (S h2))))) (S (h y v1 v0))

@[equational_result]
theorem Equation3804_implies_Equation3297 (G: Type _) [Magma G] (h: Equation3804 G) : Equation3297 G := fun x y z =>
  let v0 := M z y
  let v1 := M z v0
  let v2 := M y x
  have h3 := h z v1 y
  T (T (T (T (h x x y) (C (R v2) (T (T (h x y z) (C (T (T (T (h z y v1) (C (T (T (T (h v1 y z) (h v0 (M v1 z) v1)) (C (S (h v1 v0 z)) (R (M v0 v1)))) (S (h v0 v0 v1))) h3)) (S (h (M y v1) v0 v0))) (S h3)) (R (M x z)))) (S (h x v1 z))))) (C (h y x x) (h x v1 x))) (S (h (M x v1) v2 (M x x)))) (S (h y v1 x))

@[equational_result]
theorem Equation522_implies_Equation26 (G: Type _) [Magma G] (h: Equation522 G) : Equation26 G := fun x y =>
  let v0 := M x y
  let v1 := M v0 y
  have h2 := h v1 v1 v0
  have h3 := h v0 v1 y
  have h4 := R v1
  have h5 := h y v1 v1
  have h6 := R v0
  have h7 := C h6 (T h5 (C h4 (S h3)))
  have h8 := R y
  T (T (T (h x v1 y) (C h4 (C h4 (T (C h8 (T (h v0 y y) (C h8 (T (T (T (C h8 (C h8 h7)) (S (h v1 y v0))) h2) (C h4 (C h4 (C h6 (T (C h4 h3) (S h5))))))))) (S (h v1 y v1)))))) (C h4 (C h4 h7))) (S h2)

@[equational_result]
theorem Equation522_implies_Equation2522 (G: Type _) [Magma G] (h: Equation522 G) : Equation2522 G := fun x y z =>
  let v0 := M x z
  let v1 := M v0 z
  let v2 := M y v1
  have h3 := R v2
  let v4 := M v2 y
  have h5 := R v1
  have h6 := R v4
  T (h x v2 v2) (C h3 (T (C h3 (C h3 (C (T (T (h x v4 z) (C h6 (C h6 (C (R z) (T (h v0 v1 x) (C h5 (T (T (C h5 (C (R x) (T (C (R v0) (h x v0 z)) (S (h z v0 v0))))) (C h5 (h v0 v1 z))) (S (h z v1 v1))))))))) (S (h v1 v4 z))) h3))) (S (h y v2 v1))))

@[equational_result]
theorem Equation765_implies_Equation4200 (G: Type _) [Magma G] (h: Equation765 G) : Equation4200 G := fun x y z =>
  let v0 := M z x
  let v1 := M v0 z
  let v2 := M v1 y
  have h3 := h v2 v1 v1
  have h4 := R z
  have h5 := R v0
  let v6 := M x y
  have h7 := h v6 v1 v2
  T (T h7 (C (R v1) (T (T (T (T (h (M v2 (M (M v1 v2) v6)) v0 z) (C h5 (C h4 (S h7)))) (C h5 (T (C h4 (C (R x) (h y v0 z))) (S (h (M z v2) z x))))) (C h5 (C h4 h3))) (S (h (M v1 (M (M v1 v1) v2)) v0 z))))) (S h3)

@[equational_result]
theorem Equation1507_implies_Equation2399 (G: Type _) [Magma G] (h: Equation1507 G) : Equation2399 G := fun x y z =>
  let v0 := M z x
  let v1 := M z v0
  let v2 := M y v1
  let v3 := M v2 y
  let v4 := M z v3
  let v5 := M z v4
  have h6 := h y v2 v3
  let v7 := M v3 (M v3 v2)
  T (T (h x z z) (C (T (T (h v0 z x) (C (T (T (h v1 y x) (C (T (T (T (C h6 (h v1 y v2)) (S (h v7 v3 v2))) (h v7 v3 z)) (C (S h6) (R v5))) (R (M x (M x y))))) (S (h v5 y x))) (R (M x (M x z))))) (S (h v4 z x))) (R (M z (M z z))))) (S (h v3 z z))

@[equational_result]
theorem Equation2779_implies_Equation4210 (G: Type _) [Magma G] (h: Equation2779 G) : Equation4210 G := fun x y z =>
  let v0 := M z y
  let v1 := M v0 x
  have h2 := R v0
  have h3 := h z x x
  let v4 := M x x
  let v5 := M v4 (M z x)
  have h6 := R v4
  let v7 := M x y
  T (T (h v7 v0 v0) (C (C (R (M v0 v0)) (T (T (T (T (h (M v7 v0) x x) (C (T (C h6 (S (h z x y))) (C h6 h3)) (R x))) (S (h v5 x x))) (h v5 v0 x)) (C (C (R v1) (S h3)) h2))) h2)) (S (h (M v1 z) v0 v0))

@[equational_result]
theorem Equation3791_implies_Equation3770 (G: Type _) [Magma G] (h: Equation3791 G) : Equation3770 G := fun x y z =>
  let v0 := M z y
  let v1 := M y x
  let v2 := M z z
  have h3 := S (h z x y)
  let v4 := M y z
  let v5 := M z x
  let v6 := M x y
  T (T (T (T (h x y y) (h v1 (M y y) v6)) (C (T (T (T (T (S (h y y x)) (h y y z)) (h v0 v4 v6)) (C (T (T (C (T (T (h x y z) (h v5 v4 v6)) (C (S (h y z x)) h3)) (h z y z)) (S (h v5 v2 v4))) (S (h x z z))) h3)) (S (h z z x))) (S (h y x y)))) (h v2 v1 v0)) (C (S (h y z z)) (S (h x z y)))

@[equational_result]
theorem Equation1710_implies_Equation3008 (G: Type _) [Magma G] (h: Equation1710 G) : Equation3008 G := fun x y z =>
  let v0 := M z z
  let v1 := M y v0
  let v2 := M v1 x
  let v3 := M v2 v2
  have h4 := h v0 y v2
  let v5 := M v3 y
  let v6 := M v2 y
  let v7 := M (M v6 v6) v1
  T (h x v1 v6) (C (R v2) (T (T (h v7 v0 v2) (C (T (T (T (T (C h4 (R v7)) (S (h v5 v1 v6))) (h v5 v1 x)) (C (T (S h4) (h v0 y z)) (R (M (M x x) v1)))) (S (h (M v0 y) v1 x))) (R (M v3 v0)))) (S (h y v0 v2))))

@[equational_result]
theorem Equation1977_implies_Equation2992 (G: Type _) [Magma G] (h: Equation1977 G) : Equation2992 G := fun x y z =>
  let v0 := M z y
  let v1 := M y v0
  let v2 := M v1 x
  let v3 := M v2 z
  have h4 := h y x v0
  let v5 := M x (M v0 x)
  let v6 := M x v2
  T (T (h x v2 v2) (C (R (M v2 (M v2 v2))) (T (T (h v6 x y) (C (R (M x (M y x))) (T (T (T (C (R v6) h4) (S (h v5 x v1))) (h v5 v3 v1)) (C (C (R v3) (S (h v2 y z))) (S h4))))) (S (h (M v3 v2) x y))))) (S (h v3 v2 v2))

@[equational_result]
theorem Equation2105_implies_Equation3906 (G: Type _) [Magma G] (h: Equation2105 G) : Equation3906 G := fun x y z =>
  let v0 := M z z
  let v1 := M (M y v0) y
  let v2 := M x x
  have h3 := R v2
  have h4 := R v0
  have h5 := R x
  have h6 := h x x x
  have h7 := C (C (T (C h6 h3) (S (h x v2 x))) h5) h3
  have h8 := h v2 x x
  T (T (T h8 h7) (C (T (T (T (T (T h8 h7) (C (C (T (h x v2 z) (C (S h6) h4)) h5) h3)) (S (h v0 x x))) (h v0 v1 z)) (C (C (S (h v0 y z)) (R v1)) h4)) h3)) (S (h v1 v0 x))

@[equational_result]
theorem Equation2780_implies_Equation2 (G: Type _) [Magma G] (h: Equation2780 G) : Equation2 G := fun x y =>
  have h0 := R x
  let v1 := M y x
  let v2 := M x x
  have h3 := R v2
  let v4 := M v1 x
  have h5 := h x y x
  let v6 := M v1 v2
  let v7 := M v2 x
  T (T (T (T (T (T (h x x x) (C (C h3 (h v2 x x)) h0)) (S (h (M v2 v7) x x))) (C h3 (T (T (h v7 x x) (C (C h3 (T (T (T (C (C h3 h5) h0) (S (h v6 x x))) (h v6 y x)) (C (C (R v1) (S h5)) h0))) h0)) (S (h v4 x x))))) (h (M v2 v4) x x)) (C (C h3 (S (h v1 x x))) h0)) (S (h y x x))

@[equational_result]
theorem Equation3145_implies_Equation31 (G: Type _) [Magma G] (h: Equation3145 G) : Equation31 G := fun x y =>
  let v0 := M y y
  let v1 := M v0 x
  have h2 := h v0 y v1
  have h3 := S h2
  have h4 := R v0
  have h5 := R v1
  have h6 := C h3 h5
  have h7 := h v1 v0 v0
  have h8 := h v1 y v1
  T (h x y v0) (C (T (T (T (C (T h8 (C (C (T (C h2 h5) (S h7)) h5) h5)) h4) (C (T (T (T (C (C (T h7 h6) h5) h5) (S h8)) h7) h6) h4)) (C (C (T (h v0 v0 v0) (C (S (h v0 y v0)) h4)) h5) h4)) h3) (R x))

@[equational_result]
theorem Equation3567_implies_Equation3553 (G: Type _) [Magma G] (h: Equation3567 G) : Equation3553 G := fun x y z =>
  let v0 := M x z
  let v1 := M v0 z
  have h2 := h x z x
  have h3 := C (S h2) (R z)
  let v4 := M v1 v0
  let v5 := M (M x x) x
  let v6 := M (M x y) x
  T (T (T (T (T (T (h x y x) (h y v5 x)) (h v5 v6 z)) (C (R v6) h3)) (h v6 v1 v0)) (C (R v1) (C (T (T (S (h y v0 x)) (C (R y) (T (T (T h2 (h z v5 v0)) (h v5 v4 z)) (C (R v4) h3)))) (S (h v0 y v1))) (R v0)))) (S (h y v1 v0))

@[equational_result]
theorem Equation4197_implies_Equation43 (G: Type _) [Magma G] (h: Equation4197 G) : Equation43 G := fun x y =>
  have h0 := S (h y x x)
  have h1 := R x
  let v2 := M y x
  let v3 := M x y
  have h4 := R v3
  have h5 := T (h x x v3) (C h0 h4)
  let v6 := M x x
  have h7 := h x y x
  T (T h7 (C (T (T (T (T (C h5 (R y)) (S (h x v3 y))) (h x v3 v2)) (C (T (T (C (C (T (h y x v6) (C (S h7) (R v6))) h1) h4) (S (h v6 x v3))) (C h5 h1)) (R v2))) (S (h v3 x v2))) h1)) h0

@[equational_result]
theorem Equation492_implies_Equation1152 (G: Type _) [Magma G] (h: Equation492 G) : Equation1152 G := fun x y z =>
  let v0 := M x y
  have h1 := h z v0 z
  let v2 := M z v0
  have h3 := R v2
  have h4 := h v0 v2 z
  have h5 := T h4 (C h3 (S h1))
  have h6 := R y
  let v7 := M v2 z
  have h8 := R x
  T (T (h x y v0) (C h6 (T (C h8 (C (R v0) (C h5 (T (h y v7 x) (C (R v7) (T (C h6 (C h8 (C h8 (T (C h3 h1) (S h4))))) (S (h x y x)))))))) (S (h v0 x v7))))) (C h6 h5)

@[equational_result]
theorem Equation522_implies_Equation759 (G: Type _) [Magma G] (h: Equation522 G) : Equation759 G := fun x y z =>
  let v0 := M y x
  let v1 := M z (M v0 z)
  have h2 := h v1 v0 v1
  have h3 := h v0 v1 z
  have h4 := R v0
  have h5 := R y
  have h6 := C h4 (C h4 (S h3))
  have h7 := R x
  T (T (h x y y) (C h5 (T (T (T (C h5 (C h5 (T (T (C h7 (T (h y x x) (C h7 (T (T (T (C h7 (C h7 h3)) (S (h v1 x v1))) h2) h6)))) (S (h v0 x v0))) h3))) (S (h v1 y v1))) h2) h6))) (C h5 (T (C h4 (C h4 h3)) (S h2)))

@[equational_result]
theorem Equation627_implies_Equation205 (G: Type _) [Magma G] (h: Equation627 G) : Equation205 G := fun x y =>
  let v0 := M y (M (M x x) x)
  have h1 := h x y v0
  have h2 := R v0
  have h3 := h y x x
  have h4 := R x
  let v5 := M x y
  let v6 := M (M x v5) x
  have h7 := S (h v5 v6 x)
  let v8 := M v5 (M (M v6 x) x)
  have h9 := S h3
  T (h x v5 v8) (C (T h1 (C h4 (C h4 (T (C h9 h2) h9)))) (T (T (C h4 (T (C h7 (R v8)) h7)) (C h4 (C h4 (T h3 (C h3 h2))))) (S h1)))

@[equational_result]
theorem Equation953_implies_Equation2 (G: Type _) [Magma G] (h: Equation953 G) : Equation2 G := fun x y =>
  let v0 := M y y
  have h1 := R v0
  have h2 := R x
  let v3 := M x x
  have h4 := R v3
  let v5 := M (M y x) v0
  T (T (T (T (T (T (h x x x) (C h2 (C (h v3 x x) h4))) (S (h (M (M x v3) v3) x x))) (C (T (T (T (T (C (h x x y) h4) (h (M (M x v5) v3) x x)) (C h2 (C (T (S (h v5 x x)) (h v5 x y)) h4))) (S (h (M (M y v5) v0) x x))) (C (S (h x y y)) h1)) h4)) (h (M (M x v0) v3) x y)) (C h2 (C (S (h v0 y x)) h1))) (S (h y x y))

@[equational_result]
theorem Equation1561_implies_Equation2170 (G: Type _) [Magma G] (h: Equation1561 G) : Equation2170 G := fun x y z =>
  let v0 := M y z
  let v1 := M v0 x
  let v2 := M z y
  let v3 := M v1 v2
  have h4 := R v3
  have h5 := h v2 x v0
  let v6 := M x v0
  let v7 := M v3 v1
  T (T (h x z y) (C (T (T h5 (C (R v6) (T (h (M v2 v1) v3 v1) (C (R v7) (S (h v1 v2 v1)))))) (S (h v7 x v0))) (T (T (h v6 v1 v2) (C h4 (S h5))) (C h4 (T (h v2 v0 v3) (C (S (h v1 y z)) (S (h v3 z y)))))))) (S (h v3 v3 v1))

@[equational_result]
theorem Equation1726_implies_Equation4109 (G: Type _) [Magma G] (h: Equation1726 G) : Equation4109 G := fun x y z =>
  let v0 := M (M y z) z
  let v1 := M v0 y
  have h2 := R y
  have h3 := h v0 x v0
  have h4 := h y v0 z
  let v5 := M x x
  have h6 := R v5
  have h7 := R (M v1 v1)
  have h8 := S (h v5 x y)
  have h9 := C (T h3 (C h6 (S h4))) h2
  T (T (h v5 v1 v1) (C h7 (T (T (T (C (T (C h6 h9) h8) h9) h8) (h v5 v1 y)) (C h7 (C (T (C h6 h4) (S h3)) h2))))) (S (h v1 v1 v1))

@[equational_result]
theorem Equation2196_implies_Equation692 (G: Type _) [Magma G] (h: Equation2196 G) : Equation692 G := fun x y z =>
  let v0 := M z y
  let v1 := M v0 z
  let v2 := M x v1
  let v3 := M y v2
  let v4 := M v3 v2
  have h5 := R v2
  have h6 := h z y y
  let v7 := M (M y y) y
  T (T (T (T (h x v1 z) (C (T (C (R (M v1 z)) h6) (S (h v7 v0 z))) h5)) (C (T (T (h v7 v0 x) (C (R (M (M v0 x) x)) (T (S h6) (h z y v2)))) (S (h v4 v0 x))) h5)) (h (M v4 v2) (M v2 v3) v3)) (C (S (h y v2 v3)) (S (h v2 v3 v2)))

@[equational_result]
theorem Equation2519_implies_Equation2917 (G: Type _) [Magma G] (h: Equation2519 G) : Equation2917 G := fun x y z =>
  let v0 := M x y
  let v1 := M y v0
  let v2 := M v1 z
  let v3 := M v2 z
  have h4 := R y
  have h5 := R v3
  have h6 := R v1
  T (T (h x v3 y) (C (C h5 (C (T (h v0 v2 y) (C (T (C (C h6 (T (h z v3 v1) (C (C h5 (T (C (C (R z) (h v1 z z)) h5) (S (h z z v3)))) h6))) (T (C (C (R v0) (h y z v0)) (R v2)) (S (h z v0 v2)))) (S (h v3 v1 z))) h4)) h5)) h4)) (S (h v3 v3 y))

@[equational_result]
theorem Equation3147_implies_Equation3500 (G: Type _) [Magma G] (h: Equation3147 G) : Equation3500 G := fun x y z =>
  let v0 := M z z
  let v1 := M v0 y
  have h2 := R v1
  let v3 := M x x
  have h4 := R v3
  let v5 := M y v1
  have h6 := R v5
  T (h v3 v5 v1) (C (T (T (T (T (C (T (T (C (T (C (T (T (h v5 v3 v5) (C (S (h v3 x v5)) h6)) (C (T (h v3 v0 v3) (C (S (h v0 z v3)) h4)) h6)) h6) (S (h v3 z v5))) h4) (C (h v3 x v3) h4)) (S (h v3 v3 v3))) h2) (C (h v3 x v1) h2)) (S (h v1 v3 v1))) (C (h v0 z y) (R y))) (S (h y v0 y))) h2)

@[equational_result]
theorem Equation3804_implies_Equation4135 (G: Type _) [Magma G] (h: Equation3804 G) : Equation4135 G := fun x y z =>
  let v0 := M x y
  let v1 := M v0 z
  let v2 := M v1 v1
  let v3 := M v1 z
  let v4 := M v0 v0
  let v5 := M z v0
  have h6 := h x y y
  let v7 := M y y
  T (T (T (T (T (T (T (T h6 (h v7 v0 z)) (C (R v5) (T (h v7 z v0) (C (R v1) (S h6))))) (h v5 (M v1 v0) v1)) (C (S (h v1 z v0)) (S (h v0 v0 z)))) (h v3 v4 v1)) (C (T (h v1 v4 v1) (C (S (h v0 z v0)) (R v2))) (R (M v3 v1)))) (S (h v3 v2 v1))) (S (h v1 z v1))

@[equational_result]
theorem Equation1060_implies_Equation1257 (G: Type _) [Magma G] (h: Equation1060 G) : Equation1257 G := fun x y z w =>
  let v0 := M y y
  let v1 := M v0 z
  let v2 := M v1 w
  have h3 := C (S (h y y x)) (R y)
  let v4 := M v0 (M z v0)
  let v5 := M y (M x y)
  have h6 := T (T (C (R v0) (T (h z y v5) (C (R z) h3))) (h v4 y v5)) (C (R v4) h3)
  have h7 := R v1
  T (h x v1 w) (C (R x) (T (T (C (C h7 (T (C (R w) h6) (S (h w v0 z)))) h7) (C (R v2) h6)) (S (h v2 v0 z))))

@[equational_result]
theorem Equation1571_implies_Equation3617 (G: Type _) [Magma G] (h: Equation1571 G) : Equation3617 G := fun x y z =>
  let v0 := M x y
  let v1 := M z x
  let v2 := M v1 y
  have h3 := h v0 v1 y
  let v4 := M v2 v0
  let v5 := M x (M z y)
  have h6 := T (R (M v0 v5)) (S (h z x y))
  T (h v0 v0 v5) (C h6 (T (T (C (R v0) h6) (C h3 (T (T (T (h z x x) (C (R (M x x)) (C (R x) (T (h v1 v2 v0) (C (R v4) (S (h x v1 y))))))) (S (h v4 x x))) (C (R v2) h3)))) (S (h v2 v2 (M v1 (M v0 y))))))

@[equational_result]
theorem Equation1902_implies_Equation3500 (G: Type _) [Magma G] (h: Equation1902 G) : Equation3500 G := fun x y z =>
  let v0 := M z z
  let v1 := M y (M v0 y)
  have h2 := R (M y y)
  have h3 := h v0 y z
  have h4 := C (S (h v0 y v1)) h3
  have h5 := h v1 v1 z
  have h6 := S (h v1 v0 x)
  let v7 := M x x
  T (T (T (h v7 x y) (C (T (T (h (M x (M v7 x)) (M v0 v0) x) (C (T (T (T (C (C (R v0) h3) (S (h v7 x v0))) h6) h5) h4) (R v7))) h6) h2)) (C (T h5 h4) h2)) (S (h v1 v0 y))

@[equational_result]
theorem Equation3120_implies_Equation2925 (G: Type _) [Magma G] (h: Equation3120 G) : Equation2925 G := fun x y z =>
  have h0 := R z
  let v1 := M x z
  let v2 := M (M y v1) y
  have h3 := h v2 v2 v1
  have h4 := R v1
  have h5 := h v1 y v2
  have h6 := C (C (S h5) h4) h4
  have h7 := R x
  T (T (h x z z) (C (T (T (T (C (C (T (T (C (T (h z x x) (C (T (T (T (C (C h5 h7) h7) (S (h v2 v2 x))) h3) h6) h7)) h7) (S (h v1 v1 x))) h5) h0) h0) (S (h v2 v2 z))) h3) h6) h0)) (C (T (C (C h5 h4) h4) (S h3)) h0)

@[equational_result]
theorem Equation3289_implies_Equation320 (G: Type _) [Magma G] (h: Equation3289 G) : Equation320 G := fun x y z =>
  let v0 := M x x
  have h1 := S (h z v0 x)
  have h2 := h x x z
  let v3 := M z z
  have h4 := R v3
  have h5 := h x x y
  have h6 := R v0
  have h7 := h y v0 x
  T (T (T (T (h x v0 x) (C h6 (T (S (h x x x)) h5))) (S h7)) (h y y v0)) (C (R y) (T (C h6 (T (T (T (T (T (T (T h7 (C h6 (T (S h5) h2))) h1) (h z v3 z)) (C h4 (S (h z z z)))) (C h4 (h z z x))) (S (h x v3 z))) h2)) h1))

@[equational_result]
theorem Equation3404_implies_Equation4512 (G: Type _) [Magma G] (h: Equation3404 G) : Equation4512 G := fun x y z =>
  let v0 := M x y
  have h1 := R v0
  let v2 := M y z
  have h3 := R z
  have h4 := h v2 y z
  have h5 := h z z y
  T (T (h x v2 v0) (C h1 (T (T (T (C (R v2) (T (T (h v0 x z) (C h3 (S (h y z x)))) (h z v2 y))) (S (h v2 y v2))) h4) (C h3 (T (T (T (T (S h5) (h z z z)) (C h3 (T (C h3 h5) (S h4)))) (C h3 (T (h v2 y v0) (C h1 (S (h z v0 y)))))) (S (h v0 v0 z))))))) (S (h v0 z v0))

@[equational_result]
theorem Equation3804_implies_Equation4305 (G: Type _) [Magma G] (h: Equation3804 G) : Equation4305 G := fun x y z =>
  let v0 := M y z
  let v1 := M z v0
  let v2 := M x y
  have h3 := h v0 v2 (M y y)
  have h4 := h y z y
  have h5 := h x y y
  T (T (T (T (T (h x v2 z) (C (R (M z v2)) (h x z y))) (C (h z v2 v0) (h v0 v2 v2))) (S (h (M v2 v2) v1 (M v0 v2)))) (C (T (T (h v2 v2 v0) (C (T h3 (C (S h5) (S h4))) (T (C h5 h4) (S h3)))) (S (h v0 v0 v2))) (R v1))) (S (h z v0 v0))

@[equational_result]
theorem Equation4176_implies_Equation4325 (G: Type _) [Magma G] (h: Equation4176 G) : Equation4325 G := fun x y z =>
  let v0 := M z z
  let v1 := M y x
  have h2 := R v1
  have h3 := R y
  have h4 := R x
  let v5 := M x v1
  T (T (T (T (h x v1 v1) (C (S (h v1 y x)) h2)) (C (T (T (C (h y x v5) h3) (S (h v5 (M x v5) y))) (C (R v5) (T (T (C h4 (T (h x v1 z) (C (S (h z y x)) (R z)))) (h x (M (M z y) z) y)) (C (C (S (h z z y)) h4) h3)))) h2)) (S (h (M (M v0 x) y) x v1))) (S (h y v0 x))

@[equational_result]
theorem Equation1293_implies_Equation3120 (G: Type _) [Magma G] (h: Equation1293 G) : Equation3120 G := fun x y z =>
  let v0 := M (M (M y y) x) x
  let v1 := M y x
  let v2 := M v1 y
  let v3 := M v2 y
  let v4 := M (M v2 z) z
  have h5 := R v0
  have h6 := R y
  have h7 := h y y x
  have h8 := R v3
  have h9 := S h7
  T (T (T (h x v3 v0) (C h8 (T (C (T (C (S (h y x y)) h5) h9) h5) h9))) (C h8 (T h7 (C (T h7 (C (T (h y v4 y) (C (R v4) (C (C (S (h v1 y z)) h6) h6))) h5)) h5)))) (S (h v4 v3 v0))

@[equational_result]
theorem Equation1740_implies_Equation978 (G: Type _) [Magma G] (h: Equation1740 G) : Equation978 G := fun x y z =>
  let v0 := M x y
  let v1 := M z z
  let v2 := M v1 v0
  let v3 := M y v2
  have h4 := R v1
  have h5 := R (M x x)
  T (T (h x v3 v0) (C (R (M v3 v3)) (C (T (T (h (M v0 x) x v1) (C h5 (T (C (S (h y z x)) h4) (C (T (h y z v3) (C h4 (C (T (T (h (M v3 y) x v1) (C h5 (C (S (h v2 z y)) h4))) (S (h v0 x v1))) (R v3)))) h4)))) (S (h (M v0 v3) x v1))) (R v0)))) (S (h v3 v3 v0))

@[equational_result]
theorem Equation1756_implies_Equation2 (G: Type _) [Magma G] (h: Equation1756 G) : Equation2 G := fun x y =>
  let v0 := M x x
  let v1 := M x y
  have h2 := h x v0 v0
  have h3 := S h2
  let v4 := M v0 v0
  have h5 := h v0 v4 x
  let v6 := M v4 x
  let v7 := M v6 v6
  have h8 := h v6 v7 v7
  let v9 := M v7 v7
  T (T h2 (C (T (T (T (C (R v0) (T h5 (C h8 h3))) (S (h v9 x x))) (h v9 x y)) (C (R v1) (T (C (S h8) h2) (S h5)))) (T (h v4 y y) (C (R (M y y)) (C h3 (R y)))))) (S (h y v1 v0))

@[equational_result]
theorem Equation1910_implies_Equation26 (G: Type _) [Magma G] (h: Equation1910 G) : Equation26 G := fun x y =>
  let v0 := M x y
  let v1 := M v0 y
  let v2 := M v0 (M y y)
  have h3 := h y v0 y
  have h4 := h v1 v0 y
  have h5 := S h4
  let v6 := M v0 (M v1 y)
  T (T (h x v0 v1) (C (T (T (C (C (R x) h3) (R (M x v1))) (S (h v2 x v1))) (C (R v0) (T (C (T h3 (C (R v2) (T h4 (C (T (h v6 v6 v1) (C (T (C (R v6) h5) h5) h5)) (R v1))))) h3) (S (h (M v1 v1) v2 v1))))) (R (M v0 v1)))) (S (h v1 v0 v1))

@[equational_result]
theorem Equation2180_implies_Equation2573 (G: Type _) [Magma G] (h: Equation2180 G) : Equation2573 G := fun x y z =>
  let v0 := M z x
  let v1 := M v0 y
  let v2 := M y v1
  let v3 := M v2 z
  let v4 := M y v3
  have h5 := C (S (h y y v1)) (R v1)
  have h6 := h v0 v2 y
  let v7 := M x y
  T (T (h x v4 y) (C (R (M (M v4 y) v4)) (T (h v7 z x) (C (C (T h6 h5) (R z)) (T (T (h (M v7 x) x v1) (C (R (M (M x v1) x)) (T (T (S (h v0 x y)) h6) h5))) (S (h y x v1))))))) (S (h v3 v4 y))

@[equational_result]
theorem Equation2196_implies_Equation1304 (G: Type _) [Magma G] (h: Equation2196 G) : Equation1304 G := fun x y z =>
  let v0 := M x z
  let v1 := M v0 z
  let v2 := M v1 y
  let v3 := M y v2
  let v4 := M v3 z
  let v5 := M v4 z
  have h6 := h y v2 v3
  let v7 := M (M v2 v3) v3
  T (T (h x z v2) (C (R (M (M z v2) v2)) (T (T (h v0 z x) (C (R (M (M z x) x)) (T (T (h v1 y x) (C (R (M (M y x) x)) (T (T (T (C (h v1 y v2) h6) (S (h v7 v3 v2))) (h v7 v3 z)) (C (R v5) (S h6))))) (S (h v5 y x))))) (S (h v4 z x))))) (S (h v3 z v2))

@[equational_result]
theorem Equation2196_implies_Equation2180 (G: Type _) [Magma G] (h: Equation2196 G) : Equation2180 G := fun x y z =>
  let v0 := M x z
  let v1 := M y z
  let v2 := M v1 y
  let v3 := M v2 v0
  let v4 := M (M v3 v0) v0
  let v5 := M (M v0 y) y
  T (T (T (T (h x z v1) (C (T (h (M (M z v1) v1) v1 y) (C (R (M v2 y)) (S (h y z v1)))) (T (T (T (C (h x z v0) (h z v0 y)) (S (h v5 (M z v0) v0))) (h v5 v3 v0)) (C (R v4) (S (h v2 v0 y)))))) (S (h v4 v2 y))) (h v4 (M v0 v3) v3)) (C (S (h v2 v0 v3)) (S (h v0 v3 v0)))

@[equational_result]
theorem Equation2714_implies_Equation1983 (G: Type _) [Magma G] (h: Equation2714 G) : Equation1983 G := fun x y z =>
  let v0 := M z x
  let v1 := M z y
  let v2 := M y v1
  let v3 := M v2 v0
  let v4 := M y v3
  have h5 := R v0
  have h6 := S (h z x v1)
  T (T (h x y z) (C (C (T (C (T (h y v1 v0) (C (C (T (C (T (h v1 (M (M x z) (M x v1)) v1) (C (C h6 h6) (R v1))) (R y)) (S (h z z y))) (T (C (h v1 y v3) h5) (S (h v4 v2 v0)))) h5)) (R x)) (S (h v4 z x))) (R (M y z))) (R z))) (S (h v3 y z))

@[equational_result]
theorem Equation3804_implies_Equation4176 (G: Type _) [Magma G] (h: Equation3804 G) : Equation4176 G := fun x y z =>
  let v0 := M y z
  let v1 := M v0 x
  let v2 := M v0 y
  let v3 := M x y
  have h4 := h x y x
  have h5 := S h4
  have h6 := h v0 x x
  let v7 := M x x
  have h8 := h v3 v1 v7
  T (T (T (T (T (T h4 (h v3 v7 v1)) (C (T (h v1 v7 v3) (C h5 (T (T (C h6 h4) (S h8)) (S (h v0 y x))))) (T h8 (C (S h6) h5)))) (S (h v1 v2 v3))) (h v1 v2 v0)) (C (S (h v0 z y)) (R (M v1 v0)))) (S (h v1 z v0))

@[equational_result]
theorem Equation489_implies_Equation1504 (G: Type _) [Magma G] (h: Equation489 G) : Equation1504 G := fun x y z =>
  let v0 := M y x
  let v1 := M y z
  let v2 := M z v1
  have h3 := C (R z) (S (h v1 y z))
  have h4 := h y z v1
  have h5 := T h4 h3
  have h6 := h v0 y x
  have h7 := R x
  have h8 := R v0
  T (h x v0 y) (C h8 (T (C h7 (T (T (T (C h5 (C h8 (T (T (T h4 h3) (h v2 y x)) (C (R y) (C (R v2) (T (C h7 h6) (S (h y x v0)))))))) (S (h v0 v2 y))) h6) (C h5 (R (M v0 (M x v0)))))) (S (h v2 x v0))))

@[equational_result]
theorem Equation684_implies_Equation2917 (G: Type _) [Magma G] (h: Equation684 G) : Equation2917 G := fun x y z =>
  let v0 := M y (M x y)
  let v1 := M v0 z
  have h2 := S (h z z x)
  let v3 := M z (M (M z x) x)
  let v4 := M v1 z
  have h5 := R v1
  have h6 := S (h y y x)
  let v7 := M y (M (M y x) x)
  T (T (T (h x y v7) (C (R y) (C (R x) (T (C h6 (R v7)) h6)))) (h v0 v1 v4)) (C h5 (T (T (S (h (M v1 v4) v0 z)) (C h5 (T (h v4 z v3) (C (R z) (C (R v4) (T (C h2 (R v3)) h2)))))) (S (h z v1 z))))

@[equational_result]
theorem Equation711_implies_Equation2958 (G: Type _) [Magma G] (h: Equation711 G) : Equation2958 G := fun x y z =>
  let v0 := M z (M (M z x) x)
  have h1 := h z z x
  have h2 := R y
  let v3 := M y (M y z)
  let v4 := M v3 x
  have h5 := S (h x x x)
  let v6 := M x (M (M x x) x)
  have h7 := R v4
  have h8 := C h7 (C h7 (T (C h5 (R v6)) h5))
  have h9 := h x v4 v6
  T (T h9 h8) (C h7 (T (T (T (C h7 (T h9 h8)) (S (h v3 v4 x))) (C h2 (C h2 (T h1 (C h1 (R v0)))))) (S (h z y v0))))

@[equational_result]
theorem Equation1462_implies_Equation27 (G: Type _) [Magma G] (h: Equation1462 G) : Equation27 G := fun x y z =>
  let v0 := M x y
  let v1 := M v0 z
  have h2 := h v1 v1 v1
  have h3 := h v0 z v1
  let v4 := M v1 v1
  have h5 := R v4
  have h6 := T h2 (C h5 (S h3))
  have h7 := R x
  let v8 := M v0 v0
  have h9 := T (h v0 v0 v0) (C (R v8) (S (h x y v0)))
  T (T (T (T (T (h x y x) (C h9 (C h7 h9))) (S (h v8 x x))) (C (T (T (h v0 z x) (C h6 (C h7 h6))) (S (h v4 v0 x))) (R v0))) (C h5 h3)) (S h2)

@[equational_result]
theorem Equation1774_implies_Equation16 (G: Type _) [Magma G] (h: Equation1774 G) : Equation16 G := fun x y =>
  let v0 := M y x
  let v1 := M y v0
  let v2 := M (M y y) v0
  have h3 := h v1 y v0
  have h4 := S h3
  let v5 := M (M y v1) v0
  have h6 := h y y v0
  T (T (h x v1 v0) (C (R (M v1 v0)) (T (T (C (R (M v1 x)) (C h6 (R x))) (S (h v2 v1 x))) (C (T (C h6 (T h6 (C (T h3 (C (R v1) (T (h v5 v1 v5) (C h4 (T (C h4 (R v5)) h4))))) (R v2)))) (S (h (M v1 v1) v1 v2))) (R v0))))) (S (h v1 v1 v0))

@[equational_result]
theorem Equation2196_implies_Equation1561 (G: Type _) [Magma G] (h: Equation2196 G) : Equation1561 G := fun x y z =>
  let v0 := M z y
  let v1 := M x v0
  let v2 := M y z
  let v3 := M v2 v1
  let v4 := M v3 v1
  have h5 := R v1
  T (T (T (T (h x v0 v0) (C (T (h (M (M v0 v0) v0) (M y v0) v0) (C (S (h z y v0)) (S (h y v0 v0)))) h5)) (C (T (T (h v0 y x) (C (R (M (M y x) x)) (T (h (M v0 y) v2 v1) (C (R v4) (S (h y z y)))))) (S (h v4 y x))) h5)) (h (M v4 v1) (M v1 v3) v3)) (C (S (h v2 v1 v3)) (S (h v1 v3 v1)))

@[equational_result]
theorem Equation2714_implies_Equation1137 (G: Type _) [Magma G] (h: Equation2714 G) : Equation1137 G := fun x y z =>
  let v0 := M z z
  let v1 := M y v0
  let v2 := M v1 x
  let v3 := M y v2
  have h4 := R v0
  let v5 := M x v0
  have h6 := h z x v0
  have h7 := S (h v0 x v3)
  T (T (h x v0 v0) (C (C (T (T (T (C (h v0 y v2) (R x)) (S (h v3 v1 x))) (h v3 (M v5 (M x v3)) v3)) (C (T (T (C h7 h7) (C (C h6 h6) h4)) (S (h v0 (M (M x z) v5) v0))) (R v3))) (R (M v0 v0))) h4)) (S (h v3 v0 v0))

@[equational_result]
theorem Equation3716_implies_Equation3921 (G: Type _) [Magma G] (h: Equation3716 G) : Equation3921 G := fun x y z =>
  let v0 := M x z
  let v1 := M v0 y
  let v2 := M x x
  have h3 := R v1
  have h4 := h x x x
  have h5 := S h4
  let v6 := M v2 v2
  let v7 := M (M x v0) y
  have h8 := R (M y v7)
  T (T (T (T (h x y v7) (C h4 h8)) (C (C h4 h4) h8)) (S (h v6 y v7))) (C (T (T (T (T (T (T (T h5 (h x x z)) (C h4 (R v0))) (h v6 v0 y)) (C (C h5 h5) h3)) (C h5 h3)) (R (M v2 v1))) (S (h x v0 y))) (R y))

@[equational_result]
theorem Equation3791_implies_Equation4684 (G: Type _) [Magma G] (h: Equation3791 G) : Equation4684 G := fun x y z =>
  let v0 := M z y
  let v1 := M v0 x
  let v2 := M x y
  have h3 := h v0 x y
  let v4 := M y v0
  let v5 := M v2 x
  let v6 := M y v2
  T (T (T (T (T (h v2 z y) (h v6 v0 (M v2 z))) (C (S (h z y v2)) (S (h y v2 z)))) (h v0 v6 v1)) (C (R (M v1 v0)) (T (T (T (C (h y v2 x) h3) (S (h v5 v4 v2))) (C (R v5) (T (T (h y v0 x) (h v2 v1 v4)) (C (S h3) (S (h x y v0)))))) (S (h x v1 v2))))) (S (h v0 x v1))

@[equational_result]
theorem Equation3804_implies_Equation3770 (G: Type _) [Magma G] (h: Equation3804 G) : Equation3770 G := fun x y z =>
  let v0 := M x z
  let v1 := M y z
  let v2 := M v1 x
  let v3 := M x v0
  let v4 := M x y
  let v5 := M z v0
  T (T (T (T (h x y x) (h v4 (M x x) v0)) (C (T (T (T (T (T (T (S (h x z x)) (h x z v0)) (C (R (M v0 z)) (h x v0 z))) (S (h v5 z v0))) (h v5 z v1)) (C (h v1 z x) (S (h y v0 z)))) (S (h y v2 v0))) (T (T (T (h v4 v0 x) (h v3 (M v4 x) v4)) (C (S (h v4 y x)) (R (M v3 v4)))) (S (h v3 y v4))))) (S (h v3 v2 y))) (S (h v1 v0 x))

@[equational_result]
theorem Equation489_implies_Equation2573 (G: Type _) [Magma G] (h: Equation489 G) : Equation2573 G := fun x y z =>
  let v0 := M z x
  let v1 := M v0 y
  have h2 := T (C (R y) (h v1 v0 y)) (S (h v0 y v1))
  let v3 := M y v1
  have h4 := R x
  let v5 := M v3 z
  have h6 := R v5
  have h7 := R v3
  T (h x v3 v5) (C h7 (T (T (C h4 (T (C h6 (C h7 (T (h v5 x v3) (C h4 (C h6 (T (C h2 (R (M x v3))) (S (h x v0 y)))))))) (S (h v3 v5 x)))) (C h4 (T (h v3 z x) (C (R z) (C h2 (R (M x v0))))))) (S (h z x v0))))

@[equational_result]
theorem Equation1943_implies_Equation14 (G: Type _) [Magma G] (h: Equation1943 G) : Equation14 G := fun x y =>
  let v0 := M x y
  let v1 := M y v0
  have h2 := S (h v1 v1 v0)
  have h3 := S (h y v1 v0)
  let v4 := M v1 v0
  let v5 := M v1 v4
  have h6 := S (h v5 v1 y)
  let v7 := M v1 (M v1 v1)
  let v8 := M v1 (M v1 y)
  T (h x v1 y) (C (T (T (h v8 v8 (M v5 y)) (C (T (C (R v8) (T (T h6 (h v5 v1 v1)) (C (R v7) h3))) (S (h v7 v1 y))) (T (T h6 (h v5 v5 v4)) (C (T (C (R v5) h2) h3) h2)))) (S (h y v1 v1))) (R v0))

@[equational_result]
theorem Equation2741_implies_Equation2474 (G: Type _) [Magma G] (h: Equation2741 G) : Equation2474 G := fun x y z =>
  let v0 := M y y
  let v1 := M v0 z
  let v2 := M x v1
  have h3 := h z y v2
  have h4 := R v2
  let v5 := M x x
  have h6 := h v1 v2 v2
  let v7 := M v2 v2
  T (h x v7 v1) (C (S (h v2 v2 v2)) (T (T h6 (C (T (T (T (h (M v7 (M v1 v2)) x v2) (C (C (R v5) (S h6)) h4)) (C (T (h (M v5 v1) y z) (C (C (R v0) (S (h v0 x z))) h3)) h4)) (S (h (M v0 (M z v2)) v0 v2))) h4)) (S h3)))

@[equational_result]
theorem Equation2944_implies_Equation684 (G: Type _) [Magma G] (h: Equation2944 G) : Equation684 G := fun x y z =>
  let v0 := M (M y z) z
  let v1 := M x v0
  have h2 := R v1
  let v3 := M (M x (M x y)) y
  have h4 := R z
  have h5 := h y x y
  have h6 := S (h x x x)
  let v7 := M (M x (M x x)) x
  have h8 := C (C (T (C (R v7) h6) h6) h2) h2
  have h9 := h x v7 v1
  T (T h9 h8) (C (T (T (T (C (T h9 h8) h2) (S (h v0 x v1))) (C (C (T h5 (C (R v3) h5)) h4) h4)) (S (h y v3 z))) h2)

