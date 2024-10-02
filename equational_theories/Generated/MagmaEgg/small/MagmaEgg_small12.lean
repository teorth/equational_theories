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
theorem Equation2956_implies_Equation104 (G: Type _) [Magma G] (h: Equation2956 G) : Equation104 G := fun x y =>
  have h0 := R x
  have h1 := h y x x
  have h2 := S h1
  let v3 := M (M x (M x x)) y
  have h4 := R v3
  have h5 := h x v3 y
  let v6 := M y x
  let v7 := M x (M v6 x)
  have h8 := S (h v6 v7 y)
  let v9 := M (M v7 (M v7 y)) v6
  T (h x v9 v6) (C (T (T (C (T (C (R v9) h8) h8) h0) (C (C (T h1 (C h4 h1)) h0) h0)) (S h5)) (T h5 (C (C (T (C h4 h2) h2) h0) h0)))

@[equational_result]
theorem Equation3159_implies_Equation364 (G: Type _) [Magma G] (h: Equation3159 G) : Equation364 G := fun x y =>
  have h0 := R x
  let v1 := M y x
  have h2 := S (h y v1 y)
  have h3 := R y
  have h4 := R v1
  let v5 := M x x
  have h6 := S (h x v5 x)
  have h7 := C (h x x v5) h0
  have h8 := C (C (C (T (C (T (h v1 x x) (C (T (C (C (T h7 h6) h0) h4) (R (M v5 v1))) h4)) h4) (S (h v1 x v1))) h4) h3) h3
  have h9 := h y v1 v1
  T (T (T h7 h6) (h x y y)) (C (C (T (C (T (T (T (C (T h9 h8) h3) h2) h9) h8) h3) h2) h0) h0)

@[equational_result]
theorem Equation3161_implies_Equation2132 (G: Type _) [Magma G] (h: Equation3161 G) : Equation2132 G := fun x y z =>
  let v0 := M z z
  have h1 := T (C (h y z v0) (R y)) (S (h v0 v0 y))
  let v2 := M y y
  let v3 := M v2 x
  have h4 := R v3
  have h5 := h v3 z v0
  have h6 := h v0 v0 v3
  have h7 := R v0
  T (h x v3 v2) (C (T (C (T (T (T (T (T (C (R (M v3 v3)) h1) (C (T (C h5 h4) (S h6)) h7)) (C (h v0 z v0) h7)) (S (h v0 v0 v0))) h6) (C (S h5) h4)) (R x)) (S (h v3 y x))) h1)

@[equational_result]
theorem Equation3211_implies_Equation2917 (G: Type _) [Magma G] (h: Equation3211 G) : Equation2917 G := fun x y z =>
  let v0 := M x y
  let v1 := M y v0
  let v2 := M v1 z
  let v3 := M v2 z
  have h4 := R v2
  have h5 := R v3
  have h6 := R z
  have h7 := C (S (h v1 v1 z)) h6
  have h8 := h z v3 v1
  T (T (T (T (T (h x v0 y) (C (S (h y x y)) (R v0))) (h v1 v2 z)) (C (S (h z v1 z)) h4)) (C (T h8 (C (T (T h7 (h v2 z v3)) (C (T (C (C (C (T h8 (C h7 h5)) h5) h5) h4) (S (h v3 v2 v3))) h6)) h5)) h4)) (S (h v3 v2 z))

@[equational_result]
theorem Equation3364_implies_Equation3534 (G: Type _) [Magma G] (h: Equation3364 G) : Equation3534 G := fun x y z =>
  let v0 := M z y
  let v1 := M x y
  let v2 := M v0 (M x v0)
  let v3 := M y v0
  let v4 := M v0 v3
  have h5 := h y v2 v0
  T (T (T (T (h x y v0) h5) (h v2 v4 v4)) (C (T (T (S (h z v0 y)) (C (R z) (T (h z y y) (h y v3 v0)))) (S (h v0 z v3))) (T (T (C (R v4) (T (T (S h5) (h y v2 v1)) (C (R v2) (T (S (h x v1 y)) (h x v1 v0))))) (S (h v1 v4 v2))) (S (h y v1 v0))))) (S (h x (M v0 z) y))

@[equational_result]
theorem Equation3791_implies_Equation4673 (G: Type _) [Magma G] (h: Equation3791 G) : Equation4673 G := fun x y z =>
  let v0 := M x z
  let v1 := M x y
  let v2 := M v0 v1
  let v3 := M z x
  let v4 := M x v1
  T (T (T (h v1 z z) (C (T (T (T (T (T (T (h z v1 x) (C (h x z x) (h v1 x x))) (S (h v3 v4 (M x x)))) (C (h z x v1) (h x v1 z))) (S (h v4 v3 (M v1 z)))) (S (h v1 z x))) (h v1 z v0)) (T (T (T (T (h z z x) (h v0 v3 (M z z))) (C (S (h z x z)) (S (h x z z)))) (h v3 v0 v1)) (C (S (h y z x)) (R v2))))) (S (h (M z v0) (M y z) v2))) (S (h v0 y z))

@[equational_result]
theorem Equation3804_implies_Equation4612 (G: Type _) [Magma G] (h: Equation3804 G) : Equation4612 G := fun x y z =>
  let v0 := M y z
  let v1 := M x x
  let v2 := M v1 y
  let v3 := M v1 x
  let v4 := M x z
  let v5 := M x y
  T (T (T (T (T (h v1 y x) (h v5 v3 v1)) (C (S (h v1 x x)) (S (h x y x)))) (h v3 v5 v0)) (C (S (h x z y)) (T (T (T (T (C (h v1 x y) (h y z x)) (S (h v4 v2 (M y x)))) (h v4 v2 v3)) (C (T (C (R v3) (T (h v1 y v1) (C (R v2) (S (h x x x))))) (S (h v2 x v1))) (T (S (h v1 z x)) (h v1 z y)))) (S (h v0 x v2))))) (S (h v0 z x))

@[equational_result]
theorem Equation522_implies_Equation4421 (G: Type _) [Magma G] (h: Equation522 G) : Equation4421 G := fun x y z =>
  let v0 := M z y
  let v1 := M x y
  have h2 := R v1
  let v3 := M x v1
  have h4 := h v1 v3 v3
  have h5 := h x v3 v1
  have h6 := R v3
  have h7 := R x
  T (T (T (T (T (h v3 v1 v3) (C h2 (T (C h2 (T (T (T (C h6 (C h6 (C h7 (T h4 (C h6 (S h5)))))) (S (h v3 v3 x))) (h v3 v1 x)) (C h2 (C h2 (C h7 (T (C h6 h5) (S h4))))))) (S (h x v1 v1))))) (C h2 (h x v1 y))) (S (h y v1 v1))) (h y v0 v0)) (C (R v0) (S (h z v0 y)))

@[equational_result]
theorem Equation911_implies_Equation2 (G: Type _) [Magma G] (h: Equation911 G) : Equation2 G := fun x y =>
  let v0 := M x x
  have h1 := R v0
  let v2 := M x y
  have h3 := R x
  let v4 := M x v2
  have h5 := R v2
  have h6 := h x x y
  let v7 := M v0 v2
  let v8 := M x v0
  T (T (T (T (T (T (h x x x) (C h3 (C (h v0 x y) h1))) (S (h (M v8 v2) x x))) (C (T (T (h v8 x x) (C h3 (C (T (T (T (C h3 (C h6 h1)) (S (h v7 x x))) (h v7 x y)) (C h3 (C (S h6) h5))) h1))) (S (h v4 x x))) h5)) (h (M v4 v2) x x)) (C h3 (C (S (h v2 x y)) h1))) (S (h y x x))

@[equational_result]
theorem Equation934_implies_Equation3997 (G: Type _) [Magma G] (h: Equation934 G) : Equation3997 G := fun x y z =>
  let v0 := M x y
  have h1 := R x
  let v2 := M v0 v0
  let v3 := M x z
  have h4 := h v0 v3 y
  let v5 := M z v3
  have h6 := R v5
  T (h v0 v5 v0) (C h6 (T (T (T (C (T (h (M v5 v0) x z) (C h1 (T (C (R v3) (T (C (R z) (C h6 h4)) (S (h (M (M v3 y) (M y v0)) z v3)))) (S h4)))) (R v2)) (h (M (M x v0) v2) x x)) (C h1 (C (R (M x x)) (S (h v0 x v0))))) (S (h y x x))))

@[equational_result]
theorem Equation1507_implies_Equation1171 (G: Type _) [Magma G] (h: Equation1507 G) : Equation1171 G := fun x y z =>
  let v0 := M y z
  let v1 := M z v0
  let v2 := M v1 x
  let v3 := M y v2
  let v4 := M v3 (M v3 v2)
  let v5 := M v2 v1
  have h6 := h v1 v2 v3
  T (T (h x v1 z) (C (T (T (T (T (C h6 (h x v1 v2)) (S (h v4 v5 v2))) (h v4 v5 v4)) (C (T (S h6) (h v1 v2 y)) (R (M v4 (M v4 v5))))) (S (h (M y v3) v5 v4))) (T (C (h z y v2) (R (M z v1))) (S (h (M v2 (M v2 y)) v0 z))))) (S (h v3 y v2))

@[equational_result]
theorem Equation1929_implies_Equation3297 (G: Type _) [Magma G] (h: Equation1929 G) : Equation3297 G := fun x y z =>
  let v0 := M z (M z y)
  let v1 := M y v0
  have h2 := R (M v1 v1)
  have h3 := h v0 v0 x
  let v4 := M x x
  have h5 := R v4
  have h6 := h y z v0
  have h7 := R y
  have h8 := S (h v4 y x)
  have h9 := C h7 (T h3 (C (S h6) h5))
  T (T (h v4 v1 v1) (C (T (T (T (C h9 (T (C h9 h5) h8)) h8) (h v4 y v1)) (C (C h7 (T (C h6 h5) (S h3))) h2)) h2)) (S (h v1 v1 v1))

@[equational_result]
theorem Equation1993_implies_Equation695 (G: Type _) [Magma G] (h: Equation1993 G) : Equation695 G := fun x y z =>
  let v0 := M z z
  let v1 := M v0 y
  let v2 := M x v1
  have h3 := h v0 y v2
  let v4 := M v2 v2
  let v5 := M y v4
  let v6 := M y v2
  let v7 := M v1 (M v6 v6)
  T (h x v1 v6) (C (T (T (h v7 v0 v2) (C (R (M v0 v4)) (T (T (T (T (C (R v7) h3) (S (h v5 v1 v6))) (h v5 v1 x)) (C (R (M v1 (M x x))) (T (S h3) (h v0 y z)))) (S (h (M y v0) v1 x))))) (S (h y v0 v2))) (R v2))

@[equational_result]
theorem Equation2776_implies_Equation16 (G: Type _) [Magma G] (h: Equation2776 G) : Equation16 G := fun x y =>
  let v0 := M y x
  let v1 := M y v0
  have h2 := R v1
  have h3 := R v0
  have h4 := h y y y
  let v5 := M y y
  let v6 := M v5 v5
  let v7 := M x y
  T (T (h x y v1) (C (C (R (M y v1)) (T (T (h v7 v0 v1) (C (C (R (M v0 v1)) (T (T (T (T (h (M v7 v0) y x) (C (T (C h3 (S (h y x y))) (C h3 h4)) (R x))) (S (h v6 y x))) (h v6 y v0)) (C (C h2 (S h4)) h3))) h2)) (S (h (M v1 y) v0 v1)))) h2)) (S (h v1 y v1))

@[equational_result]
theorem Equation3791_implies_Equation3404 (G: Type _) [Magma G] (h: Equation3791 G) : Equation3404 G := fun x y z =>
  let v0 := M x y
  let v1 := M z x
  let v2 := M y v1
  have h3 := h v1 x y
  let v4 := M v0 z
  let v5 := M v1 x
  have h6 := h x y v1
  let v7 := M x v0
  T (T (T (T h6 (C (T (T (T (h v1 x v0) (C (S (h y z x)) (R v7))) (h (M y z) v7 v1)) (C (S (h x y z)) (S (h v0 z x)))) (T (T (h y v1 x) (h v0 v5 v2)) (C (S h3) (S h6))))) (S (h v4 v5 v0))) (C (R v4) h3)) (S (h z v2 v0))

@[equational_result]
theorem Equation3791_implies_Equation4362 (G: Type _) [Magma G] (h: Equation3791 G) : Equation4362 G := fun x y z =>
  let v0 := M x z
  let v1 := M v0 x
  let v2 := M x y
  let v3 := M y z
  let v4 := M v3 x
  T (T (T (T (T (T (T (T (h x v3 x) (h (M x x) v4 v0)) (C (S (h z x x)) (R (M v4 v0)))) (C (h z x y) (T (T (C (h v3 x z) (h x z v3)) (S (h v0 v4 (M z v3)))) (S (h z v3 x))))) (S (h v2 z v3))) (h v2 z v0)) (C (R (M v0 v2)) (T (T (h z v0 x) (h v0 v1 (M z v0))) (C (S (h v0 x z)) (S (h x z v0)))))) (S (h v2 v1 v0))) (S (h y v0 x))

@[equational_result]
theorem Equation3804_implies_Equation4413 (G: Type _) [Magma G] (h: Equation3804 G) : Equation4413 G := fun x y z =>
  let v0 := M x y
  let v1 := M y z
  let v2 := M x z
  let v3 := M v2 x
  let v4 := M x v0
  let v5 := M v0 v4
  T (T (T (T (T (T (T (T (h x v0 v4) (C (R (M v4 v0)) (h x v4 v0))) (S (h v5 v0 v4))) (h v5 v0 v2)) (C (h v2 v0 x) (T (C (R v5) (h x z y)) (S (h v1 v4 v0))))) (S (h v1 v3 v4))) (h v1 v3 v0)) (C (T (T (T (T (S (h v2 y x)) (h v2 y v0)) (C (h v0 y x) (R (M v2 v0)))) (S (h v2 (M v0 x) v0))) (S (h v0 z x))) (R (M v1 v0)))) (S (h v1 z v0))

@[equational_result]
theorem Equation3992_implies_Equation41 (G: Type _) [Magma G] (h: Equation3992 G) : Equation41 G := fun x y z =>
  let v0 := M x x
  have h1 := h y z v0
  let v2 := M y z
  have h3 := R v2
  have h4 := h x x v2
  have h5 := S h4
  let v6 := M v2 v0
  have h7 := R v6
  have h8 := C (T (T (C (C (R x) h4) h7) (S (h v6 x x))) h5) h3
  have h9 := h v2 v0 (M x v0)
  T (T (T (T (T h4 (h v6 x v2)) (C (C h3 h5) h7)) (C (T (T h9 h8) (C (R v0) h1)) (T h9 h8))) (S (h (M v0 v2) y v0))) (S h1)

@[equational_result]
theorem Equation1537_implies_Equation3500 (G: Type _) [Magma G] (h: Equation1537 G) : Equation3500 G := fun x y z =>
  let v0 := M z z
  let v1 := M y (M v0 y)
  have h2 := R v0
  have h3 := h x x x
  let v4 := M x x
  have h5 := R x
  have h6 := R v4
  have h7 := C h5 (T (C h6 h3) (S (h x x v4)))
  have h8 := h v4 x x
  T (T (T h8 (C h6 h7)) (C h6 (T (T (T (T h8 (C h6 (T h7 (C h5 (T (h x z v4) (C h2 (S h3))))))) (S (h v0 x x))) (h v0 z v1)) (C h2 (C (R v1) (S (h v0 z y))))))) (S (h v1 x v0))

@[equational_result]
theorem Equation1790_implies_Equation1967 (G: Type _) [Magma G] (h: Equation1790 G) : Equation1967 G := fun x y z =>
  let v0 := M z y
  let v1 := M z x
  let v2 := M y v1
  let v3 := M v2 v0
  have h4 := h v3 v2 v0
  have h5 := R v1
  let v6 := M v2 z
  have h7 := h x v2 v0
  T (T h7 (C (R v3) (T (T (h (M (M v0 x) v2) v1 v3) (C (R (M v1 v3)) (T (T (T (C (S h7) h5) (C (h x v2 z) (T (h v1 z y) (C (h v0 v1 v2) (R v6))))) (S (h (M v3 v1) v6 (M v1 v2)))) (C h4 h5)))) (S (h (M (M v0 v3) v2) v1 v3))))) (S h4)

@[equational_result]
theorem Equation2332_implies_Equation2 (G: Type _) [Magma G] (h: Equation2332 G) : Equation2 G := fun x y =>
  have h0 := R y
  have h1 := R x
  let v2 := M x y
  have h3 := h x x x
  have h4 := C h1 (C h1 (S h3))
  let v5 := M x (M x (M x x))
  T (T (h x x y) (C (T (T (h v5 x y) (C (T h4 (C h1 (T (T (C (T (T h3 (C (T (T (T (h v5 x x) (C (T h4 (C h1 (C h1 (h x y x)))) h1)) (S (h (M y (M y v2)) x x))) (C h0 (C h0 (h v2 y y)))) h1)) (S (h (M y (M y (M v2 y))) y x))) h1) (S (h v2 y x))) (C h1 (h y x x))))) h0)) (S (h (M x (M x (M y x))) x y))) h0)) (S (h y x y))

@[equational_result]
theorem Equation2349_implies_Equation522 (G: Type _) [Magma G] (h: Equation2349 G) : Equation522 G := fun x y z =>
  let v0 := M x z
  let v1 := M z v0
  let v2 := M z v1
  let v3 := M x (M x (M z z))
  let v4 := M y (M y v1)
  have h5 := R v2
  have h6 := R z
  have h7 := R v3
  have h8 := h z x z
  have h9 := S h8
  T (T (T (h x v3 v2) (C (T (C h7 (T (C h7 (S (h z z x))) h9)) h9) h5)) (C (T h8 (C h7 (T h8 (C h7 (T (h z z v4) (C (C h6 (C h6 (S (h v0 y z)))) (R v4))))))) h5)) (S (h v4 v3 v2))

@[equational_result]
theorem Equation2740_implies_Equation2 (G: Type _) [Magma G] (h: Equation2740 G) : Equation2 G := fun x y =>
  have h0 := R x
  let v1 := M y y
  let v2 := M x x
  have h3 := R v2
  have h4 := h x y y
  have h5 := R v1
  let v6 := M v1 (M x y)
  let v7 := M v6 y
  T (T (T (T (T (T (h x x x) (C (C h3 (h v2 y x)) h0)) (S (h (M v1 (M v2 x)) x y))) (C h5 (T (T (T (T (C h3 h4) (h (M v2 v7) x x)) (C (C h3 (T (S (h v6 x y)) (h v6 y y))) h0)) (S (h (M v1 v7) x y))) (C h5 (S h4))))) (h (M v1 (M v1 x)) x y)) (C (C h3 (S (h v1 y x))) h0)) (S (h y x y))

@[equational_result]
theorem Equation3120_implies_Equation1181 (G: Type _) [Magma G] (h: Equation3120 G) : Equation1181 G := fun x y z =>
  let v0 := M z x
  let v1 := M z v0
  let v2 := M v1 y
  have h3 := R v2
  let v4 := M y v2
  have h5 := R v4
  have h6 := R v1
  T (h x v2 v2) (C (T (C (C (C h3 (T (T (h x z v4) (C (C (C (T (h v0 x v1) (C (T (T (C (C (T (C (h x z v0) (R v0)) (S (h z v0 v0))) (R x)) h6) (C (h v0 z v1) h6)) (S (h z v1 v1))) h6)) (R z)) h5) h5)) (S (h v1 z v4)))) h3) h3) (S (h y v1 v2))) h3)

@[equational_result]
theorem Equation3383_implies_Equation41 (G: Type _) [Magma G] (h: Equation3383 G) : Equation41 G := fun x y z =>
  let v0 := M y z
  have h1 := h y z v0
  have h2 := S h1
  let v3 := M y (M z y)
  have h4 := R v3
  have h5 := R z
  let v6 := M x x
  have h7 := R x
  T (T (T (T (h x x z) (C h5 (T (T (T (T (h x v6 v3) (C h4 (T (C h7 (T (h v6 x x) (C h7 (S (h x x v6))))) (S (h x x x))))) (h v3 v6 x)) (C h7 (T (C h4 (S (h y z v6))) (C h4 h1)))) (S (h v3 v0 x))))) (C h5 (T (h v3 v0 v0) (C (R v0) (C h4 h2))))) (S (h v0 v3 z))) h2

@[equational_result]
theorem Equation3385_implies_Equation4512 (G: Type _) [Magma G] (h: Equation3385 G) : Equation4512 G := fun x y z =>
  let v0 := M x y
  let v1 := M v0 z
  let v2 := M z x
  have h3 := R v1
  let v4 := M y z
  have h5 := R x
  let v6 := M v4 x
  T (T (T (T (h x v4 x) (h x (M x v6) v1)) (C h3 (C h5 (C (T (T (T (T (T (h x v6 v1) (C h3 (C h5 (C (T (h v4 x y) (C (R y) (T (C (R v4) (h x y z)) (S (h z x v4))))) h3)))) (S (h x (M y v2) v1))) (S (h y z x))) (h y z v0)) (C (R v0) (S (h z x y)))) h3)))) (S (h x (M v0 v2) v1))) (S (h v0 z x))

@[equational_result]
theorem Equation928_implies_Equation1670 (G: Type _) [Magma G] (h: Equation928 G) : Equation1670 G := fun x y z =>
  let v0 := M z y
  let v1 := M v0 z
  let v2 := M x y
  let v3 := M v2 v1
  have h4 := R v2
  let v5 := M v2 v0
  have h6 := S (h y v0 x)
  T (T (h x v1 z) (C (R v1) (C (R (M v1 z)) (T (T (T (C (R x) (T (h z v2 v0) (C h4 (C (R v5) (T (C (R z) (T (h v0 v0 (M (M v0 x) (M y x))) (C (R v0) (C h6 h6)))) (S (h y z y))))))) (S (h v5 x y))) (C h4 (h v0 v3 z))) (S (h (M v3 z) v2 v1)))))) (S (h v3 v1 z))

@[equational_result]
theorem Equation948_implies_Equation2 (G: Type _) [Magma G] (h: Equation948 G) : Equation2 G := fun x y =>
  let v0 := M x x
  have h1 := R v0
  let v2 := M y y
  have h3 := R x
  have h4 := R v2
  have h5 := h x y y
  let v6 := M (M y x) v2
  let v7 := M y v6
  T (T (T (T (T (T (h x x x) (C h3 (C (h v0 y x) h1))) (S (h (M (M x v0) v2) x y))) (C (T (T (T (T (C h5 h1) (h (M v7 v0) x x)) (C h3 (C (T (S (h v6 x y)) (h v6 y y)) h1))) (S (h (M v7 v2) x y))) (C (S h5) h4)) h4)) (h (M (M x v2) v2) x y)) (C h3 (C (S (h v2 y x)) h1))) (S (h y x y))

@[equational_result]
theorem Equation1773_implies_Equation2 (G: Type _) [Magma G] (h: Equation1773 G) : Equation2 G := fun x y =>
  have h0 := S (h y x y)
  have h1 := R x
  let v2 := M x y
  have h3 := R v2
  have h4 := h x x y
  let v5 := M x x
  let v6 := M v5 x
  let v7 := M v2 x
  T (T h4 (C h3 (C (T (T (h v5 y y) (C (R (M y y)) (C (T (T (h (M y v5) x y) (C h3 (C (T (T (T (C (h x x x) (C (h y x x) (R v5))) (S (h v7 v5 v6))) (h v7 v2 v6)) (C (S h4) (C h0 h3))) h1))) (S (h (M y v2) x y))) (R y)))) (S (h v2 y y))) h1))) h0

@[equational_result]
theorem Equation1901_implies_Equation2 (G: Type _) [Magma G] (h: Equation1901 G) : Equation2 G := fun x y =>
  have h0 := S (h y x y)
  let v1 := M y x
  have h2 := R v1
  have h3 := h x x y
  let v4 := M x x
  let v5 := M x v4
  let v6 := M x v1
  have h7 := R x
  T (T h3 (C (C h7 (T (T (h v4 y y) (C (C (R y) (T (T (h (M v4 y) x y) (C (C h7 (T (T (T (C (C (R v4) (h y x x)) (h x x x)) (S (h v6 v4 v5))) (h v6 v1 v5)) (C (C h2 h0) (S h3)))) h2)) (S (h (M v1 y) x y)))) (R (M y y)))) (S (h v1 y y)))) h2)) h0

@[equational_result]
theorem Equation3804_implies_Equation3489 (G: Type _) [Magma G] (h: Equation3804 G) : Equation3489 G := fun x y z =>
  let v0 := M y z
  let v1 := M v0 z
  let v2 := M x v1
  have h3 := h v1 z y
  let v4 := M z v1
  have h5 := h y v1 z
  T (T (T (h x x v1) (h (M v1 x) v2 (M y v1))) (C (T (C (T (T h5 (C (R v4) (T (T (T (h y z v1) (C h3 (T (T (T h5 (h v4 v0 v1)) (C (R (M v1 v0)) (S (h v0 v1 z)))) (S (h v0 v0 v1))))) (S (h v0 (M v1 y) v0))) (S h3)))) (S (h v1 v1 z))) (R v2)) (S (h x v1 v1))) (S (h y x v1)))) (S (h y v1 x))

@[equational_result]
theorem Equation2714_implies_Equation26 (G: Type _) [Magma G] (h: Equation2714 G) : Equation26 G := fun x y =>
  let v0 := M x y
  let v1 := M v0 y
  have h2 := R y
  have h3 := R v1
  have h4 := h v0 x v1
  have h5 := S h4
  let v6 := M x v0
  have h7 := h v1 (M v6 (M x v1)) v1
  have h8 := h x x v0
  T (T (h x x y) (C (T (T (T (T (C (C h8 h8) (R v0)) (S (h v0 (M (M x x) v6) v0))) (h v0 v0 y)) (C (T (C (C h4 h4) h3) (S h7)) h2)) (C (T h7 (C (C h5 h5) h3)) (h y x y))) h2)) (S (h v1 (M v0 v0) y))

@[equational_result]
theorem Equation3404_implies_Equation4146 (G: Type _) [Magma G] (h: Equation3404 G) : Equation4146 G := fun x y z =>
  let v0 := M x z
  let v1 := M v0 z
  have h2 := R v0
  have h3 := h x z v1
  let v4 := M v1 x
  have h5 := R v1
  have h6 := R y
  have h7 := R x
  T (T (h x y v0) (C h2 (T (C h6 (T (T (T (h v0 x x) (C h7 (S (h z x x)))) (C h7 (h z x v0))) (S (h v1 v0 x)))) (C h6 (T (C h5 (T h3 (C h5 (T (T (T (h z v4 v0) (C h2 (T (h v4 v1 z) (C (R z) (S h3))))) (C h2 (h z v0 v0))) (S (h v1 v0 v0)))))) (S (h v0 v1 v1))))))) (S (h v1 y v0))

@[equational_result]
theorem Equation3804_implies_Equation3940 (G: Type _) [Magma G] (h: Equation3804 G) : Equation3940 G := fun x y z =>
  let v0 := M x y
  let v1 := M z y
  let v2 := M x v1
  let v3 := M v2 v0
  let v4 := M v0 z
  have h5 := h x y y
  let v6 := M y y
  T (T (T (T (T h5 (h v6 v0 z)) (C (T (T (T (T (T (T (h z v0 v1) (C (R (M v1 v0)) (h z v1 y))) (S (h (M y v1) v0 v1))) (S (h x v1 y))) (h x v1 x)) (h v2 (M x x) v0)) (C (S (h x y x)) (R v3))) (T (h v6 z v0) (C (R v4) (S h5))))) (S (h v4 v3 v0))) (R (M v4 v3))) (S (h v2 z v0))

@[equational_result]
theorem Equation3804_implies_Equation4226 (G: Type _) [Magma G] (h: Equation3804 G) : Equation4226 G := fun x y z =>
  let v0 := M z z
  let v1 := M v0 x
  let v2 := M y y
  have h3 := h v0 x x
  let v4 := M x x
  have h5 := R v1
  let v6 := M x y
  T (T (T (T (h x y y) (h v2 v6 v1)) (C (T (T (T (C h3 (h x y x)) (S (h v6 v1 v4))) (h v6 v1 (M v1 x))) (C (T (T (C (T (h v1 x v0) (C h5 (T (C h5 (h z z z)) (S (h v0 x v0))))) h3) (S (h v4 v1 v1))) (S h3)) (S (h v1 y x)))) (R (M v2 v1)))) (S (h v2 (M v1 y) v1))) (S (h v1 y y))

@[equational_result]
theorem Equation1504_implies_Equation14 (G: Type _) [Magma G] (h: Equation1504 G) : Equation14 G := fun x y =>
  let v0 := M x y
  let v1 := M y v0
  have h2 := h y x y
  let v3 := M x (M x x)
  let v4 := M y x
  let v5 := M x v4
  have h6 := R (M x (M v1 x))
  T (T (T (T (T (h x y x) (C (T (h v4 x x) (C (T (T (T (h v5 v1 x) (C (S (h v0 y x)) h6)) (C (T (h v0 y v0) (C (R v1) (S h2))) h6)) (S (h y v1 x))) (R v3))) (R v5))) (S (h v3 y x))) (h v3 v0 x)) (C (T (S (h y x x)) h2) (R (M x (M v0 x))))) (S (h v1 v0 x))

@[equational_result]
theorem Equation2494_implies_Equation4647 (G: Type _) [Magma G] (h: Equation2494 G) : Equation4647 G := fun x y z =>
  let v0 := M (M z y) z
  let v1 := M (M v0 v0) v0
  have h2 := h v0 v1
  have h3 := R x
  have h4 := R v0
  have h5 := R z
  let v6 := M (M y y) y
  have h7 := h y v6
  have h8 := S h7
  T (T (C (C h3 (T (T (T (T h7 (h (M (M v6 v6) v6) v0)) (C (C h4 (T (T (T (C (C h8 h8) h8) (h v6 z)) (C (C h5 h8) h5)) h2)) h4)) (S (h v1 v0))) (C (C h2 h2) h2))) h3) (S (h (M (M v1 v1) v1) x))) (S h2)

@[equational_result]
theorem Equation2958_implies_Equation1507 (G: Type _) [Magma G] (h: Equation2958 G) : Equation1507 G := fun x y z =>
  let v0 := M z (M z y)
  have h1 := R y
  let v2 := M v0 y
  have h3 := S (h v0 x v0)
  let v4 := M (M x (M x v0)) v0
  let v5 := M y x
  let v6 := M v5 v0
  have h7 := S (h y v6 y)
  let v8 := M (M v6 (M v6 y)) y
  T (T (h x v8 y) (C (C (T (C (R v8) h7) h7) (R x)) h1)) (C (R v5) (T (T (h y z y) (C (T (h v2 v4 v0) (C (C (T (C (R v4) h3) h3) (R v2)) (R v0))) h1)) (S (h v0 v0 y))))

@[equational_result]
theorem Equation3193_implies_Equation364 (G: Type _) [Magma G] (h: Equation3193 G) : Equation364 G := fun x y =>
  let v0 := M y x
  let v1 := M v0 x
  have h2 := R x
  have h3 := S (h y y x)
  have h4 := R y
  have h5 := S (h v0 v0 y)
  have h6 := R v0
  have h7 := C (h v0 y x) h6
  have h8 := C (C (T (T (C (T h7 h5) h6) h7) h5) h4) h4
  have h9 := h y v0 v0
  have h10 := C (C (T (C (T (T (T (C (T h9 h8) h4) h3) h9) h8) h4) h3) h2) h2
  have h11 := h x y y
  T (C (T (T h11 h10) (h v1 v0 x)) (T h11 h10)) (S (h v1 v1 v0))

@[equational_result]
theorem Equation3550_implies_Equation41 (G: Type _) [Magma G] (h: Equation3550 G) : Equation41 G := fun x y z =>
  let v0 := M x x
  have h1 := h y z v0
  let v2 := M y z
  let v3 := M v2 v0
  have h4 := h x x v2
  have h5 := S h4
  let v6 := M v0 v2
  have h7 := R v6
  have h8 := R v2
  have h9 := T (h v0 v2 (M v0 x)) (C h8 (T (T (C h7 (C h4 (R x))) (S (h x v6 x))) h5))
  T (T (T (T (T (T h4 (h x v6 v2)) (C h7 (C h5 h8))) (C h9 h9)) (C (R v3) (C h1 (R v0)))) (S (h z v3 v0))) (S h1)

@[equational_result]
theorem Equation3567_implies_Equation4023 (G: Type _) [Magma G] (h: Equation3567 G) : Equation4023 G := fun x y z =>
  let v0 := M z x
  let v1 := M z v0
  let v2 := M (M v0 v1) v0
  let v3 := M (M y y) y
  have h4 := R v3
  let v5 := M (M x z) x
  let v6 := M v1 z
  T (T (T (T (T (T (T (h x y z) (h y (M v0 z) y)) (C (T (T (T (T (T (h v0 z z) (h z v6 z)) (C (R v6) (C (h z z x) (R z)))) (S (h v5 v6 z))) (S (h v0 v5 z))) (S (h z v0 x))) h4)) (h v1 v3 v1)) (C h4 (C (h v1 v1 v0) (R v1)))) (S (h v2 v3 v1))) (S (h y v2 y))) (S (h v1 y v0))

@[equational_result]
theorem Equation3791_implies_Equation3810 (G: Type _) [Magma G] (h: Equation3791 G) : Equation3810 G := fun x y z =>
  have h0 := h z x y
  let v1 := M y x
  let v2 := M x z
  let v3 := M x y
  have h4 := h x y z
  let v5 := M y z
  let v6 := M z x
  have h7 := h v6 v5 v3
  have h8 := h y z x
  T (T h4 h7) (C (T (T (T (T (T (T (S h8) (h y z y)) (C (h y y x) (T (T (h z y z) (h (M z z) v5 v6)) (C (S (h x z z)) (T (T (C h8 h0) (S h7)) (S h4)))))) (S (h v1 v2 v3))) (C (h y x z) (h x z y))) (S (h v2 v1 (M z y)))) (S (h z y x))) (S h0))

@[equational_result]
theorem Equation543_implies_Equation1964 (G: Type _) [Magma G] (h: Equation543 G) : Equation1964 G := fun x y z =>
  let v0 := M y (M z x)
  let v1 := M v0 (M y z)
  have h2 := h y z v1
  have h3 := S h2
  have h4 := h v0 y z
  have h5 := R v1
  have h6 := R z
  have h7 := C h6 (C h5 h4)
  have h8 := R v0
  T (T (h x v0 y) (C h8 (C (R y) (T (T (T (C (R x) (T (C h8 (T h2 (C h6 (C h5 (S h4))))) (C h8 (T (T h7 h3) (h y z x))))) (S (h z x v0))) (h z v1 v0)) (C h5 (C h8 (T h7 h3))))))) (S (h v1 v0 y))

@[equational_result]
theorem Equation684_implies_Equation2196 (G: Type _) [Magma G] (h: Equation684 G) : Equation2196 G := fun x y z =>
  let v0 := M y z
  let v1 := M v0 z
  have h2 := S (h v1 v1 x)
  let v3 := M v1 (M (M v1 x) x)
  let v4 := M x v1
  have h5 := R x
  have h6 := S (h y y v0)
  let v7 := M y (M (M y v0) v0)
  T (T (h x y v7) (C (R y) (C h5 (T (C h6 (R v7)) h6)))) (C (T (T (h y x v1) (C h5 (T (T (S (h v4 y z)) (h v4 v1 v3)) (C (R v1) (C (R v4) (T (C h2 (R v3)) h2)))))) (S (h v1 x v1))) (R (M x y)))

@[equational_result]
theorem Equation1097_implies_Equation2 (G: Type _) [Magma G] (h: Equation1097 G) : Equation2 G := fun x y =>
  let v0 := M x y
  let v1 := M x v0
  have h2 := R y
  have h3 := R v0
  let v4 := M x x
  have h5 := h x x (M x v4)
  have h6 := R x
  have h7 := h x x x
  have h8 := h x x (M y v4)
  have h9 := h y x x
  T (T (T (T h8 (C h6 (C (S h9) h6))) (h (M x (M y x)) y x)) (C h2 (C (T (T (C (T (T (T (C h6 (C h9 h6)) (S h8)) h5) (C h6 (C (S h7) h6))) h3) (C (T (C h6 (C h7 h6)) (S h5)) h3)) (h v1 y x)) h2))) (S (h y y (M v1 v0)))

@[equational_result]
theorem Equation1503_implies_Equation2 (G: Type _) [Magma G] (h: Equation1503 G) : Equation2 G := fun x y =>
  let v0 := M x x
  let v1 := M x v0
  let v2 := M y y
  have h3 := S (h v2 y y)
  let v4 := M y v2
  have h5 := h v0 x x
  have h6 := R y
  have h7 := h x x y
  T (T (T (T (T h7 (C (T (h v0 y y) (C (T (T (T (T (T (h (M y v0) v1 y) (C (S (h v0 x y)) (C h6 (S h5)))) (S h7)) (h x x x)) (C h5 (C (R x) h5))) (S (h v1 v1 x))) (R v4))) (C h6 h5))) (S (h v4 v1 y))) (h v4 v4 v1)) (C h3 (C (R v1) h3))) (S (h y y v1))

@[equational_result]
theorem Equation2551_implies_Equation2 (G: Type _) [Magma G] (h: Equation2551 G) : Equation2 G := fun x y =>
  let v0 := M y x
  let v1 := M v0 x
  have h2 := R y
  let v3 := M x x
  have h4 := h x x (M v3 x)
  have h5 := R x
  have h6 := h x x x
  have h7 := R v0
  have h8 := h x x (M v3 y)
  have h9 := h y x x
  T (T (T (T h8 (C (C h5 (S h9)) h5)) (h (M (M x y) x) y x)) (C (C h2 (T (T (C h7 (T (T (T (C (C h5 h9) h5) (S h8)) h4) (C (C h5 (S h6)) h5))) (C h7 (T (C (C h5 h6) h5) (S h4)))) (h v1 y x))) h2)) (S (h y y (M v0 v1)))

@[equational_result]
theorem Equation2944_implies_Equation1320 (G: Type _) [Magma G] (h: Equation2944 G) : Equation1320 G := fun x y z =>
  let v0 := M y x
  let v1 := M (M v0 z) z
  let v2 := M y v1
  have h3 := R v2
  let v4 := M (M x (M x y)) y
  have h5 := h y x y
  have h6 := R z
  have h7 := S (h v0 x v0)
  let v8 := M (M x (M x v0)) v0
  T (T (h x y v2) (C (C (C (R y) (T (T (T (h v0 v8 z) (C (C (T (C (R v8) h7) h7) h6) h6)) (h v1 y v2)) (C (T (C (C (T h5 (C (R v4) h5)) h3) h3) (S (h y v4 v2))) h3))) h3) h3)) (S (h v2 y v2))

@[equational_result]
theorem Equation2958_implies_Equation1181 (G: Type _) [Magma G] (h: Equation2958 G) : Equation1181 G := fun x y z =>
  let v0 := M z (M z x)
  let v1 := M v0 y
  have h2 := R v1
  have h3 := h y z x
  have h4 := S h3
  have h5 := R y
  let v6 := M y v1
  have h7 := h x v0 y
  have h8 := h v1 z x
  T (h x v6 v1) (C (T (C (T (C (C (T h3 (C h2 (T h7 (C (S h8) h5)))) h2) (T (C (T (h v6 v1 y) (C (C (T (C h2 (T (C h8 h5) (S h7))) h4) (R v6)) h5)) h2) (S (h y y v1)))) (S (h v1 v1 y))) (R x)) h4) h2)

@[equational_result]
theorem Equation3120_implies_Equation725 (G: Type _) [Magma G] (h: Equation3120 G) : Equation725 G := fun x y z =>
  let v0 := M z x
  let v1 := M v0 z
  let v2 := M y v1
  have h3 := R v2
  let v4 := M y v2
  have h5 := S (h v1 z v4)
  have h6 := R v4
  have h7 := R v1
  have h8 := C (C (C (T (h v0 v1 v1) (C (S (h z v0 v1)) h7)) (R z)) h6) h6
  have h9 := h x z v4
  T (T (T (T h9 h8) h5) (h v1 x v2)) (C (T (T (C (T (C (C (h x z v1) h7) (T (T h9 h8) h5)) (S (h v1 v1 v1))) h3) (C (h v1 y v2) h3)) (S (h y v2 v2))) h3)

@[equational_result]
theorem Equation3275_implies_Equation320 (G: Type _) [Magma G] (h: Equation3275 G) : Equation320 G := fun x y z =>
  let v0 := M z z
  have h1 := h z v0 x
  have h2 := h x z z
  have h3 := R v0
  let v4 := M x x
  have h5 := R v4
  have h6 := C h5 (S (h x x x))
  have h7 := h x v4 x
  T (T (T h7 h6) (h v4 y y)) (C (R y) (T (T (C h5 (h y z z)) (C (T (T (T (T (T h7 h6) (h v4 v0 x)) (C h3 (T (C h5 (C (R x) (T h1 (C h3 (S h2))))) (S (h x v4 v0))))) (C h3 h2)) (S h1)) (R (M z (M y v0))))) (S (h z v0 y))))

@[equational_result]
theorem Equation3804_implies_Equation3404 (G: Type _) [Magma G] (h: Equation3804 G) : Equation3404 G := fun x y z =>
  let v0 := M z x
  let v1 := M y v0
  let v2 := M x y
  let v3 := M v1 v2
  have h4 := h x y y
  have h5 := S h4
  let v6 := M y y
  have h7 := h v1 v2 v6
  have h8 := h y v0 y
  T (T (T (T (T (T h4 (h v6 v2 v1)) (C (T h7 (C h5 (S h8))) (T (h v6 v1 v2) (C (T (C h4 h8) (S h7)) h5)))) (S (h v3 v1 v2))) (h v3 v1 v0)) (C (R (M v0 v1)) (T (C (S (h x v0 y)) (R v0)) (S (h z v0 x))))) (S (h z v1 v0))

@[equational_result]
theorem Equation2958_implies_Equation3553 (G: Type _) [Magma G] (h: Equation2958 G) : Equation3553 G := fun x y z =>
  let v0 := M (M x (M x x)) x
  let v1 := M x z
  have h2 := R x
  have h3 := h x x x
  have h4 := T h3 (C (R v0) h3)
  let v5 := M x y
  let v6 := M (M x (M x v5)) v5
  let v7 := M v5 x
  have h8 := h v5 x v5
  T (h v5 v5 x) (C (T (T (T (C (C (T h8 (C (R v6) h8)) (R v7)) (R v5)) (S (h v7 v6 v5))) (C (C h4 (R y)) h2)) (S (h y v0 x))) (T (h x x z) (C (T (C (C h4 (R v1)) h2) (S (h v1 v0 x))) (R z))))

@[equational_result]
theorem Equation3770_implies_Equation4098 (G: Type _) [Magma G] (h: Equation3770 G) : Equation4098 G := fun x y z =>
  let v0 := M y y
  let v1 := M v0 z
  let v2 := M v1 v0
  let v3 := M z v0
  have h4 := h y y y
  have h5 := S h4
  have h6 := S (h v0 v1 x)
  let v7 := M v1 x
  have h8 := S (h v1 x x)
  let v9 := M x x
  T (T (T (T (T (T (h x x x) (h v9 v9 v7)) (C h8 h8)) (h v7 v7 (M v0 x))) (C (T (T h6 (h v0 v1 v0)) (C (R v2) h5)) (T (T h6 (C h4 (T (h v0 z v0) (C (R v3) h5)))) (S (h v3 v0 v0))))) (S (h v3 v2 v0))) (S (h v1 z v0))

@[equational_result]
theorem Equation3804_implies_Equation3932 (G: Type _) [Magma G] (h: Equation3804 G) : Equation3932 G := fun x y z =>
  let v0 := M y z
  let v1 := M x v0
  let v2 := M x z
  let v3 := M x y
  have h4 := h x y y
  have h5 := S h4
  let v6 := M y y
  have h7 := h v0 v3 v6
  have h8 := h y z y
  T (T (T (T (T (T (T h4 (h v6 v3 v0)) (C (T h7 (C h5 (S h8))) (T (h v6 v0 v3) (C (T (T (C h4 h8) (S h7)) (S (h x z y))) h5)))) (S (h v2 v0 v3))) (h v2 v0 v1)) (C (h v1 v0 x) (R (M v2 v1)))) (S (h v2 (M v1 x) v1))) (S (h v1 z x))

@[equational_result]
theorem Equation4013_implies_Equation3526 (G: Type _) [Magma G] (h: Equation4013 G) : Equation3526 G := fun x y z =>
  let v0 := M y z
  let v1 := M v0 z
  let v2 := M v0 (M v1 v0)
  let v3 := M y (M x y)
  have h4 := R v3
  let v5 := M x (M z x)
  let v6 := M z v1
  T (T (T (T (T (T (T (h x y z) (h (M z v0) x y)) (C h4 (T (T (T (T (T (h z v0 z) (h v6 z z)) (C (C (R z) (h z z x)) (R v6))) (S (h v6 v5 z))) (S (h v5 v0 z))) (S (h v0 z x))))) (h v3 v1 v1)) (C (C (R v1) (h v1 v1 v0)) h4)) (S (h v3 v2 v1))) (S (h v2 x y))) (S (h x v1 v0))

@[equational_result]
theorem Equation1507_implies_Equation1470 (G: Type _) [Magma G] (h: Equation1507 G) : Equation1470 G := fun x y z =>
  let v0 := M z (M z y)
  let v1 := M x y
  let v2 := M z (M z v1)
  let v3 := M x v1
  let v4 := M v1 v0
  have h5 := h y x v4
  let v6 := M v4 (M v4 x)
  let v7 := M y x
  T (h x y z) (C (T (T (T (T (h v7 y x) (C (T (T (T (T (h (M y v7) v1 x) (C (T (S (h y x y)) h5) (R (M x v3)))) (S (h v6 v1 x))) (h v6 v1 z)) (C (S h5) (R v2))) (R v3))) (S (h v2 y x))) (h v2 (M v1 x) v1)) (C (S (h x v1 z)) (S (h y x v1)))) (R v0))

@[equational_result]
theorem Equation1561_implies_Equation3417 (G: Type _) [Magma G] (h: Equation1561 G) : Equation3417 G := fun x y z =>
  let v0 := M x y
  let v1 := M y x
  let v2 := M z v1
  let v3 := M z v2
  have h4 := h z x y
  have h5 := h v1 v0 v2
  have h6 := h v2 y x
  have h7 := S h4
  have h8 := R v0
  T (T (h v0 v2 v0) (C (R (M v2 v0)) (T (T (T (C h8 h7) (C h8 (T (h z v1 z) (C (C (T h5 (C h7 (S h6))) (R z)) (T (C h4 h6) (S h5)))))) (S (h (M v3 z) x y))) (C (R v3) h4)))) (S (h v3 v2 v0))

@[equational_result]
theorem Equation1764_implies_Equation1098 (G: Type _) [Magma G] (h: Equation1764 G) : Equation1098 G := fun x y z =>
  let v0 := M z y
  let v1 := M x v0
  let v2 := M v1 z
  let v3 := M y v2
  have h4 := R v3
  have h5 := S (h x z y)
  let v6 := M v1 v2
  T (T (h x v2 v0) (C (R (M v2 v0)) (C (T (h v1 y v2) (C h4 (C (T (T (h v6 v3 v0) (C (R (M v3 v0)) (C (T (C (R v6) (T (T (h v0 v0 (M (M x y) z)) (C h5 (C h5 (R v0)))) (C (h x z v0) (R v1)))) (S (h (M z v0) v1 v2))) h4))) (S (h z v3 v0))) (R y)))) (R v2)))) (S (h v3 v2 v0))

@[equational_result]
theorem Equation1967_implies_Equation2586 (G: Type _) [Magma G] (h: Equation1967 G) : Equation2586 G := fun x y z =>
  let v0 := M z y
  let v1 := M v0 x
  let v2 := M y v1
  let v3 := M v2 z
  have h4 := R v3
  let v5 := M v2 v1
  have h6 := S (h x y z)
  T (T (h x v2 v0) (C (C (R v2) (T (h v1 z v2) (C (C (R z) (T (T (h v5 v3 v0) (C (C h4 (T (C (T (T (h v0 v0 (M y (M z x))) (C (C (R v0) h6) h6)) (C (R v1) (h x y v0))) (R v5)) (S (h (M v0 y) v1 v2)))) (R (M v0 v3)))) (S (h y v3 v0)))) h4))) (R (M v0 v2)))) (S (h v3 v2 v0))

@[equational_result]
theorem Equation2145_implies_Equation2 (G: Type _) [Magma G] (h: Equation2145 G) : Equation2 G := fun x y =>
  let v0 := M x x
  let v1 := M v0 x
  let v2 := M y y
  have h3 := S (h v2 y y)
  let v4 := M v2 y
  have h5 := h v0 x x
  have h6 := h x x y
  have h7 := R y
  T (T (T (T (T h6 (C (C h5 h7) (T (h v0 y y) (C (R v4) (T (T (T (T (T (h (M v0 y) v1 y) (C (C (S h5) h7) (S (h v0 x y)))) (S h6)) (h x x x)) (C (C h5 (R x)) h5)) (S (h v1 v1 x))))))) (S (h v4 v1 y))) (h v4 v4 v1)) (C (C h3 (R v1)) h3)) (S (h y y v1))

@[equational_result]
theorem Equation2714_implies_Equation1171 (G: Type _) [Magma G] (h: Equation2714 G) : Equation1171 G := fun x y z =>
  let v0 := M y z
  let v1 := M z v0
  let v2 := M v1 x
  let v3 := M y v2
  have h4 := R v2
  let v5 := M v0 v3
  have h6 := S (h y x v0)
  T (T (h x v0 v2) (C (C (T (T (T (C (h v0 z v2) (R x)) (S (h (M z v2) v1 x))) (C (T (h z v0 v3) (C (C (T (C (T (h v0 (M (M x y) (M x v0)) v0) (C (C h6 h6) (R v0))) (R z)) (S (h y y z))) (R v5)) (R v3))) h4)) (S (h v5 y v2))) (R (M v0 v2))) h4)) (S (h v3 v0 v2))

@[equational_result]
theorem Equation2958_implies_Equation725 (G: Type _) [Magma G] (h: Equation2958 G) : Equation725 G := fun x y z =>
  let v0 := M (M z x) z
  let v1 := M y v0
  let v2 := M y v1
  have h3 := R v2
  let v4 := M v2 v2
  have h5 := S (h v2 x v2)
  let v6 := M (M x (M x v2)) v2
  have h7 := S (h z v1 z)
  let v8 := M (M v1 (M v1 z)) z
  T (T (T (T (T (h x v8 z) (C (C (T (C (R v8) h7) h7) (R x)) (R z))) (h v0 v2 v2)) (C (S (h v4 y v0)) h3)) (C (T (h v4 v6 v2) (C (C (T (C (R v6) h5) h5) (R v4)) h3)) h3)) (S (h v2 v2 v2))

@[equational_result]
theorem Equation3159_implies_Equation218 (G: Type _) [Magma G] (h: Equation3159 G) : Equation218 G := fun x y =>
  have h0 := R x
  let v1 := M x x
  have h2 := h x x v1
  have h3 := h x v1 x
  let v4 := M y v1
  have h5 := S (h y v4 y)
  have h6 := R y
  have h7 := R v4
  have h8 := C (C (C (T (C (T (h v4 x x) (C (T (C (C (T (C h2 h0) (S h3)) h0) h7) (R (M v1 v4))) h7)) h7) (S (h v4 x v4))) h7) h6) h6
  have h9 := h y v4 v4
  T (h x y y) (C (C (T (C (T (T (T (C (T h9 h8) h6) h5) h9) h8) h6) h5) (T h3 (C (S h2) h0))) h0)

@[equational_result]
theorem Equation3607_implies_Equation3526 (G: Type _) [Magma G] (h: Equation3607 G) : Equation3526 G := fun x y z =>
  let v0 := M y z
  let v1 := M v0 z
  let v2 := M x v1
  let v3 := M v1 z
  have h4 := R z
  have h5 := R v2
  have h6 := h y z v1
  let v7 := M (M z v1) y
  T (T (T (T (h x y z) (h z (M v0 x) v2)) (C h5 (C (C (T (T (h v0 x v2) (C h5 (C (R (M x v2)) (T (T (T h6 (h v1 v7 v0)) (C (R v0) (C (T (h v7 v0 z) (C h4 (S h6))) (R v1)))) (S (h v1 z v0)))))) (S (h v3 x v2))) h5) h4))) (S (h z (M v3 x) v2))) (S (h x v1 z))

@[equational_result]
theorem Equation3804_implies_Equation3588 (G: Type _) [Magma G] (h: Equation3804 G) : Equation3588 G := fun x y z =>
  let v0 := M x y
  let v1 := M v0 z
  let v2 := M z v0
  let v3 := M v0 v0
  have h4 := h x y y
  let v5 := M v0 v2
  have h6 := h x y x
  let v7 := M x x
  T (T (T (T (T (T h6 (h v0 v7 z)) (R (M (M z v7) v1))) (C (T (h z v7 v0) (C (S h6) (R v2))) (R v1))) (h v5 v1 v0)) (C (R (M v0 v1)) (T (T (C (R v5) (T (T h4 (h (M y y) v0 v0)) (C (R v3) (S h4)))) (S (h v3 v2 v0))) (S (h z v0 v0))))) (S (h z v1 v0))

@[equational_result]
theorem Equation4026_implies_Equation3553 (G: Type _) [Magma G] (h: Equation4026 G) : Equation3553 G := fun x y z =>
  let v0 := M x z
  let v1 := M v0 z
  have h2 := R y
  have h3 := R v1
  have h4 := h v0 z x
  have h5 := h x z x
  let v6 := M x v0
  have h7 := R v6
  have h8 := C h3 (T (h v1 x v6) (C (T (C h7 (S h5)) (S h4)) h3))
  let v9 := M x (M x y)
  T (T (T (T (T (T (T (T (T (h x y x) (h v9 x v1)) (C h8 (R v9))) (S (h v9 v1 v1))) (S (h v1 y x))) (C (T h4 (C h7 h5)) h2)) (S (h y x v6))) (h y x v1)) (C h8 h2)) (S (h y v1 v1))

@[equational_result]
theorem Equation1073_implies_Equation4332 (G: Type _) [Magma G] (h: Equation1073 G) : Equation4332 G := fun x y z =>
  let v0 := M z (M y z)
  let v1 := M v0 (M v0 v0)
  have h2 := h v0 v1
  have h3 := R x
  have h4 := R v0
  have h5 := R z
  let v6 := M y (M y y)
  have h7 := h y v6
  have h8 := S h7
  T (T (C h3 (C (T (T (T (T h7 (h (M v6 (M v6 v6)) v0)) (C h4 (C (T (T (T (C h8 (C h8 h8)) (h v6 z)) (C h5 (C h8 h5))) h2) h4))) (S (h v1 v0))) (C h2 (C h2 h2))) h3)) (S (h (M v1 (M v1 v1)) x))) (S h2)

@[equational_result]
theorem Equation2480_implies_Equation323 (G: Type _) [Magma G] (h: Equation2480 G) : Equation323 G := fun x y =>
  let v0 := M x y
  have h1 := R v0
  have h2 := h x v0 x
  have h3 := R x
  have h4 := h x y x
  have h5 := h v0 x (M (M y x) y)
  let v6 := M (M x v0) x
  have h7 := R y
  T (h v0 x v0) (C (T (T (T (C (C (T h2 (C (C h3 (T (C (C h1 h4) h1) (S h5))) h3)) (T (h y x (M (M x x) x)) (C (C h7 (S (h x x x))) h7))) (R v6)) (S (h v6 y x))) (C (C h3 (T h5 (C (C h1 (S h4)) h1))) h3)) (S h2)) h1)

@[equational_result]
theorem Equation3131_implies_Equation711 (G: Type _) [Magma G] (h: Equation3131 G) : Equation711 G := fun x y z =>
  let v0 := M x z
  let v1 := M v0 z
  let v2 := M y v1
  let v3 := M y v2
  have h4 := R v2
  have h5 := T (h y v3 y) (C (S (h v2 y y)) (R v3))
  have h6 := R v1
  T (T (T (T (T (h x z v1) (C (T (C (T (T (C (C (h z x z) (R x)) h6) (S (h z v1 x))) (h z v0 v0)) h6) (S (h v0 v1 v0))) (R z))) (h v1 v2 v2)) (C (C (T (C (C (C h5 h6) h6) h4) (S (h v3 v2 v1))) h4) h4)) (C (C (C h5 h4) h4) h4)) (S (h v3 v2 v2))

@[equational_result]
theorem Equation3131_implies_Equation725 (G: Type _) [Magma G] (h: Equation3131 G) : Equation725 G := fun x y z =>
  let v0 := M z x
  let v1 := M v0 z
  let v2 := M y v1
  let v3 := M y v2
  have h4 := R v2
  have h5 := R v3
  have h6 := T (h y v3 y) (C (S (h v2 y y)) h5)
  have h7 := R v1
  T (T (T (h x v2 v2) (C (C (T (T (C (C h4 (T (T (h x z v3) (C (C (C (T (h v0 v1 v0) (C (S (h z v0 v0)) h7)) h5) h5) (R z))) (S (h v1 z v3)))) h4) (C (C (C h6 h7) h7) h4)) (S (h v3 v2 v1))) h4) h4)) (C (C (C h6 h4) h4) h4)) (S (h v3 v2 v2))

@[equational_result]
theorem Equation3553_implies_Equation4026 (G: Type _) [Magma G] (h: Equation3553 G) : Equation4026 G := fun x y z =>
  let v0 := M z y
  let v1 := M z v0
  have h2 := R v1
  have h3 := h z v0 x
  let v4 := M (M z x) x
  have h5 := R v4
  have h6 := h z y x
  have h7 := C (T (h y v1 v4) (C h2 (T (C (S h6) h5) (S h3)))) h2
  have h8 := R x
  let v9 := M (M x x) x
  T (T (T (T (T (T (T (T (T (h x y x) (h y v9 v1)) (C (R v9) h7)) (S (h v1 v9 v1))) (S (h x v1 x))) (C h8 (T h3 (C h6 h5)))) (S (h y x v4))) (h y x v1)) (C h8 h7)) (S (h v1 x v1))

@[equational_result]
theorem Equation4176_implies_Equation3534 (G: Type _) [Magma G] (h: Equation4176 G) : Equation3534 G := fun x y z =>
  let v0 := M z y
  let v1 := M v0 z
  have h2 := R v1
  have h3 := S (h y v0 v0)
  have h4 := R v0
  have h5 := C (h v0 z y) h4
  let v6 := M z v1
  T (T (h x y v1) (C (C (T (T (T (T (h y v1 v0) (C (T (C (T (T h5 h3) (h y v0 z)) (R y)) (S (h z v1 y))) h4)) (h v6 v0 z)) (C (T (T (T (T (T (h v1 v6 v0) (C (S (h v0 z v1)) h4)) h5) h3) (h y v0 v1)) (C (S (h v1 z y)) h2)) (R z))) (S (h v1 v1 z))) (R x)) h2)) (S (h x v1 v1))

@[equational_result]
theorem Equation4176_implies_Equation3997 (G: Type _) [Magma G] (h: Equation4176 G) : Equation3997 G := fun x y z =>
  let v0 := M x z
  let v1 := M z v0
  let v2 := M v1 y
  have h3 := R z
  have h4 := R x
  let v5 := M x y
  have h6 := R v0
  T (T (h x y v2) (C (T (T (T (T (C (T (T (T (h y v2 v0) (C (S (h v0 v1 y)) h6)) (C (T (T (h v0 v1 x) (C (S (h x z v0)) h4)) (h v0 x y)) h6)) (S (h y v5 v0))) h4) (C (T (h y v5 z) (C (S (h z x y)) h3)) h4)) (S (h z z x))) (h z z v1)) (C (T (C (h z v1 y) h3) (S (h y v2 z))) (R v1))) (R v2))) (S (h v1 y v2))

@[equational_result]
theorem Equation1507_implies_Equation1504 (G: Type _) [Magma G] (h: Equation1507 G) : Equation1504 G := fun x y z =>
  let v0 := M y z
  let v1 := M z v0
  let v2 := M y x
  let v3 := M v2 v1
  let v4 := M v1 (M v1 v3)
  let v5 := M v1 (M v1 y)
  let v6 := M z (M z v2)
  T (T (T (T (T (h x y v1) (C (T (C (h y v2 z) (h x y v2)) (S (h v6 (M v2 y) v2))) (R v5))) (C (T (h v6 v3 v1) (C (S (h v1 v2 z)) (R v4))) (T (h v5 v0 z) (C (S (h z y v1)) (R (M z v1)))))) (S (h v4 v1 z))) (h v4 (M v3 v2) v3)) (C (S (h v2 v3 v1)) (S (h v1 v2 v3)))

@[equational_result]
theorem Equation2196_implies_Equation2199 (G: Type _) [Magma G] (h: Equation2196 G) : Equation2199 G := fun x y z =>
  let v0 := M y x
  let v1 := M (M y z) z
  let v2 := M v1 v0
  let v3 := M (M v0 v2) v2
  have h4 := h y x v2
  let v5 := M (M x v2) v2
  let v6 := M v0 x
  let v7 := M x y
  T (h x y z) (C (R v1) (T (T (T (T (h v7 y x) (C (R v6) (T (T (T (T (h (M v7 y) v0 x) (C (R (M v6 x)) (T (S (h y x y)) h4))) (S (h v5 v0 x))) (h v5 v0 v2)) (C (R v3) (S h4))))) (S (h v3 y x))) (h v3 (M x v0) v0)) (C (S (h y x v0)) (S (h x v0 v2)))))

@[equational_result]
theorem Equation3791_implies_Equation4229 (G: Type _) [Magma G] (h: Equation3791 G) : Equation4229 G := fun x y z =>
  let v0 := M z z
  let v1 := M v0 y
  have h2 := S (h v1 x y)
  let v3 := M x y
  have h4 := R v1
  have h5 := T (T (h y y v0) (C h4 (T (h y v0 v0) (C h4 (S (h z z z)))))) (S (h y v1 v0))
  have h6 := C h5 (R v3)
  let v7 := M v1 x
  let v8 := M y y
  T (T (T (T (T (T (h x y y) (h (M y x) v8 v3)) (C (S (h y y x)) (T h6 h2))) (h v8 v7 v8)) (C (S (h y y y)) (T (C (R v7) h5) (S (h x y v1))))) h6) h2

@[equational_result]
theorem Equation572_implies_Equation1670 (G: Type _) [Magma G] (h: Equation572 G) : Equation1670 G := fun x y z =>
  let v0 := M z y
  let v1 := M v0 z
  have h2 := R v1
  have h3 := T (C h2 (h v0 z z)) (S (h z v1 z))
  have h4 := R v0
  have h5 := R y
  have h6 := R z
  have h7 := R x
  let v8 := M x y
  T (h x v8 v0) (C (R v8) (C h4 (T (C h4 (C h7 (C h7 (T (h y z z) (C h6 (T (C h6 (T (T (T (C h6 (C h5 (T (h z y v1) (C h5 (C h2 h3))))) (S (h v1 z y))) (h v1 v0 v0)) (C h4 (C h4 (C h4 h3))))) (S (h v0 z v0)))))))) (S (h z v0 x)))))

@[equational_result]
theorem Equation1740_implies_Equation3906 (G: Type _) [Magma G] (h: Equation1740 G) : Equation3906 G := fun x y z =>
  let v0 := M z z
  let v1 := M (M y v0) y
  have h2 := R v0
  have h3 := C (h v0 z y) h2
  have h4 := C h2 (S (h v0 v1 y))
  have h5 := h v1 z v1
  have h6 := R (M y y)
  have h7 := S (h v1 x v0)
  let v8 := M x x
  T (T (T (h v8 y x) (C h6 (T (T (h (M (M x v8) x) x (M v0 v0)) (C (R v8) (T (T (T (T (C (S (h v8 v0 x)) h3) h7) h5) h4) h3))) h7))) (C h6 (T (T h5 h4) h3))) (S (h v1 y v0))

@[equational_result]
theorem Equation2171_implies_Equation2 (G: Type _) [Magma G] (h: Equation2171 G) : Equation2 G := fun x y =>
  let v0 := M x x
  let v1 := M y y
  let v2 := M v1 y
  have h3 := R (M v0 v0)
  let v4 := M x y
  have h5 := h v0 v0 v4
  have h6 := R (M v4 v4)
  have h7 := h v4 x x
  have h8 := h v4 x y
  have h9 := h v1 v4 v4
  T (T (T (h x (M v0 x) v0) (C (C (S (h x x x)) (R x)) h3)) (C (T (T (T (T h5 (C (S h7) h6)) (C h8 h6)) (S h9)) (C (T (h y y y) (C (R v2) (T (T (T h9 (C (S h8) h6)) (C h7 h6)) (S h5)))) (R y))) h3)) (S (h y v2 v0))

