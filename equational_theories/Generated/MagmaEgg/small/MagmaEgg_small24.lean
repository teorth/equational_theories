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
theorem Equation1507_implies_Equation4450 (G: Type _) [Magma G] (h: Equation1507 G) : Equation4450 G := fun x y z =>
  let v0 := M y z
  let v1 := M v0 z
  have h2 := S (h z v0 v1)
  let v3 := M y x
  let v4 := M x v3
  let v5 := M v1 v0
  let v6 := M v4 (M v4 v1)
  have h7 := R (M y v0)
  let v8 := M v1 v5
  have h9 := h z y v0
  have h10 := S h9
  have h11 := C h10 (R v8)
  let v12 := M v0 y
  let v13 := M v0 v12
  have h14 := h v13 v0 v1
  let v15 := M z v0
  let v16 := M z v15
  T (T (T (T (T (T (T (T (T (T (C (h x y v0) (T (C (h y v3 v0) (h x y v3)) (S (h (M v0 (M v0 v3)) (M v3 y) v3)))) (S (h v13 v3 v0))) h14) h11) (C (R z) (T (h v8 v12 v0) (C (S (h y v0 v1)) h10)))) (h v15 z y)) (C (T (T (h v16 z x) (C (T (T (T (C h9 (R v16)) (S (h v13 v0 z))) h14) h11) (R (M x (M x z))))) (S (h v8 z x))) h7)) (C (T (h v8 v1 v4) (C h2 (R v6))) h7)) (S (h v6 z y))) (h v6 v5 v1)) (C (S (h v0 v1 v4)) h2)

@[equational_result]
theorem Equation2944_implies_Equation4450 (G: Type _) [Magma G] (h: Equation2944 G) : Equation4450 G := fun x y z =>
  have h0 := R z
  have h1 := h y x y
  have h2 := S h1
  let v3 := M (M x (M x y)) y
  have h4 := R v3
  have h5 := C (C (T (C h4 h2) h2) h0) h0
  have h6 := h y v3 z
  let v7 := M y x
  have h8 := S (h y v3 v7)
  have h9 := R v7
  have h10 := T h1 (C h4 h1)
  have h11 := C (C h10 h9) h9
  let v12 := M x v7
  let v13 := M (M x (M x x)) x
  have h14 := h x v13 v12
  have h15 := R v12
  have h16 := h x x x
  have h17 := R v13
  have h18 := T (C (C h10 h0) h0) (S h6)
  have h19 := C (C h18 (C h18 (T (C (C (T h16 (C h17 h16)) h15) h15) (S h14)))) h9
  have h20 := S h16
  have h21 := C (C (T (C h17 h20) h20) h15) h15
  T (T (T (T (T (C (T (T (T h14 h21) (h (M (M x v12) v12) (M (M y z) z) v7)) (C (T (T (T (T h19 h11) h8) h6) h5) (C (T h6 h5) (T h14 h21)))) h9) h19) h11) h8) h6) h5

@[equational_result]
theorem Equation1507_implies_Equation3553 (G: Type _) [Magma G] (h: Equation1507 G) : Equation3553 G := fun x y z =>
  let v0 := M x z
  let v1 := M v0 z
  let v2 := M y v1
  let v3 := M x y
  let v4 := M x v3
  have h5 := R v4
  let v6 := M y v2
  have h7 := R (M x v0)
  let v8 := M v2 (M v2 v0)
  let v9 := M v2 (M v2 x)
  have h10 := h v9 v3 x
  let v11 := M x v4
  have h12 := R v11
  have h13 := h y x v2
  let v14 := M z x
  let v15 := M v1 (M v1 v3)
  T (T (T (T (T (T (C (h x v3 v1) (h y x v3)) (S (h v15 (M v3 x) v3))) (h v15 y x)) (C (T (T (T (C h13 (R v15)) (S (h v9 v3 v1))) h10) (C (S h13) h12)) h5)) (S (h v11 y x))) (C (T (T (h x z x) (C (T (T (T (T (h v14 z x) (C (T (T (T (T (h (M z v14) v3 x) (C (T (S (h y x z)) h13) h12)) (S h10)) (h v9 v0 v2)) (C (S (h z x v2)) (R v8))) h7)) (S (h v8 z x))) (h v8 v1 y)) (C (S (h z v0 v2)) (R v6))) h7)) (S (h v6 z x))) h5)) (S (h v2 y x))

@[equational_result]
theorem Equation2196_implies_Equation4421 (G: Type _) [Magma G] (h: Equation2196 G) : Equation4421 G := fun x y z =>
  let v0 := M z y
  let v1 := M (M v0 v0) v0
  let v2 := M v0 z
  let v3 := M (M y v2) v2
  let v4 := M x y
  have h5 := h x y v2
  let v6 := M (M v4 v0) v0
  let v7 := M v4 x
  let v8 := M v7 x
  let v9 := M (M v4 z) z
  let v10 := M x v4
  have h11 := h x v4 v0
  let v12 := M (M v10 v10) v10
  T (T (T (T (T (T (T (T (T (C (h x v4 v10) (h v4 v10 v10)) (S (h v12 (M v4 v10) v10))) (h v12 x v4)) (C (R (M v10 v4)) (T (T (T (T (T (T (T (C (R v12) h11) (S (h v6 v10 v10))) (h v6 v10 x)) (C (R (M (M v10 x) x)) (T (S h11) (h x v4 z)))) (S (h v9 v10 x))) (h v9 x x)) (C (R (M (M x x) x)) (T (T (T (C (R v9) h5) (S (h v3 v4 z))) (h v3 v4 x)) (C (R v8) (S h5))))) (S (h v8 x x))))) (S (h v7 x v4))) (C (T (C (h x y v4) (h y v4 v0)) (S (h v6 (M y v4) v4))) h5)) (S (h v3 v4 v0))) (h v3 v0 v0)) (C (R v1) (S (h z y v2)))) (C (T (h v1 (M y v0) v0) (C (S (h z y v0)) (S (h y v0 v0)))) (R z))

@[equational_result]
theorem Equation2956_implies_Equation1478 (G: Type _) [Magma G] (h: Equation2956 G) : Equation1478 G := fun x y =>
  let v0 := M x x
  let v1 := M x v0
  let v2 := M v1 y
  have h3 := h x v2 y
  have h4 := R x
  have h5 := h y x x
  have h6 := R v2
  let v7 := M (M x (M x v1)) y
  have h8 := S (h x v7 y)
  have h9 := h y x v1
  have h10 := C (C (T h9 (C (R v7) h9)) h4) h4
  let v11 := M y x
  have h12 := R v11
  have h13 := S (h v11 y x)
  have h14 := S h5
  have h15 := T (C h6 h14) h14
  have h16 := C (T (h v11 v2 y) (C (C h15 h12) h12)) h12
  have h17 := T (T (C h12 (T h16 h13)) h16) h13
  have h18 := h x v11 v11
  have h19 := S (h y v0 y)
  let v20 := M (M v0 (M v0 y)) y
  T (h x v20 y) (C (C (T (C (R v20) h19) h19) h4) (T (T h18 (C (C h17 (T h3 (C (C h15 h4) h4))) (T h18 (C (T (T (C h17 h4) h10) h8) h4)))) (C (T (T (C h12 (T h10 h8)) (C (C (T h5 (C h6 h5)) h4) h4)) (S h3)) (R v0))))

@[equational_result]
theorem Equation952_implies_Equation11 (G: Type _) [Magma G] (h: Equation952 G) : Equation11 G := fun x y =>
  let v0 := M y y
  let v1 := M x v0
  have h2 := h v1 v1 x
  let v3 := M x v1
  have h4 := h v0 v1 y
  have h5 := R v1
  have h6 := C h5 (T (C (S h4) (R (M v1 v1))) (S (h v0 v0 x)))
  let v7 := M y v1
  let v8 := M y v0
  have h9 := h (M v8 v7) v1 v1
  have h10 := R v0
  let v11 := M v0 v0
  have h12 := h y y y
  have h13 := S (h v8 x v0)
  have h14 := C (R x) (C (T (C h10 (T h12 (C (h y v0 y) (R v11)))) (S (h (M v0 v8) v0 v0))) (R (M v0 x)))
  have h15 := h y x v0
  have h16 := R y
  have h17 := h x y v1
  T (T (T (T (T (T (T h17 (C h16 (T (h (M (M v1 x) (M v1 y)) y y) (C h16 (C (S h17) h10))))) (C (T (T h15 h14) h13) (R v7))) h9) h6) (C h5 (T (C h16 (T (T (T h15 h14) h13) (C h12 h10))) (S (h v11 y y))))) (C h5 (T (C h10 (T h4 (C h2 (T h9 h6)))) (S (h (M v3 v3) v0 v1))))) (S h2)

@[equational_result]
theorem Equation3398_implies_Equation4007 (G: Type _) [Magma G] (h: Equation3398 G) : Equation4007 G := fun x y z =>
  let v0 := M y x
  let v1 := M z v0
  let v2 := M v1 z
  have h3 := R v2
  have h4 := R z
  have h5 := S (h z v1 x)
  have h6 := R v1
  have h7 := C (R x) (T (h x v0 v1) (C h6 (S (h z x v0))))
  have h8 := h y x x
  have h9 := R v0
  have h10 := R y
  T (T (T (T (h x y v2) (h v2 (M y (M x v2)) v2)) (C h3 (C (T (T (C h10 (T (h x v2 v1) (C h6 (T (T (C h3 (S (h y z x))) (C h3 (T (h y z y) (C h10 (T (T (C h4 (T (T (h y y v1) (C h6 (T (T (C h10 (T (h y v1 v0) (C h9 (T (C h6 (T (h y v0 y) (C h10 (T (T (T (T (C h9 (h y y x)) (S (h y x v0))) h8) h7) h5)))) (S (h z y v1)))))) (S (h z v0 y))) (C h4 (T (T h8 h7) h5))))) (S (h z z v1)))) (C h4 (T (h z z v2) (C h3 (S (h v1 z z)))))) (S (h v1 v2 z))))))) (S (h v1 y v2)))))) (S (h v1 v1 y))) (h v1 v1 z)) (R (M v2 v2))))) (S (h v2 (M z (M v1 v2)) v2))) (S (h v1 z v2))

@[equational_result]
theorem Equation1507_implies_Equation2573 (G: Type _) [Magma G] (h: Equation1507 G) : Equation2573 G := fun x y z =>
  let v0 := M z x
  let v1 := M v0 y
  let v2 := M y v1
  let v3 := M v2 z
  have h4 := h v2 v3 z
  let v5 := M v3 v2
  let v6 := M z (M z v3)
  let v7 := M v2 v3
  let v8 := M v2 v7
  let v9 := M v2 y
  let v10 := M v0 (M v0 v0)
  have h11 := h x z v2
  let v12 := M v3 v0
  let v13 := M v3 v12
  T (T (T (T (T (T h11 (C (T (T (h v0 v3 v0) (C (T (T (h v12 v3 v2) (C (T (T (T (T (T (h v13 x x) (C (T (T (T (C h11 (R v13)) (S (h v7 v0 v3))) (h v7 v0 v0)) (C (S h11) (R v10))) (R (M x (M x x))))) (S (h v10 x x))) (h v10 v9 v2)) (C (T (T (C (R v9) (T (h v10 v1 y) (C (S (h y v0 v0)) (R (M y v2))))) (S (h y v2 y))) (h y v2 v3)) (R (M v2 (M v2 v9))))) (S (h (M v3 v5) v9 v2))) (R v8))) (S (h v5 v3 v2))) (R (M v0 (M v0 v3))))) (S (h v2 v3 v0))) (R v7))) (h v8 v5 v6)) (C (T (S (h v2 v3 v2)) h4) (R (M v6 (M v6 v5))))) (S (h v6 v5 v6))) (h v6 v5 v3)) (C (S h4) (S (h z v2 v3)))

@[equational_result]
theorem Equation1507_implies_Equation4182 (G: Type _) [Magma G] (h: Equation1507 G) : Equation4182 G := fun x y z =>
  let v0 := M y z
  let v1 := M v0 z
  let v2 := M v1 x
  let v3 := M v1 v2
  let v4 := M y (M y v1)
  have h5 := h z v0 v0
  let v6 := M v0 (M v0 v0)
  have h7 := R (M x (M x v1))
  let v8 := M z v0
  have h9 := h z y v2
  let v10 := M v2 (M v2 y)
  have h11 := R (M x (M x v0))
  let v12 := M x y
  T (T (T (h v12 x v1) (C (T (T (T (T (T (T (T (T (T (T (T (h (M x v12) v0 x) (C (S (h z y x)) h11)) (C h9 h11)) (S (h v10 v0 x))) (h v10 v0 v0)) (C (S h9) (R v6))) (C (R z) (T (h v6 (M v0 y) v0) (C (S (h y v0 v0)) (S (h z y v0)))))) (h v8 z x)) (C (T (T (T (T (T (h (M z v8) v1 x) (C (S (h z v0 z)) h7)) (C h5 h7)) (S (h v6 v1 x))) (h v6 v1 y)) (C (S h5) (R v4))) (R (M x (M x z))))) (S (h v4 z x))) (h v4 (M v1 v0) v1)) (C (S (h v0 v1 y)) (S (h z v0 v1)))) (R v3))) (h (M v1 v3) (M v2 v1) v2)) (C (S (h v1 v2 v1)) (S (h x v1 v2)))

@[equational_result]
theorem Equation3211_implies_Equation1983 (G: Type _) [Magma G] (h: Equation3211 G) : Equation1983 G := fun x y z =>
  let v0 := M z y
  let v1 := M y v0
  let v2 := M z x
  let v3 := M v1 v2
  have h4 := R v1
  have h5 := R v3
  have h6 := R y
  have h7 := R v0
  have h8 := h y z y
  have h9 := C (S h8) h7
  have h10 := h z v0 y
  have h11 := h z v2 x
  have h12 := S h11
  have h13 := R v2
  have h14 := h x z x
  have h15 := R x
  have h16 := C (T (T (T (C h8 h7) (S h10)) h11) (C (S h14) h13)) h13
  have h17 := C (T (T (C (C h16 h15) h15) (S (h x x v2))) h14) h13
  have h18 := h v2 v3 x
  T (T (h x v1 v2) (C (T (T (T (C (C h16 h13) h15) (S (h v2 x v2))) h18) (C (T (T (T (T (T h17 h12) h10) h9) (h v1 y v0)) (C (T (T (T (C (C (T (h v1 v3 v2) (C (T (T (S (h v2 v1 v2)) h18) (C (T (T (T h17 h12) h10) h9) h5)) h5)) h7) h4) (S (h v0 v1 v3))) (h v0 y v1)) (C (T (C (C (C (T (h y v1 v0) (C (S (h v0 y v0)) h4)) h4) h4) h7) (S (h v1 v0 v1))) h6)) h6)) h5)) h4)) (S (h v3 v1 y))

@[equational_result]
theorem Equation3211_implies_Equation2335 (G: Type _) [Magma G] (h: Equation3211 G) : Equation2335 G := fun x y z =>
  have h0 := R z
  let v1 := M x z
  let v2 := M y v1
  let v3 := M y v2
  have h4 := R x
  have h5 := R v3
  have h6 := R y
  have h7 := R v2
  have h8 := h y v2 v1
  have h9 := S h8
  have h10 := h v1 y v1
  have h11 := h v1 v1 v2
  have h12 := R v1
  have h13 := S h10
  have h14 := h v2 v3 v1
  have h15 := h v2 y v2
  have h16 := h y v3 v2
  T (h x z v3) (C (T (C (C (C (T (h z v3 x) (C (T (C (C (C (T (h v3 x z) (C (T (C (C (T (h v1 y v3) (C (T (T (C (T (T (C (T (C (T h8 (C (T (T h13 h11) (C (C (C (T (C h10 h7) h9) h7) h12) h12)) h7)) h5) (S h14)) h5) (C h15 h5)) (S h16)) h12) (h v2 y y)) (C (C (T (C (C (T (T h16 (C (S h15) h5)) (C (T h14 (C (T (C (T (T (C (C (C (T h8 (C h13 h7)) h7) h12) h12) (S h11)) h10) h7) h9) h5)) h5)) h6) h6) (S (h y y v3))) h7) h6)) h6)) h0) h5) (S (h z v3 y))) h4)) h4) h4) h0) (S (h x z x))) h5)) h5) h5) h4) (S (h v3 x v3))) h0)

@[equational_result]
theorem Equation2958_implies_Equation1561 (G: Type _) [Magma G] (h: Equation2958 G) : Equation1561 G := fun x y z =>
  let v0 := M y z
  let v1 := M z y
  let v2 := M x v1
  let v3 := M v0 v2
  have h4 := R z
  let v5 := M (M x (M x z)) z
  have h6 := h z x z
  let v7 := M (M x v2) v1
  let v8 := M v1 z
  have h9 := R v1
  have h10 := h v1 x v1
  let v11 := M v3 v0
  have h12 := S (h v3 x v3)
  let v13 := M (M x (M x v3)) v3
  have h14 := R v2
  have h15 := S (h v0 x v0)
  let v16 := M (M x (M x v0)) v0
  let v17 := M (M x (M x x)) x
  have h18 := h x x x
  T (T (T (h x x v1) (C (T (C (C (T h18 (C (R v17) h18)) h14) (R x)) (S (h v2 v17 x))) h9)) (C (T (T (T (h v2 v16 v0) (C (C (T (C (R v16) h15) h15) h14) (R v0))) (h v11 v13 v3)) (C (C (T (C (R v13) h12) h12) (R v11)) (R v3))) (T (h v1 v1 z) (C (T (T (T (C (C (T h10 (C (R v7) h10)) (R v8)) h9) (S (h v8 v7 v1))) (C (C (T h6 (C (R v5) h6)) (R y)) h4)) (S (h y v5 z))) h4)))) (S (h v3 v3 v0))

@[equational_result]
theorem Equation2958_implies_Equation4013 (G: Type _) [Magma G] (h: Equation2958 G) : Equation4013 G := fun x y z =>
  let v0 := M y z
  let v1 := M z v0
  let v2 := M v1 x
  have h3 := R v1
  let v4 := M v2 v1
  have h5 := S (h v2 x v2)
  let v6 := M (M x (M x v2)) v2
  have h7 := R x
  have h8 := S (h v1 x v1)
  let v9 := M (M x (M x v1)) v1
  have h10 := R v0
  let v11 := M (M x (M x v0)) v0
  have h12 := R z
  have h13 := h v0 x v0
  let v14 := M (M x (M x y)) y
  have h15 := R y
  have h16 := h y x y
  have h17 := T h16 (C (R v14) h16)
  let v18 := M y v0
  T (T (C h7 (T (T (h y y v0) (C (T (C (C h17 (R v18)) h15) (S (h v18 v14 y))) h10)) (C (T (C (T (T (h y y z) (C (T (C (C h17 h10) h15) (S (h v0 v14 y))) h12)) (C (T h13 (C (R v11) h13)) h12)) h10) (S (h z v11 v0))) h10))) (C (T (T (T (h x v9 v1) (C (C (T (C (R v9) h8) h8) h7) h3)) (h v4 v6 v2)) (C (C (T (C (R v6) h5) h5) (R v4)) (R v2))) h3)) (S (h v2 v2 v1))

@[equational_result]
theorem Equation3404_implies_Equation4098 (G: Type _) [Magma G] (h: Equation3404 G) : Equation4098 G := fun x y z =>
  let v0 := M y y
  let v1 := M v0 z
  have h2 := h v0 z z
  let v3 := M z (M z v0)
  let v4 := M v1 z
  have h5 := R x
  have h6 := R z
  have h7 := h x x z
  have h8 := R v1
  let v9 := M x (M z x)
  have h10 := R y
  let v11 := M x x
  let v12 := M v11 y
  have h13 := S (h y y y)
  have h14 := C h10 (T (h v0 y y) (C h10 h13))
  have h15 := C h10 (T (C h5 (h y x y)) (S (h v0 y x)))
  have h16 := h x x y
  T (T (T (T (T (T h16 h15) h14) (C h10 (T (T (C h10 (h y y v11)) (S (h v12 v11 y))) (C (R v12) (T (T (T h16 h15) h14) h13))))) (S (h y v12 y))) (C h10 (T (h v11 y z) (C h6 (T (C h10 (T (C h6 (T (T h7 (h z v9 v0)) (C (R v0) (T (h v9 v1 z) (C h6 (T (T (T (C h8 (S h7)) (C h8 (T (T h7 (C h6 (T (T (C h5 (h z x v1)) (S (h v4 v1 x))) (C (R v4) h2)))) (S (h v3 v4 z))))) (S (h z v3 v1))) (S h2))))))) (S (h v1 v0 z)))) (S (h y v1 y))))))) (S (h v1 z y))

@[equational_result]
theorem Equation2958_implies_Equation1171 (G: Type _) [Magma G] (h: Equation2958 G) : Equation1171 G := fun x y z =>
  let v0 := M y z
  let v1 := M z v0
  let v2 := M v1 x
  have h3 := R v2
  have h4 := R z
  have h5 := R v0
  have h6 := S (h y x y)
  let v7 := M (M x (M x y)) y
  let v8 := M (M x (M x z)) z
  have h9 := h z x z
  let v10 := M (M x (M x v1)) v1
  let v11 := M v1 z
  have h12 := R v1
  have h13 := h v1 x v1
  have h14 := R v10
  have h15 := S h13
  let v16 := M y v2
  have h17 := S (h v2 v16 v2)
  let v18 := M (M v16 (M v16 v2)) v2
  T (h x v18 v2) (C (T (T (T (T (C (T (T (T (C (R v18) h17) h17) (h v2 v10 v1)) (C (C (T (C h14 h15) h15) h3) h12)) (R x)) (S (h v1 v1 x))) (h v1 v1 z)) (C (T (T (T (T (T (C (C (T h13 (C h14 h13)) (R v11)) h12) (S (h v11 v10 v1))) (C (C (T h9 (C (R v8) h9)) h5) h4)) (S (h v0 v8 z))) (h v0 v7 y)) (C (C (T (C (R v7) h6) h6) h5) (R y))) h4)) (S (h y y z))) h3)

@[equational_result]
theorem Equation3211_implies_Equation1699 (G: Type _) [Magma G] (h: Equation3211 G) : Equation1699 G := fun x y z =>
  let v0 := M y z
  let v1 := M v0 z
  let v2 := M y x
  let v3 := M v2 v1
  have h4 := R y
  have h5 := R z
  have h6 := h v0 y z
  have h7 := R v0
  have h8 := h v0 v0 z
  have h9 := h v1 v0 v1
  have h10 := R v1
  have h11 := h y y z
  have h12 := h z v1 y
  have h13 := h v0 z v1
  have h14 := h z v0 v0
  have h15 := S h13
  have h16 := C (T h9 (C (C (C (T (C (C h11 h5) h10) (S h12)) h10) h10) h7)) h5
  T (T (T (h x y y) (C (C (T (C (C h11 h4) (T (h y z z) (C (T (C (T (T (T (C (C (T (h z y z) (C (T (T (T h16 h15) h6) (C (T (C (C (T h8 (C (C (T h16 h15) h7) h7)) h5) h7) (S h14)) h4)) h4)) h5) h5) (S (h z z y))) h14) (C (C (T (C (C (T h13 (C (T (C (C (C (T h12 (C (C (S h11) h5) h10)) h10) h10) h7) (S h9)) h5)) h7) h7) (S h8)) h5) h7)) h4) (S h6)) h5))) (S (h y v1 y))) (R x)) h4)) (C (T (h v2 v3 v1) (C (S (h v1 v2 v1)) (R v3))) h4)) (S (h v3 y z))

@[equational_result]
theorem Equation2370_implies_Equation3128 (G: Type _) [Magma G] (h: Equation2370 G) : Equation3128 G := fun x y z =>
  have h0 := R z
  let v1 := M y x
  let v2 := M v1 z
  let v3 := M v2 y
  have h4 := h y v3 x
  have h5 := R x
  have h6 := h y v2 x
  have h7 := S h6
  let v8 := M v2 (M x (M y v2))
  have h9 := h v8 x x
  let v10 := M v3 z
  have h11 := h v8 x v10
  have h12 := R v10
  let v13 := M z (M x v2)
  have h14 := h x v1 z
  have h15 := h x v10 z
  T h15 (C (T (T (T (T (h (M v10 (M z (M x v10))) z x) (C (T (C h0 (C h5 (S h15))) (C h0 (C h5 h14))) h5)) (C (T (C h0 (C h5 (S h14))) (C h0 (C h5 (h x v2 z)))) h5)) (S (h (M v2 v13) z x))) (C (R v2) (T (T (T (h v13 x x) (C (T (T (T (T (T (C h5 (C h5 (S (h v1 z x)))) (h (M x (M x v1)) x x)) (C (T (C h5 (C h5 (S (h y x x)))) (C h5 (C h5 h6))) h5)) (S h9)) h11) (C (C h5 (C h12 h7)) h12)) h5)) (C (T (T (T (T (C (C h5 (C h12 h6)) h12) (S h11)) h9) (C (T (C h5 (C h5 h7)) (C h5 (C h5 h4))) h5)) (S (h (M v3 (M x (M y v3))) x x))) h5)) (S h4)))) h0)

@[equational_result]
theorem Equation3211_implies_Equation2186 (G: Type _) [Magma G] (h: Equation3211 G) : Equation2186 G := fun x y z =>
  let v0 := M z x
  let v1 := M y z
  let v2 := M v1 y
  let v3 := M v2 v0
  have h4 := R v3
  have h5 := R y
  have h6 := h v1 z v1
  have h7 := R z
  have h8 := R v1
  have h9 := h z y z
  have h10 := h y v1 z
  have h11 := C (T (C (C (C (T h10 (C (S h9) h8)) h8) h8) h7) (S h6)) h5
  have h12 := h z y v1
  have h13 := h z v0 x
  have h14 := S h13
  have h15 := R v0
  have h16 := h x z x
  have h17 := R x
  have h18 := C (T (T (T (C (T h6 (C (C (C (T (C h9 h8) (S h10)) h8) h8) h7)) h5) (S h12)) h13) (C (S h16) h15)) h15
  have h19 := C (T (T (C (C h18 h17) h17) (S (h x x v0))) h16) h15
  have h20 := h v0 v3 x
  T (T (h x v2 v0) (C (T (T (T (C (C h18 h15) h17) (S (h v0 x v0))) h20) (C (T (T (T (T (T h19 h14) h12) h11) (h v2 v3 v0)) (C (T (T (S (h v0 v2 v0)) h20) (C (T (T (T h19 h14) h12) h11) h4)) h4)) h4)) (R v2))) (S (h v3 v2 v3))

@[equational_result]
theorem Equation1993_implies_Equation3161 (G: Type _) [Magma G] (h: Equation1993 G) : Equation3161 G := fun x y z =>
  let v0 := M y y
  let v1 := M v0 z
  let v2 := M v1 x
  let v3 := M v2 z
  let v4 := M v3 v0
  let v5 := M x x
  let v6 := M z v5
  have h7 := h v0 z x
  have h8 := R (M v0 v5)
  have h9 := S (h y y v2)
  let v10 := M v2 v2
  let v11 := M y v10
  let v12 := M v0 v10
  have h13 := R v12
  let v14 := M v1 v10
  let v15 := M v1 v0
  T (T (h x v0 x) (C h8 (T (T (h (M x v0) v2 x) (C (R (M v2 v5)) (T (T (T (T (T (S (h v1 x y)) (h v1 v1 v1)) (C (R (M v1 (M v1 v1))) (T (T (T (T (C (h v1 v1 v2) (T (h v1 v0 v2) (C h13 (T (T (h v15 v0 x) (C h8 (T (T (T (C (R v15) h7) (S (h v6 v1 y))) (h v6 v1 v2)) (C (R v14) (S h7))))) (S (h v14 v0 x)))))) (S (h v12 v14 v1))) (h v12 v11 y)) (C h9 (T (C h13 (T (T (T (h v11 v0 x) (C h8 h9)) (C h8 (h y y y))) (S (h (M y v0) v0 x)))) (S (h y v0 v2))))) h7))) (S (h v6 v1 v1))) (h v6 v3 y)) (C (R v4) (S (h v2 z x)))))) (S (h v4 v2 x))))) (S (h v3 v0 x))

@[equational_result]
theorem Equation684_implies_Equation4162 (G: Type _) [Magma G] (h: Equation684 G) : Equation4162 G := fun x y z =>
  let v0 := M y x
  have h1 := h z z x
  have h2 := S h1
  let v3 := M z (M (M z x) x)
  have h4 := R v3
  let v5 := M v0 z
  have h6 := R v5
  have h7 := R z
  have h8 := R v0
  have h9 := S (h v5 v5 x)
  let v10 := M v5 (M (M v5 x) x)
  let v11 := M x y
  have h12 := S (h z z v11)
  let v13 := M z (M (M z v11) v11)
  let v14 := M y (M v0 x)
  have h15 := h y y x
  have h16 := R y
  let v17 := M v11 (M (M v11 x) x)
  let v18 := M y v11
  have h19 := h v11 v11 x
  T (T (T (T (T (h v11 y v11) (C h16 (T (T (T (C (R v11) (C (R v18) (T h19 (C h19 (R v17))))) (S (h v18 v11 v17))) (C h16 (C (R x) (T h15 (C h15 (R v14)))))) (S (h x y v14))))) (h v0 z v13)) (C h7 (C h8 (T (C h12 (R v13)) h12)))) (h (M z v5) v5 v10)) (C h6 (T (T (C (T (C h7 (C h8 (T h1 (C h1 h4)))) (S (h v0 z v3))) (T (C h9 (R v10)) h9)) (C h8 (T (h v5 z v3) (C h7 (C h6 (T (C h2 h4) h2)))))) (S (h z v0 z))))

@[equational_result]
theorem Equation2779_implies_Equation31 (G: Type _) [Magma G] (h: Equation2779 G) : Equation31 G := fun x y =>
  let v0 := M y y
  let v1 := M v0 x
  have h2 := h v1 v1 x
  have h3 := R v1
  let v4 := M v1 x
  have h5 := R v0
  have h6 := h v0 v1 y
  have h7 := C (T (C (R (M v1 v1)) (S h6)) (S (h v0 v0 x))) h3
  let v8 := M v0 y
  let v9 := M v1 y
  have h10 := h (M v9 v8) v1 v1
  let v11 := M v0 v0
  have h12 := R y
  have h13 := h y y y
  have h14 := S (h v8 x v0)
  have h15 := C (C (R (M x v0)) (T (C (T h13 (C (R v11) (h y v0 y))) h5) (S (h (M v8 v0) v0 v0)))) (R x)
  have h16 := h y x v0
  have h17 := h x y v1
  T (T (T (T (T (T (T h17 (C (T (h (M (M y v1) (M x v1)) y y) (C (C h5 (S h17)) h12)) h12)) (C (R v9) (T (T h16 h15) h14))) h10) h7) (C (T (C (T (T (T h16 h15) h14) (C h5 h13)) h12) (S (h v11 y y))) h3)) (C (T (C (T h6 (C (T h10 h7) h2)) h5) (S (h (M v4 v4) v0 v1))) h3)) (S h2)

@[equational_result]
theorem Equation2956_implies_Equation218 (G: Type _) [Magma G] (h: Equation2956 G) : Equation218 G := fun x y =>
  let v0 := M x x
  have h1 := h x v0 v0
  have h2 := R x
  have h3 := R v0
  let v4 := M x v0
  let v5 := M v4 x
  have h6 := h v0 v5 x
  have h7 := h x x x
  have h8 := R v5
  have h9 := T h7 (C h8 h7)
  have h10 := C (T (C (C h9 h3) h3) (S h6)) h3
  have h11 := h v0 x x
  have h12 := h x v5 x
  have h13 := S h12
  have h14 := C (C h9 h2) h2
  have h15 := h x v0 x
  have h16 := S (h y x x)
  let v17 := M v4 y
  have h18 := S h7
  have h19 := T (C h8 h18) h18
  have h20 := C (C h19 h2) h2
  have h21 := S h11
  have h22 := C (T h6 (C (C h19 h3) h3)) h3
  T (T (T (T h1 (C (T (C (T (T (T (C h3 (T h22 h21)) h22) h21) (C (T (T h12 h20) (C h3 (T h12 h20))) h2)) h2) (S h15)) h2)) (h v0 v17 y)) (C (C (T (C (R v17) h16) h16) h3) h3)) (C (R (M y v0)) (T (C (T h15 (C (T (T (T (C (T (T (C h3 (T h14 h13)) h14) h13) h2) h11) h10) (C h3 (T h11 h10))) h2)) h2) (S h1)))

@[equational_result]
theorem Equation3195_implies_Equation4458 (G: Type _) [Magma G] (h: Equation3195 G) : Equation4458 G := fun x y z =>
  have h0 := R z
  let v1 := M z y
  have h2 := S (h v1 z y)
  have h3 := h y v1 z
  let v4 := M y x
  have h5 := R v4
  have h6 := R y
  have h7 := R v1
  let v8 := M x v4
  have h9 := R v8
  T (T (T (C (T (T (h x v4 y) (C (S (h v4 y x)) h6)) (C (T (h v4 y v1) (C (C (C (T (C (T h3 (C (T (T h2 (h v1 v4 v4)) (C (C (T (C (C (T (h v4 v1 y) (C (C (T (C (C (T (h v1 v1 v8) (C (C (T (C (C (T (h v1 v4 z) (C (C (T (C (C (T (h v4 v4 v8) (C (C (T (C (C (T (h v4 z z) (C (C (T (C (C (T (h z z v8) (C (C (T (C (C (T (h z y y) (C (C (T (C (C (T (h y v8 v8) (C (C (T (C (C (T (h v8 v4 y) (C (C (T (C (C (T (h v4 v8 x) (C (S (h v8 x v4)) (R x))) h6) h5) (S (h y x v4))) h9) h6)) h9) h9) (S (h v8 y v8))) h6) h9)) h6) h6) (S (h y v8 y))) h0) h6)) h9) h0) (S (h v8 y z))) h0) h9)) h0) h0) (S (h z v8 z))) h5) h0)) h9) h5) (S (h v8 z v4))) h5) h9)) h0) h5) (S (h z v8 v4))) h7) h0)) h9) h7) (S (h v8 z v1))) h7) h9)) h6) h7) (S (h y v8 v1))) h5) h6)) h5) h5) (S (h v4 y v4))) h7) h5)) h0)) h7) (S (h z v4 v1))) h6) h5) h7)) h6)) h5) (S (h y v1 v4))) h3) (C h2 h0)

@[equational_result]
theorem Equation4176_implies_Equation4421 (G: Type _) [Magma G] (h: Equation4176 G) : Equation4421 G := fun x y z =>
  have h0 := R z
  let v1 := M z y
  have h2 := S (h z y v1)
  have h3 := R v1
  let v4 := M v1 z
  have h5 := R x
  let v6 := M y v1
  let v7 := M x y
  let v8 := M v7 v7
  have h9 := R y
  let v10 := M y x
  have h11 := h x y v7
  let v12 := M y v7
  T (T (h x v7 z) (C (T (C (C (T (T h11 (h (M v12 x) v7 x)) (C (T (T (T (C (T (h v7 x y) (h v8 y v1)) (T (T (T (T (T (T (T (h v12 x y) (C (T (h v7 v12 x) (C (S h11) h5)) h9)) (C (T (T (T (C (h x y x) h5) (S (h x v10 x))) (h x v10 z)) (C (S (h z y x)) h0)) h9)) (S (h z z y))) (h z z v1)) (C (T (C (h z v1 z) h0) (S (h z v4 z))) h3)) (C (T (h z v4 v7) (C (S (h v7 v1 z)) (R v7))) h3)) (S (h v7 v7 v1)))) (S (h v1 v6 v8))) (h v1 v6 z)) (C h2 h0)) h5)) h0) h5) (S (h z v4 x))) h0)) (C (T (T (h z v4 v1) (C (C (T (C (h v1 z y) h3) (S (h y v1 v1))) h0) h3)) h2) h0)

@[equational_result]
theorem Equation492_implies_Equation1304 (G: Type _) [Magma G] (h: Equation492 G) : Equation1304 G := fun x y z =>
  let v0 := M x z
  let v1 := M v0 z
  let v2 := M v1 y
  let v3 := M y v2
  have h4 := h z v0 x
  have h5 := S h4
  have h6 := h x z x
  have h7 := R v0
  have h8 := C h7 h6
  have h9 := h x z v0
  have h10 := R x
  have h11 := h v0 x v0
  have h12 := h z v1 v0
  have h13 := h v0 z v0
  have h14 := R v1
  have h15 := S (h v1 y v2)
  have h16 := R v2
  have h17 := C (R y) (T (h v2 v1 v2) (C h14 (C h16 (C h16 (T (C h16 (h v1 y v1)) (S (h y v2 v1)))))))
  have h18 := R z
  have h19 := C h7 (T (C h18 (T (T (T (C h18 (T (T (T h17 h15) (h v1 v0 v1)) (C h7 (C h14 (C h14 (T (C h14 h13) (S h12))))))) (S (h v0 z v1))) h11) (C h10 (C h7 (C h7 (T h8 h5)))))) (S h9))
  have h20 := h v0 v3 z
  T (T (T h9 (C h18 (T (C h10 (C h7 (C h7 (T h4 (C h7 (S h6)))))) (S h11)))) (C h18 (T h20 (C (R v3) (T (T (T (T h19 h8) h5) h12) (C h14 (T (T (S h13) h20) (C (T h17 h15) (T (T h19 h8) h5))))))))) (S (h v3 z v1))

@[equational_result]
theorem Equation2927_implies_Equation5 (G: Type _) [Magma G] (h: Equation2927 G) : Equation5 G := fun x y =>
  have h0 := R x
  let v1 := M y x
  have h2 := h y (M x (M x v1)) x
  have h3 := S h2
  have h4 := R y
  have h5 := h x x v1
  have h6 := C h5 h4
  have h7 := T h6 h3
  have h8 := C (S h5) h4
  have h9 := h y v1 y
  have h10 := S h9
  have h11 := T (T (C h0 h10) h6) h3
  have h12 := C h11 h4
  have h13 := T (T h2 h8) (C h0 h9)
  have h14 := C h13 h7
  have h15 := T h2 h8
  have h16 := C h11 h15
  have h17 := C h13 h4
  have h18 := C h4 h10
  have h19 := C h4 h9
  T (T (h x (M y y) y) (C (T (T (T (T (C (T (C h19 h7) (C (T (T h18 h17) h16) h4)) h4) (C (T (C (T (T h14 h12) h19) h4) (C (T (T (T (T (T h18 h17) h16) (C (T (T h2 h8) (C h0 h15)) h7)) (h (M (M x (M x y)) y) y x)) (C (C (C h4 (S (h x x y))) h0) (T (T (C (T (T (C h0 h7) h6) h3) h15) h14) h12))) h4)) h4)) (S (h y (M v1 x) y))) h2) h8) h0)) (C h7 h0)

@[equational_result]
theorem Equation3193_implies_Equation2290 (G: Type _) [Magma G] (h: Equation3193 G) : Equation2290 G := fun x y =>
  have h0 := R x
  let v1 := M x x
  let v2 := M x v1
  have h3 := R v2
  have h4 := S (h y y x)
  have h5 := R y
  have h6 := h x x v1
  have h7 := h v2 v2 x
  have h8 := S h7
  have h9 := h v2 x v1
  have h10 := C h9 h3
  have h11 := h x v2 v2
  have h12 := T (C (T h11 (C (C (T (T (C (T h10 h8) h3) h10) h8) h0) h0)) h0) (S h6)
  let v13 := M y v2
  have h14 := S (h v13 v13 y)
  have h15 := R v13
  have h16 := C (h v13 y v2) h15
  have h17 := C (C (T (T (T (T (C (T h16 h14) h15) h16) h14) (C h5 (C h0 h12))) (C h5 h12)) h5) h5
  have h18 := h y v13 v13
  have h19 := C (S h9) h3
  have h20 := T h6 (C (T (C (C (T (T h7 h19) (C (T h7 h19) h3)) h0) h0) (S h11)) h0)
  have h21 := R (M (M y y) y)
  T (h x y y) (C (T (T (C h21 h20) (C h21 (C h0 h20))) (C (T (C (T (T (T (C (T h18 h17) h5) h4) h18) h17) h5) h4) h3)) h0)

@[equational_result]
theorem Equation492_implies_Equation4007 (G: Type _) [Magma G] (h: Equation492 G) : Equation4007 G := fun x y z =>
  let v0 := M x y
  let v1 := M y x
  let v2 := M z v1
  have h3 := h v1 v2 z
  have h4 := S h3
  have h5 := h z v1 z
  have h6 := R v2
  have h7 := C h6 h5
  let v8 := M v2 z
  have h9 := C h6 (S h5)
  have h10 := R v8
  have h11 := R x
  have h12 := R z
  have h13 := R v0
  have h14 := h v2 z v8
  have h15 := h z v8 v2
  have h16 := h v2 z v2
  have h17 := h v8 v2 v8
  T (h v0 v2 z) (C h6 (T (C h13 (T (C h12 (C h12 (T h14 (C h12 (T (C h6 (C h10 (C h10 (T h15 (C h10 (S h16)))))) (S h17)))))) (C h12 (C h12 (T (T (T (C h12 (T h17 (C h6 (C h10 (C h10 (T (C h10 h16) (S h15))))))) (S h14)) (h v2 z v0)) (C h12 (T (C h6 (C h13 (C h13 (T (h z v0 v8) (C h13 (C h12 (T (T (T (C h10 (C h10 (C h11 (T (h y x v8) (C h11 (T (T (T (C (R y) (C (T h7 h4) (C h10 (T (h x v1 y) (C (T h3 h9) (S (h y x y))))))) (S (h v1 y v8))) h3) h9)))))) (S (h v8 v8 x))) h7) h4))))))) (S (h v0 v2 v0))))))))) (S (h z v0 z))))

@[equational_result]
theorem Equation895_implies_Equation31 (G: Type _) [Magma G] (h: Equation895 G) : Equation31 G := fun x y =>
  let v0 := M y y
  let v1 := M v0 x
  let v2 := M y x
  have h3 := h y v1 x
  have h4 := R v1
  have h5 := h v0 x v0
  have h6 := S h5
  have h7 := h y x x
  have h8 := S h7
  have h9 := R x
  have h10 := h x x (M v2 (M x x))
  have h11 := h y v0 x
  have h12 := S h11
  have h13 := R v0
  have h14 := h v0 v0 (M v2 v1)
  have h15 := C (T h14 (C h13 (C h12 h12))) (T h10 (C h9 (C h8 h8)))
  have h16 := C h9 h15
  have h17 := T (C h9 (C h7 h7)) (S h10)
  have h18 := S h14
  have h19 := C h13 (C h11 h11)
  have h20 := C h9 (C (T h19 h18) h17)
  have h21 := T h16 h6
  T (T (T (h x v1 v1) (C h4 (T (T (T (C h21 (C (T (T h15 (C (C (T h5 h20) h13) (R (M x v0)))) (C (T (T (T (T (C h21 h13) h19) h18) h5) h20) h17)) h4)) (S (h (M x v1) v0 x))) h16) h6))) (C h4 (C h3 h3))) (S (h v1 v1 (M v2 (M v1 x))))

@[equational_result]
theorem Equation1761_implies_Equation3500 (G: Type _) [Magma G] (h: Equation1761 G) : Equation3500 G := fun x y z =>
  let v0 := M z z
  let v1 := M v0 y
  let v2 := M y v1
  have h3 := R z
  have h4 := h v2 z z
  have h5 := S h4
  have h6 := h z z y
  have h7 := S h6
  have h8 := R v2
  have h9 := h z y v1
  have h10 := C (T h9 (C h8 h7)) h3
  have h11 := h v0 v0 z
  have h12 := S h9
  have h13 := C (T (C h8 h6) h12) h3
  have h14 := R v0
  have h15 := C h14 h13
  have h16 := R (M v0 z)
  have h17 := C h14 (T (T (C h16 (T h9 (C (T h4 h15) h7))) (S h11)) h10)
  have h18 := h v0 z z
  have h19 := T (T h18 h17) h5
  have h20 := T (C h14 h10) h5
  T (C (T (h x v0 z) (C (T (T (C (T (T (T (T h18 h17) (C (T (T h18 h17) h15) h13)) (C h20 h14)) (C (T (T h4 (C h14 (T (T h13 h11) (C h16 (T (C h20 h6) h12))))) (S h18)) h19)) h3) (C (R (M v0 v2)) (T (h z z v0) (C (R (M z v0)) h20)))) (S (h z v0 v2))) (C (C (R x) h19) h3))) (h x v2 z)) (S (h v2 z (M (M x v2) z)))

@[equational_result]
theorem Equation1774_implies_Equation952 (G: Type _) [Magma G] (h: Equation1774 G) : Equation952 G := fun x y z =>
  let v0 := M z y
  let v1 := M z x
  let v2 := M v1 v0
  let v3 := M y v2
  have h4 := h v3 v1 v0
  have h5 := R v3
  have h6 := h v3 y v2
  have h7 := S h6
  let v8 := M (M y x) v2
  have h9 := h (M (M y v3) v2) v3 v8
  have h10 := R v8
  have h11 := h x y v2
  have h12 := T (C h11 (T h11 (C h6 h10))) (S h9)
  have h13 := T (C h5 h12) h7
  let v14 := M x x
  let v15 := M (M y v0) v2
  have h16 := S h11
  have h17 := h v0 y v2
  have h18 := R v2
  have h19 := h x v1 v0
  T (T h19 (C h18 (T (T (h (M (M v1 x) v0) v2 v3) (C (R (M v2 v3)) (T (T (T (T (T (T (T (C (S h19) h5) (C (h x z v0) (C (h y z v0) h18))) (S (h (M v0 v0) (M z v0) v2))) (C h17 (T h17 (C (T h6 (C h5 (T h9 (C h16 (T (C h7 h10) h16))))) (R v15))))) (S (h v14 v3 v15))) (h v14 v3 v14)) (C h13 (T (C h13 h12) h7))) (C h4 h5)))) (S (h (M (M v1 v3) v0) v2 v3))))) (S h4)

@[equational_result]
theorem Equation1507_implies_Equation1699 (G: Type _) [Magma G] (h: Equation1507 G) : Equation1699 G := fun x y z =>
  let v0 := M y z
  let v1 := M v0 z
  let v2 := M y x
  let v3 := M v2 v1
  let v4 := M v1 (M v1 v2)
  have h5 := S (h v4 (M v2 y) v2)
  have h6 := C (h y v2 v1) (h x y v2)
  let v7 := M v2 v3
  have h8 := R (M x (M x z))
  let v9 := M v3 (M v3 v0)
  let v10 := M v1 (M v1 y)
  have h11 := R (M x (M x v2))
  have h12 := h x y v1
  let v13 := M z y
  let v14 := M y v2
  let v15 := M y v14
  T (T (T (T (h x y x) (C (T (T (T (T h6 h5) (h v4 x x)) (C (T (T (T (C h12 (R v4)) (S (h v10 v2 v1))) (h v10 v2 y)) (C (S h12) (R v15))) (R (M x (M x x))))) (S (h v15 x x))) (R (M x (M x y))))) (S (h v14 y x))) (C (T (T (h y z x) (C (T (T (T (T (h v13 z x) (C (T (T (T (T (T (h (M z v13) v2 x) (C (S (h x y z)) h11)) (C h12 h11)) (S (h v10 v2 x))) (h v10 v0 v3)) (C (S (h z y v1)) (R v9))) h8)) (S (h v9 z x))) (h v9 v1 v2)) (C (S (h z v0 v3)) (R v7))) h8)) (S (h v7 z x))) (T h6 h5))) (S (h v3 v2 v1))

@[equational_result]
theorem Equation2944_implies_Equation2522 (G: Type _) [Magma G] (h: Equation2944 G) : Equation2522 G := fun x y z =>
  let v0 := M (M x z) z
  let v1 := M y v0
  let v2 := M v1 y
  have h3 := R v2
  let v4 := M (M x (M x y)) y
  have h5 := h y v4 v1
  have h6 := S h5
  have h7 := R v1
  have h8 := h y x y
  have h9 := R v4
  have h10 := C (C (T h8 (C h9 h8)) h7) h7
  have h11 := S h8
  have h12 := C (C h7 (C h7 (T h5 (C (C (T (C h9 h11) h11) h7) h7)))) h3
  have h13 := S (h v1 x v1)
  let v14 := M (M x (M x v1)) v1
  have h15 := C (C (T (C (R v14) h13) h13) h3) h3
  have h16 := h v1 v14 v2
  have h17 := R z
  have h18 := S (h x x x)
  let v19 := M (M x (M x x)) x
  T (T (T (T (h x v19 z) (C (C (T (C (R v19) h18) h18) h17) h17)) (h v0 y v2)) (C (C (C (R y) (T (T (T h16 h15) h12) (C (T (T (T (C (T (T h16 h15) h12) (C h7 (T h10 h6))) (S (h (M (M y v1) v1) v1 v2))) h10) h6) h3))) h3) h3)) (S (h v2 y v2))

@[equational_result]
theorem Equation3180_implies_Equation323 (G: Type _) [Magma G] (h: Equation3180 G) : Equation323 G := fun x y =>
  let v0 := M x y
  have h1 := R v0
  let v2 := M x v0
  have h3 := h x v2 v2
  have h4 := S h3
  have h5 := R x
  have h6 := h v2 x v0
  have h7 := C h6 h5
  have h8 := T h7 h4
  have h9 := S h6
  have h10 := C h9 h5
  have h11 := h x v0 v0
  have h12 := h v0 x y
  have h13 := C (S h12) h5
  have h14 := h x x v2
  have h15 := R v2
  have h16 := h x v2 x
  have h17 := T h3 h10
  have h18 := C h17 h5
  have h19 := h v2 x x
  have h20 := C (T h7 (C (T (T (T h9 h19) (C (T (T (T (C (C h18 h15) h5) (S h16)) h3) h10) h15)) (C h8 h15)) h5)) h5
  have h21 := C h8 h5
  have h22 := C (T (T (T (C h17 h15) (C (T (T (T h7 h4) h16) (C (C h21 h15) h5)) h15)) (S h19)) h6) h5
  T (T (T (h v0 x x) (C (T (T (T (C (C (T (T (T h18 h20) (C (T (T (T h22 h4) h14) (C (T (C (T h22 h10) h5) h21) h5)) h5)) (C (T (T (T (C (T h18 h20) h5) (S h14)) h11) h13) h5)) h1) h5) (S (h x v0 x))) h11) h13) h1)) (C (T (T (T (C h12 h5) (S h11)) h3) h10) h1)) (C h8 h1)

@[equational_result]
theorem Equation3791_implies_Equation3994 (G: Type _) [Magma G] (h: Equation3791 G) : Equation3994 G := fun x y z =>
  let v0 := M x y
  let v1 := M z v0
  have h2 := S (h z y z)
  let v3 := M y z
  let v4 := M z z
  have h5 := S (h v4 v3 v0)
  have h6 := h y v0 v1
  have h7 := h v0 v1 z
  let v8 := M v1 z
  have h9 := h v1 v8 (M v0 v1)
  have h10 := h z v0 v1
  have h11 := h v1 z v0
  have h12 := R (M v1 y)
  have h13 := h y v8 v1
  have h14 := C (T (T (T (T (T (h v1 z z) (C (h z v1 z) (h z z z))) (S (h v8 v4 v4))) (h v8 v4 y)) (C (T (T h13 (C h12 (T (T (C h11 h10) (S h9)) (S h7)))) (S h6)) (R (M v4 y)))) (S (h v0 v4 y))) (h z x y)
  let v15 := M z x
  let v16 := M y v1
  T (T (T (T (T (h x y z) (h v15 v3 v8)) (C (T (T (T h14 h5) h2) (h z y v1)) (R (M v3 v8)))) (S (h v16 v3 v8))) (C (R v16) (T (T (T (T (T (T (h y z x) (h v0 v15 y)) (C (T (T h6 (C h12 (T (T h7 h9) (C (S h11) (S h10))))) (S h13)) (R (M v15 y)))) (S (h v8 v15 y))) h14) h5) h2))) (S (h v1 z y))

@[equational_result]
theorem Equation1699_implies_Equation3131 (G: Type _) [Magma G] (h: Equation1699 G) : Equation3131 G := fun x y z =>
  let v0 := M y x
  let v1 := M v0 z
  let v2 := M v1 z
  let v3 := M v2 y
  have h4 := R (M (M v3 z) z)
  let v5 := M (M v1 v3) v3
  have h6 := T (h y v2 v5) (C (R v3) (T (C (T (S (h z v1 v3)) (h z v0 z)) (R v5)) (S (h v2 v1 v3))))
  have h7 := h y v2 y
  have h8 := S h7
  let v9 := M v3 y
  have h10 := C (T (T (T (h v9 v3 z) (C h8 h4)) (C h6 h4)) (S (h v2 v3 z))) (R y)
  let v11 := M v9 y
  have h12 := S (h v11 y x)
  let v13 := M v0 x
  let v14 := M (M v3 v2) v2
  have h15 := C (T (T (T (C h7 (R v14)) (S (h v9 v3 v2))) (h v9 v3 y)) (C h8 (R v11))) (R v13)
  have h16 := h v14 y x
  have h17 := R v2
  T (T (T (T (T (T (h x v0 z) (C (T (T (h v13 v0 x) (C (T (S (h x y x)) (h x y v2)) (R (M v13 x)))) (S (h (M (M y v2) v2) v0 x))) h17)) (C (C (T (T (T (T (C h6 h17) h16) h15) h12) h10) h17) h17)) h16) h15) h12) h10

@[equational_result]
theorem Equation3211_implies_Equation2170 (G: Type _) [Magma G] (h: Equation3211 G) : Equation2170 G := fun x y z =>
  let v0 := M y z
  let v1 := M z y
  let v2 := M v0 x
  let v3 := M v2 v1
  have h4 := R v0
  have h5 := R v3
  have h6 := R x
  have h7 := R v1
  have h8 := R v2
  have h9 := R z
  have h10 := R y
  have h11 := h z y v0
  have h12 := h y v0 z
  have h13 := h z y z
  have h14 := h v0 z v0
  have h15 := h v0 v2 x
  have h16 := h x v0 x
  T (T (h x v0 v2) (C (T (T (T (T (C (C (C (T h15 (C (S h16) h8)) h8) h8) h6) (S (h v2 x v2))) (h v2 v3 v1)) (C (S (h v1 v2 v1)) h5)) (C (T (h v1 x v2) (C (T (C (C (T (T (C h16 h8) (S h15)) (C (T (h y z z) (C (C (T (C (C (T (h z y v1) (C (T (C (C (C (T (h y v1 v0) (C (T (C (T (T (T (C (C (C (T h11 (C (T (C (C (C (T h12 (C (S h13) h4)) h4) h4) h9) (S h14)) h10)) h10) h4) h4) (S (h v0 v0 y))) h14) (C (C (C (T (C h13 h4) (S h12)) h4) h4) h9)) h10) (S h11)) h7)) h7) h7) h9) (S (h v1 z v1))) h10)) h9) h9) (S (h z z y))) h10) h9)) h9)) h8) h7) (S (h v2 v1 z))) h6)) h5)) h4)) (S (h v3 v0 x))

@[equational_result]
theorem Equation4176_implies_Equation4162 (G: Type _) [Magma G] (h: Equation4176 G) : Equation4162 G := fun x y z =>
  have h0 := R z
  have h1 := S (h y x x)
  have h2 := R x
  have h3 := R y
  have h4 := h x x y
  have h5 := S h4
  let v6 := M y x
  have h7 := h x v6 y
  have h8 := h y y x
  have h9 := C (T (T (T (S (h x v6 z)) h7) (C (S h8) h3)) (C (T (T (h y y y) (C (T (T (T (C h8 h3) (S h7)) (h x v6 x)) (C (S (h x y x)) h2)) h3)) h5) h3)) h2
  let v10 := M v6 z
  have h11 := h z v10 x
  let v12 := M v10 z
  have h13 := R v10
  let v14 := M x y
  have h15 := h y v14 x
  T (h x y z) (C (T (T (T (C (T (T (T (h y z v10) (C (T (T (T (T (T (C (T (T (T h11 h9) h1) (h y x y)) h3) (S (h y v14 y))) h15) (C h5 h2)) (C (T (T (T (h x x x) (C (T (C h4 h2) (S h15)) h2)) (C (T (h y v14 z) (C (S (h z x y)) h0)) h2)) (S (h z z x))) h2)) (C (T (h z z v10) (C (C (T (T h11 h9) h1) h0) h13)) h2)) h13)) (S (h x v10 v10))) (h x v10 z)) h2) (S (h z v12 x))) (h z v12 z)) (C (T (T (T (S (h z v10 z)) h11) h9) h1) h0)) h0)

@[equational_result]
theorem Equation627_implies_Equation3660 (G: Type _) [Magma G] (h: Equation627 G) : Equation3660 G := fun x y =>
  let v0 := M x y
  let v1 := M x x
  let v2 := M v1 v0
  have h3 := h x v1 v2
  have h4 := R v2
  have h5 := h v0 x x
  have h6 := S h5
  let v7 := M v1 x
  let v8 := M v0 v7
  have h9 := R v8
  have h10 := R v1
  have h11 := C h10 (C h10 (T (C h6 h9) h6))
  have h12 := h v1 v0 v8
  let v13 := M x v7
  have h14 := h x x v13
  have h15 := R v13
  have h16 := h x x x
  have h17 := R x
  have h18 := h x x v1
  have h19 := S (h y v2 y)
  let v20 := M y (M (M v2 y) y)
  have h21 := S h12
  have h22 := C h10 (C h10 (T h5 (C h5 h9)))
  have h23 := S h16
  T (T (T (T (C h17 (T h3 (C h17 (C (T h14 (C h17 (C h17 (T (C h23 h15) h23)))) (T (T (C (T h22 h21) h4) h22) h21))))) (S h18)) (h x y v20)) (C h17 (C h17 (T (C h19 (R v20)) h19)))) (C (T h18 (C h17 (T (C h17 (C (T (C h17 (C h17 (T h16 (C h16 h15)))) (S h14)) (T (T h12 h11) (C (T h12 h11) h4)))) (S h3)))) (R v0))

@[equational_result]
theorem Equation3211_implies_Equation3567 (G: Type _) [Magma G] (h: Equation3211 G) : Equation3567 G := fun x y z =>
  let v0 := M z x
  let v1 := M v0 z
  let v2 := M y v1
  have h3 := R y
  have h4 := R v2
  let v5 := M x y
  have h6 := h y v1 v5
  have h7 := S h6
  have h8 := R v1
  have h9 := R v5
  have h10 := R z
  have h11 := h v0 x v0
  have h12 := R x
  have h13 := R v0
  have h14 := h x z x
  have h15 := h z v0 x
  have h16 := C (T (C (C (C (T h15 (C (S h14) h13)) h13) h13) h12) (S h11)) h10
  have h17 := h x z v0
  have h18 := h x v5 y
  have h19 := h y x y
  have h20 := h v5 y v5
  have h21 := C (T (T (T (C (C (C (T h6 (C (T (C (C (C (T (T (T (C (T h11 (C (C (C (T (C h14 h13) (S h15)) h13) h13) h12)) h10) (S h17)) h18) (C (S h19) h9)) h9) h9) h3) (S h20)) h8)) h8) h9) h9) (S (h v5 v5 v1))) h20) (C (C (C (T (T (T (C h19 h9) (S h18)) h17) h16) h9) h9) h3)) h8
  have h22 := h v1 v2 v5
  T (C (T (T (T h17 h16) h22) (C (T (T (T h21 h7) (h y v2 v1)) (C (T (T (S (h v1 y v1)) h22) (C (T h21 h7) h4)) h4)) h4)) h3) (S (h v2 y v2))

@[equational_result]
theorem Equation1507_implies_Equation4007 (G: Type _) [Magma G] (h: Equation1507 G) : Equation4007 G := fun x y z =>
  let v0 := M x y
  let v1 := M y x
  let v2 := M z v1
  let v3 := M v2 z
  let v4 := M v0 (M v0 v1)
  let v5 := M v2 (M v2 v0)
  have h6 := R (M x (M x v0))
  have h7 := h y x v1
  let v8 := M v1 (M v1 x)
  have h9 := R v5
  have h10 := S (h v5 (M v0 x) v0)
  have h11 := C (h x v0 v2) (h y x v0)
  let v12 := M v0 v3
  let v13 := M v0 v12
  have h14 := h z v2 y
  let v15 := M y (M y v2)
  T (T (T (T (T h11 h10) (h v5 v1 v0)) (R (M (M v1 v5) v4))) (C (T (T (C (T (T (h v1 z x) (C (T (T (T (C h14 (h v1 z v2)) (S (h v15 v3 v2))) (h v15 v3 v0)) (C (S h14) (R v13))) (R (M x (M x z))))) (S (h v13 z x))) h9) (S (h v12 v0 v2))) (C (T (T (T (T h11 h10) (h v5 y v5)) (C (T (T (T (T (T (C h7 h9) (S (h v8 v0 v2))) (h v8 v0 x)) (C (S h7) h6)) (C (h y x y) h6)) (S (h (M y v1) v0 x))) (R (M v5 (M v5 y))))) (S (h v1 y v5))) (R v3))) (R v4))) (S (h v3 v1 v0))

@[equational_result]
theorem Equation1699_implies_Equation16 (G: Type _) [Magma G] (h: Equation1699 G) : Equation16 G := fun x y =>
  let v0 := M y x
  let v1 := M y v0
  let v2 := M x v1
  let v3 := M v1 v1
  let v4 := M v3 v1
  have h5 := R v4
  let v6 := M v0 x
  have h7 := h v6 v0 x
  have h8 := R (M v6 x)
  have h9 := h x y x
  have h10 := h x y y
  let v11 := M (M y y) y
  have h12 := h v11 v0 x
  have h13 := h v11 v1 v1
  have h14 := h v0 y y
  let v15 := M (M v1 y) y
  have h16 := S h14
  have h17 := S h12
  have h18 := C (T (S h9) h10) h8
  have h19 := R (M (M v0 v1) v1)
  T (T (T (T (T (T (h x v0 v1) (C (T (T h7 h18) h17) h19)) (C (T h13 (C h16 h5)) h19)) (S (h v4 v0 v1))) (h v4 x v1)) (C (T (C (T (T (T (T (h x v0 x) (C (T (T (T (T h7 h18) h17) (h v11 v1 y)) (C h16 (R v15))) h8)) (S (h v15 v0 x))) (h v15 v3 v1)) (C (S (h v1 v1 y)) (C (T (T (h v4 v0 y) (C (T (T (T (T (C h14 h5) (S h13)) h12) (C (T (S h10) h9) h8)) (S h7)) (R (M (M v0 y) y)))) (S (h x v0 y))) (R v1)))) h5) (S (h v2 v1 v1))) (R (M v2 v1)))) (S (h v1 x v1))

@[equational_result]
theorem Equation1761_implies_Equation26 (G: Type _) [Magma G] (h: Equation1761 G) : Equation26 G := fun x y =>
  let v0 := M x y
  let v1 := M v0 y
  have h2 := R v1
  let v3 := M v1 x
  have h4 := h y y v1
  have h5 := S h4
  have h6 := h x y y
  have h7 := R (M y v1)
  have h8 := R v3
  have h9 := h y v1 x
  have h10 := T h9 (C h8 (T (C h7 h6) h5))
  have h11 := R y
  have h12 := h v0 y x
  have h13 := S h6
  let v14 := M y x
  have h15 := h v14 v3 y
  have h16 := T (C (T h15 (C (T (C h8 (T h4 (C h7 h13))) (S h9)) (C (S h12) h11))) h6) h5
  let v17 := M v14 x
  have h18 := S h15
  have h19 := C h10 (C h12 h11)
  have h20 := C (T h19 h18) h13
  let v21 := M x x
  T (T (h x x v1) (C (R (M x v1)) (C (T (T (h v21 y v1) (C h7 (T (T (C (T (C (R v21) (T (T (T h4 h20) (h v17 y v1)) (C (T (T h19 h18) (C (T h4 h20) (R x))) (T (C (C h16 h11) h2) h13)))) (S (h v17 x x))) h2) (C h16 h2)) (C h10 h2)))) (S (h v3 y v1))) h2))) (S (h v1 x v1))

@[equational_result]
theorem Equation2196_implies_Equation725 (G: Type _) [Magma G] (h: Equation2196 G) : Equation725 G := fun x y z =>
  let v0 := M z x
  let v1 := M v0 z
  let v2 := M y v1
  let v3 := M y v2
  let v4 := M v3 v2
  let v5 := M (M v2 y) y
  let v6 := M (M v1 v1) v1
  have h7 := h v0 z v2
  let v8 := M (M z v2) v2
  let v9 := M v1 y
  let v10 := M v9 y
  let v11 := M v0 x
  have h12 := R (M v11 x)
  let v13 := M v1 z
  have h14 := h z x v3
  let v15 := M (M x v3) v3
  let v16 := M x z
  T (T (T (T (T (T (h x z v2) (C (R v8) (T (T (h v16 z x) (C (R v11) (T (T (T (T (h (M v16 z) v0 x) (C h12 (T (S (h z x z)) h14))) (S (h v15 v0 x))) (h v15 v0 z)) (C (R v13) (S h14))))) (S (h v13 z x))))) (S (h v1 z v2))) (h v1 y v2)) (C (R v4) (T (T (T (T (h v9 y x) (C (R (M (M y x) x)) (T (T (T (T (h v10 v0 x) (C h12 (T (T (T (C (R v10) h7) (S (h v8 v1 y))) (h v8 v1 v1)) (C (R v6) (S h7))))) (S (h v6 v0 x))) (h v6 v2 y)) (C (R v5) (S (h y v1 v1)))))) (S (h v5 y x))) (h v5 (M v1 v2) v2)) (C (S (h y v1 v2)) (S (h v1 v2 y)))))) (h (M v4 v2) (M v2 v3) v3)) (C (S (h y v2 v3)) (S (h v2 v3 v2)))

