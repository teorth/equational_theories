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
theorem Equation711_implies_Equation725 (G: Type _) [Magma G] (h: Equation711 G) : Equation725 G := fun x y z =>
  let v0 := M z x
  let v1 := M v0 z
  have h2 := S (h v1 v1 x)
  let v3 := M v1 (M (M v1 x) x)
  have h4 := R y
  let v5 := M z (M v0 x)
  have h6 := h z v0 v5
  have h7 := S h6
  have h8 := R v5
  have h9 := h z z x
  have h10 := R v0
  have h11 := C h10 (C h10 (T h9 (C h9 h8)))
  have h12 := R x
  have h13 := S h9
  have h14 := C h10 (C (C (T h6 (C h10 (C h10 (T (C h13 h8) h13)))) h12) h12)
  have h15 := S (h x x x)
  let v16 := M x (M (M x x) x)
  have h17 := C h10 (C h10 (T (C h15 (R v16)) h15))
  have h18 := h x v0 v16
  T (T (T (T (T h18 h17) h14) (C h10 (T (T (T (C (C (T h11 h7) h12) (T (T h18 h17) h14)) (S (h (M v0 v1) v0 x))) h11) h7))) (h v1 y v3)) (C h4 (C h4 (T (C h2 (R v3)) h2)))

@[equational_result]
theorem Equation3789_implies_Equation41 (G: Type _) [Magma G] (h: Equation3789 G) : Equation41 G := fun x y z =>
  let v0 := M y z
  have h1 := h y x x
  have h2 := h x y x
  have h3 := S h2
  let v4 := M x x
  let v5 := M y x
  have h6 := h v4 v5 v4
  have h7 := S h6
  have h8 := h x x y
  have h9 := h x x x
  have h10 := C h9 h8
  have h11 := h x x z
  have h12 := S h11
  have h13 := S h9
  let v14 := M z x
  have h15 := h v4 v14 v4
  have h16 := T (T (T (T h15 (C h13 h12)) h10) h7) h3
  have h17 := h v14 v4 v4
  have h18 := C h13 (S h8)
  have h19 := T (T (T (T h2 h6) h18) (C h9 h11)) (S h15)
  T (T (T (T h8 (h v5 v4 v0)) (C (C (R v0) (T (T (T (T (T (T (T h1 (C h19 h19)) (S h17)) h12) h9) h10) h7) h3)) (T (T (T (T (T (T (T h6 h18) h13) h11) h17) (C h16 h16)) (S h1)) (h y x z)))) (S (h (M x y) (M z y) v0))) (S (h y z x))

@[equational_result]
theorem Equation3930_implies_Equation4510 (G: Type _) [Magma G] (h: Equation3930 G) : Equation4510 G := fun x y z =>
  let v0 := M x y
  have h1 := R x
  let v2 := M y z
  let v3 := M y v2
  have h4 := T (T (h x v3 y) (C (C h1 (S (h y y z))) h1)) (S (h x y y))
  have h5 := S (h x y z)
  have h6 := h y z y
  have h7 := C (C h1 (S h6)) h1
  let v8 := M z y
  have h9 := h x (M y v8) y
  let v10 := M v0 x
  have h11 := R y
  have h12 := h z y z
  have h13 := R z
  let v14 := M z v2
  have h15 := S (h y v14 z)
  have h16 := C (C h11 h12) h11
  have h17 := C h1 (T (T (T (T (T h6 h16) h15) (h y v14 v10)) (C (C h11 (C (T (T (h z v2 y) (C (C h13 (T (C (T (T h6 h16) h15) h11) (S (h y z v2)))) h13)) (S h12)) (R v10))) h11)) (S (h y v8 v10)))
  T (T (T (T (T (T (T h17 h9) h7) h5) (h x y v2)) (h (M x v3) x v2)) (C (C h4 (T (T (T h17 h9) h7) h5)) h4)) (S (h v0 x y))

@[equational_result]
theorem Equation3384_implies_Equation3451 (G: Type _) [Magma G] (h: Equation3384 G) : Equation3451 G := fun x y z w u =>
  let v0 := M x y
  let v1 := M y y
  let v2 := M u v1
  have h3 := h u y v2
  have h4 := h x y (M x v1)
  let v5 := M u y
  let v6 := M w v5
  let v7 := M z v6
  let v8 := M v1 v1
  have h9 := h v1 y x
  have h10 := h v1 y u
  have h11 := T (S h10) h9
  have h12 := R v7
  have h13 := T (T (T (T (h u v1 v7) (h v7 (M u v8) v7)) (C h12 (C h12 (C h11 h11)))) (S (h v7 (M x v8) v7))) (S (h x v1 v7))
  have h14 := T (T h3 (C h13 h13)) (S h4)
  have h15 := S h3
  let v16 := M v2 v2
  have h17 := T (T (h x v1 v6) (C (R v6) (T (S h9) h10))) (S (h u v1 v6))
  T (T (T (h x y v0) (C (R v0) h17)) (h v0 v2 z)) (C (R z) (T (T (T (T (R (M v0 v16)) (C (T h4 (C h17 h17)) (R v16))) (C h15 h15)) (h v5 v5 w)) (C (R w) (T (T (C h14 (C h14 h3)) (S (h v0 v2 v0))) (S (h u y v0))))))

@[equational_result]
theorem Equation3930_implies_Equation327 (G: Type _) [Magma G] (h: Equation3930 G) : Equation327 G := fun x y z =>
  have h0 := h y z y
  have h1 := R y
  have h2 := h z y z
  have h3 := R z
  let v4 := M y z
  let v5 := M x v4
  have h6 := h y z v5
  have h7 := S h6
  have h8 := h z v5 x
  have h9 := h x y z
  have h10 := h z x y
  have h11 := h z x v4
  have h12 := C h1 (T (T (T (S h11) h10) (C (C h3 h9) h3)) (S h8))
  have h13 := C h12 h1
  have h14 := C h1 (T (T (T h8 (C (C h3 (S h9)) h3)) (S h10)) h11)
  have h15 := h y (M z v5) z
  have h16 := C h14 h1
  have h17 := C h3 (T (T h6 h16) (C (T (T (T h12 h15) h13) h7) h1))
  let v18 := M z y
  have h19 := R x
  T (T (T h9 (C (C h19 h0) h19)) (S (h x (M y v18) y))) (C h19 (T (T (h y v18 z) (C (C h1 (T (T (C (T (T (T h2 (C h17 h3)) (S (h z v4 y))) h17) h3) (C (C h3 (T (T (C (T (T (T h6 h16) (S h15)) h14) h1) h13) h7)) h3)) (S h2))) h1)) (S h0)))

@[equational_result]
theorem Equation928_implies_Equation543 (G: Type _) [Magma G] (h: Equation928 G) : Equation543 G := fun x y z =>
  let v0 := M y z
  let v1 := M x v0
  let v2 := M z v1
  let v3 := M y v2
  let v4 := M v0 x
  have h5 := h z v0 x
  let v6 := M v1 v1
  have h7 := S (h v1 v2 x)
  have h8 := R v2
  let v9 := M v1 x
  have h10 := R z
  have h11 := R v1
  have h12 := h v1 v1 (M v9 v4)
  have h13 := h v0 v1 x
  have h14 := S h13
  T (T (h x v2 v0) (C h8 (C (R (M v2 v0)) (T (T (T h12 (C h11 (C h14 h14))) (h (M v1 (M v0 v0)) v3 v1)) (C (R v3) (T (T (C (T (h (M v3 v1) y v2) (C (R y) (S (h z v3 v1)))) (T (T (C (T (C h11 (C h13 h13)) (S h12)) h11) (h v6 z v2)) (C h10 (T (C (T (C h10 (T (h v2 v2 (M (M v2 x) v9)) (C h8 (C h7 h7)))) (S (h v1 z v1))) (R (M v6 v2))) (S (h z v1 v1)))))) (C (R v0) (C h5 h5))) (S (h v0 v0 (M v4 (M z x)))))))))) (S (h v3 v2 v0))

@[equational_result]
theorem Equation4176_implies_Equation3497 (G: Type _) [Magma G] (h: Equation4176 G) : Equation3497 G := fun x y z =>
  let v0 := M x x
  let v1 := M z y
  let v2 := M v1 z
  have h3 := R v0
  have h4 := R y
  have h5 := h v1 z v2
  have h6 := R v2
  let v7 := M z v2
  have h8 := R z
  have h9 := R v1
  have h10 := S (h y v1 x)
  have h11 := R x
  have h12 := C (h x z y) h11
  have h13 := h x x z
  have h14 := h z z y
  let v15 := M y v2
  T (T (T (T (T (T (h x x y) (C (T (C (h x y v2) h11) (S (h v2 v15 x))) h4)) (C (T (h v2 v15 y) (C (S (h y y v2)) h4)) h4)) (S (h y y y))) (h y y v0)) (C (C (T (h y v0 v0) (C (T (T (T (T (C (C (T (T (T h13 (C (T (T (T h12 h10) (h y v1 z)) (C (S h14) h8)) h8)) (S (h z z z))) h14) h3) h4) (S (h v0 v2 y))) (C h13 h6)) (C (T (C (T (T (T (T (T h12 h10) (h y v1 v1)) (C (S (h v1 z y)) h9)) (C h5 h9)) (S (h v2 v7 v1))) h8) (S (h v7 v1 z))) h6)) (S h5)) h3)) h4) h3)) (S (h y v2 v0))

@[equational_result]
theorem Equation1283_implies_Equation2 (G: Type _) [Magma G] (h: Equation1283 G) : Equation2 G := fun x y =>
  let v0 := M x x
  let v1 := M (M v0 x) x
  let v2 := M v1 v1
  let v3 := M v2 y
  let v4 := M (M v3 v3) x
  let v5 := M (M (M y y) y) y
  have h6 := R x
  have h7 := h x v1 x
  have h8 := S h7
  have h9 := R v2
  let v10 := M (M v0 y) y
  have h11 := h x v10 y
  have h12 := S h11
  have h13 := T (C (T (C (C (T h12 h7) h12) h6) (C (C h9 h7) h6)) h6) (C (C (C h8 h8) h6) h6)
  let v14 := M v10 v10
  have h15 := h v14 x x
  have h16 := R v4
  have h17 := R y
  have h18 := S h15
  have h19 := T (C (C (C h7 h7) h6) h6) (C (T (C (C h9 h8) h6) (C (C (T h8 h11) h11) h6)) h6)
  T (T (T (h x y x) (C h17 (T (h v1 v4 v1) (C h16 (T (T (C (T (T (C h8 h19) h18) h12) h19) h18) h12))))) (C h17 (T (C h16 (T (T h11 h15) (C (T (T h11 (h v14 y x)) (C (h y v5 y) h13)) h13))) (S (h v5 v4 v1))))) (S (h y y y))

@[equational_result]
theorem Equation4176_implies_Equation3959 (G: Type _) [Magma G] (h: Equation4176 G) : Equation3959 G := fun x y z =>
  let v0 := M x z
  let v1 := M y v0
  have h2 := R v0
  have h3 := R v1
  have h4 := h v1 x z
  let v5 := M x y
  have h6 := R x
  have h7 := h x y v0
  have h8 := R y
  let v9 := M v1 z
  let v10 := M z v9
  have h11 := R z
  T (T h7 (C (T (T (T (T (T (T (T h4 (C (T (T (h v0 v1 y) (C (S (h y y v0)) h8)) (C (T (T (T (h y y x) (C (T (C (h y x z) h8) (S (h z v0 y))) h6)) (C (T (h z v0 z) (C (S (h z x z)) h11)) h6)) (S (h z z x))) h8)) h11)) (S (h y z z))) (h y z v0)) (C (T (C (T (h z v0 x) (C (T (T (T (C (T (C (h x z v9) h6) (S (h v9 v10 x))) h11) (S (h v10 v1 z))) (C (T (h z v9 y) (C (S (h y v1 z)) h8)) h3)) (S (h y y v1))) h6)) h8) (S (h x y y))) h2)) (h v5 v0 v1)) (C (T (C (T (T (h v0 v1 x) (C (S h7) h6)) (h v5 x y)) (R v5)) (S (h y v5 v5))) h3)) (C (T (T (h y v5 v1) (C (T (S (h v1 x y)) h4) h3)) (S (h z v0 v1))) h3)) h2)) (S (h v1 z v0))

@[equational_result]
theorem Equation2105_implies_Equation2592 (G: Type _) [Magma G] (h: Equation2105 G) : Equation2592 G := fun x y z =>
  let v0 := M z y
  let v1 := M v0 z
  let v2 := M y v1
  let v3 := M v2 x
  have h4 := R v1
  have h5 := h y z x
  have h6 := S h5
  let v7 := M x x
  have h8 := R v7
  have h9 := h v1 v1 x
  have h10 := h (M v1 v1) v1 x
  have h11 := S h10
  have h12 := h y z v1
  have h13 := C (T (C h6 h4) (C h12 h4)) h8
  have h14 := h v7 v1 x
  have h15 := h v1 v7 x
  have h16 := C (T (T h15 (C (T (C (C (T (T h14 h13) h11) h4) h8) (S h9)) h8)) h6) h4
  T (T (h x x v0) (C (T (T (C (T (T (T h14 h13) h11) h16) (R x)) (h v3 v3 v1)) (C (C (T (T (T (T (h (M v3 v3) v1 x) (C (C (S (h y z v3)) h4) h8)) (C (C (h y z y) h4) h8)) (S (h (M y y) v1 x))) (C (R y) (T (T h5 (C (T h9 (C (C (T (T h10 (C (T (C (S h12) h4) (C h5 h4)) h8)) (S h14)) h4) h8)) h8)) (S h15)))) (R v3)) h16)) (R (M v0 v0)))) (S (h v3 v2 v0))

@[equational_result]
theorem Equation3768_implies_Equation41 (G: Type _) [Magma G] (h: Equation3768 G) : Equation41 G := fun x y z =>
  let v0 := M x x
  let v1 := M y y
  let v2 := M z x
  have h3 := R (M v2 v2)
  have h4 := h x y y
  have h5 := S (h x x x)
  have h6 := R v0
  have h7 := h z z z
  have h8 := S h4
  let v9 := M z z
  have h10 := h v9 v1 v0
  have h11 := h y z z
  have h12 := h x y z
  have h13 := R v1
  let v14 := M y z
  have h15 := T (T (h y z v14) (C (T (T (T (T (h z v14 v0) (C (S h12) (R v9))) (C h4 h7)) (S h10)) (S h11)) h13)) (S (h y y z))
  T (T (T (T (T (T (T (T (T (T (T (T (T (T (h x x y) (C h12 h6)) (S (h x v14 v0))) (h x v14 v14)) (C (T (T (C h15 (R v14)) (C h13 h15)) (S (h y y y))) h6)) h8) h12) (C (T (T (T h11 h10) (C h8 (S h7))) (S (h z x y))) h6)) (h v2 v0 x)) (C (T (T (h v0 x x) (C h6 h5)) h5) h3)) (S (h v2 x x))) (h v2 x y)) (C h4 h3)) (S (h v2 v1 v0))) (S (h y z x))

@[equational_result]
theorem Equation895_implies_Equation962 (G: Type _) [Magma G] (h: Equation895 G) : Equation962 G := fun x y z =>
  let v0 := M x z
  let v1 := M z y
  let v2 := M v1 v0
  let v3 := M y v2
  have h4 := h v1 v1 v0
  have h5 := R (M v2 v2)
  have h6 := h v1 v0 v0
  have h7 := h v0 v2 x
  have h8 := S h7
  have h9 := R v2
  have h10 := C h9 (C h8 h8)
  let v11 := M v0 x
  have h12 := h v2 v2 (M v11 (M v2 x))
  have h13 := R v0
  have h14 := T (C h9 (C h7 h7)) (S h12)
  have h15 := T h6 (C h13 h14)
  have h16 := R v3
  have h17 := h v0 v2 v2
  have h18 := R z
  have h19 := h z v0 x
  T (T (T (h x z z) (C h18 (T (C h13 (C h19 h19)) (S (h v0 v0 (M (M z x) v11)))))) (C h18 (T h17 (C (T (T (T h12 h10) (h (M v2 (M v0 v0)) v3 v1)) (C h16 (T (C (T (C h14 (T h4 (C h15 h5))) (S h17)) (C h16 h15)) (S (h y v0 v2))))) (T (C (T (C h13 (T h12 h10)) (S h6)) h5) (S h4)))))) (S (h v3 z y))

@[equational_result]
theorem Equation914_implies_Equation455 (G: Type _) [Magma G] (h: Equation914 G) : Equation455 G := fun x y z =>
  let v0 := M z y
  let v1 := M z v0
  let v2 := M y v1
  let v3 := M x v2
  have h4 := h v3 v1 v0
  let v5 := M y y
  have h6 := R v5
  let v7 := M z z
  have h8 := R (M x x)
  have h9 := h v1 x z
  have h10 := R x
  let v11 := M (M x v1) v7
  let v12 := M v3 v3
  have h13 := h x v1 v3
  have h14 := R v1
  T (T h13 (C h14 (T (T (h (M (M v1 x) v12) v1 y) (C h14 (T (T (C (S h13) (T (T (C (R y) (T (T (T (h y x x) (C h10 (C (T (T (T (C h10 (T (T (T (h y z x) (C (R z) (C (h v0 z v3) h8))) (S (h (M v1 v12) z x))) (C h9 (R v12)))) (S (h v11 x v3))) (h v11 x y)) (C h10 (C (S h9) h6))) h8))) (S (h (M v1 v5) x x))) (C (h v1 y z) h6))) (S (h (M v2 v7) y y))) (C (h v2 x y) (R v7)))) (S (h (M v3 v5) x z))) (C h4 h6)))) (S (h (M (M v1 v3) (M v0 v0)) v1 y))))) (S h4)

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
theorem Equation881_implies_Equation2 (G: Type _) [Magma G] (h: Equation881 G) : Equation2 G := fun x y =>
  have h0 := h y x y
  have h1 := S h0
  let v2 := M y y
  let v3 := M y x
  let v4 := M v3 v2
  have h5 := h x y x
  let v6 := M x x
  let v7 := M (M x y) v6
  have h8 := h v7 x x
  have h9 := R v4
  have h10 := C h9 (T (C h1 (S h8)) (S h5))
  let v11 := M v7 x
  have h12 := h x v4 (M v11 v11)
  let v13 := M v2 v3
  let v14 := M v13 x
  have h15 := h x v4 (M v14 v14)
  have h16 := h v13 x x
  have h17 := h y y x
  have h18 := C h9 (T (C h1 (S h16)) (S h17))
  let v19 := M v6 v6
  let v20 := M v19 x
  have h21 := h x x x
  have h22 := R v19
  let v23 := M v3 v3
  let v24 := M v23 x
  T (T h21 (C (R x) (T (T (h v19 y x) (C (R y) (T (C (T (T (T (C h22 (T (h y x x) (C h21 (h v23 x x)))) (S (h x v19 (M v24 v24)))) h12) h10) (T (T (T (C h22 (T h21 (C h21 (h v19 x x)))) (S (h x v19 (M v20 v20)))) h15) h18)) (C (T (T (T (C h9 (T h5 (C h0 h8))) (S h12)) h15) h18) (T (T (T (C h9 (T h17 (C h0 h16))) (S h15)) h12) h10))))) (S (h v4 y x))))) h1

@[equational_result]
theorem Equation3354_implies_Equation41 (G: Type _) [Magma G] (h: Equation3354 G) : Equation41 G := fun x y z =>
  let v0 := M x x
  have h1 := S (h z (M y v0) x)
  let v2 := M y x
  have h3 := R x
  have h4 := h y x x
  have h5 := S h4
  have h6 := h x x v2
  have h7 := C h3 (T h6 (C h3 h5))
  have h8 := h x x x
  have h9 := C h3 (S h8)
  have h10 := h x x v0
  let v11 := M y z
  have h12 := h y v0 v11
  have h13 := h y v11 x
  have h14 := R v11
  have h15 := h x v11 x
  have h16 := R v0
  have h17 := h x v0 v11
  have h18 := T (T (T (T h10 h9) h17) (C h16 (C h16 (T (T h15 (C h14 (C h14 (T (T (T h10 h9) h7) h5)))) (S h13))))) (S h12)
  have h19 := C h18 (C h18 (T (T (T (T (T (T h10 h9) h7) h5) (h y x z)) (C h3 (C h3 (h y z x)))) (S (h z x (M z v2)))))
  have h20 := h x v0 x
  have h21 := R z
  T (T (T (T (T (T (T (h x x (M x v11)) (C h3 (S (h x x v11)))) h20) h19) h1) (C h21 (T (T h12 (C h16 (C h16 (T (T h13 (C h14 (C h14 (T (T (T h4 (C h3 (T (C h3 h4) (S h6)))) (C h3 h8)) (S h10))))) (S h15))))) (S h17)))) (C h21 (T (T h20 h19) h1))) (S (h y z v0))

@[equational_result]
theorem Equation3557_implies_Equation41 (G: Type _) [Magma G] (h: Equation3557 G) : Equation41 G := fun x y z =>
  let v0 := M y z
  let v1 := M x x
  let v2 := M z y
  let v3 := M (M v0 v2) v1
  have h4 := h y z v1
  have h5 := R z
  let v6 := M v2 v1
  have h7 := R v1
  have h8 := R x
  have h9 := h x x x
  have h10 := S h9
  have h11 := h (M v1 x) x x
  have h12 := T (T h11 (C h8 (C h10 h8))) h10
  have h13 := h x x v1
  have h14 := C h8 (C (S h13) h8)
  let v15 := M v1 v1
  have h16 := h v15 x x
  have h17 := C (T (T (T h16 h14) (C h8 (C h9 h8))) (S h11)) h7
  have h18 := S h16
  have h19 := C h8 (C h13 h8)
  T (T (T (T (T (T (T (T h13 (h x v15 v1)) (C (R v15) (T (T h17 (C h12 (T (T (T h9 h19) h18) (C (h v1 v1 z) h8)))) (S (h (M v15 z) v1 x))))) (S (h z v15 v1))) (C h5 (T (T (T (T (T (h v1 v1 x) (C (T (T h9 h19) h18) (T (T h16 h14) h10))) h17) (C h12 (T (T h9 (C h8 (C (h x x v0) h8))) (S (h (M v1 v0) x x))))) (S (h v0 v1 x))) (C h4 h7)))) (S (h v6 z v1))) (h v6 z v3)) (C h5 (T (C (S h4) (R v3)) (S (h v2 v0 v1))))) (S (h y z v0))

@[equational_result]
theorem Equation1710_implies_Equation1865 (G: Type _) [Magma G] (h: Equation1710 G) : Equation1865 G := fun x y z =>
  let v0 := M y y
  let v1 := M z z
  let v2 := M v1 v1
  let v3 := M v2 v0
  let v4 := M x v0
  let v5 := M v4 v1
  have h6 := R v3
  let v7 := M v0 v5
  let v8 := M x x
  have h9 := h v1 v4 v4
  let v10 := M (M v4 v4) v4
  let v11 := M (M v5 v5) v5
  have h12 := S (h y y v1)
  let v13 := M v2 y
  let v14 := M v8 v4
  T (T (T (T (T (h x v0 v0) (C (T (h (M v0 x) v4 x) (C (S (h v0 x y)) (R v14))) (R (M (M v0 v0) v0)))) (S (h v14 v0 v0))) (h v14 v5 v3)) (C (T (T (T (T (S (h v1 v4 x)) (h v1 v0 v1)) (C (T (h (M v0 v1) v2 v1) (C (S (h v1 v1 y)) (S (h v1 v1 z)))) (T (h v3 v13 y) (C (T (C (T (T (h v13 v0 x) (C (T h12 (h y y y)) (R (M v8 v0)))) (S (h (M v0 y) v0 x))) h6) (S (h y v0 v1))) h12)))) (h v3 v11 v5)) (C (T (C (T (T (h v11 v1 x) (C (T (T (T (C h9 (R v11)) (S (h v10 v5 v5))) (h v10 v5 y)) (C (S h9) (R v7))) (R (M v8 v1)))) (S (h v7 v1 x))) h6) (S (h v5 v0 v1))) (S (h v5 v5 v5)))) (R (M (M v3 v3) v5)))) (S (h v5 v5 v3))

@[equational_result]
theorem Equation1537_implies_Equation658 (G: Type _) [Magma G] (h: Equation1537 G) : Equation658 G := fun x y z =>
  let v0 := M z z
  let v1 := M v0 y
  let v2 := M y v1
  let v3 := M x v2
  have h4 := h z z z
  have h5 := R v0
  have h6 := h z z v0
  have h7 := R z
  have h8 := h v0 z v2
  have h9 := h v0 z y
  have h10 := R v2
  have h11 := R y
  have h12 := R (M x x)
  have h13 := T (T (h v0 x z) (C h12 (T (T (C h7 (T (C h5 h4) (S h6))) h8) (C h5 (C h10 (S h9)))))) (S (h v2 x v0))
  let v14 := M v3 v3
  have h15 := R v3
  have h16 := C h5 (C h15 (T (T (T (T (T (h v14 x y) (C h12 (C h11 (T (T (C (R v14) (T (h y z v1) (C h13 (R (M v1 v2))))) (S (h v1 v3 v2))) (C h13 h11))))) (S (h v2 x y))) (h v2 v0 v0)) (C (R (M v0 v0)) (T (T (C h5 (C h10 h9)) (S h8)) (C h7 (T h6 (C h5 (S h4))))))) (S (h v0 v0 z))))
  have h17 := h v3 z v3
  T (T (h x y v0) (C (R (M y y)) (T (T (T (C h5 (T (T (T (C (R x) h13) h17) h16) (C h13 (C h15 h13)))) (S (h v3 z v2))) h17) h16))) (S (h v3 y v0))

@[equational_result]
theorem Equation3764_implies_Equation41 (G: Type _) [Magma G] (h: Equation3764 G) : Equation41 G := fun x y z =>
  let v0 := M x x
  have h1 := h y z v0
  have h2 := S h1
  let v3 := M z z
  have h4 := h z x z
  have h5 := h v0 y v0
  have h6 := S h5
  have h7 := h x x x
  let v8 := M y y
  have h9 := R v8
  have h10 := C h9 h7
  have h11 := h x y x
  have h12 := h x y z
  have h13 := S h12
  have h14 := h y y y
  have h15 := C (S h14) (S h4)
  have h16 := h v3 v8 v0
  have h17 := h y z y
  have h18 := R v3
  have h19 := h z z y
  have h20 := T (T (T (T (T (T (T (T (T h19 (C h18 (T (T (T (T (T (T h17 h16) h15) h13) h11) h10) h6))) h2) h17) h16) h15) h13) h11) h10) h6
  have h21 := R v0
  let v22 := M y z
  T (T (T (T (T (T (T (T (T (T (T (h x x z) (C h21 (h z x y))) (S (h v22 x v0))) (h v22 x x)) (C h7 (R (M x v22)))) (S (h v22 v0 x))) (C (T (T h1 (C h18 (T (T (T (T (T (T h5 (C h9 (S h7))) (S h11)) h12) (C h14 h4)) (S h16)) (S h17)))) (S h19)) h21)) (S (h x z x))) (h x z z)) (C (T (h z z z) (C h20 h20)) h4)) (S (h v3 (M v0 y) v0))) h2

@[equational_result]
theorem Equation1495_implies_Equation2 (G: Type _) [Magma G] (h: Equation1495 G) : Equation2 G := fun x y =>
  have h0 := S (h y y y)
  let v1 := M y y
  let v2 := M y (M x y)
  let v3 := M x x
  let v4 := M x v3
  have h5 := h v4 v3 x
  have h6 := S h5
  have h7 := h x x x
  have h8 := C h7 h7
  have h9 := T h8 h6
  have h10 := h x x y
  have h11 := S h10
  let v12 := M y x
  let v13 := M x v12
  have h14 := R v13
  have h15 := S h7
  have h16 := C h15 h15
  have h17 := C (T h5 h16) h14
  have h18 := S (h v3 x x)
  have h19 := h v3 x y
  have h20 := S h19
  have h21 := C (T (T (T (T h10 (C h9 h14)) h20) h8) h6) (R v4)
  have h22 := C (T (T (T (T h5 h16) h19) h17) h11) (T (T (T h21 h18) h8) h6)
  have h23 := C (T (T h20 h8) h6) h22
  have h24 := h v13 v4 x
  have h25 := h v12 x y
  T (T (h x y y) (C (T (T (T (T (T (T h25 (C (T (T h24 h23) h22) h14)) (S (h v4 x y))) (C (T (h x y x) (C (T (T (T h25 (C (T (T (T (T (T (T h24 h23) h22) h21) h18) h8) h6) h14)) h17) h11) (R v2))) h9)) (S (h v2 x x))) (h v2 v1 y)) (C (S (h y y x)) h0)) (R (M y v1)))) h0

@[equational_result]
theorem Equation2179_implies_Equation2 (G: Type _) [Magma G] (h: Equation2179 G) : Equation2 G := fun x y =>
  have h0 := S (h y y y)
  let v1 := M y y
  let v2 := M (M y x) y
  have h3 := h x x y
  have h4 := S h3
  have h5 := h x x x
  have h6 := S h5
  have h7 := C h6 h6
  let v8 := M x x
  let v9 := M v8 x
  have h10 := h v9 v8 x
  let v11 := M x y
  let v12 := M v11 x
  have h13 := R v12
  have h14 := C h13 (T h10 h7)
  have h15 := S h10
  have h16 := C h5 h5
  have h17 := S (h v8 x x)
  have h18 := h v8 x y
  have h19 := S h18
  have h20 := C (R v9) (T (T (T (T h3 (C h13 (T h16 h15))) h19) h16) h15)
  have h21 := C (T (T (T h20 h17) h16) h15) (T (T (T (T h10 h7) h18) h14) h4)
  have h22 := C h13 (T (T (T (T (T (T (h v12 v9 x) (C h21 (T (T h19 h16) h15))) h21) h20) h17) h16) h15)
  have h23 := h v11 x y
  T (T (h x y y) (C (R (M v1 y)) (T (T (T (T (T (T (T (T (T (T h23 h22) h19) h16) h15) (h v9 x y)) (C h13 (T (T (T (T h20 h17) h18) h14) h4))) (C h13 (T (h x y x) (C (R v2) (T (T (T h23 h22) h14) h4))))) (S (h v2 x y))) (h v2 v1 y)) (C h0 (S (h y y x)))))) h0

@[equational_result]
theorem Equation4005_implies_Equation41 (G: Type _) [Magma G] (h: Equation4005 G) : Equation41 G := fun x y z =>
  let v0 := M y z
  have h1 := R y
  let v2 := M x x
  let v3 := M z y
  have h4 := h y z v2
  let v5 := M v2 (M v3 v0)
  let v6 := M v2 v3
  have h7 := R v2
  have h8 := h x x x
  have h9 := S h8
  have h10 := R x
  have h11 := h x (M x v2) x
  have h12 := h x x v2
  have h13 := C (C h10 (S h12)) h10
  let v14 := M v2 v2
  have h15 := h x v14 x
  have h16 := T (T h15 h13) h9
  have h17 := h v2 v2 y
  T (T (T (T (T (T (T (T (T h12 (h v14 x v2)) (C (T (T (T (C h7 h16) h17) (C (C h1 h17) h7)) (S (h v2 (M y v14) y))) (R v14))) (S (h v14 y v2))) (C (T (T (T (T (h v2 v2 x) (C h16 (T (T h8 (C (C h10 h12) h10)) (S h15)))) (C h7 (T (T (T h15 h13) (C (C h10 h8) h10)) (S h11)))) (C (T (T h8 (C (C h10 (h x x v0)) h10)) (S (h x (M v0 v2) x))) (T (T h11 (C (C h10 h9) h10)) h9))) (S (h v2 v0 x))) h1)) (C (C h7 h4) h1)) (S (h y v6 v2))) (h y v6 v5)) (C (T (C (R v5) (S h4)) (S (h v0 v3 v2))) h1)) (S (h y z v0))

@[equational_result]
theorem Equation952_implies_Equation928 (G: Type _) [Magma G] (h: Equation952 G) : Equation928 G := fun x y z =>
  let v0 := M y z
  let v1 := M x z
  let v2 := M v0 v1
  let v3 := M y v2
  have h4 := R v0
  have h5 := h v2 y v1
  have h6 := h z v2 y
  let v7 := M (M v1 v2) (M v1 y)
  let v8 := M y v0
  let v9 := M v3 x
  have h10 := R v9
  have h11 := R x
  have h12 := T (C (R v3) h6) (S (h v1 v3 v0))
  have h13 := h z v3 v2
  let v14 := M (M v2 z) (M v2 v3)
  have h15 := h x v0 x
  T (T (T (T (T h15 (C h4 (T (h (M (M x x) (M x v0)) v2 v0) (C h5 (T (T (C (S h15) (R (M v0 v2))) (C h11 (T (T (T (T (T (T (C h4 (T (h v2 z y) (C h13 (R (M v3 v0))))) (S (h v14 v0 v3))) (h v14 z v3)) (C (R z) (T (C (S h13) h12) (C (h z x v3) (R v1))))) (S (h (M (M v3 z) v9) z x))) (C h12 h10)) (C (T (T (h v1 x v0) (C h11 (C (h v2 v0 y) (R (M v0 x))))) (S (h (M v3 v8) x v0))) h10)))) (S (h v8 x v3))))))) (S (h v7 v0 y))) (h v7 y v0)) (C (R y) (C (T (C h4 (T (h v7 z y) (C h6 (C (S h5) h4)))) (S (h (M v0 v3) v0 v2))) (R (M v0 y))))) (S (h v3 y v0))

@[equational_result]
theorem Equation627_implies_Equation2443 (G: Type _) [Magma G] (h: Equation627 G) : Equation2443 G := fun x y =>
  let v0 := M x x
  let v1 := M v0 y
  let v2 := M x v1
  let v3 := M v2 x
  have h4 := h x v2 v3
  have h5 := R v3
  have h6 := h x x x
  have h7 := S h6
  let v8 := M v0 x
  let v9 := M x v8
  have h10 := R v9
  have h11 := R v2
  have h12 := C h11 (C h11 (T (C h7 h10) h7))
  have h13 := h v2 x v9
  let v14 := M v1 v8
  have h15 := h x v1 v14
  have h16 := R v14
  have h17 := h v1 x x
  have h18 := R x
  have h19 := T (C h18 (C (T (C h18 (C h18 (T h17 (C h17 h16)))) (S h15)) (T (T h13 h12) (C (T h13 h12) h5)))) (S h4)
  have h20 := h x x v2
  have h21 := S h13
  have h22 := C h11 (C h11 (T h6 (C h6 h10)))
  have h23 := S h17
  have h24 := S (h y x y)
  let v25 := M y (M (M x y) y)
  have h26 := R v0
  T h20 (C (T (T (T (T h20 (C h18 h19)) (h v0 y v25)) (C h26 (C h26 (T (C h24 (R v25)) h24)))) (C (T (C h18 (T h4 (C h18 (C (T h15 (C h18 (C h18 (T (C h23 h16) h23)))) (T (T (C (T h22 h21) h5) h22) h21))))) (S h20)) (R v1))) h19)

@[equational_result]
theorem Equation627_implies_Equation1224 (G: Type _) [Magma G] (h: Equation627 G) : Equation1224 G := fun x y =>
  let v0 := M x x
  let v1 := M v0 x
  have h2 := h x x v0
  have h3 := S h2
  let v4 := M x (M v1 x)
  have h5 := S (h v0 x v4)
  have h6 := h x v0 x
  have h7 := R v0
  have h8 := C h7 (C h7 (T h6 (C h6 (R v4))))
  have h9 := R v1
  have h10 := h x x x
  have h11 := S h10
  let v12 := M x v1
  have h13 := R v12
  have h14 := T (C h11 h13) h11
  have h15 := R x
  have h16 := h x x v12
  have h17 := h x v0 v1
  have h18 := T h17 (C h15 (C (T h16 (C h15 (C h15 h14))) (T (T (C (T h8 h5) h9) h8) h5)))
  have h19 := S (h y x x)
  let v20 := M y v1
  have h21 := S (h x y y)
  let v22 := M x (M (M y y) y)
  have h23 := C h15 (T (C h15 (C (T (C h15 (C h15 (T h10 (C h10 h13)))) (S h16)) (T (h v0 x v22) (C (T (h v0 x v12) (C h7 (C h7 h14))) (C h7 (T (C h21 (R v22)) h21)))))) (S h17))
  T (T (T (T (T h2 h23) (C (T h2 h23) h15)) (h v1 y v20)) (C h9 (C h9 (T (C h19 (R v20)) h19)))) (C (T (C (T (C h15 h18) h3) h18) h3) (R (M v1 y)))

@[equational_result]
theorem Equation952_implies_Equation914 (G: Type _) [Magma G] (h: Equation952 G) : Equation914 G := fun x y z =>
  let v0 := M y x
  let v1 := M z z
  let v2 := M v0 v1
  let v3 := M y v2
  have h4 := h v3 x v0
  have h5 := h x v2 y
  have h6 := h v0 v2 z
  let v7 := M v0 v3
  have h8 := R v7
  let v9 := M (M z v0) (M z v2)
  have h10 := h v9 v7 v2
  have h11 := R x
  let v12 := M z x
  have h13 := R v1
  have h14 := h x z v3
  let v15 := M (M v3 x) (M v3 z)
  have h16 := h v15 z z
  have h17 := h z x y
  let v18 := M (M y z) v0
  have h19 := R (M x x)
  T (T (T (h x x v3) (C h11 (T (C (T (C (R v3) h5) (S (h v1 v3 v0))) (C (T h4 (C h11 (T (C h8 (C h6 h5)) (S h10)))) (T (T (h x x z) (C h11 (C (T (T (T (T (h v12 x v1) (C h11 (C (T (T (T (T (h (M v1 v12) x x) (C h11 (T (C (S (h z x z)) h19) (C h17 h19)))) (S (h v18 x x))) (h v18 v1 x)) (C h13 (T (C (S h17) (C h14 h13)) (S h16)))) (R (M v1 x))))) (S (h v15 x v1))) h16) (C (R z) (C (S h14) h13))) (R v12)))) (S (h (M x v1) x z))))) (S (h v9 v1 x))))) (C h11 (T h10 (C h8 (C (S h6) (S h5)))))) (S h4)

@[equational_result]
theorem Equation2196_implies_Equation759 (G: Type _) [Magma G] (h: Equation2196 G) : Equation759 G := fun x y z =>
  let v0 := M y x
  let v1 := M v0 z
  let v2 := M z v1
  let v3 := M y v2
  let v4 := M v3 v2
  have h5 := h v0 v3 v2
  have h6 := R v3
  have h7 := h v0 z v1
  have h8 := C (S h7) h6
  have h9 := h y v2 v1
  let v10 := M v4 v2
  have h11 := R v10
  have h12 := T (C h7 h6) (S h9)
  let v13 := M (M y v3) v3
  let v14 := M v0 x
  have h15 := R (M v14 x)
  let v16 := M v3 y
  let v17 := M v0 y
  let v18 := M v17 y
  have h19 := h y x v3
  let v20 := M (M x v3) v3
  let v21 := M x y
  T (T (T (T (h x y v1) (C (R (M (M y v1) v1)) (T (T (h v21 y x) (C (R v14) (T (T (T (T (h (M v21 y) v0 x) (C h15 (T (S (h y x y)) h19))) (S (h v20 v0 x))) (h v20 v0 y)) (C (R v18) (S h19))))) (S (h v18 y x))))) (S (h v17 y v1))) (C h7 (T (T (T (T (T (T h9 h8) (C (T (h v0 v3 y) (C (R (M v16 y)) h12)) (h v3 y v3))) (S (h v13 v16 y))) (h v13 v0 x)) (C h15 (T (T (T (C (R v13) (T h5 (C h11 h12))) (S (h v10 y v3))) (h v10 y v2)) (C (R v4) (T (C h11 (T h9 h8)) (S h5)))))) (S (h v4 v0 x))))) (S (h v3 v2 v1))

@[equational_result]
theorem Equation4176_implies_Equation4541 (G: Type _) [Magma G] (h: Equation4176 G) : Equation4541 G := fun x y z =>
  let v0 := M z x
  let v1 := M v0 y
  have h2 := R v1
  have h3 := R v0
  have h4 := R y
  have h5 := R x
  have h6 := h y z x
  have h7 := C h6 h4
  let v8 := M y z
  have h9 := R v8
  have h10 := S h6
  have h11 := R z
  have h12 := h x v0 y
  have h13 := h y z v8
  have h14 := h v8 (M z v8) y
  let v15 := M x v8
  T (T (T (h x v8 v1) (C (T (T (T (T (T (C (T (C (T h6 (h v1 x v8)) h2) (S (h v8 v15 v1))) h5) (C (T (h v8 v15 v8) (C (S (h v8 x v8)) h9)) h5)) (S (h v8 v8 x))) (h v8 v8 v0)) (C (T (C (h v8 v0 y) h9) (S (h y v1 v8))) h3)) (C (R (M y v1)) (T (h z x v0) (C (T (T (T (T (T (T (C (T (T (T h12 (C h10 h4)) (C h13 h4)) (S h14)) h11) (C (T (T (T (T (T h14 (C (S h13) h4)) h7) (S h12)) (h x v0 v8)) (C (S (h v8 z x)) h9)) h11)) (S (h v8 v8 z))) (h v8 v8 v1)) (C (T (C (T (h v8 v1 x) (C (C h10 h9) h5)) h9) (S (h x v8 v8))) h2)) (C (T (h x v8 y) (C (T (C h7 h5) (S (h y v1 x))) h4)) h2)) (S (h y y v1))) h3)))) h2)) (S (h (M (M y y) v0) y v1))) (S (h v0 y y))

@[equational_result]
theorem Equation3959_implies_Equation3776 (G: Type _) [Magma G] (h: Equation3959 G) : Equation3776 G := fun x y z =>
  let v0 := M z x
  let v1 := M y z
  have h2 := h v1 v0 x
  let v3 := M v0 (M v1 x)
  have h4 := h v3 x y
  have h5 := R y
  let v6 := M v1 v0
  have h7 := R v6
  let v8 := M z v1
  have h9 := h z x v1
  have h10 := S h9
  have h11 := S (h (M x v8) v1 v1)
  have h12 := R v1
  have h13 := C (C h12 h9) h12
  have h14 := h y z v6
  let v15 := M y v6
  have h16 := h x y y
  let v17 := M x y
  let v18 := M y v17
  have h19 := h y v17 v6
  T (T (T (T h16 (C (T (T (T (T (T (T h19 (h (M v17 v15) v6 v6)) (C (T (T (T (T (T (C h7 (S h19)) (h v6 v18 v1)) (C (T (T (T (C (R v18) (T (T h13 h11) h10)) (h v18 v0 y)) (C (C (R v0) (S h16)) h5)) (S (h x v0 y))) h12)) (h (M x v0) v1 x)) (C (T (C (T (T h14 (h (M z v15) v6 v6)) (C (T (T (T (C h7 (S h14)) h13) h11) h10) h7)) (S (h z x x))) (S (h v1 v0 v0))) (R x))) (S (h z v1 x))) h7)) (h v8 v6 z)) (C (C h7 (S (h y z z))) (R z))) (S (h y v6 z))) (C h5 (T h2 h4))) h5)) (S (h (M x (M v3 y)) y y))) (S h4)) (S h2)

@[equational_result]
theorem Equation2891_implies_Equation2677 (G: Type _) [Magma G] (h: Equation2891 G) : Equation2677 G := fun x y z =>
  let v0 := M y z
  have h1 := R y
  let v2 := M z v0
  let v3 := M x y
  let v4 := M v3 v0
  have h5 := h x v3 v4
  have h6 := S h5
  have h7 := R v3
  have h8 := h (M (M x (M v3 v4)) v4) x y
  have h9 := S h8
  have h10 := R x
  have h11 := C (C h5 h1) h10
  let v12 := M v4 z
  let v13 := M v3 x
  have h14 := h v13 v12 y
  have h15 := S h14
  have h16 := R v12
  have h17 := h v3 y z
  have h18 := R v13
  have h19 := C (C h6 h1) h10
  have h20 := C (T (C (T h5 (C (T h8 h19) h7)) h1) (C (C h18 h17) h1)) h16
  have h21 := C (T (C (C h18 (S h17)) h1) (C (T (C (T h11 h9) h7) h6) h1)) h16
  have h22 := h v3 y v3
  let v23 := M v3 (M y v3)
  have h24 := h v23 x y
  T (T (T (T h5 (C (T (T (T h8 h19) h14) h21) h7)) (C (T (T (T h20 h15) (C h22 h10)) (S h24)) h7)) (h (M v23 v3) z v0)) (C (C (T (T (C (T (T (C (T (T (T h24 (C (S h22) h10)) h14) h21) h7) (C (T (T (T h20 h15) h11) h9) h7)) h6) (R v2)) (h (M x v2) y z)) (C (S (h x z v0)) h1)) (R v0)) (R z))

@[equational_result]
theorem Equation2399_implies_Equation3131 (G: Type _) [Magma G] (h: Equation2399 G) : Equation3131 G := fun x y z =>
  let v0 := M y x
  let v1 := M v0 z
  let v2 := M v1 z
  let v3 := M v2 y
  have h4 := R v3
  let v5 := M y (M x (M x y))
  have h6 := R v2
  have h7 := h y y x
  let v8 := M z (M x (M x z))
  have h9 := R v0
  have h10 := h z z x
  let v11 := M v0 (M x (M x v0))
  let v12 := M v0 (M v0 v1)
  have h13 := h v0 v12 v11
  have h14 := R v12
  have h15 := h v0 v0 x
  have h16 := R v11
  have h17 := h z v0 v0
  have h18 := R v1
  have h19 := S h15
  let v20 := M x (M x (M x x))
  have h21 := h x y v20
  have h22 := R y
  have h23 := h x x x
  have h24 := R v20
  have h25 := S h23
  T (T (T (T h21 (C (C h22 (T (C h24 h25) h25)) h22)) (h (M v0 y) v3 y)) (C (C h4 (C h22 (T (T (T (T (C h22 (T (C (C h22 (T h23 (C h24 h23))) h22) (S h21))) h13) (C (T (C h14 (T (C h16 h19) h19)) (S h17)) h14)) (h (M z v12) v3 v1)) (C (T (T (C h4 (C h18 (T (T (C h18 (T (C (T h17 (C h14 (T h15 (C h16 h15)))) h14) (S h13))) (C (C h9 (T h10 (C (R v8) h10))) h9)) (S (h z v0 v8))))) (C (C h6 (T h7 (C (R v5) h7))) h6)) (S (h y v2 v5))) h4)))) h4)) (S (h v3 v3 y))

@[equational_result]
theorem Equation1121_implies_Equation2 (G: Type _) [Magma G] (h: Equation1121 G) : Equation2 G := fun x y =>
  have h0 := h y y x
  have h1 := S h0
  let v2 := M (M y (M y y)) x
  have h3 := h v2 y y
  have h4 := S h3
  have h5 := h (M (M y (M y v2)) y) y x
  have h6 := S h5
  have h7 := R x
  have h8 := R y
  have h9 := C h8 (C (T h0 (C h8 h3)) h7)
  let v10 := M x y
  let v11 := M (M y (M y v10)) y
  let v12 := M y x
  let v13 := M y v12
  have h14 := h v13 y v11
  have h15 := S h14
  have h16 := R v11
  have h17 := C h8 (C (T (C h8 h4) h1) h7)
  have h18 := C h8 (T h5 h17)
  have h19 := C h8 (T h3 h18)
  have h20 := T h0 h19
  have h21 := h v10 y y
  have h22 := C h8 (T h9 h6)
  have h23 := T (C h8 (T h22 h4)) h1
  have h24 := C h23 (T h21 (C h20 h16))
  have h25 := C h8 (T (T (T h24 h15) h9) h6)
  have h26 := C h20 (T (C h23 h16) (S h21))
  have h27 := h v13 y v10
  have h28 := C h8 (T (T (T h5 h17) h14) h26)
  T (T (T (T (T (h x y x) (C h8 (C (C h8 (h v12 y y)) h7))) (S (h (M (M y v13) y) y x))) (C (T (T h22 h28) (C h8 (T (T (T (T h24 h15) h27) h25) h18))) h8)) (C h23 (T (T (T (T h0 h19) (C h8 (T (T (T (T h22 h28) (S h27)) h14) h26))) h25) h4))) h1

@[equational_result]
theorem Equation952_implies_Equation1740 (G: Type _) [Magma G] (h: Equation952 G) : Equation1740 G := fun x y z =>
  let v0 := M z x
  let v1 := M v0 z
  let v2 := M y y
  let v3 := M v2 v1
  have h4 := h v3 v3 z
  let v5 := M z v3
  have h6 := R (M v3 x)
  have h7 := R x
  let v8 := M v2 v3
  have h9 := R v3
  let v10 := M v2 v2
  have h11 := R v2
  have h12 := h y y z
  have h13 := h y y y
  let v14 := M z y
  let v15 := M v14 v14
  have h16 := h v1 v3 v3
  let v17 := M v3 v3
  let v18 := M (M v3 v1) v17
  have h19 := h v2 v0 v2
  T (T (h x v3 z) (C h9 (T (T (T (T (T (T (C (R v0) (T (C (R z) (C h19 (R v1))) (S (h (M v10 (M v2 v0)) z v0)))) (S h19)) (h v2 v1 v2)) (C (T (T (h v1 x v3) (C h7 (C (T (T (T (T (C h9 (T (h v1 v1 v2) (C h16 (R v17)))) (S (h v18 v3 v3))) (h v18 x v3)) (C h7 (C (T (S h16) (h v1 v3 v2)) h6))) (S (h (M v3 v8) x v3))) h6))) (S (h v8 x v3))) (C (T (T (h v10 v2 v2) (C h11 (C (T (T (C h11 (T (T (h v10 x y) (C h7 (C (T (S h13) h12) (R (M y x))))) (S (h v15 x y)))) (C h11 (T (h v15 y y) (C h13 (C (S h12) h11))))) (S (h v10 v2 y))) (R v10)))) (S (h v2 v2 v2))) h9))) (h (M v8 v8) x v3)) (C h7 (C (T (S (h v3 v3 v2)) h4) h6))) (S (h (M v5 v5) x v3))))) (S h4)

@[equational_result]
theorem Equation4087_implies_Equation4099 (G: Type _) [Magma G] (h: Equation4087 G) : Equation4099 G := fun x y z w =>
  have h0 := R z
  let v1 := M x x
  have h2 := h y v1 x
  have h3 := S h2
  have h4 := R v1
  have h5 := h x x y
  have h6 := C h5 h4
  have h7 := h x x x
  have h8 := C (S h7) h4
  have h9 := h x v1 x
  have h10 := S h5
  have h11 := R x
  have h12 := R y
  have h13 := S h9
  have h14 := C h7 h4
  have h15 := C h10 h4
  have h16 := C (T (T (C (T (T (T h2 h15) h14) h13) h4) h14) h13) h12
  have h17 := h y y v1
  have h18 := S h17
  have h19 := C (T (T h9 h8) (C (T (T (T h9 h8) h6) h3) h4)) h12
  let v20 := M (M y y) z
  have h21 := h x x v20
  have h22 := R v20
  have h23 := h y y z
  have h24 := h y v20 v1
  have h25 := h x x w
  have h26 := h w v1 x
  T (T (T (T (T h9 h8) (C h25 h4)) (S h26)) (h w w z)) (C (T (T (T (T (C (T (T (T h26 (C (S h25) h4)) h14) h13) h0) (C (T h21 (C (T (T (T (T (T (C (T (T h9 h8) (C (T (T (T (T h9 h8) h6) h3) h23) h4)) h22) (S h24)) h2) h15) h14) h13) h11)) h0)) (C (T (T (T (T (T (T (T (C (T (T (T (T (T h9 h8) h6) h3) h24) (C (T (T (C (T (T (T (T (S h23) h2) h15) h14) h13) h4) h14) h13) h22)) h11) (S h21)) h9) h8) h6) h3) h17) h16) h0)) (C (T (T (T (T (T (T (T h19 h18) h2) h15) h14) h13) h5) (C (T h19 h18) h11)) h0)) (C (T (T (T (T (T (C (T h17 h16) h11) h10) h9) h8) h6) h3) h0)) (R w))

@[equational_result]
theorem Equation3145_implies_Equation1724 (G: Type _) [Magma G] (h: Equation3145 G) : Equation1724 G := fun x y z =>
  let v0 := M x z
  let v1 := M v0 x
  let v2 := M y y
  let v3 := M v2 v1
  have h4 := h v2 y v3
  have h5 := S h4
  have h6 := R v2
  have h7 := R v3
  have h8 := h v2 y v2
  have h9 := C (S h8) h6
  have h10 := h v2 v2 v2
  have h11 := T h10 h9
  have h12 := C h5 h7
  have h13 := h v3 v2 v2
  have h14 := h v3 y v3
  have h15 := R x
  have h16 := h v0 y v0
  have h17 := R v0
  have h18 := h v2 y v0
  have h19 := C (S h18) h17
  have h20 := h v0 v2 v2
  have h21 := S h20
  have h22 := C h18 h17
  have h23 := S h10
  have h24 := C h8 h6
  have h25 := T h24 h23
  have h26 := C h25 h6
  T (T (T (T (T (T (h x y z) (C (T (T (T (C (T (T (C (T (T h10 h9) (C h11 h6)) h15) (C (T (T (T (T h26 h24) h23) (h v2 v2 x)) (C (C (T (T h26 h24) h23) h15) h6)) h15)) (S (h x y v2))) (R z)) h20) h19) (C h11 h17)) h15)) (C (C h25 h17) h15)) (C (T (T (T h22 h21) h16) (C (C (T h22 h21) h17) h17)) h15)) (C (T (C (C (T h20 h19) h17) h17) (S h16)) h15)) (h v1 y v2)) (C (T (T (T (C (T h14 (C (C (T (C h4 h7) (S h13)) h7) h7)) h6) (C (T (T (T (C (C (T h13 h12) h7) h7) (S h14)) h13) h12) h6)) (C (C h11 h7) h6)) h5) (R v1))

