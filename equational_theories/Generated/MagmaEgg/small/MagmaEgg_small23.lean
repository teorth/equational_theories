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
theorem Equation725_implies_Equation4458 (G: Type _) [Magma G] (h: Equation725 G) : Equation4458 G := fun x y z =>
  let v0 := M (M z y) z
  have h1 := h v0 x y
  have h2 := R x
  let v3 := M y x
  let v4 := M x v3
  have h5 := h x v0 v4
  have h6 := S h5
  have h7 := h (M v0 (M (M v4 x) v4)) x v0
  have h8 := R v0
  have h9 := h y x z
  have h10 := R y
  have h11 := h x y v3
  have h12 := C h8 (T (C h8 (T (T (C (S h11) h10) (C h2 (T h9 (C h2 (C h5 h8))))) (S h7))) h6)
  have h13 := h (M y (M (M v3 x) v3)) v0 y
  have h14 := h v0 x v0
  let v15 := M x (M (M v0 v0) v0)
  T (C h2 (T (T (T (T (C h10 (T h11 (C h10 (T (T h13 h12) (C h14 h2))))) (S (h v15 y x))) (h v15 x x)) (C h2 (T (C h2 (T (T (C (S h14) h2) (C h8 (T h5 (C h8 (T (T h7 (C h2 (T (C h2 (C h6 h8)) (S h9)))) (C h11 h10)))))) (S h13))) (C h2 (T (T h13 h12) (C h1 h2)))))) (S (h (M x (M (M y v0) y)) x x)))) (S h1)

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
theorem Equation1090_implies_Equation3617 (G: Type _) [Magma G] (h: Equation1090 G) : Equation3617 G := fun x y z =>
  let v0 := M z x
  let v1 := M v0 y
  let v2 := M z v1
  have h3 := R y
  let v4 := M (M y (M v1 x)) x
  have h5 := h v0 v1 v4
  have h6 := R v4
  have h7 := h y v1 x
  have h8 := R v0
  have h9 := R v1
  let v10 := M x y
  have h11 := S (h y v10 x)
  let v12 := M (M y (M v10 x)) x
  have h13 := R v10
  have h14 := S h7
  have h15 := S (h x v0 x)
  let v16 := M (M x (M v0 x)) x
  have h17 := R z
  T (T (h v10 z y) (C h17 (C (T (T (T (T (T (C h13 (C (T (T (h z v0 v16) (C h8 (T (C (C h17 h15) (R v16)) h15))) (C (T h5 (C h9 (T (C (C h8 h14) h6) h14))) (T (h x v10 v12) (C h13 (T (C (C (R x) h11) (R v12)) h11))))) h3)) (S (h (M v1 y) v10 y))) (C h9 (T h7 (C (C h8 h7) h6)))) (S h5)) (h v0 v2 y)) (C (R v2) (C (S (h z v0 y)) h3))) h3))) (S (h v2 z y))

@[equational_result]
theorem Equation1507_implies_Equation2519 (G: Type _) [Magma G] (h: Equation1507 G) : Equation2519 G := fun x y z =>
  let v0 := M x z
  let v1 := M v0 y
  let v2 := M y v1
  let v3 := M v2 z
  have h4 := S (h z v2 v3)
  let v5 := M v3 v2
  let v6 := M v0 (M v0 v3)
  let v7 := M v3 v5
  let v8 := M v2 y
  let v9 := M v0 (M v0 v0)
  let v10 := M x v0
  have h11 := h z x v3
  let v12 := M v3 (M v3 x)
  let v13 := M z x
  T (T (T (T (h x z v2) (C (T (T (T (T (T (T (T (h v13 z x) (C (T (T (T (T (h (M z v13) v0 x) (C (T (S (h z x z)) h11) (R (M x v10)))) (S (h v12 v0 x))) (h v12 v0 v0)) (C (S h11) (R v9))) (R v10))) (S (h v9 z x))) (h v9 v8 v7)) (C (T (T (C (R v8) (T (h v9 v1 y) (C (S (h y v0 v0)) (R (M y v2))))) (S (h y v2 y))) (h y v2 v3)) (R (M v7 (M v7 v8))))) (S (h v7 v8 v7))) (h v7 v3 v0)) (C h4 (R v6))) (R (M v2 v3)))) (S (h v6 z v2))) (h v6 v5 v3)) (C (S (h v2 v3 v0)) h4)

@[equational_result]
theorem Equation2349_implies_Equation3131 (G: Type _) [Magma G] (h: Equation2349 G) : Equation3131 G := fun x y z =>
  have h0 := R y
  let v1 := M y x
  let v2 := M v1 z
  let v3 := M x (M x (M v2 v2))
  have h4 := R v1
  have h5 := h v2 x v2
  let v6 := M v1 v1
  let v7 := M v1 (M v1 v6)
  have h8 := h v1 v1 v1
  let v9 := M v2 z
  let v10 := M v9 y
  let v11 := M x (M x (M v10 v10))
  have h12 := h y v11 v9
  have h13 := R v9
  have h14 := h v10 x v10
  have h15 := R v11
  have h16 := R v2
  have h17 := S h14
  have h18 := S (h v1 x v1)
  let v19 := M x (M x v6)
  T (T (T (h x v19 y) (C (T (C (R v19) h18) h18) (T h12 (C (T (C h15 h17) h17) h13)))) (h (M v1 (M v10 v9)) v2 y)) (C (C h16 (T (T (C h16 (C h0 (T (T (C h4 (T (C (T h14 (C h15 h14)) h13) (S h12))) (C (T h8 (C (R v7) h8)) h0)) (S (h x v7 y))))) (C (T h5 (C (R v3) h5)) h4)) (S (h z v3 v1)))) h0)

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
theorem Equation684_implies_Equation3567 (G: Type _) [Magma G] (h: Equation684 G) : Equation3567 G := fun x y z =>
  let v0 := M z x
  let v1 := M v0 z
  let v2 := M y v1
  have h3 := S (h v2 v2 x)
  let v4 := M v2 (M (M v2 x) x)
  let v5 := M v1 v2
  have h6 := S (h v1 v1 x)
  let v7 := M v1 (M (M v1 x) x)
  have h8 := T (C h6 (R v7)) h6
  have h9 := R y
  have h10 := R v1
  let v11 := M x v1
  have h12 := R z
  have h13 := S (h v0 v0 x)
  let v14 := M v0 (M (M v0 x) x)
  let v15 := M x v0
  have h16 := S (h x x x)
  let v17 := M x (M (M x x) x)
  have h18 := R x
  T (T (C (T (T (h x x z) (C h18 (T (T (C h18 (C (T (C h18 (T (T (T (h z x v17) (C h18 (C h12 (T (C h16 (R v17)) h16)))) (h v15 v0 v14)) (C (R v0) (C (R v15) (T (C h13 (R v14)) h13))))) (S (h v0 x v0))) h12)) (h v11 v1 v7)) (C h10 (C (R v11) h8))))) (S (h v1 x v1))) h9) (C h10 (T (T (T (h y v1 v7) (C h10 (C h9 h8))) (h v5 v2 v4)) (C (R v2) (C (R v5) (T (C h3 (R v4)) h3)))))) (S (h v2 v1 v2))

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
theorem Equation2196_implies_Equation4026 (G: Type _) [Magma G] (h: Equation2196 G) : Equation4026 G := fun x y z =>
  let v0 := M z y
  let v1 := M z v0
  let v2 := M v1 x
  let v3 := M v2 x
  let v4 := M (M v0 v2) v2
  let v5 := M (M y v1) v1
  let v6 := M x y
  have h7 := h x y v1
  have h8 := R (M (M v6 x) x)
  let v9 := M y z
  let v10 := M v6 y
  let v11 := M v10 y
  let v12 := M (M v6 z) z
  T (T (T (T (T (T (C (h x y v6) (h y v6 z)) (S (h v12 (M y v6) v6))) (h v12 x x)) (C (R (M (M x x) x)) (T (T (T (C (R v12) h7) (S (h v5 v6 z))) (h v5 v6 y)) (C (R v11) (S h7))))) (S (h v11 x x))) (C (R v10) (T (T (h y z v0) (C (R (M v1 v0)) (T (T (T (T (h v9 z x) (C (R (M (M z x) x)) (T (T (T (T (T (h (M v9 z) v6 x) (C h8 (S (h x y z)))) (C h8 h7)) (S (h v5 v6 x))) (h v5 v0 v2)) (C (R v4) (S (h z y v1)))))) (S (h v4 z x))) (h v4 v1 x)) (C (R v3) (S (h z v0 v2)))))) (S (h v3 z v0))))) (S (h v2 x y))

@[equational_result]
theorem Equation3211_implies_Equation1181 (G: Type _) [Magma G] (h: Equation3211 G) : Equation1181 G := fun x y z =>
  let v0 := M z x
  let v1 := M z v0
  let v2 := M v1 y
  let v3 := M y v2
  have h4 := R z
  have h5 := R v1
  have h6 := S (h v1 v2 y)
  have h7 := C (h y v1 y) (R v2)
  have h8 := h z v0 x
  have h9 := S h8
  have h10 := R v0
  have h11 := h x z x
  have h12 := C h11 h10
  have h13 := h x z v0
  have h14 := R x
  have h15 := h v0 x v0
  have h16 := h z v1 v0
  have h17 := h v0 z v0
  have h18 := C (T (C (T (T (T (C (T (T (T h7 h6) (h v1 v0 v1)) (C (C (C (T (C h17 h5) (S h16)) h5) h5) h10)) h4) (S (h v0 z v1))) h15) (C (C (C (T h12 h9) h10) h10) h14)) h4) (S h13)) h10
  have h19 := h v0 v3 z
  T (T (T h13 (C (T (C (C (C (T h8 (C (S h11) h10)) h10) h10) h14) (S h15)) h4)) (C (T h19 (C (T (T (T (T h18 h12) h9) h16) (C (T (T (S h17) h19) (C (T (T h18 h12) h9) (T h7 h6))) h5)) (R v3))) h4)) (S (h v3 z v1))

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
theorem Equation684_implies_Equation4640 (G: Type _) [Magma G] (h: Equation684 G) : Equation4640 G := fun x y z =>
  let v0 := M (M y z) z
  have h1 := S (h v0 v0 x)
  let v2 := M v0 (M (M v0 x) x)
  let v3 := M y v0
  have h4 := R v3
  have h5 := R y
  have h6 := h y y z
  have h7 := S h6
  let v8 := M x y
  have h9 := R v8
  let v10 := M v8 x
  let v11 := M v10 (M (M v10 x) x)
  have h12 := h v10 v10 x
  let v13 := M x (M (M x x) x)
  have h14 := h x x x
  have h15 := R v10
  have h16 := R x
  have h17 := S (h x x y)
  let v18 := M x (M v8 y)
  T (T (T (T (T (h v10 x v18) (C h16 (T (T (T (T (C h15 (T (C h17 (R v18)) h17)) (C h15 (T (T (h x v8 x) (C h9 (T (C h16 (C h15 (T h14 (C h14 (R v13))))) (S (h v10 x v13))))) (C h9 (T h12 (C h12 (R v11))))))) (S (h v8 v10 v11))) (h v8 y v3)) (C h5 (C h9 (T (C h7 h4) h7)))))) (S (h y x y))) h6) (C h5 (T (h v3 v0 v2) (C (R v0) (C h4 (T (C h1 (R v2)) h1)))))) (S (h v0 y v0))

@[equational_result]
theorem Equation711_implies_Equation4421 (G: Type _) [Magma G] (h: Equation711 G) : Equation4421 G := fun x y z =>
  let v0 := M z (M (M z x) x)
  let v1 := M z y
  have h2 := h z v1 v0
  have h3 := S h2
  have h4 := R v0
  have h5 := h z z x
  have h6 := R v1
  have h7 := C h6 (C h6 (T h5 (C h5 h4)))
  have h8 := h y y x
  have h9 := S h8
  let v10 := M y (M (M y x) x)
  have h11 := R v10
  have h12 := T (C h9 h11) h9
  have h13 := R x
  have h14 := h y x v10
  have h15 := T h14 (C h13 (C h13 h12))
  have h16 := S h5
  have h17 := C h6 (C (C (T h2 (C h6 (C h6 (T (C h16 h4) h16)))) h15) h15)
  have h18 := C h6 (C h6 h12)
  have h19 := h y v1 v10
  have h20 := S h14
  have h21 := C h13 (C h13 (T h8 (C h8 h11)))
  T (T (T (T (T h21 h20) h19) h18) h17) (C h6 (T (T (T (C (C (T h7 h3) (T h21 h20)) (T (T (T (T h21 h20) h19) h18) h17)) (S (h (M v1 (M v1 z)) v1 (M x (M x y))))) h7) h3))

@[equational_result]
theorem Equation1507_implies_Equation2925 (G: Type _) [Magma G] (h: Equation1507 G) : Equation2925 G := fun x y z =>
  let v0 := M x z
  let v1 := M y v0
  let v2 := M v1 y
  have h3 := h v0 y v1
  let v4 := M v2 v1
  have h5 := h z v2 v1
  let v6 := M v2 z
  have h7 := R v6
  let v8 := M z v6
  let v9 := M v2 v6
  let v10 := M y v1
  let v11 := M x v0
  have h12 := h z x v6
  let v13 := M v6 (M v6 x)
  let v14 := M z x
  T (T (T (h x z v2) (C (T (T (T (T (h v14 z x) (C (T (T (T (T (h (M z v14) v0 x) (C (T (S (h z x z)) h12) (R (M x v11)))) (S (h v13 v0 x))) (h v13 v0 y)) (C (S h12) (R v10))) (R v11))) (S (h v10 z x))) (h v10 (M v0 x) v0)) (C (S (h x v0 y)) (S (h z x v0)))) (R v9))) (C (R v0) (T (T (T (h v9 v8 z) (C (S (h v6 z v2)) (T (C (T h5 (C h7 (S h3))) (R (M z v8))) (S (h v0 v6 z))))) (C h7 h3)) (S h5)))) (C (T (h v0 v4 v2) (C (T (C (R v4) h3) (S (h v1 v2 v1))) (S (h y v1 v2)))) (R z))

@[equational_result]
theorem Equation2958_implies_Equation1374 (G: Type _) [Magma G] (h: Equation2958 G) : Equation1374 G := fun x y z =>
  let v0 := M (M z y) z
  let v1 := M v0 x
  let v2 := M (M v1 (M v1 y)) y
  let v3 := M y v1
  have h4 := R y
  have h5 := R v3
  have h6 := h y v1 y
  have h7 := R v1
  have h8 := S (h y x y)
  let v9 := M (M x (M x y)) y
  have h10 := S (h v3 x v3)
  let v11 := M (M x (M x v3)) v3
  let v12 := M (M x (M x z)) z
  have h13 := h z x z
  have h14 := S (h v0 v0 v0)
  let v15 := M (M v0 (M v0 v0)) v0
  T (T (T (h x v15 v0) (C (C (T (C (R v15) h14) h14) (R x)) (T (C (C (T h13 (C (R v12) h13)) h4) (R z)) (S (h y v12 z))))) (C (T (T (h v1 v11 v3) (C (T (T (C (T (C (R v11) h10) h10) h7) (C (T (h v3 v9 y) (C (C (T (C (R v9) h8) h8) h5) h4)) h7)) (S (h y y v1))) h5)) (C (T h6 (C (R v2) h6)) h5)) h4)) (S (h v3 v2 y))

@[equational_result]
theorem Equation3804_implies_Equation4544 (G: Type _) [Magma G] (h: Equation3804 G) : Equation4544 G := fun x y z =>
  let v0 := M z y
  let v1 := M y z
  let v2 := M v0 v1
  have h3 := S (h v1 v0 v2)
  have h4 := h y y z
  have h5 := C (T (h z y y) (C h4 (R v0))) (T (h y z y) (C (R v1) h4))
  have h6 := S h4
  let v7 := M v0 x
  let v8 := M x y
  let v9 := M y v7
  let v10 := M v7 z
  T (T (T (T (T (h x v1 y) (h (M y v1) v8 v0)) (C (T (C (T (T (T (T (T (h z y v7) (C (h v7 y z) (h z v7 y))) (S (h v9 v10 v0))) (h v9 v10 v2)) (C (T (C (T (T h5 h3) (S (h z z y))) (R v10)) (S (h v7 z z))) (T (C (R v9) h6) (S (h y v7 y))))) (S (h y z v7))) (R v8)) (S (h x z y))) (S (h z v1 y)))) (h (M x z) (M z v1) v7)) (C (T (C (R v7) (T (T (h z v1 v0) (C (T (T (T (T h6 (h y y y)) (C h4 h4)) (C (T h5 h3) (R v2))) (S (h v0 v0 v1))) (R (M z v0)))) (S (h z v0 v0)))) (S (h z x v0))) (S (h v0 z x)))) (S (h v0 x z))

@[equational_result]
theorem Equation684_implies_Equation2170 (G: Type _) [Magma G] (h: Equation684 G) : Equation2170 G := fun x y z =>
  let v0 := M z y
  let v1 := M y z
  let v2 := M v1 x
  let v3 := M v2 v0
  have h4 := S (h v3 v3 x)
  let v5 := M v3 (M (M v3 x) x)
  let v6 := M v0 v3
  have h7 := S (h v0 v0 x)
  let v8 := M v0 (M (M v0 x) x)
  have h9 := R v2
  let v10 := M z (M (M z x) x)
  have h11 := h z z x
  have h12 := R z
  let v13 := M v1 (M v2 x)
  let v14 := M z v1
  have h15 := h v1 v1 x
  have h16 := R v1
  let v17 := M x (M (M x x) x)
  have h18 := h x x x
  T (T (T (h x v1 x) (C h16 (T (C (R x) (C h9 (T h18 (C h18 (R v17))))) (S (h v2 x v17))))) (C (T (h v1 z v1) (C h12 (T (T (T (C h16 (C (R v14) (T h15 (C h15 (R v13))))) (S (h v14 v1 v13))) (C h12 (C (R y) (T h11 (C h11 (R v10)))))) (S (h y z v10))))) (T (T (T (h v2 v0 v8) (C (R v0) (C h9 (T (C h7 (R v8)) h7)))) (h v6 v3 v5)) (C (R v3) (C (R v6) (T (C h4 (R v5)) h4)))))) (S (h v3 v0 v3))

@[equational_result]
theorem Equation1507_implies_Equation1304 (G: Type _) [Magma G] (h: Equation1507 G) : Equation1304 G := fun x y z =>
  let v0 := M x z
  let v1 := M v0 z
  let v2 := M v1 y
  let v3 := M y v2
  have h4 := R (M x (M x v2))
  let v5 := M v2 v3
  let v6 := M v2 v5
  let v7 := M v2 y
  let v8 := M v2 (M v2 v1)
  let v9 := M v0 (M v0 v0)
  let v10 := M x v0
  have h11 := h z x v3
  let v12 := M v3 (M v3 x)
  let v13 := M z x
  T (T (T (T (T (h x z v0) (C (T (T (T (T (h v13 z x) (C (T (T (T (T (h (M z v13) v0 x) (C (T (S (h z x z)) h11) (R (M x v10)))) (S (h v12 v0 x))) (h v12 v0 v0)) (C (S h11) (R v9))) (R v10))) (S (h v9 z x))) (h v9 v1 v2)) (C (S (h z v0 v0)) (R v8))) (R (M v0 v1)))) (S (h v8 z v0))) (h v8 v2 x)) (C (T (T (T (S (h y v1 v2)) (h y v2 v3)) (C (T (T (h v7 v2 x) (C (T (h (M v2 v7) v3 v2) (C (S (h v2 y v2)) (R v6))) h4)) (S (h v6 v2 x))) (R (M v3 (M v3 v2))))) (S (h v5 v2 v3))) h4)) (S (h v3 v2 x))

@[equational_result]
theorem Equation3120_implies_Equation4450 (G: Type _) [Magma G] (h: Equation3120 G) : Equation4450 G := fun x y z =>
  let v0 := M y z
  let v1 := M v0 z
  have h2 := S (h v1 v1 v0)
  have h3 := R v0
  have h4 := R v1
  have h5 := R z
  have h6 := h v0 z v0
  have h7 := h z y v0
  have h8 := C (S h7) h3
  have h9 := h y v0 v0
  have h10 := C (T (C (C (C (T h9 h8) h5) h3) h3) (S h6)) h5
  have h11 := C (C (C (T (C h7 h3) (S h9)) h5) h3) h3
  have h12 := S (h v0 v0 v1)
  have h13 := h v0 v0 z
  have h14 := C (T (T (T (C (C (T h6 h11) h5) h5) (S h13)) h6) h11) h4
  have h15 := C (C (T (C (T (T (T (C (T (T (h z v1 v1) (C (T (T (T (C h14 h4) h12) h13) (C h10 h5)) h4)) h14) h4) h12) h6) h11) h5) h10) h4) h4
  have h16 := h v1 z v1
  let v17 := M y x
  T (T (T (T (T (C (h x y v17) (R v17)) (S (h y v17 v17))) h9) h8) (C (T (h z v0 v0) (C (T (T (T (C (C (T h16 h15) h3) h3) h2) h16) h15) h3)) h3)) h2

@[equational_result]
theorem Equation1710_implies_Equation481 (G: Type _) [Magma G] (h: Equation1710 G) : Equation481 G := fun x y z =>
  let v0 := M z z
  let v1 := M y v0
  let v2 := M x v1
  let v3 := M y v2
  let v4 := M v3 v3
  let v5 := M v4 v3
  let v6 := M v0 v0
  let v7 := M (M v2 v2) y
  let v8 := M v0 v1
  have h9 := h v1 v0 v3
  let v10 := M v4 v0
  have h11 := h v1 x v3
  let v12 := M v4 x
  have h13 := h x x v3
  T (T h13 (C (T (T (T (C (T (h x v0 v3) (C (T (T (h (M v0 x) v2 x) (C (T (S (h v1 x z)) h11) (R (M (M x x) v2)))) (S (h v12 v2 x))) (R v10))) h13) (S (h v10 v12 x))) (h v10 (M v0 v3) v3)) (C (S (h v3 v0 v3)) (S (h v3 v3 z)))) (T (T (h v12 v2 v0) (C (T (T (T (T (T (S h11) (h v1 v1 v0)) (C (T (T (T (C h9 (h v1 v1 z)) (S (h v10 v8 v1))) (h v10 v8 z)) (C (S h9) (T (C (h v0 y v2) (R v8)) (S (h v7 v1 z))))) (R (M v6 v1)))) (S (h v7 v1 v0))) (h v7 v3 v3)) (C (S (h v2 y v2)) (R v5))) (R (M v6 v2)))) (S (h v5 v2 v0))))) (S (h v3 v3 v3))

@[equational_result]
theorem Equation1774_implies_Equation928 (G: Type _) [Magma G] (h: Equation1774 G) : Equation928 G := fun x y z =>
  let v0 := M x z
  let v1 := M (M y z) v0
  let v2 := M y v1
  have h3 := h v2 v2 z
  let v4 := M (M v2 v2) z
  have h5 := R x
  have h6 := h v0 y v1
  have h7 := h z y v0
  have h8 := R v2
  have h9 := T (C h8 h7) (S h6)
  have h10 := h v2 x z
  have h11 := R (M v0 x)
  let v12 := M (M x v2) z
  have h13 := R z
  have h14 := C h8 (S h7)
  have h15 := R (M v0 z)
  have h16 := h x v2 z
  let v17 := M (M v2 x) z
  have h18 := R v17
  have h19 := T h6 h14
  have h20 := h x x z
  T (T h20 (C h19 (T (T (T (T (T (T (T (T (T (h (M (M x x) z) v0 x) (C h11 (T (C (S h20) h5) (C (T h16 (C h9 h18)) h5)))) (S (h v17 v0 x))) (h v17 v0 z)) (C h15 (C (T (C h19 h18) (S h16)) h13))) (C h15 (T (T h6 h14) (C h10 h13)))) (S (h v12 v0 z))) (h v12 v0 x)) (C h11 (T (C (S h10) h5) (C (T h3 (C h9 (R v4))) h5)))) (S (h v4 v0 x))))) (S h3)

@[equational_result]
theorem Equation3211_implies_Equation3364 (G: Type _) [Magma G] (h: Equation3211 G) : Equation3364 G := fun x y z =>
  let v0 := M x z
  let v1 := M z v0
  let v2 := M y v1
  have h3 := R y
  have h4 := R v2
  let v5 := M x y
  have h6 := h y v1 v5
  have h7 := S h6
  have h8 := R v1
  have h9 := R v5
  have h10 := R v0
  have h11 := h z x z
  have h12 := C (S h11) h10
  have h13 := h x v0 z
  have h14 := h x v5 y
  have h15 := h y x y
  have h16 := C (C (C (T (T (T (C h15 h9) (S h14)) h13) h12) h9) h9) h3
  have h17 := h v5 y v5
  have h18 := S (h v5 v5 v1)
  have h19 := C (C (C (T h6 (C (T (C (C (C (T (T (T (C h11 h10) (S h13)) h14) (C (S h15) h9)) h9) h9) h3) (S h17)) h8)) h8) h9) h9
  have h20 := h v1 v2 v5
  T (C (T (T (T h13 h12) h20) (C (T (T (T (T (C (T h19 h18) h8) (C (T h17 h16) h8)) h7) (h y v2 v1)) (C (T (T (S (h v1 y v1)) h20) (C (T (C (T (T (T h19 h18) h17) h16) h8) h7) h4)) h4)) h4)) h3) (S (h v2 y v2))

@[equational_result]
theorem Equation684_implies_Equation2992 (G: Type _) [Magma G] (h: Equation684 G) : Equation2992 G := fun x y z =>
  let v0 := M y (M (M y x) x)
  have h1 := h y y x
  let v2 := M y (M z y)
  let v3 := M v2 x
  let v4 := M v3 z
  let v5 := M x (M (M x v4) v4)
  have h6 := h x x v4
  have h7 := R v2
  have h8 := R x
  let v9 := M v3 x
  let v10 := M v3 (M v9 x)
  let v11 := M x v3
  have h12 := h v3 v3 x
  have h13 := R v3
  have h14 := h x x x
  have h15 := S h14
  let v16 := M x (M (M x x) x)
  have h17 := R v16
  have h18 := T h14 (C h14 h17)
  T (T (h x v3 x) (C h13 (T (C h8 (C (R v9) h18)) (S (h v9 x v16))))) (C h13 (T (T (T (T (T (T (C h13 (T (T (h x v2 x) (C h7 (T (C h8 (C h13 h18)) (S (h v3 x v16))))) (C (T (h v2 x v16) (C h8 (C h7 (T (C h15 h17) h15)))) h13))) (C h13 (C (R v11) (T h12 (C h12 (R v10)))))) (S (h v11 v3 v10))) (C h8 (C h7 (T h6 (C h6 (R v5)))))) (S (h v2 x v5))) (C (R y) (C (R z) (T h1 (C h1 (R v0)))))) (S (h z y v0))))

@[equational_result]
theorem Equation684_implies_Equation3131 (G: Type _) [Magma G] (h: Equation684 G) : Equation3131 G := fun x y z =>
  let v0 := M y x
  let v1 := M y (M v0 x)
  let v2 := M (M v0 z) z
  let v3 := M v2 y
  have h4 := h v3 y v1
  have h5 := R v1
  have h6 := h y y x
  have h7 := R v3
  have h8 := R y
  have h9 := S h6
  have h10 := R v2
  have h11 := S (h v3 v3 x)
  let v12 := M v3 (M (M v3 x) x)
  have h13 := S (h v2 v2 x)
  let v14 := M v2 (M (M v2 x) x)
  let v15 := M v3 v2
  let v16 := M x (M (M x x) x)
  have h17 := h x x x
  T (T (T (T (h x y x) (C h8 (T (C (R x) (C (R v0) (T h17 (C h17 (R v16))))) (S (h v0 x v16))))) (C h8 (T (T (T (T (h v0 v3 v2) (C h7 (T (T (S (h v15 v0 z)) (h v15 v2 v14)) (C h10 (C (R v15) (T (C h13 (R v14)) h13)))))) (S (h v2 v3 v2))) (h v2 v3 v12)) (C h7 (T (T (C h10 (T (C h11 (R v12)) h11)) (C h10 (T h4 (C h8 (C h7 (T (C h9 h5) h9)))))) (S (h y v2 y))))))) (C h8 (C h7 (T h6 (C h6 h5))))) (S h4)

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
theorem Equation2335_implies_Equation2199 (G: Type _) [Magma G] (h: Equation2335 G) : Equation2199 G := fun x y z =>
  let v0 := M y z
  let v1 := M y x
  let v2 := M v0 z
  let v3 := M v2 v1
  have h4 := h v3 v0 y
  have h5 := R y
  have h6 := R v0
  let v7 := M v0 (M v0 v3)
  have h8 := R z
  have h9 := h v3 v0 z
  have h10 := R v2
  have h11 := R x
  have h12 := h x y z
  let v13 := M y (M y (M x z))
  have h14 := h x v2 y
  T (T h14 (C (T (T (T (h (M v2 (M v2 (M x y))) x y) (C (T (T (T (C h11 (C h11 (S h14))) (h (M x (M x x)) x z)) (C (C h11 (C h11 (T (T (T (T (C (C h11 (C h11 h12)) h8) (S (h v13 x z))) (h v13 y z)) (C (T (T (T (C h5 (C h5 (S h12))) (C (T (T (T (h y x z) (C (C h11 (C h11 (h v0 v2 z))) h8)) (S (h (M v2 (M v2 v2)) x z))) (C h10 (C h10 (h v2 v0 v1)))) (R v1))) (S (h v7 v2 v1))) (C h6 (C h6 h9))) h8)) (C (C h6 (C h6 (S h9))) h8)))) h8)) (S (h v7 x z))) h5)) (C (C h6 (C h6 h4)) h5)) (S (h (M v0 (M v0 (M v3 y))) v0 y))) h5)) (S h4)

@[equational_result]
theorem Equation2755_implies_Equation14 (G: Type _) [Magma G] (h: Equation2755 G) : Equation14 G := fun x y =>
  let v0 := M x y
  let v1 := M y v0
  let v2 := M v1 v1
  let v3 := M v2 v0
  let v4 := M y y
  have h5 := h v0 v2 y
  have h6 := R y
  have h7 := h v1 v1 v1
  have h8 := R v2
  have h9 := C h8 (T (C h7 h6) (S h5))
  have h10 := R v1
  have h11 := h y (M v0 v0) x
  have h12 := S h11
  have h13 := R x
  have h14 := h v0 v0 v0
  have h15 := C h14 h13
  have h16 := T h15 h12
  let v17 := M v0 x
  have h18 := C (S h14) h13
  have h19 := R v4
  have h20 := h v17 y y
  T (T (T (h x v4 v3) (C (T (T (T (C (C h19 (C h6 (T h11 h18))) (S (h y v1 x))) (S h20)) h15) h12) (C h8 (T h5 (C (S h7) h6))))) (C (T (T (T h11 h18) h20) (C (C h19 (C h6 h16)) (T (T (T h11 h18) (h v17 v1 v1)) (C (T (C h8 (C h10 h16)) h9) h10)))) h9)) (S (h v1 v4 v3))

@[equational_result]
theorem Equation2944_implies_Equation1171 (G: Type _) [Magma G] (h: Equation2944 G) : Equation1171 G := fun x y z =>
  let v0 := M y z
  let v1 := M z v0
  let v2 := M v1 x
  have h3 := R v2
  let v4 := M (M x (M x y)) y
  have h5 := S (h y v4 v0)
  have h6 := R v0
  have h7 := h y x y
  have h8 := C (C (T h7 (C (R v4) h7)) h6) h6
  let v9 := M (M x (M x z)) z
  have h10 := h z v9 v0
  have h11 := h z x z
  have h12 := R v9
  have h13 := R y
  have h14 := C (C h13 (C h13 (T (C (C (T h11 (C h12 h11)) h6) h6) (S h10)))) h6
  have h15 := S h11
  have h16 := C (C (T (C h12 h15) h15) h6) h6
  let v17 := M (M x (M x v1)) v1
  have h18 := h v1 x v1
  T (h x v1 v2) (C (T (T (T (T (T (C (C (T h18 (C (R v17) h18)) h3) h3) (S (h v1 v17 v2))) (C (T (T (T h10 h16) (h (M v1 v0) y v0)) (C (T (T h14 h8) h5) (C h13 (T h10 h16)))) h6)) h14) h8) h5) h3)

@[equational_result]
theorem Equation2956_implies_Equation3674 (G: Type _) [Magma G] (h: Equation2956 G) : Equation3674 G := fun x y =>
  have h0 := R x
  let v1 := M x x
  let v2 := M y x
  let v3 := M v2 v1
  have h4 := h x v3 v1
  let v5 := M x v1
  let v6 := M v5 x
  have h7 := h x v6 x
  have h8 := h x x x
  have h9 := R v6
  have h10 := R v1
  have h11 := h v2 x x
  have h12 := S h11
  let v13 := M v5 v2
  have h14 := R v13
  have h15 := C (C (T (C h14 h12) h12) h10) h10
  have h16 := h v1 v13 v2
  have h17 := R v3
  have h18 := h x v1 x
  have h19 := S (h y x x)
  let v20 := M v5 y
  have h21 := S h8
  have h22 := S h16
  have h23 := C (C (T h11 (C h14 h11)) h10) h10
  T (T (T (T (C (T h4 (C (C (T (T (C h17 (T h23 h22)) h23) h22) (T h7 (C (C (T (C h9 h21) h21) h0) h0))) h0)) h0) (S h18)) (h x v20 y)) (C (C (T (C (R v20) h19) h19) h0) h0)) (C (R v2) (T h18 (C (T (C (C (T (T h16 h15) (C h17 (T h16 h15))) (T (C (C (T h8 (C h9 h8)) h0) h0) (S h7))) h0) (S h4)) h0)))

@[equational_result]
theorem Equation2958_implies_Equation3417 (G: Type _) [Magma G] (h: Equation2958 G) : Equation3417 G := fun x y z =>
  let v0 := M y x
  let v1 := M z v0
  let v2 := M z v1
  have h3 := R v2
  let v4 := M v2 v2
  have h5 := h v2 x v2
  have h6 := S h5
  let v7 := M (M x (M x v2)) v2
  have h8 := R v7
  let v9 := M x y
  let v10 := M (M v9 (M v9 y)) y
  have h11 := R y
  have h12 := R v0
  have h13 := h y v9 y
  have h14 := S (h y z y)
  let v15 := M (M z (M z y)) y
  let v16 := M v2 v1
  T (T (T (T (T (C (T (T (h x z v0) (C (T (C (T (T (T (T (h v2 v2 v1) (C (T (T (C (C (T h5 (C h8 h5)) (R v16)) h3) (S (h v16 v7 v2))) (h v16 z v0)) (R v1))) (S (h v0 v2 v1))) (h v0 v15 y)) (C (C (T (C (R v15) h14) h14) h12) h11)) (R x)) (S (h y y x))) h12)) (C (T h13 (C (R v10) h13)) h12)) h11) (S (h v0 v10 y))) (h v0 v2 v2)) (C (S (h v4 z v0)) h3)) (C (T (h v4 v7 v2) (C (C (T (C h8 h6) h6) (R v4)) h3)) h3)) (S (h v2 v2 v2))

@[equational_result]
theorem Equation3211_implies_Equation4640 (G: Type _) [Magma G] (h: Equation3211 G) : Equation4640 G := fun x y z =>
  let v0 := M y z
  let v1 := M v0 z
  have h2 := h v1 v0 z
  have h3 := R v0
  have h4 := R v1
  have h5 := R z
  have h6 := h v1 v0 v1
  have h7 := h y y z
  have h8 := C (S h7) h5
  have h9 := h z v1 y
  have h10 := h v0 z v1
  have h11 := h z y z
  have h12 := h y v0 z
  let v13 := M x y
  have h14 := S h12
  have h15 := C h11 h3
  have h16 := S h9
  have h17 := C h7 h5
  have h18 := C (T (C (T (T (C (T h6 (C (C (C (T (C h17 h4) h16) h4) h4) h3)) h5) (S h10)) h17) h4) h16) h3
  have h19 := R v13
  T (T (T (T (T (C (T (h v13 v1 v13) (C (C (C (T (C (T (T (T (T h2 h18) h15) h14) (h y x y)) h19) (S (h x v13 y))) h19) h19) (T (T (T h2 h18) h15) h14))) (R x)) (S (h y x v13))) h12) (C (S h11) h3)) (C (T h9 (C (T (T h8 h10) (C (T (C (C (C (T h9 (C h8 h4)) h4) h4) h3) (S h6)) h5)) h4)) h3)) (S h2)

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
theorem Equation3791_implies_Equation3489 (G: Type _) [Magma G] (h: Equation3791 G) : Equation3489 G := fun x y z =>
  let v0 := M y z
  let v1 := M v0 z
  have h2 := R v0
  have h3 := h z y y
  have h4 := h y y x
  have h5 := S h4
  have h6 := h y x x
  have h7 := h x y x
  have h8 := C (S h7) (S h6)
  let v9 := M x x
  have h10 := h (M y x) (M x y) v9
  have h11 := h x x y
  T (T (T (T (T (T (T (h x x v0) (h (M v0 x) (M x v0) v9)) (C (S (h x v0 x)) (S (h v0 x x)))) (S (h v0 v0 x))) (h v0 v0 z)) (C (h z v0 y) (T (T (T (T (T (h v0 z y) (h (M y v0) (M z y) v1)) (C (T (T (S (h z y v0)) h3) (C h2 (T (T (T h4 (C h7 h6)) (S h10)) (S h11)))) (S (h y v0 z)))) (S (h v9 y v0))) (h v9 y z)) (C (T (h z v9 v0) (C (R v1) (T (T (h v9 v0 v9) (C (T (T (T (T (S (h x x x)) h11) h10) h8) h5) (T (C h2 (T (T (T h11 h10) h8) h5)) (S h3)))) (S (h y z y))))) h2)))) (S (h (M v0 y) (M v1 v0) v0))) (S (h y v1 v0))

@[equational_result]
theorem Equation3804_implies_Equation4525 (G: Type _) [Magma G] (h: Equation3804 G) : Equation4525 G := fun x y z =>
  let v0 := M y x
  have h1 := h v0 z y
  let v2 := M y z
  have h3 := h v2 (M v0 y) v0
  have h4 := R (M v2 v0)
  have h5 := h v0 x y
  have h6 := h v2 x v0
  let v7 := M x x
  have h8 := h y x x
  let v9 := M y v0
  let v10 := M x z
  let v11 := M v0 v2
  have h12 := h y x z
  let v13 := M v2 v2
  let v14 := M x v2
  T (T (T (T (T (T (T (T (T (T (h x v2 v2) (h v13 v14 v0)) (C (T (T (C h8 (h x v2 x)) (S (h v14 v0 v7))) (S (h y v2 x))) (T (T (C (R v13) h12) (S (h (M z x) v2 v2))) (S h12)))) (C (T (T (T (T (T (h y v2 v0) (h v11 v9 v2)) (C (R (M v2 v9)) (T (C (R v11) (h y z x)) (S (h v10 v2 v0))))) (S (h v10 v9 v2))) (h v10 v9 (M v0 x))) (C (S (h y x v0)) (S (h v0 z x)))) h8)) (S (h v7 (M v0 z) v0))) (C (R v7) (T (T (T h1 h3) (C (S h5) h4)) (S h6)))) (S (h v2 x x))) h6) (C h5 h4)) (S h3)) (S h1)

@[equational_result]
theorem Equation492_implies_Equation3567 (G: Type _) [Magma G] (h: Equation492 G) : Equation3567 G := fun x y z =>
  let v0 := M z x
  let v1 := M v0 z
  let v2 := M y v1
  have h3 := h z x z
  have h4 := R v0
  have h5 := C h4 (S h3)
  have h6 := h x v0 z
  let v7 := M x y
  have h8 := S (h x y v7)
  have h9 := S h6
  have h10 := C h4 h3
  have h11 := R v7
  have h12 := h v1 v2 y
  have h13 := h y v1 y
  have h14 := R v2
  have h15 := R y
  have h16 := T h6 h5
  have h17 := C h15 (T (T (T (C h11 (C h11 (T (h v2 v2 x) (C h14 (C h14 (C (R x) (T (C h16 (T (h v2 y v2) (C h15 (C h14 (C h14 (T (C h14 h13) (S h12))))))) (S (h y v1 v2))))))))) (S (h v7 v7 v2))) (h v7 v1 v7)) (C (T h10 h9) (C h11 (C h11 (T (C h11 (T (T h10 h9) (h x y x))) (S (h y v7 x)))))))
  have h18 := h y v2 v7
  T (C h16 (T h18 (C h14 (T (T (T (T (T h17 h8) h6) h5) h12) (C h14 (T (T (S h13) h18) (C h14 (T (T (T h17 h8) h6) h5)))))))) (S (h v2 v1 v2))

@[equational_result]
theorem Equation1293_implies_Equation1470 (G: Type _) [Magma G] (h: Equation1293 G) : Equation1470 G := fun x y z =>
  let v0 := M z y
  let v1 := M z v0
  have h2 := R v1
  let v3 := M x y
  let v4 := M v3 v1
  let v5 := M (M (M v4 v4) x) x
  have h6 := h v3 v1 v5
  have h7 := R v5
  have h8 := h v4 v4 x
  let v9 := M (M v1 v4) v1
  have h10 := R v4
  have h11 := R v0
  have h12 := R x
  have h13 := S h8
  have h14 := S (h x x x)
  let v15 := M (M (M x x) x) x
  have h16 := R v15
  let v17 := M v4 v1
  have h18 := S (h v0 v0 x)
  let v19 := M (M (M v0 v0) x) x
  T (T (T (h x v1 v4) (C h2 (C (C (T (C h12 (T (C (T (h z y v19) (C (R y) (T (C h18 (R v19)) h18))) h11) (C (C (T (T (h y v17 v15) (C (R v17) (T (C (T (C (S (h x y v1)) h16) h14) h16) h14))) (C (C (C (T h6 (C h2 (T (C h13 h7) h13))) h2) h2) h12)) h11) h11))) (S (h (M v9 v1) x v0))) h10) h10))) (S (h v9 v1 v4))) (C (T (C h2 (T h8 (C h8 h7))) (S h6)) h2)

@[equational_result]
theorem Equation1507_implies_Equation1293 (G: Type _) [Magma G] (h: Equation1507 G) : Equation1293 G := fun x y z =>
  let v0 := M x y
  let v1 := M v0 z
  let v2 := M v1 z
  let v3 := M y v2
  let v4 := M x v0
  have h5 := R v4
  let v6 := M y v3
  have h7 := R (M x (M x z))
  have h8 := h z v1 v3
  let v9 := M v3 (M v3 v1)
  let v10 := M x (M x v1)
  let v11 := M z v0
  let v12 := M z v11
  have h13 := h y x v3
  let v14 := M v3 (M v3 x)
  let v15 := M y x
  T (T (h x y x) (C (T (T (T (T (T (T (T (h v15 y x) (C (T (T (T (T (h (M y v15) v0 x) (C (T (S (h y x y)) h13) (R (M x v4)))) (S (h v14 v0 x))) (h v14 v0 z)) (C (S h13) (R v12))) h5)) (S (h v12 y x))) (h v12 (M v0 x) v0)) (C (S (h x v0 z)) (S (h y x v0)))) (h v0 z x)) (C (T (T (T (T (T (T (T (h v11 z x) (C (T (h v12 v1 x) (C (S (h z v0 z)) (R v10))) h7)) (S (h v10 z x))) (h v10 v2 x)) (C (T (S (h z v1 x)) h8) (R (M x (M x v2))))) (S (h v9 v2 x))) (h v9 v2 y)) (C (S h8) (R v6))) h7)) (S (h v6 z x))) h5)) (S (h v3 y x))

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
theorem Equation1761_implies_Equation3617 (G: Type _) [Magma G] (h: Equation1761 G) : Equation3617 G := fun x y z =>
  let v0 := M z x
  let v1 := M v0 y
  let v2 := M z v1
  let v3 := M x y
  let v4 := M (M x v0) y
  let v5 := M v2 v3
  have h6 := h v5 v1 v4
  have h7 := R v4
  have h8 := h v1 v1 v2
  have h9 := R v1
  have h10 := h z x y
  have h11 := R (M v1 v1)
  have h12 := h v3 v1 v1
  have h13 := R (M v1 v2)
  have h14 := R v5
  have h15 := C h14 (T (C h13 (T h12 (C h11 (C (S h10) h9)))) (S h8))
  have h16 := h v1 v2 v3
  have h17 := h x v0 y
  let v18 := M (M v3 v0) y
  have h19 := S h17
  have h20 := h v3 v0 y
  T (T (h v3 v3 v2) (C (R (M v3 v2)) (C (T (T (T (C h20 (T h20 (C (T (T h16 h15) (C (T h6 (C h19 (T (C (T (C h14 (T h8 (C h13 (T (C h11 (C h10 h9)) (S h12))))) (S h16)) h7) h19))) h9)) (R v18)))) (S (h (M x x) v1 v18))) (C h17 (T h17 (C (T h16 h15) h7)))) (S h6)) (R v2)))) (S (h v2 v3 v2))

@[equational_result]
theorem Equation2552_implies_Equation3810 (G: Type _) [Magma G] (h: Equation2552 G) : Equation3810 G := fun x y z =>
  let v0 := M z x
  let v1 := M z y
  let v2 := M v1 v0
  have h3 := R v2
  have h4 := S (h v1 x v2)
  have h5 := R v0
  let v6 := M x v2
  let v7 := M x (M v6 v1)
  let v8 := M x y
  have h9 := h y z v2
  have h10 := h v0 z y
  have h11 := R z
  have h12 := h z x v0
  have h13 := S h12
  have h14 := R x
  let v15 := M x (M (M x v0) z)
  have h16 := R v15
  have h17 := h x v15 v0
  have h18 := T (C (T h12 (C h16 (C h12 h14))) h5) (S h17)
  T (T (h v8 z y) (C (C h11 (T (T (T (C (C h11 (T (T (T (T h9 (C (C h11 (S h10)) h3)) (C h18 h3)) (h v6 z v0)) (C (C h11 (C h18 (T (C (T (T h17 (C (T (C h16 (C h13 h14)) h13) h5)) (C h11 h10)) h3) (S h9)))) h5))) (R v8)) (S (h v0 z v8))) (h v0 v7 v2)) (C (T (C (R v7) (C h4 h5)) h4) h3))) (R y))) (S (h v2 z y))

@[equational_result]
theorem Equation2714_implies_Equation3214 (G: Type _) [Magma G] (h: Equation2714 G) : Equation3214 G := fun x y z =>
  let v0 := M y z
  let v1 := M v0 z
  let v2 := M v1 y
  let v3 := M v2 x
  have h4 := h v3 (M (M x v2) (M x v3)) v3
  have h5 := R v3
  have h6 := h v2 x v3
  have h7 := R z
  have h8 := S h6
  have h9 := R v1
  let v10 := M x v0
  have h11 := h v0 x v1
  have h12 := h v0 (M (M x y) v10) v0
  have h13 := R v0
  have h14 := h y x v0
  have h15 := S h14
  T (T (T (T (h x y z) (C (T (C (T (C (h y v1 v3) (R x)) (S (h (M v1 v3) v2 x))) (T (T (T h12 (C (C h15 h15) h13)) (h (M (M y y) v0) v0 z)) (C (T (T (C (C h13 (T (C (C h14 h14) h13) (S h12))) h9) (C (C h11 h11) h9)) (S (h v1 (M v10 (M x v1)) v1))) h7))) (C (C h9 (T h4 (C (C h8 h8) h5))) (R (M v1 z)))) h7)) (S (h (M (M v2 v2) v3) v1 z))) (C (C h6 h6) h5)) (S h4)

@[equational_result]
theorem Equation2944_implies_Equation2917 (G: Type _) [Magma G] (h: Equation2944 G) : Equation2917 G := fun x y z =>
  have h0 := R z
  let v1 := M x y
  let v2 := M y v1
  have h3 := S (h v2 x v2)
  let v4 := M (M x (M x v2)) v2
  have h5 := R v1
  let v6 := M (M x v1) y
  have h7 := h y v6 v2
  have h8 := S h7
  have h9 := R v2
  have h10 := h y x y
  have h11 := R v6
  have h12 := C (C (T h10 (C h11 h10)) h9) h9
  have h13 := R x
  have h14 := S h10
  have h15 := C (C h13 (C h13 (T h7 (C (C (T (C h11 h14) h14) h9) h9)))) h5
  have h16 := S (h x x x)
  let v17 := M (M x (M x x)) x
  have h18 := C (C (T (C (R v17) h16) h16) h5) h5
  have h19 := h x v17 v1
  T (T (T (T (T h19 h18) h15) (C (T (T (T (C (T (T h19 h18) h15) (C h13 (T h12 h8))) (S (h (M (M y v2) v2) x v1))) h12) h8) h5)) (h v2 v4 z)) (C (C (T (C (R v4) h3) h3) h0) h0)

@[equational_result]
theorem Equation3211_implies_Equation4013 (G: Type _) [Magma G] (h: Equation3211 G) : Equation4013 G := fun x y z =>
  let v0 := M y z
  let v1 := M z v0
  let v2 := M v1 x
  have h3 := R v0
  have h4 := h z y z
  have h5 := C (S h4) h3
  have h6 := h y v0 z
  have h7 := T h6 h5
  have h8 := R v2
  let v9 := M x y
  have h10 := h y x v9
  have h11 := S h10
  have h12 := R x
  have h13 := S h6
  have h14 := C h4 h3
  have h15 := R v9
  have h16 := h x v9 y
  have h17 := h y x y
  have h18 := h v9 v1 v9
  have h19 := C (T (T (T (C (C (C (T (T (T h14 h13) h10) (C (T (C (C (C (T h16 (C (T (T (S h17) h6) h5) h15)) h15) h15) h7) (S h18)) h12)) h12) h15) h15) (S (h v9 v9 x))) h18) (C (C (C (T (C (T (T h14 h13) h17) h15) (S h16)) h15) h15) (T h14 h13))) h12
  have h20 := h x v2 v9
  T (C (T h20 (C (T (T (T (T (T h19 h11) h6) h5) (h v1 v2 x)) (C (T (T (S (h x v1 x)) h20) (C (T (T (T h19 h11) h6) h5) h8)) h8)) h8)) h7) (S (h v2 v1 v2))

@[equational_result]
theorem Equation508_implies_Equation1929 (G: Type _) [Magma G] (h: Equation508 G) : Equation1929 G := fun x y z =>
  let v0 := M y x
  let v1 := M y v0
  let v2 := M z z
  have h3 := h v2 v1 z
  have h4 := R v1
  have h5 := h v1 v1 v2
  have h6 := h x x v2
  have h7 := h v2 x z
  have h8 := h v2 v2 v2
  have h9 := S h8
  have h10 := h v2 v2 z
  have h11 := S h5
  have h12 := C h4 h3
  have h13 := R v2
  have h14 := T h12 h11
  have h15 := S h10
  have h16 := R v0
  have h17 := R y
  have h18 := R x
  T (T (T (h x y x) (C h17 (C h17 (T (C h18 (T (T (C h18 (T (T h6 (C h18 (S h7))) (C h18 (T h8 (C h13 (T (T h15 (h v2 y v0)) (C h17 (T (C h17 (T (T (C h13 (T (T (T (C h16 (T (h v0 v0 v2) (C h16 (S (h v2 v0 z))))) (C h16 (C h16 (T (T h8 (C h13 h15)) (C h13 (T (h v2 (M v1 v2) z) (C h14 (T (T (T (C h14 (R (M v2 v2))) (C h4 (T (C h13 h10) h9))) h12) h11)))))))) (S (h v2 v0 v1))) h10)) h9) (h v2 y z))) (S (h y y v2)))))))))) (S (h v2 x y))) h7)) (S h6))))) h5) (C h4 (S h3))

@[equational_result]
theorem Equation3791_implies_Equation3553 (G: Type _) [Magma G] (h: Equation3791 G) : Equation3553 G := fun x y z =>
  let v0 := M x z
  let v1 := M v0 z
  let v2 := M y v1
  let v3 := M v1 v0
  let v4 := M v0 y
  have h5 := h v1 v0 y
  let v6 := M z x
  have h7 := T (T (T (h v6 z v0) (C (T (S (h z z x)) (h z z v0)) (h z v0 z))) (S (h (M z v0) (M z z) v1))) (S (h v0 z z))
  let v8 := M x y
  let v9 := M v8 v0
  let v10 := M v1 x
  let v11 := M y z
  T (T (T (T (T (T (T (T (h x y z) (h v6 v11 v2)) (C (T (T (h v2 v6 z) (C (R (M z v2)) h7)) (S (h v2 v0 z))) (R (M v11 v2)))) (S (h v0 v11 v2))) (h v0 v11 v1)) (C (R v3) (T (T (T (T (C (h y z x) (T (T (T (h v0 z v1) (C h5 (T (T (h z v1 x) (h v0 v10 v8)) (C (R v9) (T (T (C (h v1 x y) (h x y v1)) (S (h v8 v10 v2))) (S (h y v1 x))))))) (S (h v4 v9 v2))) (S (h y v8 v0)))) (S (h v6 y v8))) (h v6 y y)) (C (T (T (h y v6 z) (C (R (M z y)) h7)) (S (h y v0 z))) (R (M y y)))) (S (h v0 y y))))) (C h5 (h v0 y v1))) (S (h v4 v3 v2))) (S (h y v1 v0))

