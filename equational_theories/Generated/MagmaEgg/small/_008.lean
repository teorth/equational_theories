import equational_theories.Equations.All
import equational_theories.Magma

private def congr_op {G: Type _} [Magma G] {a b c d: G} (h1: a = b) (h2: c = d): a ◇ c = b ◇ d := by
  rw [h1, h2]
private abbrev T := @Eq.trans
private abbrev S := @Eq.symm
private abbrev R := @Eq.refl
private abbrev M := @Magma.op
private abbrev C := @congr_op

@[equational_result]
theorem Equation978_implies_Equation3286 (G: Type _) [Magma G] (h: Equation978 G) : Equation3286 G := fun x y z =>
  let v0 := M z z
  let v1 := M y v0
  let v2 := M x x
  have h3 := h y v2 y
  have h4 := h v2 v1 z
  have h5 := h y v0 x
  have h6 := R v1
  have h7 := h y v0 z
  have h8 := S h7
  have h9 := C h6 h8
  have h10 := h v0 v1 z
  have h11 := R y
  have h12 := C h11 (T (T (T h10 h9) (C h6 h5)) (S h4))
  let v13 := M y y
  have h14 := R v13
  have h15 := R v2
  have h16 := h v13 v1 x
  let v17 := M v0 v1
  have h18 := R v17
  have h19 := S h10
  have h20 := C h6 h7
  have h21 := h y v2 v1
  let v22 := M v1 v1
  have h23 := R v22
  have h24 := h v22 v1 x
  let v25 := M y v1
  let v26 := M v25 v25
  have h27 := C h6 (S h5)
  have h28 := C h11 (T (T (T h4 h27) h20) h19)
  T (T (T (T h4 h27) (C h6 (T h3 (C h15 (C h14 h28))))) (S h16)) (C h11 (T (T (T (T h7 (C (T (T (T h10 h9) (C h6 (T h21 (C h15 (C h23 h28))))) (S h24)) h18)) (h (M v22 v17) y v25)) (C h11 (C (T (T (T (h v26 v1 x) (C h6 (T (C h15 (C (R v26) h12)) (S (h y v2 v25))))) h20) h19) (T (T (C (T (C (T (T (T h24 (C h6 (T (C h15 (C h23 h12)) (S h21)))) h20) h19) h18) h8) h11) h16) (C h6 (T (C h15 (C h14 h12)) (S h3))))))) (S (h v1 y z))))

@[equational_result]
theorem Equation1537_implies_Equation4461 (G: Type _) [Magma G] (h: Equation1537 G) : Equation4461 G := fun x y z =>
  let v0 := M z z
  let v1 := M v0 y
  have h2 := R x
  have h3 := h y z y
  let v4 := M x (M y x)
  let v5 := M y y
  have h6 := h v5 x v4
  have h7 := h y y x
  have h8 := h y z x
  have h9 := S h8
  have h10 := R v4
  have h11 := R (M x x)
  have h12 := h v0 x v4
  have h13 := R y
  have h14 := R v0
  have h15 := T (C h14 (C h13 (T (T h12 (C h11 (C h10 (T h9 h7)))) (S h6)))) (S h3)
  have h16 := h y z v0
  have h17 := C h2 (C (T h16 (C h14 h15)) h2)
  have h18 := S h12
  have h19 := C h14 (C h13 (T (T h6 (C h11 (C h10 (T (S h7) h8)))) h18))
  have h20 := h v1 z v0
  have h21 := h y v1 x
  have h22 := h (M v1 v1) x v4
  have h23 := R v1
  have h24 := h v1 z v1
  have h25 := R v5
  T (T (T (h v4 y v0) (C h25 (C h14 (C h17 h14)))) (C h25 (T (T (T (C h14 (C (T (T (C h2 (C (T h20 (C h14 (T (C h14 (C h23 (T (T h12 (C h11 (C h10 (T h9 h21)))) (S h22)))) (S h24)))) h2)) (C h2 (C (T (T (T (T (T (C h14 (T h24 (C h14 (C h23 (T (T h22 (C h11 (C h10 (T (S h21) h8)))) h18))))) (S h20)) (C h14 (T h3 h19))) (S h16)) h3) h19) h2))) (C h2 (C h15 h2))) h14)) (C h14 (C h10 (T (T h12 (C h11 (C h10 (T h9 (h y v4 x))))) (S (h (M v4 v4) x v4)))))) (S (h v4 z v4))) h17))) (S (h v1 y x))

@[equational_result]
theorem Equation3959_implies_Equation4369 (G: Type _) [Magma G] (h: Equation3959 G) : Equation4369 G := fun x y z =>
  let v0 := M y x
  have h1 := h z v0 x
  have h2 := S h1
  have h3 := R x
  let v4 := M z v0
  have h5 := R v0
  have h6 := R v4
  let v7 := M y z
  let v8 := M x v7
  let v9 := M v0 v8
  have h10 := R v8
  have h11 := h y x z
  have h12 := S h11
  have h13 := R z
  have h14 := h x v7 v0
  have h15 := S h14
  let v16 := M x v0
  let v17 := M v7 v16
  have h18 := R v17
  have h19 := h v8 v17 z
  have h20 := h v7 v16 v8
  have h21 := S h20
  have h22 := h (M v16 (M v7 v8)) v8 v8
  have h23 := h v7 v16 v4
  T (T (T (T (T h14 (h v17 v0 v0)) (C (C h5 h15) h5)) (h v9 v0 x)) (C (C h5 (T (T (T (C (T (T (T (T (T (T (C (T (T (T h11 (C (T h14 (C h18 h11)) h13)) (S h19)) (C h10 h20)) h10) (S h22)) h21) h23) (h (M v16 (M v7 v4)) v4 v4)) (C (T (T (T (C h6 (T (T (T (S h23) h20) h22) (C (T (T (T (C h10 h21) h19) (C (T (C h18 h12) h15) h13)) h12) h10))) (h v4 v9 x)) (C (T (C (R v9) (S (h y z x))) (S (h x v0 v7))) h3)) (S (h y x x))) h6)) (C h5 h1)) h3) (C (T (C h5 h2) (C h5 (T (T h1 (h (M v0 (M z x)) x x)) (C (C h3 h2) h3)))) h3)) (S (h (M x v4) v0 x))) (S (h z x v0)))) h3)) h2

@[equational_result]
theorem Equation2519_implies_Equation3211 (G: Type _) [Magma G] (h: Equation2519 G) : Equation3211 G := fun x y z =>
  let v0 := M y z
  let v1 := M v0 z
  let v2 := M v1 x
  let v3 := M v2 y
  let v4 := M y v2
  let v5 := M v4 v3
  have h6 := h y v3 v2
  have h7 := R v1
  have h8 := R v3
  have h9 := R x
  have h10 := R v0
  have h11 := h x z v2
  have h12 := R v2
  have h13 := h v0 x z
  have h14 := R z
  have h15 := h y v1 v2
  let v16 := M v1 (M v4 v1)
  have h17 := R y
  have h18 := h y z z
  have h19 := S h18
  have h20 := h y v2 v2
  let v21 := M v2 (M v4 v2)
  have h22 := h z v1 y
  have h23 := h z z v1
  T (T (T (T (T (T (T (T (T (T h11 (C (C h14 (T (T (S h13) (C h17 (T h22 (C (C h7 (T (C (C h14 h18) h7) (S h23))) h17)))) (C h20 (T (C (C h7 (T h23 (C (C h14 h19) h7))) h17) (S h22))))) h12)) (S (h v21 z v2))) (h v21 y v2)) (C (T (C h17 (T (C (S h20) h17) (C h18 h17))) (C h17 (T (C h19 h17) (C h15 h17)))) h12)) (S (h v16 y v2))) (h v16 x v2)) (C (C h9 (T (C (S h15) h9) (C h6 h9))) h12)) (S (h (M v3 v5) x v2))) (C (T (h v3 v1 y) (C (T (C (C h10 (T (h z v2 v0) (C (C h12 (T (C (C h14 h13) h12) (S h11))) h10))) (T (C (C h8 (T (h y x v3) (C (C h9 (S (h v1 y x))) h8))) h7) (S (h x v3 v1)))) (S (h v2 v0 x))) h6)) (R v5))) (S (h v3 v2 v5))

@[equational_result]
theorem Equation4176_implies_Equation3703 (G: Type _) [Magma G] (h: Equation4176 G) : Equation3703 G := fun x y z =>
  let v0 := M z y
  let v1 := M y z
  have h2 := R x
  let v3 := M v0 x
  have h4 := R y
  have h5 := R z
  let v6 := M x x
  have h7 := S (h v0 v6 v0)
  have h8 := R v0
  let v9 := M v1 v0
  have h10 := h z y v1
  let v11 := M (M y v1) z
  have h12 := C (T (T h10 (h v11 v1 v0)) (C (T (T (h v9 v11 v1) (C (T (T (C (S h10) (R v9)) (h v0 v9 x)) (C (S (h x v1 v0)) h2)) (R v1))) (S (h x x v1))) h8)) h8
  let v13 := M y v0
  let v14 := M x v0
  T (T (h x x x) (C (T (T (T (T (T (T (C (h x x v0) h2) (S (h v0 v14 x))) (h v0 v14 v0)) (C (S (h v0 x v0)) h8)) (h v3 v0 y)) (C (C (T (T (T (T (T (C (T (T (T (h z y v0) (h (M v13 z) v0 v0)) (C (T (T (C (T (h v0 v0 v0) (C (T (C h12 h8) h7) h8)) (T (T (T (h v13 z v6) (C (C (R (M z v6)) (T (h y v0 x) (C (S (h x z y)) h2))) (R v6))) (S (h (M (M x z) x) z v6))) (S (h x x z)))) (S (h v0 v0 v6))) h12) h8)) h7) h4) (S (h v6 z y))) (C (T (T (h x x y) (C (T (C (h x y z) h2) (S (h z v1 x))) h4)) (C (T (h z v1 z) (C (S (h z y z)) h5)) h4)) h5)) (S (h y v0 z))) (h y v0 y)) (C (S (h y z y)) h4)) (R v3)) h4)) (S (h v3 v1 y))) h2)) (S (h v1 v0 x))

@[equational_result]
theorem Equation1561_implies_Equation725 (G: Type _) [Magma G] (h: Equation1561 G) : Equation725 G := fun x y z =>
  let v0 := M z x
  let v1 := M v0 z
  let v2 := M y v1
  let v3 := M y v2
  let v4 := M z v0
  have h5 := h v1 v4 v2
  have h6 := h v2 v0 z
  have h7 := h y z v0
  have h8 := T (C h7 h6) (S h5)
  let v9 := M v3 v0
  let v10 := M x z
  have h11 := R v10
  have h12 := h z x z
  have h13 := S h12
  have h14 := h v4 v1 v0
  have h15 := h v0 z v0
  let v16 := M v1 v0
  have h17 := R v16
  have h18 := C h11 (T (C h17 h15) (S h14))
  have h19 := h v16 x z
  have h20 := h x z v0
  let v21 := M x v1
  have h22 := R v21
  have h23 := h v4 v1 z
  have h24 := h z z v0
  have h25 := R v1
  have h26 := h v10 v0 z
  have h27 := h v1 x z
  T (T (T (T (T h20 (C (T (T h23 (C (T (C h25 h12) (S h26)) (T (T (T (S h24) h12) (C h11 (T h14 (C h17 (S h15))))) (S h19)))) (S h27)) h22)) (C (T h5 (C (S h7) (S h6))) h22)) (h (M v3 v21) v0 v1)) (C (R (M v0 v1)) (T (T (C (T (T (C h8 h22) (C (T (T h27 (C (T h26 (C h25 h13)) (T (T (T h19 h18) h13) h24))) (S h23)) h22)) (S h20)) (T (T h19 h18) h13)) (h v10 y v2)) (C (R v3) (T (T (C h11 (T (h (M v2 y) v3 v0) (C (R v9) (S (h v0 v2 y))))) (S (h v9 x z))) (C h8 (R v0))))))) (S (h v3 v0 v1))

@[equational_result]
theorem Equation895_implies_Equation1098 (G: Type _) [Magma G] (h: Equation895 G) : Equation1098 G := fun x y z =>
  let v0 := M z y
  let v1 := M x v0
  let v2 := M v1 z
  have h3 := R v2
  have h4 := h y v0 v0
  have h5 := R (M v0 v0)
  let v6 := M v0 x
  have h7 := h v0 v0 (M (M y x) v6)
  have h8 := h y v0 x
  have h9 := R v0
  have h10 := T (C h9 (C h8 h8)) (S h7)
  have h11 := R y
  have h12 := h z y y
  have h13 := h z z y
  have h14 := S h8
  have h15 := T h7 (C h9 (C h14 h14))
  have h16 := C (T h4 (C h15 (T (C (T (C h11 h15) (S h12)) h5) (S h13)))) h3
  have h17 := R v1
  let v18 := M y v2
  have h19 := S (h v2 v18 x)
  have h20 := T (C h3 (T (h v18 v18 (M (M v2 x) (M v18 x))) (C (R v18) (C h19 h19)))) (S (h y v2 v2))
  have h21 := h v0 v1 x
  T (T (T (T (h x v0 v0) (C h9 (T (C h17 (C h21 h21)) (S (h v1 v1 (M v6 (M v1 x))))))) (C h9 (T (h v1 v2 v18) (C (T (h v2 v18 v18) (C (T h16 (C (C h10 (R z)) h3)) (T (C h20 (R (M v18 v18))) (S (h y y v2))))) (T (T (C (R (M v1 v18)) h20) (C (T (C h17 h16) (S (h (M v0 (M y y)) v1 z))) h11)) (C h10 h11)))))) (S (h (M (M v0 z) v2) v0 y))) (C (T (C h9 (T h13 (C (T h12 (C h11 h10)) h5))) (S h4)) h3)

@[equational_result]
theorem Equation1906_implies_Equation2 (G: Type _) [Magma G] (h: Equation1906 G) : Equation2 G := fun x y =>
  let v0 := M y y
  have h1 := h y (M x v0) y
  have h2 := S h1
  have h3 := R v0
  have h4 := h y x y
  have h5 := C h4 h3
  have h6 := S (h (M y v0) y x)
  have h7 := R x
  let v8 := M y x
  have h9 := h y (M x v8) x
  have h10 := R v8
  have h11 := h y x x
  have h12 := h v8 y y
  have h13 := T (T (S h12) (C (T h9 (C (S h11) h10)) h7)) (C (T (T (T (C h11 h10) (S h9)) h1) (C (S h4) h3)) h7)
  have h14 := R y
  have h15 := C (C h14 h13) h13
  let v16 := M v8 y
  have h17 := h (M y v16) y v16
  let v18 := M x x
  have h19 := R v18
  have h20 := h x x x
  have h21 := h x (M x v18) x
  have h22 := T h21 (C (S h20) h19)
  let v23 := M x y
  have h24 := h x (M x v23) y
  have h25 := R v23
  have h26 := h x x y
  have h27 := S h21
  have h28 := C h20 h19
  let v29 := M v18 x
  have h30 := h v18 y x
  T (T (T (T (T (T (T (T (T (T h21 (C (T (C (T h28 h27) h19) (C h7 h30)) h30)) (S (h (M y v29) x v29))) (C h14 (T (C (T (T (C h22 h7) (C (T (T (T h28 h27) h24) (C (S h26) h25)) h7)) (C (T (C h26 h25) (S h24)) h22)) h22) (S (h x x v18))))) h12) (C (T (T (T (T h17 h15) h6) h5) h2) (R v16))) h17) h15) h6) h5) h2

@[equational_result]
theorem Equation4208_implies_Equation41 (G: Type _) [Magma G] (h: Equation4208 G) : Equation41 G := fun x y z =>
  let v0 := M x x
  have h1 := R y
  have h2 := S (h (M v0 z) y x)
  have h3 := h v0 z z
  have h4 := R v0
  let v5 := M y z
  have h6 := h z z v5
  have h7 := R z
  have h8 := h z z y
  have h9 := S h8
  have h10 := h v5 z x
  have h11 := R v5
  have h12 := h x z x
  have h13 := S h12
  have h14 := R x
  let v15 := M x z
  have h16 := h x x v15
  have h17 := C (T h16 (C h13 h14)) h14
  have h18 := h x x x
  have h19 := C (S h18) h14
  have h20 := h x x v0
  have h21 := h v5 x x
  have h22 := h z x v5
  have h23 := h v0 x z
  have h24 := T (T (T (T h20 h19) h23) (C (C (T (T (T h22 (C (T (C (T (T h21 (C (C (T (T (T h20 h19) h17) h13) h11) h11)) (S h10)) h7) h9) h7)) (C h8 h7)) (S h6)) h4) h4)) (S h3)
  have h25 := C (C (T (T (T (T (T (T h20 h19) h17) h13) (h x z y)) (C (C (h y z x) h14) h14)) (S (h x y (M v15 y)))) h24) h24
  have h26 := h v0 x x
  T (T (T (T (T (T (T (h x x (M v5 x)) (C (S (h x x v5)) h14)) h26) h25) h2) (C (T (T h3 (C (C (T (T (T h6 (C h9 h7)) (C (T h8 (C (T (T h10 (C (C (T (T (T h12 (C (T (C h12 h14) (S h16)) h14)) (C h18 h14)) (S h20)) h11) h11)) (S h21)) h7)) h7)) (S h22)) h4) h4)) (S h23)) h1)) (C (T (T h26 h25) h2) h1)) (S (h y z v0))

@[equational_result]
theorem Equation1913_implies_Equation1764 (G: Type _) [Magma G] (h: Equation1913 G) : Equation1764 G := fun x y z =>
  let v0 := M y z
  let v1 := M x z
  let v2 := M v1 y
  let v3 := M v0 v2
  have h4 := h v3 v2 v0
  have h5 := R v3
  have h6 := R y
  have h7 := R v2
  have h8 := h v3 z x
  have h9 := S h8
  let v10 := M z (M v3 x)
  have h11 := h v10 v0 v1
  let v12 := M v1 v0
  have h13 := R v12
  have h14 := R v0
  let v15 := M z v2
  have h16 := h (M v0 v3) v15 (M v2 v0)
  have h17 := h y v2 z
  have h18 := h v0 v0 v2
  have h19 := R v15
  have h20 := h v1 z y
  have h21 := R v1
  have h22 := h x z x
  let v23 := M z (M x x)
  have h24 := h x v2 v0
  T (T h24 (C (T (T (h (M v2 (M x v0)) y v3) (C (T (T (T (T (C h6 (S h24)) (h (M y x) v3 v2)) (C (C h5 (T (T (T (T (T (T (T (T (C (C h6 h22) h7) (S (h v23 y v1))) (h v23 v1 v1)) (C (T (T (T (C h21 (S h22)) (C (T h20 (C h19 (h v0 v1 v2))) (h x v2 z))) (S (h (M v1 v3) v15 (M v2 v1)))) (C h21 (T h8 (C (T h11 (C (T (T (C h14 h9) h16) (C (T (C h19 (S h18)) (S h20)) (S h17))) h13)) h21)))) (R (M v1 v1)))) (S (h (M v2 v12) v1 v1))) (C (T (T (C (T h20 (C h19 h18)) h17) (S h16)) (C h14 h8)) h13)) (S h11)) (h v10 y v1)) (C (C h6 h9) h7))) (R (M v2 v3)))) (S (h (M y v3) v3 v2))) (C h6 h4)) (R (M v3 y)))) (S (h (M v2 (M v3 v0)) y v3))) h5)) (S h4)

@[equational_result]
theorem Equation1562_implies_Equation2 (G: Type _) [Magma G] (h: Equation1562 G) : Equation2 G := fun x y =>
  let v0 := M x x
  let v1 := M y v0
  have h2 := h v1 y x
  have h3 := h v0 x x
  have h4 := S h3
  have h5 := R v1
  have h6 := C h5 h4
  have h7 := h v0 y v0
  have h8 := T h7 h6
  have h9 := h (M y x) x v0
  have h10 := h v0 y x
  have h11 := R (M x v0)
  have h12 := h v0 x v0
  have h13 := S h7
  have h14 := C h5 h3
  let v15 := M v1 v0
  have h16 := h v15 x x
  let v17 := M y y
  have h18 := R v17
  have h19 := T h14 h13
  have h20 := S h12
  have h21 := C h11 h3
  have h22 := C h11 (S h10)
  have h23 := h v17 y y
  let v24 := M y v17
  have h25 := R v24
  have h26 := h v17 y v17
  let v27 := M x y
  have h28 := h v17 x y
  let v29 := M x v17
  T (T (T (T (T (T (T (T (T (T (h x y y) (C h18 (T (h v29 x y) (C (T (h v27 y v17) (C h25 (S h28))) (T (C (R v29) h23) (S (h v17 x v17))))))) (S (h (M v24 v17) y y))) (C h25 h23)) (S h26)) h28) (C (R v27) (T (T (C h18 (T (T h26 (C h25 (S h23))) (C (T (C (T (T (h y y x) (C (T (T (T h9 h22) h21) h20) (T h2 (C (T (T (T (T (T h9 h22) h21) h20) h7) h6) h19)))) (S h16)) h18) (C h19 h18)) h18))) (S (h (M v0 v17) y y))) (C h8 h18)))) (S (h v15 x y))) h16) (C (R v0) (T (C (T (T (T (T (T h14 h13) h12) (C h11 h4)) (C h11 h10)) (S h9)) h8) (S h2)))) (S (h y x x))

@[equational_result]
theorem Equation2944_implies_Equation725 (G: Type _) [Magma G] (h: Equation2944 G) : Equation725 G := fun x y z =>
  let v0 := M z x
  let v1 := M v0 z
  let v2 := M y (M y v1)
  let v3 := M (M x (M x v2)) v2
  have h4 := h v2 v3 x
  have h5 := S h4
  have h6 := R x
  have h7 := h v2 x v2
  have h8 := R v3
  have h9 := C (C (T h7 (C h8 h7)) h6) h6
  have h10 := h v1 y x
  have h11 := T (T h10 h9) h5
  have h12 := S h7
  let v13 := M (M x (M x z)) z
  have h14 := h z v13 x
  have h15 := S h14
  have h16 := h z x z
  have h17 := R v13
  have h18 := C (C (T h16 (C h17 h16)) h6) h6
  have h19 := R v0
  have h20 := S h16
  have h21 := C (C h19 (C h19 (T h14 (C (C (T (C h17 h20) h20) h6) h6)))) h11
  have h22 := R v1
  have h23 := h v0 x v0
  have h24 := S h23
  let v25 := M (M x (M x v0)) v0
  have h26 := R v25
  have h27 := T (C h26 h24) h24
  have h28 := C (C h27 h22) h22
  have h29 := h v0 v25 v1
  have h30 := h v0 v25 z
  have h31 := R z
  T (T (T (T (T (h x z v1) (C (C (T (C h31 (T h30 (C (C h27 h31) h31))) (C h31 (T (T (T (T (T (C (C (T h23 (C h26 h23)) h31) h31) (S h30)) h29) h28) h21) (C (T (T (T (C (T (T h29 h28) h21) (T (T (T (C h19 (T h18 h15)) h10) h9) h5)) (S (h (M v0 x) v0 v2))) h18) h15) (T (T h4 (C (C (T (C h8 h12) h12) h6) h6)) (S h10)))))) h11) h11)) (S (h v1 z v2))) h10) h9) h5

@[equational_result]
theorem Equation2741_implies_Equation3214 (G: Type _) [Magma G] (h: Equation2741 G) : Equation3214 G := fun x y z =>
  let v0 := M y z
  let v1 := M v0 z
  let v2 := M v1 y
  let v3 := M v2 x
  let v4 := M v3 v3
  have h5 := h v4 x v0
  have h6 := R v0
  have h7 := h (M v4 v0) x z
  have h8 := R z
  have h9 := h y v3 z
  have h10 := h y x z
  have h11 := S h10
  let v12 := M x x
  have h13 := R v12
  have h14 := h (M v12 v0) x z
  have h15 := h v12 x v0
  have h16 := T (T h15 (C (C h13 (T (T h14 (C (C h13 (T h11 h9)) h8)) (S h7))) h6)) (S h5)
  let v17 := M v0 v0
  have h18 := h (M v17 v12) v12 x
  have h19 := R x
  have h20 := h x v0 x
  have h21 := R (M v12 v12)
  have h22 := h x x x
  have h23 := h v12 v3 v0
  have h24 := S h14
  have h25 := h y y z
  let v26 := M y y
  have h27 := h (M v26 v0) x z
  have h28 := h v26 x v0
  T (T (T (T (T (T (T h20 (C (T h18 (C (T (C h21 (S h20)) (S h22)) h19)) h19)) (C (T (T h23 (C (C (T (T h5 (C (C h13 (T (T h7 (C (C h13 (T (S h9) h10)) h8)) h24)) h6)) (S h15)) (T (T h14 (C (C h13 (T h11 h25)) h8)) (S h27))) h6)) (S h28)) h19)) (C (T (C (T (T (T h10 (C (C h13 (h v0 y z)) h8)) (S (h (M v26 v1) x z))) (C (R v26) (h v1 x y))) (R y)) (S (h (M v12 v2) y y))) h19)) (C (C h13 (h v2 y x)) h19)) (S (h (M v26 v3) x x))) (C (T (T (T (T (T h28 (C (C h16 (T (T h27 (C (C h13 (T (S h25) h10)) h8)) h24)) h6)) (S h23)) (C (T h22 (C h21 h20)) h19)) (S h18)) (C (R v17) h16)) (R v3))) (S (h v3 v0 v3))

@[equational_result]
theorem Equation1277_implies_Equation2 (G: Type _) [Magma G] (h: Equation1277 G) : Equation2 G := fun x y =>
  let v0 := M (M y y) y
  let v1 := M v0 y
  have h2 := h y v1 y
  have h3 := S h2
  let v4 := M v0 v0
  let v5 := M v4 v0
  let v6 := M v5 x
  have h7 := S (h v1 v4 v6)
  have h8 := R y
  have h9 := h (M v1 v1) y y
  have h10 := T (T h2 h9) (C h2 (C (C (C h3 h3) h3) h8))
  have h11 := C (R v4) (T (h v0 y x) (C h10 (R v6)))
  let v12 := M (M (M v5 v5) v5) x
  let v13 := M (M x x) x
  let v14 := M v13 y
  let v15 := M v14 v14
  let v16 := M v15 v14
  have h17 := h x v14 y
  have h18 := S h17
  have h19 := C h17 (C (C (C h18 h18) h18) h8)
  have h20 := h v15 x y
  let v21 := M v13 x
  have h22 := h x v21 x
  have h23 := S h22
  have h24 := R x
  have h25 := S h20
  have h26 := C (C h17 h17) h17
  have h27 := C h18 (C h26 h8)
  have h28 := T (T (T h27 h25) h18) h22
  have h29 := T h20 h19
  T (T (T (T (T (h x x x) (C h24 (T (h v21 y y) (C h10 (C (T (T (T (T (T (C h23 (T (T (C h26 h24) (C (C (C h29 h29) h29) h24)) (C (C (T (C (R v16) (T (T h27 h25) h18)) (C h28 h22)) h28) h24))) (S (h (M v21 v21) x x))) h23) h17) h20) h19) h8))))) (S (h v1 x (M v16 y)))) (h v1 v5 v12)) (C (T h11 h7) (T (T (T (C (T (T (C h3 (C (C (C h2 h2) h2) h8)) (S h9)) h3) (R v12)) (S (h v5 y x))) h11) h7))) h3

@[equational_result]
theorem Equation2129_implies_Equation2 (G: Type _) [Magma G] (h: Equation2129 G) : Equation2 G := fun x y =>
  let v0 := M y x
  have h1 := R v0
  have h2 := R y
  let v3 := M y y
  have h4 := h v3 v3 x
  have h5 := S h4
  let v6 := M v3 x
  have h7 := R v6
  have h8 := h v3 y y
  have h9 := C h8 h7
  have h10 := h (M v3 v6) y x
  have h11 := S h10
  have h12 := h v0 v3 y
  have h13 := R (M v3 y)
  have h14 := h v3 y x
  have h15 := S h8
  have h16 := C h15 h13
  have h17 := h v3 v3 y
  have h18 := C h15 h7
  have h19 := T h4 h18
  have h20 := T h9 h5
  have h21 := h v6 y y
  have h22 := T h21 (C h20 h19)
  have h23 := h x y y
  let v24 := M x x
  have h25 := h (M x y) v24 x
  have h26 := R (M v24 x)
  have h27 := h v24 x y
  have h28 := h v24 x x
  have h29 := h v24 v24 x
  have h30 := T (T (T (T h29 (C (S h28) h26)) (C h27 h26)) (S h25)) (C (T (T (T (T h23 (C h22 (T (T (T h17 h16) (C h14 h13)) (S h12)))) h11) h9) h5) h2)
  have h31 := S h17
  have h32 := C h8 h13
  have h33 := R v3
  have h34 := C h33 (T (T (T (T (C (T (T (T (T h4 h18) h10) (C (T (C h19 h20) (S h21)) (T (T (T h12 (C (S h14) h13)) h32) h31))) (S h23)) h2) h25) (C (S h27) h26)) (C h28 h26)) (S h29))
  T (T (T (T (T (T (T (T (T (T (T (h x y x) (C h22 h1)) h11) h9) h5) h17) h16) h34) (h (M v3 v24) y x)) (C (T (C (T (T h17 h16) h34) (T (T (C h33 h30) h32) h31)) (S (h v24 y y))) h1)) (C h30 h1)) (S (h y y x))

@[equational_result]
theorem Equation1693_implies_Equation2 (G: Type _) [Magma G] (h: Equation1693 G) : Equation2 G := fun x y =>
  let v0 := M y y
  have h1 := h y y (M v0 x)
  have h2 := S h1
  have h3 := h y y x
  have h4 := R v0
  have h5 := C h4 h3
  have h6 := S (h (M v0 y) x y)
  have h7 := R y
  let v8 := M x y
  have h9 := h y x (M v8 x)
  have h10 := h y x x
  have h11 := R v8
  have h12 := R x
  have h13 := h v8 y y
  have h14 := T (T (S h13) (C h12 (T h9 (C h11 (S h10))))) (C h12 (T (T (T (C h11 h10) (S h9)) h1) (C h4 (S h3))))
  have h15 := C h14 (C h14 h7)
  let v16 := M y v8
  have h17 := h (M v16 y) v16 y
  let v18 := M x x
  let v19 := M y x
  have h20 := h x y (M v19 x)
  have h21 := S h20
  have h22 := h x y x
  have h23 := R v19
  have h24 := C h23 h22
  have h25 := h x x x
  have h26 := R v18
  have h27 := C h26 (S h25)
  have h28 := h x x (M v18 x)
  have h29 := T h28 h27
  have h30 := S h28
  have h31 := C h26 h25
  have h32 := C h12 (T (T (T h31 h30) h20) (C h23 (S h22)))
  have h33 := C h12 h29
  let v34 := M x v18
  have h35 := h v18 x y
  have h36 := T h31 h30
  T (T (T (T (T (T (T (T (T (T h28 (C h35 (T (C (T h33 h32) h36) (C (T (T (C h12 (T (T (T h24 h21) h28) h27)) (C h12 h36)) h35) h12)))) (S (h (M v34 y) v34 x))) (C (T (C h29 (T (T h33 h32) (C h29 (T h24 h21)))) (S (h x v18 x))) h7)) h13) (C (R v16) (T (T (T (T h17 h15) h6) h5) h2))) h17) h15) h6) h5) h2

@[equational_result]
theorem Equation508_implies_Equation914 (G: Type _) [Magma G] (h: Equation508 G) : Equation914 G := fun x y z =>
  let v0 := M z z
  let v1 := M y x
  let v2 := M v1 v0
  let v3 := M y v2
  have h4 := h v0 v3 z
  have h5 := S h4
  have h6 := R v3
  have h7 := h v3 v3 v0
  have h8 := R y
  have h9 := h x x v0
  have h10 := h v0 x z
  have h11 := h v0 v1 v2
  have h12 := S h11
  have h13 := h v2 v2 v0
  have h14 := h v0 v2 z
  have h15 := h v0 v0 v0
  have h16 := S h15
  have h17 := h v0 v0 z
  have h18 := R v0
  have h19 := C h18 h17
  have h20 := C h18 (S h17)
  have h21 := C h6 (T h7 (C h6 (T (T h5 h15) h20)))
  have h22 := R v2
  have h23 := h v0 v2 v3
  have h24 := R v1
  have h25 := T (T h15 h20) (C h18 (T h4 (C h6 (T (C h6 (T (T h19 h16) h4)) (S h7)))))
  have h26 := h v0 v1 z
  have h27 := h v1 v1 v0
  have h28 := C h24 (T (T (T h27 (C h24 (S h26))) (C h24 h25)) (C h24 (C h18 (T (T (T h21 h5) h23) (C h22 (T (C h22 (T (T (T (C h18 (T h21 h5)) h19) h16) h14)) (S h13)))))))
  have h29 := R x
  T (T (h x y x) (C h8 (T (T (C h8 (T (C h29 (T (T (C h29 (T (T h9 (C h29 (S h10))) (C h29 (T (T h15 h20) (C h18 (T (T (h v0 y v1) (C h8 (C h8 (T (T (T (C h18 (T (T h28 h12) h17)) h16) h11) (C h24 (T (C h24 (T (T (C h18 (T (T (C h22 (T (T h13 (C h22 (S h14))) (C h22 h25))) (S h23)) h17)) h16) h26)) (S h27))))))) (C h8 (T (C h8 (T (T h28 h12) (h v0 y z))) (S (h y y v0)))))))))) (S (h v0 x y))) h10)) (S h9))) (h v1 y z)) (C h8 (T h7 (C h6 h5)))))) (S (h v3 y z))

@[equational_result]
theorem Equation1320_implies_Equation711 (G: Type _) [Magma G] (h: Equation1320 G) : Equation711 G := fun x y z =>
  let v0 := M (M x z) z
  let v1 := M y v0
  let v2 := M y v1
  have h3 := h v2 v2 x
  let v4 := M v2 v2
  have h5 := R x
  have h6 := h v2 v2 z
  have h7 := R v2
  let v8 := M (M v4 z) z
  have h9 := R v0
  have h10 := h (M (M v1 x) x) y y
  have h11 := R y
  have h12 := h v0 y x
  have h13 := h (M (M v0 y) y) x x
  have h14 := h v0 x v2
  have h15 := S h14
  let v16 := M (M (M x v0) v2) v2
  have h17 := h v16 x y
  have h18 := h v16 x v1
  have h19 := R v1
  have h20 := h (M (M v0 v1) v1) x x
  have h21 := R z
  have h22 := h x y x
  let v23 := M (M (M y x) x) x
  have h24 := h x v2 x
  T (T h24 (C h7 (T (T (T (T (T (T (h (M (M (M v2 x) x) x) v2 y) (C h7 (T (T (C (C (S h24) h11) h11) (h (M (M x y) y) y x)) (C h11 (T (T (C (C (T (T (T (C h11 (C (C h22 h11) h11)) (S (h v23 y y))) (h v23 y z)) (C h11 (C (C (S h22) h21) h21))) h5) h5) h10) (C h11 (T (T (T (C (C (S h12) h11) h11) h13) (C h5 (C (C (T (T (T (C h5 (C (C h14 h11) h11)) (S h17)) h18) (C h5 (C (C h15 h19) h19))) h5) h5))) (S h20)))))))) (C h7 (T (T (C h11 (T (T (C h11 (T (T (T h20 (C h5 (C (C (T (T (T (C h5 (C (C h14 h19) h19)) (S h18)) h17) (C h5 (C (C h15 h11) h11))) h5) h5))) (S h13)) (C (C h12 h11) h11))) (S h10)) (C (C (h v1 y v0) h5) h5))) (S (h (M (M v2 v0) v0) y x))) (C (C h6 h9) h9)))) (S (h v8 v2 v0))) (h v8 v2 x)) (C h7 (T (C (C (S h6) h5) h5) (C (C h3 h5) h5)))) (S (h (M (M v4 x) x) v2 x))))) (S h3)

@[equational_result]
theorem Equation914_implies_Equation1053 (G: Type _) [Magma G] (h: Equation914 G) : Equation1053 G := fun x y z =>
  let v0 := M y z
  let v1 := M y v0
  let v2 := M v1 z
  let v3 := M x v2
  have h4 := h v3 v2 v3
  let v5 := M v3 v3
  let v6 := M y y
  let v7 := M x x
  have h8 := R v7
  have h9 := h v0 x x
  have h10 := S h9
  have h11 := R x
  let v12 := M (M x v0) v7
  have h13 := h v12 x v1
  let v14 := M v1 v1
  have h15 := R v14
  let v16 := M v0 v14
  have h17 := h v16 x x
  have h18 := h v16 y x
  have h19 := h z y v1
  have h20 := h z y v3
  have h21 := R y
  have h22 := h (M v0 v5) y x
  have h23 := R v0
  let v24 := M v0 v0
  let v25 := M v2 v2
  have h26 := h x v2 z
  have h27 := R v2
  T (T h26 (C h27 (T (T (h (M (M v2 x) (M z z)) v2 v2) (C h27 (T (T (C (S h26) (T (T (T (h v25 v1 x) (C (R v1) (T (C (T (T (h (M v1 v25) y x) (C h21 (C (S (h v0 y v2)) h8))) (S (h z y x))) h8) (C (h z v1 v2) h8)))) (S (h (M v2 v25) v1 x))) (C (h v2 x v0) (R v25)))) (S (h (M v3 v24) x v2))) (C h4 (T (T (T (h v24 v0 x) (C h23 (C (T (T (T (T (T (h (M v0 v24) x x) (C h11 (C (T (T (T (C h11 (C h9 (R v24))) (S (h v12 x v0))) h13) (C h11 (C h10 h15))) h8))) (S h17)) h18) (C h21 (C (T (S h19) h20) h8))) (S h22)) h8))) (C h23 (C (T (T (T (T (T h22 (C h21 (C (T (S h20) h19) h8))) (S h18)) h17) (C h11 (C (T (T (T (C h11 (C h9 h15)) (S h13)) (h v12 x y)) (C h11 (C h10 (R v6)))) h8))) (S (h (M v0 v6) x x))) h8))) (S (h v6 v0 x))))))) (S (h (M (M v2 v3) v5) v2 y))))) (S h4)

@[equational_result]
theorem Equation2334_implies_Equation2 (G: Type _) [Magma G] (h: Equation2334 G) : Equation2 G := fun x y =>
  have h0 := h y y x
  have h1 := R y
  let v2 := M y (M y (M x x))
  let v3 := M y x
  let v4 := M y (M y v3)
  have h5 := R x
  have h6 := h y y y
  have h7 := S h6
  have h8 := C h5 (C h5 h7)
  let v9 := M y (M y y)
  let v10 := M y v9
  have h11 := h v10 x y
  have h12 := h v10 y y
  have h13 := S h12
  have h14 := C h1 (C h1 h6)
  have h15 := h y x x
  have h16 := S h15
  have h17 := h (M x (M x v3)) x x
  let v18 := M x y
  let v19 := M x v18
  have h20 := h v19 x x
  have h21 := h v9 x y
  have h22 := h v2 x y
  have h23 := h x y x
  have h24 := h x y y
  have h25 := C h5 (C h5 (S h24))
  have h26 := h (M y (M y v18)) x y
  have h27 := T (T h26 (C (T h25 (C h5 (C h5 h23))) h5)) (S h22)
  have h28 := h x x y
  have h29 := S h23
  have h30 := T (T h22 (C (T (C h5 (C h5 h29)) (C h5 (C h5 h24))) h5)) (S h26)
  T (T h23 (C (T (T (h v2 v2 y) (C (T (C h30 (T (T (C h30 h29) (C (T (T h26 (C (T h25 (C h5 (C h5 h28))) h5)) (S (h (M x v19) x x))) h5)) (S h28))) (C h27 (T h24 (C h27 (T (T h15 (C (T h17 (C (T (T (T (C h5 (C h5 h16)) h20) (C (C h5 (C h5 (T (T (T (C (C h5 (C h5 h6)) h5) (S h11)) h12) (C (C h1 (C h1 h7)) h1)))) h5)) (S h21)) h5)) h5)) (C (T (T (T (T (T (h (M v9 x) y x) (C (T (C h1 (C h1 (T (C (T (C (T (T (T h21 (C (C h5 (C h5 (T (T (T (C h14 h1) h13) h11) (C h8 h5)))) h5)) (S h20)) (C h5 (C h5 h15))) h5) (S h17)) h5) h16))) h14) h1)) h13) h11) (C (T h8 (C h5 (C h5 h0))) h5)) (S (h v4 x y))) h5)))))) (R v2))) (S (h v4 v2 x))) h1)) (S h0)

@[equational_result]
theorem Equation1699_implies_Equation3211 (G: Type _) [Magma G] (h: Equation1699 G) : Equation3211 G := fun x y z =>
  let v0 := M y z
  let v1 := M v0 z
  let v2 := M v1 x
  let v3 := M v2 y
  let v4 := M (M v3 v1) v1
  have h5 := R v1
  let v6 := M (M v2 v3) v3
  have h7 := h v6 x x
  have h8 := R (M (M x x) x)
  have h9 := R v6
  have h10 := h x v1 v3
  have h11 := S h10
  let v12 := M (M v1 v3) v3
  have h13 := h v12 v2 v3
  have h14 := h v12 v2 v1
  have h15 := S h14
  let v16 := M (M v2 v1) v1
  have h17 := R v16
  have h18 := C h10 h17
  have h19 := h v16 x x
  have h20 := h v1 v0 z
  have h21 := S h20
  let v22 := M v1 z
  have h23 := R v22
  have h24 := h z y z
  have h25 := h z v0 z
  have h26 := C (T (S h25) h24) h23
  have h27 := R v2
  have h28 := h x v1 v22
  have h29 := C (T h28 (C h27 (T h26 h21))) h5
  have h30 := T h20 (C (T (S h24) h25) h23)
  have h31 := T (C h27 h30) (S h28)
  let v32 := M (M x v3) v3
  let v33 := M v3 y
  T h28 (C h27 (T (T (T (T h26 h21) (h v1 x v3)) (C (T (T (T h29 h19) (C (T (T (T h18 h15) (h v12 v2 y)) (C h11 (R v33))) h8)) (S (h v33 x x))) (T (T (T (h v32 v1 v1) (C (T (T (T (T (T (C (T (h v1 v2 v3) (C h31 h9)) (R v32)) (S (h v6 x v3))) h7) (C (T (T (T (C h10 h9) (S h13)) h14) (C h11 h17)) h8)) (S h19)) (C h31 h5)) (T (C (R (M v1 v1)) h30) (S (h v1 v1 v22))))) (C (T (T (T (T (T h29 h19) (C (T (T (T h18 h15) h13) (C h11 h9)) h8)) (S h7)) (h v6 v3 v1)) (C (S (h y v2 v3)) (R v4))) h5)) (S (h v4 y z))))) (S (h y v3 v1))))
