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
theorem Equation4176_implies_Equation4023 (G: Type _) [Magma G] (h: Equation4176 G) : Equation4023 G := fun x y z =>
  let v0 := M x y
  let v1 := M z x
  let v2 := M z v1
  let v3 := M y v0
  have h4 := R v1
  have h5 := h z v1 v1
  have h6 := R z
  have h7 := h v1 v1 z
  have h8 := h v1 z x
  have h9 := C (S h8) h4
  have h10 := h x v1 v1
  let v11 := M x v1
  have h12 := h v11 z x
  have h13 := R x
  have h14 := h v1 v11 z
  have h15 := h z x v1
  have h16 := h z x y
  have h17 := C (S h16) h6
  have h18 := h y v0 z
  have h19 := S h18
  have h20 := C h16 h6
  have h21 := h x v1 z
  have h22 := h v1 x v1
  let v23 := M x v2
  T (T (h x y v0) (C (T (T (h v3 x v1) (C (C (T (T (T (T (T (T (T h10 h9) (C (T (C (h z x v2) h6) (S (h v2 v23 z))) h4)) (S (h v23 z v1))) (C (T (h x v2 v1) (C (T (C (T (C (T h5 (C (T (C (T (T (T (T h7 (C (T (C h8 h4) (S h10)) h6)) h12) (C (T (T (T h14 (C (S h15) h6)) h20) h19) h13)) (C (T h18 h17) h13)) h6) (S h21)) h4)) h4) (S h22)) h13) (S (h x z x))) h4)) h6)) (S (h v1 x z))) h22) (C (T (C (T h21 (C (T (T (T (T (C (T h20 h19) h13) (C (T (T (T h18 h17) (C h15 h6)) (S h14)) h13)) (S h12)) (C (T h10 h9) h6)) (S h7)) h6)) h4) (S h5)) h4)) (R v3)) h4)) (S (h v3 v2 v1))) (R v0))) (S (h v2 y v0))

@[equational_result]
theorem Equation3620_implies_Equation4684 (G: Type _) [Magma G] (h: Equation3620 G) : Equation4684 G := fun x y z =>
  let v0 := M z y
  have h1 := h v0 x y
  have h2 := R y
  let v3 := M v0 x
  let v4 := M v0 y
  have h5 := R x
  let v6 := M x y
  let v7 := M v6 z
  have h8 := R v7
  have h9 := R v0
  have h10 := h x y v0
  have h11 := h x y z
  have h12 := S h11
  have h13 := h z v3 z
  have h14 := S h13
  have h15 := R z
  have h16 := C h15 (C h11 h15)
  have h17 := C h15 (C h12 h15)
  have h18 := h x y v7
  have h19 := h v6 z x
  let v20 := M (M x z) v6
  have h21 := h x v20 y
  T (T (T (T (T h19 h21) (h y (M (M y v20) x) y)) (C h2 (T (T (T (T (T (T (T (C (T (S h21) (S h19)) h2) (h v7 y x)) (h x (M v6 v7) v7)) (C h8 (T (C (T (T (T (T (T (C h8 (C h18 h8)) (S (h v7 (M (M v7 y) x) v7))) (S h18)) h11) h13) h17) h5) (C (T (T h16 h14) h12) h5)))) (h v7 (M v6 x) v0)) (C h9 (T (T (T (C (T (T (C h9 (T (C (T (T h11 h13) h17) h5) (C (T (T (T (T (T h16 h14) h12) h10) (h v0 (M v4 x) v0)) (C h9 (C (S h10) h9))) h5))) (S (h x (M v6 v0) v0))) (S (h v0 y x))) h8) (h v4 v7 x)) (C h5 (C (T (h x v7 x) (C h5 (C (S (h z y x)) h5))) (R v4)))) (S (h v4 v3 x))))) (S (h v3 y v0))) (C h1 h2)))) (S (h y (M (M y x) v0) y))) (S h1)

@[equational_result]
theorem Equation3791_implies_Equation4216 (G: Type _) [Magma G] (h: Equation3791 G) : Equation4216 G := fun x y z =>
  let v0 := M z y
  let v1 := M v0 z
  have h2 := h x v1 v0
  have h3 := S h2
  have h4 := h z y v0
  have h5 := h v0 z y
  have h6 := h v0 v1 (M y v0)
  have h7 := h y v0 z
  have h8 := R (M v0 x)
  have h9 := C h8 (T (T h7 h6) (C (S h5) (S h4)))
  have h10 := h x y v0
  let v11 := M v1 x
  have h12 := h x y v11
  let v13 := M y v11
  let v14 := M v11 x
  have h15 := h v11 x z
  have h16 := h x z v1
  have h17 := h z v1 v1
  have h18 := h v1 v1 x
  have h19 := R v11
  have h20 := h y v1 x
  have h21 := R (M v1 z)
  have h22 := h z y v1
  have h23 := h v11 v0 z
  have h24 := h z v11 v0
  have h25 := h (M v11 v0) (M z v11) v1
  have h26 := h v0 z v11
  T (T (T h12 (h v14 v13 v1)) (C (C (R v1) (T (T (T h15 (C h24 (T (T h16 (C h19 (T (T h17 (C h21 (T (T h18 (C (T (T h2 (C h8 (T (T (C h5 h4) (S h6)) (S h7)))) (S h10)) h19)) (S h20)))) (S h22)))) h23))) (S h25)) (S h26))) (T (T (T (T (T (C (h y v11 x) (T (T (T (T h26 h25) (C (S h24) (T (T (S h23) (C h19 (T (T h22 (C h21 (T (T h20 (C (T (T h10 h9) h3) h19)) (S h18)))) (S h17)))) (S h16)))) (S h15)) (h v11 x y))) (S (h v14 v13 (M x y)))) (S h12)) h10) h9) h3))) (S (h v1 x v1))

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
theorem Equation3804_implies_Equation3973 (G: Type _) [Magma G] (h: Equation3804 G) : Equation3973 G := fun x y z =>
  let v0 := M z x
  let v1 := M y v0
  have h2 := h v1 z z
  have h3 := S h2
  let v4 := M v1 z
  let v5 := M z z
  have h6 := h z x z
  have h7 := h v0 v4 v5
  let v8 := M v1 x
  let v9 := M v1 y
  let v10 := M v0 v0
  let v11 := M x x
  let v12 := M x z
  let v13 := M v8 v4
  have h14 := R v13
  let v15 := M v4 v12
  have h16 := R v15
  T (T (T (T (T (T (T (T (T (T (T (T (h x y z) (h (M z y) v12 v4)) (C h16 (S (h v1 y z)))) (h v15 v9 v0)) (C (R (M v0 v9)) (T (T (T (T (C h16 (T (T (T (T (h z x v1) (h v8 (M z v1) v4)) (C (S (h z z v1)) h14)) (h v5 v13 v4)) (C (T (T (C (h v1 z v1) h14) (S (h v8 (M v1 v1) v4))) (S (h v1 x v1))) h3))) (S (h v8 v12 v4))) (h v8 v12 y)) (C (T (T (T (T (T (h y v12 v0) (C (S (h x x z)) (R v1))) (h v11 v1 v0)) (C (R (M v0 v1)) (T (h v11 v0 v0) (C (R v10) (S (h z x x)))))) (S (h v10 v1 v0))) (S (h y v0 v0))) (R (M v8 y)))) (S (h v8 v0 y))))) (S (h v8 v9 v0))) (h v8 v9 v1)) (C (S (h v1 v0 y)) (R (M v8 v1)))) (S (h v8 v0 v1))) (h v8 v0 v4)) (C (T (C h2 h6) (S h7)) (T (C (T (T (h v1 x z) h7) (C h3 (S h6))) h2) (S (h v5 v0 v4))))) (S (h v5 v4 v0))) h3

@[equational_result]
theorem Equation3804_implies_Equation4007 (G: Type _) [Magma G] (h: Equation3804 G) : Equation4007 G := fun x y z =>
  let v0 := M y x
  let v1 := M z v0
  let v2 := M v1 y
  let v3 := M y z
  have h4 := h y x x
  have h5 := S (h (M x x) v0 v0)
  let v6 := M x y
  have h7 := S (h v0 v0 v6)
  let v8 := M y y
  have h9 := h v0 v6 v8
  have h10 := h y x y
  have h11 := h x y y
  have h12 := h y y x
  have h13 := C h12 (T (T h12 (C h11 h10)) (S h9))
  have h14 := h y y y
  have h15 := h v1 x y
  let v16 := M x z
  let v17 := M v1 z
  let v18 := M v17 v2
  have h19 := R v18
  let v20 := M v17 v16
  have h21 := R v20
  T (T (T (T (T (T (T (T (T (T (h x y z) (h (M z y) v16 v17)) (C h21 (S (h v1 y z)))) (h v20 v2 v17)) (C h19 (T (T (C h21 (h v1 z z)) (S (h (M z z) v16 v17))) (S (h x z z))))) (h v18 v16 v1)) (C (R (M v1 v16)) (T (T (T (C h19 (T (T (h z v0 v1) (C (h v1 v0 z) (R (M z v1)))) (S (h z v17 v1)))) (S (h z v2 v17))) (h z v2 v0)) (C (S h15) (R v1))))) (S (h (M v1 x) v16 v1))) (C h15 (T (h x z y) (C (R v3) (T (T (T (T h11 (h v8 v6 v0)) (C (T (T (T (T (T h9 (C (S h11) (S h10))) (S h12)) h14) h13) h7) (T (C (T (T h14 h13) h7) h4) h5))) h5) (S h4)))))) (S (h v3 v2 v0))) (S (h v1 z y))

@[equational_result]
theorem Equation4197_implies_Equation4200 (G: Type _) [Magma G] (h: Equation4197 G) : Equation4200 G := fun x y z =>
  let v0 := M z x
  let v1 := M v0 z
  let v2 := M y v1
  have h3 := R z
  have h4 := R y
  let v5 := M v1 y
  have h6 := h v2 y v5
  have h7 := R v5
  have h8 := h y v1 z
  have h9 := R v1
  have h10 := h z y v0
  have h11 := h y v0 v1
  have h12 := h (M (M y v0) z) y v5
  have h13 := h v0 z y
  have h14 := T (T (T h13 h12) (C (C (C h7 (T (C (T h11 (C (S h10) h9)) h3) (S h8))) h4) h7)) (S h6)
  have h15 := R x
  have h16 := h x z z
  have h17 := h v1 z v0
  have h18 := R v0
  have h19 := h x v1 z
  have h20 := S (h v1 v0 x)
  have h21 := C (T (T h16 h17) (C (S h19) h18)) h15
  have h22 := h z x x
  have h23 := h z v1 v0
  T (T (T (h x y z) (C (C (T (T (T h22 (C (T (T (T (T h21 h20) (h v1 v0 v1)) (C (S h23) h9)) (C (T (T (T h23 (C (T (T (T (h v1 v1 v0) (C (C (T (T (C h18 h14) (C (T h22 (C (T h21 h20) h15)) (T (T (T h6 (C (C (C h7 (T h8 (C (T (C h10 h9) (S h11)) h3))) h4) h7)) (S h12)) (S h13)))) (S (h v0 x v1))) h9) h18)) (S (h x v1 v0))) h19) h18)) (S h17)) (S h16)) h9)) h15)) (S (h z v1 x))) (C h3 h14)) h4) h3)) (S (h (M v2 y) y z))) (S (h v1 y y))

@[equational_result]
theorem Equation1304_implies_Equation16 (G: Type _) [Magma G] (h: Equation1304 G) : Equation16 G := fun x y =>
  let v0 := M y x
  let v1 := M y v0
  have h2 := R x
  have h3 := R v0
  let v4 := M v0 x
  let v5 := M v4 y
  have h6 := h y x v5
  have h7 := S h6
  have h8 := R v5
  have h9 := h y y x
  have h10 := C h2 (C (T h9 (C h9 h8)) h2)
  let v11 := M (M x v0) v0
  have h12 := S h9
  let v13 := M (M v1 v0) v0
  have h14 := R v13
  have h15 := S (h v0 v0 x)
  let v16 := M v4 x
  let v17 := M v16 v0
  let v18 := M (M (M x x) x) x
  have h19 := h x v16 v18
  have h20 := R v16
  have h21 := R v18
  have h22 := h x x x
  have h23 := h y x x
  have h24 := S h22
  T (T (T (T h19 (C h20 (T (C (T (C h24 h21) h24) h20) (S h23)))) (h (M v16 y) x v0)) (C h2 (C (T (T (T (C (T (T (C (T (C h20 (T h23 (C (T h22 (C h22 h21)) h20))) (S h19)) h3) h10) h7) (T (T (h v0 v13 v17) (C h14 (T (C (T (C h15 (R v17)) h15) h14) (S (h y v0 v0))))) (C (C (C (C (T h6 (C h2 (C (T (C h12 h8) h12) h2))) h3) h3) h3) (R y)))) (S (h v11 y v0))) (h v11 v1 x)) (C (h v1 v1 x) (C (C (C (C (T h10 h7) h3) h2) h2) (R v1)))) h2))) (S (h v1 x (M (M (M v1 x) x) v1)))

@[equational_result]
theorem Equation1699_implies_Equation4450 (G: Type _) [Magma G] (h: Equation1699 G) : Equation4450 G := fun x y z =>
  let v0 := M y x
  let v1 := M (M y z) z
  have h2 := h v1 v0 x
  have h3 := S h2
  let v4 := M v0 x
  let v5 := M v4 x
  have h6 := R v5
  have h7 := h x y z
  have h8 := R x
  have h9 := h v5 x x
  let v10 := M x v0
  have h11 := h (M (M x x) x) v10 x
  have h12 := R (M (M v10 x) x)
  have h13 := h v0 x x
  have h14 := h v0 x z
  have h15 := S h14
  let v16 := M (M x z) z
  have h17 := h v16 v10 x
  have h18 := S h7
  let v19 := M v10 v0
  let v20 := M v19 v0
  have h21 := S (h v0 y z)
  T (T (T (C (T (T (T (T (T (T (h x v1 z) (C (T (T (C (T (h v1 (M y v0) v1) (C h21 (T (C h21 (R v1)) h18))) h8) h9) (C (T (C h7 h6) h3) (T (T h11 (C (T (S h13) h14) h12)) (S h17)))) (R (M (M v1 z) z)))) (S (h v16 v1 z))) h17) (C h15 h12)) (C (h v0 x v0) h12)) (S (h v19 v10 x))) (R v0)) (h v20 v0 x)) (C (T (T (T (T (T (C h14 (R v20)) (S (h v16 v10 v0))) (h v16 v1 v1)) (C (T (T (C (T h2 (C h18 h6)) (T (T h17 (C (T h15 h13) h12)) (S h11))) (S h9)) (C (T (T (h v4 v0 x) (C (T (S (h x y x)) h7) h6)) h3) h8)) (R (M (M v1 v1) v1)))) (S (h x v1 v1))) h7) h6)) h3

@[equational_result]
theorem Equation2319_implies_Equation4491 (G: Type _) [Magma G] (h: Equation2319 G) : Equation4491 G := fun x y z =>
  have h0 := R z
  let v1 := M y y
  let v2 := M x v1
  let v3 := M v2 v2
  have h4 := h x v3 y
  have h5 := S h4
  have h6 := R v3
  have h7 := h x v2 y
  have h8 := C h7 h6
  let v9 := M (M z x) z
  have h10 := h (M x v3) v1 v9
  have h11 := R v1
  let v12 := M v9 v9
  have h13 := R v12
  have h14 := C (S h7) h6
  have h15 := h (M v1 (M x v12)) x y
  have h16 := R x
  have h17 := h x v1 v9
  have h18 := h x v1 z
  have h19 := S h18
  let v20 := M z z
  let v21 := M v1 (M x v20)
  have h22 := h v21 x y
  have h23 := h v21 z y
  have h24 := S h23
  have h25 := C (C h0 h18) h0
  have h26 := C (C h0 (T (T (C (T (T (T (C (T (T (T (T (T h25 h24) h22) (C (T (C h16 h19) (C h16 h17)) h16)) (S h15)) (C h11 (C (T h4 h14) h13))) h11) (S h10)) h8) h5) h6) h8) h5)) h0
  let v27 := M v9 v1
  have h28 := h v27 z v2
  have h29 := C (T (T (T (T (T (C h11 (C (T h8 h5) h13)) h15) (C (T (C h16 (S h17)) (C h16 h18)) h16)) (S h22)) h23) (C (C h0 h19) h0)) h11
  T (T (T (C (T (T (T (T (T (T (T (T h4 h14) h10) h29) h28) h26) h25) h24) (C h11 (C (T (T (T h4 h14) h10) h29) (R v20)))) h11) (S (h v27 v1 z))) h28) h26

@[equational_result]
theorem Equation2958_implies_Equation4007 (G: Type _) [Magma G] (h: Equation2958 G) : Equation4007 G := fun x y z =>
  have h0 := R z
  let v1 := M y x
  have h2 := R v1
  have h3 := S (h z x z)
  let v4 := M (M x (M x z)) z
  have h5 := T (C (R v4) h3) h3
  let v6 := M (M v1 (M v1 y)) y
  have h7 := R y
  have h8 := h y v1 y
  let v9 := M (M x (M x x)) x
  have h10 := h y v9 x
  have h11 := R x
  have h12 := h x x x
  have h13 := R v9
  have h14 := T h12 (C h13 h12)
  let v15 := M x y
  have h16 := S h12
  let v17 := M z v1
  have h18 := R v17
  have h19 := S (h v17 x v17)
  let v20 := M (M x (M x v17)) v17
  have h21 := S (h y x y)
  let v22 := M (M x v15) y
  let v23 := M x v1
  T (T (T (T (C (T (h x x v1) (C (T (T (T (T (T (C (C h14 (R v23)) h11) (S (h v23 v9 x))) (C (T (T (h x v22 y) (C (C (T (C (R v22) h21) h21) h11) h7)) (C (T (h v1 v20 v17) (C (T (T (C (T (C (R v20) h19) h19) h2) (C (T (h v17 v4 z) (C (C h5 h18) h0)) h2)) (S (h z z v1))) h18)) (T h10 (C (C (T (C h13 h16) h16) h7) h11)))) h2)) (S (h (M v15 x) z v1))) (C (C h14 h7) h11)) (S h10)) h2)) h7) (C (C (T h8 (C (R v6) h8)) h2) h7)) (S (h v1 v6 y))) (h v1 v4 z)) (C (C h5 h2) h0)

@[equational_result]
theorem Equation627_implies_Equation2646 (G: Type _) [Magma G] (h: Equation627 G) : Equation2646 G := fun x y =>
  let v0 := M x x
  let v1 := M v0 x
  let v2 := M x v1
  have h3 := R v2
  have h4 := h x x x
  have h5 := R x
  have h6 := S (h v0 x x)
  have h7 := S h4
  have h8 := R v0
  have h9 := C h8 (T (h v0 x v2) (C h8 (C h8 (T (C h7 h3) h7))))
  have h10 := C (T h9 h6) h8
  let v11 := M y v1
  have h12 := h x y v11
  have h13 := S h12
  have h14 := R v11
  have h15 := h y x x
  have h16 := C h5 (C h5 (T h15 (C h15 h14)))
  let v17 := M x y
  have h18 := R v17
  have h19 := T h16 h13
  let v20 := M x (M (M y v0) v0)
  have h21 := h x y v0
  let v22 := M x v17
  let v23 := M v0 v17
  let v24 := M v23 x
  have h25 := S (h y v23 v24)
  let v26 := M y (M (M v23 v24) v24)
  have h27 := S h15
  T (T (T (h x y v26) (C (T h12 (C h5 (C h5 (T (C h27 h14) h27)))) (C h5 (T (C h25 (R v26)) h25)))) (h (M v22 v17) v0 v0)) (C (C (T (h v22 v0 v0) (C h19 (T (T (C h19 (R (M (M v0 v0) v0))) (C h5 (T (T (T h10 h9) h6) (C h5 (T h21 (C h21 (R v20))))))) (S (h x x v20))))) h18) (T (T (C (T (T (C h19 h18) h16) h13) (T (T h10 h9) h6)) (C h5 (C h5 (T h4 (C h4 h3))))) (S (h x x v2))))

@[equational_result]
theorem Equation1699_implies_Equation4162 (G: Type _) [Magma G] (h: Equation1699 G) : Equation4162 G := fun x y z =>
  let v0 := M y x
  let v1 := M (M v0 z) z
  have h2 := R v1
  have h3 := h x y v1
  have h4 := C (S h3) h2
  let v5 := M (M y v1) v1
  have h6 := h v5 v0 z
  have h7 := S (h v5 v0 x)
  let v8 := M v0 x
  have h9 := R (M v8 x)
  have h10 := S (h y x v1)
  let v11 := M (M x v1) v1
  have h12 := C (T (T (T (T (h v8 v0 x) (C (T (S (h x y x)) h3) h9)) h7) h6) h4) h2
  have h13 := h x v0 z
  let v14 := M x y
  have h15 := C (T (C (R v14) (T (T h13 h12) (R v11))) h10) (R x)
  have h16 := R y
  let v17 := M (M v14 x) x
  have h18 := R v17
  have h19 := h v11 v14 x
  have h20 := h y x z
  let v21 := M (M x z) z
  let v22 := M v14 y
  let v23 := M v22 y
  T (T (T (T (T (T (T (C (T (T (T (T h13 h12) h19) (C (T h10 (h y x y)) h18)) (S (h v22 v14 x))) h16) (h v23 y x)) (C (T (T (T (C h20 (R v23)) (S (h v21 v14 y))) (h v21 v14 x)) (C (S h20) h18)) (R v8))) (S (h v17 y x))) h15) (h v0 x v0)) (C (T (T (T (T (T (C (T (T (T (T h13 h12) h19) (C h10 h18)) (C h16 h15)) (R v0)) (h (M (M y v0) v0) v0 x)) (C (T (S (h x y v0)) h3) h9)) h7) h6) h4) (R (M (M x v0) v0)))) (S (h v1 x v0))

@[equational_result]
theorem Equation2196_implies_Equation1699 (G: Type _) [Magma G] (h: Equation2196 G) : Equation1699 G := fun x y z =>
  let v0 := M y z
  let v1 := M v0 z
  have h2 := R v1
  let v3 := M y x
  have h4 := C (S (h y x v3)) (S (h x v3 v3))
  let v5 := M (M v3 v3) v3
  have h6 := h v5 (M x v3) v3
  have h7 := S (h v5 y x)
  let v8 := M v3 v1
  have h9 := h y x v8
  have h10 := C (R v5) (S h9)
  let v11 := M (M x v8) v8
  have h12 := h v11 v3 v3
  let v13 := M v8 v1
  let v14 := M v3 x
  have h15 := R v14
  let v16 := M v13 v1
  let v17 := M (M v1 y) y
  have h18 := h v0 z v1
  let v19 := M (M z v1) v1
  let v20 := M v1 v3
  let v21 := M v20 v3
  let v22 := M x y
  T (T (T (T (T (T (h x y z) (C h2 (T (T (h v22 y x) (C h15 (T (T (T (T (h (M v22 y) v3 x) (C (R (M v14 x)) (T (S (h y x y)) h9))) (S (h v11 v3 x))) h12) h10))) h7))) (C h2 (T h6 h4))) (h v20 v3 v8)) (C (R (M (M v3 v8) v8)) (T (T (T (T (h v21 v0 x) (C (R (M (M v0 x) x)) (T (T (T (C (R v21) h18) (S (h v19 v1 v3))) (h v19 v1 y)) (C (R v17) (S h18))))) (S (h v17 v0 x))) (h v17 v8 v1)) (C (R v16) (S (h v3 v1 y)))))) (S (h v16 v3 v8))) (C (T (T (T (T (h v13 y x) (C h15 (T (T (T (C (R v13) h9) (S (h v11 v3 v1))) h12) h10))) h7) h6) h4) h2)

@[equational_result]
theorem Equation684_implies_Equation1165 (G: Type _) [Magma G] (h: Equation684 G) : Equation1165 G := fun x y z =>
  let v0 := M y x
  let v1 := M z v0
  let v2 := M v1 z
  let v3 := M y v2
  have h4 := S (h v3 v3 x)
  let v5 := M v3 (M (M v3 x) x)
  let v6 := M y v3
  have h7 := R v3
  let v8 := M v2 (M (M v2 x) x)
  have h9 := R v8
  have h10 := h v2 v2 x
  have h11 := R v2
  have h12 := R y
  let v13 := M z (M (M z x) x)
  have h14 := h v2 z v13
  have h15 := R v13
  have h16 := h z z x
  have h17 := R z
  have h18 := S h16
  have h19 := R v1
  have h20 := S h10
  let v21 := M v0 (M (M v0 x) x)
  have h22 := h v0 v0 x
  have h23 := R v0
  let v24 := M x (M (M x v3) v3)
  have h25 := h x x v3
  T (T (h x y x) (C h12 (T (T (T (T (T (T (T (T (T (T (C (R x) (C h23 (T h25 (C h25 (R v24))))) (S (h v0 x v24))) (h v0 z v0)) (C h17 (T (C h23 (C h19 (T h22 (C h22 (R v21))))) (S (h v1 v0 v21))))) (C h17 (T (h v1 v2 v8) (C h11 (T (T (C h19 (T (C h20 h9) h20)) (C h19 (T h14 (C h17 (C h11 (T (C h18 h15) h18)))))) (S (h z v1 z))))))) (C h17 (C h11 (T h16 (C h16 h15))))) (S h14)) (h v2 y v2)) (C h12 (T (C h11 (C h7 (T h10 (C h10 h9)))) (S (h v3 v2 v8))))) (h v6 v3 v5)) (C h7 (C (R v6) (T (C h4 (R v5)) h4)))))) (S (h v3 y v3))

@[equational_result]
theorem Equation895_implies_Equation749 (G: Type _) [Magma G] (h: Equation895 G) : Equation749 G := fun x y z =>
  let v0 := M x z
  let v1 := M v0 y
  let v2 := M z v1
  let v3 := M y v2
  have h4 := h v3 v0 y
  have h5 := R v1
  have h6 := h y y v2
  have h7 := R (M v3 v3)
  have h8 := h y v2 v2
  have h9 := h v2 v3 x
  have h10 := S h9
  have h11 := R v3
  let v12 := M v2 x
  have h13 := h v3 v3 (M v12 (M v3 x))
  have h14 := R v2
  have h15 := h v2 v3 v3
  have h16 := h v0 y y
  have h17 := h y v1 x
  have h18 := S h17
  let v19 := M v1 x
  have h20 := h v1 v1 (M (M y x) v19)
  have h21 := R y
  have h22 := T (C h11 (T h6 (C (T h8 (C h14 (T (C h11 (C h9 h9)) (S h13)))) h7))) (S h15)
  have h23 := S (h v1 v2 x)
  T (T (T (T (h x v0 z) (C (R v0) (C (T (T (h v0 v3 y) (C h11 (T (T (C h5 h22) (C h5 (T (h v2 v2 (M v19 v12)) (C h14 (C h23 h23))))) (S (h z v1 v1))))) (C (T h4 (C (T h16 (C h21 (T (C h5 (C h17 h17)) (S h20)))) (C h22 h5))) (R z))) (R (M v0 z))))) (S (h (M (M y v1) (M v2 v1)) v0 z))) (C (T (C h21 (T h20 (C h5 (C h18 h18)))) (S h16)) (C (T h15 (C h11 (T (C (T (C h14 (T h13 (C h11 (C h10 h10)))) (S h8)) h7) (S h6)))) h5))) (S h4)

@[equational_result]
theorem Equation3791_implies_Equation3588 (G: Type _) [Magma G] (h: Equation3791 G) : Equation3588 G := fun x y z =>
  let v0 := M x y
  let v1 := M v0 z
  let v2 := M z v1
  have h3 := h z v1 v0
  have h4 := h v1 v0 z
  have h5 := S h4
  have h6 := R v1
  have h7 := h v0 z v1
  have h8 := R v2
  let v9 := M v2 v1
  have h10 := h v2 v1 v9
  have h11 := T h10 (C (T (C h5 h8) (S h7)) (T (C h6 h5) (S h3)))
  have h12 := R v9
  have h13 := T h3 (C h6 h4)
  have h14 := C h4 h8
  let v15 := M v0 x
  have h16 := S h10
  have h17 := C (T h7 h14) h13
  T (T (T (h x y v1) (h (M v1 x) (M y v1) v0)) (C (T (T (T (T (T (T (T (S (h y v1 x)) (h y v1 v1)) (C (T (h v1 y v2) (C h12 (T (T (h y v2 v0) (C (R (M v0 y)) (T (T (h v2 v0 v1) (C (T (T h17 h16) h5) (R (M v0 v1)))) (S (h v0 v0 v1))))) (S (h y v0 v0))))) (T (h v1 v1 v2) (C h12 (T h17 h16))))) (S (h (M y v0) v9 v9))) (C (h y v0 x) h5)) (S (h v15 v1 v0))) (C (R v15) (T (T (T (T (T (T (T (T h7 h14) (h v9 v2 v2)) (C (T (T (T (C h13 h12) (S (h v9 v2 v1))) (C h11 h8)) (S (h v2 z v1))) (R (M v2 v2)))) (S (h z v2 v2))) (h z v2 v1)) (C (h v1 z z) h11)) (S (h (M z z) v1 v2))) (S (h z v0 z))))) (S (h x z v0))) (S (h v1 x y)))) (S (h z v1 x))

@[equational_result]
theorem Equation1537_implies_Equation2146 (G: Type _) [Magma G] (h: Equation1537 G) : Equation2146 G := fun x y z =>
  let v0 := M y y
  let v1 := M v0 z
  let v2 := M x z
  let v3 := M v1 v2
  have h4 := h v0 x y
  have h5 := S h4
  have h6 := h y y y
  have h7 := S h6
  have h8 := R v0
  have h9 := C h8 h7
  have h10 := h y y v0
  let v11 := M v3 v3
  have h12 := R y
  have h13 := R (M x x)
  have h14 := R v3
  have h15 := h z y v0
  have h16 := h y z v0
  let v17 := M z z
  have h18 := R v17
  have h19 := h v17 x y
  have h20 := R z
  have h21 := h z y z
  have h22 := T h21 (C h8 (C h20 (T (T h19 (C h13 (C h12 (T (T (T (C h18 h6) (S h16)) h10) h9)))) h5)))
  have h23 := R x
  have h24 := R v1
  have h25 := S h21
  have h26 := C h8 (C h20 (T (T h4 (C h13 (C h12 (T (T (T (C h8 h6) (S h10)) h16) (C h18 h7))))) (S h19)))
  have h27 := C h8 (T h26 h25)
  have h28 := R v2
  T (T (h x v1 z) (C (R (M v1 v1)) (T (T (T (T (C h22 h28) (C (T (T (T h26 h25) h15) h27) h28)) (C h24 (C h23 (T h15 h27)))) (h (M v1 (M x v1)) y v3)) (C h8 (C h14 (T (T (T (C (C h24 (C h23 (T (C h8 h22) (S h15)))) h14) (h v11 x y)) (C h13 (C h12 (T (T (T (C (R v11) h6) (S (h y v3 v0))) h10) h9)))) h5)))))) (S (h v3 v1 v0))

@[equational_result]
theorem Equation928_implies_Equation952 (G: Type _) [Magma G] (h: Equation928 G) : Equation952 G := fun x y z =>
  let v0 := M z y
  let v1 := M z x
  let v2 := M v1 v0
  let v3 := M y v2
  have h4 := h v2 v3 v0
  have h5 := R v3
  let v6 := M v2 v2
  have h7 := S (h v2 v3 x)
  have h8 := T (h v3 v3 (M (M v3 x) (M v2 x))) (C h5 (C h7 h7))
  let v9 := M v3 v3
  have h10 := R y
  have h11 := T (C h10 h8) (S (h v2 y v2))
  have h12 := S (h y v0 x)
  have h13 := R v0
  have h14 := R z
  let v15 := M x x
  have h16 := h v1 v1 (M (M v1 x) v15)
  have h17 := h x v1 x
  have h18 := R v1
  have h19 := T (C h18 (C h17 h17)) (S h16)
  have h20 := S h17
  T (T (T (T (T (h x z x) (C h14 h19)) (C h14 (T (T (h v1 v1 v0) (C (T (T (T h16 (C h18 (C h20 h20))) (h (M v1 v15) z v0)) (C h14 (T (C (R (M z v0)) (C h19 h13)) (C (T (C h14 (T (h v0 v0 (M (M v0 x) (M y x))) (C h13 (C h12 h12)))) (S (h y z y))) (R v2))))) (T (T (T (h v6 y v3) (C h10 (T (C h11 (R (M v6 v3))) (S (h y v2 v2))))) (C h10 (T (h y v3 v3) (C h5 (C (R v9) h11))))) (S (h v9 y v2))))) (C (R (M z v3)) (C h8 h5))))) (S (h (M v3 v6) z v3))) (C h5 (C h4 h4))) (S (h v3 v3 (M (M v3 v0) (M v2 v0))))

@[equational_result]
theorem Equation1507_implies_Equation1943 (G: Type _) [Magma G] (h: Equation1507 G) : Equation1943 G := fun x y z =>
  let v0 := M x z
  let v1 := M y z
  let v2 := M y v1
  let v3 := M v2 v0
  have h4 := C (S (h x v0 v3)) (S (h z x v0))
  let v5 := M v3 (M v3 v0)
  have h6 := h v5 (M v0 x) v0
  have h7 := S (h v5 z x)
  let v8 := M x v0
  have h9 := R v8
  have h10 := h z x v3
  have h11 := C (S h10) (R v5)
  let v12 := M v3 (M v3 x)
  have h13 := h v12 v0 v3
  let v14 := M v2 v3
  have h15 := R v2
  let v16 := M v2 v14
  have h17 := R (M x v8)
  let v18 := M v3 (M v3 v2)
  have h19 := h v1 y v1
  let v20 := M v1 (M v1 y)
  let v21 := M v0 v2
  let v22 := M v0 v21
  let v23 := M z x
  T (T (T (T (T (T (h x z y) (R (M v23 v2))) (C (T (T (T (T (h v23 z x) (C (T (T (T (T (h (M z v23) v0 x) (C (T (S (h z x z)) h10) h17)) (S (h v12 v0 x))) h13) h11) h9)) h7) h6) h4) h15)) (h v21 v0 x)) (C (T (T (T (T (h v22 v1 x) (C (T (T (T (C h19 (R v22)) (S (h v20 v2 v0))) (h v20 v2 v3)) (C (S h19) (R v18))) (R (M x (M x v1))))) (S (h v18 v1 x))) (h v18 v3 v2)) (C (S (h v0 v2 v3)) (R v16))) h17)) (S (h v16 v0 x))) (C h15 (T (T (T (T (h v14 z x) (C (T (T (T (C h10 (R v14)) (S (h v12 v0 v2))) h13) h11) h9)) h7) h6) h4))

@[equational_result]
theorem Equation2105_implies_Equation1256 (G: Type _) [Magma G] (h: Equation2105 G) : Equation1256 G := fun x y z =>
  have h0 := R z
  let v1 := M y y
  let v2 := M v1 z
  let v3 := M z z
  have h4 := R v3
  have h5 := R v1
  have h6 := R v2
  have h7 := h v1 y x
  let v8 := M x x
  have h9 := R v8
  have h10 := R y
  have h11 := h y y y
  have h12 := S h11
  have h13 := C h12 h5
  have h14 := h y v1 y
  have h15 := h y v1 v2
  let v16 := M v2 v2
  have h17 := R v16
  have h18 := h v16 y x
  have h19 := C (C (T (T h18 (C (C (T (T (T (C h11 h17) (S h15)) h14) h13) h10) h9)) (S h7)) h6) h5
  have h20 := h v2 v2 y
  have h21 := h v2 v1 y
  have h22 := R x
  have h23 := S h20
  have h24 := S h14
  have h25 := C h11 h5
  have h26 := C (C (T (T h7 (C (C (T (T (T h25 h24) h15) (C h12 h17)) h10) h9)) (S h18)) h6) h5
  have h27 := C (T (T (h v2 v1 v1) (C (T (T (T h26 h23) h21) (C (T h26 h23) h5)) (R (M v1 v1)))) (S (h z v1 v1))) h0
  T (T (h x (M v2 z) z) (C (T (C (C (T (T (T (T h27 (h v3 y x)) (C (C (T (T (T (C h11 h4) (S (h y v1 z))) h14) h13) h10) h9)) (C (C (T (T (T h25 h24) (h y v1 x)) (C h12 h9)) h10) h9)) (S (h v8 y x))) h22) h27) (S (h x x z))) h4)) (C h22 (C (T (T (h z v1 z) (C (T (T (T (C (T h20 h19) h5) (S h21)) h20) h19) h4)) (S (h v2 v1 z))) h0))

@[equational_result]
theorem Equation2925_implies_Equation2335 (G: Type _) [Magma G] (h: Equation2925 G) : Equation2335 G := fun x y z =>
  let v0 := M x z
  let v1 := M y v0
  let v2 := M y v1
  let v3 := M v2 z
  have h4 := h v3 y x
  have h5 := R x
  let v6 := M x v3
  have h7 := R z
  have h8 := R v2
  have h9 := R v1
  have h10 := h y x v2
  have h11 := R y
  have h12 := h v0 z v1
  let v13 := M x (M v0 z)
  have h14 := h x x v3
  have h15 := C h5 (S h14)
  have h16 := C h5 h14
  have h17 := h x v3 x
  have h18 := C (T (C h5 (S h17)) h16) h5
  let v19 := M x x
  have h20 := h x y x
  T (T h20 (C (T (T (T (h (M (M y v19) y) x x) (C (T (C (T (C h5 (S h20)) h16) h5) (C (T h15 (C h5 h17)) h5)) h5)) (C (T h18 (C (T (T (T h15 (C (T h17 (C (T (T (T (h (M (M v3 v19) v3) x x) (C (T h18 (C (T h15 (C h5 (T (T (h x x z) (C (C (C h5 (h v0 x z)) h5) h7)) (S (h (M v13 x) x z))))) h5)) h5)) (S (h v13 x x))) (C h5 (T (C (T (T (T h12 (C (T (T (h (M (M z (M v0 v1)) z) y v1) (C (T (C (C h11 (S h12)) h11) (C h9 h10)) h9)) (C (T (C h9 (S h10)) (C h9 (h y v2 v1))) h9)) h9)) (S (h (M (M v2 v2) v2) v1 v1))) (C (C h8 (h v2 x z)) h8)) h7) (S (h (M v6 x) v2 z))))) h5)) h5)) (S (h v6 x x))) (C h5 h4)) h5)) h5)) (S (h (M (M y (M v3 x)) y) x x))) h5)) (S h4)

@[equational_result]
theorem Equation3211_implies_Equation711 (G: Type _) [Magma G] (h: Equation3211 G) : Equation711 G := fun x y z =>
  let v0 := M (M x z) z
  let v1 := M y v0
  let v2 := M y v1
  have h3 := R y
  have h4 := R v1
  have h5 := h x y x
  have h6 := S h5
  have h7 := R x
  have h8 := h y v1 v0
  have h9 := S h8
  have h10 := h v0 y v0
  have h11 := C h10 h4
  have h12 := C (T h11 h9) h7
  have h13 := h v1 x z
  have h14 := h v1 y v2
  have h15 := R v2
  have h16 := h y v2 v1
  have h17 := h v1 y v1
  have h18 := h v2 v1 v2
  have h19 := h y v1 x
  have h20 := S h13
  have h21 := C (S h10) h4
  have h22 := C (C (C (T (C (T h8 h21) h7) h20) h7) h7) h3
  have h23 := C (T (T (T (C (T (T (C (T (C (T h5 h22) h4) (S h19)) h4) h18) (C (C (C (T (C h17 h15) (S h16)) h15) h15) h4)) h3) (S h14)) h13) h12) h7
  have h24 := h y x v1
  T (T (T (T h5 h22) (C (T (C (T (T (T (C (T h14 (C (T (T (C (C (C (T h16 (C (S h17) h15)) h15) h15) h4) (S h18)) (C (T h19 (C (T (C (C (C (T h13 h12) h7) h7) h3) h6) h4)) h4)) h3)) h7) (S h24)) h8) h21) h7) h20) h3)) (C (C (T h24 h23) (T (h v0 v1 y) (C (T (C (T (C (T (C (T h13 (C (T (T (T h11 h9) h24) h23) h7)) h3) h6) h3) (C (h x x z) h3)) (R v0)) (S (h y v0 x))) h4))) h3)) (S (h v2 y x))

@[equational_result]
theorem Equation3211_implies_Equation2958 (G: Type _) [Magma G] (h: Equation3211 G) : Equation2958 G := fun x y z =>
  let v0 := M y z
  let v1 := M y v0
  let v2 := M v1 x
  let v3 := M v2 z
  have h4 := R v1
  have h5 := R y
  have h6 := h v1 v0 v1
  have h7 := R v0
  have h8 := h v0 y v0
  have h9 := h y v1 v0
  have h10 := h v0 y v1
  have h11 := h v0 z v0
  have h12 := S h11
  have h13 := R z
  have h14 := h z y z
  have h15 := S h14
  have h16 := C h15 h7
  have h17 := h y v0 z
  have h18 := C (C (C (T h17 h16) h7) h7) h13
  have h19 := C (T (T (T h18 h12) h10) (C (T (C (C (C (T h9 (C (S h8) h4)) h4) h4) h7) (S h6)) h5)) h5
  have h20 := h z y v0
  have h21 := S h9
  have h22 := h v0 v1 y
  have h23 := S h17
  have h24 := C h14 h7
  T (T (h x v1 v1) (C (T (T (C (T (C (C (C (T h17 (C (T (T (T h15 h20) (C (T (T (T h18 h12) h22) (C (T (T (T (T (C (T (C (T (T (T (C (T h6 (C (C (C (T (C h8 h4) h21) h4) h4) h7)) h5) (S h10)) h11) (C (C (C (T h24 h23) h7) h7) h13)) h5) (S h20)) h7) h24) h23) (h y y v1)) (C (C (T (C (T (T (C (T (T h17 h16) (C (T h20 h19) h7)) h4) (S h22)) h8) h4) h21) h5) h5)) h4)) h5)) (S (h v1 y y))) h7)) h7) h4) h4) (S (h v1 v1 v0))) (R x)) (h v2 v3 z)) (C (T (T (S (h z v2 z)) h20) h19) (R v3))) h4)) (S (h v3 v1 y))

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
theorem Equation492_implies_Equation2519 (G: Type _) [Magma G] (h: Equation492 G) : Equation2519 G := fun x y z =>
  let v0 := M x z
  let v1 := M v0 y
  let v2 := M y v1
  let v3 := M v2 z
  have h4 := S (h z v0 x)
  have h5 := h x z x
  have h6 := h x z v0
  have h7 := h z v2 x
  have h8 := h v1 v0 v1
  have h9 := h v0 y v0
  have h10 := R v1
  have h11 := h y v1 v0
  have h12 := R v0
  have h13 := R y
  have h14 := h v0 y v1
  have h15 := T h14 (C h13 (T (C h12 (C h10 (C h10 (T h11 (C h10 (S h9)))))) (S h8)))
  have h16 := R x
  have h17 := R z
  have h18 := R v2
  have h19 := S h14
  have h20 := C h13 (T h8 (C h12 (C h10 (C h10 (T (C h10 h9) (S h11))))))
  have h21 := T h20 h19
  have h22 := h v0 x v2
  have h23 := R v3
  have h24 := C h12 (T (T (T (C h17 (T (C h17 (T (h v3 v0 v3) (C h12 (C h23 (C h23 (T (C h23 (T (h v0 z v2) (C h17 (C h12 (C h21 h23))))) (S (h z v3 v0)))))))) (S (h v0 z v3)))) (C h17 (T h22 (C h16 (C h12 (C h21 (T (C h18 (T h5 (C h17 (C h16 (C h16 h15))))) (S h7)))))))) (S h6)) h5)
  have h25 := h v0 v3 z
  T (T h6 (C h17 (T (T (T (C h16 (C h12 (C h15 (T h7 (C h18 (T (C h17 (C h16 (C h16 h21))) (S h5))))))) (S h22)) h25) (C h23 (T (T (T h24 h4) (h z v3 v2)) (C h23 (T (T (T (T (S (h v2 z v2)) h20) h19) h25) (C h23 (T h24 h4))))))))) (S (h v3 z v3))

@[equational_result]
theorem Equation2196_implies_Equation492 (G: Type _) [Magma G] (h: Equation2196 G) : Equation492 G := fun x y z =>
  let v0 := M z y
  let v1 := M z v0
  let v2 := M x v1
  have h3 := R v2
  have h4 := h y v2 y
  let v5 := M y v2
  have h6 := R v5
  let v7 := M (M v2 y) y
  have h8 := h v7 (M v1 v2) v2
  have h9 := h v1 v2 y
  have h10 := h x v1 v2
  let v11 := M v2 v5
  let v12 := M v5 v2
  have h13 := h z y y
  have h14 := S h13
  let v15 := M (M y y) y
  have h16 := S (h v15 v0 v2)
  let v17 := M (M v0 v2) v2
  have h18 := C (R v17) h13
  let v19 := M v0 z
  let v20 := M v19 z
  let v21 := M (M v1 v0) v0
  T (h x v1 v0) (C (T (T (T (T (T (T (T (T (T (T (h v21 z v2) (C (R (M (M z v2) v2)) (T (T (T (T (C (R v21) (h z v0 v2)) (S (h v17 v1 v0))) (h v17 z x)) (C (R (M (M z x) x)) (T (T (T h18 h16) (h v15 v0 z)) (C (R v20) h14)))) (S (h v20 z x))))) (S (h v19 z v2))) (C (T (C (h z y v0) (h y v0 v2)) (S (h v17 (M y v0) v0))) (R z))) h18) h16) (h v15 v2 y)) (C (R v7) (T (T (C (T (T (h v15 v0 x) (C (R (M (M v0 x) x)) (T h14 (h z y v2)))) (S (h v12 v0 x))) h3) (h (M v12 v2) v11 v5)) (C (T (T (S (h y v2 v5)) h4) (C (T h8 (C (S h10) (S h9))) h6)) (S (h v2 v5 v2)))))) (S (h v11 v2 y))) (C (T (C h10 h9) (S h8)) h6)) (S h4)) h3)

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
theorem Equation3211_implies_Equation1165 (G: Type _) [Magma G] (h: Equation3211 G) : Equation1165 G := fun x y z =>
  let v0 := M y x
  let v1 := M z v0
  let v2 := M v1 z
  let v3 := M y v2
  have h4 := R y
  have h5 := R v3
  have h6 := R v0
  have h7 := h x y x
  have h8 := h x y v2
  have h9 := R x
  have h10 := R v2
  have h11 := h y v2 x
  have h12 := R z
  have h13 := h v1 v0 v1
  have h14 := R v1
  have h15 := h v0 z v0
  have h16 := h z v1 v0
  have h17 := h v0 z v1
  have h18 := T h17 (C (T (C (C (C (T h16 (C (S h15) h14)) h14) h14) h6) (S h13)) h12)
  have h19 := h y v3 v2
  have h20 := h v2 y v2
  have h21 := C (T (C (T (T (T (C (T (C (T (h v3 v0 v3) (C (C (C (T (T (C h18 h5) (C h20 h5)) (S h19)) h5) h5) h18)) h4) (S (h v2 y v3))) h4) (C (T (h v2 x v2) (C (C (C (T (C (T h7 (C (C (C h18 h9) h9) h4)) h10) (S h11)) h10) h10) h9)) h4)) (S h8)) h7) h6) (S (h y v0 x))) h5
  have h22 := h v0 v3 y
  have h23 := S h17
  have h24 := C (T h13 (C (C (C (T (C h15 h14) (S h16)) h14) h14) h6)) h12
  have h25 := T h24 h23
  T (T h8 (C (T (T (T (T (C (C (C (T h11 (C (T (C (C (C h25 h9) h9) h4) (S h7)) h10)) h10) h25) h9) (S (h v0 x v2))) h22) h21) (C (T h19 (C (T (T (T (T (S h20) h24) h23) h22) h21) h5)) h5)) h4)) (S (h v3 y v3))

@[equational_result]
theorem Equation4176_implies_Equation3943 (G: Type _) [Magma G] (h: Equation4176 G) : Equation3943 G := fun x y z =>
  let v0 := M x y
  let v1 := M z z
  let v2 := M x v1
  let v3 := M y v0
  have h4 := R y
  let v5 := M v2 y
  have h6 := R x
  have h7 := R v5
  have h8 := R z
  let v9 := M z v2
  have h10 := R v1
  have h11 := S (h v1 v1 z)
  have h12 := S (h v1 z z)
  have h13 := h z z z
  let v14 := M v1 z
  have h15 := C (T (T (T (T (T (T (h v1 v14 z) (C (C (S h13) h10) h8)) h12) (C h13 h8)) (S (h z v1 z))) (h z v1 v1)) (C h12 h10)) h8
  have h16 := h v14 z z
  have h17 := h x y v0
  T (T h17 (C (T (T (h v3 x y) (C (T (T (T (h v0 v3 x) (C (S h17) h6)) (C (T (h x y v5) (C (C (T (T (T (T (T (h y v5 v2) (C (T (T (C (C h7 (T (T (T (h x v1 z) (h (M v14 x) z v5)) (C (C (R (M z v5)) (T (C (C (T (T (T (T (T h13 h16) h15) h11) (h v1 v1 x)) (C (T (C (T (T (h v1 x v5) (C (C (R (M x v5)) (T (T (T h13 h16) h15) h11)) h7)) (S (h (M v1 v1) x v5))) h10) (S (h x v1 v1))) h6)) h8) h6) (S (h z v2 x)))) h7)) (S (h v9 z v5)))) h4) (S (h (M v9 z) v2 y))) (S (h z z v2))) (R v2))) (h v1 v2 z)) (C (S (h z x v1)) h8)) (C (h z x y) h8)) (S (h y v0 z))) h6) h7)) h6)) (S (h v5 v3 x))) h4)) (S (h v3 v2 y))) (R v0))) (S (h v2 y v0))

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
theorem Equation508_implies_Equation3297 (G: Type _) [Magma G] (h: Equation508 G) : Equation3297 G := fun x y z =>
  let v0 := M z y
  let v1 := M z v0
  have h2 := R v1
  let v3 := M x x
  have h4 := h y y v3
  have h5 := h v3 y x
  have h6 := h v3 v3 v3
  have h7 := S h6
  have h8 := h v3 v3 x
  let v9 := M y v1
  have h10 := h v3 v9 x
  have h11 := S h10
  have h12 := R v3
  have h13 := C h12 (S h8)
  have h14 := R v9
  have h15 := h v9 v9 v3
  have h16 := C h14 (T h15 (C h14 (T (T h11 h6) h13)))
  have h17 := R y
  have h18 := C h12 h8
  have h19 := h z z v3
  have h20 := h v3 z x
  have h21 := R z
  have h22 := C h21 (T (C h21 (T (T h18 h7) h20)) (S h19))
  have h23 := R v0
  have h24 := S h20
  T (T (h v3 v1 v9) (C h2 (T (T (T (C h2 (C h12 (T (T (T h16 h11) h20) h22))) (C h2 (T (T (C h12 (T (C h21 (T h19 (C h21 (T (T h24 h6) h13)))) h24)) h18) h7))) (C h2 (h v3 v1 x))) (S (h v1 v1 v3))))) (C (T (C h21 (C h21 (T (T h4 (C h17 (S h5))) (C h17 (T (h v3 y v0) (C h17 (T (T (C h17 (T (C h12 (T (C h23 (T (T (h v0 v0 v3) (C h23 (S (h v3 v0 x)))) (C h23 (T (T h6 h13) (C h12 (T h20 h22)))))) (S (h v3 v0 z)))) (C h12 (T h10 (C h14 (T (C h14 (T (T h18 h7) h10)) (S h15))))))) (C h17 (T (T (C h12 (T (T h16 h11) h8)) h7) h5))) (S h4)))))))) (S (h y z y))) h2)

@[equational_result]
theorem Equation2714_implies_Equation2779 (G: Type _) [Magma G] (h: Equation2714 G) : Equation2779 G := fun x y z =>
  let v0 := M x z
  let v1 := M y z
  let v2 := M v1 v0
  let v3 := M v2 y
  let v4 := M v3 v3
  have h5 := R v3
  have h6 := h v2 v3 v3
  let v7 := M v2 v2
  have h8 := R z
  have h9 := S (h v2 x v3)
  have h10 := T (h v3 (M (M x v2) (M x v3)) v3) (C (C h9 h9) h5)
  have h11 := R v1
  have h12 := S (h y x v1)
  let v13 := M x x
  have h14 := h v0 (M v13 (M x v0)) v0
  have h15 := R v0
  have h16 := h x x v0
  have h17 := T (C (C h16 h16) h15) (S h14)
  have h18 := S h16
  have h19 := R y
  have h20 := T (C h10 h19) (S (h v2 v2 y))
  T (T (T (T (T (h x x z) (C h17 h8)) (C (T (T (h v0 v1 v0) (C (T (T (T (h v7 v3 y) (C (T (C (R (M v3 v7)) h20) (S (h y v2 v2))) h19)) (C (T (h y v3 v3) (C (C h20 (R v4)) h5)) h19)) (S (h v4 v2 y))) (T (T (T h14 (C (C h18 h18) h15)) (h (M v13 v0) v1 z)) (C (T (C (C h11 h17) (R (M v1 z))) (C (R v2) (T (C (T (h v1 (M (M x y) (M x v1)) v1) (C (C h12 h12) h11)) h8) (S (h y y z))))) h8)))) (C (C h5 h10) (R (M v3 z)))) h8)) (S (h (M v7 v3) v3 z))) (C (C h6 h6) h5)) (S (h v3 (M (M v3 v2) v4) v3))

@[equational_result]
theorem Equation1967_implies_Equation1790 (G: Type _) [Magma G] (h: Equation1967 G) : Equation1790 G := fun x y z =>
  let v0 := M y z
  let v1 := M z x
  let v2 := M v1 y
  let v3 := M v0 v2
  have h4 := h v0 v0 (M z (M y v2))
  have h5 := S h4
  have h6 := h v2 z y
  have h7 := R v0
  have h8 := C (C h7 h6) h6
  have h9 := h y v3 v1
  let v10 := M v1 v3
  have h11 := h v10 x y
  have h12 := R (M y x)
  have h13 := R v10
  have h14 := h y v0 v1
  have h15 := h v0 v3 v1
  have h16 := R x
  have h17 := h z x y
  have h18 := T (T h17 (C (C h16 (T h15 (C (S h14) h13))) h12)) (S h11)
  have h19 := S h6
  have h20 := R v1
  have h21 := R v3
  have h22 := h v1 v1 (M x (M z y))
  have h23 := h y x z
  have h24 := S h23
  T (T (h x v0 z) (C (T (T (C h7 (T h22 (C (C h20 h24) h24))) (h (M v0 (M v2 y)) v3 z)) (C (T (T (T (C h21 (T (T (T (C (R z) (C h7 (T (C (C h20 h23) h23) (S h22)))) (C h18 (R (M v0 v1)))) (S (h v2 v1 v0))) (C h20 (T h9 (C (T h8 h5) (T (T h11 (C (C h16 (T (C h14 h13) (S h15))) h12)) (S h17))))))) (C h21 (C h20 (T (C (T h4 (C (C h7 h19) h19)) h18) (S h9))))) h8) h5) (R (M z v3)))) (R (M z v0)))) (S (h v3 v0 z))

@[equational_result]
theorem Equation3404_implies_Equation3414 (G: Type _) [Magma G] (h: Equation3404 G) : Equation3414 G := fun x y z =>
  let v0 := M x y
  let v1 := M z v0
  let v2 := M z v1
  let v3 := M z z
  have h4 := h v1 z z
  have h5 := R z
  have h6 := h x y v0
  let v7 := M y (M v0 x)
  have h8 := h v0 x z
  have h9 := h y z x
  have h10 := R y
  have h11 := h z z y
  have h12 := R v2
  have h13 := R v1
  have h14 := T (T (h z v0 z) (h z (M v0 v3) v1)) (C h13 (T (C (T (T (T (h v0 v3 v2) (C h12 (C (T h11 (C h10 (T (C h5 h9) (S h8)))) (R (M v2 v0))))) (S (h v0 v7 v2))) (S h6)) (T h4 (C h5 (S (h v0 z z))))) (S (h z z v0))))
  let v15 := M y z
  let v16 := M v0 z
  let v17 := M v1 v16
  let v18 := M v1 z
  have h19 := R v0
  T (T (T (T (T (T h6 (h v0 v7 v1)) (C h13 (C (T (C h10 (T h8 (C h5 (S h9)))) (S h11)) (T (T (T (T (T (T (h v1 v0 v0) (C h19 (T (T (T (T (C h19 (T (T (T (T (C h19 (h z v0 v1)) (S (h v18 v1 v0))) (h v18 v1 v1)) (C h13 (S (h z v1 v1)))) (C h13 (h z v1 v0)))) (S (h v17 v1 v0))) (h v17 v1 v1)) (C h13 (T (S (h v16 v1 v1)) (C (R v16) h14)))) (S (h v3 v16 v1))))) (S (h z v3 v0))) (C h5 h11)) (S (h v15 y z))) (h v15 y v1)) (C h13 (S (h z v1 y))))))) (S (h v2 v3 v1))) (C h12 (T (h z z v1) (C h14 (T (C h5 h4) (S (h v2 z z))))))) (S (h z (M v1 v3) v2))) (S (h z v1 z))

