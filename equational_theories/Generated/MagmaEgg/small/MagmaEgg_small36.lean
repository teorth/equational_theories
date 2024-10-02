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
theorem Equation2113_implies_Equation3740 (G: Type _) [Magma G] (h: Equation2113 G) : Equation3740 G := fun x y z =>
  let v0 := M z y
  let v1 := M x z
  let v2 := M v1 v0
  have h3 := h v2 v1 v0
  have h4 := R v2
  let v5 := M v2 v2
  have h6 := h v5 v0 v5
  have h7 := R v5
  have h8 := h v0 v1 v0
  have h9 := S h8
  have h10 := C h9 h7
  have h11 := h v0 v2 v2
  have h12 := S h11
  have h13 := C h8 h7
  have h14 := R v0
  have h15 := h v1 (M (M x v1) z) v1
  have h16 := h v1 x z
  have h17 := R v1
  let v18 := M v1 v1
  have h19 := h v18 z y
  have h20 := R y
  have h21 := R v18
  have h22 := h z x z
  have h23 := h z v1 v1
  let v24 := M x y
  let v25 := M v2 v24
  have h26 := R v24
  have h27 := S h16
  have h28 := S (h v1 z y)
  have h29 := S (h v24 x z)
  have h30 := S (h y v24 v1)
  let v31 := M v24 v1
  have h32 := S (h v2 x y)
  T (T (T (T (h v24 (M (M x v2) y) v24) (C (C h32 h26) h32)) (C (T (T (T (h v25 v1 v0) (C (C (T (T (T (C (T (T (h v1 (M (M x v24) z) v1) (C (T (T (C h29 h17) (h v31 (M (M v24 y) v1) v31)) (C (T (C (T h30 (h y x z)) (R v31)) (S (h z v24 v1))) h30)) h29)) (C (T (T (h v0 (M (M z v1) y) v0) (C (C h28 h14) h28)) (C h4 (T h15 (C (T (T (C h27 h17) h19) (C (C (T (C h22 h21) (S h23)) h20) h14)) h27)))) h26)) (R v25)) (S (h (M (M v0 v0) v1) v2 v24))) (C (T (T (C (C (T h23 (C (S h22) h21)) h20) h14) (S h19)) (C h16 h17)) h16)) (S h15)) h14) h4)) h6) (C (T (C (T (T h13 h12) h8) h7) h12) (T h13 h12))) h4)) (C (T (T (C (T h11 (C (T (T h9 h11) h10) h7)) (T h11 h10)) (S h6)) (C h3 h4)) h3)) (S (h v2 (M (M v1 v2) v0) v2))

@[equational_result]
theorem Equation2196_implies_Equation4450 (G: Type _) [Magma G] (h: Equation2196 G) : Equation4450 G := fun x y z =>
  let v0 := M y z
  let v1 := M v0 z
  let v2 := M (M v1 v0) v0
  let v3 := M y x
  let v4 := M x v3
  let v5 := M (M z z) z
  let v6 := M y v3
  have h7 := h x v3 z
  have h8 := S h7
  have h9 := h y x v3
  have h10 := S h9
  have h11 := C h10 h8
  let v12 := M (M v3 z) z
  have h13 := h v12 v4 v3
  have h14 := h v12 y x
  have h15 := h y x z
  have h16 := S h15
  have h17 := R v12
  let v18 := M (M x z) z
  have h19 := h v18 v3 z
  have h20 := h v18 v3 v4
  let v21 := M v3 v4
  let v22 := M v21 v4
  have h23 := R v22
  have h24 := R (M v3 x)
  have h25 := h v22 y x
  have h26 := h y x x
  have h27 := h v12 v4 x
  let v28 := M (M v4 x) x
  have h29 := R v28
  have h30 := R (M (M x x) x)
  have h31 := h v28 x x
  have h32 := h v21 v4 x
  have h33 := S h13
  have h34 := C h9 h7
  let v35 := M v4 v0
  let v36 := M v35 v0
  T (T (T (T (h v4 v0 v4) (C (R (M (M v0 v4) v4)) (T (T (T (T (h v35 v0 v3) (C (R (M (M v0 v3) v3)) (T (T (T (h v36 v6 v4) (C (R (M (M v6 v4) v4)) (T (T (T (C (R v36) (T (C (T (T h26 (C h30 (T (T (T h34 h33) h27) (C h29 h8)))) (S h31)) (T (T (T (T h34 h33) h14) (C h24 (T (T (T (C h17 h15) (S h19)) h20) (C h23 h16)))) (S h25))) (S h32))) (S (h v3 v4 v0))) (h v3 v4 v3)) (C h10 (T h32 (C (T (T h31 (C h30 (T (T (T (C h29 h7) (S h27)) h13) h11))) (S h26)) (T (T (T (T h25 (C h24 (T (T (T (C h23 h15) (S h20)) h19) (C h17 h16)))) (S h14)) h13) h11))))))) (S (h y v6 v4))) (h y z z)))) (S (h v5 v0 v3))) (h v5 v1 v0)) (C (R v2) (S (h v0 z z)))))) (S (h v2 v0 v4))) (h v2 (M z v1) v1)) (C (S (h v0 z v1)) (S (h z v1 v0)))

@[equational_result]
theorem Equation4197_implies_Equation4612 (G: Type _) [Magma G] (h: Equation4197 G) : Equation4612 G := fun x y z =>
  let v0 := M x x
  let v1 := M y z
  let v2 := M v1 z
  have h3 := R v2
  have h4 := R v0
  have h5 := R z
  let v6 := M v0 y
  have h7 := S (h v0 v1 v6)
  have h8 := R v6
  have h9 := R v1
  have h10 := R y
  have h11 := h x x v0
  have h12 := h x x x
  have h13 := C (T (C h12 h4) (S h11)) h10
  have h14 := C h13 h4
  have h15 := h v0 y v0
  have h16 := S h15
  have h17 := S h12
  have h18 := C h17 h4
  have h19 := C (T h11 h18) h10
  have h20 := C h19 h4
  have h21 := C (T (T h20 h16) h19) h4
  have h22 := C (T h21 h16) h8
  have h23 := h v0 v0 v6
  have h24 := h v0 v1 y
  have h25 := h y v0 v0
  have h26 := S h25
  have h27 := C (T (T h13 h15) h14) h4
  have h28 := C (T (T (T (T (T (T (C (T (C (T (h v0 y v1) (C (S (h z v0 y)) h9)) h5) (S (h v0 v1 z))) h10) (C (T h24 (C (T (T (T (C (T (T h25 h21) h16) h9) (h v6 v1 v0)) (C (C (T (T (T (C (T h11 (C (T (T (T (T h17 h11) h18) h23) h22) h4)) h8) (S (h v6 v0 v6))) h20) h16) h9) h4)) (S (h y v1 v0))) h10)) h10)) (S (h v1 y y))) (h v1 y v6)) (C (T (T (C (C (T (T h15 h27) h26) h9) h10) (S h24)) (C (T (T (T h11 h18) h23) h22) h9)) h8)) (S (h v6 v1 v6))) (C (T h15 h14) h9)) h8
  have h29 := h z y v6
  T (T (T (T (T h15 h14) (h v6 v0 v2)) (C (C (C h3 (T (T (T (T (T (T (T h15 h27) h26) (h y v0 y)) (C (T (C (T (h y y v1) (C (T (T (T (S (h z y y)) h29) h28) h7) h9)) h4) (S (h v1 v1 v0))) h10)) (S (h z v1 y))) (h z v1 z)) (C (T (T (T (T (C (h z z y) h9) (S (h z y v1))) h29) h28) h7) h5))) h4) h3)) (S (h (M (M v0 v1) z) v0 v2))) (S (h v1 z v0))

@[equational_result]
theorem Equation1507_implies_Equation2335 (G: Type _) [Magma G] (h: Equation1507 G) : Equation2335 G := fun x y z =>
  let v0 := M x z
  let v1 := M y v0
  let v2 := M y v1
  let v3 := M v2 z
  have h4 := R (M v0 (M v0 z))
  let v5 := M z v3
  let v6 := M z v5
  let v7 := M v3 (M v3 v2)
  have h8 := S (h v7 v1 x)
  have h9 := h v1 y v0
  let v10 := M v0 (M v0 y)
  let v11 := M z (M z v2)
  have h12 := C (T (T (T (C h9 (R v11)) (S (h v10 v2 z))) (h v10 v2 v3)) (C (S h9) (R v7))) (R (M x (M x v1)))
  have h13 := h v11 v1 x
  have h14 := R v2
  have h15 := h z x v3
  have h16 := S h15
  let v17 := M v3 (M v3 x)
  have h18 := h v17 v0 y
  have h19 := R z
  have h20 := C h19 (T h18 (C h16 h14))
  have h21 := S h18
  have h22 := h v2 (M v0 x) v0
  have h23 := h z x v0
  have h24 := h x v0 y
  have h25 := T (C h24 h23) (S h22)
  let v26 := M z v0
  let v27 := M z v26
  let v28 := M x v0
  let v29 := M z x
  T (T (T (T (T (T (T (T (T (h x z y) (C (T (T (h v29 z x) (C (T (T (T (T (h (M z v29) v0 x) (C (T (S (h z x z)) h15) (R (M x v28)))) (S (h v17 v0 x))) (h v17 v0 z)) (C h16 (R v27))) (R v28))) (S (h v27 z x))) (R (M y (M y z))))) (S (h v26 z y))) (C h19 h25)) (C h15 h14)) h21) (h v17 z v0)) (C (T (T (T h20 h13) h12) h8) h4)) (C (T (T (T (T (T (T (h v7 (M v2 y) v2) (C (S (h y v2 v3)) (S (h v1 y v2)))) h22) (C (S h24) (S h23))) (h v0 z z)) (C (T (T (T (T (C h15 h25) h21) (h v17 z v3)) (C (T (T (T (T (T h20 h13) h12) h8) (h v7 v3 z)) (C (S (h z v2 v3)) (R v6))) (R (M v3 (M v3 z))))) (S (h v6 z v3))) (R (M z (M z z))))) (S (h v5 z z))) h4)) (S (h v3 z v0))

@[equational_result]
theorem Equation3211_implies_Equation1320 (G: Type _) [Magma G] (h: Equation3211 G) : Equation1320 G := fun x y z =>
  let v0 := M y x
  let v1 := M v0 z
  let v2 := M v1 z
  let v3 := M y v2
  have h4 := S (h v3 y v3)
  have h5 := R y
  have h6 := R v3
  have h7 := h y v2 v2
  have h8 := S h7
  have h9 := h v2 v1 v2
  have h10 := S h9
  have h11 := R v1
  have h12 := R v2
  have h13 := R z
  have h14 := h v0 v0 z
  have h15 := C (C (S h14) h13) h12
  have h16 := h z v2 v0
  have h17 := C (C (C (T h16 h15) h12) h12) h11
  have h18 := h z v1 z
  have h19 := h v1 v2 z
  have h20 := C (T h19 (C (S h18) h12)) h12
  have h21 := h z v0 z
  have h22 := S h21
  have h23 := h v0 v1 z
  have h24 := T (T (T h23 (C (T (T (T h22 h16) h15) h20) h11)) h17) h10
  have h25 := R (M v2 v2)
  have h26 := h v2 v0 z
  have h27 := R v0
  have h28 := h y v3 v0
  have h29 := S h23
  have h30 := S h16
  have h31 := C h14 h13
  have h32 := C (T (T (C (T (T (C (T (T (C h31 h12) h30) h18) h12) (S h19)) h31) h12) h30) h21) h11
  have h33 := T (T h9 h32) h29
  have h34 := h v0 y v2
  have h35 := C (C (T (T (T (T (T (T (T (T (C (T (h v3 v0 v3) (C (C (C (T (C (T h34 (C (C (C h6 h33) h27) h5)) h6) (S h28)) h6) h6) h27)) h5) (S (h v0 y v3))) h23) (C h22 h11)) (C (T (T h16 h15) h20) h11)) h17) h10) h26) (C h25 h24)) h5) h24
  have h36 := h v0 v3 y
  have h37 := C (T (T (T (T h35 h8) h28) (C (T (C (C (C h6 h24) h27) h5) (S h34)) h6)) (C (T h36 (C (T h35 h8) h6)) h6)) h6
  T (T (h x y y) (C (T (T (C (T (C (C (T h7 (C (T (C (T (T (T (T (T (T (C h25 h33) (S h26)) h9) h32) h29) h36) h37) h5) h4) h12)) h5) h5) (S (h y y v2))) (R x)) h36) h37) h5)) h4

@[equational_result]
theorem Equation2196_implies_Equation1165 (G: Type _) [Magma G] (h: Equation2196 G) : Equation1165 G := fun x y z =>
  let v0 := M y x
  let v1 := M z v0
  let v2 := M v1 z
  let v3 := M y v2
  let v4 := M v2 v3
  let v5 := M v4 v3
  have h6 := h v1 z v2
  have h7 := S h6
  let v8 := M (M z v2) v2
  have h9 := S (h v8 v2 z)
  let v10 := M v2 z
  let v11 := M v10 z
  have h12 := C (R v11) h6
  have h13 := R (M (M v1 x) x)
  have h14 := h v11 v1 x
  have h15 := C (R v10) (S (h z v0 v0))
  let v16 := M (M v0 v0) v0
  have h17 := h v16 v1 z
  have h18 := S (h v16 y x)
  have h19 := h y x v3
  have h20 := C (R v16) (S h19)
  let v21 := M (M x v3) v3
  have h22 := h v21 v0 v0
  let v23 := M v0 v3
  let v24 := M v23 v3
  let v25 := M v0 x
  have h26 := R v25
  have h27 := C h26 (T (T (T (C (R v24) h19) (S (h v21 v0 v3))) h22) h20)
  have h28 := h v24 y x
  let v29 := M (M v3 v2) v2
  let v30 := M (M v2 y) y
  let v31 := M x y
  T (T (T (T (T (h x y v1) (C (R (M (M y v1) v1)) (T (T (T (T (T (T (T (T (T (h v31 y x) (C h26 (T (T (T (T (h (M v31 y) v0 x) (C (R (M v25 x)) (T (S (h y x y)) h19))) (S (h v21 v0 x))) h22) h20))) h18) h17) h15) h14) (C h13 (T (T (T h12 h9) (h v8 v2 y)) (C (R v30) h7)))) (S (h v30 v1 x))) (h v30 v3 v2)) (C (R v29) (S (h y v2 y)))))) (S (h v29 y v1))) (h v29 v23 v3)) (C (T (C (T (T (T (T h28 h27) h18) h17) h15) (R v3)) (S (h y v2 z))) (S (h v0 v3 v2)))) (C (R y) (T (T (h v0 v3 v1) (C (R (M (M v3 v1) v1)) (T (T (h v23 v3 x) (C (R (M (M v3 x) x)) (T (T (T (T (T (T (T h28 h27) h18) h17) h15) h14) (C h13 (T (T (T h12 h9) (h v8 v2 v3)) (C (R v5) h7)))) (S (h v5 v1 x))))) (S (h v4 v3 x))))) (S (h v2 v3 v1))))

@[equational_result]
theorem Equation2929_implies_Equation2 (G: Type _) [Magma G] (h: Equation2929 G) : Equation2 G := fun x y =>
  have h0 := h y y x
  have h1 := S h0
  have h2 := R x
  let v3 := M y x
  let v4 := M x v3
  have h5 := h x y x
  let v6 := M y (M x x)
  let v7 := M v6 x
  have h8 := h x x y
  have h9 := S h8
  have h10 := R y
  let v11 := M x y
  let v12 := M x v11
  let v13 := M v12 y
  have h14 := h x y y
  let v15 := M y v11
  let v16 := M v15 y
  have h17 := h y x y
  have h18 := S h17
  have h19 := R v12
  let v20 := M y y
  let v21 := M x v20
  let v22 := M v21 y
  have h23 := h v22 v12 y
  have h24 := h v22 x y
  have h25 := S h24
  have h26 := h y y y
  have h27 := C (C (T (C h2 (S h26)) (C h2 h17)) h10) h10
  let v28 := M y v20
  have h29 := h (M v28 y) x y
  have h30 := S h29
  have h31 := C (C (T (C h2 h18) (C h2 h26)) h10) h10
  T (T (T (T (T (T h8 (C (T (T (T (h v13 y y) (C (C (T (C h10 h9) (C h10 h14)) h10) h10)) (S (h v16 y y))) (C (C h10 (T (T (T (T (C (T h8 (C (C h19 h17) h10)) h10) (S h23)) h24) h31) h30)) h10)) h10)) (C (C (C h10 (T (T h29 h27) h25)) h10) h10)) (S (h v21 y y))) (h v21 y x)) (C (C (C h10 (T (T (C (T (T (T (T (T (h v21 x y) (C (C (C h2 (T (T h24 h31) h30)) h10) h10)) (S (h v28 x y))) (h v28 y x)) (C (C (C h10 (T (T (C (T (T (h v28 y y) (C (C (T (T (T (C h10 (T (T (T (T h29 h27) h25) h23) (C (T (C (C h19 h18) h10) h9) h10))) (h v15 x y)) (C (C (C h2 (T (T (h v16 x y) (C (C (T (C h2 (S h14)) (C h2 h8)) h10) h10)) (S (h v13 x y)))) h10) h10)) (S (h v12 x y))) h10) h10)) h9) h2) (C (T h5 (C (C (R v6) h5) h2)) h2)) (S (h v7 v6 x)))) h2) h2)) (S (h v6 y x))) h2) (h v7 v4 x)) (C (T (C (T (T (T (C (R v4) (S h5)) (h (M v4 x) x x)) (C (C (T (C h2 (S (h y x x))) (C h2 h0)) h2) h2)) (S (h (M (M y v3) x) x x))) h2) h1) h2))) h2) h2)) h1

@[equational_result]
theorem Equation3385_implies_Equation4461 (G: Type _) [Magma G] (h: Equation3385 G) : Equation4461 G := fun x y z =>
  let v0 := M z z
  let v1 := M y x
  have h2 := R z
  have h3 := h v0 v1 z
  have h4 := S h3
  have h5 := h v1 z z
  have h6 := R v0
  have h7 := C h6 (S h5)
  have h8 := h z v1 v0
  have h9 := C h2 (T h8 h7)
  have h10 := C h2 (T (C h6 h5) (S h8))
  have h11 := h v0 v1 y
  have h12 := h v1 y x
  have h13 := S h12
  let v14 := M v0 y
  have h15 := h x (M v1 v1) v14
  have h16 := S h15
  have h17 := R v14
  have h18 := h v1 v1 v0
  have h19 := h v1 v0 v0
  have h20 := S h19
  have h21 := h z z z
  have h22 := S h21
  have h23 := h z z v0
  have h24 := T h23 (C h6 h22)
  have h25 := R v1
  have h26 := C h6 (C h25 h24)
  have h27 := h v0 v1 v0
  have h28 := h z z v1
  have h29 := R x
  have h30 := C h17 (C h29 (C (T (T h23 (C h6 (T (T h22 h28) (C h25 (T (T (T (T (T h9 h4) h27) (C h6 (T h26 h20))) h26) h20))))) (S h18)) h17))
  have h31 := h x v0 v14
  have h32 := S h23
  have h33 := T (C h6 h21) h32
  have h34 := h x v0 v0
  have h35 := R y
  have h36 := C h6 (C h25 h33)
  T (T (T (h x v1 z) (C h2 (C h29 (T (T (C (T (T (T (T (h y x z) (C h2 (T (T (T (C h35 (T (h x z z) (C h2 (T (T (T h31 h30) h16) h13)))) (S (h z v1 y))) h8) h7))) h4) h11) (C h35 (T (C h6 (T (T (T (T h12 h15) (C h17 (C h29 (C (T (T h18 (C h6 (T (T (C h25 (T (T (T (T (T h19 h36) (C h6 (T h19 h36))) (S h27)) h3) h10)) (S h28)) h21))) h32) h17)))) (S h31)) (C h29 h24))) (S h34)))) h2) (C (T (T (T (C h35 (T h34 (C h6 (T (T (T (T (C h29 h33) h31) h30) h16) h13)))) (S h11)) h3) h10) h2)) (C (T h9 h4) h2))))) (S (h x (M v0 v1) z))) (S (h v0 y x))

@[equational_result]
theorem Equation3404_implies_Equation3537 (G: Type _) [Magma G] (h: Equation3404 G) : Equation3537 G := fun x y z =>
  let v0 := M x y
  let v1 := M z z
  let v2 := M v1 y
  have h3 := h v0 x z
  have h4 := h y z x
  have h5 := R z
  have h6 := R v2
  have h7 := h z z v2
  let v8 := M x v2
  let v9 := M v2 z
  have h10 := h v2 z y
  have h11 := h v1 y v1
  have h12 := h y (M v1 v1) v8
  have h13 := R (M v8 y)
  have h14 := h v1 v1 z
  have h15 := S h14
  have h16 := h z v1 z
  have h17 := S h16
  have h18 := R v1
  have h19 := h v1 z v1
  have h20 := h v1 z z
  have h21 := h z z z
  have h22 := S h21
  let v23 := M z v1
  have h24 := h v23 v1 z
  have h25 := C h5 (T (T (T (T (T (T h24 (C h5 (C h18 h22))) h17) (C h5 h21)) (S h20)) h19) (C h18 h17))
  have h26 := h z v23 z
  have h27 := R v8
  have h28 := h y v1 v8
  have h29 := R y
  have h30 := h v1 v1 y
  have h31 := h v1 y z
  have h32 := S h26
  have h33 := C h5 (T (T (T (T (T (T (C h18 h16) (S h19)) h20) (C h5 h22)) h16) (C h5 (C h18 h21))) (S h24))
  T (T (h x y v0) (C (R v0) (T (T (T (T (T (C h29 (T h3 (C h5 (S h4)))) (S (h z z y))) h7) (h v2 (M z v9) v2)) (C h6 (C (T (C h5 (T h10 (C h29 (C h5 (T (T (T (T (T (C h29 (T h11 (C h18 (T (T h12 (C h27 (C (T (T (T h14 h33) h32) h22) h13))) (S h28))))) (S h30)) h14) h33) h32) h22))))) (S h31)) (T (C h6 (T (T (T h31 (h z (M y v23) v8)) (C h27 (C (T (C h29 (C h5 (T (T (T (T (T h21 h26) h25) h15) h30) (C h29 (T (C h18 (T (T h28 (C h27 (C (T (T (T h21 h26) h25) h15) h13))) (S h12))) (S h11)))))) (S h10)) (R (M v8 z))))) (S (h z v9 v8)))) (S h7))))) (C h6 (T (T (T (h v2 v1 z) (C h5 (S (h y z v1)))) (C h5 h4)) (S h3)))))) (S (h x v2 v0))

@[equational_result]
theorem Equation1910_implies_Equation3617 (G: Type _) [Magma G] (h: Equation1910 G) : Equation3617 G := fun x y z =>
  let v0 := M z x
  let v1 := M v0 y
  let v2 := M z v1
  have h3 := R v2
  have h4 := h x v0 y
  have h5 := R z
  have h6 := C (C h5 (S h4)) h3
  let v7 := M x y
  have h8 := h (M v0 v7) z v1
  have h9 := T h8 h6
  let v10 := M x v1
  let v11 := M v2 v2
  have h12 := h v11 v10 v7
  have h13 := S h12
  have h14 := h v0 x y
  have h15 := R v7
  have h16 := h v2 z v1
  have h17 := S h16
  let v18 := M z (M v2 v1)
  have h19 := R v18
  have h20 := C (T (C h19 h17) h17) h17
  have h21 := h v18 v18 v2
  have h22 := h v18 v0 v2
  have h23 := S h22
  have h24 := R v0
  have h25 := h v7 x y
  have h26 := S h25
  have h27 := C (T (T (T (C h24 h26) h8) h6) (C h24 h16)) h9
  have h28 := h (M x (M v7 y)) v0 v7
  have h29 := C (T (T (T (T h28 h27) h23) h21) h20) h15
  have h30 := T h25 h29
  have h31 := R v10
  have h32 := C (T h14 (C h31 h30)) h14
  have h33 := T h32 h13
  have h34 := S h14
  have h35 := S h28
  have h36 := S h8
  have h37 := C (C h5 h4) h3
  have h38 := C (T (T (T (C h24 h17) h37) h36) (C h24 h25)) (T h37 h36)
  have h39 := S h21
  have h40 := C (T h16 (C h19 h16)) h16
  have h41 := C (T (C h31 (T (C (T (T (T (T h40 h39) h22) h38) h35) h15) h26)) h34) h34
  have h42 := C (T (T (T (T (T (T h28 h27) h23) h21) h20) h12) h41) h15
  T (T (h v7 v0 v7) (C (T (C h24 (T (T (T (T (C h15 (T h25 h42)) (C (T (T h25 h42) (C h33 h30)) (T (C (T (T (T (T (T (T h32 h13) h40) h39) h22) h38) h35) h15) h29))) (S (h v11 v11 v7))) h12) h41)) (C h24 h33)) h9)) (S (h v2 v0 v2))

@[equational_result]
theorem Equation3211_implies_Equation4544 (G: Type _) [Magma G] (h: Equation3211 G) : Equation4544 G := fun x y z =>
  let v0 := M y z
  let v1 := M x v0
  let v2 := M z y
  let v3 := M v2 x
  have h4 := R v2
  have h5 := R v3
  have h6 := R v1
  have h7 := R x
  have h8 := S (h x v1 v0)
  have h9 := h v0 x v0
  have h10 := R z
  have h11 := R y
  have h12 := R v0
  have h13 := h z y v0
  have h14 := h y v0 z
  have h15 := h z y z
  have h16 := h v0 z v0
  have h17 := h v0 v0 y
  have h18 := S h16
  have h19 := C (C (C (T h14 (C (S h15) h12)) h12) h12) h10
  have h20 := C (T (C (T (C (C (T (h z z y) (C (C (T (C (T (h v2 z v2) (C (C (C (T (C (T h13 (C (T (T (T h19 h18) h17) (C (C (C (T (C (T h16 (C (C (C (T (C h15 h12) (S h14)) h12) h12) h10)) h11) (S h13)) h11) h12) h12)) h11)) h4) (S (h y v2 v0))) h4) h4) h10)) h11) (S (h z y v2))) h10) h10)) h11) h10) (S (h y z z))) h10) h9) h6
  have h21 := h v1 v2 z
  have h22 := C (T (C (C (C (T h21 (C (T h20 h8) h4)) h4) h4) h7) (S (h v2 x v2))) h6
  have h23 := h x v1 v2
  have h24 := S (h x v0 v0)
  have h25 := S (h v0 x v1)
  have h26 := C (C (C (T (C h9 h6) h8) h6) h6) h12
  have h27 := h v1 v0 v1
  have h28 := C (T (T (T (C (C (C (T h23 h22) h6) h6) h4) (S (h v1 v2 v1))) h27) h26) h7
  have h29 := h v2 x v1
  have h30 := C (C (T (C (C (C (T h13 (C (T h19 h18) h11)) h11) h12) h12) (S h17)) h12) (T (T h29 h28) h25)
  have h31 := h v0 v2 v0
  T (T h21 (C (T (T (T h20 h8) (h x v3 v1)) (C (T (T (T (C (T (T (T (C (C (T (h v3 v3 v0) (C (C (C (T (C (C (T (T (T (T h29 h28) h25) h31) h30) h7) h12) h24) h12) h5) h5)) h6) h6) (S (h v1 v1 v3))) h27) h26) h7) h25) (h v0 v1 x)) (C (T (T (T (C (C (T (T (T (C (T h27 h26) h7) h25) h31) h30) h7) h12) h24) h23) h22) h6)) h5)) h4)) (S (h v3 v2 v1))

@[equational_result]
theorem Equation522_implies_Equation2573 (G: Type _) [Magma G] (h: Equation522 G) : Equation2573 G := fun x y z =>
  let v0 := M z x
  let v1 := M y (M v0 y)
  let v2 := M v1 z
  have h3 := h v1 v2 z
  have h4 := S h3
  have h5 := R v2
  have h6 := h z v2 v2
  have h7 := T h6 (C h5 h4)
  have h8 := R v1
  have h9 := C h8 h7
  have h10 := h v2 z z
  have h11 := S h10
  have h12 := T (C h5 h3) (S h6)
  have h13 := C h5 h12
  have h14 := h v0 v2 y
  have h15 := h v0 v0 v2
  have h16 := S h15
  have h17 := C h8 h12
  have h18 := R v0
  have h19 := h v2 v0 z
  have h20 := R z
  have h21 := h z v0 v0
  have h22 := T (T h14 h13) (C h5 (T (T h21 (C h18 (T (T (C h18 (C h18 (C h20 (T h14 h13)))) (S h19)) h9))) (C h18 h17)))
  have h23 := C h18 (C h18 h22)
  have h24 := C h20 (C h20 (T (T (T h23 h16) h14) h13))
  have h25 := h v0 z v0
  have h26 := h v0 v1 v2
  have h27 := h v0 v2 v0
  have h28 := S h14
  have h29 := C h5 h7
  have h30 := T (T (C h5 (T (T (C h18 h9) (C h18 (T (T h17 h19) (C h18 (C h18 (C h20 (T h29 h28))))))) (S h21))) h29) h28
  have h31 := S h27
  have h32 := C h18 (C h18 h30)
  have h33 := S h25
  have h34 := C h5 (C h5 (T (T (T (C h20 (T h10 (C h20 (T (T (T (C h20 (C h20 (T (T (T h29 h28) h15) h32))) h33) h15) h32)))) h33) h15) h32))
  have h35 := C (T (T h3 h34) h31) (C h8 h30)
  have h36 := S (h v1 x v0)
  have h37 := R x
  T (T (T (h x v2 z) (C h5 (C h5 (T (T (C h20 (T (T (T (T (T (T (C h37 (T (h z x x) (C h37 (T (T (T (T (T (T (C h37 (C h37 (T h26 h35))) h36) h3) h34) h31) h26) h35)))) h36) h3) h34) h31) h26) h35)) (C h20 (T (T (T (C (T (T h27 (C h5 (C h5 (T (T (T h23 h16) h25) (C h20 (T (C h20 (T (T (T h23 h16) h25) h24)) h11)))))) h4) (C h8 h22)) (S h26)) h25) h24))) h11)))) (C h5 (C h5 h9))) (S (h v2 v2 v1))

@[equational_result]
theorem Equation2789_implies_Equation1334 (G: Type _) [Magma G] (h: Equation2789 G) : Equation1334 G := fun x y z =>
  let v0 := M y z
  let v1 := M v0 x
  let v2 := M v1 z
  let v3 := M y v2
  have h4 := R z
  have h5 := h (M v2 v3) v3 v0
  have h6 := S h5
  have h7 := R v0
  have h8 := R v3
  have h9 := h v2 y z
  have h10 := h z y y
  have h11 := R y
  have h12 := h y x v0
  have h13 := S h12
  let v14 := M x y
  have h15 := h v0 (M (M x v0) v14) v0
  have h16 := T (C (T h15 (C (C h13 h13) h7)) h11) (S h10)
  have h17 := R (M v0 v3)
  have h18 := C (T (C h17 h16) (S h9)) h8
  have h19 := h y v0 v3
  have h20 := h v3 (M (M x v3) v14) v3
  have h21 := h y x v3
  have h22 := h v2 y y
  have h23 := R (M v3 v0)
  have h24 := h z y v2
  have h25 := C (T h24 (C h23 (T h22 (C (T (C (C h21 h21) h8) (S h20)) (T h19 h18))))) h7
  let v26 := M z v0
  have h27 := h v26 v0 y
  have h28 := S h19
  have h29 := C (T (C (C h12 h12) h7) (S h15)) h11
  have h30 := T h10 h29
  have h31 := C (T h9 (C h17 h30)) h8
  have h32 := T (T (T h25 h6) h31) h28
  have h33 := S h21
  have h34 := C (T (C h23 (T (T (C h8 (T h31 h28)) (C (T h20 (C (C h33 h33) h8)) h11)) (S h22))) (S h24)) h7
  have h35 := T (T (T h19 h18) h5) h34
  T (T (h x v2 z) (C (C (R (M v2 z)) (T (T (T (T (T (C (C (R v1) (T (T h10 h29) (C h7 (T (T (T (T (T h19 h18) h5) h34) h27) (C (T (C h16 (C h7 h32)) (C h4 h16)) h35))))) (R x)) (S (h (M (M z z) v26) v0 x))) (C (T (C h4 h30) (C h30 (C h7 h35))) h32)) (S h27)) h25) h6)) h4)) (S (h v3 v2 z))

@[equational_result]
theorem Equation684_implies_Equation522 (G: Type _) [Magma G] (h: Equation684 G) : Equation522 G := fun x y z =>
  let v0 := M z (M x z)
  let v1 := M y v0
  let v2 := M y v1
  have h3 := S (h v2 v2 x)
  let v4 := M v2 (M (M v2 x) x)
  let v5 := M v1 v2
  have h6 := R v2
  have h7 := h v1 v1 x
  have h8 := S h7
  let v9 := M v1 (M (M v1 x) x)
  have h10 := R v9
  have h11 := T (C h8 h10) h8
  have h12 := R y
  have h13 := R v1
  have h14 := h y v1 v9
  let v15 := M v0 (M (M v0 x) x)
  have h16 := R v15
  let v17 := M z (M (M z x) x)
  have h18 := h x z v17
  have h19 := R v17
  have h20 := h z z x
  have h21 := R x
  have h22 := R z
  have h23 := T (C h22 (C h21 (T h20 (C h20 h19)))) (S h18)
  have h24 := h v0 v0 x
  have h25 := T h24 (C (T h24 (C h23 h16)) h16)
  have h26 := R (M v5 v2)
  have h27 := h v0 v1 v0
  have h28 := S h24
  have h29 := S h20
  have h30 := T h18 (C h22 (C h21 (T (C h29 h19) h29)))
  let v31 := M v1 v0
  have h32 := R v31
  have h33 := h v31 x v15
  have h34 := S (h z z v2)
  let v35 := M z (M (M z v2) v2)
  T (T (T (T (T (T (T (h x z v35) (C h22 (C h21 (T (C h34 (R v35)) h34)))) h27) (C h13 (T (C h23 (C h32 h25)) (S h33)))) (h (M v1 v31) v1 v2)) (C h13 (T (T (T (C (T (C h13 (T h33 (C h30 (C h32 (T (C (T (C h30 h16) h28) h16) h28))))) (S h27)) h26) (C h23 h26)) (C h21 (T (T (T (C (T (C h13 (C h12 (T h7 (C h7 h10)))) (S h14)) h6) (C h12 (T (h v2 v1 v9) (C h13 (C h6 h11))))) (S (h v1 y v1))) (C h12 h25)))) (S (h y x v15))))) (C h13 (T (T (T h14 (C h13 (C h12 h11))) (h v5 v2 v4)) (C h6 (C (R v5) (T (C h3 (R v4)) h3)))))) (S (h v2 v1 v2))

@[equational_result]
theorem Equation2105_implies_Equation2355 (G: Type _) [Magma G] (h: Equation2105 G) : Equation2355 G := fun x y z =>
  let v0 := M z z
  let v1 := M y v0
  let v2 := M y v1
  let v3 := M v2 x
  have h4 := R v1
  have h5 := h y v0 z
  have h6 := R v0
  have h7 := R y
  have h8 := h v0 z x
  have h9 := S h8
  have h10 := R (M x x)
  have h11 := R z
  have h12 := h z z z
  have h13 := S h12
  have h14 := h z v0 z
  have h15 := C (T h14 (C h13 h6)) h11
  have h16 := h z v0 y
  let v17 := M y y
  have h18 := R v17
  have h19 := h v17 z x
  have h20 := h y y z
  have h21 := T h20 (C (C (T (T h19 (C (T (C (T (C h12 h18) (S h16)) h11) h15) h10)) h9) h7) h6)
  have h22 := C (T (C h21 h6) (S h5)) h4
  have h23 := R v3
  have h24 := S h20
  have h25 := S h19
  have h26 := C (T h16 (C h13 h18)) h11
  have h27 := C (T (C h12 h6) (S h14)) h11
  have h28 := C (C (T (T h8 (C (T h27 h26) h10)) h25) h7) h6
  have h29 := C (T h28 h24) h6
  let v30 := M v3 v3
  have h31 := R x
  let v32 := M v1 v1
  have h33 := h v32 z x
  have h34 := R v32
  have h35 := h z v0 v1
  have h36 := C (C (T (T (T (T (T (C h23 (C (T (T (T h8 (C (T h27 (C (T h35 (C h13 h34)) h11)) h10)) (S h33)) h22) h31)) (h v30 z x)) (C (T (C (T (C h12 (R v30)) (S (h z v0 v3))) h11) h26) h10)) h25) (C h7 h21)) (C h7 (T (T (T h28 h24) h5) h29))) h23) h22
  have h37 := h (M v0 x) v3 v1
  have h38 := C (T h5 h29) h4
  have h39 := C (T (T (T h38 h33) (C (T (C (T (C h12 h34) (S h35)) h11) h15) h10)) h9) h31
  T (T (h x v2 v0) (C (T (T (T (T (C (T (T h39 h37) h36) h38) (S (h v3 v2 v1))) h39) h37) h36) (R (M v0 v0)))) (S (h v3 v2 v0))

@[equational_result]
theorem Equation3398_implies_Equation3823 (G: Type _) [Magma G] (h: Equation3398 G) : Equation3823 G := fun x y z =>
  let v0 := M y x
  let v1 := M z z
  let v2 := M v1 v0
  let v3 := M x y
  have h4 := R v3
  let v5 := M z v2
  have h6 := h y x v0
  have h7 := h y y x
  have h8 := R v0
  have h9 := h v0 (M y y) v2
  have h10 := R (M v0 v2)
  have h11 := h y y z
  have h12 := h y z v1
  have h13 := h z y z
  have h14 := R v1
  have h15 := R y
  have h16 := h z v1 y
  have h17 := R z
  have h18 := h z z z
  have h19 := R v2
  have h20 := h v0 v1 v2
  have h21 := h v0 v1 v1
  have h22 := h z z v1
  have h23 := h v1 v0 v1
  have h24 := T (C h14 (T h23 (C h14 (C h8 (T (C h14 h18) (S h22)))))) (S h21)
  have h25 := S h18
  have h26 := h y x x
  have h27 := h x x v0
  have h28 := R x
  T (T (T (T (h x y y) (h y (M y v3) v2)) (C h19 (C (T (h y v3 v0) (C h8 (T (T (C h4 (T (T (h y v0 x) (C h28 (T (C h8 h26) (S h27)))) (C h28 (T (T (T (T h27 (C h8 (S h26))) (C h8 (T (T (T (T (T (T (T (T h6 (C h8 (S h7))) h9) (C h19 (C (T (T h11 (C h17 (T (C h15 (T h12 (C h14 (S h13)))) (S h16)))) h25) h10))) (S h20)) h21) (C h14 (T (C h14 (C h8 (T h22 (C h14 h25)))) (S h23)))) (h v1 v2 v2)) (C (T (T (T (h v1 v0 z) (h z (M v0 (M v1 z)) v2)) (C h19 (C (T (C h8 (T (h v1 z v2) (C h19 (T (C h17 h24) (S (h z v0 z)))))) (S (h z v2 v0))) (R v5)))) (S (h z v5 v2))) (T (C h19 h24) (C h19 (T (T (T (T h20 (C h19 (C (T (T h18 (C h17 (T h16 (C h15 (T (C h14 h13) (S h12)))))) (S h11)) h10))) (S h9)) (C h8 h7)) (S h6)))))))) (S (h v2 (M z v5) v0))) (S (h z z v2)))))) (C h4 (h x v1 y))) (S (h v1 y v3))))) (R (M y v2))))) (S (h y (M v0 (M v1 y)) v2))) (S (h v1 v0 y))

@[equational_result]
theorem Equation715_implies_Equation2 (G: Type _) [Magma G] (h: Equation715 G) : Equation2 G := fun x y =>
  have h0 := h y x y
  have h1 := S h0
  have h2 := R y
  let v3 := M x y
  have h4 := R x
  let v5 := M v3 x
  have h6 := h x x y
  let v7 := M (M x x) y
  let v8 := M x v7
  have h9 := h x y x
  have h10 := S h9
  let v11 := M y x
  let v12 := M v11 x
  have h13 := h v12 y x
  have h14 := h (M y v12) y x
  have h15 := h x y y
  let v16 := M v11 y
  have h17 := h (M y v16) y x
  have h18 := h v16 y x
  have h19 := R v12
  have h20 := h y y x
  have h21 := S h20
  let v22 := M y y
  let v23 := M v22 x
  let v24 := M y v23
  have h25 := h v24 y v12
  have h26 := h v24 y x
  have h27 := S h26
  have h28 := h y y y
  have h29 := C h2 (C h2 (T (C (S h28) h4) (C h20 h4)))
  let v30 := M v22 y
  have h31 := h (M y v30) y x
  have h32 := S h31
  have h33 := C h2 (C h2 (T (C h21 h4) (C h28 h4)))
  T (T (T (T (T (T h9 (C h2 (C h2 (T (T (T h13 (C h2 (C h2 (C (T (T h14 (C h2 (C h2 (T (C h10 h4) (C h15 h4))))) (S h17)) h4)))) (S h18)) (C (T (T (T (T (C h2 (T h9 (C h2 (C h20 h19)))) (S h25)) h26) h33) h32) h2))))) (C h2 (C h2 (C (T (T h31 h29) h27) h2)))) (S (h v23 y y))) (h v23 x y)) (C h4 (C h4 (C (T (T (C h4 (T (T (T (T (T (h v23 y x) (C h2 (C h2 (C (T (T h26 h33) h32) h4)))) (S (h v30 y x))) (h v30 x y)) (C h4 (C h4 (C (T (T (C h4 (T (T (h v30 y y) (C h2 (C h2 (T (T (T (C (T (T (T (T h31 h29) h27) h25) (C h2 (T (C h2 (C h21 h19)) h10))) h2) h18) (C h2 (C h2 (C (T (T h17 (C h2 (C h2 (T (C (S h15) h4) (C h9 h4))))) (S h14)) h4)))) (S h13))))) h10)) (C h4 (T h6 (C h4 (C h6 (R v7)))))) (S (h v8 x v7))) h2)))) (S (h v7 x y)))) (h v8 x v5)) (C h4 (T (C h4 (T (T (T (C (S h6) (R v5)) (h (M x v5) x x)) (C h4 (C h4 (T (C (S (h y x x)) h4) (C h0 h4))))) (S (h (M x (M v3 y)) x x)))) h1))) h2)))) h1

@[equational_result]
theorem Equation3211_implies_Equation2944 (G: Type _) [Magma G] (h: Equation3211 G) : Equation2944 G := fun x y z =>
  let v0 := M y x
  let v1 := M y v0
  let v2 := M v1 z
  let v3 := M v2 z
  have h4 := R y
  have h5 := h v3 v2 z
  have h6 := R v2
  have h7 := R v3
  have h8 := R z
  have h9 := h v3 v2 v3
  have h10 := h v1 v1 z
  have h11 := S h10
  have h12 := C h11 h8
  have h13 := h z v3 v1
  have h14 := h v2 z v3
  have h15 := h z v1 z
  have h16 := h v1 v2 z
  have h17 := T (T (T h16 (C (S h15) h6)) (C (T h13 (C (T (T h12 h14) (C (T (C (C (C (T h13 (C h12 h7)) h7) h7) h6) (S h9)) h8)) h7)) h6)) (S h5)
  have h18 := R v1
  have h19 := R v0
  have h20 := h v1 v3 v1
  have h21 := C (T (C (C h10 h18) h17) (S h20)) h19
  have h22 := h v0 v1 v1
  have h23 := h v0 y v3
  have h24 := h y v1 v0
  have h25 := h v0 y v0
  have h26 := h v1 v0 v1
  have h27 := S h13
  have h28 := C h10 h8
  have h29 := T (T (T h5 (C (T (C (T (T (C (T h9 (C (C (C (T (C h28 h7) h27) h7) h7) h6)) h8) (S h14)) h28) h7) h27) h6)) (C h15 h6)) (S h16)
  have h30 := S h25
  have h31 := C (T (C (C (C (T h24 (C h30 h18)) h29) h29) h19) (S h26)) h4
  have h32 := S h22
  have h33 := C (C (T h20 (C (C h11 h18) h29)) h19) h18
  have h34 := h v1 y v0
  T (T (h x y y) (C (T (T (T (C (T (C (C (T h24 (C (T (T h30 h22) (C (T (T h21 (C (T h34 (C (T (T (T (T (T (T h33 h32) h23) h31) (C (T h34 (C (T (T (T (T h33 h32) h23) h31) (C h17 h4)) h4)) h4)) (C (C (C h29 h4) h4) h4)) (C (C (T (C (T h26 (C (C (C (T (C h25 h18) (S h24)) h17) h17) h19)) h4) (S h23)) h4) h4)) h4)) h19)) (S (h y v0 y))) h18)) h18)) h4) h4) (S (h y y v1))) (R x)) h22) (C h21 h18)) (C (R (M v1 v0)) h17)) h4)) (S (h v3 y v0))

@[equational_result]
theorem Equation3586_implies_Equation41 (G: Type _) [Magma G] (h: Equation3586 G) : Equation41 G := fun x y z =>
  let v0 := M y z
  have h1 := h y z v0
  have h2 := S h1
  let v3 := M v0 y
  have h4 := R v0
  have h5 := C h1 h4
  have h6 := h v0 v0 x
  have h7 := S h6
  have h8 := h x (M (M v0 v0) v0) z
  have h9 := S h8
  have h10 := R x
  let v11 := M x x
  have h12 := h y z v11
  have h13 := S h12
  have h14 := h v11 v3 v0
  have h15 := S h14
  let v16 := M v11 x
  let v17 := M v16 v11
  have h18 := h x x v17
  have h19 := S h18
  have h20 := h v16 v11 v0
  have h21 := C h4 (T h20 (C h12 h19))
  have h22 := h v11 x v0
  have h23 := h v11 x v11
  have h24 := R v17
  have h25 := h v17 v16 v0
  have h26 := C (T (T (T (T h18 h25) (C h1 (T (T (T (T (T (C h19 h24) (S h23)) h22) h21) h15) h13))) (C h2 h4)) h6) h10
  have h27 := S h22
  have h28 := C h4 (T (C h13 h18) (S h20))
  let v29 := M v3 v0
  have h30 := h y z v29
  have h31 := R z
  have h32 := C h31 (T (T (T (T (T (S h30) h12) h14) h28) h27) h26)
  have h33 := h v3 v0 z
  have h34 := h v3 v0 x
  let v35 := M v29 v3
  have h36 := S h25
  have h37 := C h2 (T (T (T (T (T h12 h14) h28) h27) h23) (C h18 h24))
  T (T (T (T (T (T (T (h x x v0) (C h4 (T (T (T h22 h21) h15) h13))) (C h4 h30)) (h v0 v35 x)) (C h10 (T (T (C (T (T (T (T (T (T (T (T (S (h v3 v0 v0)) h33) h32) h9) h7) h5) h37) h36) h19) (T (T (T (T (T h12 h14) h28) h27) h26) (C (T (T (T h8 (C h31 (T (T (T (T (T (C (T (T (T (T h7 h5) h37) h36) h19) h10) h22) h21) h15) h13) h30))) (S h33)) h34) h10))) (S (h x v35 v11))) (S h34)))) (C h10 (T (T (T (T h33 h32) h9) h7) h5))) (S (h v0 v3 x))) h2

@[equational_result]
theorem Equation4197_implies_Equation4497 (G: Type _) [Magma G] (h: Equation4197 G) : Equation4497 G := fun x y z =>
  let v0 := M y y
  let v1 := M x v0
  let v2 := M z z
  have h3 := S (h v2 x v1)
  have h4 := R v1
  have h5 := h v0 v2 x
  have h6 := h v0 v2 v0
  have h7 := R v0
  have h8 := R v2
  have h9 := h y y y
  have h10 := h y y v0
  let v11 := M v2 x
  have h12 := h v0 v2 v11
  have h13 := R v11
  have h14 := h x v0 v2
  have h15 := C (T (T (C (T (T (C h14 h13) (S h12)) (C (T h10 (C (S h9) h7)) h8)) h7) (S h6)) h5) h4
  have h16 := h v11 v0 v1
  have h17 := h y y x
  let v18 := M x y
  have h19 := h (M v18 y) x v11
  have h20 := R x
  have h21 := h v18 y v11
  have h22 := R y
  have h23 := h x y v0
  have h24 := h y x y
  have h25 := h (M (M y x) v0) y v11
  have h26 := h x v0 y
  have h27 := h v1 x v11
  have h28 := C h13 (T (T (T h27 (C (C (C h13 (T (T (T h26 h25) (C (C (C h13 (T (C h24 h7) (S h23))) h22) h13)) (S h21))) h20) h13)) (S h19)) (S h17))
  have h29 := T (T (T h17 h19) (C (C (C h13 (T (T (T h21 (C (C (C h13 (T h23 (C (S h24) h7))) h22) h13)) (S h25)) (S h26))) h20) h13)) (S h27)
  have h30 := C (T (T (T h28 h16) h15) h3) h29
  have h31 := S (h z z v2)
  have h32 := C (h z z z) h8
  have h33 := C (T h32 h31) h20
  have h34 := h v2 x v2
  let v35 := M v1 x
  T (T (T (T (T (T (T (h x v0 v1) (h (M v35 v0) v1 v0)) (C (T (T (T (C (T (C h7 (T (T (T (T (T (h v35 v0 v11) (C (T (T (T (T h30 h28) h16) h15) h3) h13)) (C (T h34 (C (T (T h33 h34) (C h33 h8)) h8)) h13)) (S (h v2 v2 v11))) h32) h31)) h5) h4) (C (T (T (S h5) h6) (C (T (T (C (T (C h9 h7) (S h10)) h8) h12) (C (S h14) h13)) h7)) h4)) (S h16)) (C h13 h29)) h7)) h30) h28) h16) h15) h3

@[equational_result]
theorem Equation492_implies_Equation1340 (G: Type _) [Magma G] (h: Equation492 G) : Equation1340 G := fun x y z =>
  let v0 := M y z
  let v1 := M v0 z
  let v2 := M v1 x
  let v3 := M y v2
  have h4 := S (h v2 y y)
  have h5 := h y z v0
  have h6 := S h5
  have h7 := h z v0 y
  have h8 := S h7
  have h9 := h y z y
  have h10 := R v0
  have h11 := R y
  have h12 := C h11 (C h10 (C h10 (T (C h10 h9) h8)))
  have h13 := h v0 y v0
  have h14 := h v0 z v1
  have h15 := S h14
  have h16 := h z v1 v0
  have h17 := S h16
  have h18 := h v0 z v0
  have h19 := R v1
  have h20 := C h10 (C h19 (C h19 (T (C h19 h18) h17)))
  have h21 := h v1 v0 v1
  have h22 := h v1 z v1
  have h23 := R z
  have h24 := C h10 (T (T (C h23 (T (T (T (C h23 (T h21 h20)) h15) h13) h12)) h6) h9)
  have h25 := h v0 v1 z
  have h26 := S h18
  have h27 := S h13
  have h28 := S h9
  have h29 := C h11 (C h10 (C h10 (T h7 (C h10 h28))))
  have h30 := h v2 v3 y
  have h31 := h y v2 y
  have h32 := R v3
  have h33 := R v2
  have h34 := C h11 (C h33 (T (T (T (C h33 (T (h v3 y v3) (C h11 (C h32 (C h32 (T (C h32 h31) (S h30))))))) (S (h y v2 v3))) (h y y z)) (C h11 (C h11 (T (C h23 (T (T (T (C h23 (T (T (T (T h5 (C h23 (T (T (T h29 h27) h25) (C h19 (T (T (T h24 h8) h16) (C h19 (T (T h26 h25) (C h19 (T h24 h8))))))))) (S h22)) h21) h20)) h15) h13) h12)) h6)))))
  have h35 := h y v3 v2
  have h36 := S h25
  have h37 := C h10 (T (T h28 h5) (C h23 (T (T (T h29 h27) h14) (C h23 (T (C h10 (C h19 (C h19 (T h16 (C h19 h26))))) (S h21))))))
  T (T (h x v2 v1) (C h33 (T (T (T (T (T (S (h v1 x v1)) h22) (C h23 (T (T (T (C h19 (T (T (T (C h19 (T (T (C h19 (T h7 h37)) h36) h18)) h17) h7) h37)) h36) h13) h12))) h6) h35) (C h32 (T (T (T h34 h4) h30) (C h32 (T (T (S h31) h35) (C h32 (T h34 h4))))))))) (S (h v3 v2 v3))

@[equational_result]
theorem Equation492_implies_Equation3601 (G: Type _) [Magma G] (h: Equation492 G) : Equation3601 G := fun x y z =>
  let v0 := M y x
  let v1 := M v0 z
  let v2 := M z v1
  let v3 := M x y
  have h4 := S (h v1 z v3)
  have h5 := h v3 v1 z
  have h6 := S h5
  have h7 := h v1 v0 v1
  have h8 := h v0 z v0
  have h9 := R v1
  have h10 := h z v1 v0
  have h11 := C h9 (T h10 (C h9 (S h8)))
  have h12 := R v0
  have h13 := R z
  have h14 := C h13 (T (C h12 (C h9 h11)) (S h7))
  have h15 := h v0 z v1
  have h16 := T h15 h14
  have h17 := h v0 v2 x
  have h18 := R (M x (M x v2))
  have h19 := S h15
  have h20 := S h10
  have h21 := C h9 h8
  have h22 := C h13 (T h7 (C h12 (C h9 (C h9 (T h21 h20)))))
  have h23 := T h22 h19
  have h24 := h v0 y v2
  have h25 := h y x y
  have h26 := h x v0 y
  have h27 := R v2
  have h28 := R y
  have h29 := R x
  have h30 := h y x v2
  have h31 := R v3
  have h32 := h z v3 v2
  have h33 := C h9 (T (T (T (T (C h9 h23) h21) h20) h32) (C h31 (T (C h13 (T (C h27 (T (C h27 (C h29 (T h30 (C h29 (T (T (T (C h28 (C h23 (C h27 (T h26 (C h16 (S h25)))))) (S h24)) h15) h14))))) (C h23 h18))) (S h17))) (C h13 h16))))
  have h34 := C h13 (T (T (T h33 h6) (h v3 v1 v3)) (C h9 (C h31 (C h31 (T (C h31 (T (h v1 z v1) (C h13 (C h9 (T (C h9 (T h11 (C h9 (C h9 h16)))) (C h9 (T h33 h6))))))) (S (h z v3 v1)))))))
  have h35 := h z v2 v1
  T (T (T h5 (C h9 (T (C h31 (T (C h13 h23) (C h13 (T h17 (C h27 (T (C h16 h18) (C h27 (C h29 (T (C h29 (T (T (T h22 h19) h24) (C h28 (C h16 (C h27 (T (C h23 h25) (S h26))))))) (S h30)))))))))) (S h32)))) (C h9 (T h35 (C h27 (T (T (T h34 h4) (h v1 v2 z)) (C h27 (T (T (S (h z v1 z)) h35) (C h27 (T h34 h4))))))))) (S (h v2 v1 v2))

@[equational_result]
theorem Equation711_implies_Equation522 (G: Type _) [Magma G] (h: Equation711 G) : Equation522 G := fun x y z =>
  let v0 := M x z
  let v1 := M z v0
  have h2 := h v1 v1 x
  have h3 := S h2
  let v4 := M v1 (M (M v1 x) x)
  have h5 := R v4
  have h6 := R y
  have h7 := C h6 (C h6 (T (C h3 h5) h3))
  have h8 := h v1 y v4
  have h9 := R v0
  have h10 := h z v1 v0
  have h11 := S h10
  have h12 := h v0 v0 x
  have h13 := S h12
  let v14 := M v0 (M (M v0 x) x)
  have h15 := R v14
  have h16 := T (C h13 h15) h13
  have h17 := R v1
  have h18 := h v0 v1 v14
  have h19 := T h18 (C h17 (C h17 h16))
  have h20 := C h17 h19
  have h21 := T h20 h11
  have h22 := C h21 h9
  let v23 := M v1 v0
  have h24 := h (M v23 v0) v0 v0
  have h25 := S h24
  have h26 := T h12 (C h12 h15)
  have h27 := T (C h17 (C h17 h26)) (S h18)
  have h28 := C h17 h27
  have h29 := T h10 h28
  have h30 := C h29 h9
  have h31 := C (T h20 (C h30 h27)) h9
  have h32 := h v0 z v14
  have h33 := R z
  have h34 := T (C h6 (C h6 (T h2 (C h2 h5)))) (S h8)
  have h35 := T h8 h7
  have h36 := R v23
  have h37 := h v23 v0 v1
  have h38 := C h27 (T (T (T h10 h28) h37) (C h9 (T (T (C h9 (C (T (T (T (C h36 h35) (C h21 h34)) (C h33 (C h33 h26))) (S h32)) (T h30 h31))) h25) h31)))
  have h39 := C h19 h33
  have h40 := C (T (C h22 h19) h28) h9
  T (T (T (T (T (T (T (T (h x (M y (M y v1)) z) (C h34 (C h34 (T (T (T (T h39 h38) h25) h31) (C (C (T (T h24 (C h19 (T (T (T (C h9 (T (T h40 h24) (C h9 (C (T (T (T h32 (C h33 (C h33 h16))) (C h29 h35)) (C h36 h34)) (T h40 h22))))) (S h37)) h20) h11))) (C h27 h33)) h9) h9))))) (S (h (M v0 z) v1 v0))) h39) h38) h25) h22) h8) h7

@[equational_result]
theorem Equation952_implies_Equation508 (G: Type _) [Magma G] (h: Equation952 G) : Equation508 G := fun x y z =>
  let v0 := M z z
  let v1 := M x v0
  let v2 := M y v1
  let v3 := M y v2
  have h4 := h v3 z y
  let v5 := M (M y v3) (M y z)
  let v6 := M v0 v0
  have h7 := R v6
  have h8 := R v0
  have h9 := h z v3 v1
  let v10 := M (M v1 z) (M v1 v3)
  have h11 := R x
  let v12 := M z v3
  have h13 := R z
  have h14 := h z z z
  have h15 := S h14
  have h16 := h v6 v0 v0
  let v17 := M z x
  have h18 := h z z v0
  let v19 := M v0 z
  let v20 := M v19 v19
  have h21 := h v6 v0 z
  have h22 := h v0 v0 v0
  let v23 := M y v0
  let v24 := M z v0
  have h25 := R (M v1 x)
  have h26 := h v0 v1 v1
  let v27 := M z v1
  have h28 := h x z z
  T (T (T (T (T (T (T (T (T (T (T h28 (C h13 (T (h (M v17 v0) z z) (C h13 (C (S h28) h8))))) (C (T h14 (C h13 (T (T h16 (C h8 (C (T (C h8 (T (T (h v6 z z) (C h13 (C h15 h8))) (C h14 (R v24)))) (S h21)) h7))) (S h22)))) (R v27))) (h (M v24 v27) x v1)) (C h11 (C (T (S (h v0 v1 z)) h26) h25))) (C h11 (C (T (S h26) (h v0 v1 y)) h25))) (S (h (M v23 v2) x v1))) (C (R v23) (T (h v2 v0 y) (C (h v0 v3 z) (R (M v3 v23)))))) (S (h (M v24 v12) v23 v3))) (C (T (C h13 (T (T h22 (C h8 (C (T (T h21 (C h8 (T (C h15 (C h18 h8)) (S (h v20 z z))))) (C h8 (T (T (h v20 x z) (C h11 (C (T (S h18) h14) (R v17)))) (S (h v6 x z))))) h7))) (S h16))) h15) (R v12))) (C h13 (T (T (h v12 v0 v0) (C h8 (C (T (T (T (T (h (M v0 v12) x v3) (C h11 (C (T (S (h z v3 z)) h9) (R (M v3 x))))) (S (h v10 x v3))) (h v10 v0 v3)) (C h8 (T (C (S h9) (C h4 h8)) (S (h v5 z z))))) h7))) (S (h v5 v0 v0))))) (S h4)

@[equational_result]
theorem Equation684_implies_Equation759 (G: Type _) [Magma G] (h: Equation684 G) : Equation759 G := fun x y z =>
  let v0 := M y x
  let v1 := M z (M v0 z)
  let v2 := M v1 (M (M v1 x) x)
  let v3 := M y v1
  have h4 := h v3 v1 v2
  have h5 := S h4
  have h6 := R v2
  have h7 := h v1 v1 x
  have h8 := R v3
  have h9 := R v1
  have h10 := C h9 (C h8 (T h7 (C h7 h6)))
  have h11 := S h7
  have h12 := T (C h11 h6) h11
  have h13 := R y
  have h14 := S (h v3 v3 x)
  let v15 := M v3 (M (M v3 x) x)
  have h16 := C h8 (T (T (C h13 (T (C h14 (R v15)) h14)) (C h13 (T h4 (C h9 (C h8 h12))))) (S (h v1 y v1)))
  have h17 := h y v3 v15
  let v18 := M x (M (M x x) x)
  have h19 := R v18
  have h20 := h x x x
  have h21 := T h20 (C h20 h19)
  let v22 := M z (M (M z x) x)
  have h23 := h v0 z v22
  have h24 := S h23
  have h25 := R v22
  have h26 := h z z x
  have h27 := R v0
  have h28 := R z
  have h29 := C h28 (C h27 (T h26 (C h26 h25)))
  have h30 := R x
  let v31 := M v3 v1
  have h32 := R v31
  have h33 := T h17 h16
  have h34 := h x v0 x
  have h35 := S h20
  let v36 := M v0 x
  have h37 := R v36
  have h38 := h v36 x v18
  have h39 := S h26
  T (T (T (T (T h34 (C (T h23 (C h28 (C h27 (T (C h39 h25) h39)))) (T (C h30 (C h37 h21)) (S h38)))) (h (M v1 v36) v1 y)) (C h9 (T (T (T (T (C (T (C (T h29 h24) (T h38 (C h30 (C h37 (T (C h35 h19) h35))))) (S h34)) (T (T (T (C (C h9 h33) h33) (C (T h10 h5) h32)) (C h8 (T (h v31 v1 v2) (C h9 (C h32 h12))))) (S (h v1 v3 v1)))) (C h30 (T (T h29 h24) (C h13 h21)))) (S (h y x v18))) h17) h16))) h10) h5

