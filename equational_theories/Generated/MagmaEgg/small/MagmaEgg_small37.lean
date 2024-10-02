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
theorem Equation1943_implies_Equation572 (G: Type _) [Magma G] (h: Equation1943 G) : Equation572 G := fun x y z =>
  let v0 := M x y
  let v1 := M z v0
  let v2 := M z v1
  let v3 := M z v2
  have h4 := h v2 v3 v2
  let v5 := M v2 v2
  have h6 := R v5
  have h7 := h z z v1
  have h8 := h z z v0
  have h9 := R v3
  have h10 := h v2 z v1
  let v11 := M v2 v5
  have h12 := h v11 x z
  have h13 := S h7
  have h14 := R v11
  have h15 := h v3 v2 v2
  have h16 := h v3 y v2
  let v17 := M y v2
  let v18 := M y v17
  have h19 := R v18
  have h20 := R (M x (M x z))
  have h21 := h v18 x z
  have h22 := R y
  let v23 := M y v18
  have h24 := h y v17 v2
  let v25 := M v17 (M v17 v2)
  have h26 := h v25 y v17
  let v27 := M v2 (M v2 v17)
  have h28 := T (C h9 (T h13 h8)) (S h10)
  have h29 := S h21
  have h30 := C h19 h13
  have h31 := C h22 (T (T (T (T h4 (C h28 h6)) h12) (C h20 (T (T (T (C h14 h7) (S h15)) h16) h30))) h29)
  let v32 := M v17 (M v17 y)
  have h33 := h v32 z v0
  have h34 := h x v17 y
  have h35 := R v2
  have h36 := h v0 v17 y
  T (T (T (T (T (T (h x z v0) (C h35 (T (T (T (C (T h34 (C (R v32) h36)) h36) (S (h v32 v32 (M v0 y)))) h33) (C h35 (S h34))))) (C h35 (T (T (T (T (T (C h35 h34) (S h33)) (C h31 (T (T (T (T (C h31 h24) (S h26)) (h v25 x z)) (C h20 (T (T (T (C (R v25) h7) (S (h v3 v17 v2))) h16) h30))) h29))) (S (h y y v17))) (h y v3 v2)) (C h28 (R v17))))) (h v27 x y)) (C (R (M x v0)) (T (T (T (C (R v27) h24) (S (h v25 v2 v17))) h26) (C (R v23) (S h24))))) (S (h v23 x y))) (C h22 (T (T (T (T h21 (C h20 (T (T (T (C h19 h7) (S h16)) h15) (C h14 h13)))) (S h12)) (C (T h10 (C h9 (T (S h8) h7))) h6)) (S h4)))

@[equational_result]
theorem Equation684_implies_Equation2925 (G: Type _) [Magma G] (h: Equation684 G) : Equation2925 G := fun x y z =>
  let v0 := M x z
  let v1 := M y v0
  let v2 := M v1 y
  let v3 := M v2 z
  have h4 := S (h v3 z v3)
  have h5 := h v3 v3 x
  have h6 := S h5
  let v7 := M v3 (M (M v3 x) x)
  have h8 := R v7
  have h9 := T (C h6 h8) h6
  let v10 := M z v3
  have h11 := R v3
  have h12 := h z z x
  have h13 := S h12
  let v14 := M z (M (M z x) x)
  have h15 := R v14
  have h16 := T (C h13 h15) h13
  have h17 := R v2
  have h18 := R z
  have h19 := C h18 (C h17 h16)
  have h20 := h v2 z v14
  have h21 := C h18 (T (T (T h20 h19) (h v10 v3 v7)) (C h11 (C (R v10) h9)))
  let v22 := M v1 (M (M v1 x) x)
  have h23 := h v1 v1 x
  have h24 := R y
  let v25 := M v0 (M (M v0 x) x)
  have h26 := h v0 v0 x
  have h27 := T h26 (C h26 (R v25))
  have h28 := R v1
  have h29 := R v0
  let v30 := M v1 v0
  have h31 := h z v2 z
  have h32 := h v3 z v14
  let v33 := M v2 v3
  have h34 := h v33 v3 v7
  have h35 := R v33
  let v36 := M v3 (M (M v3 y) y)
  have h37 := h v3 v3 y
  T (T (T (h x z v2) (C h18 (T (T (C (R x) (T (T (T (T (T (C (T h21 h4) (T (T h20 h19) (C (T (T (T h31 (C h17 (T (C h18 (C h11 (T h12 (C h12 h15)))) (S h32)))) h34) (C h11 (C h35 h9))) (T h37 (C h37 (R v36)))))) (S (h (M v3 (M v33 v3)) v3 v36))) (C h11 (C h35 (T h5 (C h5 h8))))) (S h34)) (C h17 (T h32 (C h18 (C h11 h16))))) (S h31))) (h v0 v1 v0)) (C h28 (T (T (T (C h29 (C (R v30) h27)) (S (h v30 v0 v25))) (C h28 (T (T (h v0 y v0) (C h24 (T (C h29 (C h28 h27)) (S (h v1 v0 v25))))) (C h24 (T h23 (C h23 (R v22))))))) (S (h y v1 v22))))))) h21) h4

@[equational_result]
theorem Equation4101_implies_Equation4609 (G: Type _) [Magma G] (h: Equation4101 G) : Equation4609 G := fun x y z =>
  have h0 := R z
  let v1 := M y y
  have h2 := h y v1 y
  have h3 := S h2
  have h4 := R v1
  have h5 := h y y y
  have h6 := C h5 h4
  let v7 := M (M x x) y
  have h8 := h v1 v7 x
  have h9 := R v7
  have h10 := h y x x
  have h11 := S h5
  let v12 := M v1 z
  have h13 := h v1 v1 v12
  have h14 := S h13
  have h15 := R v12
  have h16 := h v12 v1 v1
  have h17 := C (T h16 (C (C (T h6 h3) h15) h4)) h4
  have h18 := h v12 v1 z
  have h19 := C (C (T (T (T (T h18 h17) h14) h6) h3) h0) h15
  have h20 := h z v12 v12
  have h21 := h z z z
  have h22 := S h18
  have h23 := C h11 h4
  have h24 := C (T (C (C (T h2 h23) h15) h4) (S h16)) h4
  have h25 := h z v7 x
  have h26 := S h10
  have h27 := h z y y
  have h28 := h z v1 x
  have h29 := R x
  have h30 := h y v1 x
  have h31 := h x y y
  have h32 := h v1 x x
  have h33 := S h32
  have h34 := C (T h30 (C (S h31) h4)) h29
  have h35 := R y
  T (T (T (T (C (T (T h31 (C (T h34 h33) h35)) (S (h v1 y y))) h35) (C (T h8 (C (T (C (T h26 h5) h4) h3) h9)) h35)) (S (h v7 y y))) (h v7 z z)) (C (T (T (T (T (T (T (T (T (C (T h28 (C (C (T (T (T h34 h33) h6) h3) h0) h4)) h9) (C (T (T (C (C (T (T (T h2 h23) h32) (C (T (C h31 h4) (S h30)) h29)) h0) h4) (S h28)) h27) h9)) (C (T (T (S h27) h25) (C (C h26 h0) h9)) h9)) (C (T (T (T (C (C h10 h0) h9) (S h25)) h21) (C (C (T (T (T (T (T (T h20 h19) h18) h17) h14) h6) h3) h0) h0)) h9)) (C (T (T (T (T (T (T (T (T (C (C (T (T (T (T (T (T h2 h23) h13) h24) h22) (C (C (T (T (T (T h2 h23) h13) h24) h22) h0) h15)) (S h20)) h0) h0) (S h21)) h20) h19) h18) h17) h14) h6) h3) h9)) (C (T h2 (C (T h11 h10) h4)) h9)) (S h8)) h6) h3) h0)

@[equational_result]
theorem Equation492_implies_Equation3553 (G: Type _) [Magma G] (h: Equation492 G) : Equation3553 G := fun x y z =>
  let v0 := M x z
  let v1 := M v0 z
  let v2 := M y v1
  have h3 := h v1 y v2
  have h4 := S h3
  have h5 := h y v1 y
  have h6 := R v2
  have h7 := h v1 v2 y
  have h8 := h z v0 v1
  have h9 := h v0 z v0
  have h10 := R v1
  have h11 := C h10 (S h9)
  have h12 := h z v1 v0
  have h13 := h z z x
  have h14 := h v0 z v1
  have h15 := S h12
  have h16 := C h10 h9
  have h17 := R v0
  have h18 := h v1 v0 v1
  have h19 := h z v0 x
  have h20 := S h19
  have h21 := h x z x
  have h22 := C h17 h21
  have h23 := R z
  have h24 := R x
  have h25 := h z x v0
  have h26 := h v1 z z
  have h27 := C h10 (C h6 (T (T (C h17 (T (C h17 (T h26 (C h23 (C h10 (T (T (T (C h23 (C h23 (T h25 (C h24 (T (C h23 (T (T (C h17 (T h22 h20)) h18) (C h17 (C h10 (C h10 (T h16 h15)))))) (S h14)))))) (S h13)) h12) h11))))) (S h8))) h7) (C h6 (S h5))))
  have h28 := h v2 v1 v0
  have h29 := R y
  have h30 := S h25
  have h31 := C h17 (T h19 (C h17 (S h21)))
  have h32 := S h18
  have h33 := C h17 (C h10 (C h10 (T h12 h11)))
  have h34 := C h23 (T (T h33 h32) h31)
  have h35 := C h17 (T (C h23 (C h10 (T (T (T h16 h15) h13) (C h23 (C h23 (T (C h24 (T h14 h34)) h30)))))) (S h26))
  T (C (T (h x v0 v0) (C h17 (T (C h24 (T (T (T (C h17 (C h17 (T h14 (C h23 (T (T (T h33 h32) (h v1 z v0)) (C h23 (T (C h10 (T (C h17 h31) (C h17 (C h17 (T (T (T h22 h20) h8) h35))))) (S (h v0 v1 v0))))))))) (S (h v0 v0 z))) h14) h34)) h30))) (T (h y v2 v2) (C h6 (T (T (T (C h29 (T (T (T (C h6 (C h6 (C h29 (T h3 (C h29 (T (C h10 (C h6 (T (T (C h6 h5) (S h7)) (C h17 (T h8 h35))))) (S h28))))))) (S (h v2 v2 y))) h28) h27)) h4) (h v1 v1 y)) (C h10 (C h10 (T (C h29 (T h28 h27)) h4))))))) (S (h v2 v1 v1))

@[equational_result]
theorem Equation3804_implies_Equation3573 (G: Type _) [Magma G] (h: Equation3804 G) : Equation3573 G := fun x y z =>
  let v0 := M z z
  let v1 := M v0 x
  have h2 := h y v1 v1
  have h3 := S h2
  let v4 := M y v1
  have h5 := R v4
  have h6 := h v0 x v0
  have h7 := h z z z
  have h8 := R v1
  have h9 := T (C h8 h7) (S h6)
  have h10 := h v1 x v0
  have h11 := T h10 (C h8 h9)
  have h12 := C h11 h5
  have h13 := h y x v1
  have h14 := S h13
  have h15 := S h7
  have h16 := C h8 h15
  have h17 := T h6 h16
  have h18 := T (C h8 h17) (S h10)
  have h19 := C h18 h5
  let v20 := M x y
  have h21 := h y x v0
  have h22 := S h21
  let v23 := M y v0
  have h24 := h v1 v23 v0
  have h25 := S h24
  have h26 := h v1 v0 v0
  have h27 := R v23
  have h28 := h y v0 v0
  have h29 := h y v0 v1
  have h30 := C (T (T (T (C h17 h5) (S h29)) h28) (C h15 h27)) (T (C h7 h17) (S h26))
  have h31 := h v0 v4 v1
  have h32 := C h15 h9
  T (T (T (T (T (T (h x y v0) (h (M v0 y) (M x v0) v1)) (C (S (h x x v0)) (T (T (T (T (C (h v0 y x) (T (T (T (T (T (h v0 x v1) (C h11 (R (M v0 v1)))) (S (h v0 v1 v1))) (h v0 v1 x)) (C (h x v1 y) (T (T (T (T (T (T h6 h16) h26) h32) (h v0 v1 v4)) (C (T (T (T (T (h v4 v1 z) (C (T (T (h z v1 v1) (C h18 (R (M z v1)))) (S (h z x v1))) (R (M v4 z)))) (S (h v4 x z))) (h v4 x v0)) (C h8 (T (T (T (T (T (T (T (T (C (T (T (T (T (T (T h2 h19) h14) h21) h24) (C (T (T (T (C h7 h27) (S h28)) h29) (C h9 h5)) (T h26 h32))) (S h31)) h7) (S (h v0 v4 v0))) h31) h30) h25) h22) h13) h12) h3))) (T (T (T (T (T (T h31 h30) h25) h22) h13) h12) h3))) (S (h y v4 v1))))) (S (h y v20 v4)))) (S (h y v1 v20))) h2) h19) h14))) (S (h y x x))) h13) h12) h3

@[equational_result]
theorem Equation3120_implies_Equation1152 (G: Type _) [Magma G] (h: Equation3120 G) : Equation1152 G := fun x y z =>
  let v0 := M x y
  let v1 := M (M z v0) z
  let v2 := M y v1
  have h3 := R v2
  have h4 := R v1
  have h5 := h v1 y v2
  have h6 := S h5
  have h7 := h y v2 v2
  have h8 := T h7 (C h6 h3)
  have h9 := C h8 h4
  have h10 := h v2 y y
  have h11 := S h10
  have h12 := R y
  have h13 := T (C h5 h3) (S h7)
  have h14 := C h13 h3
  have h15 := h v0 z v2
  have h16 := h v0 v2 v0
  have h17 := S h16
  have h18 := R v0
  have h19 := C h13 h4
  have h20 := h v2 y v0
  have h21 := h y v0 v0
  have h22 := T (T h15 h14) (C (T (T h21 (C (T (T (C (C (C (T h15 h14) h12) h18) h18) (S h20)) h9) h18)) (C h19 h18)) h3)
  have h23 := C (C h22 h18) h18
  have h24 := C (C (T (T (T h23 h17) h15) h14) h12) h12
  have h25 := h v0 v0 y
  have h26 := h v0 v2 v1
  have h27 := h v0 v0 v2
  have h28 := S h27
  have h29 := S h15
  have h30 := C h8 h3
  have h31 := T (T (C (T (T (C h9 h18) (C (T (T h19 h20) (C (C (C (T h30 h29) h12) h18) h18)) h18)) (S h21)) h3) h30) h29
  have h32 := C (C h31 h18) h18
  have h33 := S h25
  have h34 := C (C (T (T (T (C (T h10 (C (T (T (T (C (C (T (T (T h30 h29) h16) h32) h12) h12) h33) h16) h32) h12)) h12) h33) h16) h32) h3) h3
  have h35 := C (C h31 h4) (T (T h5 h34) h28)
  have h36 := S (h v1 v0 x)
  have h37 := R x
  T (T (h x y v2) (C (C (T (T (T (C (T (T (T (T (T (T (C (T (h y x x) (C (T (T (T (T (T (T (C (C (T h26 h35) h37) h37) h36) h5) h34) h28) h26) h35) h37)) h37) h36) h5) h34) h28) h26) h35) h12) (C (T (T (T (C (C h22 h4) (T (T h27 (C (C (T (T (T h23 h17) h25) (C (T (C (T (T (T h23 h17) h25) h24) h12) h11) h12)) h3) h3)) h6)) (S h26)) h25) h24) h12)) h11) h9) h3) h3)) (S (h v2 v1 v2))

@[equational_result]
theorem Equation3211_implies_Equation3417 (G: Type _) [Magma G] (h: Equation3211 G) : Equation3417 G := fun x y z =>
  let v0 := M y x
  let v1 := M z v0
  let v2 := M z v1
  have h3 := h v2 z v1
  have h4 := R z
  have h5 := R v2
  have h6 := R v1
  have h7 := h v2 z z
  have h8 := h z v0 v1
  have h9 := R v0
  have h10 := h v0 z v0
  have h11 := C (S h10) h6
  have h12 := h z v1 v0
  have h13 := h v2 v1 v2
  have h14 := S h13
  have h15 := h v1 z v1
  have h16 := C (S h15) h5
  have h17 := h z v2 v1
  have h18 := C (C (C (T h17 h16) h5) h5) h6
  have h19 := h v1 z v2
  have h20 := h z z v0
  have h21 := S h17
  have h22 := C h15 h5
  have h23 := C (T (C (C (T (T (T h22 h21) h20) (C (C (T (C (T h19 (C (T (T h18 h14) (C (T h12 h11) h6)) h4)) h9) (S h8)) h4) h4)) h5) h4) (S h7)) h6
  have h24 := h z v1 v2
  have h25 := S h12
  have h26 := C h10 h6
  have h27 := h v0 v0 v2
  have h28 := h v0 z v1
  have h29 := S h28
  have h30 := C (T h24 h23) h9
  have h31 := S h19
  have h32 := C (C (C (T h22 h21) h5) h5) h6
  have h33 := T (C (T (T (C (T h13 h32) h4) h31) h30) h4) h29
  have h34 := h v2 v2 z
  have h35 := h v1 v2 v0
  have h36 := S h24
  have h37 := C (T h7 (C (C (T (T (T (C (C (T h8 (C (T (C (T (T (C (T h26 h25) h6) h13) h32) h4) h31) h9)) h4) h4) (S h20)) h17) h16) h5) h4)) h6
  have h38 := C (T h37 h36) h9
  T (T (T (T (C (T (h x v2 z) (C (C h33 (R x)) (T (T h3 (C (T (T (C (T (T (T (T h37 h36) h12) h11) (C (T h27 (C (C (T (C (C (T h28 (C (T (T h38 h19) (C (T h18 h14) h4)) h4)) h5) h5) (S h34)) h9) h9)) h6)) h5) (S h35)) h30) h4)) h29))) (R y)) (S (h v0 y x))) h28) (C (T (T h38 h35) (C (T (T (T (T (C (T (C (C (T h34 (C (C h33 h5) h5)) h9) h9) (S h27)) h6) h26) h25) h24) h23) h5)) h4)) (S h3)

@[equational_result]
theorem Equation1699_implies_Equation1181 (G: Type _) [Magma G] (h: Equation1699 G) : Equation1181 G := fun x y z =>
  let v0 := M z x
  let v1 := M z v0
  let v2 := M v1 y
  have h3 := R v2
  have h4 := R y
  have h5 := h x v0 x
  let v6 := M v0 x
  have h7 := R (M v6 x)
  have h8 := h v6 v0 x
  have h9 := h x z x
  have h10 := h x z v2
  have h11 := S h10
  let v12 := M (M z v2) v2
  have h13 := h v12 v0 x
  have h14 := h v12 v1 y
  let v15 := M v2 y
  have h16 := R v15
  have h17 := h v0 z v2
  have h18 := h v15 v0 x
  let v19 := M v15 y
  have h20 := R v19
  have h21 := h v19 y x
  let v22 := M (M y x) x
  have h23 := R v22
  have h24 := h y v1 v12
  have h25 := R v12
  have h26 := T (C h3 (T h10 (C h17 h25))) (S h24)
  have h27 := h x v2 y
  let v28 := M y v2
  have h29 := h v22 v28 x
  have h30 := R (M (M v28 x) x)
  have h31 := h v2 y x
  have h32 := h v2 y v2
  have h33 := S h32
  let v34 := M v28 v2
  have h35 := h v34 v28 x
  let v36 := M v34 v2
  have h37 := S h17
  T (T (T (h x v2 v2) (C (T (T (T (T (T (T (T (T (h (M v2 x) x v2) (C (T (T (T (C (R x) h26) (C (T (T h5 (C (T (T (T (T h8 (C (T (S h9) h10) h7)) (S h13)) h14) (C h37 h16)) h7)) (S h18)) h4)) h21) (C (T (C (T h24 (C h3 (T (C h37 h25) h11))) h20) (S h27)) h23)) (R (M (M x v2) v2)))) (S (h v22 x v2))) h29) (C (S h31) h30)) (C h32 h30)) (S h35)) (h v34 v28 v2)) (C h33 (R v36))) (R (M (M v2 v2) v2)))) (S (h v36 v2 v2))) (C (T (T (T (T (T h35 (C (T h33 h31) h30)) (S h29)) (h v22 x x)) (C (T (T (T (C (T h27 (C h26 h20)) h23) (S h21)) h20) (C (T (T h18 (C (T (T (T (T (C h17 h16) (S h14)) h13) (C (T h11 h9) h7)) (S h8)) h7)) (S h5)) h4)) (R (M (M x x) x)))) (S (h y x x))) h3)

@[equational_result]
theorem Equation880_implies_Equation873 (G: Type _) [Magma G] (h: Equation880 G) : Equation873 G := fun x y =>
  let v0 := M y y
  let v1 := M x x
  let v2 := M v1 v0
  let v3 := M y v2
  let v4 := M y v3
  let v5 := M v4 v4
  have h6 := h v3 v5
  have h7 := S h6
  have h8 := h y v3
  have h9 := R v5
  have h10 := C h9 (C h8 h8)
  have h11 := R v0
  have h12 := R v3
  have h13 := h y v2
  have h14 := S h13
  have h15 := T h10 h7
  have h16 := C h15 h12
  let v17 := M v5 v0
  have h18 := R v17
  have h19 := C h18 h15
  have h20 := h (M v17 v17) v0
  have h21 := S h20
  have h22 := S h8
  have h23 := T h6 (C h9 (C h22 h22))
  have h24 := C h18 h23
  have h25 := C h23 h12
  let v26 := M v3 v3
  have h27 := R v26
  have h28 := h v2 v26
  have h29 := T (T h28 (C h27 (C h14 h14))) (C (T h25 h24) h11)
  have h30 := C h11 (C h29 h29)
  have h31 := h v1 v0
  have h32 := R v2
  have h33 := T (C h32 (T (T (T (T h31 h30) h21) h19) h16)) h14
  have h34 := C h33 h12
  have h35 := T (T (C (T h19 h16) h11) (C h27 (C h13 h13))) (S h28)
  have h36 := T h13 (C h32 (T (T (T (T h25 h24) h20) (C h11 (C h35 h35))) (S h31)))
  have h37 := C h36 h12
  let v38 := M y x
  let v39 := M v38 v38
  have h40 := h x v39
  have h41 := h y x
  have h42 := R v39
  have h43 := T (C h42 (C h41 h41)) (S h40)
  have h44 := R x
  have h45 := C h33 h44
  have h46 := C (C h45 h45) h11
  let v47 := M (M v2 v1) x
  have h48 := C h36 h44
  have h49 := S h41
  T (T (T (T (T (T h40 (C h42 (C h49 h49))) (C (C h48 h48) h11)) (C (T (T (T (T (h (M v47 v47) v0) (C h11 (T (C h46 h46) (C h43 h43)))) (C h11 (T (T h31 h30) h21))) (S (h v5 v0))) (C h37 h37)) h11)) (C (C h34 h34) h11)) h10) h7

@[equational_result]
theorem Equation1304_implies_Equation1470 (G: Type _) [Magma G] (h: Equation1304 G) : Equation1470 G := fun x y z =>
  let v0 := M x y
  let v1 := M z y
  let v2 := M z v1
  let v3 := M v0 v2
  let v4 := M (M (M y x) x) y
  let v5 := M (M v0 y) y
  have h6 := R v5
  have h7 := h y y x
  have h8 := R y
  let v9 := M (M (M v0 x) x) v0
  have h10 := h v0 v2 v9
  have h11 := R v2
  have h12 := R v9
  have h13 := h v0 v0 x
  have h14 := R v3
  have h15 := h v2 z v1
  have h16 := h z v1 v1
  let v17 := M (M v2 v1) v1
  have h18 := R v17
  have h19 := h v1 v1 x
  have h20 := S h19
  let v21 := M (M (M v1 x) x) v1
  have h22 := R v21
  have h23 := h v1 v17 v21
  let v24 := M (M (M z x) x) z
  have h25 := h z y v24
  have h26 := R v24
  have h27 := h z z x
  have h28 := T (T (C (T (C (T (C h8 (C (T h27 (C h27 h26)) h8)) (S h25)) (T h23 (C h18 (T (C (T (C h20 h22) h20) h18) (S h16))))) (S h15)) h14) (C h11 (C (T h13 (C h13 h12)) h11))) (S h10)
  have h29 := h y v3 v1
  have h30 := C (T h29 (C h14 h28)) (R v0)
  have h31 := S (h x x x)
  let v32 := M (M (M x x) x) x
  have h33 := C h8 (C (T (C h31 (R v32)) h31) h8)
  have h34 := h x y v32
  have h35 := S h27
  have h36 := C (T h15 (C (T h25 (C h8 (C (T (C h35 h26) h35) h8))) (T (C h18 (T h16 (C (T h19 (C h19 h22)) h18))) (S h23)))) h14
  have h37 := S h13
  have h38 := C h11 (C (T (C h37 h12) h37) h11)
  T (T (T (T h34 h33) h30) (C (T (C h14 (T (T h10 h38) h36)) (S h29)) (T (T (T (T h10 h38) h36) (h (M (M (M y v1) v1) v3) x y)) (C (T (T h34 h33) h30) (T (T (C (C (C h28 h8) h8) (R x)) (C h6 (T (h x y y) (C (T h7 (C h7 (R v4))) h6)))) (S (h y v5 v4))))))) (S (h v3 y v0))

@[equational_result]
theorem Equation2698_implies_Equation2 (G: Type _) [Magma G] (h: Equation2698 G) : Equation2 G := fun x y =>
  let v0 := M x x
  let v1 := M v0 v0
  have h2 := R y
  let v3 := M y y
  have h4 := R v3
  have h5 := h x v1 v1
  have h6 := S h5
  have h7 := R v1
  have h8 := R v0
  have h9 := h x x x
  have h10 := C (C h9 h8) h7
  have h11 := T h10 h6
  have h12 := C h11 h11
  let v13 := M x v0
  have h14 := R (M v13 v1)
  have h15 := C (C (S h9) h8) h7
  have h16 := T h5 h15
  have h17 := C h16 h14
  have h18 := C h16 h16
  have h19 := h v0 x y
  have h20 := S h19
  have h21 := C h16 h2
  have h22 := C h11 h14
  have h23 := T (C (T (T (T h21 h20) h18) h22) (T (T h21 h20) h18)) (C (T h17 h12) h12)
  have h24 := T h21 h20
  have h25 := R x
  let v26 := M v3 v3
  let v27 := M (M x y) v3
  have h28 := C h11 h2
  have h29 := T (C (T h18 h22) h18) (C (T (T (T h17 h12) h19) h28) (T (T h12 h19) h28))
  have h30 := T h19 h28
  have h31 := C h25 h30
  have h32 := h x v27 v1
  have h33 := h y x x
  have h34 := h x x v1
  have h35 := S h34
  let v36 := M y x
  have h37 := S (h v0 v0 v0)
  T (T (T (T (h x (M v36 v0) v13) (C (T (C (T (S (h x y x)) h34) h8) h37) (T (T h31 (C h34 h24)) h37))) (h v1 v1 y)) (C (T (T (T (T (C (T (T h35 h5) h15) h35) (S (h v0 x x))) (h v0 v0 v36)) (C h35 (T (T (T (T (C h2 h16) (C h2 (T (T (T (T h10 h6) h32) (C (C (S h33) h8) h7)) (C (C h2 h30) h29)))) (C h2 (T (T (T (T (T (C (C h2 h24) h23) (C (C h33 h8) h7)) (S h32)) h5) h15) (C h31 h29)))) (C (T (h y v27 v26) (C (C (S (h y x y)) h4) (R v26))) (T (T (C (C h25 h24) h23) h10) h6))) (S (h v3 y x))))) (C (h x x y) h4)) h2)) (S (h y v1 y))

@[equational_result]
theorem Equation2113_implies_Equation11 (G: Type _) [Magma G] (h: Equation2113 G) : Equation11 G := fun x y =>
  let v0 := M y y
  let v1 := M x v0
  let v2 := M v1 v0
  have h3 := h v0 x v0
  have h4 := R v1
  have h5 := R v0
  have h6 := h y y y
  have h7 := S h6
  have h8 := h y v0 v0
  have h9 := S h8
  let v10 := M v0 v0
  have h11 := R v10
  have h12 := C h6 h11
  have h13 := C (T (C (T (T h12 h9) h6) h11) h9) (T h12 h9)
  have h14 := h v10 y v10
  have h15 := h v0 v1 v1
  have h16 := S h15
  let v17 := M v1 v1
  have h18 := R v17
  have h19 := C h3 h18
  have h20 := C (T (C (T (T h19 h16) h3) h18) h16) (T h19 h16)
  have h21 := h v17 v0 v17
  have h22 := T (T (T h21 h20) h14) h13
  have h23 := C h22 h4
  have h24 := h v1 x v0
  have h25 := S h24
  have h26 := C (C h25 h4) h25
  have h27 := h v1 (M (M x v1) v0) v1
  have h28 := S (h y x v0)
  have h29 := S (h x y y)
  have h30 := S h27
  have h31 := S h21
  have h32 := S h3
  have h33 := C h32 h18
  have h34 := C (T h15 (C (T (T h32 h15) h33) h18)) (T h15 h33)
  have h35 := S h14
  have h36 := C h7 h11
  have h37 := C (T h8 (C (T (T h7 h8) h36) h11)) (T h8 h36)
  have h38 := C (T (T (T (T h37 h35) h34) h31) (C h24 h4)) h24
  T (T (T (h x v0 v0) (C (T (T (T (T (T (T (C (C (T (T (T (T (T h37 h35) h34) h31) (C h4 (T (T h27 h26) h23))) (C h4 (T (h (M v0 v1) v1 v1) (C (T (T (C (T (T (T (T (C h4 (T h38 h30)) h21) h20) h14) h13) h4) h38) h30) h22)))) (R x)) (T (h v0 (M (M y x) y) v0) (C (C h29 h5) h29))) (S (h v2 v1 x))) (C (T (h v1 (M (M x y) v0) v1) (C (C h28 h4) h28)) h5)) (S (h v1 y y))) h27) h26) h23) (T (C (T (h v0 (M v0 y) v0) (C (C h7 h5) h7)) h5) (S (h v0 y y))))) (C (C h3 h4) h3)) (S (h v1 v2 v1))

@[equational_result]
theorem Equation2789_implies_Equation1355 (G: Type _) [Magma G] (h: Equation2789 G) : Equation1355 G := fun x y z =>
  let v0 := M z x
  let v1 := M v0 y
  let v2 := M v1 z
  let v3 := M y v2
  have h4 := R z
  have h5 := R v3
  have h6 := R y
  have h7 := S (h y x v3)
  have h8 := T (C (T (h v3 (M (M x v3) (M x y)) v3) (C (C h7 h7) h5)) h6) (S (h v2 y y))
  have h9 := h v0 v1 v1
  have h10 := S h9
  have h11 := R v1
  have h12 := R v0
  let v13 := M x v0
  have h14 := h v1 (M (M x v1) v13) v1
  have h15 := h v0 x v1
  have h16 := T (C (C h15 h15) h11) (S h14)
  have h17 := C h16 h12
  have h18 := h y v0 v0
  have h19 := T h18 h17
  have h20 := R (M v1 v1)
  have h21 := C h20 h19
  have h22 := h y v0 y
  have h23 := C (T h22 h21) h11
  let v24 := M y v1
  have h25 := h v24 v1 v0
  have h26 := T h23 h10
  have h27 := S h22
  have h28 := S h18
  have h29 := S h15
  have h30 := T h14 (C (C h29 h29) h11)
  have h31 := C h30 h12
  have h32 := T h31 h28
  have h33 := C h20 h32
  have h34 := C (T h33 h27) h11
  have h35 := T h9 h34
  have h36 := h z x v0
  T (T (T (h x z z) (C (T (C (C h36 h36) h12) (S (h v0 (M v13 (M x z)) v0))) h4)) (C (T (T (T (T (T h9 h34) h25) (C (T (T (C h32 (T (T (T (C h30 h26) h28) h22) h21)) (C h6 (T (T (T h33 h27) h18) h17))) (C h6 h32)) h35)) (h (M (M y y) v24) v3 y)) (C (C h8 (T (C (C h19 (R v2)) (T (T (T (C (T (T (C h6 h19) (C h6 (T (T (T h31 h28) h22) h21))) (C h19 (T (T (T h33 h27) h18) (C h16 h35)))) h26) (S h25)) h23) h10)) (S (h z v1 v0)))) (T (h y v3 v3) (C (T (C (R (M v3 v3)) h8) (S (h v2 y v2))) h5)))) h4)) (S (h v3 v2 z))

@[equational_result]
theorem Equation2789_implies_Equation2722 (G: Type _) [Magma G] (h: Equation2789 G) : Equation2722 G := fun x y z =>
  let v0 := M z y
  let v1 := M y x
  let v2 := M v1 v0
  let v3 := M v2 z
  have h4 := h v3 z y
  have h5 := R y
  have h6 := R v3
  have h7 := h z v2 v1
  have h8 := h v1 v2 v2
  have h9 := S h8
  have h10 := h v2 (M (M x v2) (M x v1)) v2
  have h11 := S h10
  have h12 := R v2
  have h13 := h v1 x v2
  have h14 := C (C h13 h13) h12
  have h15 := T h14 h11
  have h16 := R v1
  have h17 := C h15 h16
  have h18 := h v0 v1 v1
  have h19 := T h18 h17
  have h20 := S h13
  have h21 := C (C h20 h20) h12
  have h22 := S h18
  have h23 := T h10 h21
  have h24 := C h23 h16
  have h25 := T h24 h22
  have h26 := C (T (C h12 (T (T (C h16 h25) h10) h21)) (C h12 h15)) h19
  let v27 := M v2 v1
  have h28 := h v27 v1 v0
  have h29 := T (T (T h18 h17) h28) h26
  let v30 := M v1 v1
  have h31 := h (M v30 v2) v0 v3
  have h32 := S h28
  have h33 := C h16 h19
  have h34 := C (T (C h12 h23) (C h12 (T (T h14 h11) h33))) h25
  have h35 := T (T (T h34 h32) h24) h22
  have h36 := C h35 (T (T (T h10 h21) h31) (C (T (C (C h19 h6) (T (C h29 h15) h9)) (S h7)) h6))
  have h37 := T (C h29 (T (T (T (C (T h7 (C (C h25 h6) (T h8 (C h35 h23)))) h6) (S h31)) h14) h11)) h9
  have h38 := T h4 (C h37 h5)
  have h39 := R v30
  T (T (T (T (h x y v2) (C (C (R (M y v2)) (T (T (T h8 h36) (h (M v0 (M z v3)) v2 v3)) (C (T (C (C h12 h38) (T (T (T (T (T (C (T (T (T h10 h21) (C h39 h33)) (C h39 (C h16 (T h28 h26)))) h37) (S (h (M (M v2 v2) v27) v1 v1))) h34) h32) h24) h22)) (S (h y v1 v0))) h38))) h12)) (S (h (M v1 y) y v2))) (C (T h8 h36) h5)) (S h4)

@[equational_result]
theorem Equation3182_implies_Equation4109 (G: Type _) [Magma G] (h: Equation3182 G) : Equation4109 G := fun x y z =>
  let v0 := M y z
  let v1 := M v0 z
  let v2 := M v1 y
  have h3 := R x
  have h4 := R v1
  have h5 := R v2
  have h6 := R z
  have h7 := h v0 z v0
  have h8 := R v0
  have h9 := h z y z
  have h10 := S h9
  let v11 := M x x
  have h12 := h v2 v11 v0
  have h13 := R v11
  have h14 := h v11 z v11
  have h15 := h v2 v2 v11
  have h16 := h v2 z v2
  have h17 := h z v2 z
  have h18 := S h17
  have h19 := C (C (C h9 h6) h5) h6
  have h20 := h v2 z z
  have h21 := h z v2 v2
  have h22 := h v11 v2 v2
  have h23 := h z v11 v11
  have h24 := h v0 v2 v11
  have h25 := h z v0 v0
  have h26 := T (C (T h20 (C (T (T (T h19 h18) h25) (C (C (T (C (T (C (T h24 (C (C (C (T (C (T h20 (C (T (T (T h19 h18) h23) (C (C (T (C (T (C (T h22 (C (C (C (T (C (T h20 (C (T (T (T h19 h18) h21) (C (C (T (T (C (C (T h20 (C (T h19 h18) h6)) h5) h6) h19) h18) h5) h5)) h6)) h5) (S h16)) h13) h5) h5)) h13) (S h15)) h6) h10) h13) h13)) h6)) h13) (S h14)) h8) h5) h13)) h8) (S h12)) h6) h10) h8) h8)) h6)) h8) (S h7)
  have h27 := R y
  have h28 := h v2 v0 y
  have h29 := h y v2 v0
  have h30 := S h20
  have h31 := C (C (C h10 h6) h5) h6
  T (C (T (h x v2 v1) (C (C (C (T (T (T (C (T (T h28 (C (T (C (C (C (T h7 (C (T (C (T (T (T (C (C (T h9 (C (T h12 (C (T (C (C (C (T h14 (C (T (C (T (T (T (C (C (T h9 (C (T h15 (C (T (C (C (C (T h16 (C (T (C (T (T (T (C (C (T (T h17 h31) (C (C (T (C (T h17 h31) h6) h30) h5) h6)) h5) h5) (S h21)) h17) h31) h6) h30) h5)) h13) h5) h5) (S h22)) h13)) h6)) h13) h13) (S h23)) h17) h31) h6) h30) h13)) h8) h5) h13) (S h24)) h8)) h6)) h8) h8) (S h25)) h17) h31) h6) h30) h8)) h27) h5) h8) (S h29)) h27)) (C (T (h y v1 y) (C (C (T (C (T h20 (C (T (T (T h19 h18) (h z y y)) (C (C (T (C (T (C (T h29 (C (C (C h26 h27) h5) h8)) h27) (S h28)) h6) h10) h27) h27)) h6)) h27) (S (h y z y))) h4) h27)) h27)) h4) (S (h y y v1))) (h y v0 z)) (C h26 h6)) h3) h5) h4)) h3) (S (h v2 v1 x))

@[equational_result]
theorem Equation4176_implies_Equation3350 (G: Type _) [Magma G] (h: Equation4176 G) : Equation3350 G := fun x y z =>
  let v0 := M z z
  let v1 := M x v0
  have h2 := R z
  have h3 := R y
  have h4 := h x v0 y
  let v5 := M (M v0 y) x
  have h6 := R x
  have h7 := h z z x
  have h8 := S h7
  let v9 := M (M z x) z
  have h10 := h v9 x v0
  have h11 := R v0
  have h12 := h v1 v9 x
  have h13 := R v1
  have h14 := h v0 v1 v0
  have h15 := S h14
  have h16 := h v0 x v0
  have h17 := C h16 h11
  have h18 := h v0 x y
  have h19 := C (S h18) h11
  let v20 := M x y
  have h21 := h y v20 v0
  have h22 := S h21
  have h23 := C h18 h11
  have h24 := C (S h16) h11
  have h25 := h v0 v1 v1
  have h26 := h v1 x v0
  have h27 := h v1 v1 x
  have h28 := h y v1 x
  let v29 := M y v1
  have h30 := h x v0 v20
  have h31 := h v20 (M v0 v20) x
  have h32 := S h26
  have h33 := C h13 (T (C (T (C (T (T (T (T (T h7 h10) (C (T (T (T h12 (C (T (T (T (T (C h8 h13) h14) h24) h23) h22) h6)) (C (T (T (T (T (T h21 h19) h17) h15) h25) (C h32 h13)) h6)) (S h27)) h11)) h32) (C h30 h6)) (S h31)) h3) (C (T h31 (C (S h30) h6)) h3)) h6) (S h28))
  have h34 := S (h v1 v5 y)
  have h35 := C (T (T (T (T (h z z y) (C (T (C (h z y v1) h2) (S (h v1 v29 z))) h3)) (C (T (h v1 v29 v1) (C (S (h v1 y v1)) h13)) h3)) (S (h v1 v1 y))) (C h4 h13)) h3
  T (T (h x y z) (C (T (T (T (T (C (T (h y z z) (C (T (T (T (T (T h35 h34) h33) (h v1 v29 v0)) (C (T (T (T (S (h v0 y v1)) h35) h34) h33) h11)) (S (h v29 x v0))) h2)) h6) (S (h z v29 x))) (C h2 (T h28 (C (C (T (T (T h26 (C (T (T (T h27 (C (T (T (T (T (T (C h26 h13) (S h25)) h14) h24) h23) h22) h6)) (C (T (T (T (T h21 h19) h17) h15) (C h7 h13)) h6)) (S h12)) h11)) (S h10)) h8) h3) h6)))) (h z v5 y)) (C (C (S h4) h2) h3)) h2)) (S (h y v1 z))

@[equational_result]
theorem Equation1131_implies_Equation2538 (G: Type _) [Magma G] (h: Equation1131 G) : Equation2538 G := fun x y z =>
  let v0 := M y x
  let v1 := M v0 z
  let v2 := M y v1
  let v3 := M v2 z
  have h4 := h v3 v3 x
  have h5 := R v3
  have h6 := R x
  have h7 := h v3 v3 v3
  let v8 := M (M v3 (M v3 v3)) v3
  have h9 := R v1
  have h10 := R z
  have h11 := h v1 x v3
  let v12 := M v3 v1
  let v13 := M v1 v1
  have h14 := R v0
  have h15 := h v0 y v2
  have h16 := S h15
  have h17 := R v2
  have h18 := h z y v0
  have h19 := R y
  have h20 := C h19 (C h18 h17)
  have h21 := h z v1 y
  have h22 := S h21
  have h23 := T h15 (C h19 (C (S h18) h17))
  let v24 := M (M v1 (M y z)) y
  have h25 := h v0 v3 v3
  let v26 := M (M v3 (M v3 v0)) v3
  have h27 := h v0 v3 v2
  have h28 := h x v3 v2
  T (T h28 (C h5 (T (T (T (T (T (h (M (M v3 (M v2 x)) v2) v1 v3) (C h9 (C (T (T (T (T (T (C h9 (S h28)) (C h9 (T (T (T (h x x y) (C h6 (C (C h6 h23) h19))) (S (h (M z v2) x y))) (C (T h21 (C h9 (T (h v24 v2 v1) (C h17 (C (C h17 h22) h9))))) h17)))) (S (h v12 v1 v2))) (C h5 (T (C h23 h10) (C (T (T (T h20 h16) h27) (C h5 (T (T (T (T (h (M (M v3 (M v2 v0)) v2) x v3) (C h6 (C (T (C h6 (S h27)) (C h6 h25)) h5))) (S (h v26 x v3))) (h v26 z v3)) (C h10 (C (T (T (T (C h10 (S h25)) (h (M z v0) x v1)) (C h6 (T (T (T (C (C h6 (T (C h9 (C (T h21 (C h9 (T (h v24 v0 v1) (C h14 (C (T (C h23 h22) (C (T h20 h16) h10)) h9))))) h14)) (S (h v13 v1 v0)))) h9) (h (M (M x v13) v1) x x)) (C h6 (C (T (C h6 (S (h v1 x v1))) (C h6 h11)) h6))) (S (h (M (M x v12) v3) x x))))) (S h11)) h5))))) h10)))) (S (h (M v1 v3) v3 z))) (C h9 h7)) h5))) (S (h v8 v1 v3))) (h v8 x v3)) (C h6 (C (T (C h6 (S h7)) (C h6 h4)) h5))) (S (h (M (M v3 (M x v3)) x) x v3))))) (S h4)

@[equational_result]
theorem Equation3385_implies_Equation3940 (G: Type _) [Magma G] (h: Equation3385 G) : Equation3940 G := fun x y z =>
  let v0 := M z y
  let v1 := M x v0
  have h2 := h v1 z x
  have h3 := S h2
  let v4 := M v1 z
  have h5 := R v4
  have h6 := h z x z
  have h7 := S h6
  have h8 := h x z y
  have h9 := S h8
  have h10 := R z
  have h11 := h y v1 v0
  have h12 := h v1 z y
  have h13 := R v0
  have h14 := h v0 v1 z
  have h15 := C h10 (T (T h14 (C h10 (T (C h13 h12) (S h11)))) (C h10 h9))
  have h16 := R v1
  have h17 := C h16 (T h15 h7)
  have h18 := C h13 (S h12)
  have h19 := C h10 (T (T (C h10 h8) (C h10 (T h11 h18))) (S h14))
  have h20 := h z x v0
  have h21 := S h20
  have h22 := C h16 (T (T h21 h6) h19)
  have h23 := h v0 z v1
  have h24 := h x v0 x
  let v25 := M v0 x
  have h26 := h x (M x v25) z
  have h27 := h x v25 v4
  have h28 := h v0 x z
  have h29 := C h13 h9
  have h30 := h y x v0
  have h31 := R x
  let v32 := M y x
  have h33 := h x (M z v32) v4
  have h34 := h z y x
  have h35 := T (T (T h34 h33) (C h5 (C h31 (C (T (C h10 (T h30 h29)) (S h28)) h5)))) (S h27)
  have h36 := T (T (C h10 (T h2 (C h31 (T (T (T (C h16 (T h6 h19)) (C h16 (T (T h15 h7) h20))) (S h23)) (C h35 h10))))) (S h26)) (S h24)
  have h37 := T (T (T h27 (C h5 (C h31 (C (T h28 (C h10 (T (C h13 h8) (S h30)))) h5)))) (S h33)) (S h34)
  T (T (T (T (h x y x) (h x (M x v32) v4)) (C h5 (C h31 (C (T (T (T (T (C h31 (T (T h30 h29) (C h13 (T (T (T (T (T h8 h11) h18) (C h35 h5)) (C h37 (T (T (h v1 z v4) (C h5 (T (h v1 (M z v4) z) (C h10 (T (C (T (T h24 h26) (C h10 (T (C h31 (T (T (T (C h37 h10) h23) h22) h17)) h3))) (C h36 h10)) (C h36 h5)))))) (S (h z v1 v4))))) h21)))) (S (h v0 z x))) h23) h22) h17) h5)))) (S (h x (M v1 (M z x)) v4))) h3

@[equational_result]
theorem Equation3385_implies_Equation4197 (G: Type _) [Magma G] (h: Equation3385 G) : Equation4197 G := fun x y z =>
  let v0 := M z x
  let v1 := M v0 y
  let v2 := M v1 z
  have h3 := h v1 z v2
  have h4 := S h3
  let v5 := M z v2
  have h6 := R v2
  have h7 := h v0 y z
  have h8 := S h7
  let v9 := M y z
  have h10 := h z (M v0 v9) v2
  have h11 := S h10
  have h12 := h v0 v9 v2
  have h13 := h y z v1
  have h14 := h z v0 y
  have h15 := R v1
  have h16 := R v0
  have h17 := h v0 (M v1 (M z v0)) v2
  have h18 := h v1 z v0
  have h19 := R z
  have h20 := C h6 (C h19 (C (T (T (T h18 h17) (C h6 (C h16 (C (T (C h15 h14) (S h13)) h6)))) (S h12)) h6))
  have h21 := h z v2 v2
  have h22 := h v1 v5 z
  have h23 := S h14
  have h24 := T (T (T h7 h10) (C h6 (C h19 (C (T (T (T h12 (C h6 (C h16 (C (T h13 (C h15 h23)) h6)))) (S h17)) (S h18)) h6)))) (S h21)
  have h25 := T (T (T h21 h20) h11) h8
  have h26 := C h6 (T (C h19 (T (C h24 h6) (C h25 (C h24 h19)))) (S h22))
  have h27 := h z v1 v2
  have h28 := T (T h27 h26) h4
  have h29 := C h19 h28
  have h30 := h z z v1
  have h31 := h z z v2
  have h32 := h z v1 z
  have h33 := S h27
  have h34 := C h6 (T h22 (C h19 (T (C h24 (C h25 h19)) (C h25 h6))))
  have h35 := T (T h3 h34) h33
  have h36 := T (C (R y) h35) h23
  T (T (T (T (h x y v2) (h v2 (M x (M y v2)) v2)) (C h6 (C h6 (C (T (T (T (T (C (R x) h36) (S (h z z x))) h30) (C h15 (T (T (T (T (T (T (T (T (T (T h29 h21) h20) h11) h8) (h v0 y v1)) (h v1 (M v0 (M y v1)) v2)) (C h6 (C h15 (C (T (C h16 (T (h y v1 z) (C h19 h36))) (S (h z z v0))) h6)))) (S (h v1 (M z z) v2))) (C h15 (T h31 (C h35 (T (T (T (S h32) h27) h26) h4))))) (C h15 (T (T (T (C h28 (T (T (T h3 h34) h33) h32)) (S h31)) h30) (C h24 (T (T (T (T h29 h21) h20) h11) h8))))))) (S (h v1 v5 v1))) h6)))) (S (h v2 (M v1 v5) v2))) h4

@[equational_result]
theorem Equation3404_implies_Equation3756 (G: Type _) [Magma G] (h: Equation3404 G) : Equation3756 G := fun x y z =>
  let v0 := M y x
  let v1 := M z z
  have h2 := S (h x v0 y)
  have h3 := h y x v1
  have h4 := S h3
  let v5 := M x (M v1 y)
  have h6 := h z z v1
  let v7 := M v1 z
  have h8 := h v1 (M z v7) v0
  let v9 := M v0 v1
  have h10 := R v9
  have h11 := h z v7 v9
  have h12 := R (M v9 z)
  have h13 := h v1 z z
  have h14 := h z z z
  have h15 := R z
  have h16 := h z (M z v1) v9
  have h17 := T (T (T h14 h16) (C h10 (C (T (C h15 h14) (S h13)) h12))) (S h11)
  have h18 := R v0
  have h19 := R v1
  have h20 := S h14
  have h21 := S h16
  have h22 := C h15 h20
  have h23 := C h10 (C (T h13 h22) h12)
  have h24 := T (T (T h11 h23) h21) h20
  have h25 := R v5
  have h26 := T (T (T (h v0 v1 v1) (C h19 (T (T (C h19 (C h19 h3)) (S (h v5 v1 v1))) (C h25 (T (T h6 (C h19 (T (T (T (T (T (T h11 h23) h21) h20) h6) h8) (C h18 (C h24 h10))))) (C h19 (T (T (C h18 (C h17 h10)) (S h8)) (S h6)))))))) (S (h v1 v5 v1))) h4
  have h27 := R y
  have h28 := S (h v9 v0 z)
  have h29 := h v1 z v0
  let v30 := M x y
  have h31 := R x
  T (T (T (T (h x y x) (C h31 (T (T (T (C h27 (T (T (T (T (h x x z) (C h15 (T (C h31 (h z x z)) (S (h v1 z x))))) (C h15 h29)) h28) (C h26 h18))) h2) (C h31 (h y x x))) (S (h v30 x x))))) (C h31 (T (h v30 x v1) (C (T (T (T (T (T (T (T (T (T h14 (C h15 (C h15 h17))) (S (h v7 z z))) (h v7 z v1)) (C h19 (T (C h15 (T (T (C h19 (T (T h13 h22) (h z v1 z))) (S (h v1 z v1))) h29)) h28))) (C h19 (C h10 h3))) (S (h v5 v9 v1))) (C h25 h26)) (h v5 v0 v1)) (C h19 (C h18 h4))) (T (T (S (h y v1 x)) (C h27 (T (T h6 (C h19 (T (T (T (T (T (T h11 h23) h21) h20) h6) h8) (C h18 (C h24 h26))))) (S (h v0 v0 v1))))) h2))))) (S (h v0 (M v1 (M v0 v0)) x))) (S (h v0 v1 v0))

@[equational_result]
theorem Equation4170_implies_Equation41 (G: Type _) [Magma G] (h: Equation4170 G) : Equation41 G := fun x y z =>
  let v0 := M x x
  have h1 := R y
  let v2 := M z z
  have h3 := R v2
  have h4 := h v0 x v0
  have h5 := R x
  have h6 := h x x v0
  have h7 := S h6
  have h8 := C h7 h5
  have h9 := h x v0 x
  have h10 := S (h x v0 v0)
  have h11 := C h4 h5
  have h12 := h x x x
  let v13 := M y z
  let v14 := M v0 v0
  have h15 := h v14 x v13
  have h16 := R v14
  have h17 := R v13
  have h18 := C h7 h17
  have h19 := h v13 v0 x
  have h20 := h v13 v0 v0
  have h21 := S h20
  have h22 := h v0 x x
  have h23 := S h22
  have h24 := R v0
  have h25 := S h4
  have h26 := C h25 h24
  have h27 := h v0 v0 v0
  have h28 := C (T (T (T h27 h26) h23) h4) h17
  let v29 := M v14 v13
  have h30 := R v29
  have h31 := h v14 x v0
  have h32 := T h6 h31
  have h33 := R z
  have h34 := S h31
  have h35 := T (T (T h25 h22) (C h4 h24)) (S h27)
  let v36 := M y y
  have h37 := R v36
  T (T (T (T (T (T (T (T (T h6 (h v14 x v36)) (C (T (T (T (T (C h6 h37) (S (h v36 v0 x))) (h v36 v0 v0)) (C h25 h37)) (S (h v36 x x))) h16)) (S (h v14 y x))) (C (T (T h27 h26) h23) h1)) (C h4 h1)) (S (h y v0 v0))) (h y v0 x)) (C (T (T (T (T (T (T h15 (C (T (T (T (C h6 h17) (S h19)) h20) (C h35 h17)) h16)) (h v29 v14 z)) (C (T (T (T (T (T (T (T (T (T (C (T h34 h7) h33) (C h6 h33)) (S (h z v0 x))) (h z v0 v0)) (C h35 h33)) (C (T (T (T h27 h26) h23) (C h32 h5)) h33)) (S (h z v14 x))) (h z v14 v2)) (C (T (T (C (T (T (T (T (T (T (T h34 h7) h12) h11) h10) h9) h8) h4) h3) (C h25 h3)) (S (h v2 x x))) h33)) (S (h z z x))) h30)) (h v2 v29 x)) (C (T (T (T (T (T (C (T (T (T (T (T (T (T (T (T (C (T (T (T (T h28 h21) h19) h18) (C h32 h17)) h30) (S (h v29 v14 v13))) (C (T (T (T h28 h21) h19) h18) h16)) (S h15)) h7) h12) h11) h10) h9) h8) h5) h11) h10) h9) h8) h4) h3)) (S (h v2 v0 v0))) h1)) (S (h y z v0))

@[equational_result]
theorem Equation1537_implies_Equation3011 (G: Type _) [Magma G] (h: Equation1537 G) : Equation3011 G := fun x y z =>
  have h0 := R x
  let v1 := M y y
  have h2 := h v1 x z
  have h3 := h z z z
  have h4 := S h3
  have h5 := R v1
  let v6 := M z z
  have h7 := h z y v6
  have h8 := R z
  have h9 := h z z v6
  have h10 := R v6
  have h11 := C h8 (T (C h10 h3) (S h9))
  let v12 := M x x
  have h13 := R v12
  have h14 := h v6 x z
  have h15 := R y
  have h16 := C h15 (T (T h14 (C h13 (T h11 (C h8 (T h7 (C h5 h4)))))) (S h2))
  let v17 := M y v6
  have h18 := R v17
  have h19 := h z v17 v6
  let v20 := M v17 v17
  have h21 := R v20
  have h22 := C h8 (T (C h21 h3) (S h19))
  have h23 := h v20 x z
  let v24 := M v17 y
  let v25 := M v24 x
  have h26 := S h14
  have h27 := C h8 (T h9 (C h10 h4))
  have h28 := C h15 (T (T h2 (C h13 (T (C h8 (T (C h5 h3) (S h7))) h27))) h26)
  have h29 := h (M y v1) z v17
  let v30 := M v25 v25
  have h31 := R v30
  have h32 := h v25 z v6
  have h33 := h z v25 v6
  have h34 := h v30 x z
  have h35 := R v25
  have h36 := h v25 z v25
  have h37 := C h18 (T (T (C (C h35 (T (C h10 (T h36 (C h10 (C h35 (T (T h34 (C h13 (T (C h8 (T (C h31 h3) (S h33))) h27))) h26))))) (S h32))) h16) (C h31 (T h29 (C h10 (C h18 (T (T (T (C h28 h18) h23) (C h13 (T h22 h27))) h26)))))) (S (h v17 v25 v6)))
  have h38 := C h18 (T (h y v25 y) (C (C h35 (T h32 (C h10 (T (C h10 (C h35 (T (T h14 (C h13 (T h11 (C h8 (T h33 (C h31 h4)))))) (S h34)))) (S h36))))) h28))
  T (T (h x v17 v24) (C (C h18 (T (h v17 z v6) (C h10 (T (T (C h10 (C h18 (T (T (T h14 (C h13 (T h11 (C h8 (T h19 (C h21 h4)))))) (S h23)) (C h16 h18)))) (S h29)) h28)))) (T (C (T h38 h37) (C h0 (T (T (T (T h38 h37) h23) (C h13 (T h22 (C h8 (T (h z x v6) (C h13 h4)))))) (S (h v12 x z))))) (S (h x v17 x))))) (C (C h18 (T (C h10 h16) (S (h y z y)))) h0)

@[equational_result]
theorem Equation3131_implies_Equation4305 (G: Type _) [Magma G] (h: Equation3131 G) : Equation4305 G := fun x y z =>
  let v0 := M y z
  have h1 := R v0
  have h2 := h z y y
  have h3 := C (S h2) h1
  have h4 := h y v0 y
  let v5 := M z v0
  have h6 := h y x v5
  have h7 := S h6
  have h8 := R x
  have h9 := R v5
  have h10 := T h4 h3
  let v11 := M x y
  have h12 := R v11
  have h13 := C (C h12 h10) h9
  have h14 := R (M v11 y)
  have h15 := C h14 h10
  have h16 := S h4
  have h17 := C h2 h1
  have h18 := T h17 h16
  have h19 := h x v11 x
  have h20 := h y x x
  have h21 := C (C (C (T (C (T (T h17 h16) h20) h12) (S h19)) h18) h18) h18
  have h22 := h v11 v5 v5
  let v23 := M x v11
  have h24 := R v23
  have h25 := R z
  have h26 := h y z v5
  have h27 := h z v5 z
  have h28 := S h27
  have h29 := h v0 z z
  have h30 := C h29 h9
  have h31 := C (T h30 h28) h18
  have h32 := h z y v5
  have h33 := C (S h29) h9
  have h34 := C (T h27 h33) h10
  have h35 := S h32
  have h36 := C h34 h18
  have h37 := C (T h26 (C (T (C (T (T (T h36 h35) h27) h33) h9) h31) h25)) h25
  T (T (T (T (h v23 x v23) (C (T (T (T (T (T (C (C (C (T (h x v11 v11) (C (C (T (C (T (T (T (C (T (T (T h22 h21) h15) h13) h8) h7) (h y z y)) (C (T (T (T (T (C (C (R (M z y)) h10) h10) (C (T (T (T h36 h35) (h z v0 v0)) (C (C (C (T (C h37 h25) (S (h y z z))) h1) h1) h1)) h18)) (S (h v0 y v0))) h37) (C (T (T (T (C (T h34 (C (T (T (T h30 h28) h32) (C h31 h10)) h9)) h25) (S h26)) h6) (C (T (T (T (C (C h12 h18) h9) (C h14 h18)) (C (C (C (T h19 (C (T (T (S h20) h4) h3) h12)) h10) h10) h10)) (S h22)) h8)) h25)) h25)) h12) (S (h x v11 z))) h12) h12)) h24) h24) h24) (S (h v11 v23 v23))) h22) h21) h15) h13) h8)) h7) h4) h3

@[equational_result]
theorem Equation725_implies_Equation14 (G: Type _) [Magma G] (h: Equation725 G) : Equation14 G := fun x y =>
  let v0 := M x y
  let v1 := M y v0
  have h2 := h v1 x x
  have h3 := S h2
  let v4 := M (M x v1) x
  let v5 := M x v4
  have h6 := R v0
  let v7 := M v0 x
  have h8 := R x
  let v9 := M (M y y) y
  have h10 := R y
  let v11 := M (M v0 y) v0
  have h12 := h y v0 v1
  have h13 := C (S h12) h6
  have h14 := C h8 h13
  let v15 := M v0 (M (M v1 y) v1)
  have h16 := h v15 x v0
  have h17 := C h12 h6
  let v18 := M v0 v1
  let v19 := M v18 v0
  have h20 := R v1
  have h21 := h v1 v1 x
  let v22 := M v1 v4
  have h23 := S (h v15 y v0)
  have h24 := h x y v1
  have h25 := C h10 (T (T (h (M y (M (M v1 x) v1)) y y) (C h10 (C h10 (C (S h24) h10)))) (C h10 h17))
  T (T (T (T (T (T h24 h25) h23) h16) (C h8 h14)) (C h8 (T (C h8 (T h2 (C h8 (T (h v5 v1 x) (C h2 (T (C h20 (T (C h3 h8) (C h20 (T (T (T (T (T (T h24 h25) h23) (h v15 v0 v1)) (C h6 (T (C h6 (R (M (M v1 v15) v1))) (C h6 (C (T (T (T (T (C h20 (T (h v15 v1 v0) (C h20 (T (C h20 h13) (C h21 h20))))) (S (h v22 v1 v1))) (h v22 x v1)) (C h8 (C h8 (T (C (S h21) h20) (C (h v1 v1 v0) h20))))) (S (h (M v1 v19) x v1))) h20))))) (S (h v19 v0 v1))) (C (T (T (T (T (T (T (T (T (h v18 x v0) (C h8 (C h8 (C (T (T (T (T (C h6 (C h6 h17)) (S (h v15 v0 v0))) h16) (C h8 (T h14 (C h8 (C (h y v0 v0) h6))))) (S (h (M v0 v11) x v0))) h6)))) (S (h v11 x v0))) (h v11 x y)) (C h8 (C h8 (C (T (T (h (M y v11) x y) (C h8 (C h8 (T (C (S (h y y v0)) h10) (C (h y y y) h10))))) (S (h (M y v9) x y))) h10)))) (S (h v9 x y))) (h v9 x x)) (C h8 (C h8 (C (T (T (h (M x v9) x x) (C h8 (C h8 (T (C (S (h y x y)) h8) (C (h y x x) h8))))) (S (h (M x v7) x x))) h8)))) (S (h v7 x x))) h6))))) (S (h x v1 v0)))))))) (S (h v5 x x))))) h3

