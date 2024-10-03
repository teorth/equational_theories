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
theorem Equation3147_implies_Equation4109 (G: Type _) [Magma G] (h: Equation3147 G) : Equation4109 G := fun x y z =>
  have h0 := R z
  have h1 := R y
  let v2 := M x x
  have h3 := h y v2 y
  have h4 := h v2 x y
  have h5 := h v2 v2 v2
  have h6 := S h5
  have h7 := R v2
  have h8 := h v2 x v2
  let v9 := M y z
  have h10 := R v9
  have h11 := h v9 v2 v9
  have h12 := h v2 x v9
  let v13 := M v9 z
  let v14 := M v13 y
  have h15 := h v2 v14 v13
  have h16 := S h15
  have h17 := R v13
  have h18 := R v14
  have h19 := h v14 v2 v14
  have h20 := h v2 x v14
  have h21 := C h8 h7
  have h22 := T (T h20 (C (C (T h21 h6) h18) h18)) (C (T (C h20 h18) (S h19)) h18)
  have h23 := S h8
  have h24 := C h23 h7
  have h25 := h v2 x v13
  have h26 := h v13 v2 v13
  have h27 := C (T h26 (C (T (T (T (S h25) h5) h24) (C h22 h7)) h17)) h17
  have h28 := C (T (C (T (T (C (T (T h27 h16) h8) h7) h6) h12) h10) (S h11)) h10
  have h29 := h v2 v13 v9
  have h30 := S h20
  have h31 := C (C (T h5 h24) h18) h18
  have h32 := C (T h19 (C h30 h18)) h18
  have h33 := C (T (C (T (T (T (C (T (T h32 h31) h30) h7) h21) h6) h25) h17) (S h26)) h17
  T (T h15 h33) (C h17 (T (C (C (T h3 (C (T (T (S h4) (h v2 z y)) (C (T (C (T (T (C (T (T (T (T (T (T (C (T (h z v2 z) (C (S (h v2 x z)) h0)) h0) (C (C h22 h0) h0)) (C (C (T (T (T (T h32 h31) h30) h15) h33) h0) h0)) (C (C (T (T (T h27 h16) h29) h28) h0) h0)) (C (C (T (T (T (C (T h11 (C (T (T (S h12) h5) (C (T (T h23 h15) h33) h7)) h10)) h10) (S h29)) h5) (C (T (T h23 h29) h28) h7)) h0) h0)) (S (h v2 v9 z))) h8) h7) h6) h4) h1) (S h3)) h1)) h1)) h0) h0) (S (h y y z))))

@[equational_result]
theorem Equation2707_implies_Equation2734 (G: Type _) [Magma G] (h: Equation2707 G) : Equation2734 G := fun x y =>
  let v0 := M x x
  let v1 := M y y
  let v2 := M v1 v0
  let v3 := M v2 y
  let v4 := M v3 y
  let v5 := M v4 v4
  have h6 := h v3 v5
  have h7 := R v5
  have h8 := h y v3
  have h9 := h y v2
  have h10 := S h9
  have h11 := R v2
  let v12 := M v3 v3
  have h13 := h v12 v1
  have h14 := S h13
  have h15 := R v1
  have h16 := R (M v1 v12)
  have h17 := R v12
  have h18 := h v2 v12
  have h19 := T h18 (C (C h10 h10) h17)
  have h20 := C (T (C h11 h19) (C h19 h16)) h15
  have h21 := h v0 v1
  have h22 := T (C (T (T h21 h20) h14) h11) h10
  have h23 := R v3
  have h24 := C h23 h22
  let v25 := M v0 v2
  let v26 := M v3 v25
  have h27 := T (C (C h9 h9) h17) (S h18)
  have h28 := T h9 (C (T (T h13 (C (T (C h27 h16) (C h11 h27)) h15)) (S h21)) h11)
  have h29 := C h23 h28
  have h30 := C h15 (C h29 h29)
  have h31 := S h8
  have h32 := T h6 (C (C h31 h31) h7)
  let v33 := M x y
  let v34 := M v33 v33
  have h35 := h x v34
  have h36 := R v34
  have h37 := h y x
  have h38 := R x
  have h39 := C h38 h22
  have h40 := T (T (C h15 (C h39 h39)) (C (C h37 h37) h36)) (S h35)
  let v41 := M x v25
  have h42 := C h38 h28
  have h43 := S h37
  T (T (T (T (T h35 (C (C h43 h43) h36)) (C h15 (C h42 h42))) (C h15 (T (T (T (h (M v41 v41) v1) (C (T (T (T (T (T (T (C h40 h40) h21) h20) h14) (C h23 h32)) (C h32 (R (M v1 v5)))) (C h30 h30)) h15)) (S (h (M v26 v26) v1))) (C h24 h24)))) (C (C h8 h8) h7)) (S h6)

@[equational_result]
theorem Equation887_implies_Equation1523 (G: Type _) [Magma G] (h: Equation887 G) : Equation1523 G := fun x y z =>
  let v0 := M z z
  let v1 := M x v0
  let v2 := M y y
  let v3 := M v2 v1
  have h4 := R v1
  let v5 := M v3 v2
  have h6 := h v1 v5 y
  have h7 := S h6
  have h8 := R v2
  have h9 := h v2 v1 y
  have h10 := R v5
  have h11 := C h10 (C h9 h8)
  let v12 := M v2 v2
  have h13 := h (M v5 v12) v3 y
  have h14 := S h13
  have h15 := R v3
  have h16 := S h9
  have h17 := C h10 (C h16 h8)
  have h18 := h v3 v3 v3
  have h19 := h v2 v1 (M v3 v3)
  have h20 := C (T (T h19 (C h4 (S h18))) (C (T h6 h17) h15)) h8
  have h21 := C h15 h20
  have h22 := T (T (T h21 h14) h11) h7
  have h23 := S h19
  have h24 := C h4 h18
  have h25 := C (T h11 h7) h15
  have h26 := C h15 (C (T (T h25 h24) h23) h8)
  have h27 := C (T (T (T h6 h17) h13) h26) h22
  have h28 := h v2 v1 v2
  have h29 := T (T h28 h27) (C h22 h4)
  let v30 := M v3 v0
  have h31 := h v2 v2 v2
  have h32 := S h31
  have h33 := R (M v12 v12)
  have h34 := h v1 v5 v12
  T (T (h x v0 v2) (C (R v0) (T (T (T (T (T (T (T (T (C h4 (T (T h20 (C (C (T h13 h26) h15) h8)) (C (T (T (T (T (T (C (T h21 h14) h15) h25) h24) h23) h28) h27) h29))) (S (h (M v3 v12) v1 v1))) h21) h14) h11) h7) h34) (C h10 (T (C h16 h33) h32))) (C (T (T (h v5 v2 v1) (C h8 (C (T (T (T (C h10 (T h31 (C h9 h33))) (S h34)) (h v1 v30 v12)) (C (R v30) (T (C (S (h v2 v1 z)) h33) h32))) (R (M v1 v1))))) (S (h v30 v2 v1))) h29)))) (S (h v3 v0 v1))

@[equational_result]
theorem Equation2789_implies_Equation4458 (G: Type _) [Magma G] (h: Equation2789 G) : Equation4458 G := fun x y z =>
  have h0 := R z
  let v1 := M z y
  have h2 := h z x v1
  let v3 := M v1 z
  let v4 := M y x
  have h5 := R y
  let v6 := M x v4
  have h7 := R v4
  have h8 := h y x v4
  have h9 := h x y x
  have h10 := h x v6 v6
  have h11 := S h10
  let v12 := M x x
  have h13 := h v6 (M (M x v6) v12) v6
  have h14 := S h13
  have h15 := R v6
  have h16 := h x x v6
  have h17 := C (C h16 h16) h15
  have h18 := T h17 h14
  have h19 := R x
  have h20 := C h18 h19
  have h21 := h v4 x x
  have h22 := T h21 h20
  have h23 := S h16
  have h24 := C (C h23 h23) h15
  have h25 := S h21
  have h26 := T h13 h24
  have h27 := C h26 h19
  have h28 := T h27 h25
  have h29 := h (M v6 x) x v4
  have h30 := C (T (T (T h21 h20) h29) (C (T (C h15 (T (T (C h19 h28) h13) h24)) (C h15 h18)) h22)) h18
  let v31 := M v4 v4
  have h32 := R v31
  let v33 := M v12 v6
  T (T (T h13 h24) (h v33 z z)) (C (T (T (C (R (M z z)) (C h0 (T (T (h v33 v4 v3) (C (C (R (M v4 v3)) (T (T (T (T (T (T h30 h11) h9) (C h32 (T h10 (C (T (T (T (C (T (C h15 h26) (C h15 (T (T h17 h14) (C h19 h22)))) h28) (S h29)) h27) h25) h26)))) (C h32 (C h7 h18))) (h (M v31 (M v4 v6)) y y)) (C (T (T (C (R (M y y)) (C h5 (T (T (C h32 (C h7 h26)) (C h32 (T h30 h11))) (S h9)))) (C (C h8 h8) h7)) (S (h v4 (M v6 (M x y)) v4))) h5))) (R v3))) (S (h y v4 v3))))) (C (C h2 h2) (R v1))) (S (h v1 (M (M x v1) (M x z)) v1))) h0)

@[equational_result]
theorem Equation3791_implies_Equation3895 (G: Type _) [Magma G] (h: Equation3791 G) : Equation3895 G := fun x y z =>
  let v0 := M x x
  let v1 := M y z
  let v2 := M y v1
  have h3 := h z v0 y
  have h4 := h v0 y v1
  have h5 := h y z z
  have h6 := S h5
  let v7 := M z z
  let v8 := M z y
  have h9 := h v8 v7 v0
  have h10 := h x x z
  have h11 := S h10
  have h12 := h (M z x) (M x z) v0
  have h13 := S h12
  have h14 := h z x x
  have h15 := h x z x
  have h16 := C h15 h14
  have h17 := h z z x
  have h18 := R v7
  have h19 := h z z z
  have h20 := S h17
  have h21 := C (S h15) (S h14)
  have h22 := h z y z
  have h23 := h z z y
  have h24 := h v8 v7 v1
  have h25 := h v1 v0 y
  have h26 := h (M v0 y) (M v1 v0) v2
  have h27 := h y v1 v0
  have h28 := T (T (T h27 h26) (C (T (T (T (S h25) (C (T (T h5 h24) (C (T (T (T (T (S h23) h17) h16) h13) h11) (S h22))) (T (T (T (T (T h10 h12) h21) h20) h19) (C h18 (T (T (T h17 h16) h13) h11))))) (S h9)) h6) (S h4))) (S h3)
  let v29 := M v2 z
  have h30 := T (T (T (T (T (C h18 (T (T (T h10 h12) h21) h20)) (S h19)) h17) h16) h13) h11
  have h31 := h v2 z z
  let v32 := M z v2
  T (T (T (T (T (T (h x x v2) (h (M v2 x) (M x v2) v0)) (C (S (h x v2 x)) (S (h v2 x x)))) (S (h v2 v2 x))) (C h28 (R v2))) (C (T (T (h z v0 v2) (C (T (T h31 (h v32 v7 v0)) (C (T (T (C (T (T (T (T h10 h12) h21) h20) (h z z v2)) (h z v2 z)) (S (h v32 v7 v29))) (S h31)) h30)) (T (h v0 v2 z) (C (T (T (T h3 (C (T (T (T h5 h9) (C (T (T (C (T (T (T (T h10 h12) h21) h20) h23) h22) (S h24)) h6) h30)) h25) h4)) (S h26)) (S h27)) (R v29))))) (S (h v0 v2 v29))) h28)) (S (h v2 z v0))

@[equational_result]
theorem Equation978_implies_Equation11 (G: Type _) [Magma G] (h: Equation978 G) : Equation11 G := fun x y =>
  let v0 := M y y
  let v1 := M x v0
  have h2 := h v1 v1 v1
  have h3 := S h2
  let v4 := M v1 v1
  have h5 := h v4 v1 x
  have h6 := S h5
  have h7 := R (M v4 v1)
  have h8 := h (M x x) v1 y
  have h9 := h x v0 x
  have h10 := h x v0 y
  have h11 := S h10
  have h12 := R v1
  have h13 := h v0 v1 y
  have h14 := T (T h13 (C h12 (T h11 h9))) (S h8)
  have h15 := h x v0 v1
  have h16 := C h12 (T (T h11 h15) (C h14 h7))
  have h17 := T (T h13 h16) h6
  have h18 := C h17 h17
  have h19 := h (M v0 v0) v1 y
  have h20 := S h19
  have h21 := h x v0 v0
  have h22 := C h12 (T h11 h21)
  have h23 := T (T (T h13 h22) h20) h18
  have h24 := C h12 h23
  let v25 := M v1 v0
  have h26 := S h13
  have h27 := C h12 (T (S h21) h10)
  have h28 := C h12 (T (S h9) h10)
  have h29 := T (T h8 h28) h26
  have h30 := C h12 (T (T (C h29 h7) (S h15)) h10)
  have h31 := T (T h5 h30) h26
  have h32 := C h31 h31
  let v33 := M v4 v4
  have h34 := R (M v33 v0)
  have h35 := C (T (T (T (T h5 h30) h22) h20) h18) h31
  have h36 := T (T (T (T h32 h19) h27) h16) h6
  have h37 := C h12 (T (T (T h32 h19) h27) h26)
  have h38 := R (M v33 v1)
  T (T (T (T (T (T (T h10 (C h17 (C h23 h12))) (C h31 h38)) (C h14 h38)) (C h29 (C h36 (T (T (T h2 h37) (h v25 v1 x)) (C (T h2 h37) (T (T (T (T (T (T (C (T (T (T h8 h28) h16) h6) (R (M v25 v1))) (C h31 (T (T (T (T (T (T (T (T (T (C (T h24 h3) h12) h5) h30) h22) h20) h18) h35) (C h36 (T (T (T (T h13 h22) h20) h18) h35))) (C h31 h34)) (C h14 h34)))) (S (h v33 v0 x))) h32) h19) h27) h26)))))) (S (h v25 v0 v1))) h24) h3

@[equational_result]
theorem Equation3385_implies_Equation4229 (G: Type _) [Magma G] (h: Equation3385 G) : Equation4229 G := fun x y z =>
  let v0 := M z z
  let v1 := M v0 y
  let v2 := M v1 x
  have h3 := R v2
  have h4 := h z z y
  have h5 := S h4
  let v6 := M z y
  have h7 := h y (M z v6) v2
  have h8 := S h7
  have h9 := h z v6 v2
  have h10 := h z y v0
  have h11 := h y z z
  have h12 := R v0
  have h13 := R z
  have h14 := h z (M v0 (M y z)) v2
  have h15 := h v0 y z
  have h16 := R y
  have h17 := C h3 (C h16 (C (T (T (T h15 h14) (C h3 (C h13 (C (T (C h12 h11) (S h10)) h3)))) (S h9)) h3))
  have h18 := h y v1 v2
  have h19 := h y v1 v1
  have h20 := h z z v0
  have h21 := h z z z
  have h22 := h v0 v0 v2
  let v23 := M y v1
  have h24 := h v0 v23 v2
  have h25 := R v1
  have h26 := h v1 (M v0 v23) y
  have h27 := h v0 y v1
  have h28 := S h27
  have h29 := S h26
  have h30 := S h18
  have h31 := C h3 (C h16 (C (T (T (T h9 (C h3 (C h13 (C (T h10 (C h12 (S h11))) h3)))) (S h14)) (S h15)) h3))
  have h32 := C (T (T (T (T h20 (C h12 (S h21))) h22) (C h3 (C h12 (C (T (T (T h4 h7) h31) h30) h3)))) (S h24)) h16
  let v33 := M y v0
  T (T (T (T (h x y v0) (h v0 (M x v33) v2)) (C h3 (C h12 (C (T (h x v33 v1) (C h25 (C (R x) (T (T (T (T (T (C (T (T (C h16 (T (T (T (T (T h4 h7) h31) h30) h19) (C h25 (T (T (T (C h16 (C h25 h32)) h29) h28) h32)))) h29) h28) (T (T h27 h26) (C h16 (C h25 (C (T (T (T (T h24 (C h3 (C h12 (C (T (T (T h18 h17) h8) h5) h3)))) (S h22)) (C h12 h21)) (S h20)) h16))))) (S h19)) h18) h17) h8) h5)))) h3)))) (S (h v0 (M v1 (M x v0)) v2))) (S (h v1 x v0))

@[equational_result]
theorem Equation4176_implies_Equation3417 (G: Type _) [Magma G] (h: Equation4176 G) : Equation3417 G := fun x y z =>
  let v0 := M y x
  have h1 := h z v0 v0
  have h2 := S h1
  have h3 := R v0
  have h4 := R z
  have h5 := h y x z
  have h6 := S h5
  let v7 := M z v0
  let v8 := M (M x z) y
  have h9 := S (h v8 z v7)
  have h10 := R v7
  let v11 := M z v7
  have h12 := S (h v11 v8 z)
  have h13 := C (C h5 (R v11)) h4
  let v14 := M v0 v11
  have h15 := S (h v14 z v7)
  have h16 := C (T (C (h z v0 v11) h4) (S (h v11 v14 z))) h10
  have h17 := h v7 z v0
  have h18 := C (S h17) h10
  have h19 := h v0 v7 v7
  have h20 := C (T (T (T (T (T h19 h18) h16) h15) h13) h12) h10
  have h21 := C (T (T h20 h9) h6) h10
  have h22 := h v7 v0 v7
  have h23 := R x
  let v24 := M v0 v0
  have h25 := h v0 v24 z
  let v26 := M x y
  let v27 := M x x
  T (T (T (T (T (T (T (T (h x y x) (C (C (h y x x) h23) h23)) (S (h x (M v27 y) x))) (C h23 (T (T (h v27 y x) (C (T (T (C h3 (T (T (h x x x) (C (T (T (T (C (h x x y) h23) (S (h y v26 x))) (h y v26 v0)) (C (S (h v0 x y)) h3)) h23)) (S (h v0 v0 x)))) h25) (C h2 h4)) h23)) (C (T (T (T (T (T (T (C h1 h4) (S h25)) (h v0 v24 v7)) (C (T (T (S (h v7 v0 v0)) h22) h21) h10)) h20) h9) h6) h23)))) (h x (M v0 x) z)) (C (S (h z v0 x)) h4)) (C (h z v0 z) h4)) (S (h z (M v0 z) z))) (C h4 (T (T (h v0 z v0) (C (T (T (T h22 h21) (h v0 v7 z)) (C (T (C (T h17 (C (T (h v7 v7 v0) (C (T (T (C (T (T (T (T (T (T (T h22 h21) h19) h18) h16) h15) h13) h12) h10) h9) h6) h3)) h3)) h3) (S (h v0 v0 v0))) h4)) h3)) h2))

@[equational_result]
theorem Equation4197_implies_Equation4461 (G: Type _) [Magma G] (h: Equation4197 G) : Equation4461 G := fun x y z =>
  let v0 := M y x
  let v1 := M z z
  have h2 := R v0
  let v3 := M v1 y
  have h4 := R v3
  have h5 := R v1
  have h6 := R x
  have h7 := h y x v1
  have h8 := S h7
  have h9 := h v1 y v1
  have h10 := S h9
  have h11 := R y
  have h12 := h z z z
  have h13 := S h12
  have h14 := C h13 h5
  have h15 := h z z v1
  have h16 := C (T h15 h14) h11
  have h17 := C h16 h5
  have h18 := h v3 v1 v3
  have h19 := C (T (C (T (T h17 h10) h16) h5) h10) h4
  have h20 := h v1 v1 v3
  have h21 := T (T (T (C (T h15 (C (T (T (T (T h13 h15) h14) h20) h19) h5)) h4) (S h18)) h17) h10
  have h22 := C (C h21 h6) h5
  have h23 := S h15
  have h24 := C h12 h5
  have h25 := S h20
  have h26 := C (T h24 h23) h11
  have h27 := C h26 h5
  have h28 := C (T h9 (C (T (T h26 h9) h27) h5)) h4
  have h29 := C (T (T (T h9 h27) h18) (C (T (C (T (T (T (T h28 h25) h24) h23) h12) h5) h23) h4)) h6
  have h30 := S (h v3 x v1)
  have h31 := C (T (T (T h7 (C h29 h5)) h30) h29) h5
  have h32 := h v3 y v3
  T (T (T (T (T (h x v0 v0) (h (M (M v0 x) v0) v0 v3)) (C (C (C h4 (T (C (T (h v0 x v1) (C (C (T (T (T (T (C (T (T (T (T (T (T (T h15 h14) h20) h19) (C (C (T (T (T h15 h14) h20) h19) h11) h4)) (S h32)) (h v3 y v1)) (C (T (T (T (T (T (T (C h21 h11) h32) (C (C (T (T (T h28 h25) h24) h23) h11) h4)) h28) h25) (h v1 v1 v0)) (C (T (T (C (T (T h31 h30) h29) h5) h22) h8) h2)) h5)) h2) (S (h v0 v1 v0))) h31) h22) h8) h6) h5)) h2) (S (h x v1 v0)))) h2) h4)) (S (h (M x v1) v0 v3))) (C (h x v1 y) h2)) (S (h v1 y v0))

@[equational_result]
theorem Equation1507_implies_Equation1340 (G: Type _) [Magma G] (h: Equation1507 G) : Equation1340 G := fun x y z =>
  let v0 := M y z
  let v1 := M v0 (M v0 v0)
  let v2 := M v0 z
  let v3 := M v2 x
  let v4 := M y v3
  let v5 := M v4 (M v4 v3)
  let v6 := M v3 y
  have h7 := h v6 v3 x
  have h8 := R (M x (M x v3))
  let v9 := M v3 v6
  have h10 := h v9 v4 v3
  let v11 := M v3 v4
  let v12 := M v3 v11
  have h13 := R v12
  have h14 := h v3 y v3
  have h15 := h v12 v3 x
  have h16 := h v3 y v4
  have h17 := h y v4 y
  let v18 := M v4 y
  let v19 := M y v4
  let v20 := M y v19
  have h21 := h v20 v18 v4
  have h22 := S h14
  have h23 := h v9 v4 y
  have h24 := h z y v3
  let v25 := M v4 (M v4 z)
  let v26 := M v3 v2
  let v27 := M v3 v26
  have h28 := h v2 v3 v4
  have h29 := h x v2 v3
  T (T h29 (C (T (T (T (T (C h28 h29) (S (h v5 v26 v3))) (h v5 v26 v5)) (C (T (S h28) (h v2 v3 y)) (R (M v5 (M v5 v26))))) (S (h v19 v26 v5))) (T (h v27 z v4) (C (T (C (h z v0 v0) (R v27)) (S (h v1 v2 v3))) (T (h v25 y v4) (C (T (C (T (T (T (T (T (T (h y v3 v2) (C (T (T h7 (C (T h10 (C h22 h13)) h8)) (S h15)) (R (M v2 (M v2 v3))))) (S (h v11 v3 v2))) (C h14 (T (C h17 h16) (S h21)))) (S h23)) (h v9 v0 v0)) (C (S h24) (R v1))) (R v25)) (S (h v1 z v4))) (T (T (T (T (T (T (T (T (h (M v4 v18) v0 x) (C (T (S (h z y v4)) h24) (R (M x (M x v0))))) (S (h v9 v0 x))) h23) (C h22 (R v20))) (C (R v3) (T h21 (C (S h17) (S h16))))) (h v11 v3 v4)) (C (T (T h15 (C (T (C h14 h13) (S h10)) h8)) (S h7)) (R v5))) (S (h y v3 v4))))))))) (S (h v4 y v1))

@[equational_result]
theorem Equation4197_implies_Equation4362 (G: Type _) [Magma G] (h: Equation4197 G) : Equation4362 G := fun x y z =>
  let v0 := M y z
  let v1 := M x v0
  let v2 := M x z
  let v3 := M y v2
  have h4 := R v3
  have h5 := R v1
  have h6 := h x v0 v1
  let v7 := M v1 x
  have h8 := h v7 v0 x
  have h9 := R x
  have h10 := h y z x
  let v11 := M x y
  have h12 := h (M v11 z) x v3
  have h13 := h v11 z v3
  have h14 := R z
  have h15 := h x y v0
  have h16 := R v0
  have h17 := h z x y
  have h18 := h (M (M z x) v0) z v3
  have h19 := h x v0 z
  have h20 := h v1 x v3
  have h21 := T (T (T h20 (C (C (C h4 (T (T (T h19 h18) (C (C (C h4 (T (C h17 h16) (S h15))) h14) h4)) (S h13))) h9) h4)) (S h12)) (S h10)
  have h22 := S h20
  have h23 := C (C (C h4 (T (T (T h13 (C (C (C h4 (T h15 (C (S h17) h16))) h14) h4)) (S h18)) (S h19))) h9) h4
  have h24 := T (T (T h10 h12) h23) h22
  have h25 := h v0 x v1
  have h26 := C (T (T h25 (C (T (C (T (C h5 h24) (C (C h9 h24) h21)) h9) (S h8)) h5)) (S h6)) (R y)
  have h27 := S (h x x v0)
  have h28 := C (T (T h6 (C (T h8 (C (T (C (C h9 h21) h24) (C h5 h21)) h9)) h5)) (S h25)) h9
  T (T (T (T h6 (h (M v7 v0) v1 v3)) (C (C (C h4 (T (T (T (T (h v7 v0 v0) (C (T (T (T (T (T (T (T (T (T (C (T (C (T (T (T (T h10 h12) h23) h22) h28) h21) h27) h16) (h (M x x) v0 v3)) (C (C (C h4 (T (h x x z) (C (T (C (T h17 h26) h9) (S (h v0 y x))) h14))) h16) h4)) (S (h (M (M v0 y) z) v0 v3))) (S (h y z v0))) h10) h12) h23) h22) h28) h16)) h27) (h x x v2)) (C (T (T (S (h z x x)) h17) h26) (R v2)))) h5) h4)) (S (h (M (M v1 y) v2) v1 v3))) (S (h y v2 v1))

@[equational_result]
theorem Equation1181_implies_Equation16 (G: Type _) [Magma G] (h: Equation1181 G) : Equation16 G := fun x y =>
  let v0 := M y x
  let v1 := M y v0
  have h2 := h v1 y v1
  have h3 := S h2
  have h4 := R y
  have h5 := h x v1 y
  have h6 := C h5 h4
  have h7 := h y x v1
  have h8 := S h7
  have h9 := R x
  let v10 := M v1 y
  have h11 := h v10 v1 y
  have h12 := R v1
  have h13 := h x y y
  have h14 := C h4 h13
  have h15 := h (M v0 v1) x v1
  have h16 := h v0 x x
  have h17 := S h16
  have h18 := h (M (M x (M x v0)) x) x x
  have h19 := h v0 x y
  have h20 := h (M (M y v1) x) x x
  have h21 := h (M x y) x y
  have h22 := C h9 h8
  have h23 := h y x y
  let v24 := M (M v1 v10) x
  have h25 := S h5
  have h26 := T (T (T h16 (C h9 (T (T (T h18 (C h9 (C (T (C h9 h17) (C h9 h19)) h9))) (S h20)) (C (C h4 (T h2 (C h4 (C h25 h4)))) h9)))) (S h21)) (C h9 h7)
  have h27 := C h4 (S h13)
  have h28 := h v1 x v1
  have h29 := h v10 x y
  T (T h13 (C h4 (T (T h29 (C h9 (T (T (T (T (T (T (C h27 h9) (h (M v0 x) v0 x)) (C h26 (C (T (T (C h9 (T (C h9 (C h14 h9)) (S h29))) (C h9 (T (T (T (T (T (C (T h28 (C h9 (C h25 h9))) h4) (C (T (C h9 (C h5 h9)) (S h28)) (T (T (T h7 (C h9 (C (C h12 (T h11 (C h12 (C h27 h12)))) h9))) (S h15)) (C h26 h12)))) (S (h v24 v1 x))) (h v24 x x)) (C h9 (C (T h22 (C h9 h23)) h9))) (S (h (M (M y (M y y)) x) x x))))) (S h23)) (R v0)))) (C (T (T (T h22 h21) (C h9 (T (T (T (C (C h4 (T (C h4 h6) h3)) h9) h20) (C h9 (C (T (C h9 (S h19)) (C h9 h16)) h9))) (S h18)))) h17) h12)) h15) (C h9 (C (C h12 (T (C h12 (C h14 h12)) (S h11))) h9))) h8))) h6))) h3

@[equational_result]
theorem Equation572_implies_Equation4162 (G: Type _) [Magma G] (h: Equation572 G) : Equation4162 G := fun x y z =>
  let v0 := M y x
  let v1 := M v0 z
  let v2 := M v1 z
  have h3 := h v2 v1 v1
  have h4 := S h3
  have h5 := h v1 z z
  have h6 := R v2
  have h7 := h z v2 z
  have h8 := T h7 (C h6 (S h5))
  have h9 := R v1
  have h10 := C h9 (C h9 (C h9 h8))
  have h11 := h v2 v1 v0
  have h12 := R v0
  have h13 := C h12 h8
  have h14 := C h12 h13
  have h15 := C h9 (C h9 (T (C h9 h14) (S h11)))
  have h16 := h v0 v1 v1
  have h17 := S h16
  have h18 := T (C h6 h5) (S h7)
  have h19 := C h12 h18
  have h20 := C h12 h19
  have h21 := C h9 (C h9 (T h11 (C h9 h20)))
  have h22 := T (T (T h3 (C h9 (C h9 (C h9 h18)))) h21) h17
  have h23 := h y x z
  have h24 := S h23
  have h25 := h v0 z v0
  have h26 := h v1 v2 v1
  have h27 := T (T (T h16 h15) h10) h4
  have h28 := h v1 v0 v0
  have h29 := R z
  have h30 := h v0 z z
  have h31 := R x
  have h32 := C h31 (T h30 (C h29 (C h29 (T (C h29 (T h28 (C h12 (T (C h12 (T (T (C h27 (C h9 (T h16 h15))) (S h26)) h13)) h20)))) (S h25)))))
  have h33 := T h32 h24
  let v34 := M x y
  have h35 := R v34
  T (T (T (T (T (T (h v34 y v34) (C (R y) (T (T (T (T (C h35 (T (C h35 (C h35 (T h23 (C h31 (T (C h29 (C h29 (T h25 (C h29 (T (C h12 (T h14 (C h12 (T (T h19 h26) (C h22 (C h9 (T h21 h17))))))) (S h28)))))) (S h30)))))) (C h35 (C h35 (T (T (T h32 h24) (h y x x)) (C h31 (C h31 h33))))))) (S (h x v34 v34))) (h x v0 v2)) (C h27 (C h6 (C h22 h33)))) (C h22 (C h22 (R (M v0 y))))))) (S (h v0 y v0))) h16) h15) h10) h4

@[equational_result]
theorem Equation2319_implies_Equation3692 (G: Type _) [Magma G] (h: Equation2319 G) : Equation3692 G := fun x y z =>
  let v0 := M z z
  let v1 := M y y
  let v2 := M v1 v0
  let v3 := M v2 v2
  have h4 := h v1 v3 z
  have h5 := S h4
  have h6 := R v3
  have h7 := h v1 v2 z
  have h8 := C h7 h6
  let v9 := M v1 v3
  have h10 := h v9 v2 v2
  have h11 := R v2
  have h12 := C (S h7) h6
  let v13 := M x x
  have h14 := h v1 v13 y
  have h15 := S h14
  let v16 := M v13 (M v1 v1)
  have h17 := h v16 v2 x
  have h18 := h v16 x x
  have h19 := R x
  have h20 := h v1 v1 v2
  let v21 := M v1 v9
  have h22 := h v21 x y
  let v23 := M v13 v13
  have h24 := R v13
  have h25 := h v13 v13 y
  have h26 := S h25
  let v27 := M v13 (M v13 v1)
  have h28 := S (h v27 x x)
  have h29 := C h19 h25
  have h30 := C (T (C h19 (S (h v13 v13 x))) h29) h19
  let v31 := M v13 v23
  have h32 := h v31 x x
  have h33 := h v13 x v13
  have h34 := R v1
  have h35 := h v13 v0 v13
  T h35 (C (T (T (T (T (T (T (T (T (T (T (T (h (M v0 v31) x z) (C (T (C h19 (S h35)) h29) h19)) (C (T (C h19 h26) (C h19 (T (T (T h33 (C (C h19 (T (T (T (T h32 h30) h28) (h v27 v1 x)) (C (C h34 h26) h34))) h19)) (S (h (M v1 v13) x y))) (C (T (T (T (T (T (T (T h4 h12) h10) (C (T (C h11 (T (T (C (T h8 h5) h6) h8) h5)) (C h11 h14)) h11)) (S h17)) h18) (C (T (C h19 h15) (C h19 h20)) h19)) (S h22)) (T (T h33 (C (C h19 (T (T (T (T h32 h30) h28) (h v27 v13 x)) (C (C h24 h26) h24))) h19)) (S (h v23 x x))))))) h19)) (S (h v21 x v13))) h22) (C (T (C h19 (S h20)) (C h19 h14)) h19)) (S h18)) h17) (C (T (C h11 h15) (C h11 (T (T h4 h12) (C (T h4 h12) h6)))) h11)) (S h10)) h8) h5) (R v0))

@[equational_result]
theorem Equation2779_implies_Equation3147 (G: Type _) [Magma G] (h: Equation2779 G) : Equation3147 G := fun x y z =>
  let v0 := M y y
  let v1 := M v0 x
  let v2 := M v1 z
  let v3 := M v2 z
  have h4 := h v3 y v3
  have h5 := h y y y
  have h6 := S h5
  have h7 := R y
  let v8 := M v0 v0
  have h9 := h v8 v0 v0
  have h10 := R v0
  have h11 := R x
  have h12 := h y y v2
  let v13 := M x y
  let v14 := M y v2
  let v15 := M v14 v14
  have h16 := h v8 v0 y
  have h17 := R v8
  have h18 := h v0 v0 v0
  let v19 := M (M y v3) (M v3 v3)
  let v20 := M v3 y
  let v21 := M v0 y
  have h22 := h v0 v3 z
  let v23 := M v0 z
  let v24 := M (M v3 z) v23
  have h25 := h v0 v1 v3
  have h26 := R (M x v1)
  let v27 := M v1 y
  have h28 := h x y y
  T (T (T (T (T (T (T (T (T (T (T (T (T h28 (C (T (h (M v0 v13) y y) (C (C h10 (S h28)) h7)) h7)) (C (R v27) (T h5 (C (T (T h9 (C (C h17 (T (C (T (T (h v8 y y) (C (C h10 h6) h7)) (C (R v21) h5)) h10) (S h16))) h10)) (S h18)) h7)))) (h (M v27 v21) x v1)) (C (C h26 (T (S (h v0 v1 y)) h25)) h11)) (C (C h26 (T (S h25) (h v0 v1 z))) h11)) (S (h (M v2 v23) x v1))) (C (T (h v2 v0 z) (C (R (M v23 v3)) h22)) (R v23))) (S (h v24 v23 v3))) (h v24 x v3)) (C (C (R (M x v3)) (T (S h22) (h v0 v3 y))) h11)) (S (h (M v20 v21) x v3))) (C (T (T (h v20 x v0) (C (C (R (M x v0)) (T (h (M v20 v0) v0 v3) (C (T (C (C h10 h4) (S (h y v3 y))) (S (h v19 y y))) h10))) h11)) (S (h v19 x v0))) (T (C (T (T h18 (C (C h17 (T (T h16 (C (T (C (C h10 h12) h6) (S (h v15 y y))) h10)) (C (T (T (h v15 x y) (C (C (R v13) (T (S h12) h5)) h11)) (S (h v8 x y))) h10))) h10)) (S h9)) h7) h6))) (S h4)

@[equational_result]
theorem Equation3147_implies_Equation3489 (G: Type _) [Magma G] (h: Equation3147 G) : Equation3489 G := fun x y z =>
  let v0 := M y z
  let v1 := M v0 z
  have h2 := R v1
  have h3 := R z
  have h4 := R y
  let v5 := M x x
  have h6 := h y v5 y
  have h7 := h v5 x y
  have h8 := h v5 v5 v5
  have h9 := S h8
  have h10 := R v5
  have h11 := h v5 x v5
  have h12 := R v0
  have h13 := h v0 v5 v0
  have h14 := h v5 x v0
  let v15 := M y v1
  have h16 := h v5 v15 v1
  have h17 := S h16
  have h18 := R v15
  have h19 := h v15 v5 v15
  have h20 := h v5 x v15
  have h21 := C h11 h10
  have h22 := T (T h20 (C (C (T h21 h9) h18) h18)) (C (T (C h20 h18) (S h19)) h18)
  have h23 := S h11
  have h24 := C h23 h10
  have h25 := h v5 x v1
  have h26 := h v1 v5 v1
  have h27 := C (T h26 (C (T (T (T (S h25) h8) h24) (C h22 h10)) h2)) h2
  have h28 := C (T (C (T (T (C (T (T h27 h17) h11) h10) h9) h14) h12) (S h13)) h12
  have h29 := h v5 v1 v0
  have h30 := S h26
  have h31 := S h20
  have h32 := C (C (T h8 h24) h18) h18
  have h33 := C (T h19 (C h31 h18)) h18
  have h34 := C (T (T (T (C (T (T h33 h32) h31) h10) h21) h9) h25) h2
  have h35 := C (T h34 h30) h2
  T h16 (C (T (T (T h34 h30) (C (C (T h6 (C (T (T (S h7) (h v5 z y)) (C (T (C (T (T (C (T (T (T (T (T (T (C (T (h z v5 z) (C (S (h v5 x z)) h3)) h3) (C (C h22 h3) h3)) (C (C (T (T (T (T h33 h32) h31) h16) h35) h3) h3)) (C (C (T (T (T h27 h17) h29) h28) h3) h3)) (C (C (T (T (T (C (T h13 (C (T (T (S h14) h8) (C (T (T h23 h16) h35) h10)) h12)) h12) (S h29)) h8) (C (T (T h23 h29) h28) h10)) h3) h3)) (S (h v5 v0 z))) h11) h10) h9) h7) h4) (S h6)) h4)) h4)) h3) h3)) (S (h y y z))) h2)

@[equational_result]
theorem Equation4197_implies_Equation3692 (G: Type _) [Magma G] (h: Equation4197 G) : Equation3692 G := fun x y z =>
  let v0 := M y y
  let v1 := M z z
  have h2 := h v0 v1 v0
  have h3 := S h2
  have h4 := R v0
  have h5 := R v1
  have h6 := h y y y
  have h7 := C (S h6) h4
  have h8 := h y y v0
  have h9 := C (T h8 h7) h5
  have h10 := C h9 h4
  have h11 := C (T (T h10 h3) h9) h4
  have h12 := h v1 v0 v0
  have h13 := C (T (T (T h12 h11) h3) h9) h4
  have h14 := h v1 v0 v1
  have h15 := S h14
  have h16 := h z z z
  have h17 := C (S h16) h5
  have h18 := h z z v1
  have h19 := C (T h18 h17) h4
  have h20 := S h12
  have h21 := S h8
  have h22 := C h6 h4
  have h23 := C (T h22 h21) h5
  have h24 := C h23 h4
  have h25 := C (T (T h23 h2) h24) h4
  have h26 := h v1 v1 v0
  have h27 := R x
  have h28 := S h18
  have h29 := C h16 h5
  have h30 := T h29 h28
  have h31 := C (T (T (T (C h30 h4) h12) h11) h24) h5
  have h32 := C (T (T (T h10 h25) h20) h19) h5
  have h33 := h v0 v0 v1
  have h34 := C h30 h27
  have h35 := h v1 x v1
  T (T (T (T (T (h x x v1) (C (T (T (C (T (T h35 (C (T (T h34 h35) (C h34 (T (T (T (T (T (T (T (T (T (T (T h18 h17) h26) (C (T (T (T (T (T (T (C (T h2 h24) h5) h32) h15) h12) h11) h3) h9) h4)) h25) h20) h14) h31) (C (T h10 (C (T (T (T h23 h2) h25) h20) h4)) h5)) (S h33)) h22) h21))) h5)) (S (h x v0 v1))) h27) (C (T (h x v0 z) (C (T (C (h z x z) (T (T (T (T (T (T (T (T (T (T (T h8 h7) h33) (C (T h13 h24) h5)) h32) h15) h12) h11) (C (T (T (T (T (T (T h23 h2) h25) h20) h14) h31) (C (T h10 h3) h5)) h4)) (S h26)) h29) h28)) (S (h x z v1))) (R z))) h27)) (S (h z z x))) h5)) h26) (C (T (C (T (T (T h2 h25) h20) h19) h5) h15) h4)) h13) h3

@[equational_result]
theorem Equation2789_implies_Equation2113 (G: Type _) [Magma G] (h: Equation2789 G) : Equation2113 G := fun x y z =>
  let v0 := M y z
  let v1 := M y x
  let v2 := M v1 z
  let v3 := M v2 v0
  have h4 := R y
  have h5 := R v3
  have h6 := h v0 v2 v2
  have h7 := R v2
  have h8 := h v2 x v3
  have h9 := S h8
  let v10 := M x v2
  have h11 := h v3 (M (M x v3) v10) v3
  have h12 := T (C (T h11 (C (C h9 h9) h5)) h7) (S h6)
  let v13 := M x y
  have h14 := h v0 (M (M x v0) v13) v0
  have h15 := R v0
  have h16 := h y x v0
  have h17 := C (T (C (C h16 h16) h15) (S h14)) h4
  have h18 := h z y y
  have h19 := R v1
  have h20 := h v1 x v2
  have h21 := S h20
  have h22 := C (C h21 h21) h7
  let v23 := M x v1
  have h24 := h v2 (M v10 v23) v2
  have h25 := h v1 v2 v0
  have h26 := S h16
  have h27 := T (C (T h14 (C (C h26 h26) h15)) h4) (S h18)
  have h28 := R (M v1 v1)
  have h29 := h (M v0 y) v1 v1
  have h30 := T h18 h17
  have h31 := h y x v1
  T (T (T (h x y y) (C (T (C (C h31 h31) h19) (S (h v1 (M v23 v13) v1))) h4)) (C (T (T (T h25 (C (T (C h5 (T (C (T (T h24 h22) (C h28 (C h19 h30))) h19) (S h29))) (C h5 h27)) (T h6 (C (T (C (C h8 h8) h5) (S h11)) h7)))) (h (M (M v3 z) (M v3 v2)) v2 v2)) (C (T (T (T (C (R (M v2 v2)) (T (T (C h7 (T (C (T (C h5 h30) (C h5 (T h29 (C (T (T (C h28 (C h19 h27)) (C (C h20 h20) h7)) (S h24)) h19)))) h12) (S h25))) (C (T h24 h22) h19)) (S (h z v1 v1)))) (S (h z v1 z))) h18) h17) (T (h v2 v3 v3) (C (T (C (R (M v3 v3)) h12) (S (h v0 v2 v0))) h5)))) h4)) (S (h v3 v0 y))

@[equational_result]
theorem Equation4176_implies_Equation3607 (G: Type _) [Magma G] (h: Equation4176 G) : Equation3607 G := fun x y z =>
  let v0 := M y z
  let v1 := M v0 x
  let v2 := M z v1
  have h3 := R z
  have h4 := h v1 v2 y
  have h5 := R y
  have h6 := h y z v1
  have h7 := h y y z
  have h8 := h x y z
  let v9 := M x y
  have h10 := R x
  have h11 := C (S h8) h10
  have h12 := h y z v0
  have h13 := R v0
  have h14 := h z v0 x
  have h15 := h x x y
  have h16 := T (C (T h15 (C (T (C h8 h10) (S h14)) h5)) h13) (S h12)
  have h17 := h v0 x y
  have h18 := h y v9 v0
  let v19 := M x v1
  have h20 := R v1
  have h21 := h v0 x z
  have h22 := C (S h21) (R v2)
  let v23 := M (M x z) v0
  have h24 := h v2 v23 z
  have h25 := h v23 z v1
  T (T (T (T h8 (C (T (T (T h21 h25) (C (T (T (T (T (T h24 (C h22 h3)) (C (T (h v1 v2 v1) (C (S (h v1 z v1)) h20)) h3)) (S (h v1 v1 z))) (C h21 h20)) (C (T h25 (C (T (T h24 (C (T (T h22 h4) (C (S h6) h5)) h3)) (S h7)) h20)) h20)) h20)) (S (h v1 (M y y) v1))) h3)) (C (C (T (T (T (T (T (T (h v0 x x) (h (M (M x x) v0) x x)) (C (T (C (T (T (T (T (T (h x x v0) (C (T (C (h x v0 x) h10) (S (h x v1 x))) (T h12 (C (T (C (T h14 h11) h5) (S h15)) h13)))) (C (R v19) h16)) (h v19 v0 x)) (C (T (T (T (h v1 v19 v0) (C (S (h v0 x v1)) h13)) (C h17 h13)) (S h18)) h10)) (C (T h18 (C (S h17) h13)) h10)) h16) (S (h x v1 v0))) h10)) (C (T (h x v1 z) (C h11 h3)) h10)) (S (h z v9 x))) (h z v9 z)) (C (T (C (C h8 h3) h3) (S (h z v1 z))) h3)) (T h7 (C (T (C h6 h5) (S h4)) h3))) h3)) (S (h (M (M v1 v2) z) v2 z))) (S (h z v1 v2))

@[equational_result]
theorem Equation2522_implies_Equation26 (G: Type _) [Magma G] (h: Equation2522 G) : Equation26 G := fun x y =>
  let v0 := M x y
  let v1 := M v0 y
  have h2 := h v1 y v1
  have h3 := S h2
  have h4 := R y
  have h5 := h x v1 y
  have h6 := C h4 h5
  have h7 := R x
  have h8 := h y x v1
  have h9 := S h8
  have h10 := R v1
  let v11 := M y v1
  have h12 := h v11 v1 y
  have h13 := h x y y
  have h14 := C h13 h4
  have h15 := h (M v1 v0) x v1
  have h16 := h v0 x x
  have h17 := S h16
  have h18 := h (M x (M (M v0 x) x)) x x
  have h19 := h v0 x y
  have h20 := h (M x (M v1 y)) x x
  have h21 := h (M y x) x y
  have h22 := C h9 h7
  have h23 := S h5
  have h24 := T (T (T h16 (C (T (T (T h18 (C (C h7 (T (C h17 h7) (C h19 h7))) h7)) (S h20)) (C h7 (C (T h2 (C (C h4 h23) h4)) h4))) h7)) (S h21)) (C h8 h7)
  have h25 := h y x y
  let v26 := M x (M v11 v1)
  have h27 := h v1 x v1
  have h28 := C (S h13) h4
  have h29 := h v11 x y
  T (T h13 (C (T (T h29 (C (T (T (T (T (T (T (C h7 h28) (h (M x v0) v0 x)) (C (C (R v0) (T (T (C (T (C (C h7 h14) h7) (S h29)) h7) (C (T (T (T (T (T (C h4 (T h27 (C (C h7 h23) h7))) (C (T (T (T h8 (C (C h7 (C (T h12 (C (C h10 h28) h10)) h10)) h7)) (S h15)) (C h10 h24)) (T (C (C h7 h5) h7) (S h27)))) (S (h v26 v1 x))) (h v26 x x)) (C (C h7 (T h22 (C h25 h7))) h7)) (S (h (M x (M (M y y) y)) x x))) h7)) (S h25))) h24)) (C h10 (T (T (T h22 h21) (C (T (T (T (C h7 (C (T (C h6 h4) h3) h4)) h20) (C (C h7 (T (C (S h19) h7) (C h16 h7))) h7)) (S h18)) h7)) h17))) h15) (C (C h7 (C (T (C (C h10 h14) h10) (S h12)) h10)) h7)) h9) h7)) h6) h4)) h3

@[equational_result]
theorem Equation2725_implies_Equation31 (G: Type _) [Magma G] (h: Equation2725 G) : Equation31 G := fun x y =>
  let v0 := M y y
  let v1 := M v0 x
  have h2 := h v1 v1 v1
  have h3 := S h2
  have h4 := R v1
  let v5 := M v1 v1
  have h6 := h v5 v1 x
  have h7 := S h6
  have h8 := h (M x x) v1 y
  have h9 := h x v0 x
  have h10 := h x v0 y
  have h11 := S h10
  have h12 := h v0 v1 y
  have h13 := T (T h12 (C (T h11 h9) h4)) (S h8)
  have h14 := R (M v1 v5)
  have h15 := h x v0 v1
  have h16 := C (T (T h11 h15) (C h14 h13)) h4
  have h17 := T (T h12 h16) h7
  have h18 := C h17 h17
  have h19 := h (M v0 v0) v1 y
  have h20 := S h19
  have h21 := h x v0 v0
  have h22 := C (T h11 h21) h4
  have h23 := T (T (T h12 h22) h20) h18
  have h24 := C h23 h4
  let v25 := M v0 v1
  have h26 := S h12
  have h27 := C (T (S h9) h10) h4
  have h28 := T (T h8 h27) h26
  have h29 := C (T (S h21) h10) h4
  have h30 := C (T (T (C h14 h28) (S h15)) h10) h4
  have h31 := T (T h6 h30) h26
  have h32 := C h31 h31
  have h33 := T (T (T (T h32 h19) h29) h16) h7
  have h34 := C (T (T (T h32 h19) h29) h26) h4
  let v35 := M v5 v5
  have h36 := R (M v0 v35)
  have h37 := C h31 (T (T (T (T h6 h30) h22) h20) h18)
  have h38 := R (M v1 v35)
  T (T (T (T (T (T (T h10 (C (C h4 h23) h17)) (C h38 h31)) (C h38 h13)) (C (C (T (T (T h2 h34) (h v25 v1 x)) (C (T (T (T (T (T (T (C (R (M v1 v25)) (T (T (T h8 h27) h16) h7)) (C (T (T (T (T (T (T (T (T (T (C h4 (T h24 h3)) h6) h30) h22) h20) h18) h37) (C (T (T (T (T h12 h22) h20) h18) h37) h33)) (C h36 h31)) (C h36 h13)) h31)) (S (h v35 v0 x))) h32) h19) h29) h26) (T h2 h34))) h33) h28)) (S (h v25 v0 v1))) h24) h3

@[equational_result]
theorem Equation3131_implies_Equation1670 (G: Type _) [Magma G] (h: Equation3131 G) : Equation1670 G := fun x y z =>
  let v0 := M z y
  let v1 := M v0 z
  let v2 := M x y
  let v3 := M v2 v1
  have h4 := R v2
  have h5 := R v3
  have h6 := h v2 v1 v1
  have h7 := R v1
  have h8 := h v1 v0 v0
  have h9 := S h8
  have h10 := R v0
  have h11 := h v0 v1 v0
  have h12 := S h11
  have h13 := h z v0 v0
  have h14 := h z y v1
  have h15 := R y
  have h16 := R z
  have h17 := h y z z
  have h18 := S h17
  have h19 := h z v1 z
  have h20 := S h13
  have h21 := C (C (T (C (T (T (C (T h11 (C (T (T h20 h19) (C (C h18 h16) h7)) h7)) h15) (S h14)) h13) h7) h12) h7) h10
  have h22 := h y v0 v1
  have h23 := h z v0 z
  have h24 := h z v0 v3
  have h25 := h v1 v2 v2
  have h26 := h v2 v3 v2
  have h27 := T h26 (C (S h25) h5)
  have h28 := C (T (C (T (T (T (T (C (C h27 h5) h10) (S h24)) h23) (C h18 h10)) (C (T h22 h21) h10)) h10) h9) h4
  have h29 := h v3 v2 v0
  have h30 := C (T h29 h28) h7
  have h31 := T (C h25 h5) (S h26)
  have h32 := h v3 v1 v1
  have h33 := S h29
  have h34 := C (T h8 (C (T (T (T (T (C (T (C (C (T h11 (C (T (T h20 h14) (C (T (C (T (T (C (C h17 h16) h7) (S h19)) h13) h7) h12) h15)) h7)) h7) h10) (S h22)) h10) (C h17 h10)) (S h23)) h24) (C (C h31 h5) h10)) h10)) h4
  have h35 := C (T h34 h33) h7
  T (T (h x v2 v0) (C (T (T (T (C (C (T (T (T (C (T (T h6 (C (T (T (T (T (C h35 h7) (C (C (C h27 h7) h7) h7)) (S h32)) h29) h28) h7)) h35) (R x)) (S (h y x v1))) h22) h21) h10) h10) h9) (h v1 v3 v3)) (C (C (C (T (T h30 (C (T (T (T (T h34 h33) h32) (C (C (C h31 h7) h7) h7)) (C h30 h7)) h7)) (S h6)) h5) h5) h5)) h4)) (S (h v3 v2 v3))

@[equational_result]
theorem Equation3131_implies_Equation3211 (G: Type _) [Magma G] (h: Equation3131 G) : Equation3211 G := fun x y z =>
  let v0 := M y z
  let v1 := M v0 z
  let v2 := M v1 x
  let v3 := M v2 y
  have h4 := S (h v3 v2 v2)
  have h5 := R v2
  have h6 := R v3
  have h7 := h v2 v3 v2
  have h8 := S h7
  have h9 := h y v2 v2
  have h10 := h y z v1
  have h11 := S h10
  have h12 := R z
  have h13 := R v1
  have h14 := R y
  have h15 := h z y z
  have h16 := h z v1 y
  have h17 := C (C (T h16 (C (C (S h15) h14) h13)) h13) h12
  have h18 := h z v0 v0
  have h19 := h v0 v1 v0
  have h20 := C (T h19 (C (S h18) h13)) h12
  have h21 := h v1 x v3
  have h22 := S h21
  have h23 := R x
  have h24 := h x v1 y
  have h25 := C (C (S h24) h13) h6
  have h26 := h y v3 v1
  have h27 := C (T (T (T (T (T (C (T h7 (C (T (T (S h9) h26) h25) h6)) h23) h22) h20) h17) h11) h9) h6
  have h28 := h x v2 v3
  have h29 := T (T h10 (C (C (T (C (C h15 h14) h13) (S h16)) h13) h12)) (C (T (C h18 h13) (S h19)) h12)
  have h30 := R (M v2 v1)
  have h31 := T (T h20 h17) h11
  have h32 := C (C (T (C (C (T h26 h25) h6) h23) h22) h23) h29
  have h33 := h v3 y x
  have h34 := C (T (T (T (T (C (C (T h33 h32) h31) h31) (C (C h30 h29) h29)) (S (h x v1 v1))) h28) (C (C (T h27 h8) h6) h5)) h5
  have h35 := h y v2 v1
  T (T h28 (C (T (T (T (T (T (T (C (T (T (T h27 h8) (h v2 v1 v1)) (C (T (T (C (C (T (T (T (C (T (T (T (T h20 h17) h11) h35) h34) h5) h4) h33) h32) h13) h13) (C (C h30 h31) h31)) (C (C (T (C (C (T h21 (C (C (T (C (C h24 h13) h6) (S h26)) h6) h23)) h23) h31) (S h33)) h29) h29)) h13)) h6) (S (h v1 v3 v1))) h20) h17) h11) h35) h34) h5)) h4

@[equational_result]
theorem Equation522_implies_Equation572 (G: Type _) [Magma G] (h: Equation522 G) : Equation572 G := fun x y z =>
  let v0 := M x y
  let v1 := M z v0
  let v2 := M z v1
  let v3 := M y v2
  have h4 := R v3
  have h5 := h y v0 v0
  have h6 := h x v0 y
  have h7 := R v0
  have h8 := R x
  have h9 := C h8 (T (C h7 h6) (S h5))
  have h10 := R z
  have h11 := C h10 (C h10 h9)
  have h12 := h v0 z x
  have h13 := T h12 h11
  have h14 := h v0 v0 z
  have h15 := h z v0 v0
  have h16 := S h15
  have h17 := h v0 v1 v1
  have h18 := S h17
  have h19 := h z v1 v0
  have h20 := R v1
  have h21 := C h20 h19
  have h22 := C h10 (T h21 h18)
  have h23 := S h12
  have h24 := C h8 (T h5 (C h7 (S h6)))
  have h25 := C h10 (C h10 h24)
  have h26 := T h25 h23
  have h27 := C h26 h22
  have h28 := h v1 v2 z
  have h29 := C h26 (T (T h22 h28) (C h26 h27))
  have h30 := C h10 (T h28 (C h26 (T h29 h16)))
  have h31 := R y
  have h32 := S h28
  have h33 := C h20 (S h19)
  have h34 := C h10 (T h17 h33)
  have h35 := C h13 h34
  have h36 := C h13 (T (T (C h13 h35) h32) h34)
  have h37 := C h10 (T (C h13 (T h15 h36)) h32)
  have h38 := h v0 v0 x
  T (T (h x v3 y) (C h4 (C h4 (T (T (T (T (C h31 (T (T h12 h11) h30)) (C h31 (T (T (T (T (T h37 h25) h23) h17) h33) (C h20 (T (T h15 h36) h27))))) (C h31 (T (T (T (T (C h20 (T (T h35 h29) h16)) h21) h18) h38) (C h7 (C h7 h9))))) (C h31 (T (T (T (C h7 (C h7 h24)) (S h38)) h14) (C h13 (C h7 h37))))) (C h31 (T (T (T (C h26 (C h7 h30)) (S h14)) (h v0 v3 v3)) (C h4 (T (C h4 (C h4 (C h13 h4))) (S (h y v3 v2)))))))))) (S (h v3 v3 y))

@[equational_result]
theorem Equation572_implies_Equation492 (G: Type _) [Magma G] (h: Equation572 G) : Equation492 G := fun x y z =>
  let v0 := M z y
  let v1 := M z v0
  let v2 := M x v1
  let v3 := M y v2
  have h4 := S (h v3 v2 v2)
  have h5 := h v2 v3 v2
  have h6 := S h5
  have h7 := h y v2 v2
  have h8 := h y z v1
  have h9 := S h8
  have h10 := h z y z
  have h11 := R y
  have h12 := R v1
  have h13 := h z v1 y
  have h14 := R z
  have h15 := C h14 (C h12 (T h13 (C h12 (C h11 (S h10)))))
  have h16 := h z v0 v0
  have h17 := h v0 v1 v0
  have h18 := C h14 (T h17 (C h12 (S h16)))
  have h19 := h v1 x v3
  have h20 := S h19
  have h21 := h x v1 y
  have h22 := R v3
  have h23 := C h22 (C h12 (S h21))
  have h24 := h y v3 v1
  have h25 := R x
  have h26 := C h22 (T (T (T (T (T (C h25 (T h5 (C h22 (T (T (S h7) h24) h23)))) h20) h18) h15) h9) h7)
  have h27 := R v2
  have h28 := h x v2 v3
  have h29 := R (M v1 v2)
  have h30 := T (T h8 (C h14 (C h12 (T (C h12 (C h11 h10)) (S h13))))) (C h14 (T (C h12 h16) (S h17)))
  have h31 := C h30 (C h25 (T (C h25 (C h22 (T h24 h23))) h20))
  have h32 := h v3 y x
  have h33 := T (T h18 h15) h9
  have h34 := C h27 (T (T (T (T (C h33 (C h33 (T h32 h31))) (C h30 (C h30 h29))) (S (h x v1 v1))) h28) (C h27 (C h22 (T h26 h6))))
  have h35 := h y v2 v1
  T (T h28 (C h27 (T (T (T (T (T (T (C h22 (T (T (T h26 h6) (h v2 v1 v1)) (C h12 (T (T (C h12 (C h12 (T (T (T (C h27 (T (T (T (T h18 h15) h9) h35) h34)) h4) h32) h31))) (C h33 (C h33 h29))) (C h30 (C h30 (T (C h33 (C h25 (T h19 (C h25 (C h22 (T (C h22 (C h12 h21)) (S h24))))))) (S h32)))))))) (S (h v1 v3 v1))) h18) h15) h9) h35) h34))) h4

@[equational_result]
theorem Equation1181_implies_Equation2958 (G: Type _) [Magma G] (h: Equation1181 G) : Equation2958 G := fun x y z =>
  let v0 := M y z
  let v1 := M y v0
  let v2 := M v1 x
  let v3 := M v2 z
  have h4 := h v3 x x
  have h5 := R x
  have h6 := R v3
  have h7 := h z v2 x
  have h8 := R v2
  let v9 := M (M x (M x z)) v2
  have h10 := h v1 z v1
  have h11 := R z
  have h12 := h z v1 y
  have h13 := T (C h11 (C h12 h11)) (S h10)
  have h14 := C h13 h5
  have h15 := h x x v0
  have h16 := S h15
  have h17 := h (M (M v0 (M v0 x)) x) x x
  have h18 := h x x x
  have h19 := h (M (M x (M x x)) x) x x
  have h20 := h x v1 v2
  have h21 := S h20
  have h22 := h (M (M v2 (M v2 x)) v1) v1 v1
  have h23 := R v1
  have h24 := T h10 (C h11 (C (S h12) h11))
  let v25 := M v2 v1
  have h26 := h v25 x v1
  have h27 := h v1 v2 v2
  let v28 := M (M v2 v25) v2
  have h29 := h v28 x v2
  T (T (T (T (T h15 (C h5 (T (T (T h17 (C h5 (C (T (C h5 h16) (C h5 h18)) h5))) (S h19)) (C (T (T (C h5 (C (T h20 (C h23 (T h22 (C h23 (C (T (C h24 h21) h14) h23))))) h5)) (S h26)) (C h8 h27)) h5)))) (S h29)) (h v28 x v1)) (C h5 (T (T (T (C (T (T (T (T (T (C h23 (T (C h24 (T (T h29 (C h5 (T (T (T (C (T (T (C h8 (S h27)) h26) (C h5 (C (T (C h23 (T (C h23 (C (T (C h24 h5) (C h13 h20)) h23)) (S h22))) h21) h5))) h5) h19) (C h5 (C (T (C h5 (S h18)) (C h5 h15)) h5))) (S h17)))) h16)) h14)) (h (M v1 v2) x v2)) (C h5 (T (C (C h8 (S (h z v2 y))) h5) (C (C h8 h7) h5)))) (S (h v9 x v2))) (h v9 v3 v2)) (C h6 (C (C h8 (S h7)) h6))) h5) (h (M (M v3 (M v3 v3)) x) x x)) (C h5 (C (T (C h5 (S (h v3 x v3))) (C h5 h4)) h5))) (S (h (M (M x (M x v3)) x) x x))))) (S h4)

