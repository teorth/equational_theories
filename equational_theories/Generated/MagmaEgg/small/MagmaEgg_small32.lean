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
theorem Equation3211_implies_Equation1793 (G: Type _) [Magma G] (h: Equation3211 G) : Equation1793 G := fun x y z =>
  let v0 := M z y
  let v1 := M v0 x
  let v2 := M y z
  let v3 := M v2 v1
  have h4 := S (h v3 v0 v1)
  have h5 := R v0
  have h6 := R v3
  have h7 := R v1
  have h8 := h v0 v1 v3
  have h9 := S h8
  have h10 := h v1 v2 v1
  have h11 := C (S h10) h6
  have h12 := h v2 v3 v1
  have h13 := h v2 v2 y
  have h14 := R v2
  have h15 := R y
  have h16 := h v2 z v2
  have h17 := R z
  have h18 := h z y z
  have h19 := h y v2 z
  have h20 := h z y v2
  have h21 := h v3 v0 v2
  have h22 := C (T h21 (C (C (T (T (T (C (C (C (T h20 (C (T (C (C (C (T h19 (C (S h18) h14)) h14) h14) h17) (S h16)) h15)) h15) h14) h14) (S h13)) h12) h11) h6) h5)) h7
  have h23 := C (C (C (T h22 h9) h7) h7) h6
  have h24 := h v1 v3 v1
  have h25 := S (h v1 v3 v0)
  have h26 := C (T (T (T h22 h9) (h v0 v1 v0)) (C (C (C (T (C (T h24 h23) h5) h4) h5) h5) h7)) h6
  have h27 := h v3 v2 v1
  have h28 := S h21
  have h29 := C (C (T (T (T (C h10 h6) (S h12)) h13) (C (C (C (T (C (T h16 (C (C (C (T (C h18 h14) (S h19)) h14) h14) h17)) h15) (S h20)) h15) h14) h14)) h6) h5
  T (T (h x v0 v0) (C (T (T (C (T (C (C (T h8 (C (T h29 h28) h7)) h5) (T (T h8 (C (T (T (T h29 h28) h27) (C (T (T (T h26 h25) (h v1 v2 v3)) (C (T (T (T (C (C (C (T h12 h11) h6) h6) h7) (S (h v3 v1 v3))) h27) (C (T h26 h25) h14)) h14)) h14)) h7)) (S (h v2 v1 v2)))) (S (h v0 v2 v1))) (R x)) h24) h23) h5)) h4

@[equational_result]
theorem Equation489_implies_Equation2373 (G: Type _) [Magma G] (h: Equation489 G) : Equation2373 G := fun x y z =>
  let v0 := M x z
  let v1 := M z v0
  let v2 := M y v1
  have h3 := h y v1 v2
  have h4 := S h3
  have h5 := h v2 y v1
  let v6 := M v0 v2
  have h7 := h v2 v6 y
  let v8 := M y y
  have h9 := h y y v8
  have h10 := h v8 y y
  have h11 := R y
  have h12 := R v6
  have h13 := h v6 y y
  have h14 := R v2
  let v15 := M v2 y
  have h16 := h v2 v15 v2
  have h17 := h v2 y v15
  have h18 := h v15 v2 y
  have h19 := h v15 y v1
  have h20 := R v1
  have h21 := R v15
  have h22 := h y v15 y
  have h23 := R v0
  have h24 := h v0 v2 v15
  let v25 := M v0 y
  have h26 := h v0 y v25
  have h27 := h v25 v0 y
  have h28 := C h11 (S h27)
  T (T (T (h x z v0) (C (R z) (S (h v0 x z)))) (h v1 v2 v0)) (C h14 (T (C h20 (T (T (T (T (T (C h23 (C (T h7 (C h12 (T (T (T (C h14 (T (T (C h11 (C h12 (T h9 (C h11 (S h10))))) (S h13)) (C h23 (T h16 (C h21 (C h14 (C h14 (T (C h21 (T h17 (C h11 (T (T (S h18) h19) (C h11 (C h21 (T (C h20 h5) h4))))))) (S h22))))))))) (S h24)) h26) h28))) (T h26 h28))) (S (h (M v6 (M y v25)) v0 y))) (C h12 (T (C h11 h27) (S h26)))) (C h12 (T (T h24 (C h14 (C h23 (T (C h21 (C h14 (C h14 (T h22 (C h21 (T (C h11 (T (T (C h11 (C h21 (T h3 (C h20 (S h5))))) (S h19)) h18)) (S h17))))))) (S h16))))) (C h14 (T h13 (C h11 (C h12 (T (C h11 h10) (S h9))))))))) (S h7)) h5)) h4))

@[equational_result]
theorem Equation3385_implies_Equation4216 (G: Type _) [Magma G] (h: Equation3385 G) : Equation4216 G := fun x y z =>
  let v0 := M x y
  let v1 := M z y
  let v2 := M v1 z
  have h3 := S (h v2 x v0)
  let v4 := M v2 x
  let v5 := M y x
  have h6 := R v4
  have h7 := S (h y x v1)
  have h8 := h v1 z z
  have h9 := S h8
  have h10 := h z (M v1 (M z z)) v4
  have h11 := S h10
  have h12 := h z z y
  have h13 := R v1
  have h14 := h y z v1
  have h15 := R z
  have h16 := C h6 (C h15 (C (T h14 (C h13 (S h12))) h6))
  let v17 := M y z
  have h18 := h z v17 v4
  have h19 := R x
  have h20 := R v2
  have h21 := C h13 (T (T (T (T (h z x v2) (C h20 (S (h x v1 z)))) (C h20 (C h19 (T (T (T (h z y z) (h z (M z v17) v4)) (C h6 (C h15 (C (T (T (T h18 h16) h11) h9) h6)))) (S (h z v2 v4)))))) (S (h x z v2))) (h x z y))
  have h22 := h x (M v1 (M z x)) v4
  have h23 := h v1 z x
  have h24 := C (R v0) (T (T (S (h x x y)) (h x x v2)) (C h20 (C h19 (T (T (T (h x v2 v4) (C h6 (C h19 (T (C (T (T (T h8 h10) (C h6 (C h15 (C (T (C h13 h12) (S h14)) h6)))) (S h18)) h6) (C (T (T (T (T (T (T (T h18 h16) h11) h9) h23) h22) (C h6 (C h19 (C (T h21 h7) h6)))) (S (h x v5 v4))) h6))))) (S (h x (M x v5) v4))) (S (h x y x))))))
  have h25 := h y x v0
  T (T (T (T (T (h x y v4) (C h6 (T (S (h y v2 x)) (C (R y) (T (T (T h23 h22) (C h6 (C h19 (C (T (T (T (T h21 h7) h25) h24) h3) h6)))) (S (h x v4 v4))))))) (S (h y x v4))) h25) h24) h3

@[equational_result]
theorem Equation492_implies_Equation2925 (G: Type _) [Magma G] (h: Equation492 G) : Equation2925 G := fun x y z =>
  let v0 := M x z
  let v1 := M y v0
  let v2 := M v1 y
  let v3 := M v2 z
  have h4 := S (h z x v3)
  have h5 := h y v0 y
  have h6 := S h5
  have h7 := R v1
  have h8 := C h7 h6
  have h9 := h v0 v1 y
  have h10 := T h9 h8
  have h11 := R x
  have h12 := C h11 (C h11 h10)
  have h13 := R z
  have h14 := T (C h7 h5) (S h9)
  have h15 := R v0
  have h16 := h z v3 v0
  have h17 := R v3
  have h18 := h v0 z v2
  have h19 := h v3 v0 v3
  have h20 := C h13 (T (T (T (T (C h14 (R (M v3 (M v3 z)))) (C h15 (C h17 (C h17 (T h16 (C h17 (T (C h13 (C h15 (C h10 h17))) (S h18)))))))) (S h19)) (h v3 v3 z)) (C h17 (C h17 (T (T (C h13 (T (C h13 (T h19 (C h15 (C h17 (C h17 (T (C h17 (T h18 (C h13 (C h15 (C h14 h17))))) (S h16))))))) (S (h v0 z v3)))) (C h13 (T (h v0 x v2) (C h11 (C h15 (C h14 (T (C (R v2) (T (h x z x) (C h13 h12))) (S (h z v2 x))))))))) (S (h x z v0))))))
  have h21 := h v2 z v3
  have h22 := S (h v0 y v1)
  have h23 := C h15 (T (C h7 h12) (C h7 (T (T (C h11 (T (C h11 (T h21 h20)) h4)) h9) h8)))
  have h24 := h v1 v0 x
  have h25 := R y
  T (h x v0 v0) (C h10 (T (C h11 (T (T (T (C h10 (C h10 (T h9 (C h7 (T (T h6 (h y v1 y)) (C h7 (T (T (T (C h25 (T (T (C h25 (T (C h25 (T h24 h23)) h22)) h24) h23)) h22) h9) h8))))))) (S (h v2 v2 v1))) h21) h20)) h4))

@[equational_result]
theorem Equation3591_implies_Equation3820 (G: Type _) [Magma G] (h: Equation3591 G) : Equation3820 G := fun x y z =>
  let v0 := M x y
  let v1 := M z z
  let v2 := M v1 v0
  have h3 := h v1 v0 v2
  have h4 := S h3
  let v5 := M v1 v2
  let v6 := M v5 v0
  let v7 := M v2 v0
  have h8 := h v5 v0 v0
  have h9 := h v0 (M v6 v0) v2
  have h10 := h x y v2
  have h11 := S h10
  let v12 := M (M x v2) y
  have h13 := R v12
  have h14 := R v6
  have h15 := C h14 (T (C h4 h13) h11)
  have h16 := h v2 v12 v6
  have h17 := T (T h10 h16) h15
  have h18 := R (M v0 v2)
  have h19 := R v2
  have h20 := h v0 v0 v2
  have h21 := R v0
  have h22 := T (T (C h14 (T h10 (C h3 h13))) (S h16)) h11
  have h23 := h x y z
  have h24 := S h23
  let v25 := M (M x z) y
  have h26 := h z v25 v2
  have h27 := R v25
  have h28 := h z v0 z
  have h29 := h v1 v0 v0
  have h30 := R v7
  have h31 := h v0 (M (M z v0) v25) v7
  have h32 := h z v25 v0
  have h33 := C (T (T (T h23 h32) h31) (C h30 (T (T (C (S h29) (C h28 h27)) (S h26)) h24))) (T (T (T (T (C h22 h21) h20) (C h19 (C h18 h17))) (S h9)) (S h8))
  have h34 := h v6 v0 v0
  T (T (T (T (T (T (T h10 h16) h15) h34) h33) (C (T (T (T (C h30 (T (T h23 h26) (C h29 (C (S h28) h27)))) (S h31)) (S h32)) h24) (T (T (T (T (T (T h8 h9) (C h19 (C h18 h22))) (S h20)) (C h17 h21)) (C h22 (T (T (T (T h10 h16) h15) h34) h33))) (S (h v7 v6 v0))))) (S (h v2 v6 v0))) h4

@[equational_result]
theorem Equation1304_implies_Equation4640 (G: Type _) [Magma G] (h: Equation1304 G) : Equation4640 G := fun x y z =>
  let v0 := M (M y z) z
  let v1 := M (M (M v0 x) x) v0
  have h2 := h v0 x v1
  have h3 := R x
  have h4 := R v1
  have h5 := h v0 v0 x
  have h6 := h y x z
  let v7 := M v0 y
  let v8 := M v7 y
  let v9 := M x y
  have h10 := R v9
  have h11 := h y y z
  have h12 := R v7
  have h13 := h y y x
  have h14 := S h13
  let v15 := M (M (M y x) x) y
  have h16 := R v15
  have h17 := C h12 (T (C (T (C h14 h16) h14) h12) (S h11))
  have h18 := h y v7 v15
  have h19 := S h6
  have h20 := S h5
  have h21 := C h3 (C (T (C h20 h4) h20) h3)
  have h22 := R z
  have h23 := C (T (T (T (T (T (C (C (T (C h12 (T h11 (C (T h13 (C h13 h16)) h12))) (S h18)) h22) h22) h2) h21) h19) h18) h17) (R v0)
  have h24 := h v8 v0 z
  have h25 := R y
  have h26 := h x x x
  have h27 := S h26
  let v28 := M (M (M x x) x) x
  have h29 := R v28
  let v30 := M v9 x
  let v31 := M (M v30 x) x
  have h32 := R v31
  T (T (T (T (T (h v30 v9 x) (C h10 (T (T (T (T (C h32 (T (h v9 x x) (C (T h26 (C h26 h29)) h32))) (S (h x v31 v28))) (h x y v28)) (C h25 (C (T (C h27 h29) h27) h25))) (C (T (T (T h18 h17) h24) (C (T (T (T (T (T (T h2 h21) h19) h18) h17) h24) (C (T (T h2 h21) h19) h23)) h23)) h10)))) (S (h y v9 (M v8 v0)))) h6) (C h3 (C (T h5 (C h5 h4)) h3))) (S h2)

@[equational_result]
theorem Equation2105_implies_Equation3161 (G: Type _) [Magma G] (h: Equation2105 G) : Equation3161 G := fun x y z =>
  let v0 := M y y
  let v1 := M v0 z
  let v2 := M v1 x
  let v3 := M v2 z
  have h4 := R v0
  have h5 := R v3
  have h6 := h v0 y x
  have h7 := S h6
  have h8 := R (M x x)
  have h9 := R y
  have h10 := h y y y
  have h11 := S h10
  have h12 := C h11 h4
  have h13 := h y v0 y
  let v14 := M v3 v3
  have h15 := R z
  have h16 := R x
  have h17 := h v1 v0 y
  have h18 := S h17
  have h19 := R v1
  have h20 := h y v0 v1
  let v21 := M v1 v1
  have h22 := R v21
  have h23 := h v21 y x
  have h24 := C (C (T (T h23 (C (C (T (T (T (C h10 h22) (S h20)) h13) h12) h9) h8)) h7) h19) h4
  have h25 := h v1 v1 y
  have h26 := T h25 h24
  have h27 := h z v0 y
  have h28 := S h27
  have h29 := S h25
  have h30 := C (C (T (T h6 (C (C (T (T (T (C h10 h4) (S h13)) h20) (C h11 h22)) h9) h8)) (S h23)) h19) h4
  have h31 := C (T (T (T h30 h29) h17) (C (T h30 h29) h4)) h4
  have h32 := R v2
  T (T (h x v1 z) (C (T (T (T (T (C h32 h26) (C h32 (T (T (T (T h30 h29) h17) h31) h28))) (C (C (T (T h17 h31) h28) h16) h15)) (h (M (M z x) z) v3 y)) (C (C (T (T (T (C h5 (C (C (T (T h27 (C (T (T (T (C h26 h4) h18) h25) h24) h4)) h18) h16) h15)) (h v14 y x)) (C (C (T (T (T (C h10 (R v14)) (S (h y v0 v3))) h13) h12) h9) h8)) h7) h5) h4)) (R (M z z)))) (S (h v3 v0 z))

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
theorem Equation3211_implies_Equation522 (G: Type _) [Magma G] (h: Equation3211 G) : Equation522 G := fun x y z =>
  let v0 := M x z
  let v1 := M z v0
  let v2 := M y v1
  let v3 := M y v2
  have h4 := S (h v3 z v0)
  have h5 := R z
  have h6 := R v3
  have h7 := R v0
  have h8 := h v1 y y
  have h9 := R y
  have h10 := R v1
  have h11 := h y v2 v3
  have h12 := R v2
  have h13 := h v2 y v2
  have h14 := C (S h13) h6
  have h15 := h y v3 v2
  have h16 := h y v1 v2
  have h17 := h v1 y v1
  have h18 := h y v2 v1
  have h19 := h v3 v2 v3
  have h20 := h v2 y v3
  have h21 := h v3 y v1
  have h22 := h y y v2
  have h23 := S h20
  have h24 := S h15
  have h25 := C h13 h6
  have h26 := C (C (C (T h25 h24) h6) h6) h12
  have h27 := C (T h19 h26) h9
  have h28 := C (C (T (C (T (T h27 h23) (C (T h22 (C (C (T (C (T h21 (C (C (T (T (T (C (T h20 (C (T (T (C (C (C (T h15 h14) h6) h6) h12) (S h19)) (C (T h18 (C (S h17) h12)) h12)) h9)) h10) (S h16)) h15) h14) h6) h9)) h12) (S h11)) h9) h9)) h10)) h9) (S h8)) h7) h6
  have h29 := h v0 v3 y
  have h30 := R x
  T (T (h x z v0) (C (T (T (T (C (C (T h8 (C (T (T (C (T (C (C (T h11 (C (T (C (C (T (T (T h25 h24) h16) (C (T (C (T (T (C (T (C h17 h12) (S h18)) h12) h19) h26) h9) h23) h10)) h6) h9) (S h21)) h12)) h9) h9) (S h22)) h10) (h v2 y x)) (C (T (C (C (C (T (h y x z) (C (T (T (C (T (C (T h29 h28) h5) h4) h9) h27) h23) h30)) h30) h30) h12) (S (h x v2 x))) h9)) h9)) h7) h30) (S (h v0 x y))) h29) h28) h5)) h4

@[equational_result]
theorem Equation492_implies_Equation522 (G: Type _) [Magma G] (h: Equation492 G) : Equation522 G := fun x y z =>
  let v0 := M x z
  let v1 := M z v0
  let v2 := M y v1
  let v3 := M y v2
  have h4 := h v3 z v0
  have h5 := h z v0 v3
  have h6 := h v0 v3 v1
  have h7 := h v1 v1 y
  have h8 := R v0
  have h9 := h v1 z v1
  have h10 := h z v0 z
  have h11 := R v1
  have h12 := h v0 v1 z
  have h13 := R z
  have h14 := C h8 (T (C h13 (C h11 (C h11 (T h12 (C h11 (S h10)))))) (S h9))
  have h15 := h z v0 v1
  have h16 := R v3
  have h17 := h v3 z v3
  have h18 := C h8 (C h8 (T (C h8 (T h17 (C h13 (C h16 (C h16 (T (C h16 (T (T h15 h14) (C h8 h7))) (S h6))))))) (S h5)))
  have h19 := h v0 v3 v0
  have h20 := S h7
  have h21 := C h8 (T (C h13 (C h16 (C h16 (T h6 (C h16 (T (T (C h8 h20) (C h8 (T h9 (C h13 (C h11 (C h11 (T (C h11 h10) (S h12)))))))) (S h15))))))) (S h17))
  have h22 := S (h z v1 v1)
  have h23 := T h4 (C h13 (T (C h16 (C h8 (C h8 (T h5 h21)))) (S h19)))
  have h24 := C h11 (C h13 (T (h v1 v3 v1) (C h23 (C h11 h20))))
  have h25 := h v1 v0 z
  have h26 := R x
  have h27 := R y
  T (T (T (T (h x v2 y) (C (R v2) (T (T (C h26 (T (C h27 h23) (C h27 (C h13 (T (h v0 z x) (C h13 (T (C h8 (C h26 (T (h v0 v0 z) (C h8 (C h8 (T (C h13 (T h25 (C h8 (T (T (T (T (T h24 h22) h15) h14) (C h8 (T h25 (C h8 (T (T (T h24 h22) h5) h21))))) h18)))) (S (h v0 z v0)))))))) (S (h x v0 v0))))))))) (S (h y x z))) (h y v1 y)))) (S (h v1 v2 y))) (C h13 (T h19 (C h16 h18)))) (S h4)

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
theorem Equation3940_implies_Equation3534 (G: Type _) [Magma G] (h: Equation3940 G) : Equation3534 G := fun x y z =>
  let v0 := M z y
  let v1 := M v0 z
  have h2 := h x v1 v0
  let v3 := M v0 v0
  let v4 := M x (M v0 v1)
  have h5 := R v3
  have h6 := R v0
  have h7 := h z y v1
  have h8 := S h7
  let v9 := M z (M v1 y)
  have h10 := h v9 z v0
  let v11 := M z z
  let v12 := M v0 v11
  have h13 := h v9 z v12
  have h14 := R v12
  have h15 := h v0 z z
  have h16 := R v9
  have h17 := h v0 v11 v0
  let v18 := M v1 z
  let v19 := M v0 v18
  have h20 := h v9 v1 v19
  have h21 := S h20
  have h22 := R v19
  have h23 := h v0 z v1
  have h24 := C (T h7 (C h16 h23)) h22
  have h25 := C (T (T h24 h21) h8) h6
  have h26 := h v0 v18 v0
  have h27 := C (T (C h16 (S h23)) h8) h22
  have h28 := T (T h7 h20) h27
  have h29 := C h6 (T h26 h25)
  let v30 := M x v1
  T (T (T (T (T (T (h x y v0) (h (M x (M v0 y)) v0 v0)) (C (T (T (T (C (C (R x) (h v0 y z)) h5) (S (h x z v3))) (h x z v0)) (C (R v30) (T (T (T h7 h20) h27) h29))) h6)) (S (h v30 v3 v0))) (C (T h2 (C (R v4) (T (T (T (T (T (T (T (T h7 h20) h27) h29) (h v0 v3 v0)) (C (T (T (T (T (T (C h28 (T (T (T (C h6 (T (C h28 h6) (S h26))) h24) h21) h8)) h25) (C h7 h6)) (S h10)) h13) (C (T (C h16 (S h15)) h8) h14)) h6)) (S h17)) h17) (C (T (T (T (C (T h7 (C h16 h15)) h14) (S h13)) h10) (C h8 h6)) h6)))) h5)) (S (h v4 v0 v3))) (S h2)

@[equational_result]
theorem Equation2196_implies_Equation2170 (G: Type _) [Magma G] (h: Equation2196 G) : Equation2170 G := fun x y z =>
  let v0 := M y z
  let v1 := M z y
  let v2 := M v0 x
  let v3 := M v2 v1
  have h4 := S (h v2 v1 v3)
  let v5 := M v1 v3
  let v6 := M (M v3 v0) v0
  let v7 := M v5 v3
  have h8 := h z y v1
  have h9 := S h8
  have h10 := C (R v7) h9
  let v11 := M y v1
  let v12 := M v11 v1
  have h13 := h v12 v1 v3
  let v14 := M v1 v2
  let v15 := M v14 v2
  let v16 := M (M v2 y) y
  have h17 := h v0 x v3
  let v18 := M (M x v3) v3
  have h19 := R (M (M v2 x) x)
  let v20 := M x v0
  have h21 := R (M (M v1 x) x)
  T (T (T (T (T (T (T (h x v0 v0) (C (T (T (T (T (h (M (M v0 v0) v0) (M z v0) v0) (C (S (h y z v0)) (S (h z v0 v0)))) (h v0 z y)) (C (R (M v1 y)) (T (T (T (T (T (h (M v0 z) v1 x) (C h21 (S (h z y z)))) (C h21 h8)) (S (h v12 v1 x))) h13) h10))) (S (h v7 z y))) (T (T (T (T (h v20 v0 v2) (C (R (M (M v0 v2) v2)) (T (T (T (T (T (h (M v20 v0) v2 x) (C h19 (S (h v0 x v0)))) (C h19 h17)) (S (h v18 v2 x))) (h v18 v2 y)) (C (R v16) (S h17))))) (S (h v16 v0 v2))) (h v16 (M x v2) v2)) (C (S (h v0 x v2)) (S (h x v2 y)))))) (C (T (h v7 v11 v1) (C h9 (S (h y v1 v3)))) (R v2))) (h v14 v2 v1)) (C (R (M v3 v1)) (T (T (T (T (h v15 z x) (C (R (M (M z x) x)) (T (T (T (C (R v15) h8) (S (h v12 v1 v2))) h13) h10))) (S (h v7 z x))) (h v7 v3 v0)) (C (R v6) h4)))) (S (h v6 v2 v1))) (h v6 v5 v3)) (C h4 (S (h v1 v3 v0)))

@[equational_result]
theorem Equation2779_implies_Equation26 (G: Type _) [Magma G] (h: Equation2779 G) : Equation26 G := fun x y =>
  let v0 := M x y
  let v1 := M v0 y
  have h2 := h v1 x v1
  have h3 := S h2
  have h4 := R x
  let v5 := M v0 v1
  let v6 := M v1 v1
  let v7 := M x v1
  have h8 := h (M v7 v6) v5 x
  have h9 := R v5
  have h10 := h v0 x y
  let v11 := M v5 v5
  have h12 := h v11 v1 v0
  have h13 := S h12
  have h14 := R v1
  have h15 := h v0 v0 v1
  let v16 := M v1 v0
  have h17 := R v16
  have h18 := h x v0 y
  have h19 := C (T h18 (C h17 h15)) h14
  have h20 := T (T (T h19 h13) (C (C h10 h2) h9)) (S h8)
  have h21 := S h15
  have h22 := C (T (C h17 h21) (S h18)) h14
  have h23 := S h10
  have h24 := C (C h23 h3) h9
  let v25 := M x v0
  have h26 := R v7
  have h27 := h x x y
  have h28 := R v0
  have h29 := h x v1 v0
  have h30 := S h29
  let v31 := M v16 v25
  have h32 := h v31 v0 v1
  have h33 := h v31 x v1
  T (T (T (T h27 (C (T (T (T (C (T h10 (C h9 h29)) h28) (S h32)) h33) (C (T (C h20 h30) h3) h4)) h4)) (C (T (T (T (T (T (T (T (T (T (T (T (C (T (T (T h2 (C (T h8 h24) h4)) (C (T h12 h22) h4)) (C h26 h29)) h4) (S h33)) h32) (C (T (C h9 h30) h23) h28)) (h (M v0 v0) x x)) (C (C (R (M x x)) (T (S h27) (h x x v1))) h4)) (S (h (M v7 v7) x x))) (C h26 (T (T (T (T h19 h13) (h v11 x v0)) (C (C (R v25) (T h21 (h v0 v0 y))) h4)) (S (h v6 x v0))))) h8) h24) h12) h22) h4)) (C h20 h4)) h3

@[equational_result]
theorem Equation4210_implies_Equation3500 (G: Type _) [Magma G] (h: Equation4210 G) : Equation3500 G := fun x y z =>
  let v0 := M z z
  let v1 := M v0 y
  let v2 := M y v1
  have h3 := R v2
  have h4 := R y
  have h5 := R v0
  have h6 := h z z z
  have h7 := S h6
  have h8 := R z
  have h9 := h v0 z v1
  have h10 := R v1
  have h11 := h z y v0
  have h12 := C (T (C h11 h10) (S h9)) h8
  have h13 := h v1 y z
  have h14 := h v0 y v0
  have h15 := h v1 y x
  have h16 := R x
  have h17 := h x y v0
  have h18 := h v0 x v1
  have h19 := h z z v0
  have h20 := h y v0 v0
  have h21 := C (T (C (T h20 (C (C (T (C h6 h5) (S h19)) h4) h5)) (T (T (T (T (C (T h18 (C (S h17) h10)) h16) (S h15)) h13) h12) h7)) (S h14)) h4
  have h22 := h (M (M v0 x) x) v0 y
  have h23 := h x x v0
  let v24 := M x x
  have h25 := R (M v2 z)
  have h26 := S h13
  have h27 := C (T h9 (C (S h11) h10)) h8
  T (T (T (T (T (T (T (T (T h23 h22) h21) h13) h12) (h (M v0 z) z v2)) (C (C h25 (T (T (h v0 z v2) (C (C h25 (T (T (T (T (T h6 h27) h26) (C (T h14 (C (T (C (C (T h19 (C h7 h5)) h4) h5) (S h20)) (T (T (T (T h6 h27) h26) h15) (C (T (C h17 h10) (S h18)) h16)))) h4)) (S h22)) (S h23))) h3)) (S (h v24 z v2)))) h3)) (C (C h25 (T (h v24 z y) (C (T (T (C (R (M y z)) (T (T (T (T (T h23 h22) h21) h13) h12) h7)) (C (T (h y z z) (h v1 z z)) h5)) (S (h z v1 v0))) h4))) h3)) (S (h (M (M z v1) y) z v2))) (S (h y v1 z))

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
theorem Equation3211_implies_Equation4421 (G: Type _) [Magma G] (h: Equation3211 G) : Equation4421 G := fun x y z =>
  let v0 := M z y
  let v1 := M v0 z
  have h2 := R v0
  have h3 := R v1
  have h4 := R z
  have h5 := h v0 y v0
  have h6 := R y
  have h7 := h y z y
  have h8 := h z v0 y
  have h9 := C (C (T h8 (C (S h7) h2)) h2) h2
  have h10 := C (T (C h9 h6) (S h5)) h4
  have h11 := h y z v0
  have h12 := S h11
  have h13 := S h8
  have h14 := C (T (C h7 h2) h13) h2
  have h15 := C (T h5 (C (C h14 h2) h6)) h4
  let v16 := M x y
  let v17 := M x v16
  have h18 := S (h v0 z v17)
  have h19 := R v17
  have h20 := h v17 v0 z
  have h21 := S h20
  have h22 := h v1 v1 v16
  have h23 := R v16
  have h24 := h y x y
  have h25 := h x v16 y
  have h26 := C (C (T (C (C (C (T h25 (C (T (T (S h24) h11) h10) h23)) h23) h3) h3) (S h22)) h4) h19
  have h27 := h z v17 v1
  have h28 := C (T (T (T (C (T (T (T (C (T (T h15 h12) h7) h2) h13) h27) h26) h2) h21) (h v17 v0 v17)) (C (C (C (T (C (T (h v0 z v0) (C (C (T h9 (C (T (T h14 (C (T h27 h26) h2)) h21) h2)) h2) h4)) h19) (S (h z v17 v0))) h19) h19) h2)) h4
  have h29 := h z v1 v0
  T (T h20 (C (T (T (T (C (C (T h22 (C (C (C (T (C (T (T h15 h12) h24) h23) (S h25)) h23) h3) h3)) h4) h19) (S h27)) h29) (C (T (T (T h28 h18) (h v0 z v1)) (C (T (T (T (C (C (C (T h29 (C (T h28 h18) h3)) h3) (T h15 h12)) h2) (S (h y v0 v1))) h11) h10) h4)) h3)) h2)) (S (h v1 v0 z))

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
theorem Equation4176_implies_Equation3620 (G: Type _) [Magma G] (h: Equation4176 G) : Equation3620 G := fun x y z =>
  let v0 := M x y
  let v1 := M z y
  let v2 := M v1 x
  have h3 := R v0
  have h4 := R z
  have h5 := h v1 x z
  let v6 := M (M x z) v1
  have h7 := R v1
  have h8 := h v1 x y
  have h9 := h y v0 v1
  have h10 := T h9 (C (S h8) h7)
  let v11 := M y v0
  let v12 := M z v1
  have h13 := R x
  have h14 := S h9
  have h15 := C h8 h7
  let v16 := M x v2
  have h17 := C (T (T (T (h v2 v16 v1) (C (S (h v1 x v2)) h7)) h15) h14) h13
  have h18 := h v16 v1 x
  have h19 := C (T (C (h x v1 x) h13) (S (h x v2 x))) h7
  have h20 := h x x v1
  have h21 := S (h x z y)
  have h22 := R v2
  have h23 := h x z v2
  T (T (h x y v0) (C (T (T (T (C (T (h y v0 v2) (C (S (h v2 x y)) h22)) h13) (S (h v2 v2 x))) (h v2 v2 z)) (C (T (T (T (C (h v2 z y) h22) (S (h y v1 v2))) (h y v1 v0)) (C (T (T (C (T (T (T (T (T (T (T (T (C (T (T (T (T (T (T (h z y v1) (C (T (C (T (T (h y v1 x) (C (T h21 h23) h13)) (C (S h23) h13)) h4) (S (h x x z))) h7)) (C (T (T (T (T h20 h19) h18) h17) (C h10 h13)) h7)) (S (h x v2 v1))) (h x v2 v2)) (C (S (h v2 v1 x)) h22)) (C (T h15 h14) h22)) h3) (S (h v2 y v0))) h21) (h x z v1)) (C (T (T (h v12 x x) (C (C (T (T (T h20 h19) h18) h17) (R v12)) h13)) (S (h v12 v11 x))) h7)) (S (h v11 z v1))) (C h10 h4)) (C (C h5 h7) h4)) (S (h v1 v6 z))) (R y)) (S (h v6 z y))) (S h5)) h3)) h4)) h3)) (S (h z v2 v0))

@[equational_result]
theorem Equation3404_implies_Equation4226 (G: Type _) [Magma G] (h: Equation3404 G) : Equation4226 G := fun x y z =>
  have h0 := R y
  let v1 := M z z
  let v2 := M v1 x
  have h3 := h v1 x v2
  have h4 := S h3
  let v5 := M v2 v1
  have h6 := h v2 (M x v5) x
  have h7 := S h6
  have h8 := h v1 x z
  have h9 := R x
  have h10 := C h9 (S h8)
  let v11 := M z v1
  have h12 := h v11 z x
  have h13 := h v11 z z
  have h14 := S h13
  have h15 := h z z z
  have h16 := R z
  have h17 := C h16 (C h16 h15)
  have h18 := h x v5 v1
  have h19 := h v5 v2 x
  have h20 := R v1
  have h21 := C (T (C h20 (T (T (T (T (T (T h15 h17) h14) h12) h10) (C h9 h3)) (S h19))) (S h18)) (T (T (T (T h15 h17) h14) h12) h10)
  let v22 := M v1 v1
  have h23 := h v22 v1 x
  have h24 := S h23
  have h25 := h v1 x v1
  have h26 := C h9 h25
  have h27 := h v1 x x
  have h28 := h (M x v1) x x
  have h29 := S h15
  have h30 := C h16 (C h16 h29)
  have h31 := S h12
  have h32 := C h9 h8
  T (T (T (h x y v1) (C h20 (C h0 h25))) (S (h (M x v22) y v1))) (C (T (T (T (T (C h9 (T (T (T (T (T (T (T (h v1 v1 z) (C h16 (T (T (C h20 (h z v1 z)) (S (h v1 z v1))) (h v1 z z)))) h14) h12) h10) (C h9 h27)) (S h28)) (C (T (T (C h9 (T (T (T (T (T (T (T h15 h17) h14) h12) h10) h26) h24) h21)) h7) h4) h9))) (C h9 (T (T (C (T (T h3 h6) (C h9 (T (T (T (T (T (T (T (C (T h18 (C h20 (T (T (T (T (T (T h19 (C h9 h4)) h32) h31) h13) h30) h29))) (T (T (T (T h32 h31) h13) h30) h29)) h23) (C h9 (S h25))) h32) h31) h13) h30) h29))) h9) h28) (C h9 (S h27))))) (C h9 (T (T h26 h24) h21))) h7) h4) h0)

@[equational_result]
theorem Equation952_implies_Equation16 (G: Type _) [Magma G] (h: Equation952 G) : Equation16 G := fun x y =>
  let v0 := M y x
  let v1 := M y v0
  have h2 := h v1 x v1
  have h3 := S h2
  let v4 := M v1 v0
  let v5 := M v1 x
  let v6 := M v1 v1
  have h7 := h (M v6 v5) v4 x
  have h8 := h v0 x y
  have h9 := R v4
  let v10 := M v4 v4
  have h11 := h v10 v1 v0
  have h12 := S h11
  let v13 := M v0 v1
  have h14 := R v13
  have h15 := h v0 v0 v1
  have h16 := h x v0 y
  have h17 := R v1
  have h18 := C h17 (T h16 (C h15 h14))
  have h19 := T (T (T h18 h12) (C h9 (C h2 h8))) (S h7)
  have h20 := R x
  have h21 := S h15
  have h22 := C h17 (T (C h21 h14) (S h16))
  have h23 := S h8
  have h24 := C h9 (C h3 h23)
  have h25 := R v5
  let v26 := M v0 x
  have h27 := h x x y
  have h28 := h x v1 v0
  have h29 := S h28
  have h30 := R v0
  let v31 := M v26 v13
  have h32 := h v31 v0 v1
  have h33 := h v31 x v1
  T (T (T (T h27 (C h20 (T (T (T (C h30 (T h8 (C h28 h9))) (S h32)) h33) (C h20 (T (C h29 h19) h3))))) (C h20 (T (T (T (T (T (T (T (T (T (T (T (C h20 (T (T (T h2 (C h20 (T h7 h24))) (C h20 (T h11 h22))) (C h28 h25))) (S h33)) h32) (C h30 (T (C h29 h9) h23))) (h (M v0 v0) x x)) (C h20 (C (T (S h27) (h x x v1)) (R (M x x))))) (S (h (M v5 v5) x x))) (C (T (T (T (T h18 h12) (h v10 x v0)) (C h20 (C (T h21 (h v0 v0 y)) (R v26)))) (S (h v6 x v0))) h25)) h7) h24) h11) h22))) (C h20 h19)) h3

@[equational_result]
theorem Equation684_implies_Equation1670 (G: Type _) [Magma G] (h: Equation684 G) : Equation1670 G := fun x y z =>
  let v0 := M y (M (M y x) x)
  have h1 := R v0
  have h2 := h y y x
  have h3 := T h2 (C h2 h1)
  have h4 := R z
  have h5 := R y
  let v6 := M z y
  have h7 := S (h v6 v6 y)
  let v8 := M v6 (M (M v6 y) y)
  have h9 := h y z y
  have h10 := S h2
  have h11 := T (C h10 h1) h10
  have h12 := R v6
  have h13 := h v6 y v0
  let v14 := M v6 (M (M v6 x) x)
  let v15 := M z v6
  have h16 := h v15 v6 v14
  have h17 := R v14
  have h18 := h v6 v6 x
  have h19 := R v15
  have h20 := S h18
  let v21 := M x y
  let v22 := M v21 y
  have h23 := R v21
  have h24 := R x
  have h25 := S (h v21 v21 x)
  let v26 := M v21 x
  let v27 := M v21 (M v26 x)
  let v28 := M x (M (M x x) x)
  have h29 := h x x x
  T (h x v21 x) (C h23 (T (T (T (T (T (T (T (T (T (C h24 (C (R v26) (T h29 (C h29 (R v28))))) (S (h v26 x v28))) (C h23 (T (T (T (h x v21 v27) (C h23 (T (T (C h24 (T (C h25 (R v27)) h25)) (C h24 (T (h v21 y v0) (C h5 (C h23 h11))))) (S (h y x y))))) (h v22 y v0)) (C h5 (C (R v22) h11))))) (S (h y v21 y))) h9) (C h4 (T (C h5 (C h12 h3)) (S h13)))) h16) (C h12 (C h19 (T (C h20 h17) h20)))) (h (M v6 (M v15 v6)) v6 v8)) (C h12 (T (T (C (T (T (T (C h12 (C h19 (T h18 (C h18 h17)))) (S h16)) (C h4 (T h13 (C h5 (C h12 h11))))) (S h9)) (T (C h7 (R v8)) h7)) (C h5 (C h4 h3))) (S (h z y v0))))))

@[equational_result]
theorem Equation3131_implies_Equation1793 (G: Type _) [Magma G] (h: Equation3131 G) : Equation1793 G := fun x y z =>
  let v0 := M z y
  let v1 := M y z
  let v2 := M v0 x
  let v3 := M v1 v2
  have h4 := R y
  have h5 := R v1
  have h6 := h y v1 y
  have h7 := h z y y
  have h8 := h z y v2
  have h9 := R v2
  have h10 := h v1 v3 v1
  have h11 := S h10
  have h12 := R v3
  have h13 := h v2 v1 v1
  have h14 := C h13 h12
  have h15 := C (T h14 h11) h9
  have h16 := C h15 h9
  have h17 := C (S h13) h12
  have h18 := C (T h10 h17) h9
  have h19 := h v3 v2 v2
  have h20 := S h19
  have h21 := C h18 h9
  have h22 := C h21 h9
  have h23 := C (T (T h22 h20) h18) h9
  have h24 := C h16 h9
  have h25 := h v3 v1 v1
  have h26 := h v2 v3 v2
  have h27 := C (T (T h15 h19) h24) h9
  have h28 := h v2 v3 v3
  have h29 := T h28 (C (T (T (C (T (C (T h21 h27) h12) (S h26)) h12) h14) h11) h12)
  have h30 := h v1 v2 v1
  have h31 := S h30
  have h32 := C (T (T (T h22 h20) h25) (C (C (C (T (C (T (T h10 h17) (C (T h26 (C (T h23 h16) h12)) h12)) h12) (S h28)) h5) h5) h5)) h9
  have h33 := C (T (T (S h7) h8) (C (T (T (T h21 h27) h32) h31) h4)) h5
  have h34 := R v0
  T (T (h x v0 v0) (C (C (C h29 h34) h34) (T (C (T h8 (C (T (T (T (T (T h21 h27) h32) h31) (h v1 y v1)) (C (T (C (T (T (T (C (C (T h6 h33) h5) h5) (S (h y v1 v1))) h6) h33) h5) (C (T (C (T (T (C (T (T (T h30 (C (T (T (T (C (C (C h29 h5) h5) h5) (S h25)) h19) h24) h9)) h23) h16) h4) (S h8)) h7) h5) (S h6)) h5)) h4)) h4)) h4) (S (h v1 y y))))) (S (h v3 v1 v0))

@[equational_result]
theorem Equation4176_implies_Equation4424 (G: Type _) [Magma G] (h: Equation4176 G) : Equation4424 G := fun x y z =>
  have h0 := R y
  have h1 := h z z z
  have h2 := S h1
  have h3 := R z
  let v4 := M z z
  have h5 := h z v4 z
  have h6 := h z v4 y
  have h7 := h y z z
  have h8 := C (T (T (T (C h7 h0) (S h6)) h5) (C h2 h3)) h3
  have h9 := h y y z
  let v10 := M x y
  have h11 := h y y v10
  let v12 := M y v10
  have h13 := h v10 v12 y
  have h14 := h v10 v12 x
  have h15 := S h14
  have h16 := R x
  have h17 := R v10
  let v18 := M x v10
  have h19 := R v4
  have h20 := h x y y
  have h21 := h y (M y y) x
  have h22 := S h9
  have h23 := C (T h6 (C (S h7) h0)) h3
  have h24 := S (h (M z v4) z y)
  have h25 := C (C (R (M z y)) (T (C h1 h3) (S h5))) h0
  have h26 := h (M v4 z) z y
  have h27 := h x y v10
  T (T (T (T (h x v10 x) (C (T (T (C (T (T (T (T (T (C h27 h16) h15) (h v10 v12 v4)) (C (S (h v4 y v10)) h19)) (C (T (T (T (T (T (T (T (T (C (T (T (T h1 h26) h25) h24) h0) (C (T h23 h22) h0)) (C h11 h0)) (S h13)) h14) (C (S h27) h16)) (C h20 h16)) (S h21)) (C h0 (T (T h9 h8) h2))) h19)) (C (T (T (C h0 (T (T (T (T (T h1 h26) h25) h24) h23) h22)) h21) (C (S h20) h16)) h19)) h16) (S (h v4 v10 x))) (C (T (T (h z z x) (C (T (C (h z x v10) h3) (S (h v10 v18 z))) h16)) (C (T (T (T (h v10 v18 v10) (C (S (h v10 x v10)) h17)) (C (h v10 x y) h17)) (S (h y v10 v10))) h16)) h17)) h16)) h15) h13) (C (T (T (T (S h11) h9) h8) h2) h0)

@[equational_result]
theorem Equation492_implies_Equation4544 (G: Type _) [Magma G] (h: Equation492 G) : Equation4544 G := fun x y z =>
  let v0 := M y z
  let v1 := M x v0
  have h2 := h v0 z y
  have h3 := h v0 z v0
  let v4 := M z y
  have h5 := h z y v4
  have h6 := S h5
  have h7 := h y v4 z
  have h8 := h z y z
  have h9 := R v4
  have h10 := R z
  have h11 := C h10 (C h9 (C h9 (T (C h9 h8) (S h7))))
  have h12 := h v4 z v4
  have h13 := h v4 v4 v0
  have h14 := h v4 x v1
  have h15 := S h14
  have h16 := h x v0 x
  have h17 := R v1
  have h18 := h v0 v1 x
  have h19 := R y
  have h20 := h v1 v4 y
  have h21 := R x
  have h22 := C h21 (T h20 (C h9 (C h17 (T (T (C h19 (T (C h19 (T h12 h11)) h6)) h18) (C h17 (S h16))))))
  have h23 := R v0
  have h24 := h v0 v0 x
  have h25 := C h19 (T (T (T (C h9 (C h9 (T h24 (C h23 (C h23 (T h22 h15)))))) (S h13)) h12) h11)
  have h26 := h y v0 v4
  have h27 := h z y v0
  have h28 := S h26
  have h29 := C h19 (T (C h10 (C h9 (C h9 (T h7 (C h9 (S h8)))))) (S h12))
  have h30 := C h19 (T h13 (C h9 (C h9 (T (C h23 (C h23 (T h14 (C h21 (T (C h9 (C h17 (T (T (C h17 h16) (S h18)) (C h19 (T h5 h29))))) (S h20)))))) (S h24)))))
  T (h v1 v0 x) (C (T h2 (C h10 (T (C h23 (T (T (T (T (C h19 (T h3 (C h10 (C h23 (C h23 (T (C h23 (T (T h5 h29) h30)) h28)))))) (S h27)) h5) h29) h30)) h28))) (T (C h17 (C h21 (T (h v1 v1 x) (C h17 (C h17 (C h21 (T (T (T h22 h15) (C h10 (T h26 (C h23 (T (T (T h25 h6) h27) (C h19 (T (C h10 (C h23 (C h23 (T h26 (C h23 (T h25 h6)))))) (S h3)))))))) (S h2)))))))) (S (h x v1 v1))))

@[equational_result]
theorem Equation1131_implies_Equation1355 (G: Type _) [Magma G] (h: Equation1131 G) : Equation1355 G := fun x y z =>
  let v0 := M z x
  let v1 := M v0 y
  let v2 := M v1 z
  have h3 := R v1
  have h4 := R v2
  have h5 := h y v2 z
  have h6 := S h5
  have h7 := R v0
  let v8 := M z y
  let v9 := M (M v2 v8) z
  have h10 := h v9 v0 v2
  have h11 := R x
  let v12 := M v2 v1
  have h13 := h y v1 z
  let v14 := M y v2
  have h15 := h v2 v0 v14
  have h16 := h z v1 v0
  have h17 := R y
  have h18 := h x y v14
  have h19 := R z
  let v20 := M (M y (M v14 x)) v14
  have h21 := h x y x
  T h21 (C h17 (T (T (T (T (T (T (T (h (M (M y (M x x)) x) x y) (C h11 (C (T (C h11 (S h21)) (C h11 h18)) h17))) (S (h v20 x y))) (h v20 z y)) (C h19 (C (C h19 (S h18)) h17))) (h (M z v1) v0 v1)) (C h7 (C (T (T (T (T (C h7 (T (C h3 (C (T h16 (C h3 (T (h (M (M v1 (M v0 z)) v0) v1 v1) (C h3 (C (C h3 (S h16)) h3))))) h3)) (S (h v12 v1 v1)))) (C h7 (C (T h15 (C h7 (T (h (M (M v0 (M v14 v2)) v14) v1 v0) (C h3 (T (T (T (C (T (T (C h3 (S h15)) (h (M v1 v2) v2 v0)) (C h4 (T (T (T (C (T (C h4 (T (C h7 (C (C h7 h5) h4)) (S h10))) h6) h7) (h (M y v0) x v1)) (C h11 (C (C h11 (T (C h3 (C (T h13 (C h3 (T (h (M (M v1 v8) z) v0 v1) (C h7 (C (C h7 (S h13)) h3))))) h7)) (S (h (M v1 v1) v1 v0)))) h3))) (S (h v1 x v1))))) h7) (h (M v12 v0) x v2)) (C h11 (C (T (C h11 (S (h y v2 v0))) (C h11 h5)) h4))) (S (h v9 x v2))))))) h3))) (S (h v9 v0 v1))) h10) (C h7 (C (C h7 h6) h4))) h3))) (S (h v2 v0 v1))))

@[equational_result]
theorem Equation2944_implies_Equation4640 (G: Type _) [Magma G] (h: Equation2944 G) : Equation4640 G := fun x y z =>
  have h0 := R z
  have h1 := h y x y
  have h2 := S h1
  let v3 := M x y
  let v4 := M x v3
  let v5 := M v4 y
  have h6 := R v5
  have h7 := C (C (T (C h6 h2) h2) h0) h0
  have h8 := h y v5 z
  have h9 := T (C (C (T h1 (C h6 h1)) h0) h0) (S h8)
  let v10 := M (M x (M x x)) x
  have h11 := h x v10 y
  have h12 := S h11
  have h13 := R y
  have h14 := h x x x
  have h15 := R v10
  have h16 := C (C (T h14 (C h15 h14)) h13) h13
  let v17 := M v3 x
  have h18 := h (M v3 y) v3 v17
  have h19 := R v3
  have h20 := C h19 (T h16 h12)
  have h21 := R v17
  have h22 := S h14
  have h23 := C (C (T (C h15 h22) h22) h13) h13
  have h24 := C h19 (T h11 h23)
  have h25 := C h19 h24
  have h26 := h v3 x v3
  have h27 := S h26
  let v28 := M (M x v4) v3
  have h29 := R v28
  have h30 := h v3 v28 v17
  have h31 := T h8 h7
  have h32 := R x
  have h33 := C h19 h20
  have h34 := S h30
  have h35 := C (C (T h26 (C h29 h26)) h21) h21
  have h36 := C h33 h21
  have h37 := T (T (T h11 h23) h18) (C (T (T h36 h35) h34) h24)
  T (T (T (T (h v17 x (M (M y z) z)) (C (C (T (C h32 (T (T (T (T (T (C h37 h21) h36) h35) h34) (C h37 h31)) (C h33 h9))) (C h32 (T (C h25 h31) (C (T (T (T (C (T (T h30 (C (C (T (C h29 h27) h27) h21) h21)) (C h25 h21)) h20) (S h18)) h16) h12) h9)))) h9) h9)) h2) h8) h7

