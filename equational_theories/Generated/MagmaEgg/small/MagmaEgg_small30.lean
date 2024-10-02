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
theorem Equation492_implies_Equation3131 (G: Type _) [Magma G] (h: Equation492 G) : Equation3131 G := fun x y z =>
  let v0 := M y x
  let v1 := M v0 z
  let v2 := M v1 z
  have h3 := h z v1 v0
  have h4 := S h3
  have h5 := h v0 z v0
  have h6 := R v1
  have h7 := C h6 h5
  have h8 := h v0 z z
  have h9 := h z v0 v1
  have h10 := h v2 v1 v2
  have h11 := h v1 z v1
  have h12 := R v2
  have h13 := C h12 (S h11)
  have h14 := h z v2 v1
  have h15 := R z
  have h16 := h v1 z v2
  have h17 := R v0
  have h18 := h z z v0
  have h19 := S h16
  have h20 := C h6 (C h12 (C h12 (T (C h12 h11) (S h14))))
  have h21 := R y
  have h22 := R x
  have h23 := C h6 (C h21 (T (C h21 (T (h v2 x v2) (C h22 (C h12 (C h12 (T (C h12 (T (h x y x) (C h21 (C h22 (C h22 (T (C h22 (T (h y v2 z) (C h12 (C h21 (T (C h15 (T (T (C h15 (T h10 h20)) h19) (C h17 (T h18 (C h15 (C h15 (T (C h17 (T h16 (C h15 (T (T (C h6 (C h12 (C h12 (T h14 h13)))) (S h10)) (C h6 (T h3 (C h6 (S h5)))))))) (S h9)))))))) (S h8)))))) (S (h v2 x y)))))))) (S (h y v2 x)))))))) (S (h x y v2))))
  have h24 := h v1 v2 y
  T (h x v0 y) (C (T (T h8 (C h15 (T (T (C h17 (T (C h15 (C h15 (T h9 (C h17 (T (C h15 (T (T (C h6 (T h7 h4)) h10) h20)) h19))))) (S h18))) h24) (C h12 (T (T (T (T (T h23 h7) h4) h14) h13) (C h12 (T h24 (C h12 (T (T h23 h7) h4))))))))) (S (h v2 z v2))) (S (h y x y)))

@[equational_result]
theorem Equation1507_implies_Equation1561 (G: Type _) [Magma G] (h: Equation1507 G) : Equation1561 G := fun x y z =>
  let v0 := M z y
  let v1 := M x v0
  let v2 := M y z
  let v3 := M v2 v1
  have h4 := S (h v1 v2 v3)
  let v5 := M v3 v2
  let v6 := M v1 (M v1 v3)
  let v7 := M v3 v5
  have h8 := h z y v1
  let v9 := M v1 (M v1 y)
  let v10 := M x v1
  have h11 := R (M x v10)
  let v12 := M v1 v0
  have h13 := R (M y (M y v1))
  let v14 := M v1 v12
  have h15 := h y z v2
  let v16 := M v2 (M v2 z)
  have h17 := h v0 x v3
  let v18 := M v3 (M v3 x)
  let v19 := M v1 x
  T (T (T (T (h x v1 v1) (C (T (T (T (T (T (T (T (T (h v19 v1 x) (C (T (T (h (M v1 v19) v1 x) (C (T (S (h v0 x v1)) h17) h11)) (S (h v18 v1 x))) h11)) (C (T (T (T (h v18 v1 y) (C (S h17) h13)) (C (T (T (T (T (C (h z v0 x) (h y z v0)) (S (h v10 (M v0 z) v0))) (h v10 y x)) (C (T (T (T (C h15 (R v10)) (S (h v16 v0 x))) (h v16 v0 v1)) (C (S h15) (R v14))) (R (M x (M x y))))) (S (h v14 y x))) h13)) (S (h v12 v1 y))) h11)) (S (h v0 v1 x))) (h v0 z y)) (C (T (T (T (T (h (M z v0) v2 x) (C (T (S (h z y z)) h8) (R (M x (M x v2))))) (S (h v9 v2 x))) (h v9 v2 v3)) (C (S h8) (R v7))) (R (M y v2)))) (S (h v7 z y))) (h v7 v3 v1)) (C h4 (R v6))) (R (M v1 (M v1 v1))))) (S (h v6 v1 v1))) (h v6 v5 v3)) (C (S (h v2 v3 v1)) h4)

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
theorem Equation1964_implies_Equation4007 (G: Type _) [Magma G] (h: Equation1964 G) : Equation4007 G := fun x y z =>
  let v0 := M z (M y x)
  let v1 := M v0 z
  let v2 := M v1 v1
  let v3 := M v1 x
  let v4 := M x y
  have h5 := h x v4 x
  have h6 := S h5
  have h7 := h x v1 v4
  let v8 := M v1 v4
  have h9 := R v8
  have h10 := R (M v4 x)
  have h11 := h v1 x x
  have h12 := R (M x x)
  have h13 := R v1
  have h14 := h x z y
  have h15 := C (S h14) h13
  have h16 := h y v0 z
  have h17 := R x
  have h18 := T (C (C h17 (T h16 h15)) h12) (S h11)
  have h19 := T (C (T h5 (C h18 h10)) h9) (S h7)
  have h20 := h v4 x v1
  have h21 := h y v1 x
  have h22 := S h16
  have h23 := C h14 h13
  have h24 := T h11 (C (C h17 (T h23 h22)) h12)
  have h25 := T h7 (C (T (C h24 h10) h6) h9)
  have h26 := h v3 x v8
  have h27 := C h24 (T h26 (C (T (C h25 (T (T (S h21) h16) h15)) (S h20)) h19))
  T (T (h v4 v0 v1) (C (C (R v0) (T (T (h v8 v1 x) (C (T (T (C h13 h19) (C h13 (T h5 (C h18 (T (C (T h20 (C h19 (T (T h23 h22) h21))) h25) (S h26)))))) (C h13 (T (h (M v1 v3) v1 v1) (C (T (T (C h13 (C h13 (T h27 h6))) h27) h6) (R v2))))) (R v3))) (S (h v2 v1 x)))) (R (M v0 v1)))) (S (h v1 v0 v1))

@[equational_result]
theorem Equation2196_implies_Equation1320 (G: Type _) [Magma G] (h: Equation2196 G) : Equation1320 G := fun x y z =>
  let v0 := M y x
  let v1 := M v0 z
  let v2 := M v1 z
  let v3 := M y v2
  let v4 := M v3 x
  let v5 := M v4 x
  let v6 := M v2 v0
  have h7 := h v2 v0 z
  have h8 := h y x v3
  have h9 := S h8
  let v10 := M (M x v3) v3
  have h11 := h v10 v0 z
  have h12 := h v10 v0 y
  let v13 := M v0 y
  let v14 := M v13 y
  have h15 := R v14
  let v16 := M v0 x
  have h17 := R v16
  have h18 := h v10 v0 x
  have h19 := R (M v16 x)
  let v20 := M x y
  have h21 := T (T (h v20 y x) (C h17 (T (T (T (T (h (M v20 y) v0 x) (C h19 (T (S (h y x y)) h8))) (S h18)) h12) (C h15 h9)))) (S (h v14 y x))
  let v22 := M x v0
  let v23 := M v22 v0
  have h24 := h y x v0
  T (T (T (T (T (T (T (T (T (T (T (h x y v2) (C (R (M v3 v2)) h21)) (S (h v13 y v2))) (C (T (C h24 (h x v0 z)) (S (h v2 v22 v0))) h8)) (S h11)) h18) (C h19 h9)) (C h19 h24)) (S (h v23 v0 x))) (h v23 x x)) (C (R (M (M x x) x)) (T (C (R v23) (T (T (T (h x y x) (C h17 h21)) (C h17 (T (T (T (T (h v14 y v1) (C (R (M (M y v1) v1)) (T (T (T (C h15 h8) (S h12)) h11) (C (R v2) h9)))) (S (h v2 y v1))) (h v2 v3 x)) (C (R v5) (T (C (T h7 (C h7 (R v6))) (R v3)) (S (h y v2 v6))))))) (S (h v5 y x)))) (S (h v4 x v0))))) (S (h v3 x x))

@[equational_result]
theorem Equation1320_implies_Equation1470 (G: Type _) [Magma G] (h: Equation1320 G) : Equation1470 G := fun x y z =>
  let v0 := M z y
  let v1 := M z v0
  let v2 := M x y
  let v3 := M v2 v1
  have h4 := h v3 y y
  have h5 := R x
  have h6 := h v3 x v3
  let v7 := M (M (M x v3) v3) v3
  have h8 := R v3
  let v9 := M (M v3 v3) v3
  have h10 := h v1 x z
  let v11 := M (M (M x v1) z) z
  have h12 := R y
  let v13 := M (M v1 y) y
  have h14 := h x y x
  have h15 := C (C (S h14) h12) h12
  let v16 := M y x
  let v17 := M (M v16 x) x
  have h18 := h x y v3
  T (T h18 (C h12 (T (T (T (h (M (M v16 v3) v3) y x) (C h12 (T (T (T (T (C (C (S h18) h5) h5) (h (M (M x x) x) y x)) (C h12 (C (C (T (T (T (C h12 (C (C h14 h5) h5)) (S (h v17 y x))) (h v17 y y)) (C h12 h15)) h5) h5))) (S (h (M v2 y) y x))) (C (C h14 h12) h12)))) (C h12 (T (T (T (T (T (T h15 (C (R v2) (T (T (T (T (T (T (h y z x) (C (R z) (C (C (h v0 z y) h5) h5))) (S (h v13 z x))) (h v13 x x)) (C h5 (C (C (T (T (T (C h5 (C (C h10 h12) h12)) (S (h v11 x y))) (h v11 x x)) (C h5 (C (C (S h10) h5) h5))) h5) h5))) (S (h (M (M v1 x) x) x x))) (C (C (h v1 v2 v3) h5) h5)))) (S (h v9 v2 x))) (h v9 x x)) (C h5 (C (C (T (T (T (C h5 (C (C h6 h8) h8)) (S (h v7 x v3))) (h v7 x x)) (C h5 (C (C (S h6) h5) h5))) h5) h5))) (S (h (M (M v3 x) x) x x))) (C (C h4 h5) h5)))) (S (h (M (M (M y v3) y) y) y x))))) (S h4)

@[equational_result]
theorem Equation1761_implies_Equation31 (G: Type _) [Magma G] (h: Equation1761 G) : Equation31 G := fun x y =>
  let v0 := M y y
  let v1 := M v0 x
  let v2 := M v1 v1
  have h3 := R v1
  have h4 := h y y x
  have h5 := S h4
  let v6 := M y x
  have h7 := h v6 v1 y
  have h8 := R y
  let v9 := M v1 y
  have h10 := R v9
  have h11 := C (T (C h10 (C h4 h8)) (S h7)) h3
  have h12 := C h10 (C h5 h8)
  have h13 := h v6 v1 v1
  have h14 := h y y v1
  let v15 := M v0 v1
  have h16 := h v15 y v1
  have h17 := R v15
  have h18 := h v9 v0 v1
  let v19 := M y v1
  have h20 := R v19
  have h21 := h v1 y v1
  have h22 := C (T (C h20 (T (T h21 (C h20 (C (T h18 (C h17 (T h11 h5))) h3))) (S h16))) (S h14)) h3
  have h23 := R v2
  have h24 := h v19 v1 v1
  have h25 := C (T h14 (C h20 (T (T h16 (C h20 (C (T (C h17 (T h4 (C (T h7 h12) h3))) (S h18)) h3))) (S h21)))) h3
  have h26 := S h24
  have h27 := C h23 (T (C h5 h3) h25)
  let v28 := M x v1
  T (T (h x v1 v0) (C (R (M v1 v0)) (C (T (T (h v28 y x) (C (T (T h13 h27) h26) (T (T (T (T (T (C (T (C (R v28) h4) (S (h y x v1))) (R x)) h13) h27) h26) h25) (C (T (h (M v19 v1) v1 v1) (C h23 (T (T (C (T (T (T (T (T h22 h24) (C h23 (T h22 (C h4 h3)))) (S h13)) h7) h12) h3) h11) h5))) h3)))) (S (h v2 y v1))) (R v0)))) (S (h v1 v1 v0))

@[equational_result]
theorem Equation2714_implies_Equation1090 (G: Type _) [Magma G] (h: Equation2714 G) : Equation1090 G := fun x y z =>
  let v0 := M y z
  let v1 := M x v0
  let v2 := M v1 z
  have h3 := R v2
  have h4 := h y y z
  have h5 := R z
  have h6 := R v0
  have h7 := h y x v0
  have h8 := S h7
  let v9 := M x y
  have h10 := h v0 (M v9 v1) v0
  have h11 := T h10 (C (C h8 h8) h6)
  have h12 := h v0 x v2
  let v13 := M x v2
  have h14 := h v13 v1 z
  have h15 := S h10
  have h16 := C (C h7 h7) h6
  have h17 := S h14
  have h18 := C h12 h5
  let v19 := M y v2
  let v20 := M v19 v2
  let v21 := M v19 v0
  have h22 := h y x v19
  have h23 := R v1
  have h24 := h x x v1
  T (h x (M v1 y) v2) (C (T (T (T (T (T (C (C (C h23 (T (T (T h4 (C (T h16 h15) h5)) h18) h17)) (T (h x x v0) (C (T (C (C h24 h24) h23) (S (h v1 (M (M x x) (M x v1)) v1))) h6))) (T (T (T (T (C (C h23 (T (h y y v2) (C (T (C (C h22 h22) (R v19)) (S (h v19 (M v9 (M x v19)) v19))) h3))) h3) (C (C (C (R x) h11) (T (T (T (h v20 v21 z) (C (T (C (R (M v21 v20)) (S (h v2 y z))) (S (h v0 v19 v2))) h5)) h18) h17)) h3)) (S (h (M (M y y) v0) x v2))) h16) h15)) (S (h v13 v1 v0))) h14) (C (S h12) h5)) (C h11 h5)) (S h4)) h3)

@[equational_result]
theorem Equation3385_implies_Equation3414 (G: Type _) [Magma G] (h: Equation3385 G) : Equation3414 G := fun x y z =>
  let v0 := M x y
  let v1 := M z v0
  let v2 := M z v1
  have h3 := R v2
  have h4 := h v1 z z
  have h5 := h z z v0
  have h6 := R v1
  have h7 := h v0 z v1
  have h8 := R z
  have h9 := C h8 (T h7 (C h6 (S h5)))
  have h10 := T h9 (S h4)
  let v11 := M v0 z
  let v12 := M z v11
  have h13 := R v0
  have h14 := S h7
  have h15 := C h6 h5
  have h16 := C h8 (T h15 h14)
  have h17 := h x y z
  have h18 := S h17
  have h19 := h z (M x (M y z)) v2
  have h20 := S h19
  have h21 := h y z v0
  have h22 := h z x y
  have h23 := R x
  have h24 := h v0 z x
  have h25 := C h3 (C h8 (C (T h24 (C h23 (T (C h13 h22) (S h21)))) h3))
  have h26 := h z v11 v2
  have h27 := S h26
  have h28 := C h3 (C h8 (C (T (C h23 (T h21 (C h13 (S h22)))) (S h24)) h3))
  have h29 := T (T (T h17 h19) h28) h27
  T (T (T (T (T (T (T h17 h19) h28) h27) h9) (C h8 (T (T h15 h14) (C h29 h8)))) (C h8 (T (T (T (T (T (T (C (T (T (T h26 h25) h20) h18) h8) (h v0 z v0)) (C h13 (T (T (h v0 v1 z) (C h8 (T (C h29 (T (T (T (T (T h4 h16) h26) h25) h20) h18)) (C h10 h13)))) (C h8 (C (T h4 h16) h13))))) (S (h z v12 v0))) (h z v12 v2)) (C h3 (C h8 (C h10 h3)))) (S (h z (M v1 z) v2))))) (S (h z v1 z))

@[equational_result]
theorem Equation3404_implies_Equation3489 (G: Type _) [Magma G] (h: Equation3404 G) : Equation3489 G := fun x y z =>
  let v0 := M y z
  have h1 := R v0
  let v2 := M v0 z
  let v3 := M y v2
  have h4 := h y z v3
  have h5 := R z
  have h6 := h (M v3 y) v3 z
  have h7 := R y
  have h8 := h y z v0
  have h9 := h (M v0 y) v0 z
  have h10 := h v0 v0 x
  have h11 := S h10
  have h12 := h x v0 x
  let v13 := M x x
  have h14 := h v13 x v0
  have h15 := h v13 x y
  have h16 := h x y x
  have h17 := R x
  have h18 := C h17 (T (T (T (C h7 h16) (S h15)) h14) (C h1 (S h12)))
  have h19 := h y y x
  have h20 := h y y y
  have h21 := S h19
  have h22 := C h7 (S h16)
  let v23 := M v2 y
  have h24 := h x x x
  T (T (T (T h24 (C h17 (T (T (T (C h17 h24) (S (h v13 x x))) h15) h22))) h21) h20) (C h7 (T (C h7 (T (T (T (T h19 h18) h11) (h v0 v0 z)) (C h5 (T (T (T (C h1 (T (C h5 (h y z v2)) (S (h v23 v2 z)))) (S (h z v23 v0))) (C h5 (T (T (h v2 y v0) (C h1 (C h7 (T (C h1 (T (h v0 z v0) (C h1 (T (C h5 (T (T (T (T (T (T h10 (C h17 (T (T (T (C h1 h12) (S h14)) h15) h22))) h21) h20) (C h7 (T (T (T (C h7 (T (T h19 h18) h11)) (S (h z v0 y))) (C h5 h8)) (S h9)))) (C h7 (T (T (T h9 (C h5 (S h8))) (C h5 h4)) (S h6)))) (C h7 (T h6 (C h5 (S h4)))))) (S (h v0 y z)))))) (S (h y v0 v0)))))) (C h1 (S (h z y y)))))) (S (h y v0 z)))))) (S (h v0 z y))))

@[equational_result]
theorem Equation1293_implies_Equation2186 (G: Type _) [Magma G] (h: Equation1293 G) : Equation2186 G := fun x y z =>
  let v0 := M z x
  let v1 := M y z
  let v2 := M v1 y
  let v3 := M v2 v0
  have h4 := R v3
  let v5 := M v3 v0
  have h6 := h v1 v1 x
  have h7 := S h6
  let v8 := M (M (M v1 v1) x) x
  have h9 := R v8
  let v10 := M (M v2 v1) v1
  have h11 := h y v10 v8
  have h12 := h v1 y v1
  have h13 := R v10
  have h14 := R v1
  let v15 := M (M (M y y) x) x
  let v16 := M v2 y
  have h17 := h z v16 v15
  have h18 := R v15
  have h19 := h y z y
  have h20 := h y y x
  have h21 := R v16
  have h22 := S h20
  let v23 := M (M (M v0 v0) x) x
  have h24 := h v0 v0 x
  T (T (h x v0 v3) (C (R v0) (C (C (T (T (T (T (T (T (T (C (R x) (T h24 (C h24 (R v23)))) (S (h z x v23))) h17) (C h21 (T (C (T (C (S h19) h18) h22) h18) h22))) (h (M v16 y) v1 v3)) (C h14 (C (C (T (T (T (T (C (T (C h21 (T h20 (C (T h20 (C h19 h18)) h18))) (S h17)) h14) (C (R z) (T h6 (C h6 h9)))) (S (h y z v8))) h11) (C h13 (T (C (T (C (S h12) h9) h7) h9) h7))) h4) h4))) (C h14 (C (C (T (T (T (C h13 (T h6 (C (T h6 (C h12 h9)) h9))) (S h11)) (h y v5 v8)) (C (R v5) (T (C (T (C (S (h v1 y v0)) h9) h7) h9) h7))) h4) h4))) (S (h v5 v1 v3))) h4) h4))) (S (h v3 v0 v3))

@[equational_result]
theorem Equation1507_implies_Equation3211 (G: Type _) [Magma G] (h: Equation1507 G) : Equation3211 G := fun x y z =>
  let v0 := M y z
  let v1 := M v0 z
  let v2 := M v1 x
  have h3 := h y v2 y
  let v4 := M y (M y v2)
  have h5 := h v4 (M v2 v1) v2
  have h6 := h x v1 v2
  have h7 := h v1 v2 y
  let v8 := M v2 y
  have h9 := R v8
  let v10 := M v8 v2
  let v11 := M v2 v8
  have h12 := h z y y
  have h13 := S h12
  let v14 := M y (M y y)
  have h15 := R v2
  have h16 := S (h v14 v0 v2)
  let v17 := M v2 (M v2 v0)
  have h18 := C h12 (R v17)
  let v19 := M z v0
  let v20 := M z v19
  let v21 := M v0 (M v0 v1)
  T (h x v1 v0) (C h15 (T (T (T (T (T (T (T (T (T (T (h v21 z v2) (C (T (T (T (T (C (h z v0 v2) (R v21)) (S (h v17 v1 v0))) (h v17 z x)) (C (T (T (T h18 h16) (h v14 v0 z)) (C h13 (R v20))) (R (M x (M x z))))) (S (h v20 z x))) (R (M v2 (M v2 z))))) (S (h v19 z v2))) (C (R z) (T (C (h y v0 v2) (h z y v0)) (S (h v17 (M v0 y) v0))))) h18) h16) (h v14 v2 y)) (C (T (T (C h15 (T (T (h v14 v0 x) (C (T h13 (h z y v2)) (R (M x (M x v0))))) (S (h v11 v0 x)))) (h (M v2 v11) v10 v8)) (C (S (h v2 v8 v2)) (T (T (S (h y v2 v8)) h3) (C h9 (T h5 (C (S h7) (S h6))))))) (R v4))) (S (h v10 v2 y))) (C h9 (T (C h7 h6) (S h5)))) (S h3)))

@[equational_result]
theorem Equation2370_implies_Equation1131 (G: Type _) [Magma G] (h: Equation2370 G) : Equation1131 G := fun x y z =>
  let v0 := M y (M z x)
  let v1 := M v0 z
  let v2 := M y v1
  have h3 := h v2 v2 x
  have h4 := R x
  let v5 := M x (M v2 v0)
  have h6 := R v0
  have h7 := h z y y
  have h8 := R y
  let v9 := M y (M y (M z y))
  let v10 := M x v0
  have h11 := h v0 y x
  let v12 := M y (M x (M v0 y))
  have h13 := h v0 v2 x
  have h14 := S h13
  let v15 := M v2 (M x (M v0 v2))
  have h16 := h v15 x v0
  let v17 := M x v10
  have h18 := h x y x
  have h19 := h x v1 x
  T (T h19 (C (T (T (T (T (T (T (T (h (M v1 (M x (M x v1))) x x) (C (T (C h4 (C h4 (S h19))) (C h4 (C h4 h18))) h4)) (C (T (C h4 (C h4 (S h18))) (C h4 (C h4 (h x v0 x)))) h4)) (S (h (M v0 v17) x x))) (C h6 (T (T (h v17 x x) (C (C h4 (T (C h4 (T (T (T (C (C h4 (C h4 h13)) h4) (S (h v15 x x))) h16) (C (C h4 (C h6 h14)) h6))) (C h4 (T (T (T (T (T (T (C (C h4 (C h6 h13)) h6) (S h16)) (h v15 x y)) (C (T (C h4 (C h8 h14)) (C h4 (C h8 h11))) h8)) (S (h v12 x y))) (h v12 x x)) (C (C h4 (T (T (T (T (T (C h4 (S h11)) (h v10 y x)) (C (T (C h8 (C h4 (S (h z x y)))) (C h8 (C h4 h7))) h4)) (S (h v9 y x))) (h v9 y v0)) (C (C h8 (C h6 (S h7))) h6))) h4))))) h4)) (S (h v5 x x))))) (h (M v0 v5) x x)) (C (T (C h4 (C h4 (S (h v2 v0 x)))) (C h4 (C h4 h3))) h4)) (S (h (M v2 (M x (M v2 v2))) x x))) h4)) (S h3)

@[equational_result]
theorem Equation3211_implies_Equation3131 (G: Type _) [Magma G] (h: Equation3211 G) : Equation3131 G := fun x y z =>
  have h0 := R y
  let v1 := M y x
  let v2 := M v1 z
  let v3 := M v2 z
  have h4 := h v3 v2 v3
  have h5 := S h4
  have h6 := R v2
  have h7 := R v3
  have h8 := R z
  have h9 := h v1 v1 z
  have h10 := C (C (S h9) h8) h7
  have h11 := h z v3 v1
  have h12 := h z v2 z
  have h13 := h v2 v3 z
  have h14 := h z v1 z
  have h15 := C (T (T (T (S h14) h11) h10) (C (T h13 (C (T (T (S h12) h11) h10) h7)) h7)) h6
  have h16 := h v1 v2 z
  have h17 := T (T h16 h15) h5
  let v18 := M v3 y
  have h19 := R v18
  have h20 := h v3 y v18
  have h21 := h y v3 y
  have h22 := h v3 v18 y
  have h23 := h v18 v1 z
  have h24 := S h11
  have h25 := C h9 h8
  have h26 := T (T h4 (C (T (T (C (T (T (C (T (T (C h25 h7) h24) h12) h7) (S h13)) h25) h7) h24) h14) h6)) (S h16)
  T (h x y y) (C (T (T (T (C (T (C (C (T (h y v1 z) (C (T (h v18 v3 v3) (C (T (C (T (T (T (T (C (R (M v3 v3)) h26) (S (h v3 v1 z))) h20) (C (T (C (C (T (C h21 h19) (S h22)) h19) h26) (S h23)) h0)) (C (T (h v18 v18 y) (C (C (C (T (C (T h23 (C (C (T h22 (C (S h21) h19)) h19) h17)) h0) (S h20)) h0) h19) h19)) h0)) h19) (S (h y v18 v18))) h7)) h17)) h0) h0) (S (h y y v3))) (R x)) h16) h15) h5) h0)

@[equational_result]
theorem Equation492_implies_Equation684 (G: Type _) [Magma G] (h: Equation492 G) : Equation684 G := fun x y z =>
  let v0 := M y z
  let v1 := M v0 z
  have h2 := h v1 z v1
  have h3 := S h2
  have h4 := h z v0 y
  have h5 := S h4
  have h6 := h y z y
  have h7 := h y z v0
  have h8 := S h7
  have h9 := R v0
  have h10 := R y
  have h11 := C h10 (C h9 (C h9 (T (C h9 h6) h5)))
  have h12 := h v0 y v0
  have h13 := h v0 z v1
  have h14 := h z v1 v0
  have h15 := S h14
  have h16 := h v0 z v0
  have h17 := R v1
  have h18 := h v1 v0 v1
  have h19 := R z
  have h20 := C h9 (T (T (C h19 (T (T (T (C h19 (T h18 (C h9 (C h17 (C h17 (T (C h17 h16) h15)))))) (S h13)) h12) h11)) h8) h6)
  have h21 := h v0 v1 z
  have h22 := S h16
  have h23 := S h12
  have h24 := S h6
  have h25 := C h10 (C h9 (C h9 (T h4 (C h9 h24))))
  have h26 := C h19 (T (T (T h25 h23) h21) (C h17 (T (T (T h20 h5) h14) (C h17 (T (T h22 h21) (C h17 (T h20 h5)))))))
  have h27 := S h21
  have h28 := C h9 (T (T h24 h7) (C h19 (T (T (T h25 h23) h13) (C h19 (T (C h9 (C h17 (C h17 (T h14 (C h17 h22))))) (S h18))))))
  have h29 := T (T h2 (C h19 (T (T (T (C h17 (T (T (T (C h17 (T (T (C h17 (T h4 h28)) h27) h16)) h15) h4) h28)) h27) h12) h11))) h8
  T (h x v1 v1) (C h29 (C (R x) (T (T (T (T (C h17 (C h29 (C h9 (T h4 (C h9 (T (T (T h24 h7) h26) h3)))))) (S (h y v1 v0))) h7) h26) h3)))

@[equational_result]
theorem Equation543_implies_Equation455 (G: Type _) [Magma G] (h: Equation543 G) : Equation455 G := fun x y z =>
  let v0 := M z y
  let v1 := M z v0
  let v2 := M y v1
  let v3 := M x v2
  have h4 := h z z y
  have h5 := R y
  have h6 := R v2
  have h7 := R z
  have h8 := R v3
  have h9 := h v2 z z
  have h10 := S h9
  have h11 := S h4
  have h12 := C h7 (C h6 (C h7 h11))
  have h13 := h z z v2
  have h14 := h v0 z y
  have h15 := h v0 z v2
  have h16 := R v0
  have h17 := h v2 v0 z
  have h18 := h y z z
  have h19 := T h18 (C h7 (T (C h7 (C h5 (T (T (T (C h7 (T h13 h12)) h10) h17) (C h16 (T (C h7 (C h6 (C h16 h4))) (S h15)))))) (S h14)))
  have h20 := R x
  T (T (h x y y) (C h5 (C h5 (T (T (T (C h20 (C h5 (T (h y v3 x) (C h8 (C h20 (T (T (C h19 (R (M v3 x))) (C (R v1) (C h8 (h x y v1)))) (S (h y v1 v3)))))))) (S (h v3 x y))) (h v3 v3 y)) (C h8 (T (T (C h5 (T (C h8 (C h8 (T (h y y z) (C h19 (T (T (T (T (C h7 (C h19 (R (M y z)))) (C h7 (T (T (T (C (T (C h7 (T h14 (C h7 (C h5 (T (T (T (C h16 (T h15 (C h7 (C h6 (C h16 h11))))) (S h17)) h9) (C h7 (T (C h7 (C h6 (C h7 h4))) (S h13)))))))) (S h18)) (C h19 h4)) (S (h z y v1))) h13) h12))) h10) (h v2 v3 z)) (C h8 (T (C h7 (C h6 (C h8 h4))) (S (h v3 z v2))))))))) (S (h v1 v3 v3)))) (h v2 y z)) (C h5 (T (C h7 (C h6 (C h5 h4))) (S (h y z v2)))))))))) (S (h v3 y y))

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
theorem Equation2196_implies_Equation1943 (G: Type _) [Magma G] (h: Equation2196 G) : Equation1943 G := fun x y z =>
  let v0 := M x z
  let v1 := M y z
  let v2 := M y v1
  let v3 := M v2 v0
  let v4 := M v3 v0
  let v5 := M (M v1 v1) v1
  have h6 := h y z v0
  have h7 := S h6
  let v8 := M z v0
  let v9 := M v8 v0
  have h10 := h v9 v1 x
  have h11 := R (M (M v1 x) x)
  let v12 := M z y
  have h13 := R (M (M y x) x)
  let v14 := M z x
  have h15 := S (h v9 v0 y)
  have h16 := h x z v0
  let v17 := M (M v0 y) y
  have h18 := C (R v17) h16
  have h19 := R (M (M x x) x)
  have h20 := h v17 x x
  have h21 := S (h v17 v8 v0)
  have h22 := C h16 (h z v0 y)
  let v23 := M v0 z
  let v24 := M v23 z
  T (T (T (T (T (h x z v3) (C (R (M (M z v3) v3)) (T (T (T (T h22 h21) h20) (C h19 (T (T (T h18 h15) (h v9 v0 z)) (C (R v24) (S h16))))) (S (h v24 x x))))) (S (h v23 z v3))) (h v23 v0 v0)) (C (R (M (M v0 v0) v0)) (T (T (T (T (C (R v23) (T (T (T (T h22 h21) h20) (C h19 (T (T (T (T h18 h15) h10) (C h11 (T h7 (h y z x)))) (S (h (M v14 x) v1 x))))) (S (h v14 x x)))) (S (h z x z))) (h z y x)) (C h13 (T (T (T (T (h v12 y x) (C h13 (T (T (T (T (h (M v12 y) v1 x) (C h11 (T (S (h y z y)) h6))) (S h10)) (h v9 v1 v1)) (C (R v5) h7)))) (S (h v5 y x))) (h v5 v2 v0)) (C (R v4) (S (h y v1 v1)))))) (S (h v4 y x))))) (S (h v3 v0 v0))

@[equational_result]
theorem Equation2944_implies_Equation4305 (G: Type _) [Magma G] (h: Equation2944 G) : Equation4305 G := fun x y z =>
  let v0 := M y z
  have h1 := R v0
  have h2 := h y x y
  have h3 := S h2
  let v4 := M x y
  let v5 := M x v4
  let v6 := M v5 y
  have h7 := R v6
  have h8 := T (C h7 h3) h3
  have h9 := C (C h8 h1) h1
  have h10 := h y v6 v0
  have h11 := h y v6 z
  have h12 := S h11
  have h13 := R z
  have h14 := T h2 (C h7 h2)
  have h15 := C (C h14 h13) h13
  have h16 := R x
  have h17 := C (C h8 h13) h13
  have h18 := R v4
  let v19 := M (M x (M x v5)) v5
  have h20 := h v5 v19 x
  have h21 := h v5 x v5
  have h22 := R v19
  have h23 := h y x x
  have h24 := S h23
  have h25 := S h21
  have h26 := C (C (T (C h22 h25) h25) h16) h16
  have h27 := S (h x x x)
  let v28 := M (M x (M x x)) x
  T (T (T (T (T (T h20 h26) h24) h10) h9) (h (M (M y v0) v0) x v0)) (C (T (C (T (T (T (T (T (C (T (T (h x v28 v4) (C (T (T (T (C (T (C (R v28) h27) h27) h18) h20) h26) h24) h18)) (C (T (T (T h23 (C (C (T h21 (C h22 h21)) h16) h16)) (S h20)) (C h16 (C h16 (T h11 h17)))) h18)) (T (C h16 (T (T (T (C (C h14 h1) h1) (S h10)) h11) h17)) (C h16 (T h15 h12)))) (S (h (M v0 z) x v4))) h15) h12) h10) h9) h1) (S (h z y v0))) h1)

@[equational_result]
theorem Equation4197_implies_Equation4135 (G: Type _) [Magma G] (h: Equation4197 G) : Equation4135 G := fun x y z =>
  let v0 := M x y
  let v1 := M v0 z
  have h2 := R z
  let v3 := M v1 z
  have h4 := R v3
  have h5 := h z v1 z
  have h6 := R v1
  have h7 := h z z v0
  have h8 := h z v0 v1
  have h9 := C (T h8 (C (S h7) h6)) h2
  have h10 := T h9 (S h5)
  let v11 := M z v0
  let v12 := M v11 z
  have h13 := R v0
  have h14 := S h8
  have h15 := C h7 h6
  have h16 := C (T h15 h14) h2
  have h17 := h v11 z v3
  have h18 := S h17
  have h19 := h z v0 y
  have h20 := R y
  have h21 := h y z x
  have h22 := h z x v0
  have h23 := C (C (C h4 (T (C (T h22 (C (S h21) h13)) h20) (S h19))) h2) h4
  have h24 := h (M (M z x) y) z v3
  have h25 := h x y z
  have h26 := T (T (T h25 h24) h23) h18
  have h27 := S h25
  have h28 := S h24
  have h29 := C (C (C h4 (T h19 (C (T (C h21 h13) (S h22)) h20))) h2) h4
  T (T (T (T (T (T (T h25 h24) h23) h18) h9) (C (T (T h15 h14) (C h2 h26)) h2)) (C (T (T (T (T (T (T (C h2 (T (T (T h17 h29) h28) h27)) (h z v0 v0)) (C (T (T (h v1 v0 z) (C (T (C (T (T (T (T (T h5 h16) h17) h29) h28) h27) h26) (C h13 h10)) h2)) (C (C h13 (T h5 h16)) h2)) h13)) (S (h v12 z v0))) (h v12 z v3)) (C (C (C h4 h10) h2) h4)) (S (h (M z v1) z v3))) h2)) (S (h v1 z z))

@[equational_result]
theorem Equation492_implies_Equation711 (G: Type _) [Magma G] (h: Equation492 G) : Equation711 G := fun x y z =>
  let v0 := M x z
  let v1 := M v0 z
  let v2 := M y v1
  let v3 := M y v2
  have h4 := h v3 z v0
  have h5 := S h4
  have h6 := h v1 v1 y
  have h7 := R v0
  have h8 := R v3
  have h9 := C h8 (C h7 (S h6))
  have h10 := h v0 v3 v1
  have h11 := S (h v0 v1 y)
  have h12 := h z v0 z
  have h13 := R z
  have h14 := C h13 (T (C h8 (C h7 h6)) (S h10))
  have h15 := h v0 v3 z
  have h16 := C h8 (C h8 (T h15 (C h8 (T (C h7 (C h13 (C h13 (T h4 h14)))) (S h12)))))
  have h17 := C h7 (T (C h13 h16) (S (h v3 z v3)))
  have h18 := h z v0 v3
  have h19 := R v1
  have h20 := T (T (T (C h7 (T (h v1 z v1) (C h13 (C h19 (C h19 (T (C h19 (T h18 h17)) h11)))))) (S (h z v0 v1))) h18) h17
  have h21 := S h15
  have h22 := C h7 (C h13 (C h13 (T (C h13 (T h10 h9)) h5)))
  have h23 := R x
  T (T (T (T (T (h x v2 y) (C (R v2) (T (T (C h23 (C (R y) (T (T h4 h14) (C h13 (T (h v0 z x) (C h13 (T (C h7 (C h23 (T (h v0 v0 v3) (C h7 (C h7 (T (T h16 (C h8 (T (T (T (C h8 (T (T (T (C h8 (T h12 h22)) h21) (h v0 z v0)) (C h13 (C h7 h20)))) (S (h z v3 v0))) h12) h22))) h21)))))) (S (h x v0 v0))))))))) (S (h y x z))) (h y v1 y)))) (S (h v1 v2 y))) (h v1 z v0)) (C h13 (T (T (T (C h19 h20) h11) h10) h9))) h5

@[equational_result]
theorem Equation711_implies_Equation4162 (G: Type _) [Magma G] (h: Equation711 G) : Equation4162 G := fun x y z =>
  let v0 := M y x
  let v1 := M (M v0 z) z
  let v2 := M v1 (M (M v1 x) x)
  have h3 := h v1 x v2
  have h4 := S h3
  have h5 := R v2
  have h6 := h v1 v1 x
  have h7 := R x
  have h8 := C h7 (C h7 (T h6 (C h6 h5)))
  have h9 := h v0 x z
  let v10 := M v1 (M (M v1 v1) v1)
  have h11 := S (h v0 x v10)
  have h12 := R v10
  have h13 := S h6
  have h14 := T (T h3 (C h7 (C h7 (T (C h13 h5) h13)))) (S h9)
  have h15 := h v1 v1 v1
  have h16 := C (T h15 (C h14 h12)) h12
  let v17 := M x (M (M x x) x)
  have h18 := h x x x
  have h19 := R y
  let v20 := M y (M v0 x)
  let v21 := M x y
  have h22 := h y v21 v20
  have h23 := R v20
  have h24 := h y y x
  have h25 := T h24 (C h24 h23)
  have h26 := R v21
  have h27 := S h24
  have h28 := T (C h27 h23) h27
  have h29 := h y x v20
  T (T (T (T (C h7 (T (T (T h29 (C h7 (C h7 h28))) (h (M x v21) x v1)) (C h7 (T (T (T (T (T (T (C h7 (C (T (T (T (C (T (T (T (C h7 (C h7 h25)) (S h29)) h22) (C h26 (C h26 h28))) (R v1)) (C (T (C h26 (C h26 h25)) (S h22)) h14)) (C h19 (C h19 (T h18 (C h18 (R v17)))))) (S (h x y v17))) (T h15 h16))) h11) h9) h8) h4) h15) h16)))) h11) h9) h8) h4

@[equational_result]
theorem Equation684_implies_Equation4216 (G: Type _) [Magma G] (h: Equation684 G) : Equation4216 G := fun x y z =>
  let v0 := M z y
  let v1 := M v0 z
  let v2 := M v1 x
  have h3 := S (h v2 v2 x)
  let v4 := M v2 (M (M v2 x) x)
  let v5 := M x v2
  have h6 := S (h x x x)
  let v7 := M x (M (M x x) x)
  have h8 := R v1
  have h9 := R x
  let v10 := M y (M (M y x) x)
  have h11 := R v10
  have h12 := h y y x
  have h13 := R z
  have h14 := R y
  let v15 := M z (M v0 y)
  have h16 := h z z y
  have h17 := R v0
  have h18 := S (h z z x)
  let v19 := M z (M (M z x) x)
  have h20 := S h12
  let v21 := M x y
  have h22 := R v21
  let v23 := M v21 (M (M v21 x) x)
  let v24 := M x v21
  have h25 := h v21 v21 x
  T (T (h v21 x v21) (C h9 (T (T (T (T (T (h (M v21 (M v24 v21)) v0 v1) (C h17 (T (T (C (T (T (T (C h22 (C (R v24) (T h25 (C h25 (R v23))))) (S (h v24 v21 v23))) (C h9 (T (h v21 y v10) (C h14 (C h22 (T (C h20 h11) h20)))))) (S (h y x y))) (T (T (C (T (C h17 (T (h v1 z v19) (C h13 (C h8 (T (C h18 (R v19)) h18))))) (S (h z v0 z))) h8) (C h13 (C h17 (T h16 (C h16 (R v15)))))) (S (h v0 z v15)))) (C h14 (C h13 (T h12 (C h12 h11))))) (S (h z y v10))))) (h v1 x v7)) (C h9 (C h8 (T (C h6 (R v7)) h6)))) (h v5 v2 v4)) (C (R v2) (C (R v5) (T (C h3 (R v4)) h3)))))) (S (h v2 x v2))

@[equational_result]
theorem Equation2105_implies_Equation4497 (G: Type _) [Magma G] (h: Equation2105 G) : Equation4497 G := fun x y z =>
  let v0 := M y y
  let v1 := M z z
  let v2 := M v1 x
  have h3 := R (M v0 v0)
  have h4 := R v0
  have h5 := R v2
  let v6 := M x v0
  have h7 := R y
  have h8 := h y y y
  have h9 := S h8
  have h10 := h y v0 z
  have h11 := S h10
  have h12 := R v1
  have h13 := C h8 h12
  have h14 := h v1 y x
  have h15 := R (M x x)
  have h16 := h y v0 v2
  let v17 := M v2 v2
  have h18 := R v17
  have h19 := h v17 y x
  have h20 := C (T (T h19 (C (C (T (T (T (C h8 h18) (S h16)) h10) (C h9 h12)) h7) h15)) (S h14)) h5
  have h21 := h v2 v2 z
  have h22 := h z z z
  have h23 := T (T (T (T (C (C (T (T (h v0 z v0) (C (C (T (T (T (C h22 h4) (S (h z v1 y))) (h z v1 z)) (C (S h22) h12)) (R z)) h3)) (S (h v1 z v0))) (R x)) h4) (C (T h21 (C h20 h12)) h4)) (S (h v2 v1 y))) (h v2 v2 y)) (C (T h20 (C (T (T (h v1 y v6) (C (C (T (T (T h13 h11) (h y v0 y)) (C h9 h4)) h7) (R (M v6 v6)))) (S (h v0 y v6))) h5)) h4)
  T (T (T (T (C (T (T (T (T (h x v0 v2) (C h23 h18)) (S (h v2 v0 v2))) (h v2 v1 z)) (C (T (C (C (T (T h14 (C (C (T (T (T h13 h11) h16) (C h9 h18)) h7) h15)) (S h19)) h5) h12) (S h21)) h12)) h4) (S (h x v1 y))) (h x v0 v0)) (C h23 h3)) (S (h v2 v0 v0))

@[equational_result]
theorem Equation2789_implies_Equation1913 (G: Type _) [Magma G] (h: Equation2789 G) : Equation1913 G := fun x y z =>
  let v0 := M x z
  let v1 := M z y
  let v2 := M y v0
  let v3 := M v2 v1
  have h4 := R v3
  have h5 := h y z z
  have h6 := S h5
  have h7 := h z v1 v1
  have h8 := R v1
  have h9 := R z
  have h10 := h v1 (M (M x v1) v0) v1
  have h11 := h z x v1
  have h12 := R (M v1 v1)
  have h13 := h y z y
  have h14 := S h11
  have h15 := T h10 (C (C h14 h14) h8)
  have h16 := R x
  let v17 := M x x
  have h18 := S (h x x v0)
  have h19 := R v2
  have h20 := S (h y x v2)
  let v21 := M x v2
  have h22 := h v2 x v3
  T (T (h x v0 y) (C (C (R (M v0 y)) (T (h (M v0 x) v1 v3) (C (T (C (T (T (T (C (T (h v1 v2 v1) (C (R (M v3 v3)) (T (h v1 v2 v2) (C (T (C (C h22 h22) h4) (S (h v3 (M (M x v3) v21) v3))) h19)))) h4) (S (h v2 v3 v3))) (h v2 (M v21 (M x y)) v2)) (C (C h20 h20) h19)) (T (T (C h8 (T (C (T (T (h v0 (M (M x v0) v17) v0) (C (C h18 h18) (R v0))) (C (R v17) (C h16 (T h7 (C (T (C h12 (T (C h15 h9) h6)) (S h13)) h8))))) h16) (S (h (M y v1) x x)))) (C h15 (T (C (T h13 (C h12 (T h5 (C (T (C (C h11 h11) h8) (S h10)) h9)))) h8) (S h7)))) h6)) (S (h v0 y y))) h4))) (R y))) (S (h v3 v0 y))

@[equational_result]
theorem Equation2789_implies_Equation1996 (G: Type _) [Magma G] (h: Equation2789 G) : Equation1996 G := fun x y z =>
  let v0 := M z z
  let v1 := M (M y v0) (M y x)
  have h2 := h v1 v0 z
  have h3 := S h2
  let v4 := M x z
  have h5 := h z (M v4 v4) z
  have h6 := S h5
  have h7 := R z
  have h8 := h z x z
  have h9 := C (C h8 h8) h7
  have h10 := h (M v0 z) v0 v0
  have h11 := h v0 (M (M x v0) v4) v0
  have h12 := R v0
  have h13 := h z x v0
  have h14 := T (C (C h13 h13) h12) (S h11)
  have h15 := S h8
  have h16 := C (C h15 h15) h7
  have h17 := T h5 h16
  have h18 := C h12 h17
  have h19 := S h13
  have h20 := T h11 (C (C h19 h19) h12)
  have h21 := R v1
  have h22 := h z x v1
  have h23 := S h22
  have h24 := C (C h23 h23) h21
  have h25 := h v1 (M (M x v1) v4) v1
  have h26 := C (C h17 (T h25 h24)) (T (T (T (T (C h17 h20) (C (T h18 (C h20 h18)) h14)) (S h10)) h9) h6)
  have h27 := T h9 h6
  have h28 := C h12 h27
  have h29 := C h12 (T h2 (C (C h27 (T (C (C h22 h22) h21) (S h25))) (T (T (T (T h5 h16) h10) (C (T (C h14 h28) h28) h20)) (C h27 h14))))
  T (T (T (T (h x y v0) (C (T (T (T h25 h24) h29) (C h20 (T (T (T (T h26 h3) h25) h24) h29))) h12)) (S (h (M (M z v1) (M z v0)) v0 v0))) h26) h3

@[equational_result]
theorem Equation3131_implies_Equation2944 (G: Type _) [Magma G] (h: Equation3131 G) : Equation2944 G := fun x y z =>
  let v0 := M y x
  let v1 := M y v0
  let v2 := M (M v1 z) z
  have h3 := R y
  have h4 := h v2 v0 v2
  have h5 := R v0
  have h6 := R v2
  have h7 := h v0 y z
  have h8 := S h7
  have h9 := h y v2 v2
  have h10 := T (C (T h9 (C (C (C h8 h6) h6) h6)) h5) (S h4)
  have h11 := T h4 (C (T (C (C (C h7 h6) h6) h6) (S h9)) h5)
  have h12 := h y v1 y
  have h13 := S h12
  have h14 := R v1
  have h15 := h v0 y y
  have h16 := C h15 h14
  have h17 := C h8 h14
  have h18 := C (T (T h17 h16) h13) h10
  have h19 := C h18 h11
  have h20 := h y v2 v1
  have h21 := h y v0 v0
  have h22 := h v2 y v1
  have h23 := C h7 h14
  have h24 := C (S h15) h14
  have h25 := C (T (T h12 h24) h23) h11
  have h26 := h v2 y y
  have h27 := C (T (T (T (C (C (C (T h26 (C (T (C (T (C (T h25 (C (T (T (T (T h17 h16) h13) h20) h19) h14)) h3) (S h22)) h3) h8) h3)) h5) h5) h5) (S h21)) h20) h19) h11
  have h28 := S h20
  have h29 := C (T (T (T (T (C h25 h10) h28) h12) h24) h23) h14
  T (T (h x y v2) (C (T (T (T (C (R (M v0 v2)) h11) (C (T (T (T (C (T (T (h v0 v2 v0) h27) h29) h6) h28) h21) (C (C (C (T (C (T h7 (C (T h22 (C (T h29 h18) h3)) h3)) h3) (S h26)) h5) h5) h5)) h10)) h27) (C (C (R (M y v2)) h10) h10)) h3)) (S (h v2 y v2))

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
theorem Equation2196_implies_Equation4358 (G: Type _) [Magma G] (h: Equation2196 G) : Equation4358 G := fun x y z =>
  let v0 := M z y
  let v1 := M x v0
  let v2 := M (M v0 v1) v1
  have h3 := S (h v2 (M y v0) v0)
  have h4 := C (h z y v0) (h y v0 v1)
  let v5 := M v1 v0
  let v6 := M v5 v0
  let v7 := M (M x z) z
  have h8 := R v7
  let v9 := M y z
  have h10 := h y z v9
  have h11 := S h10
  let v12 := M z v9
  let v13 := M (M v9 v0) v0
  let v14 := M x v9
  let v15 := M v14 v9
  let v16 := M v15 v9
  have h17 := h z y v14
  let v18 := M (M y v14) v14
  have h19 := R (M (M v0 x) x)
  let v20 := M v9 z
  let v21 := M v20 z
  let v22 := M v12 v9
  T (T (h v14 v9 v0) (C (T (T (T (h v13 y x) (C (R (M (M y x) x)) (T (T (T (C (R v13) h10) (S (h v22 v9 v0))) (h v22 v9 z)) (C (R v21) h11)))) (S (h v21 y x))) (C (T (T (T (T (T (h v20 v0 x) (C h19 (S (h z y z)))) (C h19 h17)) (S (h v18 v0 x))) (h v18 v0 v1)) (C (R v2) (S h17))) (R z))) (T (T (T (T (T (T (h v15 v9 v9) (C (R (M (M v9 v9) v9)) (T (h v16 x z) (C h8 (T (T (T (C (R v16) (h x v9 v0)) (S (h v13 v14 v9))) (h v13 v12 v9)) (C h11 (S (h z v9 v0)))))))) (S (h v7 v9 v9))) (h v7 v0 v0)) (C (R (M (M v0 v0) v0)) (T (C h8 (T (T (T h4 h3) (h v2 v1 v0)) (C (R v6) (S (h x v0 v1))))) (S (h v6 x z))))) (S (h v5 v0 v0))) (C (R v1) (T h4 h3))))) (S (h v1 v2 z))

@[equational_result]
theorem Equation3211_implies_Equation3120 (G: Type _) [Magma G] (h: Equation3211 G) : Equation3120 G := fun x y z =>
  let v0 := M y x
  let v1 := M v0 y
  let v2 := M (M v1 z) z
  have h3 := h v2 v0 y
  have h4 := S h3
  have h5 := R v0
  have h6 := R v2
  have h7 := R y
  have h8 := h v1 v1 z
  have h9 := S h8
  have h10 := C (C h9 h7) h6
  have h11 := h y v2 v1
  have h12 := h y v1 v2
  have h13 := S h12
  have h14 := R v1
  have h15 := h v2 v2 v1
  have h16 := h v2 v0 v2
  have h17 := h v0 y v0
  have h18 := S h17
  have h19 := C (C (C (T h3 (C (T (C (C h8 h7) h6) (S h11)) h5)) h5) h5) h7
  have h20 := h y v2 v0
  have h21 := C (T (T (T (C (C (C (T h20 (C (T h19 h18) h6)) h6) h6) h5) (S h16)) h15) (C (C h9 h6) h6)) h7
  have h22 := h v0 y v2
  have h23 := h v0 y v1
  have h24 := h v1 v0 v1
  have h25 := S h22
  have h26 := C (C (C (T (C (T h17 (C (C (C (T (C (T h11 h10) h5) h4) h5) h5) h7)) h6) (S h20)) h6) h6) h5
  T (T (T (T (h x y y) (C (C (T (C (C (T h20 (C (T (T (T h19 h18) (h v0 v2 y)) (C (T (C (C (T (T (T (C (T h16 h26) h7) h25) h23) (C (T (C (C (C (T h12 (C (T (C (T (T (T (C (C h8 h6) h6) (S h15)) h16) h26) h7) h25) h14)) h14) h14) h5) (S h24)) h7)) h7) h5) (S (h y v0 y))) h6)) h6)) h7) h7) (S (h y y v2))) (R x)) h7)) (h v1 v0 y)) (C (T (T (T (C (T (T (T (C (T h24 (C (C (C (T (C (T h22 h21) h14) h13) h14) h14) h5)) h7) (S h23)) h22) h21) h14) h13) h11) h10) h5)) h4

@[equational_result]
theorem Equation1761_implies_Equation4210 (G: Type _) [Magma G] (h: Equation1761 G) : Equation4210 G := fun x y z =>
  let v0 := M (M z y) x
  let v1 := M v0 z
  have h2 := R v1
  let v3 := M v1 v1
  let v4 := M x y
  have h5 := h y y v4
  have h6 := S h5
  have h7 := R y
  have h8 := h x v0 z
  have h9 := S h8
  have h10 := h z y x
  have h11 := R (M x v0)
  have h12 := h y x v0
  have h13 := C h2 (T h12 (C h11 (S h10)))
  have h14 := R (M y y)
  have h15 := h v1 y y
  have h16 := T h15 (C h14 (C (T h13 h9) h7))
  have h17 := h v4 v1 y
  have h18 := R (M y v4)
  let v19 := M v4 v1
  have h20 := R v19
  have h21 := h y v4 v1
  have h22 := T h21 (C h20 (T (C h18 h16) h6))
  have h23 := C h2 (T (C h11 h10) (S h12))
  have h24 := h x y v1
  have h25 := T (C h14 (C (T h8 h23) h7)) (S h15)
  have h26 := T (C h20 (T h5 (C h18 h25))) (S h21)
  let v27 := M y v1
  have h28 := h v27 v19 y
  have h29 := C (T h28 (C h26 (T (C (T (T (S h24) h8) h23) h22) (S h17)))) h16
  have h30 := R v3
  T (T (h v4 v1 v1) (C h30 (C (T (T (h v19 y v1) (C (R v27) (T (T (C h26 h2) (C (T h5 (C (T (C h22 (T h17 (C (T (T h13 h9) h24) h26))) (S h28)) h25)) h2)) (C (T (h (M v27 v1) v1 v1) (C h30 (T (T (C (C (T h29 h6) h2) h2) h29) h6))) h2)))) (S (h v3 y v1))) h2))) (S (h v1 v1 v1))

@[equational_result]
theorem Equation2714_implies_Equation4362 (G: Type _) [Magma G] (h: Equation2714 G) : Equation4362 G := fun x y z =>
  let v0 := M x z
  let v1 := M y z
  let v2 := M x v1
  let v3 := M y v0
  have h4 := R v0
  let v5 := M v2 v0
  have h6 := R v5
  let v7 := M v2 v3
  have h8 := R z
  have h9 := R v1
  have h10 := S (h y x v1)
  let v11 := M x x
  have h12 := R v2
  have h13 := h x x v2
  have h14 := T (h x x v1) (C (T (C (C h13 h13) h12) (S (h v2 (M v11 (M x v2)) v2))) h9)
  have h15 := h v0 (M v11 (M x v0)) v0
  have h16 := h x x v0
  have h17 := S h16
  have h18 := C (C h17 h17) h4
  let v19 := M v0 v0
  have h20 := T (C (T h15 h18) h8) (S (h x x z))
  let v21 := M v2 v2
  T (T (h v2 v2 v0) (C (C (T (T (T (T (T (T (T (h v21 x v1) (C (T (C (C h14 (R v21)) h12) (S (h v1 v2 v2))) h9)) (h (M v1 v1) v0 z)) (C (T (C (C h4 (T (C (T (h v1 x x) (C (R (M v2 v11)) h14)) h9) (S (h v11 v2 v1)))) h20) (S (h z x x))) h8)) (C (T (h z v0 v0) (C (C h20 (R v19)) h4)) h8)) (S (h v19 x z))) (C (T (T (T h15 h18) (h (M v11 v0) v2 v3)) (C (C (T (T (T (T (C h12 (T (C (C h16 h16) h4) (S h15))) (h v5 x z)) (C (T (C (C h14 h6) h4) (S (h v1 v2 v0))) h8)) (C (T (h v1 (M (M x y) v2) v1) (C (C h10 h10) h9)) h8)) (S (h y y z))) (R v7)) (R v3))) h4)) (S (h v7 y v0))) h6) h4)) (S (h v3 v2 v0))

