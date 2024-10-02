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
theorem Equation2944_implies_Equation1983 (G: Type _) [Magma G] (h: Equation2944 G) : Equation1983 G := fun x y z =>
  let v0 := M z x
  let v1 := M z y
  let v2 := M y v1
  let v3 := M v2 v0
  have h4 := R v3
  let v5 := M (M x (M x z)) z
  have h6 := h z v5 v1
  have h7 := S h6
  have h8 := R v1
  have h9 := h z x z
  have h10 := R v5
  have h11 := C (C (T h9 (C h10 h9)) h8) h8
  let v12 := M (M x (M x y)) y
  have h13 := h y v12 v1
  have h14 := S h13
  have h15 := h y x y
  have h16 := R v12
  have h17 := C (C (T h15 (C h16 h15)) h8) h8
  have h18 := R z
  have h19 := C h18 (T h17 h14)
  have h20 := C (C h18 h19) h8
  have h21 := S h15
  have h22 := C (C (T (C h16 h21) h21) h8) h8
  have h23 := C h18 (T h13 h22)
  have h24 := h (M v2 v1) z v1
  have h25 := C (T (T (T h13 h22) h24) (C (T (T h20 h11) h7) h23)) h8
  let v26 := M (M x (M x v2)) v2
  have h27 := h v2 x v2
  have h28 := C (C h18 h23) h8
  have h29 := S h9
  have h30 := C (C (T (C h10 h29) h29) h8) h8
  T (T (h x z v3) (C (C (T (C (T (T (T h6 h30) h28) (C (T (T (T (C (T (T h6 h30) h28) h19) (S h24)) h17) h14) h8)) (T (h v0 v2 v3) (C (T (T (T (T (T (C (C (T h27 (C (R v26) h27)) h4) h4) (S (h v2 v26 v3))) h25) h20) h11) h7) h4))) (C (T (T (T h25 h20) h11) h7) (R (M z v3)))) h4) h4)) (S (h v3 z v3))

@[equational_result]
theorem Equation3211_implies_Equation572 (G: Type _) [Magma G] (h: Equation3211 G) : Equation572 G := fun x y z =>
  let v0 := M x y
  let v1 := M z v0
  let v2 := M z v1
  let v3 := M y v2
  have h4 := R v0
  have h5 := R v3
  have h6 := R v2
  have h7 := R z
  have h8 := R v1
  have h9 := h v2 z v2
  have h10 := h z v1 v0
  have h11 := S h10
  have h12 := h v0 z v0
  have h13 := R y
  have h14 := h x y v2
  have h15 := R x
  have h16 := h y v2 x
  have h17 := h v2 x y
  have h18 := h v0 v0 v1
  have h19 := S h12
  have h20 := h y v2 v0
  have h21 := h x y x
  have h22 := h v2 x v2
  have h23 := h v1 v2 y
  have h24 := h z v1 v2
  T (T (h x v0 y) (C (T (T (T (S (h y x y)) (h y v3 v2)) (C (S (h v2 y v2)) h5)) (C (T (h v2 v2 z) (C (C (T (C (T (T (C (C (T (h z z v1) (C (C (T (C (T h9 (C (C (C (T (C (T h10 (C (T h19 (C (T h14 (C (T (C (C (C (T h16 (C (T (C (C (C (T h17 (C (T (C (C (T h18 (C (C (C (T (C h12 h8) h11) h8) h4) h4)) h13) h6) (S h20)) h15)) h15) h15) h13) (S h21)) h6)) h6) h6) h15) (S h22)) h13)) h13)) h8)) h6) (S h23)) h6) h6) h7)) h8) (S h24)) h7) h7)) h8) h7) (S (h v1 z z))) (C (T h24 (C (T (C (C (C (T h23 (C (T (C (T (C (T (C (T h22 (C (C (C (T (C (T h21 (C (C (C (T (C (T h20 (C (C (T (C (C (C (T h10 (C h19 h8)) h8) h4) h4) (S h18)) h13) h6)) h15) (S h17)) h15) h15) h13)) h6) (S h16)) h6) h6) h15)) h13) (S h14)) h13) h12) h8) h11) h6)) h6) h6) h7) (S h9)) h8)) h4)) h7) (S (h v0 z v1))) h6) h6)) h5)) h4)) (S (h v3 v0 v2))

@[equational_result]
theorem Equation928_implies_Equation4673 (G: Type _) [Magma G] (h: Equation928 G) : Equation4673 G := fun x y z =>
  let v0 := M y y
  let v1 := M x z
  let v2 := M v1 y
  have h3 := h y v2 y
  have h4 := R v2
  let v5 := M x y
  have h6 := S (h y v2 x)
  let v7 := M y x
  have h8 := T (h v2 v2 (M (M v2 x) v7)) (C h4 (C h6 h6))
  let v9 := M v2 v2
  have h10 := R v1
  have h11 := T (C h10 h8) (S (h y v1 y))
  have h12 := R v5
  have h13 := h y v5 x
  have h14 := R x
  have h15 := T (h y x y) (C h14 (T (C h12 (C h13 h13)) (S (h v5 v5 (M (M v5 x) v7)))))
  let v16 := M v5 v5
  let v17 := M v5 z
  let v18 := M v5 v2
  have h19 := R v18
  have h20 := h z v1 x
  let v21 := M v17 v2
  T (T (T (T (h v17 v5 v2) (C h12 (C h19 (T (T (T (T (T (T (T (T (h v21 v5 z) (C h12 (T (C (R v17) (C (R v21) (T (T (h z x z) (C h14 (T (T (T (C h10 (C h20 h20)) (S (h v1 v1 (M (M v1 x) (M z x))))) (h v1 v5 v2)) (C h12 (C h19 h11))))) (S (h v18 x y))))) (S (h v5 v17 v2))))) (h v16 x y)) (C h14 (T (C h12 (C (R v16) h15)) (S (h x v5 v5))))) (C h14 (T (h x y y) (C h15 (C (T (h v0 v1 v2) (C h10 (T (C h11 (R (M v0 v2))) (S (h v1 y y))))) h12))))) (S (h (M v1 v1) x v5))) (C h10 (T (h v1 v2 v2) (C h4 (C (R v9) h11))))) (S (h v9 v1 y))) (C h8 h4))))) (S (h (M v2 v0) v5 v2))) (C h4 (C h3 h3))) (S (h v2 v2 (M (M v2 y) v0)))

@[equational_result]
theorem Equation1537_implies_Equation2355 (G: Type _) [Magma G] (h: Equation1537 G) : Equation2355 G := fun x y z =>
  let v0 := M x x
  have h1 := h z z z
  have h2 := S h1
  have h3 := R v0
  let v4 := M z z
  have h5 := R z
  let v6 := M y v4
  have h7 := h z v6 v4
  let v8 := M v6 v6
  have h9 := R v8
  have h10 := C h5 (T (C h9 h1) (S h7))
  have h11 := h v8 x z
  have h12 := R v6
  have h13 := h v4 x z
  have h14 := S h13
  have h15 := R v4
  have h16 := h z z v4
  have h17 := C h5 (T h16 (C h15 h2))
  have h18 := h z y v4
  let v19 := M y y
  have h20 := R v19
  have h21 := h v19 x z
  have h22 := R y
  have h23 := h (M y v19) z v6
  have h24 := T (T (h y z y) (C h15 (T h23 (C h15 (C h12 (T (T (T (C (C h22 (T (T h21 (C h3 (T (C h5 (T (C h20 h1) (S h18))) h17))) h14)) h12) h11) (C h3 (T h10 h17))) h14)))))) (S (h v6 z v4))
  let v25 := M y v6
  let v26 := M v25 x
  have h27 := C h5 (T (C h15 h1) (S h16))
  T (h x y v25) (C (C h22 h24) (T (C (C h22 (T (T (h v6 v26 v4) (C (R (M v26 v26)) (T (C h15 (C h12 (T (T (T h13 (C h3 (T h27 (C h5 (T h7 (C h9 h2)))))) (S h11)) (C (C h22 (T (T h13 (C h3 (T h27 (C h5 (T h18 (C h20 h2)))))) (S h21))) h12)))) (S h23)))) (S (h y v26 y)))) (C (R x) (T (T (T (C h24 h12) h11) (C h3 (T h10 (C h5 (T (h z x v4) (C h3 h2)))))) (S (h v0 x z))))) (S (h x y x))))

@[equational_result]
theorem Equation3182_implies_Equation3214 (G: Type _) [Magma G] (h: Equation3182 G) : Equation3214 G := fun x y z =>
  let v0 := M y z
  let v1 := M v0 z
  let v2 := M v1 y
  let v3 := M v2 x
  have h4 := R x
  have h5 := R v2
  have h6 := R v3
  have h7 := h v3 v2 z
  have h8 := R z
  have h9 := h z y z
  have h10 := h v2 z v3
  have h11 := R y
  have h12 := h y z v1
  have h13 := R v1
  have h14 := S h9
  have h15 := h z v1 y
  have h16 := h z v2 z
  have h17 := C (T (C (C (C h9 h8) h5) h8) (S h16)) h8
  have h18 := h v2 z z
  have h19 := R v0
  have h20 := S (h y v2 z)
  have h21 := C (C (C h9 h11) h5) h8
  have h22 := h v2 z y
  T (T (h x v2 x) (C (C (T (T (T (C (T (h v3 v2 v2) (C (C (T (C (T (T (C (T h22 (C (T (T (T h21 h20) (h y v2 v2)) (C (C (T (C (C (T h22 (C (T (T (T (T (T h21 h20) h12) (C (C (T (C (C h9 h13) h11) (S h15)) h8) h13)) (C (T (C (T h16 (C (C (C h14 h8) h5) h8)) h8) (S h18)) h13)) (C h5 (T (C (T (h v0 y z) (C (C (T (T (T (C (T (h v0 v2 z) (C (C (C h14 h19) h5) h8)) h19) (S (h v2 z v0))) h18) h17) h11) h8)) h8) (S (h y z z))))) h11)) h5) h11) (S (h y v2 y))) h5) h5)) h11)) h5) (S (h v2 y v2))) (C (T (h v1 v3 v3) (C (C (T (T (C (T (T (T (C (T h7 (C (C (C h14 h6) h5) h8)) h6) (S h10)) h18) h17) h13) (C (C (T h15 (C (C h14 h13) h11)) h8) h13)) (S h12)) h6) h6)) h11)) h6) (S (h v3 y v3))) h5) h5)) h4) (S (h v2 v2 x))) h10) (C (T (C (C (C h9 h6) h5) h8) (S h7)) h6)) h5) h4)) (S (h v3 v2 x))

@[equational_result]
theorem Equation508_implies_Equation1137 (G: Type _) [Magma G] (h: Equation508 G) : Equation1137 G := fun x y z =>
  let v0 := M z z
  have h1 := h x x v0
  have h2 := h v0 x z
  let v3 := M y v0
  let v4 := M v3 x
  have h5 := h v0 v0 v0
  have h6 := S h5
  have h7 := h v0 v0 z
  let v8 := M y v4
  have h9 := h v0 v8 v3
  have h10 := S h9
  have h11 := h v0 v3 z
  have h12 := R v0
  have h13 := C h12 h7
  have h14 := R v3
  have h15 := C h12 (T h11 (C h14 (T (C h14 (T (T h13 h6) h11)) (S (h v3 v3 v0)))))
  have h16 := C h12 (S h7)
  have h17 := h v0 v8 z
  have h18 := R v8
  have h19 := h v8 v8 v0
  have h20 := C h18 (T h19 (C h18 (T (T (T (S h17) h5) h16) h15)))
  have h21 := R v4
  have h22 := R x
  have h23 := S h11
  have h24 := h v0 y z
  have h25 := R y
  have h26 := h y y v0
  have h27 := C h14 (C (T h26 (C h25 (S h24))) (R (M v0 v0)))
  have h28 := T h5 h16
  have h29 := C h14 (C h25 h28)
  T (h x v3 x) (C (T (C h25 h24) (S h26)) (C h14 (T (C h22 (T (T (C h22 (T (T (T (T (T h1 (C h22 (S h2))) (C h22 h28)) (C h22 h15)) (C h22 (C h12 (T (T (T (T h29 h27) h23) h9) (C h18 (T (C h18 (T (T (T (C h12 (T (T h29 h27) h23)) h13) h6) h17)) (S h19))))))) (C h22 (C h12 (T (T (T h20 h10) (h v0 v4 v8)) (C h21 (T (C h21 (T (T (C h12 (T (T h20 h10) h7)) h6) (h v0 v4 z))) (S (h v4 v4 v0))))))))) (S (h v0 x v4))) h2)) (S h1))))

@[equational_result]
theorem Equation1507_implies_Equation1876 (G: Type _) [Magma G] (h: Equation1507 G) : Equation1876 G := fun x y z =>
  let v0 := M z y
  let v1 := M y z
  let v2 := M x v1
  let v3 := M v2 v0
  have h4 := h v0 v2 v3
  have h5 := S h4
  let v6 := M v3 v2
  let v7 := M v1 (M v1 v3)
  have h8 := R (M x (M x v0))
  let v9 := M v3 v6
  have h10 := R (M x (M x v3))
  let v11 := M v0 (M v0 v2)
  let v12 := M x v2
  have h13 := h z y v0
  let v14 := M v0 (M v0 y)
  let v15 := M v1 (M v1 v1)
  have h16 := h y z v1
  let v17 := M v1 (M v1 z)
  let v18 := M v0 (M v0 v0)
  have h19 := h v1 x v3
  let v20 := M v3 (M v3 x)
  let v21 := M v0 x
  T (T (T (T (h x v0 x) (C (T (T (T (T (T (T (T (T (h v21 v0 v0) (C (T (T (T (T (h (M v0 v21) v2 x) (C (T (S (h v1 x v0)) h19) (R (M x v12)))) (S (h v20 v2 x))) (h v20 v2 v0)) (C (S h19) (R v11))) (T (T (T (T (T (T (T (h v18 y v0) (C (T (T (T (T (C h16 (R v18)) (S (h v17 v0 v0))) (h v17 v0 x)) (C (T (S h16) (h y z y)) h8)) (S (h (M y v1) v0 x))) (R v14))) (S (h v1 y v0))) (C (h y v1 v1) (h z y v1))) (S (h v15 (M v1 y) v1))) (h v15 z x)) (C (T (T (T (C h13 (R v15)) (S (h v14 v1 v1))) (h v14 v1 x)) (C (S h13) (R v12))) (R (M x (M x z))))) (S (h v12 z x))))) (S (h v11 v1 x))) (h v11 v3 x)) (C (S (h v0 v2 v0)) h10)) (C h4 h10)) (S (h v9 v3 x))) (h v9 v3 v1)) (C h5 (R v7))) h8)) (S (h v7 v0 x))) (h v7 v6 v3)) (C (S (h v2 v3 v1)) h5)

@[equational_result]
theorem Equation684_implies_Equation2373 (G: Type _) [Magma G] (h: Equation684 G) : Equation2373 G := fun x y z =>
  let v0 := M y (M (M y y) y)
  let v1 := M y (M z (M x z))
  let v2 := M v1 y
  have h3 := S (h v2 y v0)
  have h4 := R v0
  have h5 := h y y y
  have h6 := R v2
  have h7 := R y
  have h8 := C h7 (C h6 (T h5 (C h5 h4)))
  have h9 := h y v1 y
  have h10 := S h9
  have h11 := h y y x
  have h12 := S h11
  let v13 := M y x
  let v14 := M y (M v13 x)
  have h15 := R v14
  have h16 := R v1
  have h17 := C h16 (T (h v2 y v14) (C h7 (C h6 (T (C h12 h15) h12))))
  have h18 := S (h v2 v2 x)
  let v19 := M v2 (M (M v2 x) x)
  let v20 := M y v2
  have h21 := S h5
  have h22 := S (h z z x)
  let v23 := M z (M (M z x) x)
  have h24 := R x
  let v25 := M x (M (M x x) x)
  have h26 := h x x x
  T (T (T (T (h x y x) (C h7 (T (T (T (T (C h24 (C (R v13) (T h26 (C h26 (R v25))))) (S (h v13 x v25))) (C h7 (T (h x z v23) (C (R z) (C h24 (T (C h22 (R v23)) h22)))))) (h v1 y v0)) (C (T h9 (C h16 (T h8 h3))) (C h16 (T (C h21 h4) h21)))))) (C h7 (T (T (C (T h17 h10) h6) (h v20 v2 v19)) (C h6 (T (T (T (C (R v20) (T (C h18 (R v19)) h18)) (C (T (C h7 (C h16 (T h11 (C h11 h15)))) (S (h v1 y v14))) h6)) h17) h10))))) h8) h3

@[equational_result]
theorem Equation4197_implies_Equation3997 (G: Type _) [Magma G] (h: Equation4197 G) : Equation3997 G := fun x y z =>
  let v0 := M x z
  let v1 := M z v0
  let v2 := M v1 y
  have h3 := R v2
  have h4 := R v1
  have h5 := R y
  have h6 := h z v0 y
  have h7 := h (M (M y z) v0) y v2
  have h8 := R v0
  have h9 := h y z v1
  have h10 := h v0 y z
  have h11 := h y v1 v0
  have h12 := h (M y v1) y v2
  have h13 := h z v0 x
  have h14 := S h13
  have h15 := R x
  have h16 := h x x v0
  have h17 := S h16
  have h18 := C (T (T (T (T (S (h z v1 x)) (h z v1 v0)) (C (T (T (C (h v0 z z) h4) (S (h z z v1))) (h z z x)) h8)) (S (h z x v0))) (h z x x)) h8
  have h19 := h v1 x v0
  have h20 := T (T h19 h18) h17
  let v21 := M v1 x
  have h22 := h v0 x v0
  T (T (T (T (h x y v1) (h (M v21 y) v1 v2)) (C (C (C h3 (T (C (T (T (T (T h19 h18) h17) (h x x v1)) (C (T (T (C h20 h15) (C (T h16 (C (T (T (C (T h22 (C h14 h8)) h15) (C (T (T (T (T (T (C h13 h8) (S h22)) (h v0 x z)) (h v21 z v2)) (C (C (C h3 h20) (R z)) h3)) (S (h (M x x) z v2))) h15)) (S (h x z x))) h8)) h15)) h14) (T (T (T h6 h7) (C (C (C h3 (T (C (T h9 (C (S h10) h4)) h8) (S h11))) h5) h3)) (S h12)))) h5) (C (C h4 (T (T (T h12 (C (C (C h3 (T h11 (C (T (C h10 h4) (S h9)) h8))) h5) h3)) (S h7)) (S h6))) h5))) h4) h3)) (S (h (M (M v1 v1) y) v1 v2))) (S (h v1 y v1))

@[equational_result]
theorem Equation572_implies_Equation2170 (G: Type _) [Magma G] (h: Equation572 G) : Equation2170 G := fun x y z =>
  let v0 := M y z
  let v1 := M v0 x
  let v2 := M v1 (M z y)
  have h3 := h v2 v0 v0
  have h4 := S h3
  have h5 := h z y v1
  have h6 := R y
  have h7 := C h6 (S h5)
  have h8 := R v2
  have h9 := C h8 h7
  have h10 := h v1 v2 y
  have h11 := h v1 v2 v2
  have h12 := S h11
  have h13 := T h10 h9
  have h14 := R v0
  have h15 := R v1
  have h16 := C h15 (T (C h14 (C h14 (C h14 h13))) h4)
  have h17 := h v0 v1 v0
  have h18 := h v0 x v2
  have h19 := C h6 h5
  have h20 := C h8 h19
  have h21 := T h20 (S h10)
  have h22 := S h17
  have h23 := C h15 (T h3 (C h14 (C h14 (C h14 h21))))
  have h24 := R x
  have h25 := C h8 (T (T h7 h17) h16)
  have h26 := C h8 (T h20 h25)
  have h27 := C h8 h13
  have h28 := C h8 (T (T (T h23 h22) h18) (C h24 (T (T (C h8 h27) (C h8 h26)) h12)))
  have h29 := C h8 (T (C h8 (T (T (T (T (C h24 (T (T h17 h16) (C h15 (T (h v2 v1 v1) (C h15 (C h15 (T (C h15 (T (T h27 h26) (C h8 h28))) (S (h x v1 v2))))))))) (S (h v1 x v1))) h10) h25) h28)) (C h8 (C h8 (T (T (T (C h24 (T (T h11 (C h8 (C h8 (T (C h8 (T (T h23 h22) h19)) h9)))) (C h8 (C h8 h21)))) (S h18)) h17) h16))))
  have h30 := h x v0 v2
  T (T h30 (C h14 (T (T h29 h12) (C h14 (T h30 (C h14 (T (T (T h29 h12) h10) h9))))))) h4

@[equational_result]
theorem Equation3131_implies_Equation14 (G: Type _) [Magma G] (h: Equation3131 G) : Equation14 G := fun x y =>
  let v0 := M x y
  let v1 := M y v0
  have h2 := h v1 y v1
  have h3 := S h2
  have h4 := R y
  have h5 := R v1
  have h6 := h y v1 y
  have h7 := S h6
  have h8 := h v0 y y
  have h9 := C h8 h5
  have h10 := h v0 v1 v0
  have h11 := S h10
  have h12 := R v0
  have h13 := C (C (C (T h9 h7) h12) h12) h12
  have h14 := h v1 v0 v0
  have h15 := C (T h14 h13) h12
  have h16 := C h15 h5
  have h17 := h v0 v1 v1
  have h18 := C (C (T (T (T h16 h11) h17) (C (T (T (C (T h16 h11) h5) h9) h7) h5)) h5) h5
  have h19 := S h14
  have h20 := C (S h8) h5
  have h21 := C (C (C (T h6 h20) h12) h12) h12
  have h22 := C (T h21 h19) h12
  have h23 := C (T h17 h18) h4
  have h24 := C (T (T (T h23 h3) h14) h13) h12
  have h25 := S h17
  have h26 := C h22 h5
  have h27 := C (T (C (C (T (T (T (C (T (T h6 h20) (C (T h10 h26) h5)) h5) h25) h10) h26) h5) h5) h25) h4
  have h28 := C (T (T (T (T (C (T h24 h22) h12) h21) h19) h2) h27) h12
  have h29 := h y v0 v0
  have h30 := R x
  have h31 := C (T (T (T h21 h19) h2) h27) h12
  T (T (h x y v1) (C (T (T (T (T (C (T (T (T (T (T (C (T (C (T (T (T h29 h28) h24) h22) h30) (C (T (T (T (T (T h15 h31) (C (T (T (T (T h23 h3) h14) h13) (C (T h15 h31) h12)) h12)) (S h29)) (h y x y)) (C (C (T h23 h3) h4) h30)) h30)) h5) (S (h y v1 x))) h29) h28) h24) h22) h5) h16) h11) h17) h18) h4)) h3

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
theorem Equation1964_implies_Equation3398 (G: Type _) [Magma G] (h: Equation1964 G) : Equation3398 G := fun x y z =>
  let v0 := M y (M x z)
  let v1 := M z v0
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
  have h14 := h x v0 y
  have h15 := R (M v0 y)
  have h16 := h z y x
  have h17 := C (T (C h16 h15) (S h14)) h13
  have h18 := h y z v0
  have h19 := R x
  have h20 := T (C (C h19 (T h18 h17)) h12) (S h11)
  have h21 := T (C (T h5 (C h20 h10)) h9) (S h7)
  have h22 := h v4 x v1
  have h23 := h y v1 x
  have h24 := S h18
  have h25 := C (T h14 (C (S h16) h15)) h13
  have h26 := T h11 (C (C h19 (T h25 h24)) h12)
  have h27 := T h7 (C (T (C h26 h10) h6) h9)
  have h28 := h v3 x v8
  have h29 := C h26 (T h28 (C (T (C h27 (T (T (S h23) h18) h17)) (S h22)) h21))
  T (T (h v4 v0 v1) (C (C (R v0) (T (T (h v8 v1 x) (C (T (T (C h13 h21) (C h13 (T h5 (C h20 (T (C (T h22 (C h21 (T (T h25 h24) h23))) h27) (S h28)))))) (C h13 (T (h (M v1 v3) v1 v1) (C (T (T (C h13 (C h13 (T h29 h6))) h29) h6) (R v2))))) (R v3))) (S (h v2 v1 x)))) (R (M v0 v1)))) (S (h v1 v0 v1))

@[equational_result]
theorem Equation2113_implies_Equation1929 (G: Type _) [Magma G] (h: Equation2113 G) : Equation1929 G := fun x y z =>
  let v0 := M z z
  let v1 := M y x
  let v2 := M y v1
  let v3 := M v2 v0
  have h4 := h v3 v2 v0
  let v5 := M v3 v3
  have h6 := R v5
  have h7 := S (h v0 v2 v0)
  have h8 := C h7 h6
  have h9 := h v0 v3 v3
  let v10 := M v0 v0
  have h11 := R v10
  have h12 := S (h z z z)
  have h13 := C h12 h11
  have h14 := h z v0 v0
  have h15 := S (h v3 y v1)
  have h16 := h v2 z z
  have h17 := R v2
  have h18 := S (h v2 y x)
  have h19 := S (h v1 v2 v1)
  let v20 := M v2 v1
  have h21 := T (h v1 (M (M y v2) x) v1) (C (T (T (C h18 (R v1)) (h v20 (M v20 v1) v20)) (C (T (C (T h19 (h v1 y x)) (R v20)) (S (h x v2 v1))) h19)) h18)
  let v22 := M v1 v2
  have h23 := h x v1 v2
  T (T (T (T (T (T (h x y x) (C (T (T (C (T (h v1 v1 v2) (C (T (S (h x y v1)) h23) (R v22))) h23) (S (h v22 (M (M v1 x) v2) v22))) (C h21 h17)) h21)) (S (h v2 (M x v1) v2))) (h v2 (M (M y v3) v1) v2)) (C (T (T (C h15 h17) (C (C h16 (R v0)) h16)) (S (h v0 (M (M z v2) z) v0))) h15)) (C (T (T (T (T (C (T h14 (C (T (T h12 h14) h13) h11)) (T h14 h13)) (S (h v10 z v10))) (C (T h9 (C (T (T h7 h9) h8) h6)) (T h9 h8))) (S (h v5 v0 v5))) (C h4 (R v3))) h4)) (S (h v3 (M (M v2 v3) v0) v3))

@[equational_result]
theorem Equation3211_implies_Equation1507 (G: Type _) [Magma G] (h: Equation3211 G) : Equation1507 G := fun x y z =>
  let v0 := M z y
  let v1 := M z v0
  let v2 := M y x
  let v3 := M v2 v1
  have h4 := R y
  have h5 := R v3
  have h6 := R v0
  have h7 := h y z y
  have h8 := h z v0 y
  have h9 := C (T h8 (C (S h7) h6)) h6
  have h10 := R z
  have h11 := R v1
  have h12 := S h8
  have h13 := C h7 h6
  have h14 := h y z z
  have h15 := h z y v0
  have h16 := h v1 v0 v1
  have h17 := S h16
  have h18 := h v0 z v0
  have h19 := C (S h18) h11
  have h20 := h z v1 v0
  have h21 := C (C (C (T h20 h19) h11) h11) h6
  have h22 := h v0 z v1
  have h23 := h z z y
  have h24 := S h22
  have h25 := C (C (C (T (C h18 h11) (S h20)) h11) h11) h6
  have h26 := C (T (C (T (T (C (T h16 h25) h10) h24) (C (T h23 (C (C (T (C (T h22 (C (T (T h21 h17) h9) h10)) h4) (S h15)) h10) h10)) h4)) h10) (S h14)) h6
  have h27 := h v0 v1 z
  have h28 := C (T (C (C (T h15 (C (T (C (T (T (C (T h13 h12) h6) h16) h25) h10) h24) h4)) h10) h10) (S h23)) h4
  T (T (h x y y) (C (T (T (T (C (T (C (C (T h14 (C (T (T h28 h22) (C (T h21 h17) h10)) h10)) h4) (T (T h14 (C (T (T h28 h27) (C (T (T (T (T (T h26 h13) h12) h20) h19) (C (T h27 (C (T (T h26 h13) h12) h11)) h11)) h11)) h10)) (S (h v1 z v1)))) (S (h y v1 z))) (R x)) (h v2 v3 v1)) (C (S (h v1 v2 v1)) h5)) (C h9 h5)) h4)) (S (h v3 y v0))

@[equational_result]
theorem Equation3385_implies_Equation3534 (G: Type _) [Magma G] (h: Equation3385 G) : Equation3534 G := fun x y z =>
  let v0 := M z y
  let v1 := M v0 z
  let v2 := M x v1
  have h3 := R v2
  have h4 := R v1
  have h5 := h v0 z x
  have h6 := h x (M v0 (M z x)) v2
  have h7 := h z x v1
  have h8 := h x v0 z
  have h9 := R v0
  have h10 := h v1 x v0
  have h11 := R x
  have h12 := h x (M v1 x) v2
  have h13 := h v0 z y
  have h14 := S h13
  have h15 := h y y v0
  have h16 := S h15
  have h17 := C h9 (T (T (T (T (S (h v1 z y)) (h v1 z v0)) (C h9 (T (T (C h4 (h z v0 z)) (S (h z z v1))) (h z z y)))) (S (h y z v0))) (h y z y))
  have h18 := h y v1 v0
  have h19 := T (T h18 h17) h16
  let v20 := M y v1
  have h21 := h y v0 v0
  have h22 := R y
  T (T (T (T (h x y v1) (h v1 (M x v20) v2)) (C h3 (C h4 (C (T (C h11 (T (T (T (T h18 h17) h16) (h y y v1)) (C (T (T (T h5 h6) (C h3 (C h11 (C (T (C h9 (T h7 (C h4 (S h8)))) (S h10)) h3)))) (S h12)) (T (T (C h22 h19) (C h22 (T h15 (C h9 (T (T (C h22 (T h21 (C h9 h14))) (C h22 (T (T (T (T (T (C h9 h13) (S h21)) (h y v0 z)) (h z v20 v2)) (C h3 (C (R z) (C h19 h3)))) (S (h z (M y y) v2))))) (S (h z y y))))))) h14)))) (C h11 (C (T (T (T h12 (C h3 (C h11 (C (T h10 (C h9 (T (C h4 h8) (S h7)))) h3)))) (S h6)) (S h5)) h4))) h3)))) (S (h v1 (M x (M v1 v1)) v2))) (S (h x v1 v1))

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
theorem Equation1943_implies_Equation4421 (G: Type _) [Magma G] (h: Equation1943 G) : Equation4421 G := fun x y z =>
  let v0 := M x y
  let v1 := M x v0
  let v2 := M z y
  have h3 := h v1 v1 (M v2 y)
  have h4 := h v2 x y
  have h5 := R v1
  have h6 := h z x y
  have h7 := R z
  let v8 := M z (M z v2)
  have h9 := h v8 x z
  have h10 := S h6
  have h11 := R v8
  have h12 := h v1 z v2
  have h13 := h v1 x v2
  have h14 := S h13
  let v15 := M x (M x v2)
  have h16 := R v15
  have h17 := C h16 h6
  have h18 := R (M x (M x z))
  have h19 := h v15 x z
  have h20 := C h16 h10
  let v21 := M v2 z
  let v22 := M v2 v21
  let v23 := M v2 v22
  have h24 := R v23
  let v25 := M z (M z z)
  let v26 := M v0 (M v0 v1)
  have h27 := S h4
  T (T (T (T (h v1 v0 v2) (C (R (M v0 (M v0 v2))) (T (T (T (T (T (T h10 (h z v0 v1)) (C (R v26) (T (T (T (T (T (C h7 (T h3 (C (T (C h5 h27) h10) h27))) h9) (C h18 (T (T (T (C h11 h6) (S h12)) h13) h20))) (S h19)) (h v15 z z)) (C (R v25) (T h17 h14))))) (R (M v26 (M v25 v1)))) (S (h v25 v0 v1))) (h v25 v2 v21)) (C h24 (S (h v2 z z)))))) (S (h v23 v0 v2))) h24) (C (R v2) (T (T (h v22 x v1) (C (R (M x (M x v1))) (T (T (T (T (T (C (R v22) (T h13 h20)) (S (h v15 v2 z))) h19) (C h18 (T (T (T h17 h14) h12) (C h11 h10)))) (S h9)) (C h7 (T (C (T h6 (C h5 h4)) h4) (S h3)))))) (S (h z x v1))))

@[equational_result]
theorem Equation2552_implies_Equation3932 (G: Type _) [Magma G] (h: Equation2552 G) : Equation3932 G := fun x y z =>
  let v0 := M y z
  let v1 := M x v0
  let v2 := M v1 z
  have h3 := R v0
  have h4 := S (h v1 y v2)
  have h5 := R z
  let v6 := M y (M (M y v2) v1)
  let v7 := M v2 (M (M v2 v0) y)
  have h8 := h y v2 v0
  let v9 := M x y
  have h10 := h (M y v0) x v9
  have h11 := S h10
  have h12 := h v9 x v0
  have h13 := R v9
  let v14 := M x (M v1 y)
  have h15 := h z v14 v0
  have h16 := S h15
  have h17 := h y x v0
  have h18 := R v14
  have h19 := C (T h17 (C h18 (C h17 h5))) h3
  let v20 := M x (M (M x v9) x)
  have h21 := h y v20 v9
  have h22 := R y
  have h23 := h x x v9
  have h24 := R v20
  have h25 := R x
  have h26 := S h17
  have h27 := C (T (C h18 (C h26 h5)) h26) h3
  have h28 := S h23
  have h29 := C h25 (C (T h21 (C (T (C h24 (C h28 h22)) h28) h13)) (T h15 h27))
  T (T (T (T h12 (C (C h25 (T (T (T (C h29 h13) h11) h19) h16)) h3)) (h (M (M x z) v0) x v0)) (C (C h25 (T (T (T (T (T (C h29 (T (C (C h25 (T (T (T h15 h27) h10) (C (C h25 (C (T (C (T h23 (C h24 (C h23 h22))) h13) (S h21)) (T h19 h16))) h13))) h3) (S h12))) h11) (C (T h8 (C (R v7) (C h8 h5))) h3)) (S (h z v7 v0))) (h z v6 v2)) (C (T (C (R v6) (C h4 h5)) h4) (R v2)))) h3)) (S (h v2 x v0))

@[equational_result]
theorem Equation2755_implies_Equation11 (G: Type _) [Magma G] (h: Equation2755 G) : Equation11 G := fun x y =>
  let v0 := M y y
  let v1 := M x v0
  have h2 := S (h v1 x v0)
  have h3 := R v0
  let v4 := M v0 v1
  have h5 := R v4
  have h6 := R x
  have h7 := h x y v4
  have h8 := S h7
  have h9 := h v0 y x
  have h10 := C (C h3 h9) h5
  let v11 := M v0 v0
  have h12 := h (M v11 v4) y v1
  have h13 := S h12
  have h14 := R v1
  have h15 := S h9
  have h16 := C (C h3 h15) h5
  have h17 := h v1 v1 v1
  have h18 := h v0 (M v1 v1) x
  have h19 := C (C h3 (T (T h18 (C (S h17) h6)) (C h14 (T h7 h16)))) h14
  have h20 := T (T (T h19 h13) h10) h8
  have h21 := h v0 v0 x
  have h22 := T h21 (C h20 h6)
  have h23 := h v0 v0 v0
  have h24 := R (M v11 v11)
  have h25 := T (C h24 h15) (S h23)
  have h26 := h x v11 v4
  have h27 := T (T (T h7 h16) h12) (C (C h3 (T (T (C h14 (T h10 h8)) (C h17 h6)) (S h18))) h14)
  have h28 := C (T (T (T (T (T (T (T (T (T (C (R v11) (C h3 (C (T (C h27 h6) (S h21)) h14))) (C (C h3 (T h21 (C h20 h27))) (T (C (T h23 (C h24 h9)) h5) (S h26)))) (S (h (M v11 v1) y x))) h19) h13) h10) h8) h26) (C h25 h5)) (C h22 h5)) h3
  have h29 := h (M (M x x) v1) v0 v0
  have h30 := C h22 h14
  T (T (T (T (T (T h26 (C h25 h30)) (C h3 (T (T h29 h28) h2))) h30) h29) h28) h2

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
theorem Equation1507_implies_Equation4026 (G: Type _) [Magma G] (h: Equation1507 G) : Equation4026 G := fun x y z =>
  let v0 := M z y
  let v1 := M z v0
  let v2 := M y v1
  let v3 := M y x
  let v4 := M x y
  let v5 := M x v4
  have h6 := R (M x v5)
  have h7 := h y x v4
  let v8 := M v4 x
  let v9 := M v4 v8
  have h10 := h v9 v4 x
  have h11 := S (h v9 v4 v0)
  let v12 := M v0 (M v0 v4)
  have h13 := C h7 (R v12)
  have h14 := S (h v12 v8 v4)
  have h15 := C (h x v4 v0) h7
  have h16 := T (T (h v9 v5 v2) (C (T (T (T (T (T (S (h v4 x v4)) h15) h14) (h v12 y x)) (C (T (T (T (T (T h13 h11) h10) (C (S h7) h6)) (C (h y x y) h6)) (S (h (M y v3) v4 x))) (R v5))) (S (h v3 y x))) (T (C (R v2) (S (h v1 y x))) (S (h v1 y z))))) (S (h x y z))
  have h17 := R v1
  let v18 := M v1 x
  let v19 := M v1 v18
  let v20 := M v1 v19
  let v21 := M y v2
  have h22 := h v0 z v1
  let v23 := M v1 (M v1 z)
  let v24 := M x v1
  let v25 := M x v24
  T (T (T (T (T (T (T (T (T h15 h14) (h v12 y z)) (C (T h13 h11) h17)) (C h16 h17)) (h v24 x x)) (C (T (T (T (T (h v25 v0 x) (C (T (T (T (C h22 (R v25)) (S (h v23 v1 x))) (h v23 v1 y)) (C (S h22) (R v21))) (R (M x (M x v0))))) (S (h v21 v0 x))) (h v21 v18 v1)) (C (S (h x v1 y)) (R v20))) (R (M x (M x x))))) (S (h v20 x x))) (C h17 (T (T (T (h v19 v4 x) (C (S (h y x v1)) h6)) (C h7 h6)) (S h10)))) (C h17 h16)

@[equational_result]
theorem Equation1943_implies_Equation3417 (G: Type _) [Magma G] (h: Equation1943 G) : Equation3417 G := fun x y z =>
  let v0 := M y x
  let v1 := M z v0
  let v2 := M z v1
  have h3 := h y v1 x
  have h4 := S h3
  have h5 := R v2
  have h6 := C h5 h4
  let v7 := M v1 (M v1 x)
  have h8 := h v7 z v0
  let v9 := M x y
  let v10 := M v9 (M v9 v0)
  let v11 := M x v9
  have h12 := h x v2 y
  have h13 := S h12
  have h14 := R v9
  have h15 := h v7 x v0
  have h16 := h y y x
  have h17 := R (M x (M x v0))
  have h18 := h (M y v0) x v0
  have h19 := C h5 (T (T (T (T h18 (C h17 (T (S h16) h3))) (S h15)) h8) h6)
  have h20 := h y z v0
  let v21 := M y (M y v9)
  let v22 := M v2 (M v2 y)
  have h23 := h v22 x v9
  have h24 := S h23
  let v25 := M x v11
  have h26 := R v25
  have h27 := h v11 x v9
  have h28 := h x x y
  have h29 := R x
  T (T (T (T (h v9 x v9) (C (C h29 (T (T (T (T h27 (C h26 (T (S h28) h12))) h24) (C h5 (T (T (T (T (C h5 h3) (S h8)) h15) (C h17 (T h4 h16))) (S h18)))) (S h20))) (C h14 (T (T (T (T (C h29 (T (T (T (T h20 h19) h23) (C h26 (T h13 h28))) (S h27))) (h v25 x x)) (C (R (M x (M x x))) (T (T (T (C h26 h12) h24) (h v22 y v9)) (C (R v21) h13)))) (S (h v21 x x))) (C (R y) (T (C (T h20 h19) h14) h13)))))) (h v10 x y)) (C (R v11) (T (T (T (C (R v10) h3) (S (h v7 v9 v0))) h8) h6))) (S (h v2 x y))

@[equational_result]
theorem Equation3398_implies_Equation3906 (G: Type _) [Magma G] (h: Equation3398 G) : Equation3906 G := fun x y z =>
  let v0 := M z z
  let v1 := M y v0
  let v2 := M v1 y
  have h3 := R (M z v2)
  have h4 := R v0
  have h5 := h z z z
  have h6 := S h5
  have h7 := h z v0 v1
  have h8 := h y z v0
  have h9 := R v1
  have h10 := R z
  have h11 := C h10 (T (C h9 h8) (S h7))
  have h12 := h y v1 z
  have h13 := h y v0 v0
  have h14 := h z z v0
  have h15 := R y
  have h16 := h v0 y v0
  have h17 := h y v1 x
  have h18 := h y x v0
  have h19 := h x v0 v1
  have h20 := R x
  have h21 := C h15 (T (C (T (T (T (T (C h20 (T h19 (C h9 (S h18)))) (S h17)) h12) h11) h6) (T h16 (C h4 (C h15 (T (C h4 h5) (S h14)))))) (S h13))
  have h22 := h v0 (M x (M x v0)) y
  have h23 := h x x v0
  let v24 := M x x
  have h25 := R v2
  have h26 := S h12
  have h27 := C h10 (T h7 (C h9 (S h8)))
  T (T (T (T (T (T (T (T (T h23 h22) h21) h12) h11) (h z (M z v0) v2)) (C h25 (C (T (T (h z v0 v2) (C h25 (C (T (T (T (T (T h5 h27) h26) (C h15 (T h13 (C (T (T (T (T h5 h27) h26) h17) (C h20 (T (C h9 h18) (S h19)))) (T (C h4 (C h15 (T h14 (C h4 h6)))) (S h16)))))) (S h22)) (S h23)) h3))) (S (h z v24 v2))) h3))) (C h25 (C (T (h z v24 y) (C h15 (T (T (C (T (T (T (T (T h23 h22) h21) h12) h11) h6) (R (M z y))) (C h4 (T (h z y z) (h z v1 z)))) (S (h v1 z v0))))) h3))) (S (h z (M y (M v1 z)) v2))) (S (h v1 y z))

@[equational_result]
theorem Equation1910_implies_Equation1117 (G: Type _) [Magma G] (h: Equation1910 G) : Equation1117 G := fun x y z =>
  let v0 := M y (M x z)
  let v1 := M v0 z
  let v2 := M y v1
  have h3 := h v2 x v1
  let v4 := M v2 v1
  let v5 := M x v4
  have h6 := h y v0 z
  have h7 := R v1
  have h8 := h x y z
  have h9 := T (C h8 h7) (S h6)
  have h10 := R v2
  let v11 := M v2 v2
  have h12 := h v2 y v1
  have h13 := S h12
  let v14 := M y v4
  have h15 := R v14
  have h16 := C (T (C h15 h13) h13) h13
  have h17 := h v14 v14 v2
  have h18 := T h12 (C (T h17 h16) h10)
  have h19 := S (h y y v1)
  have h20 := T (C (T (C (T h12 (C h15 h12)) h12) (S h17)) h10) h13
  let v21 := M y v2
  let v22 := M y (M z v1)
  have h23 := h v11 v22 v2
  have h24 := h z y v1
  have h25 := R v22
  have h26 := S h24
  have h27 := h x x v1
  have h28 := T h6 (C (S h8) h7)
  have h29 := R x
  T (T h27 (C (T (T (T (C h29 h9) (h (M x y) v2 y)) (C (T (T (T (C h10 (T (C (C h29 h28) h28) (S h27))) (C (T (T h12 (C (T (T (T h17 h16) h23) (C (T (C h25 h20) h26) h26)) h10)) (C (T (T (T (C (T h24 (C h25 h18)) h24) (S h23)) (h v11 v21 v2)) (C (T (C (R v21) h20) h19) h19)) h18)) (T (h x y v1) (C (C (R y) h9) h10)))) (S (h v11 (M y y) v2))) (C h10 (T h3 (C (R v5) h9)))) (R (M v2 y)))) (S (h v5 v2 y))) (R (M x v1)))) (S h3)

@[equational_result]
theorem Equation3211_implies_Equation2925 (G: Type _) [Magma G] (h: Equation3211 G) : Equation2925 G := fun x y z =>
  have h0 := R z
  have h1 := R y
  let v2 := M x z
  let v3 := M y v2
  have h4 := h v3 v2 v3
  have h5 := R v2
  have h6 := R v3
  have h7 := h v2 y v2
  have h8 := h y v3 v2
  have h9 := C (T (C (C (C (T h8 (C (S h7) h6)) h6) h6) h5) (S h4)) h1
  have h10 := h v2 y v3
  let v11 := M v3 y
  let v12 := M v11 z
  have h13 := h v2 x v12
  have h14 := R x
  have h15 := T (C (T h4 (C (C (C (T (C h7 h6) (S h8)) h6) h6) h5)) h1) (S h10)
  have h16 := R v12
  have h17 := h x v2 z
  have h18 := h z x z
  have h19 := h z v11 v12
  have h20 := S h19
  have h21 := T h10 h9
  have h22 := h v11 v12 z
  have h23 := h z v11 z
  have h24 := h v12 z v12
  have h25 := T h24 (C (C (C (T (C h23 h16) (S h22)) h16) h16) h0)
  have h26 := h v12 v12 v2
  have h27 := S h24
  have h28 := C (C (C (T h22 (C (S h23) h16)) h16) h16) h0
  have h29 := R v11
  have h30 := S h18
  T (h x z z) (C (T (T (T (C (T (T (T (C (C (T (h z x v11) (C (T (T (T (C (C (C (T h17 (C h30 h21)) h29) h15) h0) (S (h v2 z v11))) h13) (C (T (T (C (T (C (C (T h17 (C (T (T h30 h19) (C (T h28 h27) h15)) h5)) h16) h16) (S h26)) h21) (C h25 h29)) h20) h14)) h14)) h0) h0) (S (h z z x))) h19) (C (T (T (T h28 h27) h26) (C (C (T (C (T (T (C h25 h21) h20) h18) h5) (S h17)) h16) h16)) h15)) h14) (S h13)) h10) h9) h0)

@[equational_result]
theorem Equation4176_implies_Equation4013 (G: Type _) [Magma G] (h: Equation4176 G) : Equation4013 G := fun x y z =>
  let v0 := M y z
  let v1 := M z v0
  let v2 := M v1 x
  have h3 := R v2
  have h4 := R v1
  have h5 := h x v2 x
  have h6 := R x
  have h7 := h x v1 x
  have h8 := h x x v1
  have h9 := R y
  have h10 := h x y z
  have h11 := S h10
  have h12 := h z v0 x
  have h13 := S h12
  let v14 := M x y
  have h15 := h x y v14
  let v16 := M y v14
  have h17 := h v14 v16 x
  have h18 := C (T (T h17 (C (T (S h15) h10) h6)) h13) h9
  have h19 := h v16 x y
  have h20 := h z v0 v1
  have h21 := h v1 y z
  have h22 := h y v14 v1
  have h23 := h v1 x y
  have h24 := h x v2 v1
  have h25 := T (T h24 (C (T (T (T (C (T (C h23 h4) (S h22)) h6) h19) h18) h21) h4)) (S h20)
  have h26 := h x y v1
  let v27 := M y v1
  T (T (T (T (T h15 (h (M v16 x) v14 v2)) (C (C (T (T (T (T (T (C (T h26 (C (T (h v27 x v2) (C (T (T (T (C h25 (R v27)) (h v1 v27 x)) (C (T (S h26) h10) h6)) h13) h3)) (T (T h20 (C (T (T (T (S h21) (C (T (T h12 (C (T h11 h15) h6)) (S h17)) h9)) (S h19)) (C (T h22 (C (S h23) h4)) h6)) h4)) (S h24)))) h3) (S (h (M x v2) v1 v2))) (C (T h5 (C (S h7) h6)) h4)) (S h8)) (h x x v2)) (C (C h25 h6) h3)) (T h19 h18)) h3)) (S (h (M v1 y) v2 v2))) (C (T (T (T (C (T h12 (C h11 h6)) h9) (S (h x x y))) h8) (C (T (C h7 h6) (S h5)) h4)) h3)) (S (h v1 x v2))

@[equational_result]
theorem Equation1537_implies_Equation1256 (G: Type _) [Magma G] (h: Equation1537 G) : Equation1256 G := fun x y z =>
  let v0 := M y y
  let v1 := M v0 z
  let v2 := M v1 z
  let v3 := M x v2
  have h4 := h z y v0
  have h5 := h v0 x y
  have h6 := S h5
  have h7 := h y y y
  have h8 := S h7
  have h9 := R v0
  have h10 := h y y v0
  have h11 := h y z v0
  let v12 := M z z
  have h13 := R v12
  have h14 := R y
  have h15 := R (M x x)
  have h16 := C h15 (C h14 (T (T (T (C h13 h7) (S h11)) h10) (C h9 h8)))
  have h17 := h v12 x y
  have h18 := R z
  have h19 := h z y z
  have h20 := T (C h9 (T h19 (C h9 (C h18 (T (T h17 h16) h6))))) (S h4)
  have h21 := R v1
  have h22 := C h21 h20
  let v23 := M v1 v1
  let v24 := M v3 v3
  have h25 := R v3
  have h26 := S h17
  have h27 := C h15 (C h14 (T (T (T (C h9 h7) (S h10)) h11) (C h13 h8)))
  have h28 := T h4 (C h9 (T (C h9 (C h18 (T (T h5 h27) h26))) (S h19)))
  have h29 := R x
  have h30 := C h22 (C h25 (T (T (T (T (C (C h29 (T (T (T h5 h27) h26) (C h28 h18))) h25) (h v24 x y)) (C h15 (C h14 (T (T (T (C (R v24) h7) (S (h y v3 v0))) (h y v1 v0)) (C (R v23) h8))))) (S (h v23 x y))) h22))
  have h31 := h (M x v0) v1 v3
  have h32 := C h29 (T (T (T (C h20 h18) h17) h16) h6)
  T (T (h x v2 v2) (C (R (M v2 v2)) (T (T (T (T (C (C h21 h28) (T (T h32 h31) h30)) (S (h v3 v1 v2))) h32) h31) h30))) (S (h v3 v2 v2))

@[equational_result]
theorem Equation952_implies_Equation3932 (G: Type _) [Magma G] (h: Equation952 G) : Equation3932 G := fun x y z =>
  let v0 := M y z
  let v1 := M x v0
  let v2 := M v1 z
  have h3 := h v2 v2 x
  let v4 := M x v2
  have h5 := R x
  let v6 := M v2 v2
  have h7 := R (M z x)
  let v8 := M x y
  have h9 := h z z v8
  let v10 := M v0 v0
  have h11 := T (T (T (h v10 x z) (C h5 (C (T (S (h z z y)) h9) h7))) (C h5 (C (T (S h9) (h z z v1)) h7))) (S (h v6 x z))
  have h12 := R (M v0 x)
  have h13 := h v0 v0 z
  let v14 := M v1 v1
  have h15 := h z v1 v8
  let v16 := M v8 v1
  let v17 := M (M v8 z) v16
  have h18 := R v0
  have h19 := h v1 y v0
  let v20 := M (M v0 v1) (M v0 y)
  have h21 := h v8 v0 y
  T (T (T (T (T (T (T (T h21 (C h18 (T (T (T (T (h (M (M y v8) (M y v0)) v16 v0) (C (R v16) (C (S h21) (S (h y v0 x))))) (h (M v16 (M v8 y)) x y)) (C h5 (C (T (S (h v1 y v8)) h19) (R (M y x))))) (S (h v20 x y))))) (C h18 (T (h v20 z y) (C h15 (C (S h19) h18))))) (S (h v17 v0 v1))) (h v17 x v1)) (C h5 (C (T (S h15) (h z v1 v1)) (R (M v1 x))))) (S (h (M v2 v14) x v1))) (C (R v2) (T (T (T (T (T (T (T (h v14 x v0) (C h5 (C (T (S (h v0 v0 x)) h13) h12))) (C h5 (C (T (S h13) (h v0 v0 v0)) h12))) (S (h (M v10 v10) x v0))) (C h11 h11)) (h (M v6 v6) x v2)) (C h5 (C (T (S (h v2 v2 v2)) h3) (R (M v2 x))))) (S (h (M v4 v4) x v2))))) (S h3)

@[equational_result]
theorem Equation1699_implies_Equation3120 (G: Type _) [Magma G] (h: Equation1699 G) : Equation3120 G := fun x y z =>
  let v0 := M y x
  let v1 := M v0 y
  let v2 := M v1 z
  let v3 := M v2 z
  let v4 := M v0 x
  have h5 := R v3
  have h6 := h y v0 v2
  have h7 := S h6
  have h8 := C h7 h5
  let v9 := M (M v0 v2) v2
  have h10 := h v9 v1 z
  have h11 := R v9
  have h12 := h x y v2
  have h13 := S h12
  let v14 := M (M y v2) v2
  let v15 := M v4 x
  have h16 := R v15
  have h17 := h x y v3
  have h18 := S h17
  have h19 := h v9 (M v0 v1) v9
  have h20 := h v1 v0 v2
  have h21 := C (T (T (T (C h20 (T h6 (C h20 h11))) (S h19)) h10) h8) h5
  have h22 := h y v1 z
  have h23 := R v0
  have h24 := S (h v0 y v2)
  have h25 := R (M v1 y)
  have h26 := h x y v1
  let v27 := M (M y v1) v1
  let v28 := M (M y v3) v3
  have h29 := S h20
  T (T (T (T h17 (C h23 (T (T (R v28) (C (T (T (T (C h6 h5) (S h10)) h19) (C h29 (T (C h29 h11) h7))) h5)) (S h22)))) (h v1 y x)) (C (T (T (T (T (T (C (T (T (T (T (T (T (T (T (T (T h22 h21) (h v28 v0 x)) (C (T h18 h26) h16)) (S (h v27 v0 x))) (h v27 v0 y)) (C (S h26) h25)) (C h12 h25)) (S (h v14 v0 y))) (h v14 (M y v0) v14)) (C h24 (T (C h24 (R v14)) h13))) (T (C h23 (T h22 h21)) h18)) (h v15 x x)) (C (T (T (T (C h12 h16) (S (h v14 v0 x))) (h v14 v0 v2)) (C h13 h11)) (R (M (M x x) x)))) (S (h v9 x x))) h10) h8) (R v4))) (S (h v3 y x))

@[equational_result]
theorem Equation492_implies_Equation2944 (G: Type _) [Magma G] (h: Equation492 G) : Equation2944 G := fun x y z =>
  let v0 := M y (M y x)
  let v1 := M v0 z
  have h2 := h z x v1
  have h3 := h x z x
  have h4 := h z v1 v0
  have h5 := S h4
  have h6 := h v0 z v0
  have h7 := R v1
  have h8 := C h7 h6
  have h9 := R x
  have h10 := C h9 (T h8 h5)
  have h11 := h v1 x y
  have h12 := R z
  have h13 := C h7 (T (C h12 (C h9 (C h9 (T h11 h10)))) (S h3))
  have h14 := h z v1 x
  have h15 := h z z v1
  have h16 := S h14
  have h17 := S h6
  have h18 := C h9 (C h9 (T (C h9 (T h4 (C h7 h17))) (S h11)))
  have h19 := C h7 (T h3 (C h12 h18))
  have h20 := C h7 (C h7 (T h19 h16))
  have h21 := h z v0 x
  have h22 := h x x y
  have h23 := h x z v1
  have h24 := h v1 x v1
  have h25 := R v0
  have h26 := h v0 v1 z
  have h27 := h v1 z z
  have h28 := C h7 (C h7 (T h14 h13))
  T (h x v1 v1) (C h7 (T (C h9 (T (T (T (C h7 (C h7 (T (T h11 (C h9 (T (T (T h8 h5) h2) (C h9 (T (T (T (C h12 (C h7 (T (T (T h19 h16) h15) (C h12 (C h12 (T (T h28 (C h7 (T (T (C h7 (T (T (T h19 h16) h21) (C h25 (T (C h12 (S h22)) (C h12 (T h23 (C h12 (T (C h9 h28) (S h24))))))))) (S h26)) h6))) h5)))))) (S h27)) h11) h10))))) h18))) (S (h v1 v1 x))) h27) (C h12 (C h7 (T (T (T (C h12 (C h12 (T (T h4 (C h7 (T (T h17 h26) (C h7 (T (T (T (C h25 (T (C h12 (T (C h12 (T h24 (C h9 h20))) (S h23))) (C h12 h22))) (S h21)) h14) h13))))) h20))) (S h15)) h14) h13))))) (S h2)))

