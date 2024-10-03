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
theorem Equation1910_implies_Equation1761 (G: Type _) [Magma G] (h: Equation1910 G) : Equation1761 G := fun x y z =>
  let v0 := M x y
  let v1 := M v0 z
  let v2 := M y z
  let v3 := M v2 v1
  have h4 := h v3 v2 v1
  have h5 := S h4
  have h6 := R v3
  let v7 := M v2 (M v3 v1)
  have h8 := h v7 v7 v3
  have h9 := S h8
  have h10 := R v7
  have h11 := C (T h4 (C h10 h4)) h4
  let v12 := M v2 v3
  have h13 := h (M v3 v3) v12 v3
  have h14 := h v2 v2 v1
  have h15 := C (T (C h10 h5) h5) h5
  have h16 := R v12
  have h17 := h v2 v0 z
  have h18 := S h17
  have h19 := R v2
  let v20 := M v0 (M v2 z)
  have h21 := h v20 v2 v1
  have h22 := S h14
  have h23 := T (T h4 (C (T (T (T (T h8 h15) h13) (C (T (C h16 (T (C (T h11 h9) h6) h5)) h22) h22)) (C h19 h17)) h6)) (S h21)
  have h24 := R v1
  T (T (T (T (T (h x v1 y) (C (C h24 (T (T (T (h v0 v3 v2) (C (C h6 (T (h (M v0 v2) v3 v1) (C (C h6 (S (h y v0 z))) (T (C h23 h24) h18)))) (R (M v3 v2)))) (S (h (M v3 y) v3 v2))) (C h23 (R y)))) (R (M v1 y)))) (S (h v20 v1 y))) h21) (C (T (T (T (T (C h19 h18) (C (T h14 (C h16 (T h4 (C (T h8 h15) h6)))) h14)) (S h13)) h11) h9) h6)) h5

@[equational_result]
theorem Equation492_implies_Equation1470 (G: Type _) [Magma G] (h: Equation492 G) : Equation1470 G := fun x y z =>
  let v0 := M x y
  let v1 := M z y
  let v2 := M z v1
  let v3 := M v0 v2
  have h4 := R v3
  have h5 := h v1 y z
  have h6 := h v1 v1 z
  have h7 := h v2 v1 v2
  have h8 := h y y z
  have h9 := R z
  have h10 := R v2
  have h11 := h z v2 y
  have h12 := R v1
  have h13 := h v1 z v2
  have h14 := h z v1 v1
  have h15 := S h13
  have h16 := C h9 (T h7 (C h12 (C h10 (C h10 (T (C h10 (C h9 h8)) (S h11))))))
  have h17 := R y
  have h18 := C h9 (T (C h17 (T (T (T (C h9 (C h9 (T (h z y z) (C h17 (T (T (T h16 h15) h5) (C h17 (T (C h12 (C h9 (T h6 (C h12 (C h12 (T h16 h15)))))) (S h14)))))))) (S (h z z y))) h14) (C h12 (C h9 (T (C h12 (C h12 (T h13 (C h9 (T (C h12 (C h10 (C h10 (T h11 (C h10 (C h9 (S h8))))))) (S h7)))))) (S h6)))))) (S h5))
  have h19 := h y z z
  have h20 := S (h y v2 y)
  have h21 := C (T h19 h18) (C h17 h8)
  have h22 := R v0
  T (T (h x y y) (C h17 (T (T (C (R x) (T h21 h20)) (h v0 v3 v0)) (C h4 (C h22 (C h22 (T (C h22 (T (h v3 y y) (C h17 (C h4 (T (T (T (T (T h21 h20) h19) h18) (h v2 v3 v0)) (C h4 (S (h v0 v2 v0)))))))) (S (h y v0 v3))))))))) (S (h v3 y v0))

@[equational_result]
theorem Equation2196_implies_Equation1507 (G: Type _) [Magma G] (h: Equation2196 G) : Equation1507 G := fun x y z =>
  let v0 := M z y
  let v1 := M z v0
  let v2 := M y x
  let v3 := M v2 v1
  let v4 := M (M v3 v1) v1
  let v5 := M (M v1 y) y
  let v6 := M (M v0 v0) v0
  have h7 := h z y v1
  let v8 := M (M y v1) v1
  let v9 := M y z
  let v10 := M v9 z
  let v11 := M (M v2 z) z
  let v12 := M v2 y
  let v13 := M v12 y
  have h14 := h y x v3
  let v15 := M (M x v3) v3
  let v16 := M v2 x
  let v17 := M x y
  T (T (T (T (T (T (T (h x y z) (C (R v10) (T (T (h v17 y x) (C (R v16) (T (T (T (T (h (M v17 y) v2 x) (C (R (M v16 x)) (T (S (h y x y)) h14))) (S (h v15 v2 x))) (h v15 v2 y)) (C (R v13) (S h14))))) (S (h v13 y x))))) (S (h v12 y z))) (C (T (C (h y x v2) (h x v2 z)) (S (h v11 (M x v2) v2))) (R y))) (C (R v11) (T (T (T (T (h y z v3) (C (R (M (M z v3) v3)) (T (T (T (T (h v9 z x) (C (R (M (M z x) x)) (T (T (T (T (h v10 v0 x) (C (R (M (M v0 x) x)) (T (S (h z y z)) h7))) (S (h v8 v0 x))) (h v8 v0 v0)) (C (R v6) (S h7))))) (S (h v6 z x))) (h v6 v1 y)) (C (R v5) (S (h z v0 v0)))))) (S (h v5 z v3))) (h v5 v3 v1)) (C (R v4) (S (h v2 v1 y)))))) (S (h v4 v2 z))) (h v4 (M v1 v3) v3)) (C (S (h v2 v1 v3)) (S (h v1 v3 v1)))

@[equational_result]
theorem Equation2399_implies_Equation4305 (G: Type _) [Magma G] (h: Equation2399 G) : Equation4305 G := fun x y z =>
  let v0 := M y z
  let v1 := M z v0
  have h2 := R v1
  let v3 := M z (M z v1)
  have h4 := h v3 v1 v0
  have h5 := S h4
  have h6 := R v3
  have h7 := h v0 z z
  have h8 := h z z x
  have h9 := S h8
  let v10 := M z (M x (M x z))
  have h11 := R v10
  have h12 := T (C h11 h9) h9
  have h13 := h z v3 v10
  have h14 := h z y v10
  have h15 := R y
  have h16 := T h8 (C h11 h8)
  have h17 := R v0
  have h18 := C (C h2 (C h17 (T (T (T (C (C h15 h16) h15) (S h14)) h13) (C (T (C h6 h12) (S h7)) h6)))) h2
  have h19 := h y v1 v0
  have h20 := S (h y x x)
  have h21 := R x
  let v22 := M x (M x y)
  have h23 := S (h v22 v22 x)
  let v24 := M v22 (M x (M x v22))
  have h25 := C (C h21 (T (C (R v24) h23) h23)) h21
  have h26 := h v22 x v24
  T (T (T (T (T (T (T (T h26 h25) h20) h19) h18) h5) (h v3 v1 x)) (C (C h2 (T (T (T (T (T (T (C h21 (C h21 (T (T h4 (C (C h2 (C h17 (T (T (T (C (T h7 (C h6 h16)) h6) (S h13)) h14) (C (C h15 h12) h15)))) h2)) (S h19)))) h26) h25) h20) h19) h18) h5)) h2)) (S (h v1 v1 z))

@[equational_result]
theorem Equation711_implies_Equation1181 (G: Type _) [Magma G] (h: Equation711 G) : Equation1181 G := fun x y z =>
  let v0 := M z (M z x)
  let v1 := M v0 y
  let v2 := M y v1
  have h3 := R y
  let v4 := M y (M (M y x) x)
  have h5 := h y v1 v4
  have h6 := S h5
  have h7 := R v4
  have h8 := h y y x
  have h9 := R v1
  have h10 := C h9 (C h9 (T h8 (C h8 h7)))
  have h11 := S h8
  have h12 := R v2
  have h13 := C h12 (C (C (T h5 (C h9 (C h9 (T (C h11 h7) h11)))) h9) h9)
  have h14 := h v1 v1 x
  have h15 := S h14
  let v16 := M v1 (M (M v1 x) x)
  have h17 := R v16
  have h18 := T (C h15 h17) h15
  have h19 := C h12 (C h12 h18)
  have h20 := h v1 v2 v16
  have h21 := h v1 y v16
  have h22 := S (h x x x)
  let v23 := M x (M (M x x) x)
  have h24 := R z
  T (T (T (T (h x z v23) (C h24 (C h24 (T (C h22 (R v23)) h22)))) (h v0 v2 y)) (C h12 (C h12 (T (C (T h21 (C h3 (C h3 h18))) h3) (C (T (T (T (T (T (C h3 (C h3 (T h14 (C h14 h17)))) (S h21)) h20) h19) h13) (C h12 (T (T (T (C (C (T h10 h6) h9) (T (T h20 h19) h13)) (S (h (M v1 (M v1 y)) v2 v1))) h10) h6))) h3))))) (S (h v2 v2 y))

@[equational_result]
theorem Equation2196_implies_Equation4458 (G: Type _) [Magma G] (h: Equation2196 G) : Equation4458 G := fun x y z =>
  let v0 := M y x
  let v1 := M x v0
  let v2 := M z y
  let v3 := M v2 z
  have h4 := h v2 z v3
  have h5 := S h4
  let v6 := M z v3
  let v7 := M (M v3 v1) v1
  let v8 := M v6 v3
  let v9 := M z v2
  have h10 := R (M (M v2 x) x)
  have h11 := R v2
  let v12 := M y v1
  have h13 := R v12
  have h14 := S (h y x v0)
  have h15 := h y v1 v0
  let v16 := M v12 v1
  have h17 := h x v0 v2
  let v18 := M (M v0 v2) v2
  let v19 := M v1 y
  let v20 := M v19 y
  T (T (T (T (T (T (T (T (T (T (T (h v1 y y) (C (R (M (M y y) y)) (T (h v19 y v1) (C (R v16) (T (T (h v20 x x) (C (R (M (M x x) x)) (T (T (T (C (R v20) h17) (S (h v18 v1 y))) (h v18 v1 v0)) (C h14 (S h17))))) (S (h y x x))))))) (S (h v16 y y))) (h v16 v2 x)) (C h10 (T (S (h z y v1)) (h z y v2)))) (S (h (M (M y v2) v2) v2 x))) (C (T (C (T h15 (C (T (T h14 h15) (C h14 h13)) h13)) h11) (S (h z y v12))) h11)) (h v9 v2 x)) (C h10 (T (T (T (T (h (M v9 v2) v3 x) (C (R (M (M v3 x) x)) (T (S (h v2 z v2)) h4))) (S (h v8 v3 x))) (h v8 v3 v1)) (C (R v7) h5)))) (S (h v7 v2 x))) (h v7 v6 v3)) (C h5 (S (h z v3 v1)))

@[equational_result]
theorem Equation1699_implies_Equation26 (G: Type _) [Magma G] (h: Equation1699 G) : Equation26 G := fun x y =>
  let v0 := M x y
  let v1 := M v0 y
  have h2 := h v1 v0 v0
  have h3 := S h2
  let v4 := M (M v0 v0) v0
  have h5 := h v4 y x
  let v6 := M y x
  let v7 := M v6 x
  have h8 := R v7
  have h9 := R v4
  have h10 := h y x y
  have h11 := S h10
  have h12 := C h11 h9
  have h13 := h v1 v0 y
  let v14 := M v1 y
  have h15 := R v14
  have h16 := h v14 y x
  have h17 := R (M (M v0 x) x)
  let v18 := M x v0
  have h19 := S h16
  have h20 := C h11 h15
  let v21 := M (M y v0) v0
  have h22 := R v21
  T (T (h x v6 v21) (C (T (T (T (h v7 v1 x) (C (T (C (T h13 h20) h8) h19) (R (M (M v1 x) x)))) (S (h y v1 x))) h10) (T (T (T (T (T (T (C (S (h x y v0)) h22) (C (R x) (T (T (h v21 v1 v1) (C (T (T (T (T (C (T h2 h12) h22) (S (h v4 y v0))) h5) (C (T (T (T (C h10 h9) h3) h13) h20) h8)) h19) (R (M (M v1 v1) v1)))) (S (h y v1 v1))))) (h v0 v18 v1)) (C (T (T (T (h (M v18 v0) v0 x) (C (S (h y x v0)) h17)) (C h10 h17)) (S (h v1 v0 x))) (T (C (S (h v0 x y)) (R v1)) h11))) h16) (C (T (T (T (C h10 h15) (S h13)) h2) h12) h8)) (S h5)))) h3

@[equational_result]
theorem Equation3940_implies_Equation3537 (G: Type _) [Magma G] (h: Equation3940 G) : Equation3537 G := fun x y z =>
  let v0 := M z z
  let v1 := M v0 y
  have h2 := h x v1 v0
  let v3 := M x (M v0 v1)
  have h4 := R v0
  have h5 := h z z v1
  have h6 := S h5
  let v7 := M z (M v1 z)
  let v8 := M y y
  let v9 := M v0 v8
  have h10 := R v7
  have h11 := R x
  let v12 := M x v8
  let v13 := M x y
  have h14 := h z z v13
  let v15 := M z (M v13 z)
  have h16 := R v15
  let v17 := M x v1
  have h18 := R z
  have h19 := h x y v0
  let v20 := M v1 y
  let v21 := M x v20
  let v22 := M v0 v20
  T (T (T h19 (C (T h2 (C (R v3) (T (T (T (T (T (T (T h5 (h v7 v1 v22)) (C (T (C h10 (S (h v0 y v1))) h6) (R v22))) (C h4 (T (T (h v0 v20 x) (C (T (T (T (T (T (T (T (C (T h14 (C h16 (h x y v1))) (R v21)) (S (h v15 v1 v21))) (h v15 v1 x)) (C (T (C (C h18 (T (C h19 h18) (S (h v17 z z)))) (R v17)) (S (h z z v17))) h11)) (C h14 h11)) (S (h v15 y x))) (h v15 y v12)) (C (T (C h16 (S (h x y y))) (S h14)) (R v12))) h11)) (S (h v0 v8 x))))) (C (T h5 (C h10 (h v0 y y))) (R v9))) (S (h v7 y v9))) (h v7 y v0)) (C h6 h4)))) h4)) (S (h v3 v0 v0))) (S h2)

@[equational_result]
theorem Equation2170_implies_Equation1561 (G: Type _) [Magma G] (h: Equation2170 G) : Equation1561 G := fun x y z =>
  let v0 := M z y
  let v1 := M x v0
  let v2 := M y z
  let v3 := M v2 v1
  have h4 := R v0
  have h5 := R v3
  have h6 := h v2 v3 v0
  let v7 := M v0 v3
  have h8 := R v7
  have h9 := R v2
  have h10 := h v1 y z
  have h11 := h v7 v1 v2
  have h12 := h v7 v1 v1
  have h13 := S h12
  let v14 := M v1 v1
  have h15 := R v14
  have h16 := S h10
  have h17 := h v14 x v0
  let v18 := M v0 x
  have h19 := R v18
  have h20 := h v1 v3 v0
  have h21 := R v1
  let v22 := M v2 x
  T (T (T (h x y z) (C (T (T (h v22 v1 v1) (C (T (T (T (C (T h17 (C (T (T (T (C (T h20 (C (C h16 h21) h8)) h15) h13) (h v7 v1 x)) (C (T (C (C h10 (R x)) h8) (S (h x v3 v0))) (T (C (h x z y) h21) (S (h v2 v0 x))))) h19)) (R v22)) (S (h v18 x v2))) (h v18 v2 v3)) (C (T (C (T (T (T (C (T h6 (C (C h16 h9) h8)) h5) (S h11)) h12) (C (T (C (C h10 h21) h8) (S h20)) h15)) h19) (S h17)) (T (C (T (h v3 v3 v0) (C (C h16 h5) h8)) (T (h v2 v0 v3) (C (S (h v3 z y)) h16))) (S (h v7 v1 v3))))) h15)) h13) h4)) (C (T h11 (C (T (C (C h10 h9) h8) (S h6)) h5)) h4)) (S (h v3 y z))

@[equational_result]
theorem Equation2958_implies_Equation684 (G: Type _) [Magma G] (h: Equation2958 G) : Equation684 G := fun x y z =>
  let v0 := M y z
  let v1 := M v0 z
  let v2 := M x v1
  have h3 := R v2
  have h4 := S (h y x y)
  let v5 := M (M x (M x y)) y
  let v6 := M (M z (M z x)) x
  have h7 := h x x v1
  have h8 := R v1
  have h9 := R x
  have h10 := h x x x
  have h11 := S h10
  let v12 := M (M x (M x x)) x
  have h13 := R v12
  have h14 := h v2 v12 x
  let v15 := M (M x (M x v2)) v2
  let v16 := M v2 v1
  have h17 := h v16 v15 v2
  have h18 := R v16
  have h19 := h v2 x v2
  have h20 := R v15
  have h21 := h x z x
  have h22 := S (h v2 y v2)
  let v23 := M (M y (M y v2)) v2
  have h24 := S h19
  T (T (T (T (T h7 (C (T (C (C (T h10 (C h13 h10)) h3) h9) (S h14)) h8)) h17) (C (C (T (C h20 h24) h24) h18) h3)) (h (M (M v2 v16) v2) v23 v2)) (C (T (T (T (C (T (T (C (R v23) h22) h22) (C (T h21 (C (R v6) h21)) h8)) (T (T (T (C (C (T h19 (C h20 h19)) h18) h3) (S h17)) (C (T h14 (C (C (T (C h13 h11) h11) h3) h9)) h8)) (S h7))) (S (h v1 v6 x))) (C (T (h v0 v5 y) (C (C (T (C (R v5) h4) h4) (R v0)) (R y))) (R z))) (S (h y y z))) h3)

@[equational_result]
theorem Equation3404_implies_Equation3526 (G: Type _) [Magma G] (h: Equation3404 G) : Equation3526 G := fun x y z =>
  let v0 := M x y
  let v1 := M y z
  let v2 := M v1 z
  let v3 := M v0 x
  have h4 := h v1 z v1
  have h5 := h v1 v1 z
  have h6 := h z v1 y
  have h7 := R v1
  have h8 := C h7 (S h6)
  have h9 := h v1 y v1
  have h10 := R z
  let v11 := M v1 y
  have h12 := h z v11 y
  have h13 := h v11 v1 z
  have h14 := h y z v1
  have h15 := h y z x
  have h16 := C h10 (S h15)
  have h17 := h v0 x z
  have h18 := R y
  have h19 := S h17
  have h20 := C h10 h15
  have h21 := h v1 y z
  have h22 := h y v1 v1
  let v23 := M v2 y
  T (T (h x y v0) (C (R v0) (T (T (h y v3 v1) (C h7 (C (R v3) (T (T (T (T (T (T (T h9 h8) (C h7 (T (C h10 (h y z v2)) (S (h v23 v2 z))))) (S (h z v23 v1))) (C h10 (T (h v2 y v1) (C h7 (T (C h18 (T (C h7 (T h4 (C h7 (T (C h10 (T (T (T (T h5 (C h10 (T (C h7 h6) (S h9)))) h12) (C h18 (T (T (T h13 (C h10 (S h14))) h20) h19))) (C h18 (T h17 h16)))) (S h21))))) (S h22))) (S (h z y y))))))) (S (h y v1 z))) h22) (C h7 (T (C h7 (T h21 (C h10 (T (T (T (T (C h18 (T h20 h19)) (C h18 (T (T (T h17 h16) (C h10 h14)) (S h13)))) (S h12)) (C h10 (T h9 h8))) (S h5))))) (S h4))))))) (S (h v2 v3 v1))))) (S (h x v2 v0))

@[equational_result]
theorem Equation887_implies_Equation1496 (G: Type _) [Magma G] (h: Equation887 G) : Equation1496 G := fun x y z =>
  let v0 := M z z
  let v1 := M y v0
  have h2 := R v1
  let v3 := M y x
  let v4 := M v3 v1
  have h5 := h v3 v1 (M v4 v4)
  have h6 := h v4 v4 v4
  have h7 := R v0
  let v8 := M v1 v1
  have h9 := h y v0 v8
  have h10 := S h9
  have h11 := h v1 v1 v1
  have h12 := C h7 h11
  have h13 := C (T h12 h10) h7
  have h14 := h v0 v1 z
  have h15 := S h14
  have h16 := C h7 (S h11)
  have h17 := C (T h9 h16) h7
  have h18 := C h13 h17
  have h19 := T (T (C h17 h2) h18) h15
  have h20 := h y v0 v0
  have h21 := R (M v0 v0)
  have h22 := h (M (M v0 v1) v0) v1 v1
  have h23 := C h17 h13
  have h24 := T (T h14 h23) (C h13 h2)
  T (T (h x v3 v1) (C (T h5 (C h2 (S h6))) (T (T (T (T (C (T (T (T (C (R x) (h v3 v3 v3)) (S (h y x (M v3 v3)))) h9) h16) (R v8)) (C (T (T (T h12 h10) h20) (C h24 (T (T (T (C h17 h21) (C h13 (C (T h14 h23) h24))) (S h22)) h13))) h19)) (C (R (M v8 v1)) h24)) (C (T (T (T (C h19 (T (T (T h17 h22) (C h17 (C (T h18 h15) h19))) (C h13 h21))) (S h20)) h9) h16) h19)) h13))) (C (T (C h2 h6) (S h5)) h2)

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
theorem Equation1790_implies_Equation546 (G: Type _) [Magma G] (h: Equation1790 G) : Equation546 G := fun x y z =>
  let v0 := M z y
  let v1 := M x v0
  let v2 := M z v1
  have h3 := h v2 z y
  have h4 := S h3
  let v5 := M y v2
  let v6 := M v5 z
  have h7 := R v6
  have h8 := h v0 v0 v5
  have h9 := S h8
  have h10 := h y v5 z
  have h11 := C (S h10) (T (C h9 h7) h4)
  let v12 := M v0 v5
  let v13 := M v5 v0
  have h14 := h (M v13 v0) v6 v12
  have h15 := T (C h10 (T h3 (C h8 h7))) (S h14)
  have h16 := R v5
  have h17 := h v0 z y
  have h18 := h v1 y v2
  have h19 := h v0 v2 v5
  let v20 := M v2 v5
  have h21 := R v12
  let v22 := M v0 x
  T (T (T (h x v5 v0) (C (R v13) (T (C (T (T (h v22 v5 v1) (C (R (M v5 v1)) (C (T (h (M v1 v22) v5 v0) (C (T (T (C h16 (T h8 (C h21 (T h14 h11)))) (C h16 (T (T (T (T (C h21 h15) h9) h19) (C (R v20) (T (T (h (M v13 v2) v6 v20) (C (S (h v1 v5 z)) (T (C (S h19) h7) h4))) (C h18 (R v2))))) (S (h (M (M v2 v1) y) v2 v5))))) (S h18)) (C (T (C (R v0) (T (C (R v1) (C h17 (R x))) (S (h (M (M y v0) z) x v0)))) (S h17)) h16))) h16))) (S (h v12 v5 v1))) h15) h9))) h14) h11

@[equational_result]
theorem Equation3185_implies_Equation1098 (G: Type _) [Magma G] (h: Equation3185 G) : Equation1098 G := fun x y z =>
  let v0 := M z y
  let v1 := M x v0
  let v2 := M v1 z
  let v3 := M y v2
  have h4 := S (h v3 z v0)
  have h5 := R z
  have h6 := R v0
  have h7 := R v3
  have h8 := h z z y
  have h9 := h y v0 z
  have h10 := T h9 (C (S h8) h6)
  have h11 := C h10 h7
  have h12 := C (S (h y y v2)) h7
  have h13 := h v2 v3 y
  have h14 := R v1
  have h15 := R v2
  have h16 := h x x v0
  have h17 := C (S h16) h14
  have h18 := h v0 v1 x
  have h19 := S h9
  have h20 := C h8 h6
  have h21 := C (C (T h20 h19) h15) h6
  have h22 := C h10 h15
  have h23 := h v2 z v0
  T (T (h x z v0) (C (C (T (T (T (T (C (T (T (T h20 h19) (h y v1 v2)) (C (C (T (T (T (C (C (T (T (h v1 v0 v3) (C (T (T (C (T (C (C (T h18 h17) h7) h14) (C (C (T (T (T (C h16 h14) (S h18)) (h v0 v1 z)) (C (T (C (T (C (T h23 (C h21 h5)) h6) (C (T (T (T (T (C (C h22 h6) h5) (S h23)) h13) h12) h11) h6)) h5) h4) h14)) h7) h14)) h7) (S (h v3 v3 v1))) h22) h6)) h21) h15) (R y)) (S (h v0 y v2))) h18) h17) h15) h14)) (R x)) (S (h v2 x v1))) h13) h12) h11) h6) h5)) h4

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
theorem Equation4197_implies_Equation3973 (G: Type _) [Magma G] (h: Equation4197 G) : Equation3973 G := fun x y z =>
  let v0 := M z x
  let v1 := M y v0
  let v2 := M v1 z
  let v3 := M z v1
  have h4 := R v2
  have h5 := R z
  have h6 := h v3 z v2
  have h7 := h z v1 v0
  have h8 := R v0
  have h9 := R v1
  have h10 := h v0 z y
  have h11 := h z y v1
  have h12 := h (M (M z y) v0) z v2
  have h13 := h y v0 z
  have h14 := h y v0 x
  have h15 := R x
  have h16 := h x y z
  have h17 := h y z v0
  have h18 := C h4 (T (T (T (T (T (C (T h17 (C (S h16) h8)) h15) (S h14)) h13) h12) (C (C (C h4 (T (C (T h11 (C (S h10) h9)) h8) (S h7))) h5) h4)) (S h6))
  have h19 := h v1 y v1
  have h20 := h v0 v1 y
  have h21 := h v1 v1 v0
  T (T (T (T h16 (h (M v0 y) z v2)) (C (C (T (C h4 (T (T (T (T (T (T (h v0 y v1) (C (S (h v0 v0 y)) h9)) (C (T (C (T (T (T (T (T (h z x y) (h (M (M y z) x) y v2)) (C (C (T h18 (C h4 (T (T (T h6 (C (C (C h4 (T h7 (C (T (C h10 h9) (S h11)) h8))) h5) h4)) (S h12)) (S h13)))) (R y)) h4)) (S (h v1 y v2))) h19) (C (S h20) h9)) h8) (S h21)) h9)) (C (T h21 (C (T (C h20 h9) (S h19)) h8)) h9)) (S (h y v0 v1))) h14) (C (T (C h16 h8) (S h17)) h15))) h18) h5) h4)) (S (h (M v3 z) z v2))) (S (h v1 z z))

@[equational_result]
theorem Equation2349_implies_Equation1504 (G: Type _) [Magma G] (h: Equation2349 G) : Equation1504 G := fun x y z =>
  let v0 := M y z
  let v1 := M z v0
  let v2 := M y x
  let v3 := M v2 v1
  have h4 := R y
  let v5 := M x (M x (M v1 v1))
  have h6 := h v0 v5 z
  have h7 := R z
  have h8 := h v1 x v1
  have h9 := R v5
  have h10 := C h7 (T (C (T h8 (C h9 h8)) h7) (S h6))
  have h11 := R v2
  have h12 := S h8
  have h13 := C h7 (T h6 (C (T (C h9 h12) h12) h7))
  let v14 := M z v1
  let v15 := M x (M x (M z z))
  have h16 := R v15
  have h17 := h z x z
  let v18 := M x (M x (M v3 v3))
  have h19 := h v3 x v3
  let v20 := M v1 (M v1 v3)
  have h21 := h v2 v5 v20
  have h22 := R v20
  have h23 := h v1 v1 v2
  T (T (h x y y) (C (C h4 (T (C h4 (T (T (T h21 (C (T (C h9 (T (C h9 (S h23)) h12)) h12) h22)) (h (M v1 v20) z v3)) (C (T (T (T (C h7 (C h7 (T (T (T (C (R v3) (T (C (T h8 (C h9 (T h8 (C h9 h23)))) h22) (S h21))) (C (T h19 (C (R v18) h19)) h11)) (S (h v1 v18 v2))) h13))) (C h7 (C h7 h10))) (C (T h17 (C h16 (T h17 (C h16 (h z z y))))) (R v14))) (S (h y v15 v14))) (C h11 h13)))) (C h4 (C h4 (C h11 h10))))) h4)) (S (h v3 y y))

@[equational_result]
theorem Equation2511_implies_Equation2982 (G: Type _) [Magma G] (h: Equation2511 G) : Equation2982 G := fun x y z =>
  let v0 := M z x
  let v1 := M y v0
  let v2 := M v1 z
  let v3 := M v2 y
  have h4 := h v3 y v0
  have h5 := S h4
  have h6 := R v0
  let v7 := M y (M (M v3 y) v0)
  have h8 := R x
  have h9 := R z
  have h10 := h y v0 z
  have h11 := S h10
  have h12 := R v2
  have h13 := h v0 v2 z
  have h14 := S h13
  have h15 := C (C h12 h10) h9
  have h16 := h v1 v1 y
  have h17 := R y
  let v18 := M v1 (M (M v1 v1) y)
  let v19 := M v0 v2
  T (T (T (T (h x v19 v2) (C (T (C (R v19) (S (h z x v2))) h11) h12)) (h (M y v2) z v0)) (C (T (T (T (C h9 (T (T (T (C (T (T (T (T (C (C h17 (T (h v2 y z) (C (T (C h17 (T h15 h14)) h16) h9))) h9) (S (h v18 y z))) (h v18 y x)) (C (C h17 (T (C (S h16) h8) (C (h v1 z y) h8))) h8)) (S (h (M z v3) y x))) h6) (C (C h9 (T h4 (C (T (h v7 v0 z) (C (C h6 (T (T (C h5 h9) h15) h14)) h9)) h6))) h6)) (S (h (M v0 v0) z v0))) (C (T h13 (C (C h12 h11) h9)) h6))) (h (M z (M (M v3 z) v0)) v0 x)) (C (C h6 (T (C (S (h v3 z v0)) h8) (C h4 h8))) h8)) (S (h v7 v0 x))) h6)) h5

@[equational_result]
theorem Equation2958_implies_Equation492 (G: Type _) [Magma G] (h: Equation2958 G) : Equation492 G := fun x y z =>
  let v0 := M z (M z y)
  let v1 := M x v0
  let v2 := M y v1
  have h3 := R y
  let v4 := M v2 y
  have h5 := S (h v2 x v2)
  let v6 := M (M x (M x v2)) v2
  have h7 := R v1
  have h8 := S (h y z y)
  let v9 := M v0 y
  let v10 := M (M x (M x x)) x
  have h11 := h v1 v10 x
  have h12 := S h11
  have h13 := R x
  have h14 := h x x x
  have h15 := R v10
  have h16 := T h14 (C h15 h14)
  have h17 := C (C h16 h7) h13
  let v18 := M x v1
  have h19 := S h14
  let v20 := M (M x v18) v1
  have h21 := R v0
  have h22 := h v1 x v1
  let v23 := M x y
  T (T (T (h x x y) (C (T (T (T (T (T (C (C h16 (R v23)) h13) (S (h v23 v10 x))) (C (T (T (h x x v1) (C (T (C (C h16 (R v18)) h13) (S (h v18 v10 x))) h7)) (C (T (C (T (T (h x x v0) (C (T h17 h12) h21)) (C (T h22 (C (R v20) h22)) h21)) h7) (S (h v0 v20 v1))) (T h11 (C (C (T (C h15 h19) h19) h7) h13)))) h3)) (S (h (M v18 x) z y))) h17) h12) h3)) (C (T (T (T (h v1 v9 y) (C (C (T (C (R v9) h8) h8) h7) h3)) (h v4 v6 v2)) (C (C (T (C (R v6) h5) h5) (R v4)) (R v2))) h3)) (S (h v2 v2 y))

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

@[equational_result]
theorem Equation895_implies_Equation3737 (G: Type _) [Magma G] (h: Equation895 G) : Equation3737 G := fun x y z =>
  let v0 := M x y
  let v1 := M y z
  let v2 := M (M x z) v1
  let v3 := M v0 x
  have h4 := R v3
  have h5 := h x x (M (M v2 x) (M x x))
  have h6 := h v2 x x
  have h7 := h x y z
  have h8 := R v2
  have h9 := C h8 (T (C (S h7) (C h6 h6)) (S h5))
  have h10 := h y v2 v2
  have h11 := h y z z
  have h12 := h z v1 x
  have h13 := S h12
  have h14 := R v1
  have h15 := h v1 v1 (M (M z x) (M v1 x))
  have h16 := R z
  have h17 := R (M v0 v0)
  have h18 := R v0
  have h19 := S h6
  have h20 := h v0 v0 (M (M y x) v3)
  have h21 := h y v0 x
  have h22 := T (C h18 (C h21 h21)) (S h20)
  have h23 := S h21
  T (T (h v0 v0 x) (C h18 (T (C (C (T h20 (C h18 (C h23 h23))) (R x)) h4) (C (T (T (T (T (T (C h22 (T (T (h x x y) (C (T (h x y y) (C (R y) h22)) h17)) (C (T (C (T h10 h9) h18) (C (T (T (T (C h8 (T h5 (C h7 (C h19 h19)))) (S h10)) h11) (C h16 (T (C h14 (C h12 h12)) (S h15)))) h18)) h17))) (S (h (M z v1) v0 v0))) (C h16 (T h15 (C h14 (C h13 h13))))) (S h11)) h10) h9) h4)))) (S (h v2 v0 x))

@[equational_result]
theorem Equation1710_implies_Equation1496 (G: Type _) [Magma G] (h: Equation1710 G) : Equation1496 G := fun x y z =>
  let v0 := M z z
  let v1 := M y v0
  let v2 := M v0 v0
  let v3 := M v2 v1
  let v4 := M v1 v1
  let v5 := M v4 y
  let v6 := M y x
  have h7 := S (h v5 v6 x)
  let v8 := M x x
  have h9 := R (M v8 v6)
  have h10 := h x y v1
  let v11 := M v6 v1
  let v12 := M v4 v0
  have h13 := R v12
  have h14 := h z z v6
  have h15 := S h14
  let v16 := M (M v6 v6) z
  have h17 := h v16 v0 x
  let v18 := M v8 v0
  have h19 := R v18
  T (h x y v12) (C (R v6) (T (T (T (T (T (C (T (T (T (T (T (C (T (h v12 (M v0 x) x) (C (S (h x v0 v1)) (S (h x x z)))) (T (h v12 v16 z) (C (T (C (T (T h17 (C (T h15 (h z z z)) h19)) (S (h (M v0 z) v0 x))) h13) (S (h z v0 v1))) h15))) (h v18 z x)) (C (T (T (T (C h14 h19) (S h17)) (h v16 v0 v1)) (C h15 h13)) (R (M v8 z)))) (S (h v12 z x))) (h v12 (M v0 v11) v11)) (C (S (h v11 v0 v1)) (S (h v11 v11 z)))) (R y)) (h (M (M v11 v11) y) v6 x)) (C (T (S (h x y v11)) h10) h9)) h7) (C (R v4) (T (T (h y v0 z) (C (T (T (T (T (h (M v0 y) v6 x) (C (T (S (h x y z)) h10) h9)) h7) (h v5 v1 v0)) (C (S (h v0 y v1)) (R v3))) (R v2))) (S (h v3 v0 z))))) (S (h v1 v1 v0))))

@[equational_result]
theorem Equation3211_implies_Equation3370 (G: Type _) [Magma G] (h: Equation3211 G) : Equation3370 G := fun x y z =>
  let v0 := M z x
  let v1 := M z v0
  have h2 := R v1
  let v3 := M x y
  have h4 := R v3
  have h5 := R y
  have h6 := R v0
  have h7 := R x
  have h8 := h v0 z v1
  have h9 := S h8
  have h10 := R z
  have h11 := h z v1 v0
  have h12 := h v0 z v0
  have h13 := C (C (C (T (C h12 h2) (S h11)) h2) h2) h6
  have h14 := h v1 v0 v1
  have h15 := S (h v1 z v0)
  have h16 := C (S h12) h2
  have h17 := C (T (T (C (T (C (h x z x) h6) (S (h z v0 x))) h6) h14) h13) h10
  have h18 := h z x v0
  have h19 := C (T (T (T (C (T h14 h13) h10) h9) (h v0 v1 v0)) (C (C (C (T (C (T (h v1 z z) (C (C (T (T (T (C (C (T h18 (C (T h17 h9) h7)) h10) h10) (S (h z z x))) h11) h16) h2) h10)) h6) (S (h z v0 v1))) h6) h6) h2)) h10
  T (h v3 v1 y) (C (T (C (C (C (T (h v1 y v3) (C (T (C (C (T (T (T (C (h y x y) h4) (S (h x v3 y))) (h x v1 z)) (C (C (T h19 h15) h7) (T (C (T h18 (C (T (T (T h17 h9) (h v0 v0 z)) (C (C (T (T (C (C (T h8 (C (T (C (C (C (T h11 h16) h2) h2) h6) (S h14)) h10)) h10) h10) (C (T (T (T h19 h15) h14) h13) h10)) h9) h6) h6)) h7)) h6) (S (h x v0 v0))))) h4) h2) (S (h v3 v1 x))) h5)) h5) h5) h4) (S (h y v3 y))) h2)

@[equational_result]
theorem Equation3211_implies_Equation4216 (G: Type _) [Magma G] (h: Equation3211 G) : Equation4216 G := fun x y z =>
  let v0 := M z y
  let v1 := M v0 z
  let v2 := M v1 x
  have h3 := R y
  have h4 := R v2
  have h5 := R v0
  have h6 := h y z y
  have h7 := C (S h6) h5
  have h8 := h z v0 y
  have h9 := R z
  have h10 := h v0 y v0
  have h11 := C (T (C (C (C (T h8 h7) h5) h5) h3) (S h10)) h9
  have h12 := h y z v0
  have h13 := T h12 h11
  let v14 := M x y
  have h15 := h y x v14
  have h16 := S h15
  have h17 := R x
  have h18 := S h12
  have h19 := C (T h10 (C (C (C (T (C h6 h5) (S h8)) h5) h5) h3)) h9
  have h20 := R v14
  have h21 := h x v14 y
  have h22 := h y x y
  have h23 := h v14 v1 v14
  have h24 := C (T (T (T (C (C (C (T (T (T h19 h18) h15) (C (T (C (C (C (T h21 (C (T (T (S h22) h12) h11) h20)) h20) h20) h13) (S h23)) h17)) h17) h20) h20) (S (h v14 v14 x))) h23) (C (C (C (T (C (T (T h19 h18) h22) h20) (S h21)) h20) h20) (T h19 h18))) h17
  have h25 := h x v2 v14
  T (C (T h25 (C (T (T (T h24 h16) (h y v0 z)) (C (T (T (T (C (C (T (h v1 v2 x) (C (T (T (S (h x v1 x)) h25) (C (T (T (T h24 h16) h12) h11) h4)) h4)) h9) h13) (S (h z v1 v2))) h8) h7) h5)) h4)) h3) (S (h v2 y v0))

@[equational_result]
theorem Equation3791_implies_Equation3297 (G: Type _) [Magma G] (h: Equation3791 G) : Equation3297 G := fun x y z =>
  let v0 := M z y
  let v1 := M z v0
  let v2 := M y v1
  have h3 := h v1 v0 v2
  have h4 := h y v1 z
  have h5 := S h4
  have h6 := h z y v1
  let v7 := M v1 z
  have h8 := h v2 v0 v7
  have h9 := h v1 z y
  have h10 := h z v0 v1
  have h11 := S h10
  let v12 := M v0 v1
  have h13 := h v7 v12 v1
  have h14 := S h13
  have h15 := h v1 z v0
  have h16 := S h9
  have h17 := h v0 v1 z
  have h18 := h v1 v2 v0
  have h19 := h v12 v0 v7
  have h20 := h v7 v12 v0
  have h21 := T (T (T (T (T h10 h13) (C (S h17) (T (S h15) h9))) (S h18)) (C h10 h4)) (S h19)
  T (T (T (T (T (T (h x x y) (h (M y x) (M x y) (M x x))) (C (S (h x y x)) (S (h y x x)))) (S (h y y x))) (h y y v0)) (C (R (M v0 y)) (T (T (T (T (h y v0 z) (C (R v0) (T (T (T (T (T (T (h v0 z v0) (C (R (M v0 v0)) h21)) (S (h v0 v12 v0))) (h v0 v12 v1)) (C (T h3 (C (T (T (C h4 h21) (S h20)) h11) (T (T (C h6 h4) (S h8)) h16))) (R (M v12 v1)))) h14) h11))) h17) (C (T (T h10 h20) (C h5 (T (T (T (T (T h19 (C h11 h5)) h18) (C h17 (T h16 h15))) h14) h11))) (T (T h9 h8) (C (S h6) h5)))) (S h3)))) (S (h y v1 v0))

@[equational_result]
theorem Equation2779_implies_Equation3617 (G: Type _) [Magma G] (h: Equation2779 G) : Equation3617 G := fun x y z =>
  let v0 := M z x
  let v1 := M v0 y
  let v2 := M z v1
  have h3 := h v2 y v2
  have h4 := R y
  let v5 := M v2 v2
  let v6 := M (M y v2) v5
  have h7 := R v1
  have h8 := R v0
  let v9 := M x y
  have h10 := h v0 v2 v9
  let v11 := M (M v2 v9) (M v0 v9)
  have h12 := R x
  have h13 := h z z v9
  let v14 := M z v9
  let v15 := M v14 v14
  have h16 := h z x x
  let v17 := M x x
  let v18 := M v17 v0
  let v19 := M y v0
  have h20 := R (M v19 (M v18 v0))
  have h21 := R v17
  let v22 := M x v1
  T (C (T (T (h x y v1) (C (C (R (M y v1)) (T (T (T (T (h v22 v2 v2) (C (C (R v5) (T (T (T (T (T (T (T (h (M v22 v2) x x) (C (T (C h21 (S (h z x v1))) (C h21 h16)) h12)) (S (h v18 x x))) (h v18 y v0)) (C h20 h4)) (C (T h20 (C (R v19) (T (T (T (T (C (T (h v18 z x) (C (C h8 (S h16)) h13)) h8) (S (h v15 v0 z))) (h v15 x z)) (C (C (R (M x z)) (T (S h13) (h z z x))) h12)) (S (h (M v0 v0) x z))))) h4)) (S (h v0 y v0))) h10)) (R v2))) (S (h v11 v2 v2))) (h v11 v1 v2)) (C (T (T (C (R (M v1 v2)) (S h10)) (C (C h7 h3) h8)) (S (h v6 v0 y))) h7))) h4)) (S (h v6 y v1))) h4) (S h3)

@[equational_result]
theorem Equation2789_implies_Equation2586 (G: Type _) [Magma G] (h: Equation2789 G) : Equation2586 G := fun x y z =>
  let v0 := M z y
  let v1 := M v0 x
  let v2 := M y v1
  let v3 := M v2 z
  have h4 := h v2 v3 v3
  have h5 := S h4
  have h6 := R v3
  have h7 := R v2
  have h8 := h v3 (M (M x v3) (M x v2)) v3
  have h9 := h v2 x v3
  have h10 := T (C (C h9 h9) h6) (S h8)
  have h11 := h z v2 v2
  have h12 := T h11 (C h10 h7)
  let v13 := M v3 v3
  have h14 := R v13
  have h15 := C h14 h12
  have h16 := h z v2 z
  have h17 := C (T h16 h15) h6
  have h18 := R v1
  have h19 := S h16
  have h20 := S h11
  have h21 := S h9
  have h22 := C (T h8 (C (C h21 h21) h6)) h7
  have h23 := C h14 (T h22 h20)
  have h24 := T h23 h19
  have h25 := R v0
  have h26 := T (T (T h22 h20) h16) h15
  T (h x v0 z) (C (T (T (T (C (T (T (C h25 h12) (C h25 h26)) (C (T (h v0 y v1) (C (T (C h7 (T (C (T (h y z v3) (C (C (T h17 h5) h25) (T (C h7 h12) (C h7 h26)))) h25) (S (h (M v13 (M v3 v2)) v2 v0)))) (C h7 h24)) h18)) (T (T (T h23 h19) h11) (C h10 (T h4 (C h24 h6)))))) h18) (S (h (M z v3) v3 v1))) h17) h5) (R z))

@[equational_result]
theorem Equation1507_implies_Equation2196 (G: Type _) [Magma G] (h: Equation1507 G) : Equation2196 G := fun x y z =>
  let v0 := M x y
  let v1 := M y z
  let v2 := M v1 z
  let v3 := M v2 v0
  have h4 := S (h v0 v2 v3)
  let v5 := M v3 v2
  let v6 := M v0 (M v0 v3)
  let v7 := M v3 v5
  let v8 := M v1 (M v1 v1)
  have h9 := h z y v0
  let v10 := M v0 (M v0 y)
  let v11 := M z y
  let v12 := M y v0
  let v13 := M y v12
  let v14 := M x v0
  have h15 := h y x v3
  let v16 := M v3 (M v3 x)
  have h17 := R (M x v14)
  let v18 := M y x
  T (T (T (T (T (T (h x y v0) (C (T (T (h v18 y x) (C (T (T (T (T (T (h (M y v18) v0 x) (C (S (h y x y)) h17)) (C h15 h17)) (S (h v16 v0 x))) (h v16 v0 y)) (C (S h15) (R v13))) (R v14))) (S (h v13 y x))) (R v10))) (S (h v12 y v0))) (C (T (T (T (T (h y z v2) (C (T (T (T (T (h v11 z v3) (C (T (T (T (T (h (M z v11) v1 x) (C (T (S (h z y z)) h9) (R (M x (M x v1))))) (S (h v10 v1 x))) (h v10 v1 v1)) (C (S h9) (R v8))) (R (M v3 (M v3 z))))) (S (h v8 z v3))) (h v8 v2 v3)) (C (S (h z v1 v1)) (R v7))) (R (M v2 (M v2 z))))) (S (h v7 z v2))) (h v7 v3 v0)) (C h4 (R v6))) (T (C (h x v0 v3) (h y x v0)) (S (h (M v3 (M v3 v0)) (M v0 x) v0))))) (S (h v6 v0 v3))) (h v6 v5 v3)) (C (S (h v2 v3 v0)) h4)

@[equational_result]
theorem Equation3185_implies_Equation2776 (G: Type _) [Magma G] (h: Equation3185 G) : Equation2776 G := fun x y z =>
  let v0 := M x y
  let v1 := M y z
  let v2 := M v1 v0
  let v3 := M v2 z
  have h4 := h v3 z v0
  have h5 := R z
  have h6 := R v0
  have h7 := R v3
  have h8 := h z v3 v2
  have h9 := h v2 v2 z
  have h10 := C (T (C h9 h7) (S h8)) h6
  have h11 := C (T h8 (C (S h9) h7)) h6
  have h12 := h z v1 v0
  have h13 := C (T (C (S h12) h6) h11) h7
  have h14 := h v1 v3 v0
  have h15 := h v2 y z
  have h16 := R y
  have h17 := R v2
  have h18 := S h14
  have h19 := C (T h10 (C h12 h6)) h7
  have h20 := h v0 v2 v3
  have h21 := T (C (T h14 h13) h17) (S h20)
  have h22 := C (C h21 h5) h16
  have h23 := R v1
  T (T (T (h x z v0) (C (T (T (T (C (T (T (T (C (T (C (T h12 (C (T (C (T h4 (C (T (T (C (T (T (C h11 h7) h19) h18) h6) h15) h22) h5)) h6) (S (h y v0 z))) h23)) h6) (C (C (T (h y v0 x) (C (S (h x x y)) h6)) h23) h6)) (R x)) (S (h v1 x v0))) (h v1 v1 v2)) (C (C (C h21 h23) h17) h23)) h6) (S (h v2 v0 v1))) h15) h22) h5)) (C (T (T (C (C (T h20 (C (T h19 h18) h17)) h5) h16) (S h15)) (C (T (T h14 h13) (C h10 h7)) h6)) h5)) (S h4)

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
theorem Equation1943_implies_Equation522 (G: Type _) [Magma G] (h: Equation1943 G) : Equation522 G := fun x y z =>
  let v0 := M x z
  let v1 := M z v0
  let v2 := M y v1
  let v3 := M y v2
  have h4 := h z v1 v0
  have h5 := S h4
  have h6 := R v3
  have h7 := C h6 h5
  let v8 := M v1 v0
  let v9 := M v1 v8
  have h10 := h v9 y v1
  have h11 := R v0
  have h12 := h z y v1
  have h13 := h v1 v1 v0
  have h14 := S h13
  have h15 := R v9
  have h16 := h v9 v9 v8
  have h17 := C (T (C h6 (T (T (T (C h6 h4) (S h10)) h16) (C (T (C h15 h14) h5) h14))) (S h12)) h11
  have h18 := h x v3 z
  let v19 := M x v0
  have h20 := R (M x v19)
  have h21 := h x z z
  let v22 := M z (M z z)
  have h23 := R (M y (M y v0))
  have h24 := h x v2 z
  let v25 := M v2 (M v2 z)
  T (T (T (T h18 h17) (h v1 y z)) (C (R (M y (M y z))) (T (T (C (R v1) (T (T (T (T (T (T (T (T (T (T (T (T (T h12 (C h6 (T (T (T (C (T h4 (C h15 h13)) h13) (S h16)) h10) h7))) (h (M v3 (M v3 z)) x v0)) (C h20 (T (S h18) h24))) (S (h v25 x v0))) (h v25 y v0)) (C h23 (S h24))) (C h23 h21)) (S (h v22 y v0))) (h v22 x v0)) (C h20 (S h21))) (C h20 (h x x z))) (S (h v19 x v0))) (C (T h18 h17) h11))) h10) h7))) (S (h v3 y z))

@[equational_result]
theorem Equation1761_implies_Equation3601 (G: Type _) [Magma G] (h: Equation1761 G) : Equation3601 G := fun x y z =>
  let v0 := M (M y x) z
  let v1 := M z v0
  let v2 := M v1 v1
  have h3 := R v1
  let v4 := M x y
  have h5 := h y y v4
  have h6 := S h5
  have h7 := R y
  have h8 := h x z v0
  have h9 := S h8
  have h10 := h y x z
  have h11 := C h3 h10
  have h12 := R (M y y)
  have h13 := h v1 y y
  have h14 := T h13 (C h12 (C (T h11 h9) h7))
  have h15 := h v4 v1 y
  have h16 := R (M y v4)
  let v17 := M v4 v1
  have h18 := R v17
  have h19 := h y v4 v1
  have h20 := T h19 (C h18 (T (C h16 h14) h6))
  have h21 := C h3 (S h10)
  have h22 := h x y v1
  have h23 := T (C h12 (C (T h8 h21) h7)) (S h13)
  have h24 := T (C h18 (T h5 (C h16 h23))) (S h19)
  let v25 := M y v1
  have h26 := h v25 v17 y
  have h27 := C (T h26 (C h24 (T (C (T (T (S h22) h8) h21) h20) (S h15)))) h14
  T (T (h v4 v1 v0) (C (R (M v1 v0)) (C (T (T (h v17 y v1) (C (R v25) (T (T (C h24 h3) (C (T h5 (C (T (C h20 (T h15 (C (T (T h11 h9) h22) h24))) (S h26)) h23)) h3)) (C (T (h (M v25 v1) v1 v1) (C (R v2) (T (T (C (C (T h27 h6) h3) h3) h27) h6))) h3)))) (S (h v2 y v1))) (R v0)))) (S (h v1 v1 v0))

@[equational_result]
theorem Equation2399_implies_Equation26 (G: Type _) [Magma G] (h: Equation2399 G) : Equation26 G := fun x y =>
  let v0 := M x y
  let v1 := M v0 y
  have h2 := R x
  let v3 := M x v0
  let v4 := M y v3
  have h5 := h y x v4
  have h6 := S h5
  have h7 := h y y x
  have h8 := R v4
  have h9 := C (C h2 (T h7 (C h8 h7))) h2
  have h10 := R v0
  let v11 := M v0 (M v0 x)
  let v12 := M x (M x (M x x))
  let v13 := M x v3
  have h14 := h x v13 v12
  have h15 := R v13
  have h16 := h x x x
  have h17 := R v12
  have h18 := h y x x
  have h19 := S h7
  let v20 := M v0 (M v0 v1)
  have h21 := R v20
  have h22 := S (h v0 v0 x)
  let v23 := M v0 v13
  have h24 := S h16
  T (T (T (T h14 (C (T (C h15 (T (C h17 h24) h24)) (S h18)) h15)) (h (M y v13) x v0)) (C (C h2 (T (T (T (C (T (T (h v0 v20 v23) (C (T (C h21 (T (C (R v23) h22) h22)) (S (h y v0 v0))) h21)) (C (R y) (C h10 (C h10 (C h10 (T h5 (C (C h2 (T (C h8 h19) h19)) h2))))))) (T (T (C h10 (T (C (T h18 (C h15 (T h16 (C h17 h16)))) h15) (S h14))) h9) h6)) (S (h v11 y v0))) (h v11 v1 x)) (C (C (R v1) (C h2 (C h2 (C h10 (T h9 h6))))) (h v1 v1 x)))) h2)) (S (h v1 x (M v1 (M x (M x v1)))))

