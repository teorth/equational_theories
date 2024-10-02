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
theorem Equation2519_implies_Equation26 (G: Type _) [Magma G] (h: Equation2519 G) : Equation26 G := fun x y =>
  let v0 := M x y
  let v1 := M v0 y
  let v2 := M y v0
  let v3 := M v2 v1
  have h4 := h v1 v0 v3
  have h5 := R v3
  have h6 := h y v1 v0
  have h7 := R v0
  have h8 := h (M v1 v3) x v0
  have h9 := R x
  have h10 := h y y y
  have h11 := C (S h10) h9
  have h12 := C h10 h9
  have h13 := h y v0 v0
  let v14 := M v0 (M v2 v0)
  have h15 := h v14 x v0
  have h16 := R y
  have h17 := S h6
  have h18 := R v1
  have h19 := S (h y v0 x)
  let v20 := M (M y x) v0
  T (T (T (T (T (T (T (h x x y) (C (C h9 (C (T (T (T (T (T (h v0 x v20) (C (C h9 h19) (R v20))) (h (M v0 v20) x x)) (C (C h9 (T (C h19 h9) (C (T (h y v1 x) (C (C h18 (T (C (C h16 (h x y y)) h18) (S (h y y v1)))) h9)) h9))) h9)) (S (h (M v1 y) x x))) (C (T (T (T (T h4 (C (C h7 h17) h5)) h8) (C (T (C h9 (T (C h17 h9) h12)) (C h9 (T h11 (C h13 h9)))) h7)) (S h15)) h16)) h9)) h16)) (S (h v14 x y))) h15) (C (T (C h9 (T (C (S h13) h9) h12)) (C h9 (T h11 (C h6 h9)))) h7)) (S h8)) (C (C h7 h6) h5)) (S h4)

@[equational_result]
theorem Equation3804_implies_Equation3417 (G: Type _) [Magma G] (h: Equation3804 G) : Equation3417 G := fun x y z =>
  let v0 := M y x
  let v1 := M z v0
  let v2 := M z v1
  have h3 := h v1 v1 z
  have h4 := h v2 (M v1 z) v1
  have h5 := R (M v2 v1)
  have h6 := h v1 v0 z
  have h7 := h v2 v0 v1
  have h8 := h v0 v0 z
  have h9 := S h8
  let v10 := M v0 z
  let v11 := M x y
  have h12 := h v0 v0 v11
  let v13 := M y y
  have h14 := h v0 v11 v13
  have h15 := h y x y
  have h16 := h x y y
  have h17 := h y y x
  have h18 := h y y y
  have h19 := S h17
  have h20 := S h15
  T (T (T (T (T (T (T (T (T (T h16 (h v13 v11 v0)) (C (S (h x x y)) (T (T (C h18 h15) (S (h v0 v13 v13))) h20))) (S (h y x x))) h15) (h v0 v13 z)) (C (T (h z v13 v0) (C h20 (R v1))) (R v10))) (h (M v0 v1) v10 v1)) (C (T (T (T h9 h12) (C h19 (T (T h14 (C (S h16) h20)) h19))) (S h18)) (S (h z v1 v0)))) (C (T (T (T (T (T (T (T (T (T (T h18 (C h17 (T (T h17 (C h16 h15)) (S h14)))) (S h12)) h8) (h v1 v10 v1)) (C h9 (T (T (T h3 h4) (C (S h6) h5)) (S h7)))) (S (h v2 v0 v0))) h7) (C h6 h5)) (S h4)) (S h3)) (R v2))) (S (h z v1 v1))

@[equational_result]
theorem Equation952_implies_Equation914 (G: Type _) [Magma G] (h: Equation952 G) : Equation914 G := fun x y z =>
  let v0 := M y x
  let v1 := M z z
  let v2 := M v0 v1
  let v3 := M y v2
  have h4 := h v3 x v0
  have h5 := h x v2 y
  have h6 := h v0 v2 z
  let v7 := M v0 v3
  have h8 := R v7
  let v9 := M (M z v0) (M z v2)
  have h10 := h v9 v7 v2
  have h11 := R x
  let v12 := M z x
  have h13 := R v1
  have h14 := h x z v3
  let v15 := M (M v3 x) (M v3 z)
  have h16 := h v15 z z
  have h17 := h z x y
  let v18 := M (M y z) v0
  have h19 := R (M x x)
  T (T (T (h x x v3) (C h11 (T (C (T (C (R v3) h5) (S (h v1 v3 v0))) (C (T h4 (C h11 (T (C h8 (C h6 h5)) (S h10)))) (T (T (h x x z) (C h11 (C (T (T (T (T (h v12 x v1) (C h11 (C (T (T (T (T (h (M v1 v12) x x) (C h11 (T (C (S (h z x z)) h19) (C h17 h19)))) (S (h v18 x x))) (h v18 v1 x)) (C h13 (T (C (S h17) (C h14 h13)) (S h16)))) (R (M v1 x))))) (S (h v15 x v1))) h16) (C (R z) (C (S h14) h13))) (R v12)))) (S (h (M x v1) x z))))) (S (h v9 v1 x))))) (C h11 (T h10 (C h8 (C (S h6) (S h5)))))) (S h4)

@[equational_result]
theorem Equation952_implies_Equation1053 (G: Type _) [Magma G] (h: Equation952 G) : Equation1053 G := fun x y z =>
  let v0 := M y z
  let v1 := M y v0
  let v2 := M v1 z
  let v3 := M x v2
  have h4 := R v2
  have h5 := S (h z x v2)
  have h6 := R (M v2 x)
  have h7 := h z v2 v0
  let v8 := M (M v0 z) (M v0 v2)
  have h9 := R x
  let v10 := M v1 v2
  have h11 := C h9 (C (T (T (T (T (h (M v2 v10) x v2) (C h9 (C (T (S (h z v2 v1)) h7) h6))) (S (h v8 x v2))) (h v8 v2 v2)) (C h4 (T (C (S h7) (R (M v2 v2))) (S (h z z v1))))) h6)
  have h12 := h v10 x v2
  let v13 := M z x
  let v14 := M y v2
  have h15 := h z x z
  let v16 := M (M z z) v13
  have h17 := R (M x x)
  let v18 := M v1 x
  T (T (h x v2 v1) (C h4 (C (T (T (h v18 x v2) (C h9 (C (T (T (T (T (h (M v2 v18) x x) (C h9 (T (C (S (h z x v1)) h17) (C h15 h17)))) (S (h v16 x x))) (h v16 v2 x)) (C h4 (C (S h15) (R v3)))) h6))) (S (h (M z v3) x v2))) (T (T (T (T (T (T (T (T h12 h11) h5) (h z v14 v1)) (C (R v14) (S (h v0 v2 y)))) (h (M v14 v0) x z)) (C h9 (C (T (S (h v2 z y)) (h v2 z v1)) (R v13)))) (S (h (M v10 v2) x z))) (C (T (T h12 h11) h5) h4))))) (S (h v3 v2 z))

@[equational_result]
theorem Equation2196_implies_Equation759 (G: Type _) [Magma G] (h: Equation2196 G) : Equation759 G := fun x y z =>
  let v0 := M y x
  let v1 := M v0 z
  let v2 := M z v1
  let v3 := M y v2
  let v4 := M v3 v2
  have h5 := h v0 v3 v2
  have h6 := R v3
  have h7 := h v0 z v1
  have h8 := C (S h7) h6
  have h9 := h y v2 v1
  let v10 := M v4 v2
  have h11 := R v10
  have h12 := T (C h7 h6) (S h9)
  let v13 := M (M y v3) v3
  let v14 := M v0 x
  have h15 := R (M v14 x)
  let v16 := M v3 y
  let v17 := M v0 y
  let v18 := M v17 y
  have h19 := h y x v3
  let v20 := M (M x v3) v3
  let v21 := M x y
  T (T (T (T (h x y v1) (C (R (M (M y v1) v1)) (T (T (h v21 y x) (C (R v14) (T (T (T (T (h (M v21 y) v0 x) (C h15 (T (S (h y x y)) h19))) (S (h v20 v0 x))) (h v20 v0 y)) (C (R v18) (S h19))))) (S (h v18 y x))))) (S (h v17 y v1))) (C h7 (T (T (T (T (T (T h9 h8) (C (T (h v0 v3 y) (C (R (M v16 y)) h12)) (h v3 y v3))) (S (h v13 v16 y))) (h v13 v0 x)) (C h15 (T (T (T (C (R v13) (T h5 (C h11 h12))) (S (h v10 y v3))) (h v10 y v2)) (C (R v4) (T (C h11 (T h9 h8)) (S h5)))))) (S (h v4 v0 x))))) (S (h v3 v2 v1))

@[equational_result]
theorem Equation2714_implies_Equation4612 (G: Type _) [Magma G] (h: Equation2714 G) : Equation4612 G := fun x y z =>
  let v0 := M y z
  let v1 := M x y
  have h2 := R v0
  have h3 := h y x v0
  let v4 := M x x
  have h5 := h y (M v4 v1) y
  have h6 := R y
  have h7 := h x x y
  have h8 := T (C (C h7 h7) h6) (S h5)
  have h9 := S h7
  have h10 := C (C h9 h9) h6
  have h11 := T h5 h10
  let v12 := M v4 y
  let v13 := M v12 v12
  let v14 := M v12 y
  let v15 := M x v4
  have h16 := h v12 (M v15 (M x v12)) v12
  have h17 := R v12
  have h18 := h v4 x v12
  have h19 := R v4
  have h20 := h x x v4
  have h21 := S h20
  have h22 := h v4 (M v4 v15) v4
  have h23 := S h18
  T (T (T h16 (C (T (T (C h23 h23) (C (C h20 h20) h19)) (S h22)) h17)) (h (M v4 v12) y z)) (C (T (T (T (C (T (T (C (T (T (T h5 h10) (h v12 v12 y)) (C (R (M v13 v14)) (T (h y v4 y) (C (R v13) h11)))) (T (C (T (T h22 (C (C h21 h21) h19)) (C h18 h18)) h17) (S h16))) (S (h v14 v13 v12))) (C h8 h11)) h2) (C (C h6 h8) h2)) (C (C h3 h3) h2)) (S (h v0 (M v1 (M x v0)) v0))) (R z))

@[equational_result]
theorem Equation4176_implies_Equation4541 (G: Type _) [Magma G] (h: Equation4176 G) : Equation4541 G := fun x y z =>
  let v0 := M z x
  let v1 := M v0 y
  have h2 := R v1
  have h3 := R v0
  have h4 := R y
  have h5 := R x
  have h6 := h y z x
  have h7 := C h6 h4
  let v8 := M y z
  have h9 := R v8
  have h10 := S h6
  have h11 := R z
  have h12 := h x v0 y
  have h13 := h y z v8
  have h14 := h v8 (M z v8) y
  let v15 := M x v8
  T (T (T (h x v8 v1) (C (T (T (T (T (T (C (T (C (T h6 (h v1 x v8)) h2) (S (h v8 v15 v1))) h5) (C (T (h v8 v15 v8) (C (S (h v8 x v8)) h9)) h5)) (S (h v8 v8 x))) (h v8 v8 v0)) (C (T (C (h v8 v0 y) h9) (S (h y v1 v8))) h3)) (C (R (M y v1)) (T (h z x v0) (C (T (T (T (T (T (T (C (T (T (T h12 (C h10 h4)) (C h13 h4)) (S h14)) h11) (C (T (T (T (T (T h14 (C (S h13) h4)) h7) (S h12)) (h x v0 v8)) (C (S (h v8 z x)) h9)) h11)) (S (h v8 v8 z))) (h v8 v8 v1)) (C (T (C (T (h v8 v1 x) (C (C h10 h9) h5)) h9) (S (h x v8 v8))) h2)) (C (T (h x v8 y) (C (T (C h7 h5) (S (h y v1 x))) h4)) h2)) (S (h y y v1))) h3)))) h2)) (S (h (M (M y y) v0) y v1))) (S (h v0 y y))

@[equational_result]
theorem Equation492_implies_Equation725 (G: Type _) [Magma G] (h: Equation492 G) : Equation725 G := fun x y z =>
  let v0 := M z x
  let v1 := M v0 z
  let v2 := M y v1
  let v3 := M y v2
  have h4 := R v2
  have h5 := C h4 (S (h y v1 y))
  have h6 := h v1 v2 y
  have h7 := R v0
  have h8 := C h7 (S (h z x z))
  have h9 := h x v0 z
  have h10 := R y
  have h11 := R x
  have h12 := R z
  have h13 := R v3
  have h14 := h v0 z v1
  have h15 := h z v1 v0
  have h16 := h v0 z v0
  have h17 := R v1
  have h18 := h v1 v0 v1
  T (T (T (T (T h9 h8) h6) h5) (C h4 (T (h y v3 v3) (C h13 (C h10 (T (C h13 (T (C h13 (T (h v3 z v0) (C h12 (T (T (T (C h13 (C h7 (h v1 v1 y))) (S (h v0 v3 v1))) h14) (C h12 (T (C h7 (C h17 (C h17 (T h15 (C h17 (S h16)))))) (S h18))))))) (C h13 (C h12 (T (T (T (C h12 (T h18 (C h7 (C h17 (C h17 (T (C h17 h16) (S h15))))))) (S h14)) (h v0 z v3)) (C h12 (T (C h7 (C h13 (C h13 (T (h z v3 x) (C h13 (C h12 (T (C h11 (C h11 (C h10 (T (h v2 y x) (C h10 (T (C h4 (C h11 (C h11 (T (h y x v2) (C h11 (T (C h10 (C h4 (C h4 (T (T (T h9 h8) h6) h5)))) (S (h v2 y v2)))))))) (S (h x v2 x)))))))) (S (h x x y))))))))) (S (h v3 v0 v3))))))))) (S (h v3 v3 z)))))))) (S (h v3 v2 y))

@[equational_result]
theorem Equation1507_implies_Equation2199 (G: Type _) [Magma G] (h: Equation1507 G) : Equation2199 G := fun x y z =>
  let v0 := M y x
  let v1 := M y z
  let v2 := M v1 z
  let v3 := M v2 v0
  have h4 := S (h v0 v2 v3)
  let v5 := M v3 v2
  let v6 := M v0 (M v0 v3)
  let v7 := M v0 y
  let v8 := M v3 (M v3 v0)
  have h9 := S (h v8 v7 v0)
  have h10 := h y v0 v3
  have h11 := C h10 (h x y v0)
  let v12 := M v3 v5
  let v13 := M v1 (M v1 v1)
  have h14 := h z y v0
  let v15 := M v0 v7
  let v16 := M z y
  let v17 := M y v0
  T (T (T (T (T (T (h x y v3) (C (T (T (T (T h11 h9) (h v8 v7 v8)) (C (T (S h10) (h y v0 y)) (R (M v8 (M v8 v7))))) (S (h (M y v17) v7 v8))) (R (M v3 (M v3 y))))) (S (h v17 y v3))) (C (T (T (T (T (h y z z) (C (T (T (T (T (h v16 z y) (C (T (T (T (T (h (M z v16) v1 x) (C (T (S (h z y z)) h14) (R (M x (M x v1))))) (S (h v15 v1 x))) (h v15 v1 v1)) (C (S h14) (R v13))) (R (M y v1)))) (S (h v13 z y))) (h v13 v2 v3)) (C (S (h z v1 v1)) (R v12))) (R (M z (M z z))))) (S (h v12 z z))) (h v12 v3 v0)) (C h4 (R v6))) (T h11 h9))) (S (h v6 v0 v3))) (h v6 v5 v3)) (C (S (h v2 v3 v0)) h4)

@[equational_result]
theorem Equation2958_implies_Equation1320 (G: Type _) [Magma G] (h: Equation2958 G) : Equation1320 G := fun x y z =>
  let v0 := M y x
  let v1 := M v0 z
  let v2 := M v1 z
  have h3 := R v2
  have h4 := R x
  have h5 := R v0
  have h6 := S (h y v0 y)
  let v7 := M (M v0 (M v0 y)) y
  have h8 := R z
  have h9 := R v1
  have h10 := S (h v0 x v0)
  let v11 := M (M x (M x v0)) v0
  let v12 := M (M v0 (M v0 v1)) v1
  have h13 := h v1 v0 v1
  have h14 := S (h v1 x v1)
  let v15 := M (M x (M x v1)) v1
  have h16 := T (C (R v15) h14) h14
  have h17 := S (h v2 x v2)
  let v18 := M (M x (M x v2)) v2
  have h19 := C (T (C (T (T (T (C (R v18) h17) h17) (h v2 v15 v1)) (C (C h16 h3) h9)) h8) (S (h v1 v1 z))) h3
  have h20 := h z v18 v2
  let v21 := M v1 v2
  T (h x z v2) (C (T (T (C (T (T (C h8 (T (C (T (T (T h20 h19) (h v21 v15 v1)) (C (C h16 (R v21)) h9)) h3) (S (h v1 v1 v2)))) (C (T (T h20 h19) (C (T h13 (C (R v12) h13)) h3)) h9)) (S (h v2 v12 v1))) h4) (C (T (T (T (C (T (h v1 v11 v0) (C (C (T (C (R v11) h10) h10) h9) h5)) h8) (S (h v0 v0 z))) (h v0 v7 y)) (C (C (T (C (R v7) h6) h6) h5) (R y))) h4)) (S (h y y x))) h3)

@[equational_result]
theorem Equation684_implies_Equation2349 (G: Type _) [Magma G] (h: Equation684 G) : Equation2349 G := fun x y z =>
  let v0 := M x (M (M x x) x)
  have h1 := h z x v0
  have h2 := R v0
  have h3 := h x x x
  have h4 := T h3 (C h3 h2)
  have h5 := R z
  have h6 := R x
  let v7 := M z x
  let v8 := M v7 (M (M v7 x) x)
  let v9 := M x v7
  have h10 := h v9 v7 v8
  have h11 := R v8
  have h12 := h v7 v7 x
  have h13 := R v9
  have h14 := R v7
  let v15 := M v7 (M (M v7 y) y)
  have h16 := h v7 v7 y
  have h17 := S h12
  have h18 := T (C h17 h11) h17
  have h19 := S h3
  let v20 := M y v7
  let v21 := M y v20
  let v22 := M v21 x
  T (h x v21 x) (C (R v21) (T (T (T (T (T (T (T (C h6 (C (R v22) h4)) (S (h v22 x v0))) (C (T (C (R y) (T (h v20 v7 v8) (C h14 (C (R v20) h18)))) (S (h v7 y v7))) (T (h x z x) (C (T (T (T h1 (C h6 (C h5 (T (C h19 h2) h19)))) h10) (C h14 (C h13 h18))) (T (T (T (C h6 (C h14 h4)) (S (h v7 x v0))) h16) (C h16 (R v15))))))) (S (h (M v7 (M v9 v7)) v7 v15))) (C h14 (C h13 (T h12 (C h12 h11))))) (S h10)) (C h6 (C h5 h4))) (S h1)))

@[equational_result]
theorem Equation952_implies_Equation4297 (G: Type _) [Magma G] (h: Equation952 G) : Equation4297 G := fun x y z =>
  let v0 := M z z
  have h1 := R (M y x)
  let v2 := M y v0
  have h3 := R x
  let v4 := M z y
  let v5 := M z v2
  let v6 := M x y
  have h7 := h z y v6
  let v8 := M (M v6 z) (M v6 y)
  let v9 := M x v6
  let v10 := M v9 y
  have h11 := h v6 v6 y
  let v12 := M y v6
  let v13 := M v12 v12
  let v14 := M v9 v9
  have h15 := h v9 y v2
  T h15 (C (R y) (T (T (T (T (T (T (T (T (T (T (h (M (M v2 v9) (M v2 y)) x y) (C h3 (C (T (S h15) (h v9 y v9)) h1))) (S (h (M v14 v10) x y))) (C (T (T (T (T (h v14 x v6) (C h3 (C (T (S (h v6 v6 x)) h11) (R (M v6 x))))) (S (h v13 x v6))) (h v13 v9 v6)) (C (R v9) (T (C (S h11) (R (M v6 v9))) (S (h y v6 x))))) (R v10))) (h (M v10 v10) x y)) (C h3 (C (T (S (h y y v9)) (h y y z)) h1))) (S (h (M v4 v4) x y))) (C (T (T (h v4 x v0) (C h3 (C (T (T (T (T (h (M v0 v4) x y) (C h3 (C (T (S (h z y z)) h7) h1))) (S (h v8 x y))) (h v8 v0 y)) (C (R v0) (C (S h7) (R v2)))) (R (M v0 x))))) (S (h v5 x v0))) (R v4))) (h (M v5 v4) x y)) (C h3 (C (S (h v2 y z)) h1))) (S (h v0 x y))))

@[equational_result]
theorem Equation2105_implies_Equation1523 (G: Type _) [Magma G] (h: Equation2105 G) : Equation1523 G := fun x y z =>
  let v0 := M z z
  let v1 := M x v0
  let v2 := M y y
  let v3 := M v2 v1
  let v4 := M v1 v1
  have h5 := R v4
  have h6 := R v2
  have h7 := h v2 y x
  let v8 := M x x
  have h9 := R v8
  have h10 := R y
  have h11 := h y y y
  have h12 := S h11
  have h13 := C h12 h6
  have h14 := h y v2 y
  let v15 := M v3 v3
  have h16 := R v1
  have h17 := h y v2 z
  have h18 := R v0
  have h19 := S h14
  have h20 := C h11 h6
  T (T (T (T (h x v2 z) (C (T (C (C (T (T h7 (C (C (T (T (T h20 h19) (h y v2 x)) (C h12 h9)) h10) h9)) (S (h v8 y x))) (R x)) h6) (S (h x x y))) h18)) (h v1 v1 v1)) (C (T (T (T (C (T (T (T (h v4 y x) (C (C (T (T (T (C h11 h5) (S (h y v2 v1))) h14) h13) h10) h9)) (C (C (T (T (T h20 h19) h17) (C h12 h18)) h10) h9)) (S (h v0 y x))) h16) (C (T (T (h v0 y v2) (C (C (T (T (T (C h11 h18) (S h17)) h14) h13) h10) (R (M v2 v2)))) (S (h v2 y v2))) h16)) (h v3 v3 y)) (C (C (T (T (h v15 y x) (C (C (T (T (T (C h11 (R v15)) (S (h y v2 v3))) h14) h13) h10) h9)) (S h7)) (R v3)) h6)) h5)) (S (h v3 v2 v1))

@[equational_result]
theorem Equation684_implies_Equation692 (G: Type _) [Magma G] (h: Equation684 G) : Equation692 G := fun x y z =>
  let v0 := M z y
  let v1 := M v0 z
  let v2 := M y (M x v1)
  have h3 := S (h v1 v1 v2)
  let v4 := M v1 (M (M v1 v2) v2)
  have h5 := h y z y
  have h6 := h y y x
  have h7 := S h6
  let v8 := M y (M (M y x) x)
  have h9 := R v8
  have h10 := T (C h7 h9) h7
  have h11 := R v0
  have h12 := R y
  have h13 := h v0 y v8
  have h14 := R z
  let v15 := M v0 (M (M v0 x) x)
  let v16 := M z v0
  have h17 := h v16 v0 v15
  have h18 := R v15
  have h19 := h v0 v0 x
  have h20 := R v16
  let v21 := M v0 (M (M v0 y) y)
  have h22 := h v0 v0 y
  have h23 := S h19
  T (h x v1 v4) (C (T (T (T (T (T (C h11 (T (T (h z y v8) (C h12 (C h14 h10))) (C (T (T (T h5 (C h14 (T (C h12 (C h11 (T h6 (C h6 h9)))) (S h13)))) h17) (C h11 (C h20 (T (C h23 h18) h23)))) (T h22 (C h22 (R v21)))))) (S (h (M v0 (M v16 v0)) v0 v21))) (C h11 (C h20 (T h19 (C h19 h18))))) (S h17)) (C h14 (T h13 (C h12 (C h11 h10))))) (S h5)) (C (R x) (T (C h3 (R v4)) h3)))

@[equational_result]
theorem Equation1507_implies_Equation692 (G: Type _) [Magma G] (h: Equation1507 G) : Equation692 G := fun x y z =>
  let v0 := M z y
  let v1 := M v0 z
  let v2 := M x v1
  let v3 := M y v2
  let v4 := M y v3
  let v5 := M x v2
  have h6 := h v1 x v3
  have h7 := S h6
  let v8 := M v3 (M v3 x)
  have h9 := h v8 v2 v3
  let v10 := M v3 (M v3 v2)
  have h11 := R v10
  have h12 := h y z v0
  let v13 := M v3 (M v3 v0)
  have h14 := h y z z
  let v15 := M z (M z z)
  let v16 := M z v0
  let v17 := M z v16
  have h18 := R (M x v5)
  let v19 := M y x
  T (T (h x y v1) (C (T (T (T (T (T (h v19 y z) (C (T (T (T (T (T (h (M y v19) v2 x) (C (S (h v1 x y)) h18)) (C h6 h18)) (S (h v8 v2 x))) h9) (C h7 h11)) (T (T (T (h v16 z x) (C (T (T (T (T (h v17 y x) (C (T (T (T (C h14 (R v17)) (S (h v15 v0 z))) (h v15 v0 v3)) (C (S h14) (R v13))) (R (M x (M x y))))) (S (h v13 y x))) (h v13 v1 v0)) (C (S (h z v0 v3)) (S h12))) (R (M x (M x z))))) (S (h y z x))) h12))) (S (h v10 v1 v0))) (h v10 v1 x)) (C (T (T (T (C h6 h11) (S h9)) (h v8 v2 y)) (C h7 (R v4))) (R v5))) (S (h v4 v1 x))) (R (M v1 (M v1 y))))) (S (h v3 y v1))

@[equational_result]
theorem Equation1902_implies_Equation3692 (G: Type _) [Magma G] (h: Equation1902 G) : Equation3692 G := fun x y z =>
  let v0 := M y y
  let v1 := M z z
  let v2 := M v0 v1
  have h3 := S (h v2 v2 v0)
  let v4 := M v0 v0
  let v5 := M v2 v2
  have h6 := h (M v2 v5) v1 x
  let v7 := M x x
  have h8 := R v7
  have h9 := h v2 v2 z
  have h10 := R v1
  have h11 := h v0 v1 x
  have h12 := C (T (T h11 (C (C h10 h9) h8)) (S h6)) (R v4)
  have h13 := S (h (M v0 v4) v7 x)
  have h14 := C (C h8 (h v0 v0 x)) h8
  have h15 := C (C h8 (S (h v0 x x))) h8
  let v16 := M v0 x
  have h17 := h (M x v16) v7 x
  have h18 := R v0
  let v19 := M v1 (M x v1)
  let v20 := M v7 x
  have h21 := C (R x) (T (T (h v20 v7 v2) (C (C h8 (T (T (T (C (C h8 (h x v1 x)) h8) (S (h v19 v7 x))) (h v19 v0 x)) (C (C h18 (S (h x v1 y))) h8))) (R v5))) (S (h v16 v7 v2)))
  T (T (T (T (T (T (T (T (T (h v7 x x) (C (T (T (T (T (T (T (T (T (T h21 h17) h15) h14) h13) h12) h3) (h v2 v2 x)) (C (T (T h6 (C (C h10 (S h9)) h8)) (S h11)) h8)) (C h18 (h v7 x y))) h8)) (S (h (M x v20) v0 x))) h21) h17) h15) h14) h13) h12) h3

@[equational_result]
theorem Equation3959_implies_Equation3776 (G: Type _) [Magma G] (h: Equation3959 G) : Equation3776 G := fun x y z =>
  let v0 := M z x
  let v1 := M y z
  have h2 := h v1 v0 x
  let v3 := M v0 (M v1 x)
  have h4 := h v3 x y
  have h5 := R y
  let v6 := M v1 v0
  have h7 := R v6
  let v8 := M z v1
  have h9 := h z x v1
  have h10 := S h9
  have h11 := S (h (M x v8) v1 v1)
  have h12 := R v1
  have h13 := C (C h12 h9) h12
  have h14 := h y z v6
  let v15 := M y v6
  have h16 := h x y y
  let v17 := M x y
  let v18 := M y v17
  have h19 := h y v17 v6
  T (T (T (T h16 (C (T (T (T (T (T (T h19 (h (M v17 v15) v6 v6)) (C (T (T (T (T (T (C h7 (S h19)) (h v6 v18 v1)) (C (T (T (T (C (R v18) (T (T h13 h11) h10)) (h v18 v0 y)) (C (C (R v0) (S h16)) h5)) (S (h x v0 y))) h12)) (h (M x v0) v1 x)) (C (T (C (T (T h14 (h (M z v15) v6 v6)) (C (T (T (T (C h7 (S h14)) h13) h11) h10) h7)) (S (h z x x))) (S (h v1 v0 v0))) (R x))) (S (h z v1 x))) h7)) (h v8 v6 z)) (C (C h7 (S (h y z z))) (R z))) (S (h y v6 z))) (C h5 (T h2 h4))) h5)) (S (h (M x (M v3 y)) y y))) (S h4)) (S h2)

@[equational_result]
theorem Equation2958_implies_Equation692 (G: Type _) [Magma G] (h: Equation2958 G) : Equation692 G := fun x y z =>
  let v0 := M (M z y) z
  let v1 := M x v0
  have h2 := R v1
  let v3 := M (M x (M x z)) z
  have h4 := h z x z
  let v5 := M (M v1 (M v1 x)) x
  have h6 := h x x v0
  have h7 := R v0
  have h8 := R x
  have h9 := h x x x
  have h10 := S h9
  let v11 := M (M x (M x x)) x
  have h12 := R v11
  have h13 := h v1 v11 x
  let v14 := M (M x (M x v1)) v1
  let v15 := M v1 v0
  have h16 := h v15 v14 v1
  have h17 := R v15
  have h18 := h v1 x v1
  have h19 := R v14
  have h20 := h x v1 x
  have h21 := S (h v1 y v1)
  let v22 := M (M y (M y v1)) v1
  have h23 := S h18
  T (T (T (T (T (T h6 (C (T (C (C (T h9 (C h12 h9)) h2) h8) (S h13)) h7)) h16) (C (C (T (C h19 h23) h23) h17) h2)) (h (M (M v1 v15) v1) v22 v1)) (C (T (C (T (T (C (R v22) h21) h21) (C (T h20 (C (R v5) h20)) h7)) (T (T (T (C (C (T h18 (C h19 h18)) h17) h2) (S h16)) (C (T h13 (C (C (T (C h12 h10) h10) h2) h8)) h7)) (S h6))) (S (h v0 v5 x))) h2)) (C (T (C (C (T h4 (C (R v3) h4)) (R y)) (R z)) (S (h y v3 z))) h2)

@[equational_result]
theorem Equation684_implies_Equation725 (G: Type _) [Magma G] (h: Equation684 G) : Equation725 G := fun x y z =>
  let v0 := M z x
  let v1 := M v0 z
  let v2 := M v1 (M (M v1 x) x)
  let v3 := M y v1
  have h4 := h v1 v1 x
  let v5 := M x (M (M x x) x)
  have h6 := R v5
  have h7 := h x x x
  have h8 := T h7 (C h7 h6)
  have h9 := R z
  have h10 := R x
  have h11 := S (h v0 v0 y)
  let v12 := M v0 (M (M v0 y) y)
  have h13 := h x z x
  have h14 := S h7
  have h15 := R v0
  have h16 := h v0 x v5
  let v17 := M v0 (M (M v0 x) x)
  let v18 := M z v0
  have h19 := h v18 v0 v17
  have h20 := R v17
  have h21 := h v0 v0 x
  have h22 := R v18
  have h23 := S h21
  T (T (T (T (T (T (T h13 (C h9 (T (C h10 (C h15 h8)) (S h16)))) h19) (C h15 (C h22 (T (C h23 h20) h23)))) (h (M v0 (M v18 v0)) v0 v12)) (C h15 (T (T (C (T (T (T (C h15 (C h22 (T h21 (C h21 h20)))) (S h19)) (C h9 (T h16 (C h10 (C h15 (T (C h14 h6) h14)))))) (S h13)) (T (C h11 (R v12)) h11)) (C h10 (C h9 h8))) (S (h z x v5))))) (h v1 y v1)) (C (R y) (T (C (R v1) (C (R v3) (T h4 (C h4 (R v2))))) (S (h v3 v1 v2))))

@[equational_result]
theorem Equation2319_implies_Equation1523 (G: Type _) [Magma G] (h: Equation2319 G) : Equation1523 G := fun x y z =>
  let v0 := M x x
  let v1 := M z z
  let v2 := M x v1
  let v3 := M y y
  let v4 := M v3 v2
  have h5 := h v4 v0 y
  have h6 := S h5
  have h7 := R v0
  have h8 := h x v3 z
  have h9 := S h8
  have h10 := R x
  have h11 := h v4 x y
  have h12 := C (T h11 (C (C h10 h9) h8)) h7
  let v13 := M v4 v0
  have h14 := R v3
  have h15 := C (T h5 (C (T (C (C h10 h8) h9) (S h11)) h7)) h14
  have h16 := h v3 v1 v2
  have h17 := R v4
  have h18 := T (C h17 (S h16)) h9
  have h19 := h v4 v1 z
  have h20 := T h8 (C h17 h16)
  let v21 := M v1 (M v4 v1)
  have h22 := h v21 x z
  let v23 := M v4 v4
  have h24 := T h12 h6
  T (T (T (T (T h8 h15) (C (T (T (T (T (T (T (h v13 v4 x) (C (C h17 (T (T (C h24 h7) (h v13 v3 v4)) (C (T (T (T (C h14 (C h24 (R v23))) (h (M v3 (M v4 v23)) x y)) (C (T (C h20 (S (h v4 v3 v4))) (C h18 h19)) h10)) (S h22)) h14))) h17)) (S (h v21 v4 y))) h22) (C (T (C h20 (S h19)) (C h18 (h v4 v3 y))) h10)) (S (h (M v3 (M v4 v3)) x y))) (C h14 h15)) h14)) (S (h v13 v3 y))) h12) h6

@[equational_result]
theorem Equation2891_implies_Equation2677 (G: Type _) [Magma G] (h: Equation2891 G) : Equation2677 G := fun x y z =>
  let v0 := M y z
  have h1 := R y
  let v2 := M z v0
  let v3 := M x y
  let v4 := M v3 v0
  have h5 := h x v3 v4
  have h6 := S h5
  have h7 := R v3
  have h8 := h (M (M x (M v3 v4)) v4) x y
  have h9 := S h8
  have h10 := R x
  have h11 := C (C h5 h1) h10
  let v12 := M v4 z
  let v13 := M v3 x
  have h14 := h v13 v12 y
  have h15 := S h14
  have h16 := R v12
  have h17 := h v3 y z
  have h18 := R v13
  have h19 := C (C h6 h1) h10
  have h20 := C (T (C (T h5 (C (T h8 h19) h7)) h1) (C (C h18 h17) h1)) h16
  have h21 := C (T (C (C h18 (S h17)) h1) (C (T (C (T h11 h9) h7) h6) h1)) h16
  have h22 := h v3 y v3
  let v23 := M v3 (M y v3)
  have h24 := h v23 x y
  T (T (T (T h5 (C (T (T (T h8 h19) h14) h21) h7)) (C (T (T (T h20 h15) (C h22 h10)) (S h24)) h7)) (h (M v23 v3) z v0)) (C (C (T (T (C (T (T (C (T (T (T h24 (C (S h22) h10)) h14) h21) h7) (C (T (T (T h20 h15) h11) h9) h7)) h6) (R v2)) (h (M x v2) y z)) (C (S (h x z v0)) h1)) (R v0)) (R z))

@[equational_result]
theorem Equation3398_implies_Equation3286 (G: Type _) [Magma G] (h: Equation3398 G) : Equation3286 G := fun x y z =>
  let v0 := M z z
  let v1 := M y v0
  have h2 := h y v1 v1
  have h3 := h y v1 v0
  have h4 := R v1
  have h5 := h v1 v0 v1
  have h6 := h z z v0
  have h7 := S h6
  have h8 := h z z z
  have h9 := R v0
  have h10 := C h9 h8
  have h11 := h v0 v0 v1
  have h12 := S h11
  have h13 := h y v0 v0
  have h14 := C h4 h13
  have h15 := h v1 v1 v1
  have h16 := C h4 (S h13)
  have h17 := S h8
  have h18 := C h9 h17
  let v19 := M y v1
  let v20 := M z v0
  have h21 := T (T (T (T (T (T (T h2 (C h4 (T (C h4 h3) (S h5)))) (C h4 (C h4 (T (T (T h6 h18) h11) h16)))) (S h15)) h14) h12) h10) h7
  have h22 := R v19
  T (T (T (T (T (T (T (T (T (T (T (T (h x x z) (h z (M x (M x z)) v19)) (C h22 (C (T (T (T (T (C (R x) (T (h x z v19) (C h22 (T (C (R z) (T (T (h x v19 v19) (C h22 (C h21 (R (M x v19))))) (S (h x v0 v19)))) (S (h z x z)))))) (S (h z v19 x))) (h z v19 v0)) (C h9 (C h21 (R v20)))) (S (h z v0 v0))) (R (M z v19))))) (S (h z v20 v19))) h17) h6) h18) h11) h16) h15) (C h4 (C h4 (T (T (T h14 h12) h10) h7)))) (C h4 (T h5 (C h4 (S h3))))) (S h2)

@[equational_result]
theorem Equation2779_implies_Equation2558 (G: Type _) [Magma G] (h: Equation2779 G) : Equation2558 G := fun x y z =>
  let v0 := M y z
  let v1 := M v0 z
  let v2 := M y v1
  let v3 := M v2 x
  have h4 := R v2
  have h5 := R x
  have h6 := h y x z
  let v7 := M (M x z) v0
  have h8 := R (M x x)
  let v9 := M x v1
  have h10 := R (M x v2)
  have h11 := S (h y x v2)
  have h12 := h y v2 y
  let v13 := M (M v2 y) (M y y)
  let v14 := M v2 v1
  have h15 := C (C h10 (T (T (T (T (h (M v14 v2) x v2) (C (C h10 (T (S (h y v2 v1)) h12)) h5)) (S (h v13 x v2))) (h v13 v2 v2)) (C (T (C (R (M v2 v2)) (S h12)) (S (h y y v1))) h4))) h5
  have h16 := h v14 x v2
  let v17 := M v2 z
  T (T (h x v2 v1) (C (C (T (T (T (T (T (T (T (T h16 h15) h11) (h y v17 v1)) (C (S (h v0 v2 z)) (R v17))) (h (M v0 v17) x y)) (C (C (R (M x y)) (T (S (h v2 y z)) (h v2 y v1))) h5)) (S (h (M v2 v14) x y))) (C h4 (T (T h16 h15) h11))) (T (T (h v9 x v2) (C (C h10 (T (T (T (T (h (M v9 v2) x x) (C (T (C h8 (S (h y x v1))) (C h8 h6)) h5)) (S (h v7 x x))) (h v7 v2 x)) (C (C (R v3) (S h6)) h4))) h5)) (S (h (M v3 y) x v2)))) h4)) (S (h v3 v2 y))

@[equational_result]
theorem Equation684_implies_Equation2271 (G: Type _) [Magma G] (h: Equation684 G) : Equation2271 G := fun x y z =>
  have h0 := S (h z z x)
  let v1 := M z (M (M z x) x)
  let v2 := M y z
  let v3 := M y v2
  let v4 := M x v3
  have h5 := h v3 v3 x
  have h6 := S h5
  let v7 := M v3 (M (M v3 x) x)
  have h8 := R v7
  have h9 := T (C h6 h8) h6
  let v10 := M v4 v3
  have h11 := R v3
  have h12 := R v4
  have h13 := R x
  have h14 := S (h v4 v4 x)
  let v15 := M v4 x
  let v16 := M v4 (M v15 x)
  let v17 := M v3 v4
  have h18 := S (h v3 v3 v3)
  let v19 := M v3 (M (M v3 v3) v3)
  let v20 := M x (M (M x x) x)
  have h21 := h x x x
  T (h x v4 x) (C h12 (T (T (T (T (T (T (C h13 (C (R v15) (T h21 (C h21 (R v20))))) (S (h v15 x v20))) (C h12 (T (T (T (T (h x v3 v19) (C h11 (C h13 (T (C h18 (R v19)) h18)))) (h v17 v4 v16)) (C h12 (C (R v17) (T (C h14 (R v16)) h14)))) (C h12 (T (T (C (T (C h11 (C h13 (T h5 (C h5 h8)))) (S (h x v3 v7))) h12) (C h13 (T (h v4 v3 v7) (C h11 (C h12 h9))))) (S (h v3 x v3))))))) (C h12 (T (h v10 v3 v7) (C h11 (C (R v10) h9))))) (S (h v3 v4 v3))) (C (R y) (T (h v2 z v1) (C (R z) (C (R v2) (T (C h0 (R v1)) h0)))))) (S (h z y z))))

@[equational_result]
theorem Equation1537_implies_Equation1993 (G: Type _) [Magma G] (h: Equation1537 G) : Equation1993 G := fun x y z =>
  let v0 := M z z
  let v1 := M x y
  let v2 := M y v0
  let v3 := M v2 v1
  have h4 := h v0 x z
  have h5 := S h4
  have h6 := h z z z
  have h7 := S h6
  have h8 := R v0
  have h9 := h z z v0
  have h10 := R z
  have h11 := C h10 (T h9 (C h8 h7))
  let v12 := M v3 v3
  have h13 := R (M x x)
  have h14 := R v1
  let v15 := M v2 v2
  have h16 := R v2
  have h17 := h z y v0
  let v18 := M y y
  have h19 := R v18
  have h20 := h v18 x z
  have h21 := R y
  have h22 := C h21 (T (T h20 (C h13 (T (C h10 (T (C h19 h6) (S h17))) h11))) h5)
  T (T (T (h x z y) (C h8 (T (C (T (h y z y) (C h8 h22)) h14) (C (T (C h8 (T (T (C h21 (T (T h4 (C h13 (T (C h10 (T (C h8 h6) (S h9))) (C h10 (T h17 (C h19 h7)))))) (S h20))) (h (M y v18) z v2)) (C h8 (C h16 (T (T (T (C h22 h16) (h v15 x z)) (C h13 (T (C h10 (T (C (R v15) h6) (S (h z v2 v0)))) h11))) h5))))) (S (h v2 z v0))) h14)))) (C h8 (T (h v3 z v3) (C h8 (C (R v3) (T (T (h v12 x z) (C h13 (T (C h10 (T (C (R v12) h6) (S (h z v3 v0)))) h11))) h5)))))) (S (h v3 z v0))

@[equational_result]
theorem Equation1774_implies_Equation4673 (G: Type _) [Magma G] (h: Equation1774 G) : Equation4673 G := fun x y z =>
  let v0 := M x z
  let v1 := M v0 y
  let v2 := M x y
  have h3 := h v1 v2 v1
  have h4 := R v1
  have h5 := h z x y
  have h6 := h v1 x z
  have h7 := S h5
  have h8 := R (M x v1)
  have h9 := h y x v1
  let v10 := M v2 z
  have h11 := h v0 x v10
  have h12 := h z x v10
  have h13 := h y x z
  let v14 := M x v10
  have h15 := R v14
  let v16 := M (M x v0) v10
  have h17 := h v16 v14 y
  have h18 := R v10
  have h19 := S h13
  let v20 := M v1 v10
  have h21 := C h19 h18
  have h22 := h v10 v0 v10
  have h23 := h v10 v2 v1
  let v24 := M (M v2 v10) v1
  T (T (T h23 (C h7 (T (T (h v24 z v10) (C (R (M z v10)) (T (T (T (C (T (C h5 (R v24)) (S h23)) h18) (C (T h22 (C h19 h21)) (T h22 (C (T (T h19 (h y v0 v10)) (C h19 (R v20))) h21)))) (S (h v20 y (M y v10)))) (C (T h3 (C h7 (T (T (C h7 h4) (C (T h12 (C h15 h19)) (T h6 (C h11 (T (C h8 h5) (S h9)))))) (S h17)))) h18)))) (S (h v16 z v10))))) (C h5 (T (T h17 (C (T (C h15 h13) (S h12)) (T (C (S h11) (T h9 (C h8 h7))) (S h6)))) (C h5 h4)))) (S h3)

@[equational_result]
theorem Equation2399_implies_Equation3131 (G: Type _) [Magma G] (h: Equation2399 G) : Equation3131 G := fun x y z =>
  let v0 := M y x
  let v1 := M v0 z
  let v2 := M v1 z
  let v3 := M v2 y
  have h4 := R v3
  let v5 := M y (M x (M x y))
  have h6 := R v2
  have h7 := h y y x
  let v8 := M z (M x (M x z))
  have h9 := R v0
  have h10 := h z z x
  let v11 := M v0 (M x (M x v0))
  let v12 := M v0 (M v0 v1)
  have h13 := h v0 v12 v11
  have h14 := R v12
  have h15 := h v0 v0 x
  have h16 := R v11
  have h17 := h z v0 v0
  have h18 := R v1
  have h19 := S h15
  let v20 := M x (M x (M x x))
  have h21 := h x y v20
  have h22 := R y
  have h23 := h x x x
  have h24 := R v20
  have h25 := S h23
  T (T (T (T h21 (C (C h22 (T (C h24 h25) h25)) h22)) (h (M v0 y) v3 y)) (C (C h4 (C h22 (T (T (T (T (C h22 (T (C (C h22 (T h23 (C h24 h23))) h22) (S h21))) h13) (C (T (C h14 (T (C h16 h19) h19)) (S h17)) h14)) (h (M z v12) v3 v1)) (C (T (T (C h4 (C h18 (T (T (C h18 (T (C (T h17 (C h14 (T h15 (C h16 h15)))) h14) (S h13))) (C (C h9 (T h10 (C (R v8) h10))) h9)) (S (h z v0 v8))))) (C (C h6 (T h7 (C (R v5) h7))) h6)) (S (h y v2 v5))) h4)))) h4)) (S (h v3 v3 y))

@[equational_result]
theorem Equation1699_implies_Equation2199 (G: Type _) [Magma G] (h: Equation1699 G) : Equation2199 G := fun x y z =>
  let v0 := M y x
  let v1 := M y z
  let v2 := M (M v1 v1) v1
  let v3 := M v1 z
  have h4 := h v3 v3 v2
  have h5 := R v2
  have h6 := h z v1 v1
  have h7 := h z y z
  have h8 := h v3 v1 v1
  let v9 := M v3 v3
  have h10 := R v9
  let v11 := M v9 v3
  have h12 := h v11 z x
  have h13 := R (M (M z x) x)
  have h14 := R v11
  have h15 := S h6
  have h16 := h v2 v3 v3
  let v17 := M v3 v0
  let v18 := M v17 v0
  let v19 := M v18 v0
  have h20 := R v19
  let v21 := M (M v3 z) z
  have h22 := h v0 y z
  T (T (T (T (h x v0 x) (C (T (T (T (T (T (T (T (T (C h22 (T (h x y z) (C h22 (R v3)))) (S (h v3 (M y v0) v3))) h4) (C h10 (T (C (T h15 h7) h5) (S h8)))) h12) (C (T (T (T (C h6 h14) (S h16)) (h v2 v3 z)) (C h15 (R v21))) h13)) (S (h v21 z x))) (h v21 v17 v0)) (C (S (h v0 v3 z)) h20)) (R (M (M v0 x) x)))) (S (h v19 v0 x))) h20) (C (T (T (T (T (h v18 z x) (C (T (T (T (C h6 (R v18)) (S (h v2 v3 v0))) h16) (C h15 h14)) h13)) (S h12)) (C h10 (T h8 (C (T (S h7) h6) h5)))) (S h4)) (R v0))

@[equational_result]
theorem Equation4197_implies_Equation3823 (G: Type _) [Magma G] (h: Equation4197 G) : Equation3823 G := fun x y z =>
  let v0 := M y x
  let v1 := M z z
  let v2 := M v1 v0
  have h3 := R y
  have h4 := R v2
  have h5 := R v0
  have h6 := R v1
  have h7 := h z z v1
  have h8 := S h7
  have h9 := h z z z
  have h10 := C h9 h6
  have h11 := T h10 h8
  have h12 := C h11 h5
  have h13 := C h12 h6
  have h14 := h v1 v0 v1
  have h15 := S h14
  have h16 := C (S h9) h6
  have h17 := C (T h7 h16) h5
  have h18 := C (T (T (C h17 h6) h15) h17) h6
  have h19 := h v1 v1 v2
  have h20 := C h11 h3
  have h21 := h v1 y v1
  have h22 := S h19
  have h23 := C (T h14 (C (T (T h12 h14) h13) h6)) h4
  T (T (T (h x y y) (C (T (T (T (T (h v0 y v1) (C (C (T (T (T h14 h13) (h v2 v1 v2)) (C (T (C (T (T (T (T h23 h22) h10) h8) h9) h6) h8) h4)) h3) h6)) (S (h v2 y v1))) (h v2 y v2)) (C (T (T (T (T (C (T (T (T h23 h22) h10) h8) h3) h21) (C (T (T h20 h21) (C h20 h6)) h6)) (S (h y v1 v1))) (C h3 (T (T (T (T (T h7 h16) h19) (C (T (T h18 h15) (C (T (T (T h7 h16) h19) (C (T h18 h15) h4)) h5)) h4)) (S (h v2 v0 v2))) (C (T h14 h13) h5)))) h4)) h3)) (S (h (M (M v2 v1) v0) v2 y))) (S (h v1 v0 v2))

@[equational_result]
theorem Equation3804_implies_Equation3370 (G: Type _) [Magma G] (h: Equation3804 G) : Equation3370 G := fun x y z =>
  let v0 := M z x
  let v1 := M z v0
  let v2 := M y v1
  let v3 := M v1 v2
  let v4 := M z z
  let v5 := M v1 z
  let v6 := M v0 v1
  have h7 := h z x x
  let v8 := M x x
  let v9 := M v0 v0
  let v10 := M x y
  have h11 := h z x v0
  let v12 := M v1 v1
  have h13 := h x v1 y
  let v14 := M y y
  let v15 := M v14 v2
  have h16 := R v15
  T (T (T (T (T (T (T (T (T (T (T (T (h x y y) (h v14 v10 v2)) (C (S h13) h16)) (h (M x v1) v15 v2)) (C (T (T (T (C (h y v1 y) h16) (S (h v14 v14 v2))) (S (h y y y))) (h y y x)) (T (T (T (T (C h13 (h y v1 v1)) (S (h v12 v10 v2))) (h v12 v10 v0)) (C (R (M v0 v10)) (T (T (T (C (R v12) h11) (S (h (M v0 x) v1 v1))) (S h11)) h7))) (S (h v8 v10 v0))))) (S (h v8 (M y x) v10))) (S (h y x x))) (h y x v1)) (h (M v1 x) v2 v1)) (C (R v3) (T (T (T (T (C (h v1 x z) (T (T (h z v0 v0) (h v9 v1 v0)) (C (R v6) (T (T (C (R v9) h7) (S (h v8 v0 v0))) (S h7))))) (S (h v6 v5 v0))) (C (T (C (h z x z) (R v1)) (S (h z v4 v0))) (R v5))) (S (h v1 v4 z))) (S (h z v0 z))))) (h v3 v1 v2)) (C (R (M v2 v1)) (S (h y v2 v1)))) (S (h y v1 v2))

@[equational_result]
theorem Equation2196_implies_Equation3553 (G: Type _) [Magma G] (h: Equation2196 G) : Equation3553 G := fun x y z =>
  let v0 := M x z
  let v1 := M v0 z
  have h2 := R v1
  let v3 := M y x
  let v4 := M x y
  let v5 := M v3 x
  let v6 := M y v1
  have h7 := h x y v6
  have h8 := R (M (M v4 x) x)
  let v9 := M (M y v6) v6
  have h10 := h v9 v4 x
  have h11 := S (h v9 v4 v0)
  let v12 := M (M v4 v0) v0
  have h13 := C (R v12) h7
  have h14 := S (h v12 (M y v4) v4)
  have h15 := C (h x y v4) (h y v4 v0)
  let v16 := M v1 x
  have h17 := T (T (h v9 (M v4 y) v16) (C (T (C (S (h v1 x y)) (R v16)) (S (h v1 x z))) (T (T (T (T (T (S (h v4 y v6)) h15) h14) (h v12 x x)) (C (R (M (M x x) x)) (T (T (T (T h13 h11) h10) (C h8 (T (S h7) (h x y x)))) (S (h v5 v4 x))))) (S (h v3 x x))))) (S (h y x z))
  let v18 := M v6 v1
  let v19 := M v18 v1
  let v20 := M v1 y
  T (T (T (T (T (T (T (T (T h15 h14) (h v12 x z)) (C h2 (T h13 h11))) (C h2 h17)) (h v20 y x)) (C (R v5) (T (h (M v20 y) v6 v1) (C (R v19) (S (h y v1 y)))))) (S (h v19 y x))) (C (T (T (h v18 v4 x) (C h8 (T (S (h x y v1)) h7))) (S h10)) h2)) (C h17 h2)

@[equational_result]
theorem Equation3211_implies_Equation4413 (G: Type _) [Magma G] (h: Equation3211 G) : Equation4413 G := fun x y z =>
  let v0 := M y z
  let v1 := M v0 z
  have h2 := h v1 v0 z
  have h3 := S h2
  have h4 := R v0
  have h5 := R v1
  have h6 := R z
  have h7 := h v1 v0 v1
  have h8 := h y y z
  have h9 := S h8
  have h10 := C h9 h6
  have h11 := h z v1 y
  have h12 := h v0 z v1
  have h13 := C (T h11 (C (T (T h10 h12) (C (T (C (C (C (T h11 (C h10 h5)) h5) h5) h4) (S h7)) h6)) h5)) h4
  have h14 := h z y z
  have h15 := C (S h14) h4
  have h16 := h y v0 z
  let v17 := M x y
  have h18 := R v17
  have h19 := S h11
  have h20 := C h8 h6
  have h21 := R x
  let v22 := M x v17
  have h23 := T (T (T h16 h15) h13) h3
  have h24 := R v22
  T (T (T (T (T (C (T (h x v1 y) (C (C (T (T h9 (h y x v17)) (C (T (C (C (T (h v22 v22 v1) (C (C (T (C (C (C (T (T (h x v17 y) (C (S (h y x y)) h18)) (C h23 h18)) h18) h5) h5) (S (h v1 v1 v17))) h24) h24)) h18) h23) (S (h v17 v1 v22))) h21)) h21) (T (T (T h2 (C (T (C (T (T (C (T h7 (C (C (C (T (C h20 h5) h19) h5) h5) h4)) h6) (S h12)) h20) h5) h19) h4)) (C h14 h4)) (S h16)))) h18) (S (h y v17 x))) h16) h15) h13) h3

@[equational_result]
theorem Equation572_implies_Equation4450 (G: Type _) [Magma G] (h: Equation572 G) : Equation4450 G := fun x y z =>
  let v0 := M y z
  let v1 := M v0 z
  have h2 := h z v1 z
  have h3 := S h2
  have h4 := h v0 z z
  have h5 := R v1
  have h6 := C h5 h4
  have h7 := C h5 (S h4)
  have h8 := h z v0 z
  have h9 := h y z z
  have h10 := h y x x
  let v11 := M y x
  let v12 := M x v11
  have h13 := h v11 v12 v11
  have h14 := h x v11 v11
  have h15 := R v12
  have h16 := R x
  have h17 := h v12 x x
  have h18 := R v0
  have h19 := S h17
  have h20 := C h16 (C h16 (C h16 (T h13 (C h15 (S h14)))))
  have h21 := S h9
  have h22 := C h18 (T (T (T h21 h10) h20) h19)
  have h23 := S (h v0 v12 v12)
  have h24 := C h15 (T (C h15 (C h15 (T h2 h7))) (C h15 (C h15 (T (T (T h6 h3) h8) h22))))
  have h25 := R z
  have h26 := h v12 z v12
  T (T h26 (C h25 (T (T (T h24 h23) (h v0 v1 v1)) (C h5 (T (C h5 (C h5 (T (T (T (C h18 (C h18 (T h8 (C h18 (T (T (T (T (T h21 h10) h20) h19) h26) (C h25 (T h24 h23))))))) (S (h z v0 v0))) h8) h22))) (C h5 (T (C h5 (T (T (T (C h18 (T (T (T h17 (C h16 (C h16 (C h16 (T (C h15 h14) (S h13)))))) (S h10)) h9)) (S h8)) h2) h7)) (C h5 (T h6 h3))))))))) (S (h v1 z v1))

@[equational_result]
theorem Equation1320_implies_Equation26 (G: Type _) [Magma G] (h: Equation1320 G) : Equation26 G := fun x y =>
  let v0 := M x y
  let v1 := M v0 y
  have h2 := h v1 x x
  have h3 := S h2
  have h4 := h (M (M (M x v1) x) x) x y
  have h5 := R y
  have h6 := R x
  let v7 := M (M (M v1 v1) x) x
  have h8 := R v7
  have h9 := h x x y
  let v10 := M x x
  let v11 := M (M v10 y) y
  let v12 := M v10 x
  have h13 := h v12 y v1
  have h14 := R v1
  have h15 := h x y x
  have h16 := S h15
  let v17 := M (M (M y x) x) x
  have h18 := h v17 y x
  have h19 := h v17 y y
  have h20 := h v1 y v1
  have h21 := h v1 v1 x
  have h22 := h x x v0
  T (T h22 (C h6 (T (T (T (T (T (h (M (M v10 v0) v0) x x) (C h6 (T (T (T (C (C (S h22) h6) h6) h13) (C h5 (C (C (T (T (T (C h5 (C (C h15 h6) h6)) (S h18)) h19) (C h5 (C (C h16 h5) h5))) h14) h14))) (S h20)))) (C h6 (T h21 (C (T h21 (C (T (T (T (T h20 (C h5 (C (C (T (T (T (C h5 (C (C h15 h5) h5)) (S h19)) h18) (C h5 (C (C h16 h6) h6))) h14) h14))) (S h13)) (h v12 x x)) (C h6 (T (T (C (C (T (T (T (C h6 (C (C h9 h6) h6)) (S (h v11 x x))) (h v11 x y)) (C h6 (C (C (S h9) h5) h5))) h6) h6) h4) (C h6 (C (C h3 h5) h5))))) h8)) h8)))) (S (h (M x (M (M v1 y) y)) x v7))) (C h6 (C (C h2 h5) h5))) (S h4)))) h3

@[equational_result]
theorem Equation4176_implies_Equation3489 (G: Type _) [Magma G] (h: Equation4176 G) : Equation3489 G := fun x y z =>
  let v0 := M y z
  let v1 := M v0 z
  have h2 := R v1
  have h3 := R z
  have h4 := S (h v1 v1 x)
  have h5 := R x
  let v6 := M x x
  have h7 := C (T (h x v6 v1) (C (S (h v1 x x)) h2)) h5
  have h8 := h x x x
  have h9 := C (T (C h8 h5) (S (h x v6 x))) h5
  have h10 := h y z v0
  have h11 := S h10
  let v12 := M z v0
  have h13 := h v12 y z
  have h14 := S h13
  have h15 := h v0 v12 v0
  have h16 := S h15
  have h17 := R v0
  have h18 := h v0 z v0
  have h19 := C h18 h17
  have h20 := h v0 z v1
  have h21 := h v1 (M z v1) v0
  have h22 := h z v1 v0
  T (T (T (T (T h8 h9) h7) h4) (C (T (C (T (T (T (T h10 (C (T h13 (C (T h15 (C (S h18) h17)) h3)) h17)) (S h22)) (h z v1 v6)) (C (T (T (C (C h2 (T (T (h x x z) (C (T (T (T (C (T (h x z v1) (C (C (T (T h22 (C (T (T (C (T (C h20 h17) (S h21)) h3) (C (T (T (T h21 (C (S h20) h17)) h19) h16) h3)) h14) h17)) h11) h5) h2)) h5) (S (h v1 v0 x))) h19) h16) h3)) h14)) h3) (S (h (M v12 y) v0 z))) h11) (T (T (T h8 h9) h7) h4))) h3) (S (h (M v1 v1) y z))) h2)) (S (h y v1 v1))

@[equational_result]
theorem Equation1507_implies_Equation4358 (G: Type _) [Magma G] (h: Equation1507 G) : Equation4358 G := fun x y z =>
  let v0 := M z y
  let v1 := M x v0
  have h2 := S (h v0 x v1)
  have h3 := h x v1 x
  have h4 := C (S h3) h2
  let v5 := M v1 x
  let v6 := M x v1
  let v7 := M x v6
  have h8 := h v7 v5 v1
  let v9 := M y z
  let v10 := M v9 (M v9 v9)
  have h11 := R v7
  have h12 := R v6
  have h13 := h y z v9
  let v14 := M v9 (M v9 z)
  let v15 := M v1 (M v1 v0)
  let v16 := M v1 v5
  let v17 := M x v9
  let v18 := M v0 x
  T (T (T (T (C (R x) (T (C (h y v9 v9) (h z y v9)) (S (h v10 (M v9 y) v9)))) (C (T h3 (C (T (T (T (C (R v1) (T (T (h x v0 x) (R (M v18 v6))) (C (T (T (T (T (h v18 v0 x) (C (T (T (T (T (h (M v0 v18) v17 x) (C (T (S (h v9 x v0)) (h v9 x v1)) (R (M x (M x v17))))) (S (h v16 v17 x))) (h v16 v1 x)) (C h2 h11)) h12)) (S (h v7 v0 x))) h8) h4) (T (h v6 (M v0 z) v0) (C (S (h z v0 x)) (S (h y z v0))))))) (h v15 y v1)) (C (T (T (T (T (C h13 (R v15)) (S (h v14 v0 v1))) (h v14 v0 x)) (C (T (S h13) (h y z y)) h12)) (S (h (M y v9) v0 x))) (R (M v1 (M v1 y))))) (S (h v9 y v1))) h11)) (R v10))) (S (h v7 v9 v9))) h8) h4

@[equational_result]
theorem Equation2196_implies_Equation1793 (G: Type _) [Magma G] (h: Equation2196 G) : Equation1793 G := fun x y z =>
  let v0 := M z y
  let v1 := M v0 x
  let v2 := M y z
  let v3 := M v2 v1
  let v4 := M v3 v1
  have h5 := h y z v2
  let v6 := M (M z v2) v2
  have h7 := R (M (M v2 x) x)
  have h8 := R (M (M y x) x)
  let v9 := M v0 v1
  let v10 := M v9 v1
  have h11 := h z y v1
  let v12 := M (M y v1) v1
  let v13 := M (M v0 v0) v0
  have h14 := R (M (M v1 x) x)
  have h15 := h v0 x v3
  have h16 := h (M (M x v3) v3) v1 x
  have h17 := R (M (M v1 v3) v3)
  let v18 := M x v1
  T (T (h x v1 x) (C h14 (T (T (T (T (T (T (T (h v18 v1 v3) (C h17 (T (T (h (M v18 v1) v1 x) (C h14 (T (S (h v0 x v1)) h15))) (S h16)))) (C h17 (T (T (T h16 (C h14 (S h15))) (C h14 (T (T (T (T (C (h z y v0) (h y v0 v0)) (S (h v13 (M y v0) v0))) (h v13 z x)) (C (R (M (M z x) x)) (T (T (T (C (R v13) h11) (S (h v12 v0 v0))) (h v12 v0 v1)) (C (R v10) (S h11))))) (S (h v10 z x))))) (S (h v9 v1 x))))) (S (h v0 v1 v3))) (h v0 y x)) (C h8 (T (h (M v0 y) v2 x) (C h7 (S (h y z y)))))) (C h8 (T (T (T (C h7 h5) (S (h v6 v2 x))) (h v6 v2 v1)) (C (R v4) (S h5))))) (S (h v4 y x))))) (S (h v3 v1 x))

@[equational_result]
theorem Equation3404_implies_Equation3370 (G: Type _) [Magma G] (h: Equation3404 G) : Equation3370 G := fun x y z =>
  let v0 := M x y
  let v1 := M z x
  have h2 := S (h v0 z y)
  have h3 := h x y z
  have h4 := R y
  have h5 := C h4 (S h3)
  have h6 := h v1 z y
  have h7 := T h6 h5
  have h8 := R z
  have h9 := S (h v1 z x)
  have h10 := h x x z
  have h11 := R x
  let v12 := M z v1
  have h13 := S (h x x v12)
  have h14 := C h11 (S (h v12 x y))
  let v15 := M y v12
  have h16 := h v15 y x
  have h17 := R v12
  have h18 := C h4 (T (T (h z x z) (C h8 (T (T (C h11 (T (T (h z z v12) (C h17 (T (T (T (C h8 (h v12 z y)) (S (h v15 y z))) h16) h14))) h13)) (C h11 h10)) h9))) (C h8 h7))
  have h19 := R v0
  T (h x y y) (C h4 (T (T (T (T (C h4 (T (T (h y x y) (C h4 (T (C h11 (T (T (T (h y y v12) (C h17 (T (T (T (C h4 (h v12 y y)) (S (h v15 y y))) h16) h14))) h13) h10)) h9))) (C h4 h7))) (S (h v0 y y))) (h v0 y v0)) (C h19 (T (T (T (C h4 (T (T (T (C h19 (T h3 (C h8 (T h18 h2)))) (S (h z z v0))) (h z z x)) (C h11 (T (T (T (C h8 (h x z z)) (S (h v1 z z))) h6) h5)))) (S (h v0 x y))) (h v0 x v1)) (C (R v1) (T (T (S (h y v1 x)) h18) h2))))) (S (h z v1 v0))))

