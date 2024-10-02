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
theorem Equation492_implies_Equation2271 (G: Type _) [Magma G] (h: Equation492 G) : Equation2271 G := fun x y z =>
  let v0 := M y z
  let v1 := M y v0
  let v2 := M x v1
  let v3 := M v2 z
  have h4 := R v3
  have h5 := S (h z y v1)
  have h6 := h y v0 y
  have h7 := R v1
  have h8 := h v0 v1 y
  have h9 := h z z y
  have h10 := S h9
  have h11 := R y
  have h12 := h y v1 z
  have h13 := R z
  have h14 := C h13 (T (T h12 (C h7 (C h11 h10))) (C h7 (T h8 (C h7 (S h6)))))
  have h15 := R v0
  have h16 := C h13 (T (C h15 (C h11 (T (h v0 v0 v1) (C h15 (C h15 (T (C h7 (T (T (C h7 (C h11 h9)) (S h12)) h6)) (S h8))))))) (S (h y v0 v0)))
  have h17 := h v0 z y
  have h18 := R v2
  T (T (h x v1 z) (C h7 (T (T (T (C (R x) (T (T h10 (h z v2 z)) (C h18 (C h13 (C h13 (S (h x z y))))))) (S (h v2 x z))) (h v2 v3 v2)) (C h4 (C h18 (C h18 (T (C h18 (T (h v3 v1 y) (C h7 (C h4 (T (T (T (C h11 (T (T (T (C h11 (T (C h11 (T (T h17 h16) h14)) h5)) h17) h16) h14)) h5) (h z v3 v2)) (C h4 (S (h v2 z v2)))))))) (S (h v1 v2 v3))))))))) (S (h v3 v1 v2))

@[equational_result]
theorem Equation3404_implies_Equation3601 (G: Type _) [Magma G] (h: Equation3404 G) : Equation3601 G := fun x y z =>
  let v0 := M y x
  have h1 := R z
  have h2 := R y
  have h3 := h y x z
  let v4 := M x (M z y)
  let v5 := M v0 z
  have h6 := R v5
  have h7 := h z v5 v0
  have h8 := R v0
  let v9 := M v5 v0
  let v10 := M z z
  let v11 := M x y
  have h12 := R x
  have h13 := h y x v0
  let v14 := M v0 y
  let v15 := M z v5
  let v16 := M y y
  T (T (T (T (T (h x y y) (C h2 (C h2 (h y x y)))) (S (h (M x v16) y y))) (C (T (h x v16 y) (C h2 (T (T (T (T (T (T (T (C (T (T (T (h y y v5) (C h6 (T (C h2 (h v5 y z)) (S (h v15 z y))))) (C h6 (T (h v15 z z) (C h1 (S (h v5 z z)))))) (S (h z z v5))) (T (T h13 (C h8 (T (T (h x v14 y) (C h2 (T (T (T (T (T (h v14 v0 x) (C h12 (S h13))) (C h12 (h y x x))) (S (h v11 x x))) (h v11 x z)) (C h1 (S (h y z x)))))) (S (h z z y))))) (h v0 v10 v5))) (S (h v9 v5 v10))) (h v9 v5 z)) (C h1 (S (h v0 z v5)))) h7) (C h8 (T (T (T (h v5 v5 z) (C h1 (T (C h6 h7) (S (h v5 v0 v5))))) (C h1 (C h6 h3))) (S (h v4 v5 z))))) (S (h z v4 v0))) (S h3)))) h2)) (h (M y v0) y z)) (C h1 (S (h v0 z y)))

@[equational_result]
theorem Equation2196_implies_Equation2349 (G: Type _) [Magma G] (h: Equation2196 G) : Equation2349 G := fun x y z =>
  let v0 := M z x
  let v1 := M y v0
  let v2 := M y v1
  let v3 := M v2 z
  let v4 := M (M v2 v3) v3
  let v5 := M v3 v2
  let v6 := M v5 v2
  let v7 := M z v2
  let v8 := M (M v1 v3) v3
  let v9 := M (M v0 v0) v0
  let v10 := M v0 z
  let v11 := M v10 z
  have h12 := h z x v3
  let v13 := M (M x v3) v3
  let v14 := M v0 x
  let v15 := M x z
  T (T (T (T (h x z v3) (C (R (M (M z v3) v3)) (T (T (h v15 z x) (C (R v14) (T (T (T (T (h (M v15 z) v0 x) (C (R (M v14 x)) (T (S (h z x z)) h12))) (S (h v13 v0 x))) (h v13 v0 z)) (C (R v11) (S h12))))) (S (h v11 z x))))) (S (h v10 z v3))) (C (T (T (T (T (C (h z x v0) (h x v0 v0)) (S (h v9 (M x v0) v0))) (h v9 v1 v3)) (C (R v8) (S (h y v0 v0)))) (C (T (h v8 v2 v3) (C (R v4) (S (h y v1 v3)))) (R y))) (T (T (T (h z v2 y) (C (R (M (M v2 y) y)) (T (T (h v7 v2 x) (C (R (M (M v2 x) x)) (T (h (M v7 v2) v3 v2) (C (R v6) (S (h v2 z v2)))))) (S (h v6 v2 x))))) (S (h v5 v2 y))) (C (R v3) (T (C (h y v1 v2) (h v1 v2 v3)) (S (h v4 (M v1 v2) v2))))))) (S (h v3 v4 y))

@[equational_result]
theorem Equation3764_implies_Equation41 (G: Type _) [Magma G] (h: Equation3764 G) : Equation41 G := fun x y z =>
  let v0 := M x x
  have h1 := h y z v0
  have h2 := S h1
  let v3 := M z z
  have h4 := h z x z
  have h5 := h v0 y v0
  have h6 := S h5
  have h7 := h x x x
  let v8 := M y y
  have h9 := R v8
  have h10 := C h9 h7
  have h11 := h x y x
  have h12 := h x y z
  have h13 := S h12
  have h14 := h y y y
  have h15 := C (S h14) (S h4)
  have h16 := h v3 v8 v0
  have h17 := h y z y
  have h18 := R v3
  have h19 := h z z y
  have h20 := T (T (T (T (T (T (T (T (T h19 (C h18 (T (T (T (T (T (T h17 h16) h15) h13) h11) h10) h6))) h2) h17) h16) h15) h13) h11) h10) h6
  have h21 := R v0
  let v22 := M y z
  T (T (T (T (T (T (T (T (T (T (T (h x x z) (C h21 (h z x y))) (S (h v22 x v0))) (h v22 x x)) (C h7 (R (M x v22)))) (S (h v22 v0 x))) (C (T (T h1 (C h18 (T (T (T (T (T (T h5 (C h9 (S h7))) (S h11)) h12) (C h14 h4)) (S h16)) (S h17)))) (S h19)) h21)) (S (h x z x))) (h x z z)) (C (T (h z z z) (C h20 h20)) h4)) (S (h v3 (M v0 y) v0))) h2

@[equational_result]
theorem Equation2399_implies_Equation2196 (G: Type _) [Magma G] (h: Equation2399 G) : Equation2196 G := fun x y z =>
  let v0 := M x y
  let v1 := M y z
  let v2 := M v1 z
  let v3 := M v2 v0
  have h4 := R v3
  let v5 := M x v0
  let v6 := M v0 (M x v5)
  have h7 := R v2
  have h8 := h v0 v0 x
  let v9 := M z (M x (M x z))
  have h10 := R y
  have h11 := h z z x
  let v12 := M y v5
  let v13 := M y (M y v1)
  have h14 := h y v13 v12
  have h15 := R v13
  have h16 := h y y x
  have h17 := R v12
  have h18 := T h16 (C h17 h16)
  have h19 := h z y y
  have h20 := R v1
  have h21 := S h16
  have h22 := R x
  T (T (h x v3 v0) (C (C h4 (C (R v0) (T (T (T (T (T (C (C h22 h18) h22) (S (h y x v12))) h14) (C (T (C h15 (T (C h17 h21) h21)) (S h19)) h15)) (h (M z v13) v3 v1)) (C (T (T (C h4 (C h20 (T (T (C h20 (T (C (T h19 (C h15 h18)) h15) (S h14))) (C (C h10 (T h11 (C (R v9) h11))) h10)) (S (h z y v9))))) (C (C h7 (T h8 (C (R v6) h8))) h7)) (S (h v0 v2 v6))) h4)))) h4)) (S (h v3 v3 v0))

@[equational_result]
theorem Equation3791_implies_Equation3350 (G: Type _) [Magma G] (h: Equation3791 G) : Equation3350 G := fun x y z =>
  let v0 := M z z
  let v1 := M x v0
  let v2 := M v1 x
  let v3 := M x y
  have h4 := R v1
  have h5 := h z z z
  have h6 := S h5
  have h7 := h v0 x v0
  have h8 := h x v0 v0
  let v9 := M v0 x
  have h10 := R v9
  have h11 := T (C h10 h5) (S h8)
  have h12 := h v0 v9 v0
  have h13 := S h7
  have h14 := T (S (h v0 v0 x)) h6
  have h15 := C h14 (T (C h5 h4) h13)
  have h16 := h v9 v0 v1
  have h17 := C h10 h6
  have h18 := h x y v0
  let v19 := M y v0
  T (T (T (T (T (T (T (T h18 (h v9 v19 v1)) (C h14 (T (T (C (h y v0 x) (T (T (T (T (T (T (T h8 h17) h16) h15) h12) (C (R (M v0 v0)) h11)) h13) (h v0 x y))) (S (h v9 v19 v3))) (S h18)))) (h v0 v3 x)) (C (T (T (T (T (T (T h8 h17) h16) h15) h12) (C h6 h11)) (h v0 v1 x)) (T (T (h v3 x x) (C (R (M x v3)) (T (T (h x x v0) (C (T h7 (C h6 h4)) h4)) (S (h v1 x v0))))) (S (h v3 v1 x))))) (S (h v2 v3 v1))) (C (h v1 x y) (h x y v1))) (S (h v3 v2 (M y v1)))) (S (h y v1 x))

@[equational_result]
theorem Equation1495_implies_Equation2 (G: Type _) [Magma G] (h: Equation1495 G) : Equation2 G := fun x y =>
  have h0 := S (h y y y)
  let v1 := M y y
  let v2 := M y (M x y)
  let v3 := M x x
  let v4 := M x v3
  have h5 := h v4 v3 x
  have h6 := S h5
  have h7 := h x x x
  have h8 := C h7 h7
  have h9 := T h8 h6
  have h10 := h x x y
  have h11 := S h10
  let v12 := M y x
  let v13 := M x v12
  have h14 := R v13
  have h15 := S h7
  have h16 := C h15 h15
  have h17 := C (T h5 h16) h14
  have h18 := S (h v3 x x)
  have h19 := h v3 x y
  have h20 := S h19
  have h21 := C (T (T (T (T h10 (C h9 h14)) h20) h8) h6) (R v4)
  have h22 := C (T (T (T (T h5 h16) h19) h17) h11) (T (T (T h21 h18) h8) h6)
  have h23 := C (T (T h20 h8) h6) h22
  have h24 := h v13 v4 x
  have h25 := h v12 x y
  T (T (h x y y) (C (T (T (T (T (T (T h25 (C (T (T h24 h23) h22) h14)) (S (h v4 x y))) (C (T (h x y x) (C (T (T (T h25 (C (T (T (T (T (T (T h24 h23) h22) h21) h18) h8) h6) h14)) h17) h11) (R v2))) h9)) (S (h v2 x x))) (h v2 v1 y)) (C (S (h y y x)) h0)) (R (M y v1)))) h0

@[equational_result]
theorem Equation492_implies_Equation3364 (G: Type _) [Magma G] (h: Equation492 G) : Equation3364 G := fun x y z =>
  let v0 := M x z
  let v1 := M z v0
  let v2 := M y v1
  let v3 := M x y
  have h4 := S (h x y v3)
  have h5 := h x z v0
  have h6 := S h5
  have h7 := h z v0 x
  have h8 := h x z x
  have h9 := R v0
  have h10 := R x
  have h11 := h v0 x v0
  have h12 := R z
  have h13 := C h12 (T h11 (C h10 (C h9 (C h9 (T (C h9 h8) (S h7))))))
  have h14 := R v3
  have h15 := h v1 v2 y
  have h16 := h y v1 y
  have h17 := R v2
  have h18 := R y
  have h19 := C h12 (T (C h10 (C h9 (C h9 (T h7 (C h9 (S h8)))))) (S h11))
  have h20 := C h18 (T (T (T (C h14 (C h14 (T (h v2 v2 x) (C h17 (C h17 (C h10 (T (C (T h5 h19) (T (h v2 y v2) (C h18 (C h17 (C h17 (T (C h17 h16) (S h15))))))) (S (h y v1 v2))))))))) (S (h v3 v3 v2))) (h v3 v1 v3)) (C (T h13 h6) (C h14 (C h14 (T (C h14 (T (T h13 h6) (h x y x))) (S (h y v3 x)))))))
  have h21 := h y v2 v3
  T (C h10 (T h21 (C h17 (T (T (T (T (T h20 h4) h5) h19) h15) (C h17 (T (T (S h16) h21) (C h17 (T h20 h4)))))))) (S (h v2 x v2))

@[equational_result]
theorem Equation684_implies_Equation2519 (G: Type _) [Magma G] (h: Equation684 G) : Equation2519 G := fun x y z =>
  have h0 := R z
  have h1 := S (h y y x)
  let v2 := M y (M (M y x) x)
  let v3 := M x z
  have h4 := R v3
  have h5 := h z z x
  have h6 := S h5
  let v7 := M z (M (M z x) x)
  have h8 := R v7
  have h9 := S (h v3 v3 y)
  let v10 := M v3 y
  let v11 := M v3 (M v10 y)
  have h12 := R x
  let v13 := M v3 (M (M v3 x) x)
  let v14 := M z v3
  have h15 := h v14 v3 v13
  have h16 := R v13
  have h17 := h v3 v3 x
  have h18 := R v14
  have h19 := S h17
  have h20 := S (h z z v10)
  let v21 := M z (M (M z v10) v10)
  T (T (T (T (T (T (h x z v21) (C h0 (C h12 (T (C h20 (R v21)) h20)))) h15) (C h4 (C h18 (T (C h19 h16) h19)))) (h (M v3 (M v14 v3)) v3 v11)) (C h4 (T (C (T (T (T (C h4 (C h18 (T h17 (C h17 h16)))) (S h15)) (C h0 (C h12 (T h5 (C h5 h8))))) (S (h x z v7))) (T (T (T (C h9 (R v11)) h9) (h v3 z v7)) (C h0 (C h4 (T (C h6 h8) h6))))) (S (h z x z))))) (C (T (h v3 y v2) (C (R y) (C h4 (T (C h1 (R v2)) h1)))) h0)

@[equational_result]
theorem Equation1090_implies_Equation1761 (G: Type _) [Magma G] (h: Equation1090 G) : Equation1761 G := fun x y z =>
  let v0 := M x y
  let v1 := M v0 z
  let v2 := M y z
  let v3 := M v2 v1
  have h4 := R z
  have h5 := S (h v1 v3 x)
  let v6 := M (M v1 (M v3 x)) x
  have h7 := R v2
  have h8 := R v3
  let v9 := M (M y (M v0 x)) x
  have h10 := h y v0 x
  have h11 := R x
  have h12 := R v0
  let v13 := M (M z (M v2 x)) x
  have h14 := h y v2 v13
  have h15 := R v13
  have h16 := h z v2 x
  have h17 := R y
  have h18 := T (C h7 (T h16 (C (C h17 h16) h15))) (S h14)
  have h19 := h v0 v3 z
  have h20 := h v2 v0 z
  have h21 := S h16
  T (T (h x v0 z) (C h12 (C (T (T (T (C h11 (C (T (T (T (T h19 (C h8 (C (S h20) h4))) (C h8 h18)) (h (M v3 y) v2 z)) (C h7 (C (T (T (C (T (C h8 (T (T h14 (C h7 (T (C (C h17 h21) h15) h21))) (C h20 h4))) (S h19)) h18) (C h12 (T h10 (C (C h11 h10) (R v9))))) (S (h x v0 v9))) h4))) h4)) (S (h v2 x z))) (h v2 v3 v6)) (C h8 (T (C (C h7 h5) (R v6)) h5))) h4))) (S (h v3 v0 z))

@[equational_result]
theorem Equation914_implies_Equation1137 (G: Type _) [Magma G] (h: Equation914 G) : Equation1137 G := fun x y z =>
  let v0 := M z z
  let v1 := M y v0
  let v2 := M v1 x
  have h3 := h v2 y z
  let v4 := M y y
  have h5 := R v4
  let v6 := M y v2
  have h7 := h v0 v6 v6
  have h8 := R v6
  let v9 := M v6 v0
  let v10 := M v9 (M v6 v6)
  have h11 := R (M x x)
  let v12 := M v1 v1
  have h13 := R y
  let v14 := M v2 v12
  have h15 := h y v6 v2
  have h16 := R v0
  have h17 := h v1 v6 z
  T (T (h x v1 v1) (C (T (T h17 (C h8 (T (T (T (h (M (M v6 v1) v0) v6 z) (C h8 (C (S h17) h16))) (C h8 (T (h (M v1 v0) y z) (C h15 (C (S (h v0 y z)) h16))))) (S (h (M (M v6 y) (M v2 v2)) v6 v0))))) (S h15)) (R v14))) (C h13 (T (T (h v14 y y) (C h13 (T (T (T (T (T (C (T (C h13 (C h3 (R v12))) (S (h v9 y v1))) h5) (h (M v9 v4) v6 x)) (C h8 (T (C (S (h v0 v6 y)) h11) (C h7 h11)))) (S (h v10 v6 x))) (h v10 v6 y)) (C h8 (T (T (C (S h7) h5) (h (M v0 v4) z v0)) (C (R z) (T (C (S (h z z y)) (R (M v0 v0))) (S (h z z z))))))))) (S h3)))

@[equational_result]
theorem Equation1537_implies_Equation452 (G: Type _) [Magma G] (h: Equation1537 G) : Equation452 G := fun x y z =>
  let v0 := M y z
  let v1 := M z v0
  let v2 := M y v1
  let v3 := M x v2
  have h4 := R v1
  have h5 := h y x z
  have h6 := S h5
  have h7 := h v1 x v1
  let v8 := M v1 v1
  have h9 := h v8 x v1
  have h10 := S h9
  have h11 := h y v1 z
  have h12 := C h4 h11
  have h13 := C h4 h6
  let v14 := M x x
  have h15 := R v14
  have h16 := h v14 x v1
  have h17 := h v1 x v14
  have h18 := C (T (T h17 (C h15 (T (C h15 (C h4 (T (T h16 (C h15 (T h13 h12))) h10))) (S h7)))) h6) h4
  let v19 := M v3 v3
  have h20 := R (M v3 v19)
  T (T (h x v0 x) (C (R (M v0 v0)) (T (T (T (C (R x) (T (T (T h16 (C h15 (T h13 (C h4 (h y y z))))) (S (h (M y y) x v1))) (C (R y) (T (T h5 (C h15 (T h7 (C h15 (C h4 (T (T h9 (C h15 (T (C h4 (S h11)) (C h4 h5)))) (S h16))))))) (S h17))))) (h v3 v1 v3)) (C (R v8) h20)) (C h18 (T h20 (C (R v3) (T (T (T (h v19 x v1) (C h15 (T (C h4 (S (h y v3 z))) h12))) h10) h18))))))) (S (h v3 v0 v2))

@[equational_result]
theorem Equation2179_implies_Equation2 (G: Type _) [Magma G] (h: Equation2179 G) : Equation2 G := fun x y =>
  have h0 := S (h y y y)
  let v1 := M y y
  let v2 := M (M y x) y
  have h3 := h x x y
  have h4 := S h3
  have h5 := h x x x
  have h6 := S h5
  have h7 := C h6 h6
  let v8 := M x x
  let v9 := M v8 x
  have h10 := h v9 v8 x
  let v11 := M x y
  let v12 := M v11 x
  have h13 := R v12
  have h14 := C h13 (T h10 h7)
  have h15 := S h10
  have h16 := C h5 h5
  have h17 := S (h v8 x x)
  have h18 := h v8 x y
  have h19 := S h18
  have h20 := C (R v9) (T (T (T (T h3 (C h13 (T h16 h15))) h19) h16) h15)
  have h21 := C (T (T (T h20 h17) h16) h15) (T (T (T (T h10 h7) h18) h14) h4)
  have h22 := C h13 (T (T (T (T (T (T (h v12 v9 x) (C h21 (T (T h19 h16) h15))) h21) h20) h17) h16) h15)
  have h23 := h v11 x y
  T (T (h x y y) (C (R (M v1 y)) (T (T (T (T (T (T (T (T (T (T h23 h22) h19) h16) h15) (h v9 x y)) (C h13 (T (T (T (T h20 h17) h18) h14) h4))) (C h13 (T (h x y x) (C (R v2) (T (T (T h23 h22) h14) h4))))) (S (h v2 x y))) (h v2 v1 y)) (C h0 (S (h y y x)))))) h0

@[equational_result]
theorem Equation4176_implies_Equation4182 (G: Type _) [Magma G] (h: Equation4176 G) : Equation4182 G := fun x y z =>
  have h0 := R x
  let v1 := M x y
  let v2 := M y z
  have h3 := R v1
  have h4 := R v2
  have h5 := R z
  have h6 := h x y z
  have h7 := C (S h6) h0
  have h8 := h z v2 x
  have h9 := T h8 h7
  have h10 := h z v2 y
  have h11 := S h10
  have h12 := R y
  have h13 := h y y z
  let v14 := M v2 z
  let v15 := M v14 x
  have h16 := T (C (T (T (h y z z) (C (T (T (C (T (T (h z z v14) (C (T (T (T (C (h z v14 x) h5) (S (h x v15 z))) (h x v15 y)) (C (S (h y v14 x)) h12)) (R v14))) (S (h y y v14))) h12) (C h13 h12)) h11) h5)) (C h9 h5)) h0) (S (h z v1 x))
  T (T (h x y x) (C (T (C (T (T (h y x x) (C (T (C (T (T (T (T (h x x y) (C (T (C h6 h0) (S h8)) h12)) (C (T h10 (C (S h13) h12)) h12)) (S (h y y y))) h13) h12) h11) h0)) (C h9 h0)) h0) (S (h x v1 x))) h0)) (C (T (T (h x v1 v1) (C (T (T (T (T (C (T (T (T (T (C h6 h3) (C (C h16 h5) h3)) (S (h z z v1))) (h z z y)) (C (T (T (T (C (h z y z) h5) (S (h z v2 z))) h8) h7) h12)) h0) (S (h y v1 x))) (h y v1 v2)) (C (S (h v2 x y)) h4)) (C h16 h4)) h3)) (S (h v2 z v1))) h0)

@[equational_result]
theorem Equation572_implies_Equation1165 (G: Type _) [Magma G] (h: Equation572 G) : Equation1165 G := fun x y z =>
  let v0 := M y x
  let v1 := M z v0
  let v2 := M v1 z
  let v3 := M y v2
  have h4 := S (h v3 y v3)
  have h5 := h y v2 v0
  have h6 := S h5
  have h7 := R (M v0 (M v0 v3))
  have h8 := h z v0 v0
  have h9 := R v1
  have h10 := h v0 v1 v0
  have h11 := C (T h10 (C h9 (S h8))) h7
  have h12 := R v3
  have h13 := C h12 (T h11 h6)
  have h14 := h v0 v3 v0
  have h15 := S h10
  have h16 := C h9 h8
  have h17 := R z
  have h18 := R y
  have h19 := C h18 (C h17 (C h17 (T (C h12 (T h5 (C (T h16 h15) h7))) (S h14))))
  have h20 := h v3 y z
  have h21 := C h12 (T (T (T (T (C h9 (T (C h9 (C h18 (T h20 h19))) (S (h z v1 y)))) h16) h15) h14) h13)
  have h22 := h y v3 v1
  have h23 := R x
  T (T (h x y v3) (C h18 (C h12 (T (T (T (C h12 (C h23 (T (h y x y) (C h23 (T (C h18 (T (T (T (C h18 (T h14 (C h12 (T (T (T h11 h6) h22) h21)))) h4) h20) h19)) (C h18 (T (C h18 (C h17 (C h17 (T h14 h13)))) (S h20)))))))) (S (h y v3 x))) h22) h21)))) h4

@[equational_result]
theorem Equation2105_implies_Equation1496 (G: Type _) [Magma G] (h: Equation2105 G) : Equation1496 G := fun x y z =>
  let v0 := M z z
  let v1 := M y v0
  let v2 := M y x
  let v3 := M v2 v1
  have h4 := R v0
  have h5 := R v3
  have h6 := h v0 z x
  have h7 := S h6
  have h8 := R (M x x)
  have h9 := R z
  have h10 := h z z z
  have h11 := S h10
  have h12 := C h11 h4
  have h13 := h z v0 z
  let v14 := M v3 v3
  have h15 := h y y z
  have h16 := S h15
  have h17 := R y
  let v18 := M y y
  have h19 := h v18 z x
  have h20 := R v18
  have h21 := h z v0 y
  have h22 := C (C (T (T h6 (C (C (T (T (T (C h10 h4) (S h13)) h21) (C h11 h20)) h9) h8)) (S h19)) h17) h4
  have h23 := R v2
  T (T (h x y v1) (C (T (h (M v2 y) v3 z) (C (C (T (T (T (C h5 (T (C h23 (T h15 (C (C (T (T h19 (C (C (T (T (T (C h10 h20) (S h21)) h13) h12) h9) h8)) h7) h17) h4))) (C h23 (T (T (T h22 h16) (h y v0 z)) (C (T h22 h16) h4))))) (h v14 z x)) (C (C (T (T (T (C h10 (R v14)) (S (h z v0 v3))) h13) h12) h9) h8)) h7) h5) h4)) (R (M v1 v1)))) (S (h v3 v0 v1))

@[equational_result]
theorem Equation2779_implies_Equation3601 (G: Type _) [Magma G] (h: Equation2779 G) : Equation3601 G := fun x y z =>
  let v0 := M y x
  let v1 := M v0 z
  let v2 := M z v1
  have h3 := h v2 v1 v0
  have h4 := R x
  have h5 := h z x z
  have h6 := R v0
  have h7 := h x y v2
  let v8 := M (M y v2) (M x v2)
  let v9 := M x y
  let v10 := M v9 x
  let v11 := M x v9
  have h12 := R v11
  have h13 := h y v9 y
  let v14 := M (M v9 y) (M y y)
  have h15 := h v9 x v9
  let v16 := M v11 (M v9 v9)
  T (T (T (T (T h15 (C (T (T (T (h v16 x v0) (C (C (R (M x v0)) (T (T (T (T (C (T (h v16 y x) (C (C h6 (S h15)) h13)) h6) (S (h v14 v0 v9))) (h v14 x v9)) (C (T (C h12 (S h13)) (C h12 (h y v9 x))) h4)) (S (h (M v10 v0) x v9)))) h4)) (S (h v10 x v0))) (C (R v9) h7)) h4)) (S (h v8 x y))) (h v8 v1 y)) (C (T (T (T (T (T (C (R (M v1 y)) (S h7)) (C (T (C (C h6 h5) (R y)) (S (h (M (M x z) (M z z)) y x))) h4)) (S h5)) (h z x v1)) (C (C (R (M x v1)) h3) h4)) (S (h (M (M v1 v0) (M v2 v0)) x v1))) (R v1))) (S h3)

@[equational_result]
theorem Equation4005_implies_Equation41 (G: Type _) [Magma G] (h: Equation4005 G) : Equation41 G := fun x y z =>
  let v0 := M y z
  have h1 := R y
  let v2 := M x x
  let v3 := M z y
  have h4 := h y z v2
  let v5 := M v2 (M v3 v0)
  let v6 := M v2 v3
  have h7 := R v2
  have h8 := h x x x
  have h9 := S h8
  have h10 := R x
  have h11 := h x (M x v2) x
  have h12 := h x x v2
  have h13 := C (C h10 (S h12)) h10
  let v14 := M v2 v2
  have h15 := h x v14 x
  have h16 := T (T h15 h13) h9
  have h17 := h v2 v2 y
  T (T (T (T (T (T (T (T (T h12 (h v14 x v2)) (C (T (T (T (C h7 h16) h17) (C (C h1 h17) h7)) (S (h v2 (M y v14) y))) (R v14))) (S (h v14 y v2))) (C (T (T (T (T (h v2 v2 x) (C h16 (T (T h8 (C (C h10 h12) h10)) (S h15)))) (C h7 (T (T (T h15 h13) (C (C h10 h8) h10)) (S h11)))) (C (T (T h8 (C (C h10 (h x x v0)) h10)) (S (h x (M v0 v2) x))) (T (T h11 (C (C h10 h9) h10)) h9))) (S (h v2 v0 x))) h1)) (C (C h7 h4) h1)) (S (h y v6 v2))) (h y v6 v5)) (C (T (C (R v5) (S h4)) (S (h v0 v3 v2))) h1)) (S (h y z v0))

@[equational_result]
theorem Equation492_implies_Equation1699 (G: Type _) [Magma G] (h: Equation492 G) : Equation1699 G := fun x y z =>
  let v0 := M y z
  let v1 := M v0 z
  have h2 := h z v0 y
  have h3 := S h2
  have h4 := h y z y
  have h5 := R v0
  have h6 := C h5 h4
  have h7 := h y z z
  have h8 := h z y v0
  have h9 := h v1 v0 v1
  have h10 := h v0 z v0
  have h11 := R v1
  have h12 := C h11 (S h10)
  have h13 := h z v1 v0
  have h14 := R z
  have h15 := h v0 z v1
  have h16 := R y
  have h17 := h z z y
  have h18 := S h15
  have h19 := C h5 (C h11 (C h11 (T (C h11 h10) (S h13))))
  have h20 := C h5 (T (C h14 (T (T (C h14 (T h9 h19)) h18) (C h16 (T h17 (C h14 (C h14 (T (C h16 (T h15 (C h14 (T (T (C h5 (C h11 (C h11 (T h13 h12)))) (S h9)) (C h5 (T h2 (C h5 (S h4)))))))) (S h8)))))))) (S h7))
  have h21 := h v0 v1 z
  let v22 := M y x
  T (h x v22 y) (C (R v22) (T (T (T (S (h y x y)) h7) (C h14 (T (T (C h16 (T (C h14 (C h14 (T h8 (C h16 (T (C h14 (T (T (C h5 (T h6 h3)) h9) h19)) h18))))) (S h17))) h21) (C h11 (T (T (T (T (T h20 h6) h3) h13) h12) (C h11 (T h21 (C h11 (T (T h20 h6) h3))))))))) (S (h v1 z v1))))

@[equational_result]
theorem Equation952_implies_Equation928 (G: Type _) [Magma G] (h: Equation952 G) : Equation928 G := fun x y z =>
  let v0 := M y z
  let v1 := M x z
  let v2 := M v0 v1
  let v3 := M y v2
  have h4 := R v0
  have h5 := h v2 y v1
  have h6 := h z v2 y
  let v7 := M (M v1 v2) (M v1 y)
  let v8 := M y v0
  let v9 := M v3 x
  have h10 := R v9
  have h11 := R x
  have h12 := T (C (R v3) h6) (S (h v1 v3 v0))
  have h13 := h z v3 v2
  let v14 := M (M v2 z) (M v2 v3)
  have h15 := h x v0 x
  T (T (T (T (T h15 (C h4 (T (h (M (M x x) (M x v0)) v2 v0) (C h5 (T (T (C (S h15) (R (M v0 v2))) (C h11 (T (T (T (T (T (T (C h4 (T (h v2 z y) (C h13 (R (M v3 v0))))) (S (h v14 v0 v3))) (h v14 z v3)) (C (R z) (T (C (S h13) h12) (C (h z x v3) (R v1))))) (S (h (M (M v3 z) v9) z x))) (C h12 h10)) (C (T (T (h v1 x v0) (C h11 (C (h v2 v0 y) (R (M v0 x))))) (S (h (M v3 v8) x v0))) h10)))) (S (h v8 x v3))))))) (S (h v7 v0 y))) (h v7 y v0)) (C (R y) (C (T (C h4 (T (h v7 z y) (C h6 (C (S h5) h4)))) (S (h (M v0 v3) v0 v2))) (R (M v0 y))))) (S (h v3 y v0))

@[equational_result]
theorem Equation1507_implies_Equation2522 (G: Type _) [Magma G] (h: Equation1507 G) : Equation2522 G := fun x y z =>
  let v0 := M x z
  let v1 := M v0 z
  let v2 := M y v1
  let v3 := M v2 y
  let v4 := M v2 v3
  have h5 := S (h v4 v2 v3)
  let v6 := M v3 (M v3 v2)
  have h7 := S (h v6 v3 v2)
  have h8 := h v1 y v2
  have h9 := C (h y v2 v3) h8
  let v10 := M v1 v2
  let v11 := M v1 (M v1 v1)
  have h12 := R v11
  let v13 := M v1 v10
  let v14 := M v0 (M v0 v0)
  let v15 := M x v0
  have h16 := h z x v3
  let v17 := M v3 (M v3 x)
  let v18 := M z x
  T (T (T (T (T (h x z v1) (C (T (T (T (T (h v18 z x) (C (T (T (T (T (h (M z v18) v0 x) (C (T (S (h z x z)) h16) (R (M x v15)))) (S (h v17 v0 x))) (h v17 v0 v0)) (C (S h16) (R v14))) (R v15))) (S (h v14 z x))) (h v14 v1 v1)) (C (S (h z v0 v0)) h12)) (R (M v1 (M v1 z))))) (S (h v11 z v1))) (h v11 v2 v2)) (C (T (T (T (C (T (T (T (T h9 h7) (h v6 v1 x)) (C (T (T (T (C h8 (R v6)) h5) (h v4 v2 v1)) (C (S h8) (R v13))) (R (M x (M x v1))))) (S (h v13 v1 x))) h12) (S (h v10 v1 v1))) (C h8 (T h9 h7))) h5) (R (M v2 (M v2 v2))))) (S (h v3 v2 v2))

@[equational_result]
theorem Equation3193_implies_Equation1884 (G: Type _) [Magma G] (h: Equation3193 G) : Equation1884 G := fun x y =>
  let v0 := M x x
  have h1 := R v0
  have h2 := h y y v0
  have h3 := S h2
  have h4 := R y
  let v5 := M y v0
  have h6 := h v5 v5 y
  have h7 := S h6
  have h8 := R v5
  have h9 := h v5 y v0
  have h10 := C h9 h8
  have h11 := C (C (T (T (C (T h10 h7) h8) h10) h7) h4) h4
  have h12 := h y v5 v5
  have h13 := C (C (T (C (T (T (T (C (T h12 h11) h4) h3) h12) h11) h4) h3) h1) h1
  have h14 := h v0 y y
  have h15 := R x
  let v16 := M v5 v0
  have h17 := T h14 h13
  have h18 := h v0 v16 v0
  have h19 := S h12
  have h20 := C (S h9) h8
  have h21 := C (C (T (T h6 h20) (C (T h6 h20) h8)) h4) h4
  have h22 := T (C (C (T h2 (C (T (T (T h21 h19) h2) (C (T h21 h19) h4)) h4)) h1) h1) (S h14)
  T (T (T (h x x x) (C (T (C (C (T h18 (C (T (T (T (C (T (C (C (T (h v16 v16 v5) (C (S (h v16 v5 v0)) h22)) h17) (R v16)) (C (R (M (M v16 v0) v16)) h22)) h1) (S h18)) (h v0 v0 x)) (C (S (h v0 x x)) h17)) h1)) h15) h15) (S (h x v0 v16))) h15)) h14) h13

@[equational_result]
theorem Equation3404_implies_Equation3895 (G: Type _) [Magma G] (h: Equation3404 G) : Equation3895 G := fun x y z =>
  let v0 := M y z
  let v1 := M y v0
  have h2 := h y z v0
  have h3 := S h2
  let v4 := M v0 y
  have h5 := R v1
  have h6 := h z v4 y
  have h7 := S h6
  have h8 := h v4 v0 v0
  have h9 := S h8
  have h10 := h y v0 v0
  have h11 := R v0
  have h12 := C h11 h10
  have h13 := h y v0 v1
  have h14 := h (M v1 y) v1 v0
  have h15 := R y
  have h16 := h v1 y v0
  have h17 := R x
  have h18 := S (h v1 v1 x)
  let v19 := M x x
  have h20 := h x x x
  have h21 := C h17 (T (T (T (C h17 h20) (S (h v19 x x))) (h v19 x v1)) (C h5 (S (h x v1 x))))
  T (T (T (T h20 h21) h18) (C h5 (T (T (T (C h15 h2) (C h15 (T (C h11 (T h6 (C h15 (T h8 (C h11 (S h10)))))) (S h16)))) (C h15 (T (h v1 y v19) (C (T (T h20 h21) h18) (T (T (C h15 (C (T (T (h x x y) (C h15 (T (T (T (C h17 (T (h y x v1) (C h5 (C h17 (T (T h16 (C h11 (T (T (C h15 (T (C h11 h13) (S h14))) (C h15 (T (T (T h14 (C h11 (S h13))) h12) h9))) h7))) h3))))) (S (h v0 v1 x))) h12) h9))) h7) h5)) (S (h v0 (M z v4) y))) h3))))) (S (h z (M v1 v1) y))))) (S (h v1 z v1))

@[equational_result]
theorem Equation1165_implies_Equation492 (G: Type _) [Magma G] (h: Equation1165 G) : Equation492 G := fun x y z =>
  let v0 := M z y
  let v1 := M z v0
  let v2 := M x v1
  let v3 := M v2 y
  let v4 := M y v2
  let v5 := M v4 v3
  have h6 := R v0
  have h7 := R v2
  have h8 := h x v2 z
  have h9 := R z
  have h10 := h v0 z x
  have h11 := R v4
  have h12 := R x
  have h13 := R v1
  have h14 := h y v2 v4
  have h15 := h y v2 x
  let v16 := M (M x v3) x
  have h17 := h z y v1
  have h18 := h y z z
  have h19 := h z v1 z
  have h20 := R y
  T (T (T (T (T (T (T h8 (C h7 (C (T (T (S h10) (C (T h17 (C h20 (C (T (C h13 (C h18 h9)) (S h19)) h13))) h20)) (C (T (C h20 (C (T h19 (C h13 (C (S h18) h9))) h13)) (S h17)) h15)) h9))) (S (h v16 v2 z))) (h v16 v2 x)) (C h7 (C (T (C h12 (S h15)) (C h12 h14)) h12))) (S (h (M v5 v4) v2 x))) (C (R v5) (T (h v4 y v1) (C h14 (T (C (T (C h13 (C (T (h y v4 x) (C h11 (C (S (h v1 x y)) h12))) h11)) (S (h x v1 v4))) (C (T (h z v0 v2) (C h6 (C (T (C h7 (C h10 h9)) (S h8)) h7))) h6)) (S (h v2 x v0))))))) (S (h v4 v5 v2))

@[equational_result]
theorem Equation1964_implies_Equation16 (G: Type _) [Magma G] (h: Equation1964 G) : Equation16 G := fun x y =>
  let v0 := M y x
  let v1 := M y v0
  let v2 := M x v1
  have h3 := R (M v1 y)
  have h4 := R v2
  have h5 := h y v1 y
  have h6 := S h5
  have h7 := h x y y
  have h8 := C h7 h3
  have h9 := h y x v1
  have h10 := T h9 (C (T h8 h6) h4)
  have h11 := R v1
  have h12 := S h7
  have h13 := C h12 h3
  have h14 := T (C (T h5 h13) h4) (S h9)
  have h15 := h v1 y x
  have h16 := h v0 x y
  let v17 := M x y
  have h18 := h v17 y v2
  have h19 := R x
  have h20 := T (T (C h19 (T h18 (C (T (C h10 (S h16)) (S h15)) h14))) h8) h6
  let v21 := M x v17
  let v22 := M x x
  have h23 := S h18
  have h24 := C (T h15 (C h14 h16)) h10
  have h25 := C h19 (T h24 h23)
  T (T (h x v1 x) (C (C h11 (T (T (h v22 v1 y) (C (T (T (C h11 (T (C (T (T (T (T h5 h13) h25) (h v21 v1 y)) (C (T (C h11 (C (R y) h20)) h12) (T (T h24 h23) (C h19 (T (T h5 h13) h25))))) (R v22)) (S (h v21 x x)))) (C h11 h20)) (C h11 h10)) h3)) (S (h v2 v1 y)))) (R (M v1 x)))) (S (h v1 v1 x))

@[equational_result]
theorem Equation2196_implies_Equation2925 (G: Type _) [Magma G] (h: Equation2196 G) : Equation2925 G := fun x y z =>
  let v0 := M x z
  let v1 := M y v0
  let v2 := M v1 y
  let v3 := M v2 z
  let v4 := M v3 z
  have h5 := S (h v4 v1 x)
  have h6 := h v1 y y
  let v7 := M (M y y) y
  let v8 := M (M v1 x) x
  have h9 := R v8
  have h10 := C h9 (T (h v7 v2 z) (C (R v4) (S h6)))
  let v11 := M v2 y
  let v12 := M v11 y
  have h13 := C h9 (T (C (R v12) h6) (S (h v7 v2 y)))
  have h14 := h v12 v1 x
  have h15 := R (M (M z v0) v0)
  have h16 := h y v0 v3
  have h17 := C (R v11) (S h16)
  let v18 := M (M v0 v3) v3
  have h19 := h v18 v1 y
  have h20 := S (h v18 v1 x)
  let v21 := M v0 z
  have h22 := R (M (M z x) x)
  T (T (T (h x z v0) (C h15 (T (T (T (T (T (T (h v0 z x) (C h22 (T (T (h v21 z x) (C h22 (T (T (T (T (T (T (T (T (h (M v21 z) v1 x) (C h9 (T (S (h y v0 z)) h16))) h20) h19) h17) h14) h13) h10) h5))) (S (h v3 z x))))) (S (h v2 z x))) (C (T (C (h y v0 v1) (h v0 v1 x)) (S (h v8 (M v0 v1) v1))) h16)) h20) h19) h17))) (C h15 (T (T (T h14 h13) h10) h5))) (S (h v3 z v0))

@[equational_result]
theorem Equation2714_implies_Equation3770 (G: Type _) [Magma G] (h: Equation2714 G) : Equation3770 G := fun x y z =>
  let v0 := M x z
  have h1 := R v0
  let v2 := M y z
  let v3 := M x v2
  let v4 := M x y
  have h5 := R v2
  have h6 := h y x v2
  have h7 := R y
  have h8 := h y v4 v0
  have h9 := S h8
  let v10 := M v4 v0
  have h11 := h v10 x z
  have h12 := R z
  have h13 := R v10
  have h14 := h x x y
  have h15 := R v4
  have h16 := h x x v4
  have h17 := S h16
  have h18 := h v4 (M (M x x) (M x v4)) v4
  have h19 := T h18 (C (C h17 h17) h15)
  have h20 := T (C h19 h7) (S h14)
  have h21 := T (C (C h16 h16) h15) (S h18)
  have h22 := T h14 (C h21 h7)
  let v23 := M v4 v4
  have h24 := T h11 (C (T (C (C h22 h13) h1) h9) h12)
  T (T (h v4 v4 v0) (C (C (C h15 h19) h13) h1)) (C (T (T (T (C (C h15 h21) h24) (C (T (h v23 x y) (C (T (T (T (C (C (T h14 (C h21 (T h8 (C (C h20 h24) h1)))) (R v23)) h15) (S (h (M v3 v0) v4 v4))) (C (C h22 (T (C (T h8 (C (C h20 h13) h1)) h12) (S h11))) h1)) h9) h7)) h5)) (C (C h6 h6) h5)) (S (h v2 (M v4 v3) v2))) h1)

@[equational_result]
theorem Equation4197_implies_Equation4364 (G: Type _) [Magma G] (h: Equation4197 G) : Equation4364 G := fun x y z =>
  let v0 := M z x
  let v1 := M y v0
  have h2 := R v1
  have h3 := R z
  have h4 := R y
  let v5 := M y z
  have h6 := R x
  let v7 := M x v5
  have h8 := h x v5 z
  have h9 := R v5
  have h10 := h z x y
  have h11 := h x y v5
  have h12 := C h2 (T (C (T h11 (C (S h10) h9)) h3) (S h8))
  have h13 := C (T (C h10 h9) (S h11)) h3
  have h14 := R v7
  have h15 := h y z x
  let v16 := M x y
  have h17 := h (M v16 z) x v1
  have h18 := h v7 x v1
  have h19 := T (T (T h15 h17) (C (C h12 h6) h2)) (S h18)
  T (T (T (T (T h8 h13) (h v16 z v1)) (C (C (C h2 (T (h x y v0) (C (T (C (T (C (T (T (T h10 (h (M v5 x) y v1)) (C (C (T (C h2 (T (T (T (T (h v5 x v7) (C (T (C (T (C h14 h19) (C (C h6 h19) (T (T (T h18 (C (C (C h2 (T h8 h13)) h6) h2)) (S h17)) (S h15)))) h6) (S (h (M v7 x) v5 x))) h14)) (S (h x v5 v7))) h8) h13)) h12) h4) h2)) (S (h v7 y v1))) h6) (S (h v5 y x))) h4) (S (h z y y))) (R v0)))) h3) h2)) (S (h (M (M z y) v0) z v1))) (S (h y v0 z))

@[equational_result]
theorem Equation3804_implies_Equation3979 (G: Type _) [Magma G] (h: Equation3804 G) : Equation3979 G := fun x y z =>
  let v0 := M z z
  let v1 := M y v0
  have h2 := h v1 x v0
  have h3 := h z z z
  have h4 := S h3
  have h5 := h y v0 v0
  have h6 := S h5
  have h7 := R v1
  have h8 := C h3 h7
  have h9 := T h8 h6
  have h10 := C h9 h4
  have h11 := h v0 v1 v0
  have h12 := C h4 h7
  let v13 := M v0 x
  have h14 := R v13
  have h15 := h y x v0
  have h16 := T h5 h12
  let v17 := M x y
  let v18 := M v1 x
  have h19 := R v18
  have h20 := h v0 x v1
  let v21 := M x v0
  T (T (T (T (T (T (h x y v0) (h (M v0 y) v21 v1)) (C (T (T (T (T (T (C h16 (R v21)) (C (T (T (h v0 v1 v18) (C (T (C h19 h16) (S h20)) (T (C h3 (T (T (h v1 x y) (C (T (T (T h15 (h v13 v1 v0)) (C (T h11 h10) (T (T (T (C h14 h3) (S (h v0 x v0))) h20) (C h19 h9)))) (S (h v18 v0 v1))) (h v1 y x))) (S (h v17 v0 v18)))) (S (h v17 v0 v0))))) (S (h v17 x v0))) (h x v0 y))) (S (h v1 x v17))) h2) (C h14 (T (T (T (C h16 h3) (S h11)) h8) h6))) (S h15)) (S (h y y v0)))) (S (h y x y))) h15) (C h14 (T (T (T h5 h12) h11) h10))) (S h2)

@[equational_result]
theorem Equation3804_implies_Equation4162 (G: Type _) [Magma G] (h: Equation3804 G) : Equation4162 G := fun x y z =>
  let v0 := M y x
  let v1 := M v0 z
  let v2 := M v1 y
  let v3 := M y z
  have h4 := h y x x
  have h5 := S h4
  have h6 := S (h y x y)
  let v7 := M x x
  have h8 := S (h y y x)
  let v9 := M x y
  have h10 := h x y x
  have h11 := h x x x
  let v12 := M v1 x
  let v13 := M v12 v0
  have h14 := R v13
  have h15 := h v7 v0 v7
  have h16 := h y z v0
  let v17 := M v1 z
  let v18 := M y v1
  T (T (T (T (T (T (T (T (T (T h10 (h v9 v7 v0)) (C (T (T (C h4 h11) (S h15)) h5) h8)) h6) (h y x v1)) (h v12 v18 v0)) (C (T (T (T (h v0 v18 v17) (C (T (S (h y z v1)) h16) (T (T (T (h v0 v17 v1) (C (R (M v1 v17)) (h v0 v1 z))) (S (h (M z v1) v17 v1))) (S (h v1 v1 z))))) (S (h v1 (M y v0) v1))) (S h16)) h14)) (h v3 v13 v0)) (C (T (T (T (C (T (T h4 h15) (C h5 (S h11))) h14) (S (h v12 v7 v0))) (C (h v1 x y) (T (T (T h11 (C (R v7) (T (T (T (h x x y) (C h4 h10)) (S (h v9 v0 v7))) h8))) (h v7 (M y y) v0)) (C h6 h5)))) (S (h v0 v2 v0))) (R (M v3 v0)))) (S (h v3 v2 v0))) (S (h v1 z y))

@[equational_result]
theorem Equation627_implies_Equation2443 (G: Type _) [Magma G] (h: Equation627 G) : Equation2443 G := fun x y =>
  let v0 := M x x
  let v1 := M v0 y
  let v2 := M x v1
  let v3 := M v2 x
  have h4 := h x v2 v3
  have h5 := R v3
  have h6 := h x x x
  have h7 := S h6
  let v8 := M v0 x
  let v9 := M x v8
  have h10 := R v9
  have h11 := R v2
  have h12 := C h11 (C h11 (T (C h7 h10) h7))
  have h13 := h v2 x v9
  let v14 := M v1 v8
  have h15 := h x v1 v14
  have h16 := R v14
  have h17 := h v1 x x
  have h18 := R x
  have h19 := T (C h18 (C (T (C h18 (C h18 (T h17 (C h17 h16)))) (S h15)) (T (T h13 h12) (C (T h13 h12) h5)))) (S h4)
  have h20 := h x x v2
  have h21 := S h13
  have h22 := C h11 (C h11 (T h6 (C h6 h10)))
  have h23 := S h17
  have h24 := S (h y x y)
  let v25 := M y (M (M x y) y)
  have h26 := R v0
  T h20 (C (T (T (T (T h20 (C h18 h19)) (h v0 y v25)) (C h26 (C h26 (T (C h24 (R v25)) h24)))) (C (T (C h18 (T h4 (C h18 (C (T h15 (C h18 (C h18 (T (C h23 h16) h23)))) (T (T (C (T h22 h21) h5) h22) h21))))) (S h20)) (R v1))) h19)

@[equational_result]
theorem Equation1943_implies_Equation16 (G: Type _) [Magma G] (h: Equation1943 G) : Equation16 G := fun x y =>
  let v0 := M y x
  let v1 := M y v0
  have h2 := h v1 v0 v0
  have h3 := S h2
  have h4 := h y y x
  have h5 := S (h y y v1)
  let v6 := M y v1
  have h7 := S (h v6 x y)
  have h8 := S h4
  have h9 := C (R v6) h8
  have h10 := h v1 y v0
  let v11 := M x y
  let v12 := M x v11
  have h13 := R v12
  have h14 := R (M y v6)
  have h15 := C h14 (T (C h13 (T h10 h9)) h7)
  have h16 := h v12 y v1
  let v17 := M v0 (M v0 v0)
  have h18 := R v17
  have h19 := h y v0 v0
  have h20 := C h18 h8
  let v21 := M v0 y
  let v22 := M v0 v21
  have h23 := T (T h16 h15) h5
  T (T (T (T (h x v12 v11) (C (C h23 (S (h x x y))) h13)) (C (T (T (h v0 v12 v21) (C (T (T (T (T (C h13 (S (h v0 x y))) (C h23 (R v0))) h2) h20) (C h18 h19)) (T (T (T (h v22 y v1) (C h14 (T (T (T (T (C (R v22) (T h2 h20)) (S (h v17 v0 y))) (h v17 x y)) (C h13 (T (T (T (C h18 h4) h3) h10) h9))) h7))) h5) h19))) (S (h v17 v17 v1))) h13)) (C h18 (T (T (T h16 h15) h5) h4))) h3

@[equational_result]
theorem Equation2105_implies_Equation3011 (G: Type _) [Magma G] (h: Equation2105 G) : Equation3011 G := fun x y z =>
  let v0 := M z z
  let v1 := M y v0
  let v2 := M v1 y
  let v3 := M v2 x
  let v4 := M x x
  have h5 := R v4
  have h6 := R v0
  have h7 := R v3
  have h8 := h v0 z v3
  let v9 := M v3 v3
  have h10 := R v9
  have h11 := R z
  have h12 := h z z z
  have h13 := h z v0 z
  have h14 := h v0 v2 z
  have h15 := R v2
  have h16 := h v0 y z
  have h17 := h v2 v0 v3
  have h18 := S (h v2 y x)
  have h19 := R y
  have h20 := T (T h8 (C (T (T (C (T (C h12 h6) (S h13)) h11) h14) (C (C (S h16) h15) h6)) h10)) (S h17)
  have h21 := C h19 h20
  have h22 := T (h y v1 z) (C (R (M v2 v1)) h20)
  T (T (h x x x) (C (T (h (M v4 x) v3 z) (C (C (T (T (T (T (T (T (C h7 (C (T (T (h v4 y x) (C (C (T (T (C h22 h5) (S (h v1 v2 x))) h21) h19) h5)) h18) (R x))) (h v9 y x)) (C (C (T (T (C h22 h10) (S (h v1 v2 v3))) h21) h19) h5)) h18) h17) (C (T (T (C (C h16 h15) h6) (S h14)) (C (T h13 (C (S h12) h6)) h11)) h10)) (S h8)) h7) h6)) h5)) (S (h v3 v0 x))

@[equational_result]
theorem Equation3404_implies_Equation3823 (G: Type _) [Magma G] (h: Equation3404 G) : Equation3823 G := fun x y z =>
  let v0 := M y x
  have h1 := h y x v0
  have h2 := h v0 y z
  have h3 := h x z y
  have h4 := R z
  have h5 := R x
  have h6 := h z z x
  have h7 := R v0
  let v8 := M z z
  have h9 := R v8
  let v10 := M v8 v0
  have h11 := S (h z z v10)
  have h12 := R v10
  let v13 := M v0 y
  have h14 := T (h v8 v0 z) (C h4 (T (T (C h7 (C h4 (h z z v0))) (S (h (M z (M v0 z)) z v0))) (C (T (T (T (T (C h4 (h v0 z v8)) (S (h v10 v8 z))) (h v10 v8 v0)) (C h7 (T (C h9 (C (T (T (T h1 (h v0 (M x v13) v10)) (C h12 (C (T (T (T (h x v13 v8) (C h9 (C (T h2 (C h4 (S h3))) (R (M v8 x))))) (S (h x (M z (M x z)) v8))) (S h6)) (R (M v10 v0))))) (S (h v0 v8 v10))) h12)) (S (h v0 (M v0 v8) v8))))) (S (h v8 v0 v0))) h4)))
  T (T (T (T (h x y v10) (C h12 (T (T (C (R y) (T (h v10 x v10) (C h14 (T (C h5 (T (C h12 h14) h11)) (h x v8 y))))) (S (h v10 (M z (M v10 z)) y))) h11))) (h v10 v8 v8)) (C h9 (S (h v0 v8 v8)))) (C h9 (T (C h7 (T h6 (C h5 (T (C h4 h3) (S h2))))) (S h1)))

@[equational_result]
theorem Equation627_implies_Equation1224 (G: Type _) [Magma G] (h: Equation627 G) : Equation1224 G := fun x y =>
  let v0 := M x x
  let v1 := M v0 x
  have h2 := h x x v0
  have h3 := S h2
  let v4 := M x (M v1 x)
  have h5 := S (h v0 x v4)
  have h6 := h x v0 x
  have h7 := R v0
  have h8 := C h7 (C h7 (T h6 (C h6 (R v4))))
  have h9 := R v1
  have h10 := h x x x
  have h11 := S h10
  let v12 := M x v1
  have h13 := R v12
  have h14 := T (C h11 h13) h11
  have h15 := R x
  have h16 := h x x v12
  have h17 := h x v0 v1
  have h18 := T h17 (C h15 (C (T h16 (C h15 (C h15 h14))) (T (T (C (T h8 h5) h9) h8) h5)))
  have h19 := S (h y x x)
  let v20 := M y v1
  have h21 := S (h x y y)
  let v22 := M x (M (M y y) y)
  have h23 := C h15 (T (C h15 (C (T (C h15 (C h15 (T h10 (C h10 h13)))) (S h16)) (T (h v0 x v22) (C (T (h v0 x v12) (C h7 (C h7 h14))) (C h7 (T (C h21 (R v22)) h21)))))) (S h17))
  T (T (T (T (T h2 h23) (C (T h2 h23) h15)) (h v1 y v20)) (C h9 (C h9 (T (C h19 (R v20)) h19)))) (C (T (C (T (C h15 h18) h3) h18) h3) (R (M v1 y)))

@[equational_result]
theorem Equation2196_implies_Equation1181 (G: Type _) [Magma G] (h: Equation2196 G) : Equation1181 G := fun x y z =>
  let v0 := M z x
  let v1 := M z v0
  let v2 := M v1 y
  let v3 := M y v2
  let v4 := M v3 v2
  have h5 := S (h v4 v2 v3)
  have h6 := h v1 y v2
  let v7 := M (M v2 v3) v3
  have h8 := S (h v7 v3 v2)
  have h9 := C h6 (h y v2 v3)
  let v10 := M v2 v1
  let v11 := M v10 v1
  let v12 := M (M v1 v1) v1
  have h13 := R v12
  let v14 := M (M v0 v0) v0
  have h15 := h z x v3
  let v16 := M (M x v3) v3
  let v17 := M v0 x
  let v18 := M x z
  T (T (T (T (T (h x z v1) (C (R (M (M z v1) v1)) (T (T (T (T (h v18 z x) (C (R v17) (T (T (T (T (h (M v18 z) v0 x) (C (R (M v17 x)) (T (S (h z x z)) h15))) (S (h v16 v0 x))) (h v16 v0 v0)) (C (R v14) (S h15))))) (S (h v14 z x))) (h v14 v1 v1)) (C h13 (S (h z v0 v0)))))) (S (h v12 z v1))) (h v12 v2 v2)) (C (R (M (M v2 v2) v2)) (T (T (T (C h13 (T (T (T (T h9 h8) (h v7 v1 x)) (C (R (M (M v1 x) x)) (T (T (T (C (R v7) h6) h5) (h v4 v2 v1)) (C (R v11) (S h6))))) (S (h v11 v1 x)))) (S (h v10 v1 v1))) (C (T h9 h8) h6)) h5))) (S (h v3 v2 v2))

@[equational_result]
theorem Equation3804_implies_Equation3601 (G: Type _) [Magma G] (h: Equation3804 G) : Equation3601 G := fun x y z =>
  let v0 := M y x
  let v1 := M v0 z
  let v2 := M z y
  let v3 := M y v1
  let v4 := M x y
  let v5 := M x z
  have h6 := h x y x
  have h7 := S h6
  let v8 := M x x
  have h9 := h v4 v8 v0
  have h10 := h v4 v0 v8
  have h11 := h y x x
  have h12 := h x x y
  have h13 := h x x x
  have h14 := S h13
  have h15 := S h12
  have h16 := S h11
  have h17 := C (T (T h10 (C h16 h7)) h15) h15
  have h18 := h v0 v0 v4
  have h19 := h y x y
  have h20 := S h19
  have h21 := h v0 (M y y) v0
  T (T (T (T (T (T (T (T (T (T h6 h9) (C (T (T (C h11 h13) (S (h v8 v0 v8))) h16) (S (h y y x)))) h20) (h y x z)) (C (h z x y) (h y z x))) (S (h v5 v2 v0))) (h v5 v2 v1)) (C (R (M v1 v2)) (T (h v5 v1 y) (C (R v3) (T (T (T (h v5 y v0) (C (h v0 y x) (C (R v5) (T (T (T (T h19 h21) (C (T h21 (C h20 (T (T h18 h17) h14))) (T (T (T (T (T h18 h17) h14) h12) (C h11 h6)) (S h10)))) (S h9)) h7)))) (S (h v5 (M v0 x) v4))) (S (h v0 z x))))))) (S (h v3 v2 v1))) (S (h z v1 y))

@[equational_result]
theorem Equation887_implies_Equation1902 (G: Type _) [Magma G] (h: Equation887 G) : Equation1902 G := fun x y z =>
  let v0 := M z z
  have h1 := R v0
  let v2 := M x y
  have h3 := R v2
  let v4 := M y v2
  have h5 := h y v2 (M v4 v4)
  have h6 := h v4 v4 v4
  have h7 := h v2 v2 v2
  have h8 := R y
  have h9 := C h8 (S h7)
  have h10 := h x y (M v2 v2)
  let v11 := M y y
  let v12 := M v4 v0
  have h13 := h v2 v12 v11
  have h14 := R (M v11 v11)
  have h15 := h y v2 z
  have h16 := h y y y
  have h17 := R v12
  have h18 := T (C h17 (T h16 (C h15 h14))) (S h13)
  have h19 := R x
  have h20 := C h17 (T (C (S h15) h14) (S h16))
  have h21 := T h13 h20
  have h22 := C (T (T (T (C h21 h19) (C h18 (T h10 h9))) (C h3 h6)) (S h5)) h3
  have h23 := S h10
  have h24 := C h8 h7
  have h25 := C (T (T (T h5 (C h3 (S h6))) (C h21 (T h24 h23))) (C h18 h19)) h3
  T (T (T (T (h x y v12) (C h8 (C (T (T h13 h20) (C (T (C h25 h1) (C (T (T h22 h24) h23) h1)) h8)) (R (M v12 v12))))) (S (h (M x v0) y v12))) (C (T (T h10 h9) h25) h1)) (C h22 h1)

