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
theorem Equation1537_implies_Equation3294 (G: Type _) [Magma G] (h: Equation1537 G) : Equation3294 G := fun x y z =>
  let v0 := M z (M y z)
  have h1 := R v0
  let v2 := M x x
  have h3 := h v0 x v0
  have h4 := S h3
  let v5 := M v0 v0
  have h6 := h v5 x x
  have h7 := S h6
  have h8 := h x x x
  have h9 := S h8
  have h10 := R v5
  have h11 := h x v0 v2
  have h12 := R x
  have h13 := C h12 (T h11 (C h10 h9))
  have h14 := R v2
  have h15 := h x x v2
  have h16 := C h12 (T (C h14 h8) (S h15))
  have h17 := h v2 x x
  have h18 := C h14 (C h1 (T (T (T h17 (C h14 h16)) (C h14 h13)) h7))
  T (T (T (T h17 (C h14 (T h16 h13))) h7) (C (T h3 (C h14 (C h1 (T (T (T h6 (C h14 (C h12 (T (C h10 h8) (S h11))))) (C h14 (C h12 (T h15 (C h14 h9))))) (S h17))))) h1)) (C (T (T (T (T h18 h4) (h v0 v2 v2)) (C (R (M v2 v2)) (T h18 h4))) (S (h y v2 z))) h1)

@[equational_result]
theorem Equation2105_implies_Equation4098 (G: Type _) [Magma G] (h: Equation2105 G) : Equation4098 G := fun x y z =>
  have h0 := R z
  let v1 := M y y
  let v2 := M v1 z
  have h3 := R v1
  have h4 := S (h v1 x x)
  let v5 := M x x
  have h6 := R v5
  have h7 := R x
  have h8 := h x x x
  have h9 := S h8
  have h10 := C (C (T (h x v5 y) (C h9 h3)) h7) h6
  let v11 := M v2 v2
  have h12 := h x v5 z
  let v13 := M z z
  have h14 := R v13
  have h15 := h v13 x x
  T (T (T (T (h v5 x x) (C (C (T (C h8 h6) (S (h x v5 x))) h7) h6)) (C (C (T h12 (C h9 h14)) h7) h6)) (S h15)) (C (T (T (h z z v1) (C (T (T (C (T (T (T h15 (C (C (T (C h8 h14) (S h12)) h7) h6)) h10) h4) h0) (h v2 v2 y)) (C (C (T (T (T (h v11 x x) (C (C (T (C h8 (R v11)) (S (h x v5 v2))) h7) h6)) h10) h4) (R v2)) h3)) (R (M v1 v1)))) (S (h v2 v1 v1))) h0)

@[equational_result]
theorem Equation4197_implies_Equation3820 (G: Type _) [Magma G] (h: Equation4197 G) : Equation3820 G := fun x y z =>
  let v0 := M z z
  let v1 := M x y
  have h2 := S (h v0 v1 v0)
  have h3 := R v0
  have h4 := R v1
  have h5 := S (h z z z)
  have h6 := C h5 h3
  have h7 := h z z v0
  have h8 := C (T h7 h6) h4
  have h9 := C h8 h3
  have h10 := C (T (T h9 h2) h8) h3
  have h11 := R z
  have h12 := h z v1 z
  let v13 := M v0 v1
  have h14 := R v13
  T (T (T (T (T (h x y z) (C (T (T (T (T (T (C (T (h z x v1) (C (S (h y z x)) h4)) (R y)) (S (h z v1 y))) h12) (h v13 z v0)) (C (C (T (T (T (C (T h7 (C (T (T (T (T h5 h7) h6) (h v0 v0 v13)) (C (T h10 h2) h14)) h3)) h14) (S (h v13 v0 v13))) h9) h2) h11) h3)) (C (S h12) h3)) h11)) (S (h v1 v0 z))) (h v1 v0 v0)) h10) h2

@[equational_result]
theorem Equation492_implies_Equation759 (G: Type _) [Magma G] (h: Equation492 G) : Equation759 G := fun x y z =>
  let v0 := M y x
  let v1 := M v0 z
  have h2 := h v1 v0 v1
  have h3 := h v0 z v0
  have h4 := R v1
  have h5 := h z v1 v0
  have h6 := R v0
  have h7 := R z
  have h8 := C h7 (T (C h6 (C h4 (C h4 (T h5 (C h4 (S h3)))))) (S h2))
  have h9 := h v0 z v1
  let v10 := M z v1
  let v11 := M y v10
  have h12 := R v11
  have h13 := R y
  have h14 := R x
  T (h x y v0) (C h13 (T (T (T (C h14 (C h6 (C h6 (T (h y v0 x) (C h6 (T (C h13 (C h14 (C h14 (T (h v0 x y) (C h14 (T (C h6 (T (T (C h13 (T h9 h8)) (h v11 y v11)) (C h13 (C h12 (C h12 (T (C h12 (T (h y v10 y) (C (T (C h7 (T h2 (C h6 (C h4 (C h4 (T (C h4 h3) (S h5))))))) (S h9)) (R (M y (M y v11)))))) (S (h v0 v11 y)))))))) (S (h y v0 v11)))))))) (S (h x y x)))))))) (S (h v0 x v0))) h9) h8))

@[equational_result]
theorem Equation684_implies_Equation1374 (G: Type _) [Magma G] (h: Equation684 G) : Equation1374 G := fun x y z =>
  let v0 := M z y
  let v1 := M v0 z
  let v2 := M v1 x
  have h3 := R v2
  have h4 := S (h y y x)
  let v5 := M y (M (M y x) x)
  have h6 := R v0
  let v7 := M z (M (M z x) x)
  have h8 := h z z x
  have h9 := R z
  let v10 := M v1 (M v2 x)
  let v11 := M z v1
  have h12 := h v1 v1 x
  have h13 := R v1
  let v14 := M x (M (M x x) x)
  have h15 := h x x x
  T (T (h x v1 x) (C h13 (T (C (R x) (C h3 (T h15 (C h15 (R v14))))) (S (h v2 x v14))))) (C (T (T (h v1 z v1) (C h9 (T (T (T (T (T (C h13 (C (R v11) (T h12 (C h12 (R v10))))) (S (h v11 v1 v10))) (C h9 (C h6 (T h8 (C h8 (R v7)))))) (S (h v0 z v7))) (h v0 y v5)) (C (R y) (C h6 (T (C h4 (R v5)) h4)))))) (S (h y z y))) h3)

@[equational_result]
theorem Equation684_implies_Equation2186 (G: Type _) [Magma G] (h: Equation684 G) : Equation2186 G := fun x y z =>
  let v0 := M z x
  have h1 := R v0
  let v2 := M y z
  let v3 := M v2 y
  have h4 := S (h v3 v3 x)
  let v5 := M v3 (M (M v3 x) x)
  let v6 := M y v3
  have h7 := S (h y y x)
  let v8 := M y (M (M y x) x)
  have h9 := R v2
  have h10 := R y
  let v11 := M z (M v0 x)
  have h12 := h z z x
  have h13 := R z
  let v14 := M x (M (M x x) x)
  have h15 := h x x x
  T (T (h x z x) (C h13 (T (C (R x) (C h1 (T h15 (C h15 (R v14))))) (S (h v0 x v14))))) (C (T (T (h z y z) (C h10 (T (T (T (T (T (C h13 (C h9 (T h12 (C h12 (R v11))))) (S (h v2 z v11))) (h v2 y v8)) (C h10 (C h9 (T (C h7 (R v8)) h7)))) (h v6 v3 v5)) (C (R v3) (C (R v6) (T (C h4 (R v5)) h4)))))) (S (h v3 y v3))) h1)

@[equational_result]
theorem Equation1537_implies_Equation481 (G: Type _) [Magma G] (h: Equation1537 G) : Equation481 G := fun x y z =>
  let v0 := M z z
  let v1 := M y v0
  let v2 := M y (M x v1)
  have h3 := S (h v0 x z)
  have h4 := h z z z
  have h5 := R v0
  have h6 := R z
  have h7 := C h6 (T (h z z v0) (C h5 (S h4)))
  let v8 := M v2 v2
  have h9 := R (M x x)
  let v10 := M v1 v1
  have h11 := R v1
  let v12 := M y y
  have h13 := R y
  T (T (T (h x z y) (C h5 (C h13 (C (R x) (T (T (h y z y) (C h5 (T (h (M y v12) z v1) (C h5 (C h11 (T (T (T (C (C h13 (T (T (h v12 x z) (C h9 (T (C h6 (T (C (R v12) h4) (S (h z y v0)))) h7))) h3)) h11) (h v10 x z)) (C h9 (T (C h6 (T (C (R v10) h4) (S (h z v1 v0)))) h7))) h3)))))) (S (h v1 z v0))))))) (C h5 (T (h v2 z v2) (C h5 (C (R v2) (T (T (h v8 x z) (C h9 (T (C h6 (T (C (R v8) h4) (S (h z v2 v0)))) h7))) h3)))))) (S (h v2 z v0))

@[equational_result]
theorem Equation1537_implies_Equation3906 (G: Type _) [Magma G] (h: Equation1537 G) : Equation3906 G := fun x y z =>
  have h0 := R y
  let v1 := M x x
  let v2 := M z z
  let v3 := M y v2
  have h4 := h v1 x x
  have h5 := h x x x
  have h6 := S h5
  have h7 := R v1
  have h8 := h x x v1
  have h9 := R x
  let v10 := M v3 v3
  have h11 := R v3
  have h12 := h x y v1
  let v13 := M y y
  have h14 := R v13
  have h15 := h v13 x x
  T (T (T (T h4 (C h7 (C h9 (T (C h7 h5) (S h8))))) (C h7 (C h9 (T h12 (C h14 h6))))) (S h15)) (C (T (T (h y y y) (C h14 (T (h (M y v13) x v3) (C h7 (C h11 (T (T (T (T (C (C h0 (T (T (T h15 (C h7 (C h9 (T (C h14 h5) (S h12))))) (C h7 (C h9 (T (h x z v1) (C (R v2) h6))))) (S (h v2 x x)))) h11) (h v10 x x)) (C h7 (C h9 (T (C (R v10) h5) (S (h x v3 v1)))))) (C h7 (C h9 (T h8 (C h7 h6))))) (S h4))))))) (S (h v3 y v1))) h0)

@[equational_result]
theorem Equation2105_implies_Equation1710 (G: Type _) [Magma G] (h: Equation2105 G) : Equation1710 G := fun x y z =>
  let v0 := M z z
  let v1 := M v0 y
  let v2 := M y x
  let v3 := M v2 v1
  let v4 := M v1 v1
  have h5 := R v4
  have h6 := R v0
  have h7 := R v3
  have h8 := S (h v0 z x)
  have h9 := R (M x x)
  have h10 := R z
  have h11 := h z z z
  have h12 := C (S h11) h6
  have h13 := h z v0 z
  let v14 := M v3 v3
  have h15 := T (C (T (h v1 v1 z) (C (C (T (T (h v4 z x) (C (C (T (T (T (C h11 h5) (S (h z v0 v1))) h13) h12) h10) h9)) h8) (R v1)) h6)) h6) (S (h v1 v0 z))
  have h16 := R v2
  T (T (h x y v1) (C (T (h (M v2 y) v3 z) (C (C (T (T (T (C h7 (T (C h16 (T (h y v0 z) (C h15 h6))) (C h16 h15))) (h v14 z x)) (C (C (T (T (T (C h11 (R v14)) (S (h z v0 v3))) h13) h12) h10) h9)) h8) h7) h6)) h5)) (S (h v3 v0 v1))

@[equational_result]
theorem Equation2329_implies_Equation2 (G: Type _) [Magma G] (h: Equation2329 G) : Equation2 G := fun x y =>
  let v0 := M x (M x x)
  let v1 := M x v0
  let v2 := M x (M x (M v0 v0))
  let v3 := M y (M v2 v2)
  let v4 := M y y
  let v5 := M x (M x v4)
  have h6 := h y x v5
  have h7 := S h6
  have h8 := R x
  have h9 := R (M v5 v5)
  let v10 := M y (M y v4)
  have h11 := h y y v10
  have h12 := S h11
  have h13 := T (C h8 (C h8 (T (C h12 (T h12 h6)) (C h6 h9)))) (C h8 (C h8 (C h7 h7)))
  let v14 := M v10 v10
  have h15 := h x x v1
  have h16 := T (C h8 (C h8 (C h6 h6))) (C h8 (C h8 (T (C h7 h9) (C h11 (T h7 h11)))))
  T (T h15 (C (T (T (h v1 v5 v3) (C (T (C h16 (T (T (C h16 (S h15)) (S (h v14 x x))) h12)) (C h13 (T (T h11 (h v14 x y)) (C h13 h6)))) (R v3))) (S (h v5 v5 v3))) (R v1))) (S (h y x v1))

@[equational_result]
theorem Equation3008_implies_Equation2132 (G: Type _) [Magma G] (h: Equation3008 G) : Equation2132 G := fun x y z =>
  let v0 := M y y
  let v1 := M z z
  let v2 := M v0 x
  let v3 := M v2 v1
  have h4 := R v0
  have h5 := R v1
  let v6 := M v3 v3
  let v7 := M v1 v1
  have h8 := h v1 v7 y
  have h9 := S h8
  have h10 := R v7
  have h11 := h v0 v1 z
  have h12 := C h11 h10
  have h13 := h v1 v1 z
  have h14 := T h13 (C (T (T (T (C (C (T (h v1 v7 z) (C (S h13) h10)) (T h8 (C (S h11) h10))) h5) (S (h (M v0 v7) v1 v1))) h12) h9) h5)
  T (T (T (h x v0 z) (C (C (T (T (T (T (C h11 h14) h9) (h v1 v1 v3)) (C (T (h (M (M v1 v6) v1) v0 v1) (C (C (T h12 h9) (T (C (C h14 (R v6)) h5) (S (h v6 v1 z)))) h4)) h5)) (S (h v0 v1 v3))) (R x)) h4)) (C (T (h v2 v3 v0) (C (S (h (M v0 v0) v2 z)) (R v3))) h4)) (S (h v3 v0 y))

@[equational_result]
theorem Equation3193_implies_Equation218 (G: Type _) [Magma G] (h: Equation3193 G) : Equation218 G := fun x y =>
  let v0 := M x x
  let v1 := M y v0
  let v2 := M v1 x
  have h3 := h x x v2
  have h4 := R x
  have h5 := R v2
  have h6 := h x v1 v1
  have h7 := R v1
  have h8 := h v1 y v0
  have h9 := C (S h8) h7
  have h10 := h v1 v1 y
  have h11 := h x v2 x
  have h12 := R v0
  have h13 := S (h y y v0)
  have h14 := R y
  have h15 := S h10
  have h16 := C h8 h7
  have h17 := T (T (C (T h16 h15) h7) h16) h15
  have h18 := C (C h17 h14) h14
  have h19 := h y v1 v1
  T (T (T (T h3 (C (T (C (C (C (T h6 (C (C h17 h4) h4)) h5) h4) h4) (S h11)) h4)) (h v0 y y)) (C (C (T (C (T (T (T (C (T h19 h18) h14) h13) h19) h18) h14) h13) h12) h12)) (C h7 (T (C (T h11 (C (C (C (T (C (C (T (T h10 h9) (C (T h10 h9) h7)) h4) h4) (S h6)) h5) h4) h4)) h4) (S h3)))

@[equational_result]
theorem Equation1507_implies_Equation2271 (G: Type _) [Magma G] (h: Equation1507 G) : Equation2271 G := fun x y z =>
  let v0 := M y (M y z)
  let v1 := M x v0
  let v2 := M v1 z
  let v3 := M v2 v2
  let v4 := M v1 v2
  let v5 := M v1 v4
  have h6 := R v5
  let v7 := M v2 v3
  have h8 := h z v1 v2
  let v9 := M v2 (M v2 v1)
  have h10 := R (M y (M y v1))
  let v11 := M z v0
  let v12 := M v2 x
  T (T (h x v2 x) (C (T (T (h v12 v2 v1) (C (T (T (T (T (T (T (h (M v2 v12) v1 y) (C (S (h v0 x v2)) h10)) (C (T (h v0 v2 v1) (C (T (T (T (C (h v2 v1 v2) (T (h v0 z y) (C (R v11) (h v0 z v1)))) (S (h v9 v4 v11))) (h v9 (M v1 x) v1)) (C (S (h x v1 v2)) (S (h v0 x v1)))) h6)) h10)) (S (h v5 v1 y))) (h v5 z x)) (C (T (T (T (C h8 h6) (S (h v9 v2 v1))) (h v9 v2 v2)) (C (S h8) (R v7))) (R (M x (M x z))))) (S (h v7 z x))) h6)) (S (h v3 v2 v1))) (R (M x (M x v2))))) (S (h v2 v2 x))

@[equational_result]
theorem Equation1537_implies_Equation2132 (G: Type _) [Magma G] (h: Equation1537 G) : Equation2132 G := fun x y z =>
  let v0 := M z z
  let v1 := M y y
  let v2 := M v1 x
  let v3 := M v2 v0
  have h4 := h v0 x y
  have h5 := S h4
  have h6 := h y y y
  have h7 := S h6
  have h8 := R v0
  have h9 := C h8 h7
  have h10 := h y z v1
  let v11 := M v3 v3
  have h12 := R y
  let v13 := M x x
  have h14 := R v13
  let v15 := M v2 v2
  T (T (T (T (T (h x y v0) (C (R v1) (T (C h8 (C (R x) (T (T h4 (C h14 (C h12 (T (T (T (C h8 h6) (S h10)) (h y x v1)) (C h14 h7))))) (S (h v13 x y))))) (S (h x z x))))) (h v2 z v2)) (C h8 (C (R v2) (T (T (h v15 x y) (C h14 (C h12 (T (T (T (C (R v15) h6) (S (h y v2 v1))) h10) h9)))) h5)))) (C h8 (T (h v3 z v3) (C h8 (C (R v3) (T (T (h v11 x y) (C h14 (C h12 (T (T (T (C (R v11) h6) (S (h y v3 v1))) h10) h9)))) h5)))))) (S (h v3 z v0))

@[equational_result]
theorem Equation1699_implies_Equation1320 (G: Type _) [Magma G] (h: Equation1699 G) : Equation1320 G := fun x y z =>
  let v0 := M y x
  let v1 := M (M v0 z) z
  let v2 := M y v1
  let v3 := M v0 y
  have h4 := R v1
  have h5 := h y v0 z
  have h6 := h x y y
  have h7 := S h6
  let v8 := M (M y y) y
  let v9 := M v2 v1
  let v10 := M v9 v1
  have h11 := R (M v3 y)
  have h12 := h v0 y y
  T (T (T (T (h x v0 z) (C (T (T (T (T (T (C h12 (T h6 (C h12 (R v8)))) (S (h v8 (M y v0) v8))) (h v8 v0 y)) (C h7 h11)) (C (h x y v1) h11)) (S (h v9 v0 y))) h4)) (h v10 v1 z)) (C (T (T (T (T (T (C (h v1 y y) (R v10)) (S (h v8 v2 v1))) (h v8 v0 x)) (C (T h7 (h x y v2)) (R (M (M v0 x) x)))) (S (h (M (M y v2) v2) v0 x))) (C (T (C h5 (C h5 h4)) (S (h v1 v3 v1))) (R v2))) (R (M (M v1 z) z)))) (S (h v2 v1 z))

@[equational_result]
theorem Equation2196_implies_Equation1293 (G: Type _) [Magma G] (h: Equation2196 G) : Equation1293 G := fun x y z =>
  let v0 := M x y
  let v1 := M (M v0 z) z
  let v2 := M y v1
  let v3 := M v2 z
  let v4 := M v3 z
  let v5 := M v1 y
  let v6 := M y x
  let v7 := M v6 x
  have h8 := h x y y
  let v9 := M (M y y) y
  have h10 := R v1
  let v11 := M x z
  let v12 := M v11 z
  T (T (h x z v2) (C (R (M (M z v2) v2)) (T (T (h v11 z v0) (C (R (M (M z v0) v0)) (T (T (T (T (h v12 v0 z) (C h10 (T (C (R v12) (T (T (T (T (C (h x y v0) (h y v0 z)) (S (h v1 (M y v0) v0))) (h v1 x x)) (C (R (M (M x x) x)) (T (T (T (T (C h10 h8) (S (h v9 v0 z))) (h v9 v0 x)) (C (R (M (M v0 x) x)) (T (S h8) (h x y x)))) (S (h v7 v0 x))))) (S (h v6 x x)))) (S (h y x z))))) (h v5 y x)) (C (R v7) (T (h (M v5 y) v2 z) (C (R v4) (S (h y v1 y)))))) (S (h v4 y x))))) (S (h v3 z v0))))) (S (h v2 z v2))

@[equational_result]
theorem Equation2958_implies_Equation2271 (G: Type _) [Magma G] (h: Equation2958 G) : Equation2271 G := fun x y z =>
  let v0 := M y z
  let v1 := M y v0
  let v2 := M x v1
  let v3 := M v2 z
  have h4 := R z
  have h5 := R v3
  let v6 := M v3 z
  have h7 := S (h v3 v0 v3)
  let v8 := M (M v0 (M v0 v3)) v3
  let v9 := M (M x (M x v2)) v2
  have h10 := R v2
  have h11 := h v2 x v2
  have h12 := R v9
  have h13 := R x
  let v14 := M v2 x
  have h15 := S h11
  have h16 := S (h x x x)
  let v17 := M (M x (M x x)) x
  T (T (h x y z) (C (T (T (T (T (T (C (T (T (T (h v1 v17 x) (C (C (T (C (R v17) h16) h16) (R v1)) h13)) (h v14 v9 v2)) (C (C (T (C h12 h15) h15) (R v14)) h10)) h13) (S (h v2 v2 x))) (h v2 v2 z)) (C (T (C (C (T h11 (C h12 h11)) h5) h10) (S (h v3 v9 v2))) h4)) (h v6 v8 v3)) (C (C (T (C (R v8) h7) h7) (R v6)) h5)) h4)) (S (h v3 v3 z))

@[equational_result]
theorem Equation492_implies_Equation1983 (G: Type _) [Magma G] (h: Equation492 G) : Equation1983 G := fun x y z =>
  let v0 := M z y
  let v1 := M y v0
  let v2 := M z x
  let v3 := M v1 v2
  have h4 := R x
  have h5 := h v0 z v0
  have h6 := h z y z
  have h7 := R v0
  have h8 := h y v0 z
  have h9 := R z
  have h10 := R y
  have h11 := C h10 (T (C h9 (C h7 (C h7 (T h8 (C h7 (S h6)))))) (S h5))
  have h12 := h z y v0
  have h13 := R v1
  have h14 := C (T (C h10 (T h5 (C h9 (C h7 (C h7 (T (C h7 h6) (S h8))))))) (S h12)) (T (C h4 (C h4 (C h13 (C (T h12 h11) h4)))) (S (h x x v1)))
  have h15 := R v3
  have h16 := h v1 v3 x
  have h17 := R v2
  T (T (h x v2 z) (C h17 (T (T (T (T (S (h z x z)) h12) h11) h16) (C h15 (T (T h14 (h v2 v1 v3)) (C h13 (T (C h17 (C h15 (C h15 (T h16 (C h15 h14))))) (S (h v3 v2 v3))))))))) (S (h v3 v2 v1))

@[equational_result]
theorem Equation1537_implies_Equation887 (G: Type _) [Magma G] (h: Equation1537 G) : Equation887 G := fun x y z =>
  let v0 := M z z
  let v1 := M x y
  let v2 := M v1 v0
  let v3 := M y v2
  have h4 := S (h v0 x z)
  have h5 := h z z z
  have h6 := R v0
  have h7 := C h6 (S h5)
  have h8 := h z z v0
  let v9 := M v3 v3
  have h10 := R z
  have h11 := R (M x x)
  let v12 := M v2 v2
  have h13 := R v2
  let v14 := M v1 v1
  T (T (h x y y) (C (R (M y y)) (T (T (C (R y) (T (T (h v1 v0 v1) (C (R (M v0 v0)) (T (h (M v1 v14) z v2) (C h6 (C h13 (T (T (T (C (C (R v1) (T (T (h v14 x z) (C h11 (C h10 (T (T (T (C (R v14) h5) (S (h z v1 v0))) h8) h7)))) h4)) h13) (h v12 x z)) (C h11 (C h10 (T (T (T (C (R v12) h5) (S (h z v2 v0))) h8) h7)))) h4)))))) (S (h v2 v0 v0)))) (h v3 z v3)) (C h6 (C (R v3) (T (T (h v9 x z) (C h11 (C h10 (T (T (T (C (R v9) h5) (S (h z v3 v0))) h8) h7)))) h4)))))) (S (h v3 y v0))

@[equational_result]
theorem Equation3193_implies_Equation1035 (G: Type _) [Magma G] (h: Equation3193 G) : Equation1035 G := fun x y =>
  let v0 := M x x
  let v1 := M y v0
  let v2 := M v1 x
  have h3 := h x x v2
  have h4 := R x
  have h5 := R v2
  have h6 := h x v1 v1
  have h7 := R v1
  have h8 := h v1 y v0
  have h9 := C (S h8) h7
  have h10 := h v1 v1 y
  have h11 := h x v2 x
  have h12 := S (h y y v0)
  have h13 := R y
  have h14 := S h10
  have h15 := C h8 h7
  have h16 := T (T (C (T h15 h14) h7) h15) h14
  have h17 := C (C h16 h13) h13
  have h18 := h y v1 v1
  have h19 := T (C (C (C (T h6 (C (C h16 h4) h4)) h5) h4) h4) (S h11)
  T (T h3 (C h19 (T h3 (C h19 h4)))) (C h4 (T (h v0 y y) (C (C (T (C (T (T (T (C (T h18 h17) h13) h12) h18) h17) h13) h12) (R v0)) (T (C (T h11 (C (C (C (T (C (C (T (T h10 h9) (C (T h10 h9) h7)) h4) h4) (S h6)) h5) h4) h4)) h4) (S h3)))))

@[equational_result]
theorem Equation3385_implies_Equation3591 (G: Type _) [Magma G] (h: Equation3385 G) : Equation3591 G := fun x y z =>
  let v0 := M x z
  let v1 := M v0 y
  let v2 := M z v1
  have h3 := R v2
  have h4 := h y x z
  have h5 := R v0
  have h6 := C h5 (S h4)
  have h7 := h z y v0
  have h8 := R x
  let v9 := M z y
  have h10 := h x v9 v2
  have h11 := C (T (T (T h10 (C h3 (C h8 (C (T h7 h6) h3)))) (S (h x (M v0 (M y x)) v2))) (S (h v0 y x))) h3
  have h12 := R z
  let v13 := M y z
  T (T (T (h x y z) (h z (M x v13) v2)) (C h3 (C h12 (T (C (T (T (T (h x v13 v2) (C h3 (C h8 (C (T (T (T (T (h y z v1) (C (R v1) (T (S (h z v0 y)) (C h12 (T (T (T (h x z y) (h y (M x v9) v2)) (C h3 (C (R y) h11))) (S (h y v1 v2))))))) (S (h z y v1))) h7) h6) h3)))) (C h3 (C h8 (C (T (C h5 h4) (S h7)) h3)))) (S h10)) h3) h11)))) (S (h z v1 v2))

@[equational_result]
theorem Equation1114_implies_Equation2 (G: Type _) [Magma G] (h: Equation1114 G) : Equation2 G := fun x y =>
  have h0 := R y
  let v1 := M (M y (M y y)) x
  let v2 := M x (M y x)
  have h3 := h v2 x v1
  have h4 := S h3
  have h5 := R v1
  have h6 := h y x x
  have h7 := h y y x
  have h8 := R x
  have h9 := C h8 (T h7 (C h6 h5))
  let v10 := M x y
  let v11 := M (M y v10) y
  have h12 := h v10 x v11
  have h13 := R v11
  have h14 := S h6
  have h15 := h x y y
  let v16 := M v2 x
  T (T (h x x y) (C h8 (T (C (T (T (T (h (M x (M x x)) x v16) (C h8 (T (C (S (h x x x)) (R v16)) h14))) h12) (C h8 (T (C (T (C h8 (C (T h9 h4) h8)) h14) h13) (S h15)))) h0) (C (T (T (T (C h8 (T h15 (C (T h6 (C h8 (C (T h3 (C h8 (T (C h14 h5) (S h7)))) h8))) h13))) (S h12)) h9) h4) h0)))) (S (h y x y))

@[equational_result]
theorem Equation2196_implies_Equation1504 (G: Type _) [Magma G] (h: Equation2196 G) : Equation1504 G := fun x y z =>
  let v0 := M y z
  let v1 := M z v0
  let v2 := M v0 v1
  have h3 := h y z v0
  let v4 := M y x
  let v5 := M v4 y
  let v6 := M v5 y
  let v7 := M v4 v1
  have h8 := h y v7 v1
  have h9 := R v7
  have h10 := h v4 v1 v0
  let v11 := M (M v7 v1) v1
  have h12 := R v11
  let v13 := M v4 x
  let v14 := M x y
  T (T (T (h x y v0) (C (R (M (M y v0) v0)) (T (T (h v14 y x) (C (R v13) (T (T (T (T (h (M v14 y) v4 x) (C (R (M v13 x)) (T (T (S (h y x y)) h8) (C h12 (T (C h3 h9) (S h10)))))) (S (h v11 v4 x))) (h v11 v4 y)) (C (R v6) (T (C h12 (T h10 (C (S h3) h9))) (S h8)))))) (S (h v6 y x))))) (S (h v5 y v0))) (C (R v4) (T (h y v2 v1) (C (S (h z v0 v1)) (T (C h3 (R v2)) (S (h v0 v1 v0))))))

@[equational_result]
theorem Equation2196_implies_Equation2271 (G: Type _) [Magma G] (h: Equation2196 G) : Equation2271 G := fun x y z =>
  let v0 := M y z
  let v1 := M y v0
  let v2 := M x v1
  let v3 := M v2 z
  let v4 := M v3 v2
  let v5 := M v4 v2
  let v6 := M z v2
  let v7 := M v6 v2
  let v8 := M z y
  have h9 := h y z v2
  let v10 := M (M v0 v0) v0
  let v11 := M (M v1 v2) v2
  T (T (T (h x v1 v2) (C (T (T (T (T (T (h v11 y v2) (C (R (M (M y v2) v2)) (T (T (T (T (C (R v11) (h y v0 v0)) (S (h v10 v1 v2))) (h v10 y x)) (C (R (M (M y x) x)) (T (T (T (T (C (R v10) h9) (S (h v7 v0 v0))) (h v7 v0 x)) (C (R (M (M v0 x) x)) (T (S h9) (h y z y)))) (S (h (M v8 y) v0 x))))) (S (h v8 y x))))) (S (h z y v2))) (h z v2 y)) (C (R (M (M v2 y) y)) (T (T (h v6 v2 x) (C (R (M (M v2 x) x)) (T (h v7 v3 v2) (C (R v5) (S (h v2 z v2)))))) (S (h v5 v2 x))))) (S (h v4 v2 y))) (R v2))) (h v5 (M z v3) v3)) (C (S (h v2 z v3)) (S (h z v3 v2)))

@[equational_result]
theorem Equation2196_implies_Equation2992 (G: Type _) [Magma G] (h: Equation2196 G) : Equation2992 G := fun x y z =>
  let v0 := M z y
  let v1 := M y v0
  let v2 := M v1 x
  have h3 := h x v2 z
  have h4 := S (h v1 x v2)
  let v5 := M x v2
  let v6 := M v2 z
  let v7 := M v6 z
  have h8 := T (h v7 v5 v2) (C h4 (S h3))
  have h9 := h v1 x v6
  have h10 := C (R v7) (S h9)
  let v11 := M (M x v6) v6
  have h12 := h v11 v2 z
  let v13 := M v2 v1
  let v14 := M v13 v1
  let v15 := M v2 x
  have h16 := R (M v15 x)
  T h3 (C h8 (T (T (h v5 v2 x) (C h16 (T (T (T (T (T (T (T (T (T (h (M v5 v2) v2 x) (C h16 h4)) (C h16 h9)) (S (h v11 v2 x))) h12) h10) (C h8 (R v1))) (h v13 v1 v0)) (C (S (h z y v0)) (T (T (h v14 v1 x) (C (R v15) (T (T (T (C (R v14) h9) (S (h v11 v2 v1))) h12) h10))) (S (h v7 v1 x))))) (C (R z) h8)))) (S (h z v2 x))))

@[equational_result]
theorem Equation2722_implies_Equation16 (G: Type _) [Magma G] (h: Equation2722 G) : Equation16 G := fun x y =>
  let v0 := M y x
  let v1 := M y v0
  have h2 := R y
  have h3 := h x y v1
  let v4 := M v1 y
  have h5 := h v4 v0 y
  have h6 := T h5 (C (S h3) h2)
  let v7 := M y v1
  have h8 := R v7
  have h9 := C h8 h6
  let v10 := M v7 v4
  have h11 := R v1
  have h12 := R (M v1 v0)
  have h13 := T (C h3 h2) (S h5)
  have h14 := R v0
  let v15 := M v0 (M x y)
  have h16 := C h14 h6
  T (T (h x y x) (C (T (T (T (h v15 v0 v1) (C (T (C (T (T (T (T (T (C h14 (C h14 h13)) (C (T (h v0 y x) (C (C h11 h13) (T h3 (C h16 h11)))) h16)) (S (h v4 v1 v15))) (h v4 v1 v10)) (C (T (C (R (M v1 v4)) (S (h v1 y v1))) (S (h v0 y v1))) (R v10))) (C h14 h9)) h12) (C (C h14 (C h8 h13)) h12)) h11)) (S (h v10 v0 v1))) h9) (R x))) (S (h v1 y x))

@[equational_result]
theorem Equation2958_implies_Equation4305 (G: Type _) [Magma G] (h: Equation2958 G) : Equation4305 G := fun x y z =>
  let v0 := M y z
  let v1 := M z v0
  have h2 := R z
  let v3 := M v1 z
  have h4 := S (h v1 x v1)
  let v5 := M (M x (M x v1)) v1
  have h6 := R v0
  have h7 := S (h z x z)
  let v8 := M (M x (M x z)) z
  let v9 := M x (M x y)
  let v10 := M v9 y
  have h11 := R y
  have h12 := h y x y
  have h13 := R v10
  let v14 := M (M x (M x v9)) v9
  have h15 := h v9 x v9
  T (T (T (T (T (T (h v9 v9 y) (C (T (C (C (T h15 (C (R v14) h15)) h13) (R v9)) (S (h v10 v14 v9))) h11)) (S h12)) (h y y z)) (C (T (C (C (T h12 (C h13 h12)) h6) h11) (S (h v0 v10 y))) h2)) (C (T (T (T (h v0 v8 z) (C (C (T (C (R v8) h7) h7) h6) h2)) (h v3 v5 v1)) (C (C (T (C (R v5) h4) h4) (R v3)) (R v1))) h2)) (S (h v1 v1 z))

@[equational_result]
theorem Equation1111_implies_Equation2 (G: Type _) [Magma G] (h: Equation1111 G) : Equation2 G := fun x y =>
  let v0 := M y y
  let v1 := M y v0
  have h2 := h y y v1
  have h3 := R x
  let v4 := M x v0
  have h5 := h y x v4
  have h6 := S h5
  let v7 := M v4 x
  let v8 := M (M x (M v7 v7)) x
  let v9 := M x x
  let v10 := M y v9
  have h11 := h x y v10
  let v12 := M x v9
  have h13 := h x x v12
  have h14 := S h13
  let v15 := M v12 x
  let v16 := M (M x (M v15 v15)) x
  T (T (T (h x x v8) (C h3 (T (T (T (C (T (T (T (h v12 x v16) (C h3 (T (T (T (C h14 (R v16)) (S (h v15 x x))) (C (C h3 (C h13 h13)) h3)) (C (T (T (C h3 (C h14 h14)) (h v12 x x)) (C h3 (C (T h14 h11) h11))) h3)))) (S (h (M y (M v10 v10)) x x))) (S h11)) (R v8)) (S (h v7 x x))) (C (C h3 (C h5 h5)) h3)) (C (T (T (C h3 (C h6 h6)) (h v4 x y)) (C h3 (C (T h6 h2) h2))) h3)))) (S (h (M y (M v1 v1)) x x))) (S h2)

@[equational_result]
theorem Equation1993_implies_Equation1746 (G: Type _) [Magma G] (h: Equation1993 G) : Equation1746 G := fun x y z =>
  let v0 := M z z
  let v1 := M v0 x
  let v2 := M y y
  let v3 := M v2 v1
  let v4 := M v1 v1
  let v5 := M v2 v4
  let v6 := M y v4
  have h7 := h y y v1
  let v8 := M x x
  have h9 := R (M v3 (M v3 v3))
  let v10 := M v1 v4
  have h11 := h v0 x v2
  let v12 := M x (M v2 v2)
  have h13 := R (M v1 v8)
  T (T (T (T (T (T (h x v0 y) (C (R (M v0 v2)) (T (T (T (T (T (h (M x v0) v1 x) (C h13 (S (h v0 x z)))) (C h13 h11)) (S (h v12 v1 x))) (h v12 v1 v1)) (C (R v10) (S h11))))) (S (h v10 v0 y))) (h v10 v3 v3)) (C h9 (S (h v2 v1 v1)))) (C h9 (T (T (T (C h7 (T (h y v2 v1) (C (R v5) (T (T (h (M y v2) v2 x) (C (R (M v2 v8)) (T (S (h y y y)) h7))) (S (h v6 v2 x)))))) (S (h v5 v6 y))) (h v5 (M v3 v2) v3)) (C (S (h v3 v3 y)) (S (h v3 v2 v1)))))) (S (h v3 v3 v3))

@[equational_result]
theorem Equation2958_implies_Equation2180 (G: Type _) [Magma G] (h: Equation2958 G) : Equation2180 G := fun x y z =>
  let v0 := M y z
  let v1 := M v0 y
  let v2 := M (M v0 (M v0 v1)) v1
  let v3 := M x z
  let v4 := M v1 v3
  have h5 := S (h y x y)
  let v6 := M (M x (M x y)) y
  have h7 := R v4
  have h8 := h v1 v0 v1
  have h9 := R v3
  have h10 := S (h v1 x v1)
  let v11 := M (M x (M x v1)) v1
  have h12 := S (h v4 x v4)
  let v13 := M (M x (M x v4)) v4
  let v14 := M (M x (M x x)) x
  have h15 := h x x x
  T (T (h x x z) (C (T (T (T (T (C (C (T h15 (C (R v14) h15)) h9) (R x)) (S (h v3 v14 x))) (h v3 v13 v4)) (C (T (T (C (T (C (R v13) h12) h12) h9) (C (T (h v4 v11 v1) (C (C (T (C (R v11) h10) h10) h7) (R v1))) h9)) (S (h v1 v1 v3))) h7)) (C (T h8 (C (R v2) h8)) h7)) (T (h z v6 y) (C (C (T (C (R v6) h5) h5) (R z)) (R y))))) (S (h v4 v2 v1))

@[equational_result]
theorem Equation3804_implies_Equation4497 (G: Type _) [Magma G] (h: Equation3804 G) : Equation4497 G := fun x y z =>
  let v0 := M z z
  let v1 := M v0 x
  have h2 := R v1
  have h3 := S (h z z y)
  have h4 := C (S (h y z z)) (S (h z y z))
  let v5 := M y z
  let v6 := M z y
  have h7 := h v6 v5 v0
  have h8 := R (M v6 v5)
  have h9 := h y y z
  let v10 := M y y
  let v11 := M x v10
  let v12 := M y v10
  have h13 := h x v10 v10
  have h14 := R v11
  have h15 := h y y y
  T (T (T (T (T (T (T h13 (C (S h15) h14)) (C (T (T (T (T h9 h8) h7) h4) h3) h14)) (h v0 v11 x)) (C (T (T (T (T (T (T (T (T (h x v11 y) (C (T (h y v11 v10) (C (T (C h15 h14) (S h13)) (R v12))) (h x y v10))) (S (h (M v10 y) v12 v11))) (S (h y y v10))) h9) h8) h7) h4) h3) h2)) (h v0 v1 v1)) (C (T (C h2 (T (h v0 x v0) (C h2 (S (h z z z))))) (S (h v1 x v0))) (R (M v0 v1)))) (S (h v0 x v1))

@[equational_result]
theorem Equation4197_implies_Equation3331 (G: Type _) [Magma G] (h: Equation4197 G) : Equation3331 G := fun x y z =>
  let v0 := M y z
  let v1 := M z v0
  let v2 := M x v1
  have h3 := R v2
  have h4 := R v0
  have h5 := h v0 x z
  have h6 := R z
  have h7 := R x
  let v8 := M x y
  let v9 := M z y
  T (T (T (T (T (h x y v0) (C (T (C (T h5 (C (T (T (h v1 x x) (C (T (T (h v2 x v0) (C (C (T (T (T (C (T (T (T (T (h y z z) (h (M v9 z) z v2)) (C (C (C h3 (T (T (T (h v9 z v2) (C (C (C h3 (T (h z y v0) (C (S (h z z y)) h4))) h6) h3)) (S (h (M (M z z) v0) z v2))) (S (h z v0 z)))) h6) h3)) (S (h v1 z v2))) (h v1 z x)) h3) (S (h z x v2))) (h z x v8)) (C (S (h y z x)) (R v8))) h7) h4)) (S (h v8 x v0))) h7)) (S (h y x x))) h6)) (R y)) (S (h x z y))) h4)) (h (M x z) v0 v2)) (C (C (C h3 (T (h x z v1) (C (S h5) (R v1)))) h4) h3)) (S (h (M (M v0 x) v1) v0 v2))) (S (h x v1 v0))

@[equational_result]
theorem Equation4197_implies_Equation3940 (G: Type _) [Magma G] (h: Equation4197 G) : Equation3940 G := fun x y z =>
  let v0 := M z y
  let v1 := M x v0
  let v2 := M v1 z
  have h3 := R v2
  have h4 := R z
  have h5 := R y
  have h6 := R v0
  have h7 := h y x z
  have h8 := C (S h7) h6
  have h9 := h x z v0
  let v10 := M x z
  have h11 := h v10 y v2
  have h12 := C h3 (T (T (T h11 (C (C (C h3 (T h9 h8)) h5) h3)) (S (h (M (M y x) v0) y v2))) (S (h x v0 y)))
  let v13 := M z x
  T (T (T (h x y z) (h (M v13 y) z v2)) (C (C (T (C h3 (T (T (T (h v13 y v2) (C (C (C h3 (T (T (T (T (h z x v1) (C (T (S (h v0 z x)) (C (T (T (T (h z y x) (h (M v10 y) x v2)) (C (C h12 (R x)) h3)) (S (h v1 x v2))) h4)) (R v1))) (S (h x z v1))) h9) h8)) h5) h3)) (C (C (C h3 (T (C h7 h6) (S h9))) h5) h3)) (S h11))) h12) h4) h3)) (S (h v1 z v2))

@[equational_result]
theorem Equation1507_implies_Equation2482 (G: Type _) [Magma G] (h: Equation1507 G) : Equation2482 G := fun x y z =>
  let v0 := M y z
  let v1 := M v0 y
  let v2 := M x v1
  let v3 := M v2 z
  have h4 := S (h z v2 v3)
  let v5 := M v3 v2
  let v6 := M z (M z v3)
  let v7 := M v3 v5
  have h8 := h v1 x v3
  let v9 := M v3 (M v3 x)
  let v10 := M v1 x
  let v11 := M v1 v0
  T (T (T (T (h x z v3) (C (T (T (T (T (T (C (T (h z v11 v1) (C (T (C (R v11) (h z y v0)) (S (h v0 v1 v0))) (S (h y v0 v1)))) (R x)) (h v10 v1 y)) (C (T (T (T (T (h (M v1 v10) v2 x) (C (T (S (h v1 x v1)) h8) (R (M x (M x v2))))) (S (h v9 v2 x))) (h v9 v2 v3)) (C (S h8) (R v7))) (R (M y (M y v1))))) (S (h v7 v1 y))) (h v7 v3 z)) (C h4 (R v6))) (R (M v3 (M v3 z))))) (S (h v6 z v3))) (h v6 v5 v3)) (C (S (h v2 v3 z)) h4)

@[equational_result]
theorem Equation1993_implies_Equation3692 (G: Type _) [Magma G] (h: Equation1993 G) : Equation3692 G := fun x y z =>
  let v0 := M z z
  let v1 := M y y
  let v2 := M v1 v0
  have h3 := h y y v0
  have h4 := S h3
  let v5 := M y (M v0 v0)
  let v6 := M x x
  let v7 := M v6 v6
  let v8 := M v1 v7
  have h9 := R v7
  let v10 := M v1 v1
  have h11 := h x x x
  let v12 := M x v6
  let v13 := M v6 v0
  T (T (T (T (T (h v6 v0 v1) (C (T (h (M v0 v10) v2 v1) (C (S (h v1 v1 z)) (S (h v1 v0 v1)))) (T (T (h v13 x x) (C (R v12) (T (T (T (C (R v13) h11) (S (h v12 v6 z))) (h v12 v6 x)) (C h9 (S h11))))) (S (h v7 x x))))) (C (T (h v10 v5 y) (C h4 (T (C (R v10) (T (T (h v5 v1 x) (C (R (M v1 v6)) (T h4 (h y y y)))) (S (h (M y v1) v1 x)))) (S (h y v1 y))))) h9)) (h v8 y x)) (C (R (M y v6)) (T (T (T (C (R v8) h3) (S (h v5 v1 v6))) (h v5 v1 z)) (C (R v2) h4)))) (S (h v2 y x))

@[equational_result]
theorem Equation2196_implies_Equation1358 (G: Type _) [Magma G] (h: Equation2196 G) : Equation1358 G := fun x y z =>
  let v0 := M z x
  let v1 := M v0 z
  let v2 := M v1 y
  let v3 := M y v2
  let v4 := M v3 z
  let v5 := M v4 z
  have h6 := h y v2 v3
  let v7 := M (M v2 v3) v3
  let v8 := M v0 x
  have h9 := R v8
  let v10 := M (M v0 v0) v0
  have h11 := h z x v3
  let v12 := M (M x v3) v3
  let v13 := M x z
  T (T (h x z v1) (C (R (M (M z v1) v1)) (T (T (T (T (T (T (T (h v13 z x) (C h9 (T (T (T (T (h (M v13 z) v0 x) (C (R (M v8 x)) (T (S (h z x z)) h11))) (S (h v12 v0 x))) (h v12 v0 v0)) (C (R v10) (S h11))))) (S (h v10 z x))) (h v10 (M x v0) v0)) (C (S (h z x v0)) (S (h x v0 v0)))) (h v0 z x)) (C h9 (T (T (h v1 y x) (C (R (M (M y x) x)) (T (T (T (C (h v1 y v2) h6) (S (h v7 v3 v2))) (h v7 v3 z)) (C (R v5) (S h6))))) (S (h v5 y x))))) (S (h v4 z x))))) (S (h v3 z v1))

@[equational_result]
theorem Equation522_implies_Equation4413 (G: Type _) [Magma G] (h: Equation522 G) : Equation4413 G := fun x y z =>
  let v0 := M y z
  let v1 := M v0 z
  have h2 := h v1 v1 v0
  have h3 := h v0 v1 z
  have h4 := R v1
  have h5 := h z v1 v1
  have h6 := R v0
  have h7 := C h6 (T h5 (C h4 (S h3)))
  have h8 := R z
  let v9 := M x y
  have h10 := R v9
  let v11 := M x v9
  have h12 := h v9 v11 v11
  have h13 := h x v11 v9
  have h14 := R v11
  have h15 := R x
  T (T (T (h v11 v1 z) (C h4 (C h4 (T (C h8 (T (T (C (T (T (T (h v11 v9 v11) (C h10 (T (C h10 (T (T (T (C h14 (C h14 (C h15 (T h12 (C h14 (S h13)))))) (S (h v11 v11 x))) (h v11 v9 x)) (C h10 (C h10 (C h15 (T (C h14 h13) (S h12))))))) (S (h x v9 v9))))) (C h10 (h x v9 y))) (S (h y v9 v9))) h8) (h v0 z z)) (C h8 (T (T (T (C h8 (C h8 h7)) (S (h v1 z v0))) h2) (C h4 (C h4 (C h6 (T (C h4 h3) (S h5))))))))) (S (h v1 z v1)))))) (C h4 (C h4 h7))) (S h2)

@[equational_result]
theorem Equation1507_implies_Equation2349 (G: Type _) [Magma G] (h: Equation1507 G) : Equation2349 G := fun x y z =>
  let v0 := M z x
  let v1 := M y (M y v0)
  let v2 := M v1 z
  let v3 := M v2 v2
  let v4 := M v2 v3
  have h5 := R v4
  let v6 := M x z
  let v7 := M x v6
  let v8 := M v0 v1
  have h9 := h v1 v0 y
  let v10 := M v2 x
  let v11 := M v2 v10
  let v12 := M x v0
  let v13 := M x v12
  T (T (h x v2 v2) (C (T (T (h v10 v2 v0) (C (T (T (h v11 z x) (C (T (T (T (T (T (C (T (T (h z x v1) (C (T (T (h v6 x x) (C (T (h v7 v0 x) (C (S (h x z x)) (R v13))) (R (M x (M x x))))) (S (h v13 x x))) (R (M v1 (M v1 x))))) (S (h v12 x v1))) (R v11)) (S (h v0 x v2))) (C (h z v0 y) (h x z v0))) (S (h v1 (M v0 z) v0))) (h v1 v2 v2)) (C (T (C (R v2) (T h9 (C (R v8) h9))) (S (h z v1 v8))) h5)) (R v7))) (S (h v4 z x))) (R (M v0 (M v0 v2))))) (S (h v3 v2 v0))) h5)) (S (h v2 v2 v2))

@[equational_result]
theorem Equation1507_implies_Equation4640 (G: Type _) [Magma G] (h: Equation1507 G) : Equation4640 G := fun x y z =>
  let v0 := M x y
  let v1 := M v0 x
  let v2 := M v1 y
  have h3 := S (h y x v0)
  have h4 := R v2
  have h5 := h y v1 v0
  let v6 := M y z
  have h7 := R v6
  have h8 := R (M x (M x v6))
  let v9 := M v1 v2
  let v10 := M v6 z
  have h11 := h x v0 v6
  let v12 := M v6 (M v6 v0)
  let v13 := M y v1
  let v14 := M y v13
  T (T (T (T (T (T (T (h v1 y v10) (C (T (h v13 y v1) (C (T (T (h v14 x x) (C (T (T (T (C h11 (R v14)) (S (h v12 v1 y))) (h v12 v1 v0)) (C (S h11) h3)) (R (M x (M x x))))) (S (h y x x))) (R v9))) (R (M v10 (M v10 y))))) (S (h v9 y v10))) (h v9 v6 x)) (C (S (h z y v1)) h8)) (C (h z y v6) h8)) (S (h (M v6 (M v6 y)) v6 x))) (C h7 (T (C h7 (T h5 (C h4 (T (T h3 h5) (C h4 h3))))) (S (h z y v2))))

@[equational_result]
theorem Equation1864_implies_Equation27 (G: Type _) [Magma G] (h: Equation1864 G) : Equation27 G := fun x y z =>
  let v0 := M x y
  let v1 := M v0 z
  have h2 := R v1
  let v3 := M z z
  have h4 := h v0 v1 v1
  have h5 := S h4
  let v6 := M v1 v1
  have h7 := R v6
  let v8 := M x v1
  have h9 := h (M v0 v6) v1 v8
  have h10 := h x z z
  have h11 := h (M x v3) z v0
  have h12 := h x z v0
  have h13 := T h12 (C (T h11 (C (S h10) h2)) h2)
  have h14 := T (C (T (C h10 h2) (S h11)) h2) (S h12)
  have h15 := h x v1 v1
  have h16 := S h15
  have h17 := h (M x v6) v1 v8
  T (T (T (T (T h15 (C (T (T (T h17 (C h16 h14)) (h (M x x) v1 (M y v1))) (C (T (C (T (C h15 h13) (S h17)) h7) h16) (T (C (T (C (h y z z) h2) (S (h (M y v3) z v0))) h2) (S (h y z v0))))) h7)) h9) (C h5 h14)) (h (M v0 x) v1 (M z v1))) (C (T (C (T (C h4 h13) (S h9)) h7) h5) (T (C (T (C (h z z z) h2) (S (h (M z v3) z v0))) h2) (S (h z z v0))))

@[equational_result]
theorem Equation3211_implies_Equation2482 (G: Type _) [Magma G] (h: Equation3211 G) : Equation2482 G := fun x y z =>
  let v0 := M y z
  have h1 := h z y v0
  have h2 := S h1
  have h3 := R y
  have h4 := R z
  have h5 := R v0
  have h6 := h y v0 z
  have h7 := h z y z
  have h8 := h v0 z v0
  have h9 := C (T h8 (C (C (C (T (C h7 h5) (S h6)) h5) h5) h4)) h3
  have h10 := T h9 h2
  let v11 := M v0 y
  let v12 := M x v11
  have h13 := R x
  have h14 := R v12
  let v15 := M v12 z
  have h16 := R v15
  T (h x v11 v12) (C (T (C (C (C (T (h v11 v12 x) (C (T (C (C (C (T (h v12 x v11) (C (T (T (T (C (T (T (C h14 h10) (h v15 v11 v15)) (C (C (C (T (C (T (T h9 h2) (h z v12 z)) h16) (S (h v12 v15 z))) h16) h16) h10)) h14) (S (h z v12 v15))) h1) (C (T (C (C (C (T h6 (C (S h7) h5)) h5) h5) h4) (S h8)) h3)) h13)) h13) h13) (R v11)) (S (h x v11 x))) h14)) h14) h14) h13) (S (h v12 x v12))) h10)

@[equational_result]
theorem Equation684_implies_Equation1470 (G: Type _) [Magma G] (h: Equation684 G) : Equation1470 G := fun x y z =>
  let v0 := M y (M (M y x) x)
  let v1 := M z y
  have h2 := R v0
  have h3 := h y y x
  have h4 := R y
  let v5 := M x y
  have h6 := S h3
  have h7 := T (C h6 h2) h6
  let v8 := M v5 y
  have h9 := R v5
  have h10 := R x
  have h11 := S (h v5 v5 x)
  let v12 := M v5 x
  let v13 := M v5 (M v12 x)
  let v14 := M x (M (M x x) x)
  have h15 := h x x x
  T (h x v5 x) (C h9 (T (T (T (T (T (C h10 (C (R v12) (T h15 (C h15 (R v14))))) (S (h v12 x v14))) (C h9 (T (T (T (h x v5 v13) (C h9 (T (T (C h10 (T (C h11 (R v13)) h11)) (C h10 (T (h v5 y v0) (C h4 (C h9 h7))))) (S (h y x y))))) (h v8 y v0)) (C h4 (C (R v8) h7))))) (S (h y v5 y))) (h y z y)) (C (R z) (T (C h4 (C (R v1) (T h3 (C h3 h2)))) (S (h v1 y v0))))))

@[equational_result]
theorem Equation684_implies_Equation2335 (G: Type _) [Magma G] (h: Equation684 G) : Equation2335 G := fun x y z =>
  let v0 := M x z
  let v1 := M z (M (M z v0) v0)
  let v2 := M y v0
  let v3 := M y v2
  let v4 := M v3 z
  have h5 := h z z v0
  have h6 := S (h z z x)
  let v7 := M z (M (M z x) x)
  have h8 := T (C h6 (R v7)) h6
  have h9 := R v4
  have h10 := R z
  have h11 := S (h v4 v4 z)
  let v12 := M v4 (M (M v4 z) z)
  let v13 := M v0 (M (M v0 x) x)
  have h14 := h v0 v0 x
  T (T (h x z v7) (C h10 (T (T (T (T (C (R x) h8) (h v0 y v0)) (C (R y) (T (C (R v0) (C (R v2) (T h14 (C h14 (R v13))))) (S (h v2 v0 v13))))) (h v3 v4 v12)) (C h9 (T (T (T (C (R v3) (T (T (T (C h11 (R v12)) h11) (h v4 z v7)) (C h10 (C h9 h8)))) (S (h z v3 z))) h5) (C h5 (R v1))))))) (S (h v4 z v1))

@[equational_result]
theorem Equation1304_implies_Equation572 (G: Type _) [Magma G] (h: Equation1304 G) : Equation572 G := fun x y z =>
  let v0 := M x y
  let v1 := M z v0
  let v2 := M z v1
  let v3 := M y v2
  have h4 := R v3
  have h5 := R y
  let v6 := M (M (M y x) x) y
  have h7 := R v2
  have h8 := h y y x
  let v9 := M (M (M z x) x) z
  have h10 := R v0
  have h11 := h z z x
  let v12 := M (M (M x x) x) x
  have h13 := h x y v12
  have h14 := R v12
  have h15 := h x x x
  have h16 := S h15
  T (T (T (T h13 (C h5 (C (T (C h16 h14) h16) h5))) (h (M y v0) v3 y)) (C h4 (C (C (T (T (C (T (C h5 (C (T h15 (C h15 h14)) h5)) (S h13)) h5) (h v0 v3 v1)) (C h4 (T (T (C (C (T (C h10 (C (T h11 (C h11 (R v9))) h10)) (S (h z v0 v9))) (R v1)) h4) (C h7 (C (T h8 (C h8 (R v6))) h7))) (S (h y v2 v6))))) h5) h4))) (S (h v3 v3 y))

@[equational_result]
theorem Equation1507_implies_Equation2373 (G: Type _) [Magma G] (h: Equation1507 G) : Equation2373 G := fun x y z =>
  let v0 := M x z
  let v1 := M z v0
  let v2 := M y v1
  let v3 := M v2 y
  let v4 := M x v0
  have h5 := R v4
  let v6 := M z v3
  let v7 := M z v6
  have h8 := h y v2 v3
  let v9 := M v3 (M v3 v2)
  let v10 := M v0 (M v0 v0)
  have h11 := h z x v3
  let v12 := M v3 (M v3 x)
  let v13 := M z x
  T (T (h x z x) (C (T (T (T (T (T (T (T (h v13 z x) (C (T (T (T (T (h (M z v13) v0 x) (C (T (S (h z x z)) h11) (R (M x v4)))) (S (h v12 v0 x))) (h v12 v0 v0)) (C (S h11) (R v10))) h5)) (S (h v10 z x))) (h v10 (M v0 x) v0)) (C (S (h x v0 v0)) (S (h z x v0)))) (h v0 z x)) (C (T (T (h v1 y x) (C (T (T (T (C h8 (h v1 y v2)) (S (h v9 v3 v2))) (h v9 v3 z)) (C (S h8) (R v7))) (R (M x (M x y))))) (S (h v7 y x))) h5)) (S (h v6 z x))) h5)) (S (h v3 z x))

@[equational_result]
theorem Equation2105_implies_Equation2755 (G: Type _) [Magma G] (h: Equation2105 G) : Equation2755 G := fun x y z =>
  let v0 := M z x
  let v1 := M y y
  let v2 := M v1 v0
  let v3 := M v2 z
  let v4 := M v2 v2
  have h5 := R v4
  have h6 := R v1
  have h7 := R v3
  have h8 := S (h v1 y x)
  have h9 := R (M x x)
  have h10 := R y
  have h11 := h y y y
  have h12 := C (S h11) h6
  have h13 := h y v1 y
  let v14 := M v3 v3
  have h15 := S (h v2 v1 y)
  have h16 := C (C (T (T (h v4 y x) (C (C (T (T (T (C h11 h5) (S (h y v1 v2))) h13) h12) h10) h9)) h8) (R v2)) h6
  have h17 := h v2 v2 y
  T (T (h x z v2) (C (T (h (M v0 z) v3 y) (C (C (T (T (T (C h7 (C (T (T (h v0 v1 y) (C (T (T (T (C (T h17 h16) h6) h15) h17) h16) h6)) h15) (R z))) (h v14 y x)) (C (C (T (T (T (C h11 (R v14)) (S (h y v1 v3))) h13) h12) h10) h9)) h8) h7) h6)) h5)) (S (h v3 v1 v2))

@[equational_result]
theorem Equation2779_implies_Equation1171 (G: Type _) [Magma G] (h: Equation2779 G) : Equation1171 G := fun x y z =>
  let v0 := M y z
  let v1 := M z v0
  let v2 := M v1 x
  let v3 := M y v2
  have h4 := h v3 y v3
  have h5 := R y
  let v6 := M v0 v0
  let v7 := M y v3
  have h8 := R v3
  have h9 := h y y z
  have h10 := h y v2 y
  let v11 := M (M v2 y) (M y y)
  have h12 := R (M v7 (M v11 v3))
  have h13 := h x v0 v3
  T (T (T (T (T (T (T (T h13 (C (T (h (M (M v0 v3) (M x v3)) z v0) (C (C (R v1) (S h13)) (R z))) (R v0))) (h (M (M v2 z) v0) x v2)) (C (C (R (M x v2)) (T (S (h y v2 z)) h10)) (R x))) (S (h v11 x v2))) (h v11 y v3)) (C h12 h5)) (C (T (T h12 (C (C h9 h4) (T (C (T (h v11 y v2) (C (C h8 (S h10)) h9)) h8) (S (h v6 v3 y))))) (S (h (M v7 (M v3 v3)) v6 y))) h5)) (S h4)

@[equational_result]
theorem Equation887_implies_Equation2755 (G: Type _) [Magma G] (h: Equation887 G) : Equation2755 G := fun x y z =>
  let v0 := M z x
  let v1 := M y y
  let v2 := M v1 v0
  let v3 := M v2 z
  let v4 := M v3 v3
  let v5 := M v1 v1
  let v6 := M v2 v1
  have h7 := h v0 v6 v5
  have h8 := R (M v5 v5)
  have h9 := h v1 v0 y
  have h10 := h v1 v1 v1
  have h11 := R v6
  have h12 := R v0
  have h13 := R v3
  T (T (h x v0 v3) (C h12 (C (T (h (M x v0) v3 v1) (C h13 (T (T (T (C (T (T (C (T (C (R x) (h v0 v0 v0)) (S (h z x (M v0 v0)))) h13) (C (R z) (h v3 v3 v3))) (S (h v2 z v4))) (C (T (T (h v1 v0 (M v2 v2)) (C h12 (S (h v2 v2 v2)))) (C (T h7 (C h11 (T (C (S h9) h8) (S h10)))) (R v2))) (R v1))) (S (h (M v6 v1) v2 y))) (C h11 (T h10 (C h9 h8)))) (S h7)))) (R v4)))) (S (h v3 v0 v3))

@[equational_result]
theorem Equation2741_implies_Equation3500 (G: Type _) [Magma G] (h: Equation2741 G) : Equation3500 G := fun x y z =>
  let v0 := M z z
  let v1 := M v0 y
  let v2 := M y v1
  have h3 := h v2 v0 v2
  have h4 := R v2
  let v5 := M v2 v2
  let v6 := M v0 v0
  have h7 := h v0 z v2
  have h8 := R v0
  let v9 := M v0 v2
  let v10 := M x x
  let v11 := M v1 v1
  have h12 := R v10
  let v13 := M v10 v10
  have h14 := h v10 v2 v10
  T (T (T (T (T (T h14 (C (T (T (T (h (M v5 v13) x v10) (C (T (C h12 (S h14)) (C h12 (h v10 v1 v10))) h12)) (S (h (M v11 v13) x v10))) (C (R v11) (T (T (h v13 x x) (C (T (C h12 (S (h x x x))) (C h12 (h x v1 x))) (R x))) (S (h (M v11 v10) x x))))) h12)) (S (h v11 v1 v10))) (C (C h8 (h y z v1)) (R v1))) (S (h v9 z v1))) (C (T (T h7 (C (T (T (h (M v0 v9) z v2) (C (C h8 (S h7)) h4)) (C (R v6) h3)) h4)) (S (h (M v6 v5) v0 v2))) h4)) (S h3)

@[equational_result]
theorem Equation2958_implies_Equation3364 (G: Type _) [Magma G] (h: Equation2958 G) : Equation3364 G := fun x y z =>
  let v0 := M x z
  let v1 := M z v0
  have h2 := R z
  let v3 := M v1 z
  have h4 := S (h v1 x v1)
  let v5 := M (M x (M x v1)) v1
  have h6 := R v0
  have h7 := S (h z x z)
  let v8 := M (M x v0) z
  let v9 := M (M x (M x x)) x
  have h10 := R x
  have h11 := h x x x
  have h12 := T h11 (C (R v9) h11)
  let v13 := M x y
  let v14 := M (M x (M x v13)) v13
  let v15 := M v13 x
  have h16 := h v13 x v13
  T (h v13 v13 x) (C (T (T (T (C (C (T h16 (C (R v14) h16)) (R v15)) (R v13)) (S (h v15 v14 v13))) (C (C h12 (R y)) h10)) (S (h y v9 x))) (T (T (h x x z) (C (T (T (T (T (T (C (C h12 h6) h10) (S (h v0 v9 x))) (h v0 v8 z)) (C (C (T (C (R v8) h7) h7) h6) h2)) (h v3 v5 v1)) (C (C (T (C (R v5) h4) h4) (R v3)) (R v1))) h2)) (S (h v1 v1 z))))

