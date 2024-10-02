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
theorem Equation1537_implies_Equation1384 (G: Type _) [Magma G] (h: Equation1537 G) : Equation1384 G := fun x y z =>
  let v0 := M z z
  let v1 := M v0 x
  let v2 := M y (M v1 y)
  have h3 := h v0 x z
  have h4 := h z z z
  have h5 := S h4
  have h6 := R v0
  have h7 := h z z v0
  have h8 := R z
  let v9 := M v2 v2
  let v10 := M x x
  have h11 := R v10
  T (T (T (T (h x z v0) (C h6 (T (C h6 (C (R x) (T (T h3 (C h11 (T (C h8 (T (C h6 h4) (S h7))) (C h8 (T (h z x v0) (C h11 h5)))))) (S (h v10 x z))))) (S (h x z x))))) (h v1 v1 y)) (C (R (M v1 v1)) (T (h v2 z v2) (C h6 (C (R v2) (T (T (h v9 x z) (C h11 (T (C h8 (T (C (R v9) h4) (S (h z v2 v0)))) (C h8 (T h7 (C h6 h5)))))) (S h3))))))) (S (h v2 v1 v0))

@[equational_result]
theorem Equation2104_implies_Equation2 (G: Type _) [Magma G] (h: Equation2104 G) : Equation2 G := fun x y =>
  have h0 := h y x x
  have h1 := S h0
  have h2 := h x x x
  have h3 := S h2
  have h4 := C h3 h3
  let v5 := M x x
  have h6 := h x v5 (M v5 x)
  have h7 := h x v5 (M (M x y) x)
  have h8 := S h7
  have h9 := C h2 h0
  have h10 := R x
  have h11 := S h6
  have h12 := C h2 h2
  have h13 := S (h v5 x y)
  let v14 := M y x
  have h15 := R v14
  have h16 := C h10 (T h6 h4)
  T (T (h x y x) (C (T (T (T (T (T (C (T (T (T (T (h v14 x y) (C (C (T (T (C (T (T (T h6 h4) h16) (C (T (T h6 h4) h16) (T h12 h11))) h15) h13) h16) h10) h15)) h13) h12) h11) (R y)) h9) h8) h6) h4) (C (T h7 (C h3 h1)) h10)) (T (T (T h9 h8) h6) h4))) h1

@[equational_result]
theorem Equation2196_implies_Equation2522 (G: Type _) [Magma G] (h: Equation2196 G) : Equation2522 G := fun x y z =>
  let v0 := M x z
  let v1 := M v0 z
  let v2 := M y v1
  let v3 := M v2 y
  let v4 := M v3 y
  let v5 := M v1 x
  have h6 := h v1 x z
  let v7 := M v1 z
  have h8 := h x z v2
  let v9 := M (M z v2) v2
  let v10 := M (M v0 v0) v0
  T (T (T (T (T (T (h x z v3) (C (R (M (M z v3) v3)) (T (T (T (T (C (h x z v0) (h z v0 v0)) (S (h v10 (M z v0) v0))) (h v10 x x)) (C (R (M (M x x) x)) (T (T (T (C (R v10) h8) (S (h v9 v0 v0))) (h v9 v0 z)) (C (R v7) (S h8))))) (S (h v7 x x))))) (S (h v1 z v3))) (h v1 v2 y)) (C (R v4) (T (C (T h6 (C h6 (R v5))) (R v2)) (S (h y v1 v5))))) (h (M v4 y) (M y v3) v3)) (C (S (h v2 y v3)) (S (h y v3 y)))

@[equational_result]
theorem Equation2663_implies_Equation2850 (G: Type _) [Magma G] (h: Equation2663 G) : Equation2850 G := fun x y =>
  let v0 := M x x
  let v1 := M x v0
  let v2 := M v1 y
  let v3 := M v2 y
  have h4 := h v3 v1
  have h5 := R v1
  let v6 := M v3 v1
  have h7 := h v2 y
  have h8 := S (h v1 v1)
  let v9 := M v1 v1
  have h10 := h v9 v0
  have h11 := R v0
  have h12 := h x v0
  have h13 := T (C (C h12 h12) h11) (S h10)
  let v14 := M v0 v0
  have h15 := h v0 v0
  have h16 := S h12
  T (T (T (T (T (T h12 (C (T (T h10 (C (C h16 h16) h11)) (C h15 h15)) h11)) (S (h (M v14 v14) v0))) (C h13 h13)) (h (M v9 v9) v1)) (C (T (T (C h8 h8) (C (T (T (T (h v1 y) (C (C h7 h7) (R y))) (S (h (M v3 v3) y))) (C h4 h4)) h5)) (S (h (M v6 v6) v1))) h5)) (S h4)

@[equational_result]
theorem Equation3804_implies_Equation3906 (G: Type _) [Magma G] (h: Equation3804 G) : Equation3906 G := fun x y z =>
  let v0 := M x x
  let v1 := M z z
  let v2 := M y v1
  let v3 := M v2 v0
  let v4 := M v0 y
  have h5 := h x x x
  have h6 := h x x y
  have h7 := S h6
  have h8 := S (h y x x)
  let v9 := M y x
  let v10 := M x y
  T (T (T (T (T h5 (C (R v0) (T (T (T (h x x z) (h (M z x) (M x z) v1)) (C (S (h x z z)) (S (h z x z)))) (S (h z z x))))) (h v0 v1 y)) (C (T (T (h y v1 y) (h v2 (M y y) v0)) (C (T (T (T (T (C h6 (h y y x)) (S (h v10 v10 v9))) (h v10 v10 v0)) (C (T (T (h v0 v10 v9) (C h7 h8)) h8) (S (h x y x)))) h7) (R v3))) (T (h v0 y v0) (C (R v4) (S h5))))) (S (h v4 v3 v0))) (S (h v2 y v0))

@[equational_result]
theorem Equation3804_implies_Equation4421 (G: Type _) [Magma G] (h: Equation3804 G) : Equation4421 G := fun x y z =>
  let v0 := M x y
  let v1 := M z y
  let v2 := M v1 v0
  let v3 := M v0 z
  have h4 := h x y y
  let v5 := M v0 v0
  have h6 := R v5
  have h7 := h x y x
  have h8 := h z y x
  let v9 := M x v0
  have h10 := h x v0 v0
  T (T (T (T (T (T h10 (C (T (T (T (h v0 v0 v9) (C (h v9 v0 x) (R (M v0 v9)))) (S (h v0 (M v9 x) v9))) (S (h v9 y x))) h10)) (S (h v5 y v9))) (h v5 y z)) (C (T (T (T (T h8 (h v0 (M z x) v0)) (C (S h8) h6)) (h v1 v5 v0)) (C (T (T (C h7 h6) (S (h v0 (M x x) v0))) (S h7)) (R v2))) (T (h v5 z v0) (C (R v3) (T (T (C h6 h4) (S (h (M y y) v0 v0))) (S h4)))))) (S (h v3 v2 v0))) (S (h v1 z v0))

@[equational_result]
theorem Equation3804_implies_Equation4450 (G: Type _) [Magma G] (h: Equation3804 G) : Equation4450 G := fun x y z =>
  let v0 := M y x
  let v1 := M x v0
  let v2 := M y z
  let v3 := M v2 v1
  have h4 := R v1
  have h5 := h x v0 x
  let v6 := M x x
  let v7 := M z v0
  let v8 := M v2 y
  T (T (T (T (T h5 (h v1 v6 v2)) (C (R (M v2 v6)) (T (T (T (C h4 (T (T (T (T (T (T (h y z v2) (C (h v2 z y) (R (M y v2)))) (S (h y v8 v2))) (h y v8 v0)) (C (S (h v2 x y)) (R (M y v0)))) (C (R (M v2 x)) (h y v0 z))) (S (h v7 x v2)))) (S (h v7 v0 x))) (h v7 v0 (M x z))) (C (S (h y z x)) (S (h x v0 z)))))) (C (T (h v2 v6 v1) (C (S h5) (R v3))) (C (T (T (h y z v0) (C (R (M v0 z)) (h y v0 x))) (S (h v1 z v0))) h4))) (S (h (M v1 z) v3 v1))) (S (h v2 z v1))

@[equational_result]
theorem Equation3959_implies_Equation3331 (G: Type _) [Magma G] (h: Equation3959 G) : Equation3331 G := fun x y z =>
  let v0 := M y z
  let v1 := M z v0
  have h2 := R v1
  let v3 := M x v1
  have h4 := R z
  let v5 := M y v3
  have h6 := h z v5 v0
  have h7 := S h6
  have h8 := R v0
  have h9 := h x y v1
  let v10 := M x y
  have h11 := h y v10 z
  have h12 := h x y y
  have h13 := S h12
  have h14 := R y
  let v15 := M y v10
  T (T (T h12 (h v15 y v1)) (C (T (T (T (T (C h14 (T (T (h v15 v1 y) (C (T (T (T (T (C h2 h13) (h v1 v10 z)) (C (T (C h9 (S (h y z z))) h7) h4)) (C (T h6 (C (S h9) h8)) h4)) (S h11)) h14)) h13)) h11) (C (T (C h9 h8) h7) h4)) (h (M z v5) z v3)) (C (C h4 (S (h y z v3))) (R v3))) h2)) (S (h x v1 v1))

@[equational_result]
theorem Equation909_implies_Equation703 (G: Type _) [Magma G] (h: Equation909 G) : Equation703 G := fun x y =>
  let v0 := M x x
  let v1 := M v0 x
  let v2 := M y v1
  let v3 := M y v2
  have h4 := h v3 v1
  let v5 := M v1 v3
  have h6 := h v2 y
  have h7 := R v1
  have h8 := S (h v1 v1)
  let v9 := M v1 v1
  have h10 := h v9 v0
  have h11 := h x v0
  have h12 := R v0
  have h13 := T (C h12 (C h11 h11)) (S h10)
  let v14 := M v0 v0
  have h15 := h v0 v0
  have h16 := S h11
  T (T (T (T (T (T h11 (C h12 (T (T h10 (C h12 (C h16 h16))) (C h15 h15)))) (S (h (M v14 v14) v0))) (C h13 h13)) (h (M v9 v9) v1)) (C h7 (T (T (C h8 h8) (C h7 (T (T (T (h v1 y) (C (R y) (C h6 h6))) (S (h (M v3 v3) y))) (C h4 h4)))) (S (h (M v5 v5) v1))))) (S h4)

@[equational_result]
theorem Equation1943_implies_Equation26 (G: Type _) [Magma G] (h: Equation1943 G) : Equation26 G := fun x y =>
  let v0 := M x y
  let v1 := M v0 y
  have h2 := S (h y y v1)
  let v3 := M x v0
  have h4 := h v3 x v0
  have h5 := h x x y
  have h6 := h x v1 y
  have h7 := R (M x v3)
  let v8 := M v1 (M v1 y)
  have h9 := h v8 x v0
  have h10 := h v8 y v1
  have h11 := h v0 v1 y
  let v12 := M y v1
  let v13 := M y v12
  have h14 := R v13
  T (T (T (T (h x v1 v0) (C (R (M v1 (M v1 v0))) (T (T (T (T h4 (C h7 (T (S h5) h6))) (S h9)) h10) (C h14 (S h11))))) (S (h v13 v1 v0))) (h v13 v13 v12)) (C (C (T (T (h v13 x v0) (C h7 (T (T (T (T (C h14 h11) (S h10)) h9) (C h7 (T (S h6) h5))) (S h4)))) (S (h x x v0))) h2) h2)

@[equational_result]
theorem Equation2196_implies_Equation2186 (G: Type _) [Magma G] (h: Equation2196 G) : Equation2186 G := fun x y z =>
  let v0 := M y z
  let v1 := M z x
  let v2 := M v0 y
  let v3 := M v2 v1
  have h4 := S (h v2 v1 v3)
  let v5 := M v1 v3
  let v6 := M (M v3 v0) v0
  let v7 := M v5 v3
  have h8 := h z x v3
  let v9 := M (M x v3) v3
  let v10 := M v1 x
  let v11 := M x z
  T (T (T (T (h x z v0) (C (T (h (M (M z v0) v0) v0 y) (C (R (M v2 y)) (S (h y z v0)))) (T (T (T (T (h v11 z x) (C (R v10) (T (T (T (T (h (M v11 z) v1 x) (C (R (M v10 x)) (T (S (h z x z)) h8))) (S (h v9 v1 x))) (h v9 v1 v3)) (C (R v7) (S h8))))) (S (h v7 z x))) (h v7 v3 v0)) (C (R v6) h4)))) (S (h v6 v2 y))) (h v6 v5 v3)) (C h4 (S (h v1 v3 v0)))

@[equational_result]
theorem Equation3211_implies_Equation1358 (G: Type _) [Magma G] (h: Equation3211 G) : Equation1358 G := fun x y z =>
  let v0 := M z x
  let v1 := M v0 z
  let v2 := M v1 y
  have h3 := R v2
  have h4 := h y v1 y
  have h5 := C (S h4) h3
  have h6 := h v1 v2 y
  have h7 := R z
  have h8 := R v0
  have h9 := h z v0 v1
  have h10 := R v1
  have h11 := h v0 v1 z
  have h12 := h z v0 z
  have h13 := h v1 z v1
  T (T (T (h x z v0) (C (T (C (T (C (C (T h9 (C (T (T (T (C (C (C (T h11 (C (S h12) h10)) h10) h10) h7) (S h13)) h6) h5) h8)) h8) h8) (C (C (T (T (T (C (T (T (T (C h4 h3) (S h6)) h13) (C (C (C (T (C h12 h10) (S h11)) h10) h10) h7)) h8) (S h9)) (h z v0 x)) (C (S (h x z x)) h8)) h8) h8)) (R x)) (S (h v0 x v0))) h7)) h6) h5

@[equational_result]
theorem Equation3804_implies_Equation4515 (G: Type _) [Magma G] (h: Equation3804 G) : Equation4515 G := fun x y z =>
  let v0 := M x z
  let v1 := M y z
  let v2 := M v0 v0
  let v3 := M v0 y
  have h4 := h y z y
  have h5 := h v0 y y
  have h6 := h v1 v3 (M y y)
  have h7 := h v0 z y
  let v8 := M x v1
  let v9 := M x x
  T (T (T (T (T (T (T (h x v1 x) (h v8 v9 v0)) (C (T (h v0 v9 v0) (C (S (h x z x)) (R v2))) (R (M v8 v0)))) (S (h v8 v2 v0))) (h v8 v2 v1)) (C (R (M v1 v2)) (T (T (T (T (T (h v8 v1 v3) (C (T (T (C h5 h4) (S h6)) (S h7)) (T (C (T (T (T (h x v1 z) (h (M z v1) v0 v1)) (C (R (M v1 v0)) (S (h y v1 z)))) (S (h y v0 v1))) (R v3)) (S (h v0 v0 y))))) (S (h v0 z v0))) h7) h6) (C (S h5) (S h4))))) (S (h v3 v2 v1))) (S (h v0 y v0))

@[equational_result]
theorem Equation492_implies_Equation1320 (G: Type _) [Magma G] (h: Equation492 G) : Equation1320 G := fun x y z =>
  let v0 := M y x
  let v1 := M v0 z
  let v2 := M v1 z
  have h3 := h v2 v1 v2
  have h4 := h v1 z v1
  have h5 := R v2
  have h6 := h z v2 v1
  have h7 := R v1
  have h8 := R z
  have h9 := h v1 z v2
  have h10 := R v0
  have h11 := R y
  have h12 := R x
  T (h x y v2) (C h11 (T (C h12 (C h5 (C h5 (T (h y v2 x) (C h5 (T (C h11 (C h12 (C h12 (T (h v2 x y) (C h12 (T (C h5 (C h11 (T (h v0 z z) (C h8 (T (T (C h10 (T (C h8 (C h8 (T (h z v0 v1) (C h10 (T (C h8 (T (T (C h7 (T (C h7 (h v0 z v0)) (S (h z v1 v0)))) h3) (C h7 (C h5 (C h5 (T (C h5 h4) (S h6))))))) (S h9)))))) (S (h z z v0)))) h9) (C h8 (T (C h7 (C h5 (C h5 (T h6 (C h5 (S h4)))))) (S h3)))))))) (S (h y v2 z)))))))) (S (h x y x)))))))) (S (h v2 x v2))))

@[equational_result]
theorem Equation1507_implies_Equation1181 (G: Type _) [Magma G] (h: Equation1507 G) : Equation1181 G := fun x y z =>
  let v0 := M z x
  let v1 := M z v0
  let v2 := M v1 y
  let v3 := M y v2
  let v4 := M y v3
  let v5 := M x v1
  have h6 := h v1 x z
  let v7 := M z v1
  have h8 := h x z v2
  let v9 := M v2 (M v2 z)
  let v10 := M v0 (M v0 v0)
  T (T (T (T (T (T (h x z v3) (C (T (T (T (T (C (h z v0 v0) (h x z v0)) (S (h v10 (M v0 z) v0))) (h v10 x x)) (C (T (T (T (C h8 (R v10)) (S (h v9 v0 v0))) (h v9 v0 z)) (C (S h8) (R v7))) (R (M x (M x x))))) (S (h v7 x x))) (R (M v3 (M v3 z))))) (S (h v1 z v3))) (h v1 v2 y)) (C (T (C (R v2) (T h6 (C (R v5) h6))) (S (h y v1 v5))) (R v4))) (h (M y v4) (M v3 y) v3)) (C (S (h y v3 y)) (S (h v2 y v3)))

@[equational_result]
theorem Equation1902_implies_Equation4098 (G: Type _) [Magma G] (h: Equation1902 G) : Equation4098 G := fun x y z =>
  let v0 := M y y
  let v1 := M v0 z
  have h2 := h (M y (M z y)) v0 v1
  have h3 := R (M v1 v1)
  have h4 := h z y y
  have h5 := R v0
  have h6 := R v1
  let v7 := M x x
  have h8 := R v7
  let v9 := M v0 x
  T (T (T (T (T (T (C (R x) (T (T (h x v7 x) (C (C h8 (T (h (M x v7) v0 x) (C (C h5 (S (h x x y))) h8))) h8)) (S (h v9 v7 x)))) (h (M x v9) v7 x)) (C (C h8 (S (h v0 x x))) h8)) (C (C h8 (h v0 z x)) h8)) (S (h (M z v1) v7 x))) (C (T (T (h z y v0) (C (T h2 (C (C h5 (S h4)) h3)) (R (M v0 v0)))) (S (h v1 v1 v0))) h6)) (C h6 (T (T (h v1 v1 z) (C (T (C (C h5 h4) h3) (S h2)) (R (M z z)))) (S (h z y z))))

@[equational_result]
theorem Equation3804_implies_Equation3794 (G: Type _) [Magma G] (h: Equation3804 G) : Equation3794 G := fun x y z =>
  let v0 := M z x
  let v1 := M z y
  let v2 := M v0 v0
  let v3 := M v0 v1
  have h4 := S (h z x z)
  let v5 := M z z
  have h6 := S (h z y x)
  let v7 := M x y
  have h8 := T (T (C (h z x x) (h x y x)) (S (h v7 v0 (M x x)))) h6
  have h9 := h z y z
  let v10 := M y y
  let v11 := M v10 v0
  T (T (T (T (T (T (T (T (T (h x y y) (h v10 v7 v0)) (C h8 (R v11))) (h v1 v11 v3)) (C (T (T (S (h v10 v1 v0)) (S (h z y y))) h9) (T (T (T (C h9 (R v3)) (S (h v0 v5 v1))) (h v0 v5 v7)) (C (T (h v7 v5 v0) (C h4 h6)) h8)))) (S (h v3 v5 v1))) (h v3 v5 v0)) (C (T (h v0 v5 v0) (C h4 (R v2))) (R (M v3 v0)))) (S (h v3 v2 v0))) (S (h v0 v1 v0))

@[equational_result]
theorem Equation684_implies_Equation1699 (G: Type _) [Magma G] (h: Equation684 G) : Equation1699 G := fun x y z =>
  let v0 := M y z
  let v1 := M y x
  let v2 := M v1 (M (M v1 v0) v0)
  let v3 := M v1 (M v0 z)
  have h4 := h v1 v1 v0
  have h5 := R v3
  have h6 := S (h v3 v3 x)
  let v7 := M v3 (M (M v3 x) x)
  have h8 := R y
  let v9 := M x (M (M x x) x)
  have h10 := h x x x
  have h11 := R x
  have h12 := S (h v1 v1 y)
  let v13 := M v1 (M (M v1 y) y)
  T (T (h x v1 v13) (C (R v1) (T (T (T (T (T (C h11 (T (C h12 (R v13)) h12)) (C h11 (C h8 (T h10 (C h10 (R v9)))))) (S (h y x v9))) (h y v3 v7)) (C h5 (T (C h8 (T (C h6 (R v7)) h6)) (S (h v1 y z))))) (C h5 (T h4 (C h4 (R v2))))))) (S (h v3 v1 v2))

@[equational_result]
theorem Equation1537_implies_Equation978 (G: Type _) [Magma G] (h: Equation1537 G) : Equation978 G := fun x y z =>
  let v0 := M z z
  let v1 := M x y
  let v2 := M y (M v0 v1)
  have h3 := h v0 x z
  have h4 := h z z z
  have h5 := S h4
  have h6 := R v0
  have h7 := h z z v0
  have h8 := R z
  let v9 := M v2 v2
  have h10 := R (M x x)
  let v11 := M v1 v1
  T (T (h x y y) (C (R (M y y)) (T (T (C (R y) (T (h v1 z v0) (C h6 (T (C h6 (C (R v1) (T (T h3 (C h10 (T (C h8 (T (C h6 h4) (S h7))) (C h8 (T (h z v1 v0) (C (R v11) h5)))))) (S (h v11 x z))))) (S (h v1 z v1)))))) (h v2 z v2)) (C h6 (C (R v2) (T (T (h v9 x z) (C h10 (T (C h8 (T (C (R v9) h4) (S (h z v2 v0)))) (C h8 (T h7 (C h6 h5)))))) (S h3))))))) (S (h v2 y v0))

@[equational_result]
theorem Equation1891_implies_Equation2 (G: Type _) [Magma G] (h: Equation1891 G) : Equation2 G := fun x y =>
  let v0 := M x x
  let v1 := M y x
  let v2 := M x v0
  have h3 := h x v2 v2
  have h4 := R (M v2 v2)
  have h5 := h x x x
  have h6 := T (C h5 h4) (S h3)
  let v7 := M y y
  let v8 := M x v7
  have h9 := h x v8 v8
  have h10 := R (M v8 v8)
  have h11 := h y x x
  have h12 := T (T (T (C h11 h10) (S h9)) h3) (C (S h5) h4)
  have h13 := h x v0 v0
  have h14 := S h13
  have h15 := T (T h14 h9) (C (S h11) h10)
  let v16 := M v0 v0
  T (T h13 (C (T (h v16 y y) (C (C (R y) h14) (R v7))) (T (h v16 x y) (C (T (T (T (C h13 (R (M v16 v16))) (C h15 h15)) (C h12 h12)) (C h6 h6)) (R v1))))) (S (h y v1 v0))

@[equational_result]
theorem Equation1993_implies_Equation1523 (G: Type _) [Magma G] (h: Equation1993 G) : Equation1523 G := fun x y z =>
  let v0 := M z z
  let v1 := M x v0
  let v2 := M y y
  let v3 := M v2 v1
  let v4 := M v3 v3
  let v5 := M v3 (M v1 v1)
  have h6 := S (h v2 v1 x)
  have h7 := h x x z
  have h8 := C h7 (R v3)
  have h9 := h x v0 x
  let v10 := M x x
  let v11 := M v0 v10
  let v12 := M v1 v2
  T (T (T (T (h x v3 y) (C (R (M v3 v2)) (T (T h8 h6) (h v2 v1 v3)))) (S (h (M v1 v4) v3 y))) (C (T (T (h v1 v2 x) (C (R (M v2 v10)) (T (T (T (T (h v12 x x) (C (R (M x v10)) (T (T (T (C (R v12) h9) (S (h v11 v1 y))) (h v11 v1 x)) (C (S h7) (S h9))))) (S (h x x x))) (h x v3 v1)) (C (R v5) (T h8 h6))))) (S (h v5 v2 x))) (R v4))) (S (h v3 v3 v1))

@[equational_result]
theorem Equation3804_implies_Equation4684 (G: Type _) [Magma G] (h: Equation3804 G) : Equation4684 G := fun x y z =>
  let v0 := M z y
  have h1 := R (M v0 z)
  let v2 := M x y
  let v3 := M v2 v0
  have h4 := R v3
  let v5 := M y y
  have h6 := h z y y
  let v7 := M v2 y
  let v8 := M v0 v7
  have h9 := R v8
  T (T (T (T (T (T (T (T (h v2 z y) (h (M y z) v7 v0)) (C h9 (S (h z z y)))) (h v8 (M z z) v0)) (C (S (h z y z)) (T (T (C h9 h6) (S (h v5 v7 v0))) (S (h v2 y y))))) (h v0 v7 z)) (C (T (T (T (h z v7 v0) (C h9 (h z v0 y))) (S (h (M y v0) v7 v0))) (S (h v2 v0 y))) h1)) (C (T (T (T (T (C (h x y x) (T (T h6 (h v5 v0 v2)) (C h4 (S (h x y y))))) (S (h v3 (M x x) v2))) (C h4 (h x x y))) (S (h (M y x) v0 v2))) (S (h z x y))) h1)) (S (h v0 x z))

@[equational_result]
theorem Equation684_implies_Equation1358 (G: Type _) [Magma G] (h: Equation684 G) : Equation1358 G := fun x y z =>
  have h0 := S (h y y x)
  let v1 := M y (M (M y x) x)
  let v2 := M z x
  let v3 := M v2 z
  have h4 := R v3
  have h5 := S (h v3 v3 x)
  let v6 := M v3 (M (M v3 x) x)
  let v7 := M z v3
  have h8 := S (h z z x)
  let v9 := M z (M v2 x)
  have h10 := R v2
  have h11 := R z
  let v12 := M x (M (M x x) x)
  have h13 := h x x x
  T (T (T (T (T (h x z x) (C h11 (T (C (R x) (C h10 (T h13 (C h13 (R v12))))) (S (h v2 x v12))))) (C h11 (T (T (T (h v2 z v9) (C h11 (C h10 (T (C h8 (R v9)) h8)))) (h v7 v3 v6)) (C h4 (C (R v7) (T (C h5 (R v6)) h5)))))) (S (h v3 z v3))) (h v3 y v1)) (C (R y) (C h4 (T (C h0 (R v1)) h0)))

@[equational_result]
theorem Equation2105_implies_Equation3008 (G: Type _) [Magma G] (h: Equation2105 G) : Equation3008 G := fun x y z =>
  let v0 := M z z
  let v1 := M y v0
  let v2 := M v1 x
  let v3 := M v2 y
  have h4 := R v0
  have h5 := R v3
  have h6 := S (h v0 z x)
  have h7 := R (M x x)
  have h8 := R z
  have h9 := h z z z
  have h10 := C (T (h z v0 z) (C (S h9) h4)) h8
  let v11 := M v3 v3
  let v12 := M y y
  T (T (h x v1 v0) (C (T (h (M v2 v1) v3 z) (C (C (T (T (T (C h5 (C (R v2) (T (C (T (h y y z) (C (C (T (T (h v12 z x) (C (T (C (T (C h9 (R v12)) (S (h z v0 y))) h8) h10) h7)) h6) (R y)) h4)) h4) (S (h y v0 z))))) (h v11 z x)) (C (T (C (T (C h9 (R v11)) (S (h z v0 v3))) h8) h10) h7)) h6) h5) h4)) (R (M v0 v0)))) (S (h v3 v0 v0))

@[equational_result]
theorem Equation2170_implies_Equation1320 (G: Type _) [Magma G] (h: Equation2170 G) : Equation1320 G := fun x y z =>
  let v0 := M y x
  let v1 := M v0 z
  let v2 := M v1 z
  let v3 := M y v2
  have h4 := R (M v3 v2)
  let v5 := M v2 v3
  have h6 := h v5 v1 z
  let v7 := M z v1
  have h8 := R v7
  have h9 := R v5
  have h10 := h v2 y v2
  have h11 := h (M v2 y) v3 v2
  have h12 := T (T h6 (C (T (C h10 h9) (S h11)) h8)) (S (h y v1 z))
  T (T (h x v2 v3) (C (T (T (T (T (T (T (T (T (C h12 (R x)) (h v0 (M x y) v1)) (C (S (h v1 x y)) (S (h z y x)))) (h v2 v2 v3)) (C (C h12 (R v2)) h4)) (C (h v3 v1 z) h4)) (S (h v7 v2 v3))) (h v7 v2 y)) (C (T (C (T h11 (C (S h10) h9)) h8) (S h6)) (R v3))) h4)) (S (h v3 v2 v3))

@[equational_result]
theorem Equation2552_implies_Equation3737 (G: Type _) [Magma G] (h: Equation2552 G) : Equation3737 G := fun x y z =>
  let v0 := M y z
  let v1 := M (M x z) v0
  have h2 := R v0
  have h3 := R x
  let v4 := M x (M (M x v0) y)
  have h5 := h z v4 v0
  have h6 := R z
  have h7 := h y x v0
  have h8 := R v4
  let v9 := M x y
  have h10 := R v9
  have h11 := S h7
  have h12 := S (h x x v9)
  let v13 := M x (M (M x v9) x)
  T (T (h v9 x v0) (C (C h3 (T (T (T (T (T (C (C h3 (C (T (h y v13 v9) (C (T (C (R v13) (C h12 (R y))) h12) h10)) (T h5 (C (T (C h8 (C h11 h6)) h11) h2)))) h10) (S (h (M y v0) x v9))) (C (T h7 (C h8 (C h7 h6))) h2)) (S h5)) (h z x v1)) (C (C h3 (S (h v0 x z))) (R v1)))) h2)) (S (h v1 x v0))

@[equational_result]
theorem Equation2718_implies_Equation2 (G: Type _) [Magma G] (h: Equation2718 G) : Equation2 G := fun x y =>
  have h0 := h y x x
  have h1 := S h0
  have h2 := R x
  let v3 := M x y
  let v4 := M v3 v3
  have h5 := h v4 x x
  let v6 := M y x
  let v7 := M x x
  let v8 := M v7 v6
  have h9 := C (T (C (S (h v8 x x)) h1) (S (h x x y))) (R v4)
  let v10 := M x v8
  have h11 := h x (M v10 v10) v4
  let v12 := M v6 v7
  let v13 := M v7 v7
  let v14 := M x v13
  have h15 := R v12
  have h16 := h x y x
  let v17 := M x v4
  T (T h16 (C (T (T (h v12 y x) (C (C (T (T (T (C (T h0 (C h5 h16)) h15) (S (h x (M v17 v17) v12))) h11) h9) (T (T (T (C (T (h x x x) (C (h v13 x x) h16)) h15) (S (h x (M v14 v14) v12))) h11) h9)) h2)) (S h5)) h2)) h1

@[equational_result]
theorem Equation3211_implies_Equation684 (G: Type _) [Magma G] (h: Equation3211 G) : Equation684 G := fun x y z =>
  let v0 := M y z
  let v1 := M v0 z
  let v2 := M x v1
  have h3 := S (h y z y)
  have h4 := R z
  have h5 := R y
  have h6 := S (h z v0 v1)
  have h7 := R v0
  have h8 := R v1
  have h9 := C (T (h v1 z v1) (C (C (C (T (C (h z v0 z) h8) (S (h v0 v1 z))) h8) h8) h4)) h7
  have h10 := C (T h9 h6) h5
  have h11 := h v0 y z
  T (h x v2 v1) (C (T (T (S (h v1 x v1)) (C (T h11 (C (T (T (T h9 h6) (h z y y)) (C (T (T (C (T (C (C (T (T (h y v0 z) (C (S (h z y z)) h7)) (C (T (h z v0 y) (C (T (C (C (C (T h11 h10) h5) h5) h4) h3) h7)) h7)) h5) h5) (S (h y y v0))) h4) h11) h10) h5)) h5)) h4)) h3) (R v2))

@[equational_result]
theorem Equation1507_implies_Equation14 (G: Type _) [Magma G] (h: Equation1507 G) : Equation14 G := fun x y =>
  let v0 := M x y
  have h1 := S (h y x v0)
  let v2 := M v0 x
  let v3 := M y v0
  let v4 := M y v3
  have h5 := R y
  let v6 := M y v4
  let v7 := M v3 (M v3 v0)
  have h8 := R v7
  have h9 := h v0 y v3
  let v10 := M v3 (M v3 y)
  let v11 := M x (M x v3)
  have h12 := R v11
  let v13 := M v3 x
  T (T (T (T (T (T (h x v3 v3) (C (T (h v13 v3 x) (C (T (T (h (M v3 v13) v0 v3) (C (S (h y x v3)) h8)) (C h5 (T (h v7 v2 v0) (C (S (h x v0 v3)) h1)))) h12)) (R (M v3 (M v3 v3))))) (S (h v11 v3 v3))) (h v11 v0 v3)) (C (T (T (T (C h9 h12) (S (h v10 v3 x))) (h v10 v3 y)) (C (S h9) (R v6))) h8)) (S (h v6 v0 v3))) (C h5 (T (h v4 v2 v0) (C (S (h x v0 y)) h1)))

@[equational_result]
theorem Equation1507_implies_Equation1152 (G: Type _) [Magma G] (h: Equation1507 G) : Equation1152 G := fun x y z =>
  let v0 := M x y
  let v1 := M z v0
  let v2 := M v1 z
  let v3 := M y v2
  let v4 := M v0 (M v0 v0)
  let v5 := M v2 v1
  let v6 := M x v0
  have h7 := h y x v3
  let v8 := M v3 (M v3 x)
  let v9 := M y x
  T (T (h x y y) (C (T (T (T (T (T (h v9 y x) (C (T (T (T (T (h (M y v9) v0 x) (C (T (S (h y x y)) h7) (R (M x v6)))) (S (h v8 v0 x))) (h v8 v0 v0)) (C (S h7) (R v4))) (R v6))) (S (h v4 y x))) (h v4 v5 v4)) (C (T (T (C (R v5) (T (T (h v4 (M v0 x) v0) (C (S (h x v0 v0)) (S (h y x v0)))) (h v0 z v1))) (S (h v1 v2 v1))) (h v1 v2 y)) (R (M v4 (M v4 v5))))) (S (h (M y v3) v5 v4))) (R (M y (M y y))))) (S (h v3 y y))

@[equational_result]
theorem Equation1561_implies_Equation1876 (G: Type _) [Magma G] (h: Equation1561 G) : Equation1876 G := fun x y z =>
  let v0 := M y z
  let v1 := M x v0
  let v2 := M z y
  let v3 := M v1 v2
  have h4 := h v3 x v1
  have h5 := S h4
  have h6 := h x z y
  have h7 := S h6
  have h8 := R v1
  have h9 := R v3
  have h10 := h v1 v1 v2
  have h11 := h v1 y z
  have h12 := h v0 v2 v1
  have h13 := C (T h12 (C h7 (S h11))) (T h10 (C h9 (C h8 h7)))
  have h14 := R v0
  T (T (T h6 (C (T (T (h v2 v0 v1) (C (T (T (T h13 h5) (h v3 x v0)) (C h8 (T (C h9 (C h14 h6)) (S (h v0 v1 v2))))) (T (T (S (h v1 z y)) h11) (C h14 (T h4 (C (T (C h6 h11) (S h12)) (T (C h9 (C h8 h6)) (S h10)))))))) (S (h v0 v1 v0))) h8)) h13) h5

@[equational_result]
theorem Equation2958_implies_Equation1504 (G: Type _) [Magma G] (h: Equation2958 G) : Equation1504 G := fun x y z =>
  let v0 := M y z
  let v1 := M z v0
  have h2 := R z
  let v3 := M v1 z
  have h4 := S (h v1 x v1)
  let v5 := M (M x (M x v1)) v1
  have h6 := R v0
  have h7 := S (h z x z)
  let v8 := M (M x (M x z)) z
  let v9 := M (M x (M x y)) y
  have h10 := h y x y
  let v11 := M (M y x) v1
  have h12 := S (h y v11 y)
  let v13 := M (M v11 (M v11 y)) y
  T (h x v13 y) (C (C (T (C (R v13) h12) h12) (R x)) (T (T (h y y z) (C (T (T (T (T (T (C (C (T h10 (C (R v9) h10)) h6) (R y)) (S (h v0 v9 y))) (h v0 v8 z)) (C (C (T (C (R v8) h7) h7) h6) h2)) (h v3 v5 v1)) (C (C (T (C (R v5) h4) h4) (R v3)) (R v1))) h2)) (S (h v1 v1 z))))

@[equational_result]
theorem Equation2958_implies_Equation4450 (G: Type _) [Magma G] (h: Equation2958 G) : Equation4450 G := fun x y z =>
  let v0 := M (M x (M x y)) y
  let v1 := M y z
  have h2 := R y
  have h3 := h y x y
  have h4 := R v0
  have h5 := R x
  let v6 := M y x
  have h7 := R v6
  have h8 := S h3
  let v9 := M (M x (M x x)) x
  have h10 := h x x x
  let v11 := M x v6
  let v12 := M (M x (M x v11)) v11
  let v13 := M v11 x
  have h14 := h v11 x v11
  T (T (T (T (T (h v11 v11 x) (C (T (T (T (C (C (T h14 (C (R v12) h14)) (R v13)) (R v11)) (S (h v13 v12 v11))) (C (C (T h10 (C (R v9) h10)) h7) h5)) (S (h v6 v9 x))) h5)) (C (T (h v6 v0 y) (C (C (T (C h4 h8) h8) h7) h2)) h5)) (S (h y y x))) (h y y z)) (C (T (C (C (T h3 (C h4 h3)) (R v1)) h2) (S (h v1 v0 y))) (R z))

@[equational_result]
theorem Equation3566_implies_Equation333 (G: Type _) [Magma G] (h: Equation3566 G) : Equation333 G := fun x y =>
  let v0 := M x y
  have h1 := h x y v0
  have h2 := R y
  have h3 := h v0 x y
  have h4 := S h3
  have h5 := R x
  have h6 := h y v0 v0
  have h7 := h (M v0 y) v0 y
  have h8 := R v0
  have h9 := h y y x
  have h10 := h y v0 y
  have h11 := C (T (C h8 (T (T h10 (C h8 (C h9 h8))) (S h7))) (S h6)) h5
  have h12 := C h5 h11
  have h13 := C (T h6 (C h8 (T (T h7 (C h8 (C (S h9) h8))) (S h10)))) h5
  have h14 := h (M y v0) x v0
  have h15 := C h5 h13
  have h16 := C (T (T (C h5 (T (T (T h3 h15) (S h14)) h13)) h12) h4) h2
  T (T h1 (C h2 (C (T (T h3 h15) (C h5 (T (T (T h11 h14) h12) h4))) h2))) (C h2 (T (T (T h16 (h (M v0 x) y x)) (C h2 h16)) (S h1)))

@[equational_result]
theorem Equation3791_implies_Equation4421 (G: Type _) [Magma G] (h: Equation3791 G) : Equation4421 G := fun x y z =>
  let v0 := M z y
  let v1 := M x y
  have h2 := R v1
  have h3 := h v0 z y
  have h4 := S h3
  let v5 := M v0 z
  let v6 := M y v0
  have h7 := h y v0 z
  have h8 := h z y v0
  have h9 := T (T (T h3 (h v6 v0 v0)) (C (T (T (C h8 h7) (S (h v6 v0 v5))) h4) (R (M v0 v0)))) (S (h z v0 v0))
  T (T (T (T (h x v1 v5) (h (M v5 x) (M v1 v5) (M x v1))) (C (T (S (h v1 v5 x)) (C h2 h9)) (T (T (S (h v5 x v1)) (h v5 x y)) (C (T (T (T (T (h y v5 y) (C (T (T (h y y v0) (C (R (M v0 y)) (T (T h7 (h v0 v5 v6)) (C h4 (S h8))))) (S (h y v5 v0))) (R (M v5 y)))) (S (h v5 v5 y))) (C (R v5) h9)) (S (h z z v0))) h2)))) (S (h (M z v0) (M z z) v1))) (S (h v0 z z))

@[equational_result]
theorem Equation3940_implies_Equation3331 (G: Type _) [Magma G] (h: Equation3940 G) : Equation3331 G := fun x y z =>
  let v0 := M y z
  let v1 := M z v0
  let v2 := M x v1
  let v3 := M x y
  let v4 := M v3 v2
  have h5 := R z
  let v6 := M z v1
  have h7 := R v6
  have h8 := h z v0 z
  have h9 := R x
  let v10 := M x (M v1 y)
  let v11 := M v3 v3
  T (T (T (T (h x y v3) (h (M x (M v3 y)) v3 v3)) (C (T (T (T (C (C h9 (h v3 y x)) (R v11)) (S (h x x v11))) (h x x v4)) (C (C h9 (T (T (T (S (h v3 v1 x)) (h v3 v1 z)) (C (T (T (T (T (T (C (T (h x y v1) (C (R v10) h8)) h7) (S (h v10 z v6))) (C (C h9 (S (h z z y))) h5)) (S (h x z z))) (h x z v6)) (C (C h9 (S h8)) h7)) h5)) (S (h v2 v1 z)))) (R v4))) (R v3))) (S (h (M x (M v2 v1)) v2 v3))) (S (h x v1 v2))

@[equational_result]
theorem Equation4197_implies_Equation3588 (G: Type _) [Magma G] (h: Equation4197 G) : Equation3588 G := fun x y z =>
  let v0 := M x y
  let v1 := M v0 z
  let v2 := M z v1
  have h3 := R v2
  have h4 := R v0
  have h5 := R v1
  let v6 := M z v0
  have h7 := R z
  T (T (T (T (h x y v0) (h (M (M v0 x) y) v0 v2)) (C (C (C h3 (T (T (T (C (T (h v0 x v0) (C (S (h y v0 x)) h4)) (R y)) (S (h v0 v0 y))) (h v0 v0 v1)) (C (T (T (T (S (h z v0 v0)) (h z v0 v2)) (C (T (C (T (T (T (h v2 z v2) (C (C (C h3 (T (T (T (h z v1 z) (h (M (M z z) v1) z v2)) (C (C (C h3 (T (C (h z z v0) h5) (S (h z v0 v1)))) h7) h3)) (S (h v6 z v2)))) h7) h3)) (S (h (M v6 z) z v2))) (S (h v0 z z))) h4) (h v1 v0 z)) h3)) (S (h v0 z v2))) h5))) h4) h3)) (S (h (M v1 v1) v0 v2))) (S (h z v1 v0))

@[equational_result]
theorem Equation1304_implies_Equation1943 (G: Type _) [Magma G] (h: Equation1304 G) : Equation1943 G := fun x y z =>
  let v0 := M x z
  have h1 := R v0
  let v2 := M y z
  have h3 := R v2
  let v4 := M (M (M y x) x) y
  have h5 := h y z v4
  have h6 := R z
  have h7 := R v4
  have h8 := h y y x
  have h9 := C (C (T (C h6 (C (T h8 (C h8 h7)) h6)) (S h5)) h3) h1
  have h10 := S h8
  let v11 := M y v2
  let v12 := M (M (M v11 x) x) v11
  have h13 := h v11 v11 x
  have h14 := S (h x x x)
  let v15 := M (M (M x x) x) x
  T (T (T (h x z v15) (C h6 (C (T (C h14 (R v15)) h14) h6))) (C (T (T (T (T (h z v0 v2) (C h1 h9)) (C h1 (C (T h13 (C h13 (R v12))) h1))) (S (h v11 v0 v12))) (C (T h5 (C h6 (C (T (C h10 h7) h10) h6))) h3)) h1)) h9

@[equational_result]
theorem Equation1359_implies_Equation2 (G: Type _) [Magma G] (h: Equation1359 G) : Equation2 G := fun x y =>
  have h0 := R x
  have h1 := h y x x
  have h2 := C h1 h0
  let v3 := M y x
  have h4 := h v3 x y
  let v5 := M (M (M x v3) x) x
  have h6 := R y
  have h7 := h x x y
  let v8 := M (M v3 y) y
  T (T (h x y y) (C h6 (T (T (h v8 y y) (C h6 (T (T (T (h (M (M (M y v8) y) y) x x) (C h0 (C (C (T (T (S (h v8 x y)) (h v8 x x)) (C h0 (C (C (S h7) h0) h0))) h0) h0))) (S (h (M (M x x) x) x x))) (C (T (T (C h0 (T (T (T (T (T h7 (C h0 (C (C (h v3 y x) h6) h6))) (S (h v5 x y))) (h v5 x x)) (C h0 (C (T (C (T (S (h v3 x x)) h2) h0) (C (T (C (S h1) h0) h4) h0)) h0))) (S (h (M (M (M y v3) y) y) x x)))) (S h4)) h2) h0)))) (S (h (M (M (M x y) x) x) y x))))) (S (h y y x))

@[equational_result]
theorem Equation1507_implies_Equation4544 (G: Type _) [Magma G] (h: Equation1507 G) : Equation4544 G := fun x y z =>
  let v0 := M z y
  have h1 := R (M v0 (M v0 z))
  let v2 := M y z
  let v3 := M x v2
  let v4 := M x v3
  have h5 := h z y y
  let v6 := M y (M y y)
  let v7 := M y (M y v2)
  let v8 := M v2 x
  let v9 := M x v4
  T (T (T (T (T (C (h x v3 x) (h v2 x v3)) (S (h v9 (M v3 x) v3))) (h v9 v2 v2)) (C (T (C (h v2 x v2) (R v9)) (S (h (M v2 v8) v3 x))) (R (M v2 (M v2 v2))))) (S (h v8 v2 v2))) (C (T (T (T (T (T (C (h y v2 y) (h z y v2)) (S (h v7 (M v2 y) v2))) (h v7 z v0)) (C (T (C h5 (R v7)) (S (h v6 v2 y))) h1)) (C (T (T (h v6 v2 x) (C (T (S h5) (h z y z)) (R v4))) (S (h (M z v0) v2 x))) h1)) (S (h v0 z v0))) (R x))

@[equational_result]
theorem Equation1726_implies_Equation3500 (G: Type _) [Magma G] (h: Equation1726 G) : Equation3500 G := fun x y z =>
  let v0 := M z z
  let v1 := M v0 y
  let v2 := M y v1
  let v3 := M v1 y
  let v4 := M x x
  let v5 := M y y
  have h6 := S (h v5 v4 v3)
  have h7 := R v3
  have h8 := C (h v0 y y) h7
  have h9 := h v0 z y
  have h10 := S (h v0 v0 v3)
  have h11 := C h9 h7
  have h12 := R (M v0 v0)
  have h13 := R (M v4 v4)
  have h14 := R v5
  T (T (h v4 y v4) (C h14 (T (T (T (C h13 (T (T (T (T (h v4 v0 v3) (C h12 (T (C (S (h v0 x y)) h7) h11))) h10) h9) h8)) h6) (h v5 v2 v1)) (C (R (M v2 v2)) (C (T (C h14 (C (T (T (h v0 v4 v0) (C h13 (T (T (T (C h12 (T h9 h11)) h10) h9) h8))) h6) (R y))) (S (h y y y))) (R v1)))))) (S (h v2 y v2))

@[equational_result]
theorem Equation2958_implies_Equation2335 (G: Type _) [Magma G] (h: Equation2958 G) : Equation2335 G := fun x y z =>
  let v0 := M x z
  let v1 := M (M x (M x v0)) v0
  let v2 := M y (M y v0)
  let v3 := M v2 z
  have h4 := R v3
  have h5 := h v0 x v0
  have h6 := R z
  have h7 := S (h v3 x v3)
  let v8 := M (M x (M x v3)) v3
  let v9 := M (M x (M x x)) x
  have h10 := R x
  have h11 := h x x x
  have h12 := S (h v0 z v0)
  let v13 := M (M z (M z v0)) v0
  T (T (h x v13 v0) (C (T (T (T (T (T (C (T (C (R v13) h12) h12) h10) (C (C (T h11 (C (R v9) h11)) h6) h10)) (S (h z v9 x))) (h z v8 v3)) (C (T (T (C (T (C (R v8) h7) h7) h6) (C (h v3 y v0) h6)) (S (h v0 v2 z))) h4)) (C (T h5 (C (R v1) h5)) h4)) (R v0))) (S (h v3 v1 v0))

@[equational_result]
theorem Equation3567_implies_Equation3526 (G: Type _) [Magma G] (h: Equation3567 G) : Equation3526 G := fun x y z =>
  have h0 := R z
  have h1 := h y z x
  have h2 := C (S h1) h0
  have h3 := R x
  let v4 := M (M x y) x
  let v5 := M y z
  let v6 := M (M y y) y
  let v7 := M (M v5 x) v5
  let v8 := M v5 z
  let v9 := M v8 v5
  let v10 := M v5 y
  have h11 := R v10
  have h12 := T (T (T h1 (h z v4 v5)) (h v4 v9 z)) (C (R v9) h2)
  T (T (T (T (T (T (T (T (h x y v5) (h y v7 v5)) (C (R v7) (T (T (T (T (T (C h11 h12) (S (h v5 v10 v8))) (C h12 h11)) (S (h z (M v9 v8) y))) (S (h v5 z v8))) (C (h y z y) h0)))) (S (h v6 v7 z))) (S (h x v6 v5))) (C h3 (C (h y y x) (R y)))) (S (h v4 x y))) (h v4 x z)) (C h3 h2)

@[equational_result]
theorem Equation684_implies_Equation2399 (G: Type _) [Magma G] (h: Equation684 G) : Equation2399 G := fun x y z =>
  let v0 := M z x
  let v1 := M z v0
  let v2 := M y v1
  let v3 := M v2 y
  have h4 := S (h v3 v3 x)
  let v5 := M v3 (M (M v3 x) x)
  let v6 := M y v3
  have h7 := S (h y y x)
  let v8 := M y (M (M y x) x)
  have h9 := R v2
  have h10 := R y
  let v11 := M v1 (M (M v1 x) x)
  have h12 := h v1 v1 x
  let v13 := M x (M (M x x) x)
  have h14 := h x x x
  T (T (T (T (h x z x) (C (R z) (T (C (R x) (C (R v0) (T h14 (C h14 (R v13))))) (S (h v0 x v13))))) (h v1 y v1)) (C h10 (T (T (T (T (T (C (R v1) (C h9 (T h12 (C h12 (R v11))))) (S (h v2 v1 v11))) (h v2 y v8)) (C h10 (C h9 (T (C h7 (R v8)) h7)))) (h v6 v3 v5)) (C (R v3) (C (R v6) (T (C h4 (R v5)) h4)))))) (S (h v3 y v3))

@[equational_result]
theorem Equation1492_implies_Equation2135 (G: Type _) [Magma G] (h: Equation1492 G) : Equation2135 G := fun x y =>
  let v0 := M x y
  let v1 := M y y
  let v2 := M v1 y
  let v3 := M v2 v0
  let v4 := M v3 v3
  let v5 := M v3 v4
  have h6 := R (M v0 (M v0 v0))
  let v7 := M v2 (M v2 v2)
  let v8 := M y v1
  have h9 := R v8
  let v10 := M v1 (M v1 v1)
  have h11 := h y y
  let v12 := M x x
  have h13 := T (T (T (h (M x v12) v0) (C (S (h y x)) h6)) (C (T (T (T (T h11 (C (T (h v1 v2) (C (T (C (R v2) (T (T (h v1 y) (C (T (h v8 v1) (C (S h11) (R v10))) h9)) (S (h v10 y)))) (S (h y v1))) (R v7))) h9)) (S (h v7 y))) (h v7 v3)) (C (S (h v0 v2)) (R v5))) h6)) (S (h v5 v0))
  T (T (h x x) (C (T (T (h v12 x) (C h13 h13)) (S (h v4 v3))) h13)) (S (h v3 v3))

@[equational_result]
theorem Equation1537_implies_Equation1101 (G: Type _) [Magma G] (h: Equation1537 G) : Equation1101 G := fun x y z =>
  let v0 := M z z
  let v1 := M x v0
  let v2 := M y (M v1 y)
  have h3 := S (h v0 x z)
  have h4 := h z z z
  have h5 := R v0
  have h6 := R z
  have h7 := C h6 (T (h z z v0) (C h5 (S h4)))
  let v8 := M v2 v2
  let v9 := M x x
  have h10 := R v9
  let v11 := M v1 v1
  T (T (T (T (T (h x v0 x) (C (R (M v0 v0)) (T (T (C (R x) (T (T (h v9 x z) (C h10 (T (C h6 (T (C h10 h4) (S (h z x v0)))) h7))) h3)) (h v1 z v1)) (C h5 (C (R v1) (T (T (h v11 x z) (C h10 (T (C h6 (T (C (R v11) h4) (S (h z v1 v0)))) h7))) h3)))))) (S (h v1 v0 v0))) (h v1 z y)) (C h5 (T (h v2 z v2) (C h5 (C (R v2) (T (T (h v8 x z) (C h10 (T (C h6 (T (C (R v8) h4) (S (h z v2 v0)))) h7))) h3)))))) (S (h v2 z v0))

@[equational_result]
theorem Equation2196_implies_Equation684 (G: Type _) [Magma G] (h: Equation2196 G) : Equation684 G := fun x y z =>
  let v0 := M (M y z) z
  let v1 := M x v0
  let v2 := M y v1
  have h3 := h v1 v2 v1
  have h4 := h y v1 v2
  let v5 := M (M v2 v1) v1
  have h6 := h v5 (M v1 v2) v2
  let v7 := M v2 y
  let v8 := M v7 y
  let v9 := M v1 y
  let v10 := M (M y v0) v0
  have h11 := S (h v0 y z)
  let v12 := M v0 y
  T (T (T (T (T (h x v0 v12) (C (T (C h11 (R v12)) h11) (R v1))) (C (R v0) (T (T (T (T (h v1 y v0) (R (M v10 v9))) (C (R v10) (T (T (h v9 y x) (C (R (M (M y x) x)) (T (h (M v9 y) v2 y) (C (R v8) (S (h y v1 y)))))) (S (h v8 y x))))) (S (h v7 y v0))) (C (T (C h4 h3) (S h6)) (R y))))) (S (h v5 y z))) h6) (C (S h4) (S h3))

@[equational_result]
theorem Equation2522_implies_Equation2199 (G: Type _) [Magma G] (h: Equation2522 G) : Equation2199 G := fun x y z =>
  let v0 := M y x
  let v1 := M (M y z) z
  let v2 := M v1 v0
  have h3 := h v2 v1 v2
  have h4 := R v1
  have h5 := R x
  have h6 := h v1 y v1
  have h7 := R y
  have h8 := h y v1 z
  have h9 := h y x v0
  let v10 := M x (M (M y v0) v0)
  have h11 := h x v1 y
  T (T h11 (C (T (T (h (M v1 (M (M x y) y)) x v1) (C (C h5 (T (T (T (T (T (T (C (S h11) h4) (h (M x v1) x x)) (C (T (C h5 (C (S (h y x z)) h5)) (C h5 (C h9 h5))) h5)) (S (h v10 x x))) (h v10 v1 x)) (C (C h4 (C (S h9) h5)) (T h6 (C (C h7 (S h8)) h7)))) (C h3 (T (C (C h7 h8) h7) (S h6))))) h5)) (S (h (M v1 (M (M v2 v2) v2)) x v1))) h4)) (S h3)

@[equational_result]
theorem Equation3591_implies_Equation4200 (G: Type _) [Magma G] (h: Equation3591 G) : Equation4200 G := fun x y z =>
  let v0 := M z x
  let v1 := M v0 z
  let v2 := M v1 y
  let v3 := M x y
  have h4 := R y
  have h5 := h v0 z z
  let v6 := M v1 z
  have h7 := R v6
  have h8 := R z
  let v9 := M (M x v1) y
  let v10 := M v2 v3
  let v11 := M v3 v3
  T (T (T (T (h x y v3) (h v3 (M (M x v3) y) v3)) (C (R v3) (T (T (T (C (R v11) (C (h x v3 y) h4)) (S (h y y v11))) (h y y v10)) (C (R v10) (C (T (T (T (S (h v1 v3 y)) (h v1 v3 z)) (C h8 (T (T (T (T (T (C h7 (T (h x y v1) (C h5 (R v9)))) (S (h z v9 v6))) (C h8 (C (S (h z z x)) h4))) (S (h z y z))) (h z y v6)) (C h7 (C (S h5) h4))))) (S (h v1 v2 z))) h4))))) (S (h v2 (M (M v1 v2) y) v3))) (S (h v1 y v2))

@[equational_result]
theorem Equation3804_implies_Equation4182 (G: Type _) [Magma G] (h: Equation3804 G) : Equation4182 G := fun x y z =>
  let v0 := M y z
  let v1 := M v0 v0
  have h2 := h y z z
  let v3 := M v0 x
  have h4 := h y z x
  have h5 := h y x z
  have h6 := h x z y
  have h7 := S h6
  let v8 := M x y
  let v9 := M z x
  have h10 := h v9 v8 v0
  let v11 := M v8 v8
  have h12 := R v11
  have h13 := h x y y
  T (T (T (T (T (T (T h13 (h (M y y) v8 v8)) (C h12 (S h13))) (h v11 v8 v0)) (C h7 (T (T (T (T (C h12 (T (T h4 (C h6 h5)) (S h10))) (S (h v9 v8 v8))) h10) (C h7 (S h5))) (S h4)))) (h (M x z) v0 v3)) (C (T (C (R v3) (T (T h2 (h (M z z) v0 v0)) (C (R v1) (S h2)))) (S (h v1 x v0))) (T (S (h v0 z x)) (h v0 z v0)))) (S (h (M v0 z) x v1))

@[equational_result]
theorem Equation572_implies_Equation14 (G: Type _) [Magma G] (h: Equation572 G) : Equation14 G := fun x y =>
  let v0 := M x y
  let v1 := M y v0
  have h2 := S (h v1 v0 v0)
  have h3 := h v0 v1 v0
  have h4 := S h3
  have h5 := h y v0 v0
  have h6 := h x y y
  have h7 := S h6
  have h8 := R y
  have h9 := R v1
  have h10 := h y v1 y
  have h11 := C h9 (T (T (C (R x) (T h3 (C h9 (T (T (S h5) h10) (C h9 (C h8 h7)))))) (S (h y x v1))) h5)
  have h12 := R v0
  have h13 := h x v0 v1
  have h14 := C h12 (T h13 (C h12 (C h9 (T h11 h4))))
  have h15 := C h12 h7
  have h16 := h y v0 y
  T (T h13 (C h12 (T (T (T (T (T (C h9 (T (T (T h11 h4) (h v0 y y)) (C h8 (T (C h8 (C h8 (T (C h12 (T (T h16 h15) h14)) h2))) h7)))) (C h9 (C h8 h6))) (S h10)) h16) h15) h14))) h2

@[equational_result]
theorem Equation684_implies_Equation1320 (G: Type _) [Magma G] (h: Equation684 G) : Equation1320 G := fun x y z =>
  let v0 := M y x
  let v1 := M v0 (M (M v0 y) y)
  let v2 := M (M v0 z) z
  let v3 := M y v2
  have h4 := h v0 v0 y
  have h5 := R v3
  have h6 := R y
  have h7 := S (h v3 v3 x)
  let v8 := M v3 (M (M v3 x) x)
  let v9 := M x (M (M x x) x)
  have h10 := h x x x
  have h11 := R x
  have h12 := S (h v0 v0 z)
  let v13 := M v0 v2
  T (T (h x v0 v13) (C (R v0) (T (T (T (T (T (C h11 (T (C h12 (R v13)) h12)) (C h11 (C h6 (T h10 (C h10 (R v9)))))) (S (h y x v9))) (h y v3 v8)) (C h5 (T (T (C h6 (T (C h7 (R v8)) h7)) (C h6 (h v3 v0 z))) (S (h v0 y v2))))) (C h5 (T h4 (C h4 (R v1))))))) (S (h v3 v0 v1))

@[equational_result]
theorem Equation3159_implies_Equation2290 (G: Type _) [Magma G] (h: Equation3159 G) : Equation2290 G := fun x y =>
  let v0 := M x x
  have h1 := h x v0 x
  have h2 := S h1
  have h3 := R x
  have h4 := h x x v0
  have h5 := T (C h4 h3) h2
  let v6 := M x v0
  have h7 := R v6
  let v8 := M y v6
  let v9 := M v8 x
  have h10 := R y
  have h11 := R v9
  have h12 := R v8
  have h13 := T (C (T (h y v9 v9) (C (C (C (T (C (T (h v9 v8 v8) (C (C (C (T (C (T (h v8 v6 v6) (C (C (C (T (C (T (h v6 x x) (C (T (C (C h5 h3) h7) (R (M v0 v6))) h7)) h7) (S (h v6 x v6))) h7) h12) h12)) h12) (S (h v8 v6 v8))) h12) h11) h11)) h11) (S (h v9 v8 v9))) h11) h10) h10)) h10) (S (h y v9 y))
  have h14 := S h4
  T (T (T (T h1 (C h14 (T h1 (C h14 h3)))) (h v6 y y)) (C (C (C h13 h10) h7) h7)) (C (C h13 h7) (T (C h4 h5) h2))

@[equational_result]
theorem Equation3620_implies_Equation4200 (G: Type _) [Magma G] (h: Equation3620 G) : Equation4200 G := fun x y z =>
  let v0 := M z x
  let v1 := M v0 z
  have h2 := R z
  let v3 := M v1 y
  let v4 := M v3 x
  have h5 := h v4 z v0
  have h6 := S h5
  have h7 := h x y v1
  have h8 := R v0
  let v9 := M x y
  have h10 := h v9 x z
  have h11 := R x
  have h12 := h x y x
  have h13 := S h12
  have h14 := R v1
  let v15 := M v9 x
  T (T (T h12 (h x v15 v1)) (C h14 (T (T (T (T (C (T (T (h v1 v15 x) (C h11 (T (T (T (T (C h13 h14) (h v9 v1 z)) (C h2 (T (C (S (h z x z)) h7) h6))) (C h2 (T h5 (C h8 (S h7))))) (S h10)))) h13) h11) h10) (C h2 (T (C h8 h7) h6))) (h z (M v4 z) v3)) (C (R v3) (C (S (h z x v3)) h2))))) (S (h v1 y v1))

@[equational_result]
theorem Equation508_implies_Equation1746 (G: Type _) [Magma G] (h: Equation508 G) : Equation1746 G := fun x y z =>
  let v0 := M z z
  have h1 := h x x v0
  have h2 := h v0 x z
  let v3 := M y y
  let v4 := M v3 (M v0 x)
  have h5 := h v3 v4 y
  have h6 := h v3 v3 v3
  have h7 := h v3 v3 y
  have h8 := R v3
  have h9 := R v4
  have h10 := S (h v3 z y)
  have h11 := R z
  have h12 := C h11 (T (T (h z z v3) (C h11 h10)) (C h11 (T h6 (C h8 (S h7)))))
  have h13 := R v0
  have h14 := R x
  T (h x v0 x) (C (T h12 h10) (C h13 (T (C h14 (T (T (C h14 (T (T h1 (C h14 (S h2))) (C h14 (T (h v0 v0 v0) (C h13 (T (T (T (T (S (h v0 v0 z)) h12) h10) h5) (C h9 (T (C h9 (T (T (C h8 h7) (S h6)) h5)) (S (h v4 v4 v3)))))))))) (S (h v0 x v4))) h2)) (S h1))))

@[equational_result]
theorem Equation2180_implies_Equation2992 (G: Type _) [Magma G] (h: Equation2180 G) : Equation2992 G := fun x y z =>
  let v0 := M z y
  let v1 := M y v0
  let v2 := M v1 x
  let v3 := M v2 z
  have h4 := R v0
  have h5 := h y y v0
  have h6 := h z v1 y
  have h7 := C (T h6 (C (S h5) h4)) (R x)
  let v8 := M x v3
  let v9 := M v8 x
  have h10 := R (M (M x v2) x)
  T (T (h x z v3) (C (R (M (M z v3) z)) (T (h v8 v0 x) (C (T (T (T (T (h (M (M v0 x) v0) x v2) (C h10 (S (h v1 v0 x)))) (C h10 (h v1 v1 x))) (S (h (M v2 v1) x v2))) (C (R v2) (T (C h5 h4) (S h6)))) (T (T (h v9 x v2) (C h10 (T (T (T (C (R v9) (T (h v2 v0 z) (C (S (h z z y)) (R v3)))) (S (h z x v3))) (h z z x)) (C (C h7 (R z)) h7)))) (S (h v3 x v2))))))) (S (h v3 z v3))

@[equational_result]
theorem Equation492_implies_Equation4358 (G: Type _) [Magma G] (h: Equation492 G) : Equation4358 G := fun x y z =>
  let v0 := M z y
  let v1 := M y z
  have h2 := S (h y v1 v0)
  let v3 := M x v1
  have h4 := R v0
  have h5 := R z
  have h6 := R y
  have h7 := C h6 (T (C h5 (C h4 (C h4 (T (h y v0 z) (C h4 (S (h z y z))))))) (S (h v0 z v0)))
  have h8 := h z y v0
  have h9 := R v3
  have h10 := R x
  have h11 := R v1
  have h12 := C h6 (T (h v0 v0 v1) (C h4 (C h4 (T (C h11 (C h11 (T (h v0 x v3) (C h10 (T (C h4 (C h9 (T (T (C h9 (h x v1 x)) (S (h v1 v3 x))) (C h6 (T h8 h7))))) (S (h v3 v0 y))))))) (S (h v1 v1 x))))))
  C h10 (T (h v1 z y) (C h5 (T (C h11 (T (T (T (T (C h6 (T (h v1 z v1) (C h5 (C h11 (C h11 (T (C h11 (T (T h8 h7) h12)) h2)))))) (S (h z y v1))) h8) h7) h12)) h2)))

