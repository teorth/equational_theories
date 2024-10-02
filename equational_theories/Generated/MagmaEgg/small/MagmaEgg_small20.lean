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
theorem Equation1293_implies_Equation572 (G: Type _) [Magma G] (h: Equation1293 G) : Equation572 G := fun x y z =>
  let v0 := M x y
  let v1 := M z v0
  let v2 := M z v1
  let v3 := M y v2
  have h4 := S (h y y y)
  let v5 := M (M (M y y) y) y
  have h6 := R v5
  let v7 := M (M v3 y) y
  have h8 := R v1
  let v9 := M (M (M v1 v1) x) x
  have h10 := h v1 v1 x
  have h11 := R y
  let v12 := M (M (M v0 v0) x) x
  have h13 := h x y v12
  have h14 := R v12
  have h15 := h v0 v0 x
  have h16 := S h15
  T (T (T (T h13 (C h11 (T (C h16 h14) h16))) (h (M y v0) y v1)) (C h11 (T (T (C (T (T (C (C (T (C h11 (T h15 (C h15 h14))) (S h13)) h11) h8) (C (R v0) (T h10 (C h10 (R v9))))) (S (h z v0 v9))) h8) (h v2 v7 v5)) (C (R v7) (T (C (T (C (S (h y v2 y)) h6) h4) h6) h4))))) (S (h v3 y y))

@[equational_result]
theorem Equation1304_implies_Equation2399 (G: Type _) [Magma G] (h: Equation1304 G) : Equation2399 G := fun x y z =>
  let v0 := M (M (M y x) x) y
  let v1 := M z x
  let v2 := M z v1
  have h3 := R v2
  have h4 := h y y x
  let v5 := M y v2
  have h6 := R v5
  let v7 := M (M (M v2 x) x) v2
  let v8 := M (M v5 v2) v2
  have h9 := R v8
  have h10 := h v2 v2 x
  have h11 := h y v2 v2
  have h12 := S (h v2 v2 z)
  let v13 := M (M (M v2 z) z) v2
  let v14 := M (M v1 x) z
  have h15 := R x
  have h16 := h z z x
  T (h x v5 v1) (C h6 (T (T (T (C (T (T (C (T (C h15 (C (T h16 (C h16 (R v14))) h15)) (S (h z x v14))) (R v1)) (h v2 v8 v13)) (C h9 (T (C (T (C h12 (R v13)) h12) h9) (S h11)))) h6) (C (T (C h9 (T h11 (C (T h10 (C h10 (R v7))) h9))) (S (h v2 v8 v7))) h6)) (C h3 (C (T h4 (C h4 (R v0))) h3))) (S (h y v2 v0))))

@[equational_result]
theorem Equation1761_implies_Equation2714 (G: Type _) [Magma G] (h: Equation1761 G) : Equation2714 G := fun x y z =>
  let v0 := M y z
  let v1 := M y x
  let v2 := M v1 v0
  let v3 := M v2 z
  have h4 := R v3
  have h5 := h y x v0
  have h6 := S h5
  let v7 := M x v0
  have h8 := h v7 v2 x
  have h9 := S h8
  have h10 := R x
  let v11 := M v2 x
  have h12 := R v11
  have h13 := C h12 (C h5 h10)
  have h14 := R v1
  have h15 := h v11 v1 v2
  have h16 := R v2
  have h17 := C h12 (C h6 h10)
  have h18 := R (M v1 v2)
  T (T (h x v0 v3) (C (R (M v0 v3)) (T (C (T (T h8 h17) (C (T h15 (C h18 (T (C (T h13 h9) h16) h6))) h14)) h4) (C (T (T (T (T (C (T (C h18 (T h5 (C (T h8 h17) h16))) (S h15)) h14) h13) h9) (h v7 v2 z)) (C h4 (C h6 (R z)))) h4)))) (S (h v3 v0 v3))

@[equational_result]
theorem Equation2552_implies_Equation3398 (G: Type _) [Magma G] (h: Equation2552 G) : Equation3398 G := fun x y z =>
  let v0 := M x z
  let v1 := M y v0
  have h2 := R v1
  let v3 := M x (M (M x v0) x)
  have h4 := R v0
  have h5 := h x x v0
  let v6 := M x (M (M x v1) y)
  have h7 := h v0 v6 v1
  have h8 := h y x v1
  have h9 := R v6
  let v10 := M x y
  have h11 := R v10
  have h12 := S h8
  have h13 := S (h x x v10)
  let v14 := M x (M (M x v10) x)
  have h15 := R x
  T (h v10 x v1) (C (T (T (C h15 (T (T (T (C (C h15 (C (T (h y v14 v10) (C (T (C (R v14) (C h13 (R y))) h13) h11)) (T h7 (C (T (C h9 (C h12 h4)) h12) h2)))) h11) (S (h (M y v1) x v10))) (C (T h8 (C h9 (C h8 h4))) h2)) (S h7))) (C (T h5 (C (R v3) (C h5 (R z)))) h4)) (S (h z v3 v0))) h2)

@[equational_result]
theorem Equation4176_implies_Equation3804 (G: Type _) [Magma G] (h: Equation4176 G) : Equation3804 G := fun x y z =>
  let v0 := M x y
  let v1 := M x z
  let v2 := M z y
  have h3 := R v0
  have h4 := R x
  have h5 := R z
  have h6 := h z x y
  have h7 := S h6
  have h8 := h y v0 z
  let v9 := M y v0
  have h10 := R v1
  have h11 := h z x z
  have h12 := h z v1 z
  T (T (h x y v0) (C (T (C (T (h y v0 v2) (C (S (h v2 x y)) (T (h z y v0) (C (T (C (T (T (T (T h8 (C (T h7 h11) h5)) (S h12)) (h z v1 x)) (C (T (T (T (C (T (C (T (h x z v1) (C (T (T (h (M z v1) x v1) (C (C (R (M x v1)) (T (T h12 (C (T (S h11) h6) h5)) (S h8))) h10)) (S (h v9 x v1))) h10)) h4) (S (h v1 v9 x))) h5) (S (h v9 x z))) (C (T h8 (C h7 h5)) h4)) (S (h z z x))) h4)) h5) (S (h x z z))) h3)))) h4) (S (h (M v1 v0) v2 x))) h3)) (S (h v2 v1 v0))

@[equational_result]
theorem Equation492_implies_Equation4450 (G: Type _) [Magma G] (h: Equation492 G) : Equation4450 G := fun x y z =>
  let v0 := M y z
  let v1 := M v0 z
  have h2 := h z v0 y
  have h3 := S h2
  have h4 := h y z y
  have h5 := S (h y y v0)
  have h6 := R v0
  have h7 := R y
  have h8 := C h7 (C h7 (C h6 (T h2 (C h6 (S h4)))))
  have h9 := C h6 (T (T h8 h5) h4)
  have h10 := R v1
  have h11 := h v0 v1 y
  let v12 := M y x
  have h13 := R v12
  T (T (T (T (C (R x) (T (h v12 y v12) (C h7 (C h13 (C h13 (T (C h13 (h y x y)) (S (h x v12 y)))))))) (S (h y x v12))) (h y z v0)) (C (R z) (T (T (T (C h7 (C h6 (T (h v1 v1 y) (C h10 (C h10 (T h8 h5)))))) (S (h v0 y v1))) h11) (C h10 (T (T (T (T h9 h3) (h z v1 v0)) (C h10 (S (h v0 z v0)))) (C h10 (T h11 (C h10 (T h9 h3))))))))) (S (h v1 z v1))

@[equational_result]
theorem Equation1943_implies_Equation1470 (G: Type _) [Magma G] (h: Equation1943 G) : Equation1470 G := fun x y z =>
  let v0 := M z y
  let v1 := M z v0
  let v2 := M x y
  let v3 := M v1 z
  have h4 := R v1
  have h5 := S (h z z y)
  have h6 := C h4 h5
  let v7 := M v2 v1
  let v8 := M v2 v7
  let v9 := M v2 v8
  have h10 := h v2 v2 v1
  let v11 := M v1 (M v1 v7)
  let v12 := M x (M x z)
  have h13 := R v12
  T (T (T (T (T (h x z y) (C h4 (T (h v2 v12 v1) (C (T (C h13 (T (C h13 (T (h v1 v1 v0) (C h6 h5))) (S (h v3 x z)))) (S (h v1 x z))) (R v7))))) (h v11 x v2)) (C (R (M x (M x v2))) (T (T (T (C (R v11) h10) (S (h v8 v1 v7))) (h v8 v2 v7)) (C (R v9) (S h10))))) (S (h v9 x v2))) (C (R v2) (T (T (h v8 v0 z) (C (R (M v0 (M v0 z))) (T (C (R v8) (T (h z v1 v0) (C h6 h4))) (S (h v3 v2 v1))))) (S (h v1 v0 z))))

@[equational_result]
theorem Equation1964_implies_Equation1774 (G: Type _) [Magma G] (h: Equation1964 G) : Equation1774 G := fun x y z =>
  let v0 := M y x
  let v1 := M v0 z
  let v2 := M y z
  let v3 := M v2 v1
  let v4 := M y v3
  have h5 := h z v2 v0
  have h6 := S h5
  let v7 := M v2 v0
  have h8 := h v7 v0 v3
  have h9 := S h8
  let v10 := M v0 v3
  have h11 := R v10
  have h12 := R v0
  have h13 := C (C h12 h5) h11
  have h14 := h v10 v3 v1
  have h15 := R (M v3 v1)
  have h16 := C (C h12 h6) h11
  have h17 := R v3
  have h18 := R v1
  T (T (h x v3 y) (C (C h17 (T (T (h v0 v3 v2) (C (T (C h17 (T (T h8 h16) (C h18 (T h14 (C (T (C h17 (T h13 h9)) h6) h15))))) (C h17 (T (T (T (T (C h18 (T (C (T h5 (C h17 (T h8 h16))) h15) (S h14))) h13) h9) (h v7 y v3)) (C (C (R y) h6) (R v4))))) (R (M v3 v2)))) (S (h v4 v3 v2)))) (R (M v3 y)))) (S (h v3 v3 y))

@[equational_result]
theorem Equation2349_implies_Equation2958 (G: Type _) [Magma G] (h: Equation2349 G) : Equation2958 G := fun x y z =>
  let v0 := M y (M y z)
  let v1 := M v0 x
  let v2 := M v1 z
  have h3 := R v2
  let v4 := M x (M x (M v2 v2))
  have h5 := R v1
  have h6 := h v2 x v2
  let v7 := M z (M z v2)
  let v8 := M x (M x (M z z))
  have h9 := h v1 v8 v7
  have h10 := R v7
  have h11 := h z z v1
  have h12 := R v8
  have h13 := h z x z
  have h14 := R y
  have h15 := S h13
  T (T (h x v1 v0) (C (C h5 (C h5 (T (T (T h9 (C (T (C h12 (T (C h12 (S h11)) h15)) h15) h10)) (h (M z v7) y v2)) (C (C h14 (C h14 (T (T (C h3 (T (C (T h13 (C h12 (T h13 (C h12 h11)))) h10) (S h9))) (C (T h6 (C (R v4) h6)) h5)) (S (h z v4 v1))))) h3)))) (R v0))) (S (h v2 v1 v0))

@[equational_result]
theorem Equation3804_implies_Equation4679 (G: Type _) [Magma G] (h: Equation3804 G) : Equation4679 G := fun x y z =>
  let v0 := M y z
  let v1 := M y v0
  let v2 := M x y
  have h3 := h y z v2
  let v4 := M v2 z
  let v5 := M v4 v4
  have h6 := R v5
  have h7 := R (M v0 v4)
  have h8 := h v2 z v2
  let v9 := M v2 v2
  T (T (T (T (T (h v2 z v0) (C (T (T (T (T (h v0 z v2) (C h8 (T (T (T (T (T (h v0 v2 (M y y)) (C (S (h x y y)) (S (h y z y)))) (h v2 v0 z)) (h (M z v0) v4 v0)) (C h7 (S (h y v0 z)))) (S (h y v4 v0))))) (S (h y v9 v4))) (h y v9 v0)) (C (T (T (T (T (T (h v0 v9 v4) (C (T (h v4 v9 v4) (C (S h8) h6)) h7)) (S (h v0 v5 v4))) (C h3 h6)) (S (h v4 (M y v2) v4))) (S h3)) (R v1))) (R (M v2 v0)))) (S (h v2 v1 v0))) (h v2 v1 (M v0 x))) (C (S (h y x v0)) (S (h v0 y x)))) (S (h v0 x y))

@[equational_result]
theorem Equation543_implies_Equation928 (G: Type _) [Magma G] (h: Equation543 G) : Equation928 G := fun x y z =>
  let v0 := M x z
  let v1 := M y z
  let v2 := M v1 v0
  let v3 := M y v2
  have h4 := h v2 y z
  have h5 := h v1 x z
  have h6 := S h5
  have h7 := R v2
  have h8 := R z
  have h9 := h x z v2
  have h10 := R y
  have h11 := C h8 (T (C h10 (T h9 (C h8 (C h7 h6)))) (S h4))
  have h12 := T (C h8 (C h7 h5)) (S h9)
  have h13 := R v1
  have h14 := R x
  have h15 := R v3
  T (T h9 (C h8 (C h7 (T (T h6 (h v1 v3 z)) (C h15 (T (C h8 (T (T (T (C h13 (T (T (C h15 (T (h z y x) (C h10 (T (T (T (C h14 h11) h6) (h v1 v0 v3)) (C (R v0) (C h15 (S (h y v1 v0)))))))) (S (h v0 v3 y))) (C h14 (T (h z v2 v1) (C h7 (C h13 h12)))))) (S (h v2 v1 x))) h4) (C h10 h12))) h11)))))) (S (h v3 z v2))

@[equational_result]
theorem Equation684_implies_Equation4421 (G: Type _) [Magma G] (h: Equation684 G) : Equation4421 G := fun x y z =>
  let v0 := M z y
  let v1 := M v0 (M (M v0 x) x)
  have h2 := h v0 v0 x
  have h3 := R z
  let v4 := M y (M (M y x) x)
  have h5 := R v4
  have h6 := h y y x
  have h7 := R v0
  have h8 := R y
  have h9 := S h6
  let v10 := M x y
  let v11 := M x v10
  let v12 := M v11 (M (M v11 x) x)
  let v13 := M v0 v11
  have h14 := h v11 v11 x
  T (h v11 v0 v11) (C h7 (T (T (T (C (R v11) (C (R v13) (T h14 (C h14 (R v12))))) (S (h v13 v11 v12))) (C h7 (T (T (T (T (C (R x) (T (h v10 y v4) (C h8 (C (R v10) (T (C h9 h5) h9))))) (S (h y x y))) (h y z y)) (C h3 (T (C h8 (C h7 (T h6 (C h6 h5)))) (S (h v0 y v4))))) (C h3 (T h2 (C h2 (R v1))))))) (S (h z v0 v1))))

@[equational_result]
theorem Equation1710_implies_Equation1993 (G: Type _) [Magma G] (h: Equation1710 G) : Equation1993 G := fun x y z =>
  let v0 := M x y
  let v1 := M z z
  let v2 := M y v1
  let v3 := M v2 v0
  let v4 := M v3 v3
  let v5 := M v4 v3
  let v6 := M v1 v2
  let v7 := M x x
  have h8 := h y x v3
  let v9 := M v4 x
  let v10 := M v4 v1
  have h11 := h x x v3
  T (T h11 (C (T (T (T (C (T (h x v1 v3) (C (T (T (h (M v1 x) v0 x) (C (T (S (h y x z)) h8) (R (M v7 v0)))) (S (h v9 v0 x))) (R v10))) h11) (S (h v10 v9 x))) (h v10 (M v1 v3) v3)) (C (S (h v3 v1 v3)) (S (h v3 v3 z)))) (T (T (h v9 v0 v2) (C (T (T (S h8) (h y v3 v3)) (C (T (C (R v3) (T (T (h y v1 x) (C (T (h (M v1 y) v2 z) (C (S (h v1 y z)) (R v6))) (R (M v7 v1)))) (S (h v6 v1 x)))) (S (h v0 v2 z))) (R v5))) (R (M (M v2 v2) v0)))) (S (h v5 v0 v2))))) (S (h v3 v3 v3))

@[equational_result]
theorem Equation2779_implies_Equation2573 (G: Type _) [Magma G] (h: Equation2779 G) : Equation2573 G := fun x y z =>
  let v0 := M z x
  let v1 := M v0 y
  let v2 := M y v1
  let v3 := M v2 z
  have h4 := R v0
  have h5 := R v3
  have h6 := h v2 z v1
  let v7 := M v2 v1
  let v8 := M (M z v1) v7
  have h9 := R v1
  have h10 := h x y v0
  let v11 := M (M y v0) (M x v0)
  T (T (T (T (T h10 (C (T (h v11 v2 v1) (C (C (T (T (h v7 x v2) (C (C (R (M x v2)) (T (h (M v7 v2) v2 v2) (C (T (C (R (M v2 v2)) (S (h y v2 v1))) (S (h y y v1))) (R v2)))) (R x))) (S (h y x v2))) (T (C (T (h v11 v0 y) (C (C h9 (S h10)) h4)) h9) (S (h z v1 x)))) h6)) (R y))) (S (h v8 y z))) (h v8 v0 v3)) (C (C (R (M v0 v3)) (T (C (T (h v8 v2 z) (C (C h5 (S h6)) (h v2 v2 z))) h5) (S (h (M v3 v3) v3 v2)))) h4)) (S (h v3 v0 v3))

@[equational_result]
theorem Equation3591_implies_Equation4146 (G: Type _) [Magma G] (h: Equation3591 G) : Equation4146 G := fun x y z =>
  let v0 := M x z
  let v1 := M v0 z
  let v2 := M v1 z
  have h3 := R z
  have h4 := h v0 z v1
  have h5 := S h4
  let v6 := M v0 v1
  let v7 := M v6 z
  let v8 := M v1 v1
  let v9 := M v8 v7
  have h10 := h x z z
  have h11 := R v1
  T (T (T (T (h x y v0) (C (R v0) (C (T (T (T (T (h x v0 z) (C h3 (T (h v0 v0 v1) (C h11 (T (T (C (R v6) (T (T (T h10 (C h3 h4)) (S (h v0 v7 z))) (C (T (T h10 (h z v1 v1)) (C h11 (C (S h10) h11))) (R v7)))) (S (h v1 v7 v6))) h5))))) (C h3 (T (T (T (C h11 (C h10 h3)) (S (h z z v1))) (h z z v8)) (C (R v8) (C (S (h v0 v1 z)) h3))))) (h z v9 v2)) (C (R v2) (T (T (C (S (h v0 z z)) (R v9)) (S (h v1 v7 v1))) h5))) (R y)))) (h v0 (M (M v2 v1) y) z)) (C h3 (S (h v2 y v1)))) (S (h v1 y z))

@[equational_result]
theorem Equation1710_implies_Equation4497 (G: Type _) [Magma G] (h: Equation1710 G) : Equation4497 G := fun x y z =>
  let v0 := M z z
  let v1 := M v0 x
  let v2 := M (M v0 v0) v1
  let v3 := M y y
  let v4 := M x v3
  have h5 := h v3 x z
  have h6 := S (h y y v1)
  let v7 := M v1 v1
  let v8 := M v7 v3
  have h9 := R v8
  have h10 := R (M (M x x) v3)
  let v11 := M v7 y
  let v12 := M v0 v4
  let v13 := M v3 v4
  T (T (h v4 v4 v2) (C (T (T (T (T (C (T (h v4 v3 v1) (C (T (T (h v13 v3 x) (C (T (T (T (C h5 (R v13)) (S (h v1 v4 y))) (h v1 v4 z)) (C (S h5) (R v12))) h10)) (S (h v12 v3 x))) h9)) (h v4 v4 z)) (S (h v8 v12 v4))) (h v8 v11 y)) (C (T (C (T (T (h v11 v3 x) (C (T h6 (h y y y)) h10)) (S (h (M v3 y) v3 x))) h9) (S (h y v3 v1))) h6)) h5) (R (M (M v2 v2) v4)))) (S (h v1 v4 v2))

@[equational_result]
theorem Equation1929_implies_Equation3906 (G: Type _) [Magma G] (h: Equation1929 G) : Equation3906 G := fun x y z =>
  let v0 := M z z
  let v1 := M y v0
  let v2 := M v1 y
  have h3 := R v0
  let v4 := M y y
  let v5 := M y v1
  have h6 := S (h v4 v5 z)
  have h7 := R v5
  have h8 := h v0 y z
  have h9 := C (T h8 (C h7 (h v0 y y))) h3
  have h10 := S h8
  have h11 := h v0 y x
  have h12 := C (T (C h7 (S h11)) h10) h3
  have h13 := h (M x x) v5 z
  have h14 := R y
  have h15 := C h7 h10
  have h16 := h v0 v5 z
  T (T (T h13 h12) (C (T (T (T (T (T h16 (C (T h15 h10) h3)) h9) h6) (h v4 v1 v2)) (C (C (R v1) (T (C (T (C h14 (T (T h16 (C (T h15 (C h7 h11)) h3)) (S h13))) (C h14 (T (T (T h13 h12) h9) h6))) (R v4)) (S (h y y y)))) (R (M v2 v2)))) h3)) (S (h v2 v2 z))

@[equational_result]
theorem Equation2105_implies_Equation2319 (G: Type _) [Magma G] (h: Equation2105 G) : Equation2319 G := fun x y z =>
  let v0 := M z z
  let v1 := M (M y (M x v0)) y
  have h2 := R v0
  have h3 := R v1
  have h4 := h v0 z x
  let v5 := M x x
  have h6 := R v5
  have h7 := R z
  have h8 := h z z z
  have h9 := S h8
  have h10 := h z v0 z
  let v11 := M v1 v1
  have h12 := R y
  T (T (h x y v0) (C (T (h (M (M y x) y) v1 z) (C (C (T (T (T (C h3 (C (C h12 (T (h x v0 z) (C (T (C (C (T (T h4 (C (T (C (T (C h8 h2) (S h10)) h7) (C (T (h z v0 x) (C h9 h6)) h7)) h6)) (S (h v5 z x))) (R x)) h2) (S (h x x z))) h2))) h12)) (h v11 z x)) (C (T (C (T (C h8 (R v11)) (S (h z v0 v1))) h7) (C (T h10 (C h9 h2)) h7)) h6)) (S h4)) h3) h2)) (R (M v0 v0)))) (S (h v1 v0 v0))

@[equational_result]
theorem Equation2399_implies_Equation1304 (G: Type _) [Magma G] (h: Equation2399 G) : Equation1304 G := fun x y z =>
  let v0 := M x z
  let v1 := M v0 z
  let v2 := M v1 y
  have h3 := R v2
  let v4 := M y (M x (M x y))
  have h5 := R v1
  have h6 := h y y x
  let v7 := M v1 (M x (M x v1))
  let v8 := M v1 (M v1 v2)
  have h9 := R v8
  have h10 := h v1 v1 x
  have h11 := h y v1 v1
  have h12 := S (h v1 v1 z)
  let v13 := M v1 (M z (M z v1))
  let v14 := M z (M x v0)
  have h15 := R x
  have h16 := h z z x
  T (h x v2 v0) (C (T (T (T (C h3 (T (T (C (R v0) (T (C (C h15 (T h16 (C (R v14) h16))) h15) (S (h z x v14)))) (h v1 v8 v13)) (C (T (C h9 (T (C (R v13) h12) h12)) (S h11)) h9))) (C h3 (T (C (T h11 (C h9 (T h10 (C (R v7) h10)))) h9) (S (h v1 v8 v7))))) (C (C h5 (T h6 (C (R v4) h6))) h5)) (S (h y v1 v4))) h3)

@[equational_result]
theorem Equation2958_implies_Equation1358 (G: Type _) [Magma G] (h: Equation2958 G) : Equation1358 G := fun x y z =>
  let v0 := M (M z x) z
  let v1 := M v0 y
  have h2 := R v1
  let v3 := M (M x (M x v0)) v0
  have h4 := R v0
  have h5 := R y
  have h6 := h v0 x v0
  let v7 := M y v1
  let v8 := M (M x (M x v7)) v7
  have h9 := R v7
  have h10 := h v7 x v7
  let v11 := M (M x (M x y)) y
  have h12 := h y x y
  have h13 := S (h z x z)
  let v14 := M (M x (M x z)) z
  T (h x y v1) (C (T (T (T (C (R (M y v7)) (T (h x v14 z) (C (C (T (C (R v14) h13) h13) (R x)) (R z)))) (C (T (C (T (T (h y y v1) (C (T (C (C (T h12 (C (R v11) h12)) h9) h5) (S (h v7 v11 y))) h2)) (C (T h10 (C (R v8) h10)) h2)) h9) (S (h v1 v8 v7))) h4)) (C (C (T h6 (C (R v3) h6)) h5) h4)) (S (h y v3 v0))) h2)

@[equational_result]
theorem Equation2958_implies_Equation2196 (G: Type _) [Magma G] (h: Equation2958 G) : Equation2196 G := fun x y z =>
  let v0 := M x y
  have h1 := R v0
  let v2 := M (M x v0) y
  let v3 := M y z
  have h4 := R y
  have h5 := h y x y
  let v6 := M (M z (M z x)) x
  have h7 := R x
  have h8 := h x z x
  let v9 := M v3 z
  let v10 := M v9 v0
  let v11 := M (M x (M x v10)) v10
  have h12 := R v10
  have h13 := h v10 x v10
  let v14 := M (M x (M x v9)) v9
  have h15 := h v9 x v9
  T (h x v9 v0) (C (T (T (T (T (C (T (C (T (T (h v9 v9 v0) (C (T (C (C (T h15 (C (R v14) h15)) h12) (R v9)) (S (h v10 v14 v9))) h1)) (C (T h13 (C (R v11) h13)) h1)) h12) (S (h v0 v11 v10))) h7) (C (C (T h8 (C (R v6) h8)) h4) h7)) (S (h y v6 x))) (h y y z)) (C (T (C (C (T h5 (C (R v2) h5)) (R v3)) h4) (S (h v3 v2 y))) (R z))) h1)

@[equational_result]
theorem Equation3182_implies_Equation2714 (G: Type _) [Magma G] (h: Equation3182 G) : Equation2714 G := fun x y z =>
  let v0 := M y z
  let v1 := M y x
  let v2 := M v1 v0
  let v3 := M v2 z
  have h4 := R y
  have h5 := R v2
  have h6 := R v3
  have h7 := h v2 y z
  have h8 := R z
  have h9 := h v0 y x
  have h10 := S h9
  have h11 := h x v2 y
  have h12 := C (T (C (T h11 (C (C h10 h5) h4)) h8) (S h7)) h4
  have h13 := T (C (C h9 h5) h4) (S h11)
  have h14 := R v0
  have h15 := R x
  T (T h11 (C (C (T (T h10 (h v0 y v3)) (C (T (C (T (T (T (C (T (T (C (T (h y x z) (C (T (T (T (C h12 h15) h10) (h v0 v3 v1)) (C (C (S (h z v1 v0)) h6) (R v1))) h8)) h6) (S (h v1 z v3))) (C (T (h y v0 v2) (C (C h13 h14) h5)) h15)) h14) (S (h v2 x v0))) h7) (C h13 h8)) h4) h12) h6)) h5) h4)) (S (h v3 v2 y))

@[equational_result]
theorem Equation3193_implies_Equation3674 (G: Type _) [Magma G] (h: Equation3193 G) : Equation3674 G := fun x y =>
  have h0 := R x
  let v1 := M y x
  have h2 := h x v1 x
  have h3 := R v1
  have h4 := h y y x
  have h5 := S h4
  have h6 := R y
  have h7 := h v1 v1 y
  have h8 := S h7
  have h9 := h v1 y x
  have h10 := C h9 h3
  have h11 := C (C (T (T (C (T h10 h8) h3) h10) h8) h6) h6
  have h12 := h y v1 v1
  have h13 := C (C (T (C (T (T (T (C (T h12 h11) h6) h5) h12) h11) h6) h5) h0) h0
  have h14 := h x y y
  have h15 := h x x v1
  have h16 := S h12
  have h17 := C (S h9) h3
  have h18 := C (C (T (T h7 h17) (C (T h7 h17) h3)) h6) h6
  T (T (T (T (C (T h2 (C (C (C (T (C (C (T h4 (C (T (T (T h18 h16) h4) (C (T h18 h16) h6)) h6)) h0) h0) (S h14)) h3) h0) h0)) h0) (S h15)) h14) h13) (C h3 (T h15 (C (T (C (C (C (T h14 h13) h3) h0) h0) (S h2)) h0)))

@[equational_result]
theorem Equation3404_implies_Equation3994 (G: Type _) [Magma G] (h: Equation3404 G) : Equation3994 G := fun x y z =>
  let v0 := M x y
  let v1 := M z v0
  have h2 := R v0
  let v3 := M v1 z
  have h4 := R z
  have h5 := h z z x
  have h6 := h x z v0
  let v7 := M v0 x
  have h8 := h v7 v0 z
  have h9 := h v7 v0 v1
  have h10 := h x v1 v0
  have h11 := R v1
  have h12 := R x
  have h13 := h v1 v1 x
  T (T (T (T (h x y v0) (C h2 (T (C (R y) (T (h v0 x z) (C h4 (S (h y z x))))) (S (h z z y))))) (C h2 (T (T h5 (C h12 (T (T (T (C h4 h6) (S h8)) h9) (C h11 (S h10))))) (S h13)))) (C h2 (T (T (T (T (T h13 (C h12 (T (T (T (C h11 h10) (S h9)) h8) (C h4 (S h6))))) (S h5)) (h z z z)) (C h4 (T (C h4 (h z z v1)) (S (h v3 v1 z))))) (C h4 (T (h v3 v1 v0) (C h2 (S (h z v0 v1)))))))) (S (h v1 z v0))

@[equational_result]
theorem Equation1073_implies_Equation2573 (G: Type _) [Magma G] (h: Equation1073 G) : Equation2573 G := fun x y z =>
  let v0 := M z x
  let v1 := M (M y (M v0 y)) z
  let v2 := M v1 (M v1 v1)
  have h3 := h v1 v2
  let v4 := M v0 (M v0 v0)
  have h5 := h v0 v4
  have h6 := R x
  let v7 := M z (M z z)
  have h8 := h z v7
  have h9 := S h8
  have h10 := T (C h9 h6) h5
  have h11 := C h8 h6
  have h12 := R y
  let v13 := M x (M x x)
  have h14 := h x v13
  have h15 := T (T (h v13 v0) (C (R v0) (T (T (T (C (S h14) h11) (S (h v7 x))) (h v7 v1)) (C h3 (T (T (C h9 (C (T (T (T (C h12 (C h5 h12)) (S (h v4 y))) (C h11 (C h11 h11))) (C h10 (C h10 h10))) (R z))) (S (h (M v4 (M v4 v4)) z))) (S h5)))))) (S (h v2 v0))
  T (T h14 (C h15 (C h15 h15))) (S h3)

@[equational_result]
theorem Equation1074_implies_Equation2 (G: Type _) [Magma G] (h: Equation1074 G) : Equation2 G := fun x y =>
  let v0 := M (M y (M y y)) x
  have h1 := R x
  let v2 := M v0 (M v0 v0)
  let v3 := M x (M x x)
  let v4 := M v3 x
  have h5 := h x v4 x
  let v6 := M v4 v4
  have h7 := h x v3 v3
  have h8 := S h7
  have h9 := h x (M v3 y) y
  have h10 := S h9
  have h11 := T h8 h9
  have h12 := T h10 h7
  let v13 := M (M v4 v6) x
  T (T (h x v0 (M v2 x)) (C (R v0) (T (C (T (T (T (h v3 x v13) (C h1 (T (T (T (T (C h8 (R v13)) (S (h v4 x x))) (C (C h9 (C h9 h9)) h1)) (C (C h12 (C h12 h12)) h1)) (C (T (T (T (C h11 (C h11 h11)) (C h10 (C h10 h10))) (h v3 x x)) (C h5 (C (T h8 h5) h5))) h1)))) (S (h v6 x x))) (S h5)) (C (R v2) h1)) (S (h v0 x x))))) (S (h y v0 x))

@[equational_result]
theorem Equation2755_implies_Equation1740 (G: Type _) [Magma G] (h: Equation2755 G) : Equation1740 G := fun x y z =>
  let v0 := M z x
  let v1 := M v0 z
  have h2 := h z (M v1 v1) v0
  have h3 := R v0
  have h4 := h v1 v1 v1
  have h5 := C h3 (T (C h4 h3) (S h2))
  let v6 := M y y
  have h7 := R v6
  have h8 := C h3 (T h2 (C (S h4) h3))
  let v9 := M v6 v1
  let v10 := M v9 v9
  have h11 := h v1 v10 v6
  have h12 := h v9 v9 v9
  have h13 := R z
  let v14 := M z z
  T (T (T (T (h x v9 z) (C (C (R v10) (T (T (h v0 v14 v9) (C (T (C (R (M v14 v14)) (S (h z y v0))) (S (h z z z))) (R v9))) (C h13 (T (C h7 h8) (C h7 (T (T h5 h11) (C (S h12) h7))))))) h13)) (S (h (M v6 (M v9 v6)) v9 z))) (C h7 (T (T (C h12 h7) (S h11)) h8))) (C h7 h5)

@[equational_result]
theorem Equation492_implies_Equation1171 (G: Type _) [Magma G] (h: Equation492 G) : Equation1171 G := fun x y z =>
  let v0 := M y z
  let v1 := M z v0
  let v2 := M v1 x
  have h3 := h v0 y v0
  have h4 := h y z y
  have h5 := R v0
  have h6 := h z v0 y
  have h7 := R y
  have h8 := R z
  have h9 := C h8 (T (C h7 (C h5 (C h5 (T h6 (C h5 (S h4)))))) (S h3))
  have h10 := h y z v0
  let v11 := M y v2
  have h12 := R v11
  have h13 := R v2
  have h14 := R x
  T (h x y v2) (C h7 (T (C h14 (C h13 (C h13 (T (T (T h10 h9) (h v1 v2 x)) (C h13 (T (C (R v1) (C h14 (C h14 (T (h v2 x v1) (C h14 (T (T (T (C h13 (T (T (C (T (C h8 (T h3 (C h7 (C h5 (C h5 (T (C h5 h4) (S h6))))))) (S h10)) h13) (h v11 y v11)) (C h7 (C h12 (C h12 (T (C h12 (h y v2 y)) (S (h v2 v11 y)))))))) (S (h y v2 v11))) h10) h9)))))) (S (h x v1 x)))))))) (S (h v2 x v2))))

@[equational_result]
theorem Equation1740_implies_Equation3286 (G: Type _) [Magma G] (h: Equation1740 G) : Equation3286 G := fun x y z =>
  let v0 := M z z
  let v1 := M y v0
  have h2 := h v1 v0 v1
  have h3 := R v0
  have h4 := h y z x
  have h5 := R (M v1 v1)
  have h6 := h (M (M x y) x) v1 v0
  have h7 := R (M v0 v0)
  have h8 := h y v0 x
  let v9 := M x x
  have h10 := R v9
  let v11 := M x v0
  let v12 := M (M y x) y
  T (T (T (T (T (C (T (T (h x v0 v9) (C h7 (C (T (T (T (T (h (M v9 x) x v9) (C h10 (T (C (S (h x x x)) h10) (C (h x x y) h10)))) (S (h v12 x v9))) (h v12 x v0)) (C h10 (C (S (h x z y)) h3))) h10))) (S (h v11 v0 v9))) (R x)) (h (M v11 x) x v9)) (C h10 (C (S (h v0 x x)) h10))) (C h10 (C (h v0 x y) h10))) (S (h (M v1 y) x v9))) (C (T (T h2 (C h7 (T (C h5 (C h4 h3)) (S h6)))) (S h8)) (T (T h8 (C h7 (T h6 (C h5 (C (S h4) h3))))) (S h2)))

@[equational_result]
theorem Equation1964_implies_Equation3906 (G: Type _) [Magma G] (h: Equation1964 G) : Equation3906 G := fun x y z =>
  let v0 := M z z
  let v1 := M y v0
  let v2 := M v1 y
  let v3 := M z (M z x)
  have h4 := h v2 z z
  have h5 := S h4
  have h6 := R v0
  have h7 := R v2
  have h8 := h z y z
  have h9 := C (S h8) h7
  have h10 := h z v1 y
  have h11 := R z
  have h12 := C h11 (T h10 h9)
  have h13 := S (h v0 z v0)
  have h14 := C (C h11 (T (C h8 h7) (S h10))) h6
  have h15 := C (T (T h10 h9) (C h11 (T h4 h14))) (R (M z v0))
  have h16 := C (T (T h15 h13) h12) h6
  have h17 := h v0 z z
  have h18 := R v3
  have h19 := h x z z
  T (C (T h19 (C h18 (T (T h17 (C (T (T (T (T h15 h13) h17) h16) h5) (T (T h17 h16) h14))) (C h7 (T (C h12 h6) h5))))) (T h19 (C h18 (T (T h17 h16) h5)))) (S (h v2 v3 v2))

@[equational_result]
theorem Equation3131_implies_Equation2170 (G: Type _) [Magma G] (h: Equation3131 G) : Equation2170 G := fun x y z =>
  let v0 := M z y
  let v1 := M y z
  let v2 := M v1 x
  let v3 := M v2 v0
  have h4 := R v1
  have h5 := R v3
  have h6 := h v1 v2 v1
  have h7 := R v2
  have h8 := h x v1 v1
  have h9 := C (S h8) h7
  have h10 := R x
  have h11 := S (h v0 v2 v2)
  have h12 := h v2 v3 v2
  have h13 := R z
  T (T (h x v1 v3) (C (C (T (C (T (h v2 v3 x) (C (T (T (T (T (C (T (C (C (T (T (h v3 v2 z) (C (C (T (C (C (T h12 (C h11 h5)) h5) h13) (S (h y z v3))) h13) h7)) (C (T h6 h9) h7)) h7) h10) (S (h v2 x v2))) h10) (C (T h12 (C (T (T h11 (h v0 v3 v1)) (C (C (S (h x v1 v0)) h4) h5)) h5)) h10)) (S (h v1 x v3))) h6) h9) h5)) h5) (C (C (T (C h8 h7) (S h6)) h5) h5)) h5) h4)) (S (h v3 v1 v3))

@[equational_result]
theorem Equation3385_implies_Equation3334 (G: Type _) [Magma G] (h: Equation3385 G) : Equation3334 G := fun x y z =>
  let v0 := M z y
  let v1 := M v0 x
  let v2 := M z v0
  have h3 := R v1
  let v4 := M v0 v0
  have h5 := h v0 z y
  have h6 := h z z y
  have h7 := S h6
  have h8 := R v0
  have h9 := R z
  have h10 := R v2
  have h11 := R v4
  T (T (T (h x y v1) (C h3 (T (T (T (T (T (S (h y v0 x)) (h y v0 v0)) (C h8 (T (T (S h5) (h v0 z v4)) (C h11 (S (h z v0 v0)))))) (S (h v4 z v0))) (h v4 z v2)) (C h10 (T (C h11 (T (T (T (T (h z v2 v2) (C h10 (C h9 (T (T (T (h v2 v2 z) (C h9 (T (T (T (C h10 (h v2 z v0)) (S (h v0 v2 v2))) (h v0 v2 z)) (C h9 (T (T (C h8 (h v2 z y)) (S (h y v2 v0))) h7))))) (S (h z z z))) h6)))) (S (h z y v2))) (h z y z)) (C h9 (T (T (C h9 (T (h y z v0) (C h8 h7))) (S (h v0 z z))) h5)))) (S (h z y v4))))))) (C h3 (h v2 v0 x))) (S (h x v2 v1))

@[equational_result]
theorem Equation3404_implies_Equation4109 (G: Type _) [Magma G] (h: Equation3404 G) : Equation4109 G := fun x y z =>
  let v0 := M y z
  let v1 := M v0 z
  have h2 := R z
  let v3 := M v0 v0
  have h4 := R y
  let v5 := M x x
  have h6 := R v1
  have h7 := R x
  have h8 := h v0 y y
  have h9 := h z y y
  have h10 := h y y z
  let v11 := M v0 y
  T (T (h x x z) (C h2 (T (T (T (T (T (T (T (C h7 (h z x y)) (S (h v0 y x))) (h v0 y z)) (C h2 (T (C h4 (T (C h2 (h y z v0)) (S (h v11 v0 z)))) (S (h z v11 y))))) (C h2 (T (C h2 (T h8 (C h4 (S h9)))) (S h10)))) (C h2 (T (T (T (T (T (T h10 (C h2 (T (C h4 h9) (S h8)))) (C h2 (T (h v0 y v1) (C h6 (S (h z v1 y)))))) (S (h v1 v1 z))) (h v1 v1 x)) (C h7 (T (T (T (C h6 (h x v1 x)) (S (h v5 x v1))) (h v5 x v0)) (C (R v0) (S (h x v0 x)))))) (S (h v0 v0 x))))) (h z v3 y)) (C h4 (T (h v3 v0 z) (C h2 (S (h v0 z v0)))))))) (S (h v1 y z))

@[equational_result]
theorem Equation3802_implies_Equation41 (G: Type _) [Magma G] (h: Equation3802 G) : Equation41 G := fun x y z =>
  have h0 := h y z z
  have h1 := S h0
  let v2 := M x x
  let v3 := M y y
  let v4 := M z z
  have h5 := h z z z
  have h6 := h y x x
  have h7 := h z z y
  have h8 := S h5
  have h9 := h y z y
  have h10 := S h9
  have h11 := R v3
  let v12 := M y z
  have h13 := h y v3 v12
  have h14 := h v4 v3 y
  have h15 := S (h v12 v3 v2)
  T (T (T (T (T (T (T (h x x y) (h (M y x) v2 v2)) (C (S (h x x x)) (T (T (T (T (T (T (C h6 (T (T (T (T (T (h y x v12) (C (T (T (T (h v12 x y) (C h6 (R (M v12 v12)))) h15) h10) h11)) h10) h0) (h v4 v3 v12)) (C h10 (T (T (T (T h8 h7) (C (T (T h9 (C h9 h11)) (S h13)) h5)) (S h14)) h1)))) h15) h10) h0) h14) (C (T (T h13 (C h10 h11)) h10) h8)) (S h7)))) (S (h z x x))) (h z x y)) (C h6 h5)) (S (h v4 v3 v2))) h1

@[equational_result]
theorem Equation3804_implies_Equation4620 (G: Type _) [Magma G] (h: Equation3804 G) : Equation4620 G := fun x y z =>
  let v0 := M x x
  let v1 := M v0 y
  let v2 := M z y
  let v3 := M v2 v1
  let v4 := M v1 z
  have h5 := S (h v1 y v0)
  have h6 := h x x x
  have h7 := R v1
  have h8 := h v0 y v0
  have h9 := C h7 (T h8 (C h7 (S h6)))
  have h10 := T (C h7 h6) (S h8)
  let v11 := M v0 x
  have h12 := h z y v0
  T (T (T (h v0 y z) (C (T (T (T (T h12 (h v1 (M z v0) v1)) (C (S h12) (T (T (T (T (T h9 h5) (h v1 y x)) (C (h x y v0) (T (h v1 x v0) (C (R v11) h10)))) (S (h v11 (M x v0) v1))) (S (h x x v0))))) (h v2 v0 v1)) (C h10 (R v3))) (T (h v0 z v1) (C (R v4) (T (T (h v0 v1 v1) (C (T h9 h5) (R (M v0 v1)))) (S (h v0 y v1))))))) (S (h v4 v3 v1))) (S (h v2 z v1))

@[equational_result]
theorem Equation3963_implies_Equation41 (G: Type _) [Magma G] (h: Equation3963 G) : Equation41 G := fun x y z =>
  let v0 := M x x
  have h1 := h y z v0
  let v2 := M y z
  let v3 := M z (M z y)
  have h4 := R v2
  let v5 := M v0 v3
  have h6 := R v5
  have h7 := h x x v0
  have h8 := h x x y
  let v9 := M x v0
  have h10 := R v9
  have h11 := R v3
  have h12 := h x x v2
  have h13 := S h12
  have h14 := h v9 v2 v2
  let v15 := M v2 (M v2 v9)
  T (T (T (T (T h12 h14) (h v15 v2 v2)) (C (T (T (T (T (T (T (C h4 (T (h v2 v15 v3) (C (T (T (C (R v15) (T (S h14) h13)) (S (h v9 v2 v0))) h13) h11))) (C (T (h y z v2) (C h11 h1)) h6)) (S (h v0 v3 v5))) (C (T h7 (C h10 h8)) h11)) (S (h y v9 v3))) (h y v9 v5)) (C (T (C h10 (S h8)) (S h7)) h6)) h4)) (S (h v3 v0 v2))) (S h1)

@[equational_result]
theorem Equation4176_implies_Equation3297 (G: Type _) [Magma G] (h: Equation4176 G) : Equation3297 G := fun x y z =>
  let v0 := M z y
  let v1 := M z v0
  have h2 := R z
  have h3 := R y
  let v4 := M v0 v0
  have h5 := R x
  let v6 := M x x
  have h7 := R v1
  have h8 := h y v0 y
  have h9 := h y z y
  have h10 := h y y z
  let v11 := M y v0
  T (T (h x x z) (C (T (T (T (T (T (T (T (C (h x z y) h5) (S (h y v0 x))) (h y v0 z)) (C (T (C (T (C (h z y v0) h2) (S (h v0 v11 z))) h3) (S (h v11 z y))) h2)) (C (T (C (T h8 (C (S h9) h3)) h2) (S h10)) h2)) (C (T (T (T (T (T (T h10 (C (T (C h9 h3) (S h8)) h2)) (C (T (h y v0 v1) (C (S (h v1 z y)) h7)) h2)) (S (h v1 v1 z))) (h v1 v1 x)) (C (T (T (T (C (h v1 x x) h7) (S (h x v6 v1))) (h x v6 v0)) (C (S (h v0 x x)) (R v0))) h5)) (S (h v0 v0 x))) h2)) (h v4 z y)) (C (T (h v0 v4 z) (C (S (h z v0 v0)) h2)) h3)) h2)) (S (h y v1 z))

@[equational_result]
theorem Equation4176_implies_Equation3588 (G: Type _) [Magma G] (h: Equation4176 G) : Equation3588 G := fun x y z =>
  let v0 := M x y
  let v1 := M v0 z
  have h2 := R v0
  have h3 := R z
  let v4 := M z v1
  have h5 := h z z y
  have h6 := R y
  have h7 := h z y v0
  let v8 := M y v0
  have h9 := h v0 v8 z
  have h10 := h v0 v8 v1
  have h11 := R v1
  have h12 := h v1 y v0
  have h13 := h v1 v1 y
  T (T (T (T (T (h x y v0) (C (T (C (T (h y v0 z) (C (S (h z x y)) h3)) (R x)) (S (h z z x))) h2)) (C (T (T h5 (C (T (T (T (C h7 h3) (S h9)) h10) (C (S h12) h11)) h6)) (S h13)) h2)) (C (T (T (T (T h13 (C (T (T (T (C h12 h11) (S h10)) h9) (C (S h7) h3)) h6)) (S h5)) (h z z z)) (C (T (C (h z z v1) h3) (S (h v1 v4 z))) h3)) h2)) (C (C (T (h v1 v4 v0) (C (S (h v0 z v1)) h2)) h3) h2)) (S (h z v1 v0))

@[equational_result]
theorem Equation684_implies_Equation2279 (G: Type _) [Magma G] (h: Equation684 G) : Equation2279 G := fun x y z =>
  let v0 := M y (M (M y x) x)
  have h1 := h y y x
  let v2 := M y (M z y)
  have h3 := h v2 v2 x
  have h4 := S h3
  let v5 := M v2 (M (M v2 x) x)
  have h6 := R v5
  let v7 := M x v2
  have h8 := R v7
  have h9 := R v2
  have h10 := R x
  have h11 := S (h v7 v7 x)
  let v12 := M v7 (M (M v7 x) x)
  let v13 := M v2 v7
  have h14 := S (h v2 v2 v2)
  let v15 := M v2 (M (M v2 v2) v2)
  T (T (T (T (h x v2 v15) (C h9 (C h10 (T (C h14 (R v15)) h14)))) (h v13 v7 v12)) (C h8 (C (R v13) (T (C h11 (R v12)) h11)))) (C h8 (T (T (T (T (C (T (C h9 (C h10 (T h3 (C h3 h6)))) (S (h x v2 v5))) h8) (C h10 (T (h v7 v2 v5) (C h9 (C h8 (T (C h4 h6) h4)))))) (S (h v2 x v2))) (C (R y) (C (R z) (T h1 (C h1 (R v0)))))) (S (h z y v0))))

@[equational_result]
theorem Equation1301_implies_Equation749 (G: Type _) [Magma G] (h: Equation1301 G) : Equation749 G := fun x y z =>
  let v0 := M x z
  let v1 := M v0 y
  let v2 := M z v1
  let v3 := M y v2
  let v4 := M y x
  let v5 := M (M v4 v3) x
  have h6 := R v2
  have h7 := h y v3 x
  let v8 := M v2 y
  have h9 := R v3
  let v10 := M v8 v1
  have h11 := R x
  have h12 := S (h y z x)
  let v13 := M (M v4 z) x
  have h14 := R v10
  have h15 := S (h x v0 x)
  let v16 := M (M (M x x) v0) x
  have h17 := R z
  T (T (T (T (h x v3 v1) (C h9 (C (C (T (C h11 (C (T (T (h v0 z v16) (C h17 (T (C (C h15 h17) (R v16)) h15))) (C (T (h z v10 v13) (C h14 (T (C (T (C h12 h14) (S (h z y v1))) (R v13)) h12))) h11)) (R y))) (S (h v10 x y))) h9) (R v1)))) (S (h v8 v3 v1))) (C h6 (T h7 (C (C h7 h6) (R v5))))) (S (h v3 v2 v5))

@[equational_result]
theorem Equation1790_implies_Equation949 (G: Type _) [Magma G] (h: Equation1790 G) : Equation949 G := fun x y z =>
  let v0 := M y z
  let v1 := M z x
  let v2 := M v1 v0
  let v3 := M y v2
  have h4 := R v0
  let v5 := M v2 v1
  let v6 := M v1 y
  have h7 := h x y z
  have h8 := T (C (h z v1 y) (T h7 (C (h v0 v0 v1) (R v6)))) (S (h (M v2 v0) v6 (M v0 v1)))
  have h9 := h v1 v1 y
  let v10 := M (M y v1) v1
  have h11 := h v10 v0 v6
  have h12 := h x z x
  T (T (T h12 (C (R v1) (T (h (M (M x x) z) v2 v1) (C (R v5) (T (T (T (T (T (C (S h12) (R v2)) (C h7 (C h9 h4))) (S h11)) (h v10 v3 v1)) (C (R (M v3 v1)) (C (T (C h8 (T h11 (C (R (M v0 v6)) (C (S h9) h4)))) (S (h v6 v2 v0))) (R v3)))) (S (h y v3 v1))))))) (C h8 (T (h (M v5 y) v0 v3) (C (R (M v0 v3)) (C (S (h v1 y v2)) h4))))) (S (h v3 v2 v0))

@[equational_result]
theorem Equation2196_implies_Equation1876 (G: Type _) [Magma G] (h: Equation2196 G) : Equation1876 G := fun x y z =>
  let v0 := M z y
  let v1 := M y z
  let v2 := M x v1
  let v3 := M v2 v0
  have h4 := S (h v2 v0 v3)
  let v5 := M v0 v3
  let v6 := M (M v3 y) y
  let v7 := M v5 v3
  have h8 := h z y y
  let v9 := M (M y y) y
  let v10 := M v0 v2
  let v11 := M v10 v2
  let v12 := M (M v1 v1) v1
  T (T (T (T (T (T (h x v1 v1) (C (T (T (h v12 y x) (C (R (M (M y x) x)) (T (C (R v12) (h y z y)) (S (h (M v0 y) v1 v1))))) (S (h v0 y x))) (R v2))) (h v10 v2 v2)) (C (R (M (M v2 v2) v2)) (T (T (T (T (h v11 z x) (C (R (M (M z x) x)) (T (T (T (C (R v11) h8) (S (h v9 v0 v2))) (h v9 v0 v3)) (C (R v7) (S h8))))) (S (h v7 z x))) (h v7 v3 y)) (C (R v6) h4)))) (S (h v6 v2 v2))) (h v6 v5 v3)) (C h4 (S (h v0 v3 y)))

@[equational_result]
theorem Equation3211_implies_Equation1670 (G: Type _) [Magma G] (h: Equation3211 G) : Equation1670 G := fun x y z =>
  let v0 := M z y
  let v1 := M v0 z
  let v2 := M x y
  let v3 := M v2 v1
  have h4 := R v3
  have h5 := R y
  have h6 := R x
  have h7 := R z
  have h8 := h v0 y v0
  have h9 := R v0
  have h10 := h y z y
  have h11 := h z v0 y
  have h12 := h y z v0
  have h13 := C (T (C (C (C (C h6 (T h12 (C (T (C (C (C (T h11 (C (S h10) h9)) h9) h9) h5) (S h8)) h7))) (R v1)) h6) h6) (S (h x x v1))) h5
  have h14 := h y v3 x
  T (T (h x v2 y) (C (T (T (S (h y x y)) h14) (C (T (T (T (T h13 (h v2 v3 v1)) (C (S (h v1 v2 v1)) h4)) (C (T (C (T h8 (C (C (C (T (C h10 h9) (S h11)) h9) h9) h5)) h7) (S h12)) h4)) (C (T h14 (C h13 h4)) h4)) h4)) (R v2))) (S (h v3 v2 v3))

@[equational_result]
theorem Equation3211_implies_Equation3553 (G: Type _) [Magma G] (h: Equation3211 G) : Equation3553 G := fun x y z =>
  let v0 := M x z
  let v1 := M v0 z
  have h2 := R v1
  let v3 := M x y
  have h4 := R v3
  have h5 := R y
  have h6 := S (h v1 v0 v1)
  have h7 := R v0
  have h8 := C (S (h x x z)) (R z)
  have h9 := C h8 h2
  have h10 := h z v1 x
  have h11 := S (h z v0 z)
  have h12 := h v0 v1 z
  have h13 := S (h z x z)
  have h14 := h x v0 z
  T (h v3 v1 y) (C (T (C (C (C (T (h v1 y v3) (C (T (C (C (T (T (T (T (T (T (C (h y x y) h4) (S (h x v3 y))) h14) (C (T (T h13 h10) (C (T (T h8 h12) (C (T (T h11 h10) h9) h2)) h2)) h7)) h6) (h v1 x z)) (C (R (M v1 v1)) (T (T (T (T h14 (C h13 h7)) (C (T (T h10 h9) (C (T h12 (C h11 h2)) h2)) h7)) (C (C (C (T h10 h9) h2) h2) h7)) h6))) h4) h2) (S (h v3 v1 v1))) h5)) h5) h5) h4) (S (h y v3 y))) h2)

@[equational_result]
theorem Equation684_implies_Equation4026 (G: Type _) [Magma G] (h: Equation684 G) : Equation4026 G := fun x y z =>
  let v0 := M z y
  let v1 := M z v0
  let v2 := M v1 x
  have h3 := R v1
  let v4 := M x (M (M x x) x)
  have h5 := h x x x
  have h6 := R x
  let v7 := M v2 x
  let v8 := M v2 (M v7 x)
  let v9 := M x v2
  have h10 := h v2 v2 x
  have h11 := R v2
  let v12 := M v1 v7
  let v13 := M v2 v1
  have h14 := h v1 v1 x
  let v15 := M y (M (M y x) x)
  have h16 := h y y x
  T (C h6 (T (T (T (h y z y) (C (R z) (T (C (R y) (C (R v0) (T h16 (C h16 (R v15))))) (S (h v0 y v15))))) (h v1 v2 v1)) (C h11 (T (T (C h3 (C (R v13) (T h14 (C h14 (R v12))))) (S (h v13 v1 v12))) (C (T (h v2 x v2) (C h6 (T (T (T (C h11 (C (R v9) (T h10 (C h10 (R v8))))) (S (h v9 v2 v8))) (C h6 (C h3 (T h5 (C h5 (R v4)))))) (S (h v1 x v4))))) h3))))) (S (h v2 x v1))

@[equational_result]
theorem Equation968_implies_Equation3997 (G: Type _) [Magma G] (h: Equation968 G) : Equation3997 G := fun x y z =>
  let v0 := M x z
  let v1 := M z v0
  let v2 := M v1 y
  have h3 := h v2 v1 v2
  let v4 := M (M v2 v1) (M v2 v2)
  have h5 := R (M v1 x)
  have h6 := R x
  let v7 := M v0 v1
  have h8 := h y z z
  have h9 := R v1
  let v10 := M (M z z) (M z y)
  let v11 := M x y
  let v12 := M v0 v11
  have h13 := h v11 v1 v11
  T (T h13 (C h9 (T (T (T (T (T (T (T (h (M (M v11 v1) (M v11 v11)) x v1) (C h6 (C h5 (T (S h13) (h v11 v1 v0))))) (S (h (M v7 v12) x v1))) (C (R v7) (T (T (T (T (h v12 x z) (C h6 (C (R (M z x)) (T (S (h y z x)) h8)))) (S (h v10 x z))) (h v10 v0 z)) (C (R v0) (C h9 (S h8)))))) (h (M v7 (M v0 v2)) x v1)) (C h6 (T (C h5 (S (h v2 v1 v0))) (C h5 h3)))) (S (h v4 x v1))) (R v4)))) (S h3)

@[equational_result]
theorem Equation1537_implies_Equation3286 (G: Type _) [Magma G] (h: Equation1537 G) : Equation3286 G := fun x y z =>
  let v0 := M x x
  let v1 := M z z
  let v2 := M y v1
  have h3 := h v0 x x
  have h4 := h x x x
  have h5 := S h4
  have h6 := R v0
  have h7 := h x x v0
  have h8 := R x
  let v9 := M v2 v2
  have h10 := R v2
  have h11 := h x y v0
  let v12 := M y y
  have h13 := R v12
  have h14 := h v12 x x
  have h15 := R y
  T (T (T (T h3 (C h6 (C h8 (T (C h6 h4) (S h7))))) (C h6 (C h8 (T h11 (C h13 h5))))) (S h14)) (C h15 (T (T (h y y y) (C h13 (T (h (M y v12) x v2) (C h6 (C h10 (T (T (T (T (C (C h15 (T (T (T h14 (C h6 (C h8 (T (C h13 h4) (S h11))))) (C h6 (C h8 (T (h x z v0) (C (R v1) h5))))) (S (h v1 x x)))) h10) (h v9 x x)) (C h6 (C h8 (T (C (R v9) h4) (S (h x v2 v0)))))) (C h6 (C h8 (T h7 (C h6 h5))))) (S h3))))))) (S (h v2 y v0))))

@[equational_result]
theorem Equation3211_implies_Equation492 (G: Type _) [Magma G] (h: Equation3211 G) : Equation492 G := fun x y z =>
  let v0 := M z y
  let v1 := M z v0
  let v2 := M x v1
  have h3 := h y z v0
  have h4 := R z
  have h5 := R y
  have h6 := R v0
  have h7 := h z v0 y
  have h8 := h y z y
  have h9 := h v0 y v0
  have h10 := S (h v0 v1 z)
  have h11 := R v1
  have h12 := h v0 z v0
  have h13 := h z v1 v0
  have h14 := S h8
  have h15 := C (T (T h14 h3) (C (T (T (T (C (C (C (T h7 (C h14 h6)) h6) h6) h5) (S h9)) (h v0 z v1)) (C (T (C (C (C (T h13 (C (S h12) h11)) h11) h11) h6) (S (h v1 v0 v1))) h4)) h4)) h6
  T (h x v2 v1) (C (T (T (T (S (h v1 x v1)) (h v1 z v1)) (C (T (T (T (C (T (T (T (C (T (T (C (T h7 h15) h11) h10) h12) h11) (S h13)) h7) h15) h11) h10) h9) (C (C (C (T (C h8 h6) (S h7)) h6) h6) h5)) h4)) (S h3)) (R v2))

@[equational_result]
theorem Equation3404_implies_Equation3794 (G: Type _) [Magma G] (h: Equation3404 G) : Equation3794 G := fun x y z =>
  let v0 := M z y
  let v1 := M z x
  have h2 := R x
  let v3 := M v1 x
  let v4 := M x y
  have h5 := S (h v4 x y)
  have h6 := R y
  have h7 := h v1 z v1
  have h8 := h x v1 z
  have h9 := R v1
  have h10 := h v1 v1 x
  have h11 := C h6 (T (T h10 (C h2 (T (C h9 h8) (S h7)))) (C h2 (T (h v1 z y) (C h6 (S (h x y z))))))
  have h12 := C h6 (T (T (T (h x x x) (C h2 (T (C h2 (h x x z)) (S (h v1 z x))))) (C h2 (T h7 (C h9 (S h8))))) (S h10))
  have h13 := h x y x
  T (T h13 (C h2 (T (T (T (T (T h12 h11) h5) (C (T h13 (C h2 (T (T (T (T (T h12 h11) h5) (h v4 x v3)) (C (R v3) (T (S (h y v3 x)) (h y v3 z)))) (S (h v0 z v3))))) h2)) (h (M x (M v0 z)) x v0)) (C (R v0) (C h2 (S (h z x v0))))))) (S (h v1 v0 x))

@[equational_result]
theorem Equation3547_implies_Equation41 (G: Type _) [Magma G] (h: Equation3547 G) : Equation41 G := fun x y z =>
  let v0 := M x x
  let v1 := M y y
  have h2 := R z
  have h3 := h v0 x x
  let v4 := M v0 v0
  have h5 := h x (M v4 x) v0
  have h6 := R v0
  have h7 := h x x v0
  have h8 := h x v4 v0
  have h9 := T (S h8) (S h7)
  have h10 := h v4 x x
  have h11 := R x
  have h12 := T h7 h8
  have h13 := h x x x
  have h14 := h v4 v0 v0
  let v15 := M z z
  T (T (T (T (T (T (T (T h13 (h x (M v0 x) (M (M v15 v15) x))) (C (T (T (T h3 h5) (C (T (T h10 (C h11 (C h9 h11))) (S h13)) (C h12 h6))) (S h14)) (S (h v15 v0 x)))) (S (h z (M v4 v0) v0))) (C h2 (T (T (T h14 (C (T (T h13 (C h11 (C h12 h11))) (S h10)) (C h9 h6))) (S h5)) (S h3)))) (S (h x z x))) (h x z (M (M v1 v1) x))) (C h2 (S (h v1 v0 x)))) (S (h y z v0))

@[equational_result]
theorem Equation492_implies_Equation3211 (G: Type _) [Magma G] (h: Equation492 G) : Equation3211 G := fun x y z =>
  let v0 := M y z
  have h1 := h y z v0
  have h2 := h z v0 y
  have h3 := h y z y
  have h4 := R v0
  have h5 := R y
  have h6 := h v0 y v0
  let v7 := M v0 z
  have h8 := S (h v0 v7 z)
  have h9 := h v0 z v0
  have h10 := R v7
  have h11 := h z v7 v0
  have h12 := R z
  have h13 := S h3
  have h14 := C h4 (T (T h13 h1) (C h12 (T (T (T (C h5 (C h4 (C h4 (T h2 (C h4 h13))))) (S h6)) (h v0 z v7)) (C h12 (T (C h4 (C h10 (C h10 (T h11 (C h10 (S h9)))))) (S (h v7 v0 v7)))))))
  let v15 := M v7 x
  T (h x v15 v7) (C (R v15) (T (T (T (S (h v7 x v7)) (h v7 z v7)) (C h12 (T (T (T (C h10 (T (T (T (C h10 (T (T (C h10 (T h2 h14)) h8) h9)) (S h11)) h2) h14)) h8) h6) (C h5 (C h4 (C h4 (T (C h4 h3) (S h2)))))))) (S h1)))

@[equational_result]
theorem Equation731_implies_Equation1543 (G: Type _) [Magma G] (h: Equation731 G) : Equation1543 G := fun x y z =>
  let v0 := M z (M z x)
  let v1 := M y y
  let v2 := M v1 v0
  have h3 := R v1
  have h4 := h v0 v1 v0
  let v5 := M v0 v0
  let v6 := M v1 (M v5 v0)
  have h7 := h x v1 v1
  have h8 := R z
  let v9 := M v1 (M (M v1 v1) x)
  have h10 := R x
  have h11 := h x v1 x
  let v12 := M (M x x) x
  have h13 := R y
  have h14 := R v2
  T (T (h x v2 v0) (C h14 (C h14 (T (T (T (T (T (T (T (T (T (T (h (M v5 x) v1 y) (C h3 (S (h x v1 v0)))) (C h3 h11)) (S (h v12 v1 y))) (h v12 y y)) (C h13 (C h13 (T (T (T (T (T (h (M v1 v12) x y) (C h10 (T (C h10 (S h11)) (C h10 h7)))) (S (h v9 x y))) (h v9 z y)) (C h8 (C h8 (S h7)))) h4)))) (S (h v6 y y))) (h v6 v1 y)) (C h3 (C h3 (S h4)))) (C h3 (h v2 v1 z))) (S (h (M (M z z) v2) v1 y)))))) (S (h v2 v2 z))

