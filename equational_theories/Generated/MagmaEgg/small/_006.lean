import equational_theories.Equations.All
import equational_theories.Magma

private def congr_op {G: Type _} [Magma G] {a b c d: G} (h1: a = b) (h2: c = d): a ◇ c = b ◇ d := by
  rw [h1, h2]
private abbrev T := @Eq.trans
private abbrev S := @Eq.symm
private abbrev R := @Eq.refl
private abbrev M := @Magma.op
private abbrev C := @congr_op

@[equational_result]
theorem Equation1790_implies_Equation3607 (G: Type _) [Magma G] (h: Equation1790 G) : Equation3607 G := fun x y z =>
  let v0 := M x y
  let v1 := M y z
  let v2 := M v1 x
  let v3 := M v2 v0
  let v4 := M v0 v1
  let v5 := M z v2
  have h6 := h z x y
  have h7 := S h6
  have h8 := h y v2 x
  have h9 := R (M v2 x)
  have h10 := R v5
  have h11 := h x z v2
  T (T (h v0 v5 y) (C (T (T (C h10 (T h8 (C h9 h7))) (S h11)) (h x v0 v1)) (T (T (T (C (R (M y v0)) (T (h v5 v0 y) (C (R (M v0 y)) (T (C (R (M y v5)) (C (T h11 (C h10 (T (C h9 h6) (S h8)))) (R y))) (S (h y y v5)))))) (S (h y y v0))) (h y v1 x)) (C (T (h v2 v2 v0) (C (R v3) (C h7 (R v2)))) (R v4))))) (S (h v5 v4 v3))

@[equational_result]
theorem Equation1333_implies_Equation2 (G: Type _) [Magma G] (h: Equation1333 G) : Equation2 G := fun x y =>
  let v0 := M (M x y) x
  let v1 := M v0 x
  have h2 := R x
  have h3 := h x x y
  let v4 := M x x
  let v5 := M (M v4 v4) x
  have h6 := h v4 x x
  let v7 := M v4 x
  let v8 := M v7 x
  let v9 := M (M v4 v0) x
  have h10 := h x x x
  have h11 := S h10
  let v12 := M (M v4 v7) x
  T (T (h x x v1) (C h2 (T (T (T (T (T (C (C (S h3) h2) h2) (h v7 x v5)) (C h2 (T (T (T (C (C (S h6) (R v7)) h2) (h v12 x v8)) (C h2 (C (T (C h11 (R v12)) (S (h v7 x x))) h2))) h11))) (C h2 (T (T (T h3 (C h2 (C (T (h v0 x x) (C h10 (R v9))) h2))) (S (h v9 x v8))) (C (C h6 (R v0)) h2)))) (S (h v0 x v5))) (C (C h3 (R y)) h2)))) (S (h y x v1))

@[equational_result]
theorem Equation2135_implies_Equation1492 (G: Type _) [Magma G] (h: Equation2135 G) : Equation1492 G := fun x y =>
  let v0 := M y y
  let v1 := M y v0
  let v2 := M y x
  let v3 := M v2 v1
  let v4 := M v3 v3
  let v5 := M v4 v3
  let v6 := M (M v1 v1) v1
  let v7 := M (M v0 v0) v0
  have h8 := h y y
  let v9 := M v0 y
  have h10 := R v9
  have h11 := R (M (M v2 v2) v2)
  let v12 := M x x
  have h13 := T (T (T (h (M v12 x) v2) (C h11 (S (h y x)))) (C h11 (T (T (T (T h8 (C h10 (T (T (T (T (h v0 y) (C h10 (T (h v9 v0) (C (R v7) (S h8))))) (S (h v7 y))) (h v7 v1)) (C (R v6) (S (h y v0)))))) (S (h v6 y))) (h v6 v3)) (C (R v5) (S (h v2 v1)))))) (S (h v5 v2))
  T (T (h x x) (C h13 (T (T (h v12 x) (C h13 h13)) (S (h v4 v3))))) (S (h v3 v3))

@[equational_result]
theorem Equation627_implies_Equation2036 (G: Type _) [Magma G] (h: Equation627 G) : Equation2036 G := fun x y =>
  let v0 := M x x
  let v1 := M v0 x
  let v2 := M v1 (M x y)
  have h3 := S (h y y v2)
  let v4 := M y (M (M y v2) v2)
  have h5 := R x
  have h6 := S (h x y y)
  let v7 := M x (M (M y y) y)
  have h8 := R v0
  have h9 := h x x x
  have h10 := S h9
  let v11 := M x v1
  have h12 := R v11
  have h13 := T (C h5 (C (T (C h5 (C h5 (T h9 (C h9 h12)))) (S (h x x v11))) (T (h v0 x v7) (C (T (h v0 x v11) (C h8 (C h8 (T (C h10 h12) h10)))) (C h8 (T (C h6 (R v7)) h6)))))) (S (h x v0 v1))
  have h14 := h x x v0
  T (h x y v4) (C (T h14 (C (T h14 (C h5 h13)) h13)) (C h5 (T (C h3 (R v4)) h3)))

@[equational_result]
theorem Equation1776_implies_Equation19 (G: Type _) [Magma G] (h: Equation1776 G) : Equation19 G := fun x y z =>
  let v0 := M z x
  let v1 := M y v0
  have h2 := h v0 v1 v1
  have h3 := S h2
  let v4 := M v1 v1
  have h5 := h (M v4 v0) v1 (M v1 x)
  have h6 := h x y y
  have h7 := R v1
  let v8 := M y y
  have h9 := h (M v8 x) y v0
  have h10 := h x y v0
  have h11 := R v4
  have h12 := h x v1 v1
  T (T (T (T (T h12 (C h11 (T (h (M v4 x) v1 (M v8 z)) (C (S (h z y v0)) (S h12))))) h5) (C (T (C h7 (T (C h7 h6) (S h9))) (S h10)) h3)) (h (M x v0) v1 (M v1 y))) (C (T (C h7 (T (C h7 (h y y y)) (S (h (M v8 y) y v0)))) (S (h y y v0))) (T (C h11 (T (C (T h10 (C h7 (T h9 (C h7 (S h6))))) h2) (S h5))) h3))

@[equational_result]
theorem Equation1293_implies_Equation684 (G: Type _) [Magma G] (h: Equation1293 G) : Equation684 G := fun x y z =>
  let v0 := M (M y z) z
  let v1 := M x v0
  have h2 := R v1
  let v3 := M y v1
  let v4 := M (M (M v3 v3) x) x
  have h5 := h y v1 v4
  have h6 := R v4
  have h7 := h v3 v3 x
  have h8 := R v0
  have h9 := S h7
  have h10 := R z
  let v11 := M (M v3 v0) v0
  have h12 := S (h v1 v1 x)
  let v13 := M (M (M v1 v1) x) x
  T (T (T (T (h x v0 v13) (C h8 (T (C h12 (R v13)) h12))) (C h8 (T (T (h v1 v11 z) (C (R v11) (C (C (S (h y v1 v0)) h10) h10))) (C (C (C (C (T h5 (C h2 (T (C h9 h6) h9))) h2) h8) h8) h8)))) (S (h (M (M v1 v3) v1) v0 v0))) (C (T (C h2 (T h7 (C h7 h6))) (S h5)) h2)

@[equational_result]
theorem Equation3755_implies_Equation3798 (G: Type _) [Magma G] (h: Equation3755 G) : Equation3798 G := fun x y z w =>
  let v0 := M w y
  let v1 := M z x
  let v2 := M x v0
  let v3 := M v0 v1
  have h4 := h v0 x z
  let v5 := M x y
  let v6 := M y x
  let v7 := M x v5
  have h8 := R (M x v6)
  have h9 := h x y w
  T (T (T (T (T h9 (h v6 v0 x)) (h (M v0 v6) v2 v0)) (C (T (T (T (T (C (R v2) (T (T (T (T (h v0 v6 x) (C (S h9) h8)) (C (T (T (h x y x) (h v6 v5 x)) (C (S (h y x y)) (R v7))) h8)) (S (h v7 v6 x))) (S (h v5 x y)))) (S (h v0 x v5))) h4) (h v2 v1 v0)) (C (T (T (T (h v1 v2 x) (C (T (S h4) (h v0 x v0)) (R (M x v2)))) (S (h (M v0 x) v2 x))) (S (h x v0 x))) (R v3))) (R (M v0 v2)))) (S (h v3 v2 v0))) (S (h v1 v0 x))

@[equational_result]
theorem Equation2714_implies_Equation1761 (G: Type _) [Magma G] (h: Equation2714 G) : Equation1761 G := fun x y z =>
  let v0 := M x y
  let v1 := M v0 z
  let v2 := M y z
  have h3 := h y x v2
  have h4 := R y
  have h5 := h x x y
  have h6 := R v0
  have h7 := h x x v0
  have h8 := S h7
  let v9 := M x x
  have h10 := h v0 (M v9 (M x v0)) v0
  have h11 := T (C (T h10 (C (C h8 h8) h6)) h4) (S h5)
  T (T (T h5 (C (T (C (C h7 h7) h6) (S h10)) h4)) (h (M v0 y) x v1)) (C (T (T (C (T (T (C (R x) h11) (h v9 v0 y)) (C (T (C (R (M v0 v9)) h11) (S (h y x x))) h4)) (T (h (M x v1) v0 z) (C (S (h y x v1)) (R z)))) (C (C h3 h3) (R v2))) (S (h v2 (M v0 (M x v2)) v2))) (R v1))

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
theorem Equation2105_implies_Equation1264 (G: Type _) [Magma G] (h: Equation2105 G) : Equation1264 G := fun x y z =>
  have h0 := h z y x
  have h1 := S h0
  let v2 := M x x
  have h3 := R v2
  let v4 := M (M y z) y
  have h5 := h v4 v4 x
  have h6 := R v4
  let v7 := M v4 v4
  have h8 := h v7 v4 x
  have h9 := h z y v4
  have h10 := h v2 v4 x
  have h11 := h v4 v2 x
  have h12 := R x
  have h13 := S h10
  have h14 := C (T (C (S h9) h6) (C h0 h6)) h3
  have h15 := C h6 (T (T h0 (C (T h5 (C (C (T (T h8 h14) h13) h6) h3)) h3)) (S h11))
  T (T (h x (M v4 z) v4) (C (T (C (C (T (T (T h15 h8) h14) h13) h12) h15) (S (h x x v4))) (R v7))) (C h12 (C h6 (T (T h11 (C (T (C (C (T (T h10 (C (T (C h1 h6) (C h9 h6)) h3)) (S h8)) h6) h3) (S h5)) h3)) h1)))

@[equational_result]
theorem Equation4176_implies_Equation4461 (G: Type _) [Magma G] (h: Equation4176 G) : Equation4461 G := fun x y z =>
  have h0 := R y
  have h1 := h z z z
  have h2 := S h1
  have h3 := R z
  let v4 := M z z
  have h5 := h z v4 z
  have h6 := h z v4 y
  let v7 := M v4 y
  have h8 := h y v7 z
  have h9 := R v4
  have h10 := C (S (h v4 y x)) h9
  let v11 := M y x
  have h12 := h x v11 v4
  let v13 := M x v11
  T (T (T (T (T h12 h10) (h v7 v4 v13)) (C (T (T (C (C (T (T h1 (C (T (T (C h1 h3) (S h5)) h6) h3)) (S h8)) (T (h x v11 z) (C (S (h z y x)) h3))) (R v7)) (S (h (M (M z y) z) y v7))) (S (h z z y))) (R v13))) (h v4 v13 y)) (C (T (T (T (T (T (C (C (T h12 h10) h0) h9) (S (h y v7 v4))) h8) (C (S h6) h3)) (C (T h5 (C h2 h3)) h3)) h2) h0)

@[equational_result]
theorem Equation2663_implies_Equation2060 (G: Type _) [Magma G] (h: Equation2663 G) : Equation2060 G := fun x y =>
  let v0 := M x x
  let v1 := M x y
  let v2 := M v1 y
  let v3 := M v2 v0
  have h4 := h v3 v3
  have h5 := R v3
  let v6 := M v3 v3
  have h7 := R v0
  have h8 := h v2 v0
  have h9 := h v1 y
  have h10 := h x v0
  let v11 := M x v0
  have h12 := h v0 v0
  have h13 := S h12
  let v14 := M v0 v0
  have h15 := h x v3
  have h16 := S h15
  let v17 := M x v3
  T (T h15 (C (T (T (T (T (h (M v17 v17) v3) (C (C h16 h16) h5)) (C (T (T (T h12 (C (T (T (T (h (M v14 v14) v0) (C (C h13 h13) h7)) (C (T (C (C h10 h10) h7) (S (h (M v11 v11) v0))) h7)) (S h10)) h7)) (C (T (T (T (h x y) (C (C h9 h9) (R y))) (S (h (M v2 v2) y))) (C h8 h8)) h7)) (S (h v6 v0))) h5)) (C (C h4 h4) h5)) (S (h (M v6 v6) v3))) h5)) (S h4)

@[equational_result]
theorem Equation2105_implies_Equation655 (G: Type _) [Magma G] (h: Equation2105 G) : Equation655 G := fun x y z =>
  let v0 := M (M z y) z
  have h1 := R v0
  have h2 := h y z x
  have h3 := S h2
  let v4 := M x x
  have h5 := R v4
  have h6 := h v0 v0 x
  let v7 := M v0 v0
  have h8 := h v7 v0 x
  have h9 := h y z v0
  have h10 := h v4 v0 x
  have h11 := h v0 v4 x
  have h12 := R x
  have h13 := S h10
  have h14 := C (T (C (S h9) h1) (C h2 h1)) h5
  have h15 := C (T (T h2 (C (T h6 (C (C (T (T h8 h14) h13) h1) h5)) h5)) (S h11)) h1
  T (T (h x (M y v0) v0) (C (T (C (C (T (T (T h15 h8) h14) h13) h12) h15) (S (h x x v0))) (R v7))) (C h12 (C (T (T h11 (C (T (C (C (T (T h10 (C (T (C h3 h1) (C h9 h1)) h5)) (S h8)) h1) h5) (S h6)) h5)) h3) h1))

@[equational_result]
theorem Equation2880_implies_Equation2688 (G: Type _) [Magma G] (h: Equation2880 G) : Equation2688 G := fun x y z =>
  let v0 := M z z
  let v1 := M x y
  let v2 := M (M v1 v0) y
  have h3 := R v2
  let v4 := M v2 (M v2 v2)
  have h5 := R x
  have h6 := R v0
  have h7 := h v2 v1 v0
  let v8 := M v1 v1
  let v9 := M (M v2 v8) v0
  have h10 := R y
  have h11 := h x v1 v0
  let v12 := M (M x v8) v0
  let v13 := M x (M y y)
  T (T (h x y v2) (C (C (T (T (h v13 z x) (C (C (T (T (T (T (T (T (T (h (M v13 v0) z x) (C (T (C (S (h x y v0)) h5) (C h11 h5)) h5)) (S (h v12 z x))) (h v12 z y)) (C (T (T (C (S h11) h10) (h v1 z y)) (C h7 h10)) h10)) (S (h v9 z y))) (h v9 z v0)) (C (T (T (C (S h7) h6) (C (h v2 v2 v0) h6)) (S (h v4 z v0))) h6)) h5) h5)) (S (h v4 z x))) h3) h3)) (S (h v2 v2 v2))

@[equational_result]
theorem Equation3120_implies_Equation759 (G: Type _) [Magma G] (h: Equation3120 G) : Equation759 G := fun x y z =>
  let v0 := M y x
  let v1 := M v0 z
  let v2 := M z v1
  let v3 := M y v2
  have h4 := R v3
  have h5 := R y
  have h6 := R v1
  have h7 := h z v0 v1
  have h8 := C (S h7) h6
  have h9 := h v0 v1 v1
  have h10 := h v0 x v2
  have h11 := S h10
  have h12 := R v2
  have h13 := R x
  have h14 := R v0
  have h15 := h x y v0
  have h16 := h y v0 v0
  have h17 := C (C (C (T h16 (C (S h15) h14)) h13) h12) (T h9 h8)
  T (T (h x y v3) (C (C (T (C (T h10 (C (C (C (T (C h15 h14) (S h16)) h13) h12) (T (C h7 h6) (S h9)))) h5) (C (T (T (T (T (T h17 h11) h9) h8) (h v2 v0 v3)) (C (T (C (T (T (T (T h17 h11) h9) h8) (h v2 y v3)) h4) (S (h y v3 v3))) h4)) h5)) h4) h4)) (S (h v3 y v3))

@[equational_result]
theorem Equation3607_implies_Equation4656 (G: Type _) [Magma G] (h: Equation3607 G) : Equation4656 G := fun x y z =>
  let v0 := M x z
  let v1 := M v0 z
  have h2 := h v0 z v1
  let v3 := M x y
  let v4 := M z v1
  let v5 := M v4 v0
  have h6 := h v1 v5 v3
  let v7 := M (M v5 v3) v1
  have h8 := R v3
  let v9 := M (M y v3) x
  have h10 := h x y v3
  have h11 := R v9
  have h12 := h x z v1
  have h13 := R z
  let v14 := M v4 x
  T (T (T (T (h v3 y v3) (C h8 (T (C (T (C (R y) h10) (S (h v9 x y))) h8) (C (T (T (T (T (h v9 x z) (C h13 (C (T (T (T h12 (h v1 v14 v0)) (C (R v0) (C (T (h v14 v0 z) (C h13 (S h12))) (R v1)))) (S (h v1 z v0))) h11))) (S (h v9 v1 z))) (C h11 (T (T h2 h6) (C h10 (R v7))))) (S (h v7 v3 v9))) h8)))) (S (h v3 v7 v3))) (S h6)) (S h2)

@[equational_result]
theorem Equation3930_implies_Equation377 (G: Type _) [Magma G] (h: Equation3930 G) : Equation377 G := fun x y =>
  have h0 := R x
  let v1 := M x y
  have h2 := h x y v1
  have h3 := h y v1 x
  have h4 := S h3
  have h5 := R y
  let v6 := M v1 x
  have h7 := h v1 x v6
  have h8 := R v1
  have h9 := h v1 (M x v6) x
  have h10 := h x v1 x
  have h11 := h v1 x v1
  have h12 := C h5 (T (C (T (T h11 (C (C h8 h10) h8)) (S h9)) h8) (S h7))
  have h13 := C h12 h5
  have h14 := C h5 (T h7 (C (T (T h9 (C (C h8 (S h10)) h8)) (S h11)) h8))
  have h15 := h y v6 v1
  have h16 := C h14 h5
  have h17 := C h0 (T (T (C (T (T (T h3 h16) (S h15)) h14) h5) h13) h4)
  T (T h2 (C (C h0 (T (T h3 h16) (C (T (T (T h12 h15) h13) h4) h5))) h0)) (C (T (T (T h17 (h x (M y v1) y)) (C h17 h0)) (S h2)) h0)

@[equational_result]
theorem Equation627_implies_Equation1630 (G: Type _) [Magma G] (h: Equation627 G) : Equation1630 G := fun x y =>
  have h0 := h y x x
  have h1 := S h0
  let v2 := M x x
  let v3 := M v2 x
  let v4 := M y v3
  have h5 := R v4
  have h6 := R v2
  have h7 := h v2 y v4
  let v8 := M v2 y
  let v9 := M x (M (M y v8) v8)
  have h10 := h x y v8
  have h11 := R x
  let v12 := M v2 v8
  have h13 := S (h v12 v2 v8)
  have h14 := S (h v8 x x)
  let v15 := M v8 v3
  have h16 := R v12
  have h17 := C h16 (T (h v12 v8 v15) (C h16 (C h16 (T (C h14 (R v15)) h14))))
  T (T (T (h x v12 v12) (C h11 (T (T (T (C h11 (T (T (C (T h17 h13) h16) h17) h13)) (C h11 (T (C h6 (C h6 (T h0 (C h0 h5)))) (S h7)))) (C h11 (C h11 (T h10 (C h10 (R v9)))))) (S (h x x v9))))) h7) (C h6 (C h6 (T (C h1 h5) h1)))

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

