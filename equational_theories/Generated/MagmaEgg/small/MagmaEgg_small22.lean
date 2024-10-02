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
theorem Equation3620_implies_Equation3994 (G: Type _) [Magma G] (h: Equation3620 G) : Equation3994 G := fun x y z =>
  let v0 := M x y
  let v1 := M z v0
  have h2 := h v1 z x
  have h3 := S h2
  have h4 := R v1
  let v5 := M v1 z
  have h6 := h z v0 z
  have h7 := S h6
  have h8 := h v1 z v1
  have h9 := S h8
  let v10 := M v5 v1
  have h11 := R v10
  have h12 := R z
  have h13 := h v10 v5 z
  have h14 := R x
  have h15 := h x y v1
  T (T (T (T (T h15 (h v1 (M (M v1 y) x) v1)) (C h4 (C (S h15) h4))) (h v1 (M v0 v1) x)) (C h14 (C (T (T (C h14 (T (T (h v0 v1 v5) (C (R v5) (T (T (T (h v10 v0 z) (C h12 h9)) (C h12 (T h8 (C h6 h11)))) (S h13)))) (C (T (T h2 (h x (M (M x z) v1) x)) (C h14 (C h3 h14))) (T (T h13 (C h12 (T (C h7 h11) h9))) h7)))) (S (h v1 (M v5 x) x))) (S (h x z v1))) h4))) h3

@[equational_result]
theorem Equation3804_implies_Equation4210 (G: Type _) [Magma G] (h: Equation3804 G) : Equation4210 G := fun x y z =>
  let v0 := M z y
  let v1 := M v0 x
  let v2 := M v1 z
  let v3 := M v1 y
  let v4 := M y z
  let v5 := M v0 v1
  let v6 := M x z
  let v7 := M v0 v0
  have h8 := h z y z
  let v9 := M z z
  let v10 := M x y
  let v11 := M v2 v6
  have h12 := R v11
  T (T (T (T (T (T (h x y z) (h v0 v6 v2)) (C h12 (S (h v1 y z)))) (h v11 v3 v2)) (C (R (M v2 v3)) (T (T (T (T (T (T (C h12 (h v1 z z)) (S (h v9 v6 v2))) (S (h x z z))) (h x z y)) (h v4 v10 v1)) (C (T (T (T (T (T (T (T (C (h v0 x x) (h x y x)) (S (h v10 v1 (M x x)))) (S (h v0 y x))) (h v0 y z)) (C (T (T (T (T h8 (h v0 v9 v0)) (C (S h8) (R v7))) (h v0 v7 v1)) (C (S (h v0 x v0)) (R v5))) (h v0 z x))) (S (h v6 v5 v1))) (h v6 v5 (M v1 x))) (C (S (h v0 x v1)) (S (h v1 z x)))) (R (M v4 v1)))) (S (h v4 v2 v1))))) (S (h v4 v3 v2))) (S (h v1 z y))

@[equational_result]
theorem Equation2105_implies_Equation2602 (G: Type _) [Magma G] (h: Equation2105 G) : Equation2602 G := fun x y z =>
  let v0 := M z z
  let v1 := M v0 x
  let v2 := M (M y v1) y
  have h3 := R v0
  have h4 := R v2
  have h5 := S (h v0 z x)
  let v6 := M x x
  have h7 := R v6
  have h8 := R z
  have h9 := h z z z
  have h10 := C (T (h z v0 z) (C (S h9) h3)) h8
  let v11 := M v2 v2
  have h12 := R y
  let v13 := M v1 v1
  T (T (h x y v0) (C (T (h (M (M y x) y) v2 z) (C (C (T (T (T (C h4 (C (C h12 (T (T (T (h x x z) (C (C (T (T (h v6 z x) (C (T (C (T (C h9 h7) (S (h z v0 x))) h8) h10) h7)) h5) (R x)) h3)) (C (T (h v1 v1 z) (C (C (T (T (h v13 z x) (C (T (C (T (C h9 (R v13)) (S (h z v0 v1))) h8) h10) h7)) h5) (R v1)) h3)) h3)) (S (h v1 v0 z)))) h12)) (h v11 z x)) (C (T (C (T (C h9 (R v11)) (S (h z v0 v2))) h8) h10) h7)) h5) h4) h3)) (R (M v0 v0)))) (S (h v2 v0 v0))

@[equational_result]
theorem Equation684_implies_Equation1876 (G: Type _) [Magma G] (h: Equation684 G) : Equation1876 G := fun x y z =>
  let v0 := M z y
  let v1 := M y z
  let v2 := M x v1
  let v3 := M v2 v0
  have h4 := S (h v3 v3 x)
  let v5 := M v3 (M (M v3 x) x)
  let v6 := M v0 v3
  have h7 := S (h v0 v0 x)
  let v8 := M v0 (M (M v0 x) x)
  have h9 := R v0
  have h10 := S (h v1 v1 v3)
  let v11 := M v1 (M (M v1 v3) v3)
  let v12 := M z (M (M z x) x)
  have h13 := h z z x
  have h14 := R z
  let v15 := M v1 (M (M v1 x) x)
  let v16 := M z v1
  have h17 := h v1 v1 x
  T (T (T (h x v1 v11) (C (T (h v1 z v1) (C h14 (T (T (T (C (R v1) (C (R v16) (T h17 (C h17 (R v15))))) (S (h v16 v1 v15))) (C h14 (C (R y) (T h13 (C h13 (R v12)))))) (S (h y z v12))))) (C (R x) (T (C h10 (R v11)) h10)))) (C h9 (T (T (T (h v2 v0 v8) (C h9 (C (R v2) (T (C h7 (R v8)) h7)))) (h v6 v3 v5)) (C (R v3) (C (R v6) (T (C h4 (R v5)) h4)))))) (S (h v3 v0 v3))

@[equational_result]
theorem Equation711_implies_Equation725 (G: Type _) [Magma G] (h: Equation711 G) : Equation725 G := fun x y z =>
  let v0 := M z x
  let v1 := M v0 z
  have h2 := S (h v1 v1 x)
  let v3 := M v1 (M (M v1 x) x)
  have h4 := R y
  let v5 := M z (M v0 x)
  have h6 := h z v0 v5
  have h7 := S h6
  have h8 := R v5
  have h9 := h z z x
  have h10 := R v0
  have h11 := C h10 (C h10 (T h9 (C h9 h8)))
  have h12 := R x
  have h13 := S h9
  have h14 := C h10 (C (C (T h6 (C h10 (C h10 (T (C h13 h8) h13)))) h12) h12)
  have h15 := S (h x x x)
  let v16 := M x (M (M x x) x)
  have h17 := C h10 (C h10 (T (C h15 (R v16)) h15))
  have h18 := h x v0 v16
  T (T (T (T (T h18 h17) h14) (C h10 (T (T (T (C (C (T h11 h7) h12) (T (T h18 h17) h14)) (S (h (M v0 v1) v0 x))) h11) h7))) (h v1 y v3)) (C h4 (C h4 (T (C h2 (R v3)) h2)))

@[equational_result]
theorem Equation1507_implies_Equation2279 (G: Type _) [Magma G] (h: Equation1507 G) : Equation2279 G := fun x y z =>
  let v0 := M z y
  let v1 := M y v0
  let v2 := M x v1
  let v3 := M v2 z
  have h4 := S (h z v2 v3)
  let v5 := M v3 v2
  let v6 := M v0 (M v0 v3)
  let v7 := M v3 v5
  have h8 := h y z z
  let v9 := M z (M z z)
  have h10 := h v1 x v3
  let v11 := M v3 (M v3 x)
  let v12 := M z x
  T (T (T (T (h x z y) (C (T (T (T (T (h v12 z x) (C (T (T (T (T (h (M z v12) v2 x) (C (T (S (h v1 x z)) h10) (R (M x (M x v2))))) (S (h v11 v2 x))) (h v11 v2 v3)) (C (S h10) (R v7))) (T (T (T (T (h (M x (M x z)) v0 x) (C (T (S (h y z x)) h8) (R (M x (M x v0))))) (S (h v9 v0 x))) (h v9 v0 y)) (C (S h8) (R (M y v1)))))) (S (h v7 v1 y))) (h v7 v3 v0)) (C h4 (R v6))) (R (M y (M y z))))) (S (h v6 z y))) (h v6 v5 v3)) (C (S (h v2 v3 v0)) h4)

@[equational_result]
theorem Equation2789_implies_Equation562 (G: Type _) [Magma G] (h: Equation2789 G) : Equation562 G := fun x y z =>
  let v0 := M z x
  let v1 := M y v0
  let v2 := M z v1
  let v3 := M y v2
  have h4 := R v3
  have h5 := h y z v3
  have h6 := R z
  have h7 := S (h y x v3)
  let v8 := M x y
  have h9 := T (h v3 (M (M x v3) v8) v3) (C (C h7 h7) h4)
  let v10 := M x z
  have h11 := h z x v2
  have h12 := h y x v1
  have h13 := h z x v0
  T (T (T (T (T (h x z z) (C (T (C (C h13 h13) (R v0)) (S (h v0 (M (M x v0) v10) v0))) h6)) (C (T (h v0 y y) (C (T (T (T (C (C h12 h12) (R v1)) (S (h v1 (M (M x v1) v8) v1))) (h v1 z z)) (C (T (C (C h11 h11) (R v2)) (S (h v2 (M (M x v2) v10) v2))) h6)) (T (h y v3 v3) (C (T (C (R (M v3 v3)) (T (C h9 (R y)) (S (h v2 y y)))) (S (h v2 y v2))) h9)))) h6)) (S (h (M (M y y) v3) v2 z))) (C (C h5 h5) h4)) (S (h v3 (M (M z v3) (M z y)) v3))

@[equational_result]
theorem Equation2958_implies_Equation572 (G: Type _) [Magma G] (h: Equation2958 G) : Equation572 G := fun x y z =>
  let v0 := M x y
  let v1 := M z (M z v0)
  let v2 := M y v1
  have h3 := R y
  let v4 := M v2 y
  have h5 := S (h v2 x v2)
  let v6 := M (M x (M x v2)) v2
  have h7 := R v1
  have h8 := S (h y z y)
  let v9 := M (M z (M z y)) y
  have h10 := R x
  let v11 := M v1 x
  have h12 := S (h v1 x v1)
  let v13 := M (M x (M x v1)) v1
  let v14 := M (M v1 v11) x
  have h15 := h x v1 x
  T (T (h x x y) (C (T (T (T (T (T (T (T (T (C (C (T h15 (C (R v14) h15)) (R v0)) h10) (S (h v0 v14 x))) (h v0 v1 x)) (C (T (T (S (h v11 z v0)) (h v11 v13 v1)) (C (C (T (C (R v13) h12) h12) (R v11)) h7)) h10)) (S (h v1 v1 x))) (h v1 v9 y)) (C (C (T (C (R v9) h8) h8) h7) h3)) (h v4 v6 v2)) (C (C (T (C (R v6) h5) h5) (R v4)) (R v2))) h3)) (S (h v2 v2 y))

@[equational_result]
theorem Equation3789_implies_Equation41 (G: Type _) [Magma G] (h: Equation3789 G) : Equation41 G := fun x y z =>
  let v0 := M y z
  have h1 := h y x x
  have h2 := h x y x
  have h3 := S h2
  let v4 := M x x
  let v5 := M y x
  have h6 := h v4 v5 v4
  have h7 := S h6
  have h8 := h x x y
  have h9 := h x x x
  have h10 := C h9 h8
  have h11 := h x x z
  have h12 := S h11
  have h13 := S h9
  let v14 := M z x
  have h15 := h v4 v14 v4
  have h16 := T (T (T (T h15 (C h13 h12)) h10) h7) h3
  have h17 := h v14 v4 v4
  have h18 := C h13 (S h8)
  have h19 := T (T (T (T h2 h6) h18) (C h9 h11)) (S h15)
  T (T (T (T h8 (h v5 v4 v0)) (C (C (R v0) (T (T (T (T (T (T (T h1 (C h19 h19)) (S h17)) h12) h9) h10) h7) h3)) (T (T (T (T (T (T (T h6 h18) h13) h11) h17) (C h16 h16)) (S h1)) (h y x z)))) (S (h (M x y) (M z y) v0))) (S (h y z x))

@[equational_result]
theorem Equation3804_implies_Equation4369 (G: Type _) [Magma G] (h: Equation3804 G) : Equation4369 G := fun x y z =>
  let v0 := M y z
  let v1 := M x v0
  let v2 := M y x
  let v3 := M z v1
  let v4 := M v1 v1
  have h5 := h x v0 v0
  let v6 := M v0 v0
  have h7 := h x v0 x
  let v8 := M x x
  let v9 := M z v8
  let v10 := M y y
  let v11 := M v2 y
  let v12 := M y v0
  let v13 := M v0 v12
  have h14 := h y z z
  T (T (T (T (T h7 (h v1 v8 z)) (C (R v9) (T (T (T (T (T (h v1 z v2) (C (h v2 z y) (T (T (T (S (h y v0 x)) (h y v0 v0)) (h v6 v12 v0)) (C (R v13) (T (T (C (R v6) h14) (S (h (M z z) v0 v0))) (S h14)))))) (S (h v13 v11 v0))) (C (T (C (h y z y) (R v12)) (S (h y v10 v0))) (R v11))) (S (h v2 v10 y))) (S (h y x y))))) (h v9 v2 v1)) (C (R (M v1 v2)) (T (T (C (T (h z v8 v1) (C (S h7) (R v3))) (T (T h5 (h v6 v1 v1)) (C (R v4) (S h5)))) (S (h v4 v3 v1))) (S (h z v1 v1))))) (S (h z v2 v1))

@[equational_result]
theorem Equation492_implies_Equation4216 (G: Type _) [Magma G] (h: Equation492 G) : Equation4216 G := fun x y z =>
  let v0 := M z y
  let v1 := M v0 z
  let v2 := M v1 x
  let v3 := M x y
  have h4 := h x v1 v3
  have h5 := S h4
  have h6 := h z y z
  have h7 := R v0
  have h8 := C h7 (S h6)
  have h9 := h y v0 z
  have h10 := h y v3 x
  have h11 := h x y x
  have h12 := R v3
  have h13 := R x
  have h14 := h v3 x v3
  have h15 := S h9
  have h16 := C h7 h6
  have h17 := R v1
  have h18 := C (T h9 h8) (T (T (T (C h12 (C h12 (C h17 (T h4 (C h17 (T (C h13 (C h12 (C h12 (T (T (T h16 h15) h10) (C h12 (S h11)))))) (S h14))))))) (S (h v3 v3 v1))) h14) (C h13 (C h12 (C h12 (T (T (T (C h12 h11) (S h10)) h9) h8)))))
  have h19 := R v2
  have h20 := h y v2 v3
  T (C h13 (T h20 (C h19 (T (T (T h18 h5) (h x v1 v2)) (C h17 (T (C h13 (C h19 (C h19 (T (T (T h16 h15) h20) (C h19 (T h18 h5)))))) (S (h v2 x v2)))))))) (S (h v2 x v1))

@[equational_result]
theorem Equation2105_implies_Equation3500 (G: Type _) [Magma G] (h: Equation2105 G) : Equation3500 G := fun x y z =>
  let v0 := M z z
  let v1 := M v0 y
  let v2 := M y v1
  let v3 := M x x
  have h4 := R v3
  have h5 := R v1
  have h6 := h v3 x x
  have h7 := R x
  have h8 := h x x x
  have h9 := S h8
  have h10 := h x v3 x
  let v11 := M v1 v1
  have h12 := R y
  have h13 := h x v3 y
  let v14 := M y y
  have h15 := R v14
  have h16 := h v14 x x
  T (T (T h6 (C (T (C (T (C h8 h4) (S h10)) h7) (C (T h13 (C h9 h15)) h7)) h4)) (S h16)) (C h12 (T (T (h y y v2) (C (T (h (M v14 y) v1 x) (C (C (T (T (T (T (C h5 (C (T (T (T h16 (C (C (T (C h8 h15) (S h13)) h7) h4)) (C (C (T (h x v3 z) (C h9 (R v0))) h7) h4)) (S (h v0 x x))) h12)) (h v11 x x)) (C (C (T (C h8 (R v11)) (S (h x v3 v1))) h7) h4)) (C (C (T h10 (C h9 h4)) h7) h4)) (S h6)) h5) h4)) (R (M v2 v2)))) (S (h v1 v3 v2))))

@[equational_result]
theorem Equation2789_implies_Equation3794 (G: Type _) [Magma G] (h: Equation2789 G) : Equation3794 G := fun x y z =>
  let v0 := M z y
  let v1 := M z x
  let v2 := M v1 v0
  have h3 := h v2 (M (M x v2) (M x v1)) v2
  have h4 := S h3
  have h5 := R v2
  have h6 := h v1 x v2
  have h7 := C (C h6 h6) h5
  have h8 := S h6
  have h9 := T h3 (C (C h8 h8) h5)
  have h10 := R v0
  have h11 := T h7 h4
  have h12 := h v0 v1 v1
  have h13 := S h12
  have h14 := R v1
  have h15 := C h9 h14
  have h16 := T h15 h13
  T (T (T (C (T (T (h x v2 v1) (C (C h16 (S (h y z x))) (T (T (h v1 v2 v2) (C (T (T (T (C (T (C h5 h9) (C h5 (T (T h7 h4) (C h14 (T h12 (C h11 h14)))))) h16) (S (h (M v2 v1) v1 v0))) h15) h13) h9)) (C h10 h11)))) (C (R (M v0 y)) (C h10 h9))) (R y)) (S (h (M (M v1 v1) v2) v0 y))) h7) h4

@[equational_result]
theorem Equation2944_implies_Equation1304 (G: Type _) [Magma G] (h: Equation2944 G) : Equation1304 G := fun x y z =>
  let v0 := M (M x z) z
  let v1 := M v0 y
  have h2 := R v1
  have h3 := h y v0 v1
  have h4 := S h3
  have h5 := h v0 x v0
  have h6 := S h5
  let v7 := M (M x (M x v0)) v0
  have h8 := R v7
  have h9 := C (C (T (C h8 h6) h6) h2) h2
  have h10 := h v0 v7 v1
  have h11 := C (T h10 h9) h2
  have h12 := R z
  have h13 := h x x x
  have h14 := S h13
  let v15 := M (M x (M x x)) x
  have h16 := R v15
  have h17 := C (C (T (C h16 h14) h14) h12) h12
  have h18 := h x v15 z
  have h19 := S h10
  have h20 := C (C (T h5 (C h8 h5)) h2) h2
  have h21 := S h18
  have h22 := C (C (T h13 (C h16 h13)) h12) h12
  T (T (T (T (T h18 h17) h10) h9) (C (T h11 (C (T (T (T h20 h19) h22) h21) (C (T h22 h21) (T h3 (C (T h20 h19) h2))))) h2)) (C (T (C (T (T (T h18 h17) h10) h9) (C (T h18 h17) (T h11 h4))) h4) h2)

@[equational_result]
theorem Equation4176_implies_Equation3737 (G: Type _) [Magma G] (h: Equation4176 G) : Equation3737 G := fun x y z =>
  let v0 := M y z
  let v1 := M x z
  have h2 := R v0
  let v3 := M z v1
  have h4 := R y
  have h5 := R v3
  let v6 := M x y
  have h7 := R x
  have h8 := C (S (h x y z)) h7
  have h9 := h z v0 x
  have h10 := S (h z v0 y)
  let v11 := M z v0
  T (T (T (h x y v0) (C (T (C (T (T (h y v0 v0) (C (T (C (T (T (T (h v0 v0 y) (C (T (C (h v0 y z) h2) (S (h z v0 v0))) h4)) (h v11 y z)) (C (T (h v0 v11 y) (C (S (h y z v0)) h4)) (R z))) h4) h10) h2)) (C (T h9 h8) h2)) h7) (S (h v0 v6 x))) h2)) (C (T (T (C h2 (T (h x y y) (C (T (T (T (T (T (C (T (h y y y) (C (T (T (T (C (h y y z) h4) h10) h9) h8) h4)) h7) (S (h y v6 x))) (h y v6 v3)) (C (S (h v3 x y)) h5)) (C (h v3 x z) h5)) (S (h z v1 v3))) h4))) (h v0 (M v3 y) v1)) (C (C (S (h y z v1)) h2) (R v1))) h2)) (S (h v1 v0 v0))

@[equational_result]
theorem Equation684_implies_Equation3211 (G: Type _) [Magma G] (h: Equation684 G) : Equation3211 G := fun x y z =>
  let v0 := M (M y z) z
  let v1 := M v0 x
  let v2 := M y (M (M y v1) v1)
  let v3 := M v1 y
  have h4 := h y y v1
  have h5 := R v3
  have h6 := R y
  have h7 := S (h y y v0)
  let v8 := M y (M (M y v0) v0)
  have h9 := S (h v3 v3 v3)
  let v10 := M v3 (M (M v3 v3) v3)
  have h11 := R v1
  have h12 := S (h v1 v1 x)
  let v13 := M v1 (M (M v1 x) x)
  let v14 := M x v1
  have h15 := S (h x x x)
  let v16 := M x (M (M x x) x)
  have h17 := R x
  T (T (T (h x y z) (C h6 (T (T (T (C h17 (T (T (T (h v0 x v16) (C h17 (C (R v0) (T (C h15 (R v16)) h15)))) (h v14 v1 v13)) (C h11 (C (R v14) (T (C h12 (R v13)) h12))))) (S (h v1 x v1))) (h v1 v3 v10)) (C h5 (T (C h11 (T (T (T (C h9 (R v10)) h9) (h v3 y v8)) (C h6 (C h5 (T (C h7 (R v8)) h7))))) (S (h y v1 y))))))) (C h6 (C h5 (T h4 (C h4 (R v2)))))) (S (h v3 y v2))

@[equational_result]
theorem Equation725_implies_Equation1876 (G: Type _) [Magma G] (h: Equation725 G) : Equation1876 G := fun x y z =>
  let v0 := M y z
  let v1 := M x v0
  have h2 := h y z v1
  have h3 := S h2
  have h4 := h (M z (M (M v1 y) v1)) x z
  have h5 := S h4
  have h6 := R z
  have h7 := R x
  have h8 := C h7 (C h7 (C h2 h6))
  have h9 := R v1
  let v10 := M z y
  have h11 := h x v1 v10
  let v12 := M (M v10 x) v10
  let v13 := M v1 v12
  have h14 := C h7 (C h7 (C h3 h6))
  have h15 := R v0
  have h16 := h x v0 v10
  have h17 := h (M v0 v12) x v0
  have h18 := h x v1 y
  T h18 (C h9 (T (T (T (T (T (h (M v1 (M (M y x) y)) x v1) (C h7 (T (T (C h7 (T (T (C (S h18) h9) h8) h5)) (C h7 (T (T h4 h14) (C h7 (C h16 h15))))) (S h17)))) (C h7 (T (T h17 (C h7 (T (T (C h7 (C (S h16) h15)) h8) h5))) (C h7 (T (T h4 h14) (C h11 h9)))))) (S (h v13 x v1))) (h v13 z v1)) (C h6 (T (C h6 (T (T (C (S h11) h9) h8) h5)) h3))))

@[equational_result]
theorem Equation1993_implies_Equation2146 (G: Type _) [Magma G] (h: Equation1993 G) : Equation2146 G := fun x y z =>
  let v0 := M x z
  let v1 := M y y
  let v2 := M v1 z
  let v3 := M v2 v1
  have h4 := h v1 z z
  let v5 := M z (M z z)
  let v6 := M v0 v0
  let v7 := M v2 v6
  let v8 := M x x
  have h9 := R (M v1 v8)
  let v10 := M v1 v6
  have h11 := R v10
  let v12 := M y v6
  have h13 := h y y v0
  have h14 := R (M v2 v8)
  let v15 := M z (M v1 v1)
  T (h x z v1) (C (T (T (T (T (R v15) (h v15 v2 x)) (C h14 (S (h v1 z v1)))) (C h14 (T (T (T (C h13 (T (h y v1 v0) (C h11 (T (T (h (M y v1) v1 x) (C h9 (T (S (h y y y)) h13))) (S (h v12 v1 x)))))) (S (h v10 v12 y))) (h v10 v7 v2)) (C (S (h v2 v2 v0)) (T (C h11 (T (T (h v7 v1 x) (C h9 (T (T (T (C (R v7) h4) (S (h v5 v2 v0))) (h v5 v2 y)) (C (R v3) (S h4))))) (S (h v3 v1 x)))) (S (h v2 v1 v0))))))) (S (h v2 v2 x))) (R v0))

@[equational_result]
theorem Equation2383_implies_Equation1131 (G: Type _) [Magma G] (h: Equation2383 G) : Equation1131 G := fun x y z =>
  let v0 := M z x
  let v1 := M y v0
  let v2 := M v1 z
  let v3 := M x v2
  let v4 := M y v2
  let v5 := M x (M v4 v3)
  have h6 := R y
  have h7 := h v2 x v4
  let v8 := M v1 (M v2 v2)
  have h9 := R v1
  have h10 := h z v1 v2
  let v11 := M z (M z v0)
  let v12 := M v1 v3
  have h13 := h x v12 v11
  have h14 := R v11
  have h15 := h z v1 x
  have h16 := h x z z
  have h17 := R v12
  have h18 := R z
  have h19 := S h15
  T (T (T (T (T h13 (C (T (C h17 (T (C h14 h19) (S h16))) h19) h14)) (h (M z v11) z y)) (C (T (T (C h18 (C h6 (C h18 (T (C (T h15 (C h17 (T h16 (C h14 h15)))) h14) (S h13))))) (C (T h10 (C (R v8) (C h9 h10))) h9)) (S (h v2 v8 v1))) h6)) (C (T h7 (C (R v5) (C h6 h7))) h6)) (S (h v4 v5 y))

@[equational_result]
theorem Equation2779_implies_Equation2725 (G: Type _) [Magma G] (h: Equation2779 G) : Equation2725 G := fun x y z =>
  let v0 := M z z
  let v1 := M y x
  let v2 := M v1 v0
  have h3 := h v0 x v2
  let v4 := M (M x v2) (M v0 v2)
  have h5 := R x
  let v6 := M x z
  have h7 := R z
  have h8 := R v0
  let v9 := M v0 v0
  have h10 := h z z z
  let v11 := M v2 y
  have h12 := h x z v11
  let v13 := M (M z v11) (M x v11)
  T (T (T (T (T (T (T h12 (C (T (T (h v13 x v0) (C (C (R (M x v0)) (T (C (T (h v13 z z) (C (C h8 (S h12)) (h z x z))) h8) (S (h (M v6 v0) v0 x)))) h5)) (S (h v6 x v0))) h7)) (C (R v6) (T h10 (C (T (T (h v9 v0 v0) (C (C (R v9) (T (C (T (h v9 z z) (C (C h8 (S h10)) h10)) h8) (S (h v9 v0 z)))) h8)) (S (h v0 v0 v0))) h7)))) (h (M v6 (M v0 z)) x x)) (C (C (R (M x x)) (T (S (h v0 x z)) h3)) h5)) (S (h v4 x x))) (h v4 y x)) (C (C (R v1) (S h3)) (R y))

@[equational_result]
theorem Equation3193_implies_Equation166 (G: Type _) [Magma G] (h: Equation3193 G) : Equation166 G := fun x y =>
  let v0 := M x x
  have h1 := R v0
  have h2 := h x x x
  have h3 := R x
  have h4 := h v0 v0 x
  have h5 := S h4
  have h6 := h v0 x x
  have h7 := C h6 h1
  have h8 := h x v0 v0
  have h9 := T (C (T h8 (C (C (T (T (C (T h7 h5) h1) h7) h5) h3) h3)) h3) (S h2)
  have h10 := S (h y y x)
  have h11 := R y
  have h12 := C (C (C h11 h9) h11) h11
  have h13 := C (S h6) h1
  have h14 := C (T (C (C (T (T h4 h13) (C (T h4 h13) h1)) h3) h3) (S h8)) h3
  let v15 := M y x
  have h16 := S (h v15 v15 y)
  have h17 := R v15
  have h18 := h v15 y x
  have h19 := C (C (T (T (C (T (T (C h18 h17) h16) h18) h17) h16) (C h11 (T h2 h14))) h11) h11
  have h20 := h y v15 v15
  T (T (T h2 h14) (h v0 y y)) (C (C (T (C (T (T (T (T (C (T (T h20 h19) h12) h11) h10) h20) h19) h12) h11) h10) h9) h1)

@[equational_result]
theorem Equation3193_implies_Equation4385 (G: Type _) [Magma G] (h: Equation3193 G) : Equation4385 G := fun x y =>
  have h0 := h x x x
  have h1 := R x
  let v2 := M x x
  have h3 := h v2 v2 x
  have h4 := S h3
  have h5 := R v2
  have h6 := h v2 x x
  have h7 := C h6 h5
  have h8 := h x v2 v2
  have h9 := T (C (T h8 (C (C (T (T (C (T h7 h4) h5) h7) h4) h1) h1)) h1) (S h0)
  have h10 := S (h y y (M x v2))
  have h11 := R y
  have h12 := C (S h6) h5
  have h13 := C (T (C (C (T (T h3 h12) (C (T h3 h12) h5)) h1) h1) (S h8)) h1
  let v14 := M y x
  have h15 := S (h v14 v14 y)
  have h16 := R v14
  have h17 := C (h v14 y x) h16
  have h18 := C (C (T (T (T (C (T h17 h15) h16) h17) h15) (C h11 (T (T h0 h13) (C h1 (T h0 h13))))) h11) h11
  have h19 := h y v14 v14
  T (T (C h1 h9) (h v2 y y)) (C (C (T (C (T (T (T (C (T h19 h18) h11) h10) h19) h18) h11) h10) h9) h9)

@[equational_result]
theorem Equation3384_implies_Equation4367 (G: Type _) [Magma G] (h: Equation3384 G) : Equation4367 G := fun x y z w =>
  let v0 := M y z
  let v1 := M w z
  let v2 := M z z
  let v3 := M w v2
  have h4 := h v0 v3 v1
  have h5 := h w z v3
  have h6 := h y z (M y v2)
  let v7 := M y v1
  let v8 := M v2 v2
  have h9 := h v2 z y
  have h10 := h v2 z w
  have h11 := T (S h10) h9
  have h12 := R v7
  have h13 := T (T (T (T (h w v2 v7) (h v7 (M w v8) v7)) (C h12 (C h12 (C h11 h11)))) (S (h v7 (M y v8) v7))) (S (h y v2 v7))
  have h14 := R v1
  have h15 := S h5
  let v16 := M x v0
  have h17 := T (T (h y v2 v16) (C (R v16) (T (S h9) h10))) (S (h w v2 v16))
  T (T (T (C (R x) (T (T (T (h y z v0) (C (R v0) h17)) h4) (C h14 (C (T (T h6 (C h17 h17)) h15) h15)))) (S (h v1 v1 x))) (h v1 v1 y)) (C (R y) (T (T (C h14 (C (T (T h5 (C h13 h13)) (S h6)) h5)) (S h4)) (S (h w z v0))))

@[equational_result]
theorem Equation3930_implies_Equation4510 (G: Type _) [Magma G] (h: Equation3930 G) : Equation4510 G := fun x y z =>
  let v0 := M x y
  have h1 := R x
  let v2 := M y z
  let v3 := M y v2
  have h4 := T (T (h x v3 y) (C (C h1 (S (h y y z))) h1)) (S (h x y y))
  have h5 := S (h x y z)
  have h6 := h y z y
  have h7 := C (C h1 (S h6)) h1
  let v8 := M z y
  have h9 := h x (M y v8) y
  let v10 := M v0 x
  have h11 := R y
  have h12 := h z y z
  have h13 := R z
  let v14 := M z v2
  have h15 := S (h y v14 z)
  have h16 := C (C h11 h12) h11
  have h17 := C h1 (T (T (T (T (T h6 h16) h15) (h y v14 v10)) (C (C h11 (C (T (T (h z v2 y) (C (C h13 (T (C (T (T h6 h16) h15) h11) (S (h y z v2)))) h13)) (S h12)) (R v10))) h11)) (S (h y v8 v10)))
  T (T (T (T (T (T (T h17 h9) h7) h5) (h x y v2)) (h (M x v3) x v2)) (C (C h4 (T (T (T h17 h9) h7) h5)) h4)) (S (h v0 x y))

@[equational_result]
theorem Equation4176_implies_Equation3729 (G: Type _) [Magma G] (h: Equation4176 G) : Equation3729 G := fun x y z =>
  let v0 := M x y
  let v1 := M z z
  have h2 := R v0
  let v3 := M v0 v1
  have h4 := R v3
  have h5 := R z
  have h6 := T (C (T (h y v0 z) (C (S (h z x y)) h5)) (R x)) (S (h z z x))
  have h7 := h x y v0
  let v8 := M v1 x
  have h9 := R y
  have h10 := h z z v0
  let v11 := M (M z v0) z
  T (T (T (T h7 (C h6 h2)) (C h10 h2)) (C (T (T (h v11 v0 v1) (C (T (T (T (T (T (T (T (T (h v3 v11 v0) (C (C (S h10) h4) h2)) (C (T (h v1 v3 y) (C (S (h y v0 v1)) h9)) h2)) (S (h y y v0))) (h y y z)) (C (T (T (C (h y z z) h9) (S (h z v1 y))) (h z v1 x)) h5)) (S (h x v8 z))) (h x v8 v0)) (C (S (h v0 v1 x)) (T (T (T h7 (h (M (M y v0) x) v0 v3)) (C (C (R (M v0 v3)) h6) h4)) (S (h v1 v0 v3))))) (R v1))) (S (h (M v1 v0) v0 v1))) h2)) (S (h v0 v1 v0))

@[equational_result]
theorem Equation492_implies_Equation4413 (G: Type _) [Magma G] (h: Equation492 G) : Equation4413 G := fun x y z =>
  let v0 := M y z
  let v1 := M v0 z
  let v2 := M x (M x y)
  have h3 := S (h v1 z v1)
  have h4 := h z v0 y
  have h5 := S h4
  have h6 := h y z y
  have h7 := S (h y y v0)
  have h8 := R v0
  have h9 := R y
  have h10 := C h9 (C h9 (C h8 (T h4 (C h8 (S h6)))))
  have h11 := C h8 (T (T h10 h7) h6)
  have h12 := R v1
  have h13 := h v0 v1 y
  have h14 := C h12 (T (T (T (T h11 h5) (h z v1 v0)) (C h12 (S (h v0 z v0)))) (C h12 (T h13 (C h12 (T h11 h5)))))
  have h15 := R z
  T (h v2 v0 z) (C h8 (T (C (R v2) (C h15 (T (T (T (C h15 (T h13 h14)) h3) (h v1 y x)) (C (T (T (h y z v0) (C h15 (T (T (T (C h9 (C h8 (T (h v1 v1 y) (C h12 (C h12 (T h10 h7)))))) (S (h v0 y v1))) h13) h14))) h3) (R (M v1 v2)))))) (S (h z v2 v1))))

@[equational_result]
theorem Equation1504_implies_Equation1152 (G: Type _) [Magma G] (h: Equation1504 G) : Equation1152 G := fun x y z =>
  let v0 := M x y
  let v1 := M z v0
  let v2 := M v1 z
  let v3 := M y v2
  let v4 := M x v1
  have h5 := h z v1 z
  have h6 := R v1
  have h7 := C h6 (S h5)
  have h8 := h v0 z v2
  have h9 := R y
  have h10 := T (h v1 x y) (C (R v4) (C h9 (T h8 h7)))
  let v11 := M v1 (M v3 v1)
  have h12 := R (M x (M v0 x))
  let v13 := M z x
  T (T (h x z y) (C (T (h v13 x x) (C (T (T (h (M x v13) v1 x) (C (T (T (S (h v0 z x)) h8) h7) (R (M x (M v1 x))))) (S (h z v1 x))) (T (T (T (T (T (h (M x (M x x)) v0 x) (C (S (h y x x)) h12)) (C (T (h y v3 v1) (C (T (C (C h9 (T (C h6 h5) (S h8))) (h y x y)) (S (h v0 y v0))) (R v11))) h12)) (S (h v11 v0 x))) (C h10 (C (R v3) h10))) (S (h v3 v4 v3))))) (R (M y (M z y))))) (S (h v3 z y))

@[equational_result]
theorem Equation684_implies_Equation3120 (G: Type _) [Magma G] (h: Equation684 G) : Equation3120 G := fun x y z =>
  let v0 := M y x
  let v1 := M v0 y
  let v2 := M (M v1 z) z
  have h3 := S (h v2 v2 x)
  let v4 := M v2 (M (M v2 x) x)
  let v5 := M x v2
  have h6 := R x
  let v7 := M x (M (M x x) x)
  have h8 := h x x x
  have h9 := R y
  let v10 := M v1 (M (M v1 v2) v2)
  have h11 := h v1 v1 v2
  let v12 := M y (M v0 x)
  have h13 := h y y x
  have h14 := R v1
  have h15 := R v0
  T (T (T (T (T (h x v0 y) (C h15 (T (T (C h6 (T (C h14 (T (h y v0 y) (C h15 (T (T (T (C h9 (C h14 (T h13 (C h13 (R v12))))) (S (h v1 y v12))) h11) (C h11 (R v10)))))) (S (h v0 v1 v10)))) (C h6 (C h9 (T h8 (C h8 (R v7)))))) (S (h y x v7))))) (h v1 x v2)) (R (M x (M v1 (M v5 v2))))) (C h6 (T (T (S (h v5 v1 z)) (h v5 v2 v4)) (C (R v2) (C (R v5) (T (C h3 (R v4)) h3)))))) (S (h v2 x v2))

@[equational_result]
theorem Equation914_implies_Equation3297 (G: Type _) [Magma G] (h: Equation914 G) : Equation3297 G := fun x y z =>
  let v0 := M z y
  let v1 := M z v0
  let v2 := M y v1
  have h3 := h v2 x v0
  let v4 := M v0 v0
  let v5 := M x v2
  let v6 := M x x
  have h7 := R v6
  have h8 := R x
  have h9 := h v2 x z
  let v10 := M z z
  let v11 := M v5 v10
  have h12 := h x v2 v0
  let v13 := M (M v2 x) v4
  have h14 := R v2
  T (C h8 (T (T (T (T (T (T (T (T (T (h x v2 x) (C h14 (C (T (T (C h14 (T (h x x x) (C h12 (R (M v6 v6))))) (S (h v13 v2 v6))) (h v13 v2 y)) h7))) (S (h (M (M v2 v13) (M y y)) v2 x))) (C (S h12) (T (C (R y) (T (T (T (h y z x) (C (R z) (C (h v0 z v0) h7))) (S (h (M v1 v4) z x))) (C (h v1 y z) (R v4)))) (S (h (M v2 v10) y v0))))) (C h8 (C h9 (R v10)))) (S (h v11 x z))) (h v11 x x)) (C h8 (C (S h9) h7))) (C h8 (C h3 h7))) (S (h (M v5 v4) x x)))) (S h3)

@[equational_result]
theorem Equation1301_implies_Equation2928 (G: Type _) [Magma G] (h: Equation1301 G) : Equation2928 G := fun x y z =>
  let v0 := M x z
  let v1 := M y v0
  let v2 := M v1 z
  let v3 := M v2 y
  let v4 := M (M (M v2 x) v3) x
  have h5 := R y
  have h6 := h v2 v3 x
  have h7 := R z
  let v8 := M (M v1 v1) v0
  have h9 := R v0
  have h10 := h y v1 v0
  let v11 := M (M (M z x) x) x
  let v12 := M (M v0 z) z
  have h13 := h x v12 v11
  have h14 := R v11
  have h15 := R v12
  have h16 := h z x x
  have h17 := h x z z
  have h18 := S h16
  T (T (T (T (T h13 (C h15 (T (C (T (C h18 h15) (S h17)) h14) h18))) (h (M v12 z) y z)) (C h5 (C (T (T (C (C (T (C h15 (T h16 (C (T h17 (C h16 h15)) h14))) (S h13)) h7) h5) (C h9 (T h10 (C (C h10 h9) (R v8))))) (S (h v1 v0 v8))) h7))) (C h5 (T h6 (C (C h6 h5) (R v4))))) (S (h v3 y v4))

@[equational_result]
theorem Equation2779_implies_Equation2714 (G: Type _) [Magma G] (h: Equation2779 G) : Equation2714 G := fun x y z =>
  let v0 := M y z
  let v1 := M y x
  let v2 := M v1 v0
  have h3 := R y
  let v4 := M v2 z
  let v5 := M v0 v4
  have h6 := R x
  have h7 := h y v0 x
  have h8 := S h7
  let v9 := M v0 x
  let v10 := M v9 v1
  have h11 := h v10 v1 v0
  have h12 := R v1
  have h13 := R v2
  have h14 := R (M x v1)
  have h15 := h x z v4
  T h15 (C (T (T (T (h (M (M z v4) (M x v4)) y z) (C (C (R v0) (S h15)) h3)) (C (T (T (T (h v9 x v1) (C (C h14 (T h11 (C (C h13 h8) h12))) h6)) (C (C h14 (T (T (T (T (T (C (C h13 h7) h12) (S h11)) (h v10 x v0)) (C (C (R (M x v0)) (T h8 (h y v0 v4))) h6)) (S (h (M v5 (M y v4)) x v0))) (C (R v5) (T (C (h y v2 z) (R v4)) (S (h v1 v4 v0)))))) h6)) (S (h v5 x v1))) h3)) (S (h v2 y z))) (R z))

@[equational_result]
theorem Equation2944_implies_Equation492 (G: Type _) [Magma G] (h: Equation2944 G) : Equation492 G := fun x y z =>
  let v0 := M z (M z y)
  let v1 := M x v0
  have h2 := R v1
  have h3 := h y z x
  have h4 := S h3
  have h5 := R x
  have h6 := h v0 x v0
  have h7 := S h6
  let v8 := M (M x v1) v0
  have h9 := R v8
  have h10 := C (C (T (C h9 h7) h7) h5) h5
  have h11 := h v0 v8 x
  have h12 := h v0 x v1
  have h13 := S h12
  have h14 := h x x x
  have h15 := S h14
  let v16 := M (M x (M x x)) x
  have h17 := R v16
  have h18 := C (C (T (C h17 h15) h15) h2) h2
  have h19 := h x v16 v1
  have h20 := C (T h19 h18) h2
  have h21 := R z
  T (T (T h19 h18) (C (T (T h20 h13) (C h21 (C h21 (T (T (T (T h3 (C (C (T h6 (C h9 h6)) h5) h5)) (S h11)) h12) (C (T (C (C (T h14 (C h17 h14)) h2) h2) (S h19)) h2))))) h2)) (C (T (T (T (C h21 (C h21 (T (T (T (T h20 h13) h11) h10) h4))) h11) h10) h4) h2)

@[equational_result]
theorem Equation2958_implies_Equation522 (G: Type _) [Magma G] (h: Equation2958 G) : Equation522 G := fun x y z =>
  let v0 := M x z
  let v1 := M z v0
  let v2 := M y (M y v1)
  let v3 := M v2 y
  have h4 := S (h v2 x v2)
  let v5 := M (M x (M x v2)) v2
  have h6 := R z
  let v7 := M v1 z
  have h8 := S (h v1 v2 v1)
  let v9 := M (M v2 (M v2 v1)) v1
  have h10 := R v0
  have h11 := S (h z x z)
  let v12 := M (M x v0) z
  let v13 := M (M x (M x x)) x
  have h14 := h x x x
  T (T (T (T (T (T (h x x z) (C (T (T (T (T (T (C (C (T h14 (C (R v13) h14)) h10) (R x)) (S (h v0 v13 x))) (h v0 v12 z)) (C (C (T (C (R v12) h11) h11) h10) h6)) (h v7 v9 v1)) (C (C (T (C (R v9) h8) h8) (R v7)) (R v1))) h6)) (S (h v1 v1 z))) (h v1 v2 y)) (R (M (M (M v2 v3) v1) y))) (C (T (T (S (h v3 y v1)) (h v3 v5 v2)) (C (C (T (C (R v5) h4) h4) (R v3)) (R v2))) (R y))) (S (h v2 v2 y))

@[equational_result]
theorem Equation2958_implies_Equation1793 (G: Type _) [Magma G] (h: Equation2958 G) : Equation1793 G := fun x y z =>
  let v0 := M y z
  let v1 := M z y
  let v2 := M v1 x
  let v3 := M v0 v2
  have h4 := R y
  have h5 := R v0
  let v6 := M v0 y
  have h7 := S (h v0 x v0)
  let v8 := M (M x (M x v0)) v0
  have h9 := T (C (R v8) h7) h7
  have h10 := S (h y x y)
  let v11 := M (M x (M x y)) y
  let v12 := M v3 v0
  have h13 := S (h v3 x v3)
  let v14 := M (M x (M x v3)) v3
  have h15 := S (h v1 v2 v1)
  let v16 := M (M v2 (M v2 v1)) v1
  T (T (h x v16 v1) (C (T (T (T (T (C (T (C (R v16) h15) h15) (R x)) (h v2 v8 v0)) (C (C h9 (R v2)) h5)) (h v12 v14 v3)) (C (C (T (C (R v14) h13) h13) (R v12)) (R v3))) (T (C (T (T (T (h z v11 y) (C (C (T (C (R v11) h10) h10) (R z)) h4)) (h v6 v8 v0)) (C (C h9 (R v6)) h5)) h4) (S (h v0 v0 y))))) (S (h v3 v3 v0))

@[equational_result]
theorem Equation492_implies_Equation2522 (G: Type _) [Magma G] (h: Equation492 G) : Equation2522 G := fun x y z =>
  let v0 := M x z
  let v1 := M v0 z
  let v2 := M y v1
  let v3 := M v2 y
  have h4 := h z v0 x
  have h5 := S h4
  have h6 := h x z x
  have h7 := R v0
  have h8 := C h7 h6
  have h9 := h x z v0
  have h10 := R x
  have h11 := h v0 x v0
  have h12 := h z v1 v0
  have h13 := h v0 z v0
  have h14 := R v1
  have h15 := S (h v1 v2 y)
  have h16 := C (R v2) (h y v1 y)
  have h17 := R z
  have h18 := C h7 (T (C h17 (T (T (T (C h17 (T (T (T h16 h15) (h v1 v0 v1)) (C h7 (C h14 (C h14 (T (C h14 h13) (S h12))))))) (S (h v0 z v1))) h11) (C h10 (C h7 (C h7 (T h8 h5)))))) (S h9))
  have h19 := h v0 v3 z
  T (T (T h9 (C h17 (T (C h10 (C h7 (C h7 (T h4 (C h7 (S h6)))))) (S h11)))) (C h17 (T h19 (C (R v3) (T (T (T (T h18 h8) h5) h12) (C h14 (T (T (S h13) h19) (C (T h16 h15) (T (T h18 h8) h5))))))))) (S (h v3 z v1))

@[equational_result]
theorem Equation711_implies_Equation2482 (G: Type _) [Magma G] (h: Equation711 G) : Equation2482 G := fun x y z =>
  let v0 := M z (M (M z x) x)
  let v1 := M y z
  have h2 := S (h z v1 v0)
  have h3 := h z z x
  have h4 := R v1
  have h5 := C h4 (C h4 (T h3 (C h3 (R v0))))
  have h6 := R z
  let v7 := M y (M (M y x) x)
  have h8 := h y v1 v7
  have h9 := R v7
  have h10 := h y y x
  have h11 := C h4 (C (C (T (C h4 (C h4 (T h10 (C h10 h9)))) (S h8)) h6) h6)
  have h12 := S h10
  have h13 := C h4 (C h4 (T (C h12 h9) h12))
  let v14 := M v1 y
  let v15 := M v14 (M (M v14 x) x)
  let v16 := M x v14
  have h17 := h v14 v14 x
  have h18 := R v16
  T (h x v16 v14) (C h18 (T (T (T (T (T (C h18 (C h18 (T h17 (C h17 (R v15))))) (S (h v14 v16 v15))) (C h4 (T (T (T h8 h13) (h (M v1 v14) v1 z)) (C (C (T h8 h13) h6) (T (T h11 h5) h2))))) h11) h5) h2))

@[equational_result]
theorem Equation1507_implies_Equation3131 (G: Type _) [Magma G] (h: Equation1507 G) : Equation3131 G := fun x y z =>
  let v0 := M y x
  let v1 := M v0 z
  let v2 := M v1 z
  let v3 := M v2 y
  let v4 := M v2 (M v2 v3)
  have h5 := R (M x (M x y))
  let v6 := M y (M y v2)
  let v7 := M v1 (M v1 v1)
  let v8 := M v2 (M v2 v0)
  have h9 := h x y y
  let v10 := M y (M y y)
  let v11 := M z v0
  let v12 := M z v11
  T (T (T (T (T (h x y x) (C (T (T (h v0 z y) (C (T (T (T (T (h v11 z v3) (C (T (T (T (T (h v12 x x) (C (T (T (T (C h9 (R v12)) (S (h v10 v0 z))) (h v10 v0 v2)) (C (S h9) (R v8))) (R (M x (M x x))))) (S (h v8 x x))) (h v8 v1 v1)) (C (S (h z v0 v2)) (R v7))) (R (M v3 (M v3 z))))) (S (h v7 z v3))) (h v7 v2 y)) (C (S (h z v1 v1)) (R v6))) (R (M y (M y z))))) (S (h v6 z y))) h5)) (C (T (h v6 v3 v2) (C (S (h y v2 y)) (R v4))) h5)) (S (h v4 y x))) (h v4 (M v3 v2) v3)) (C (S (h v2 v3 v2)) (S (h y v2 v3)))

@[equational_result]
theorem Equation2196_implies_Equation2399 (G: Type _) [Magma G] (h: Equation2196 G) : Equation2399 G := fun x y z =>
  let v0 := M z x
  let v1 := M z v0
  let v2 := M y v1
  let v3 := M v2 y
  let v4 := M v3 v2
  let v5 := M v4 v2
  let v6 := M y v2
  have h7 := R (M (M v2 x) x)
  let v8 := M (M v1 v2) v2
  let v9 := M (M v0 v0) v0
  have h10 := h z x v3
  let v11 := M (M x v3) v3
  let v12 := M v0 x
  let v13 := M x z
  T (T (T (T (T (h x z v0) (C (R (M v1 v0)) (T (T (T (T (h v13 z x) (C (R v12) (T (T (T (T (h (M v13 z) v0 x) (C (R (M v12 x)) (T (S (h z x z)) h10))) (S (h v11 v0 x))) (h v11 v0 v0)) (C (R v9) (S h10))))) (S (h v9 z x))) (h v9 v1 v2)) (C (R v8) (S (h z v0 v0)))))) (S (h v8 z v0))) (h v8 v2 x)) (C h7 (T (T (T (S (h y v1 v2)) (h y v2 v3)) (C (R (M (M v2 v3) v3)) (T (T (h v6 v2 x) (C h7 (T (h (M v6 v2) v3 v2) (C (R v5) (S (h v2 y v2)))))) (S (h v5 v2 x))))) (S (h v4 v2 v3))))) (S (h v3 v2 x))

@[equational_result]
theorem Equation2196_implies_Equation3601 (G: Type _) [Magma G] (h: Equation2196 G) : Equation3601 G := fun x y z =>
  let v0 := M y x
  let v1 := M v0 z
  let v2 := M z v1
  let v3 := M x y
  let v4 := M (M v3 z) z
  have h5 := h x y v2
  let v6 := M (M y v2) v2
  have h7 := R v4
  have h8 := S (h v4 (M y v3) v3)
  have h9 := C (h x y v3) (h y v3 z)
  let v10 := M v2 v3
  let v11 := M v10 v3
  have h12 := h z v1 y
  let v13 := M (M v1 y) y
  T (T (T (T h9 h8) (h v4 v0 v2)) (C (R (M (M v0 v2) v2)) (T (T (C h7 (T (T (h v0 z x) (C (R (M (M z x) x)) (T (T (T (C (h v0 z v1) h12) (S (h v13 v2 v1))) (h v13 v2 v3)) (C (R v11) (S h12))))) (S (h v11 z x)))) (S (h v10 v3 z))) (C (R v2) (T (T (T (T h9 h8) (h v4 x v4)) (C (R (M (M x v4) v4)) (T (T (T (T (C h7 h5) (S (h v6 v3 z))) (h v6 v3 x)) (C (R (M (M v3 x) x)) (T (S h5) (h x y x)))) (S (h (M v0 x) v3 x))))) (S (h v0 x v4))))))) (S (h v2 v0 v2))

@[equational_result]
theorem Equation2685_implies_Equation3534 (G: Type _) [Magma G] (h: Equation2685 G) : Equation3534 G := fun x y z =>
  let v0 := M z y
  let v1 := M v0 z
  let v2 := M x v1
  have h3 := h v2 v2 v0
  have h4 := R v0
  let v5 := M (M v2 v2) (M v0 v2)
  have h6 := R x
  have h7 := R (M x v0)
  let v8 := M x y
  have h9 := h v2 v8 v0
  let v10 := M v0 v0
  have h11 := h x v8 z
  let v12 := M (M x v8) (M z v8)
  let v13 := M v8 v0
  have h14 := h v8 v2 v0
  have h15 := h v8 v8 v0
  T (T h15 (C (T (T (T (T (T (T (T (T (T (h (M (M v8 v8) (M v0 v8)) v0 x) (C (C (T (S h15) h14) h7) h6)) (C (C (T (S h14) (h v8 v0 v0)) h7) h6)) (S (h (M v13 v10) v0 x))) (C (T (T (T (T (h v13 z x) (C (C (T (S (h x y z)) h11) (R (M x z))) h6)) (S (h v12 z x))) (h v12 z v0)) (C (C (S h11) (R v1)) h4)) (R v10))) (h (M (M v2 v0) v10) v0 x)) (C (C (T (S (h v2 v0 v0)) h9) h7) h6)) (C (C (T (S h9) h3) h7) h6)) (S (h v5 v0 x))) (R v5)) h4)) (S h3)

@[equational_result]
theorem Equation2741_implies_Equation4098 (G: Type _) [Magma G] (h: Equation2741 G) : Equation4098 G := fun x y z =>
  have h0 := R z
  let v1 := M y y
  let v2 := M v1 z
  let v3 := M x x
  let v4 := M v2 z
  have h5 := R v3
  let v6 := M v3 v3
  let v7 := M v4 v4
  have h8 := R v6
  have h9 := R y
  have h10 := h y y y
  have h11 := S h10
  let v12 := M v1 v1
  have h13 := R x
  have h14 := S (h x x x)
  have h15 := h x v2 x
  let v16 := M (M v2 v2) v3
  have h17 := h v3 v4 y
  T (T (T (T (T (T h17 (C (T (T (h (M v7 (M v3 y)) x y) (C (T (T (T (T (T (C h5 (S h17)) (h v6 x x)) (C (T (C h5 h14) (C h5 h15)) h13)) (S (h v16 x x))) (h v16 v3 x)) (C (T (C h8 (S h15)) h14) h13)) h9)) (C h5 h10)) h9)) (S (h v12 x y))) (h v12 v1 y)) (C (T (C (R v12) h11) h11) h9)) (h v1 v3 z)) (C (T (T (T (C h8 (T (h v2 v7 z) (C (S (h v4 v4 v4)) h0))) (h (M v6 (M v4 z)) x z)) (C (C h5 (S (h v4 v3 z))) h0)) (S (h v2 x z))) h0)

@[equational_result]
theorem Equation3147_implies_Equation1865 (G: Type _) [Magma G] (h: Equation3147 G) : Equation1865 G := fun x y z =>
  let v0 := M z z
  have h1 := R v0
  let v2 := M y y
  let v3 := M x v2
  let v4 := M v3 v0
  have h5 := R v2
  have h6 := R v4
  have h7 := h v2 v0 v2
  have h8 := h v0 z v2
  have h9 := h v2 y v0
  have h10 := h v0 v2 v0
  have h11 := h x v2 x
  have h12 := R x
  have h13 := h v2 y x
  have h14 := R v3
  T (h x x v0) (C (C (T (C (T (T (C (T (T h11 (C (S h13) h12)) (C (T h7 (C (T (T (S h8) (h v0 y v3)) (C (T (C (T (T (C h9 h1) (S h10)) (h v0 z v3)) h14) (S (h v3 v0 v3))) h14)) h5)) h12)) h12) (S (h v2 v3 x))) h13) h12) (S h11)) (T (T (T (h v0 v0 v0) (C (S (h v0 z v0)) h1)) (C (T h10 (C (T (T (T (S h9) (h v2 v2 v2)) (C (S (h v2 y v2)) h5)) (C (T (h v2 z v4) (C (T (T (C (T (C h8 h5) (S h7)) h6) (C (h v2 y v4) h6)) (S (h v4 v2 v4))) h6)) h5)) h1)) h1)) (S (h v2 v4 v0)))) h1)

@[equational_result]
theorem Equation3384_implies_Equation3451 (G: Type _) [Magma G] (h: Equation3384 G) : Equation3451 G := fun x y z w u =>
  let v0 := M x y
  let v1 := M y y
  let v2 := M u v1
  have h3 := h u y v2
  have h4 := h x y (M x v1)
  let v5 := M u y
  let v6 := M w v5
  let v7 := M z v6
  let v8 := M v1 v1
  have h9 := h v1 y x
  have h10 := h v1 y u
  have h11 := T (S h10) h9
  have h12 := R v7
  have h13 := T (T (T (T (h u v1 v7) (h v7 (M u v8) v7)) (C h12 (C h12 (C h11 h11)))) (S (h v7 (M x v8) v7))) (S (h x v1 v7))
  have h14 := T (T h3 (C h13 h13)) (S h4)
  have h15 := S h3
  let v16 := M v2 v2
  have h17 := T (T (h x v1 v6) (C (R v6) (T (S h9) h10))) (S (h u v1 v6))
  T (T (T (h x y v0) (C (R v0) h17)) (h v0 v2 z)) (C (R z) (T (T (T (T (R (M v0 v16)) (C (T h4 (C h17 h17)) (R v16))) (C h15 h15)) (h v5 v5 w)) (C (R w) (T (T (C h14 (C h14 h3)) (S (h v0 v2 v0))) (S (h u y v0))))))

@[equational_result]
theorem Equation3131_implies_Equation3370 (G: Type _) [Magma G] (h: Equation3131 G) : Equation3370 G := fun x y z =>
  let v0 := M z x
  let v1 := M z v0
  let v2 := M y v1
  have h3 := R v2
  have h4 := R v1
  have h5 := R v0
  have h6 := h z v1 z
  have h7 := h v0 z z
  have h8 := C (S h7) h4
  have h9 := C (T h6 h8) h5
  have h10 := T (T (h v1 z v2) (C (C (C (T (C (T (T h6 h8) (C (T (h v0 v1 v0) (C (T (C (T (T (C (C h9 h5) h5) (S (h v1 v0 v0))) h9) h5) (C (C (T (C h7 h4) (S h6)) h5) h5)) h4)) h4)) h4) (S (h v0 v1 v1))) h3) h3) (R z))) (S (h x z v2))
  have h11 := C h10 h3
  have h12 := C (S (h v1 y y)) h3
  have h13 := h y v2 y
  let v14 := M x y
  have h15 := R v14
  T (T (h v14 v1 v1) (C (C (T (T (C (C (T (h v1 v14 v1) (C (T (T (T (T (C (R (M (M v14 v1) v1)) h10) (S (h y x v1))) h13) h12) h11) h15)) h15) h10) (S (h v2 x v14))) (C (T (T h13 h12) h11) h4)) h4) h10)) (S (h v2 x v1))

@[equational_result]
theorem Equation3404_implies_Equation3534 (G: Type _) [Magma G] (h: Equation3404 G) : Equation3534 G := fun x y z =>
  let v0 := M z y
  let v1 := M v0 z
  let v2 := M x v1
  have h3 := R z
  have h4 := R v1
  let v5 := M x y
  have h6 := R y
  have h7 := h v0 z v0
  have h8 := h y v0 z
  have h9 := h y v0 x
  have h10 := R v0
  have h11 := h v5 x v0
  let v12 := M v5 y
  T (T (h x y v2) (C (R v2) (T (T (T (T (T (T (T (T (C h6 (T (T (T (T (T (T (h v2 x v0) (C h10 (S (h v1 v0 x)))) (C h10 (T (T (h v1 v0 y) (C h6 (S (h z y v0)))) (h y v0 v5)))) (S (h v12 v5 v0))) (h v12 v5 v1)) (C h4 (S (h y v1 v5)))) (C (T (T h7 (C h10 (T (S h8) h9))) (S h11)) (R (M y v1))))) (S (h v1 (M v5 x) y))) (C h4 (T (T h11 (C h10 (T (S h9) h8))) (S h7)))) (h v1 v1 y)) (C h6 (T (C h4 (h y v1 x)) (S (h v5 x v1))))) (C h6 (T (h v5 x z) (C h3 (S (h y z x)))))) (S (h z z y))) (h z z v1)) (C h4 (T (C h3 (h v1 z x)) (S (h v2 x z))))))) (S (h x v1 v2))

@[equational_result]
theorem Equation3404_implies_Equation3820 (G: Type _) [Magma G] (h: Equation3404 G) : Equation3820 G := fun x y z =>
  let v0 := M x y
  let v1 := M z z
  let v2 := M v1 v0
  have h3 := R v2
  have h4 := R z
  have h5 := T (C (R y) (T (h v0 x z) (C h4 (S (h y z x))))) (S (h z z y))
  have h6 := h x y v0
  have h7 := R v0
  let v8 := M y v1
  have h9 := R x
  have h10 := h z z v0
  let v11 := M z (M v0 z)
  T (T (T (T h6 (C h7 h5)) (C h7 h10)) (C h7 (T (T (h v0 v11 v1) (C (R v1) (T (T (T (T (T (T (T (T (T (h v11 v2 v0) (C h7 (C h3 (S h10)))) (C h7 (T (h v2 v1 x) (C h9 (S (h v0 x v1)))))) (S (h x x v0))) (h x x z)) (C h4 (T (T (C h9 (h z x z)) (S (h v1 z x))) (h v1 z y)))) (S (h v8 y z))) (h v8 y v0)) (C h7 (S (h v1 v0 y)))) (C (T (T (T h6 (h v0 (M y (M v0 x)) v2)) (C h3 (C h5 (R (M v2 v0))))) (S (h v0 v1 v2))) h3)))) (S (h v0 (M v0 v1) v1))))) (S (h v1 v0 v0))

@[equational_result]
theorem Equation3930_implies_Equation327 (G: Type _) [Magma G] (h: Equation3930 G) : Equation327 G := fun x y z =>
  have h0 := h y z y
  have h1 := R y
  have h2 := h z y z
  have h3 := R z
  let v4 := M y z
  let v5 := M x v4
  have h6 := h y z v5
  have h7 := S h6
  have h8 := h z v5 x
  have h9 := h x y z
  have h10 := h z x y
  have h11 := h z x v4
  have h12 := C h1 (T (T (T (S h11) h10) (C (C h3 h9) h3)) (S h8))
  have h13 := C h12 h1
  have h14 := C h1 (T (T (T h8 (C (C h3 (S h9)) h3)) (S h10)) h11)
  have h15 := h y (M z v5) z
  have h16 := C h14 h1
  have h17 := C h3 (T (T h6 h16) (C (T (T (T h12 h15) h13) h7) h1))
  let v18 := M z y
  have h19 := R x
  T (T (T h9 (C (C h19 h0) h19)) (S (h x (M y v18) y))) (C h19 (T (T (h y v18 z) (C (C h1 (T (T (C (T (T (T h2 (C h17 h3)) (S (h z v4 y))) h17) h3) (C (C h3 (T (T (C (T (T (T h6 h16) (S h15)) h14) h1) h13) h7)) h3)) (S h2))) h1)) (S h0)))

