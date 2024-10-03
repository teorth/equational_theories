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
theorem Equation2944_implies_Equation2399 (G: Type _) [Magma G] (h: Equation2944 G) : Equation2399 G := fun x y z =>
  let v0 := M z (M z x)
  let v1 := M y v0
  let v2 := M v1 y
  have h3 := R v2
  let v4 := M (M x (M x y)) y
  have h5 := h y v4 v1
  have h6 := S h5
  have h7 := R v1
  have h8 := h y x y
  have h9 := R v4
  have h10 := C (C (T h8 (C h9 h8)) h7) h7
  have h11 := S h8
  have h12 := C (C h7 (C h7 (T h5 (C (C (T (C h9 h11) h11) h7) h7)))) h3
  have h13 := S (h v1 x v1)
  let v14 := M (M x (M x v1)) v1
  have h15 := C (C (T (C (R v14) h13) h13) h3) h3
  have h16 := h v1 v14 v2
  let v17 := M (M x (M x v0)) v0
  have h18 := R x
  have h19 := h v0 x v0
  T (T (T (T (T (h x z x) (C (C (T h19 (C (R v17) h19)) h18) h18)) (S (h v0 v17 x))) (h v0 y v2)) (C (C (C (R y) (T (T (T h16 h15) h12) (C (T (T (T (C (T (T h16 h15) h12) (C h7 (T h10 h6))) (S (h (M (M y v1) v1) v1 v2))) h10) h6) h3))) h3) h3)) (S (h v2 y v2))

@[equational_result]
theorem Equation1301_implies_Equation2370 (G: Type _) [Magma G] (h: Equation1301 G) : Equation2370 G := fun x y z =>
  let v0 := M x y
  let v1 := M z v0
  let v2 := M y v1
  let v3 := M v2 z
  let v4 := M (M (M v2 x) v3) x
  have h5 := R z
  have h6 := h v2 v3 x
  let v7 := M (M v2 v2) v1
  have h8 := R v1
  have h9 := h y v2 v1
  have h10 := R y
  let v11 := M (M (M z x) v1) x
  have h12 := R v0
  have h13 := h z v1 x
  let v14 := M (M (M v1 x) x) x
  let v15 := M (M v0 v1) y
  have h16 := h x v15 v14
  have h17 := R v14
  have h18 := R v15
  have h19 := h v1 x x
  have h20 := h x v1 y
  have h21 := S h19
  T (T (T (T (T h16 (C h18 (T (C (T (C h21 h18) (S h20)) h17) h21))) (h (M v15 v1) z y)) (C h5 (T (T (C (T (T (C (C (T (C h18 (T h19 (C (T h20 (C h19 h18)) h17))) (S h16)) h10) h5) (C h12 (T h13 (C (C h13 h12) (R v11))))) (S (h v1 v0 v11))) h10) (C h8 (T h9 (C (C h9 h8) (R v7))))) (S (h v2 v1 v7))))) (C h5 (T h6 (C (C h6 h5) (R v4))))) (S (h v3 z v4))

@[equational_result]
theorem Equation2196_implies_Equation1171 (G: Type _) [Magma G] (h: Equation2196 G) : Equation1171 G := fun x y z =>
  let v0 := M y z
  let v1 := M z v0
  let v2 := M v1 x
  let v3 := M y v2
  have h4 := S (h y v2 v3)
  let v5 := M v2 v3
  let v6 := M (M v3 y) y
  let v7 := M v5 v3
  have h8 := h v1 x v3
  let v9 := M (M x v3) v3
  let v10 := M x y
  have h11 := h y z v0
  let v12 := M (M v0 v0) v0
  have h13 := h y z v2
  let v14 := M (M z v2) v2
  let v15 := M v0 z
  let v16 := M v15 z
  T (T (T (T (h x y v0) (C (R (M (M y v0) v0)) (T (T (T (T (h v10 y z) (C (T (T (T (h v15 z x) (C (R (M (M z x) x)) (T (T (T (T (h v16 y x) (C (R (M (M y x) x)) (T (T (T (C (R v16) h13) (S (h v14 v0 z))) (h v14 v0 v0)) (C (R v12) (S h13))))) (S (h v12 y x))) (h v12 v1 v0)) (C (S h11) (S (h z v0 v0)))))) (S (h y z x))) h11) (T (T (T (T (h (M v10 y) v2 x) (C (R (M (M v2 x) x)) (T (S (h v1 x y)) h8))) (S (h v9 v2 x))) (h v9 v2 v3)) (C (R v7) (S h8))))) (S (h v7 v1 v0))) (h v7 v3 y)) (C (R v6) h4)))) (S (h v6 y v0))) (h v6 v5 v3)) (C h4 (S (h v2 v3 y)))

@[equational_result]
theorem Equation3211_implies_Equation1561 (G: Type _) [Magma G] (h: Equation3211 G) : Equation1561 G := fun x y z =>
  let v0 := M z y
  let v1 := M x v0
  have h2 := R v1
  let v3 := M y z
  have h4 := R x
  have h5 := R v3
  let v6 := M v3 v1
  have h7 := h v1 v3 v6
  have h8 := S h7
  have h9 := R v6
  have h10 := h v3 v6 v1
  have h11 := h v1 v3 v1
  have h12 := C (C (C (T (C h11 h9) (S h10)) h9) h9) h2
  have h13 := h v6 v1 v6
  have h14 := R v0
  have h15 := C (S h11) h9
  have h16 := R y
  T (h x v1 v3) (C (T (C (T (C (C (T h7 (C (T (C (C (C (T h10 h15) h9) h9) h2) (S h13)) h5)) h5) h5) (C (C (T (T (T (C (T h13 h12) h5) h8) (h v1 v3 x)) (C (T (C (C (C (T (h v3 x v0) (C (T (C (T (T (T (C (T (h v1 v6 v1) (C (C (C (T (C (T (h v6 v0 v3) (C (C (T (T (T (C (C (C (T (h z y v3) (C (T (C (C (C (T (h y v3 z) (C (S (h z y z)) h5)) h5) h5) (R z)) (S (h v3 z v3))) h16)) h16) h5) h5) (S (h v3 v3 y))) h10) h15) h9) h14)) h2) (S (h v0 v1 v6))) h2) h2) h9)) h14) (S (h v6 v0 v1))) h13) h12) h5) h8) h4)) h4) h4) h2) (S (h x v1 x))) h5)) h5) h5)) h4) (S (h v3 x v3))) h2)

@[equational_result]
theorem Equation3211_implies_Equation2399 (G: Type _) [Magma G] (h: Equation3211 G) : Equation2399 G := fun x y z =>
  let v0 := M z x
  let v1 := M z v0
  let v2 := M y v1
  let v3 := M v2 y
  have h4 := R z
  have h5 := R v1
  have h6 := S (h v1 y v2)
  have h7 := R v2
  have h8 := C (T (h v2 v1 v2) (C (C (C (T (C (h v1 y v1) h7) (S (h y v2 v1))) h7) h7) h5)) (R y)
  have h9 := h z v0 x
  have h10 := S h9
  have h11 := R v0
  have h12 := h x z x
  have h13 := C h12 h11
  have h14 := h x z v0
  have h15 := R x
  have h16 := h v0 x v0
  have h17 := h z v1 v0
  have h18 := h v0 z v0
  have h19 := C (T (C (T (T (T (C (T (T (T h8 h6) (h v1 v0 v1)) (C (C (C (T (C h18 h5) (S h17)) h5) h5) h11)) h4) (S (h v0 z v1))) h16) (C (C (C (T h13 h10) h11) h11) h15)) h4) (S h14)) h11
  have h20 := h v0 v3 z
  T (T (T h14 (C (T (C (C (C (T h9 (C (S h12) h11)) h11) h11) h15) (S h16)) h4)) (C (T h20 (C (T (T (T (T h19 h13) h10) h17) (C (T (T (S h18) h20) (C (T (T h19 h13) h10) (T h8 h6))) h5)) (R v3))) h4)) (S (h v3 z v1))

@[equational_result]
theorem Equation881_implies_Equation2 (G: Type _) [Magma G] (h: Equation881 G) : Equation2 G := fun x y =>
  have h0 := h y x y
  have h1 := S h0
  let v2 := M y y
  let v3 := M y x
  let v4 := M v3 v2
  have h5 := h x y x
  let v6 := M x x
  let v7 := M (M x y) v6
  have h8 := h v7 x x
  have h9 := R v4
  have h10 := C h9 (T (C h1 (S h8)) (S h5))
  let v11 := M v7 x
  have h12 := h x v4 (M v11 v11)
  let v13 := M v2 v3
  let v14 := M v13 x
  have h15 := h x v4 (M v14 v14)
  have h16 := h v13 x x
  have h17 := h y y x
  have h18 := C h9 (T (C h1 (S h16)) (S h17))
  let v19 := M v6 v6
  let v20 := M v19 x
  have h21 := h x x x
  have h22 := R v19
  let v23 := M v3 v3
  let v24 := M v23 x
  T (T h21 (C (R x) (T (T (h v19 y x) (C (R y) (T (C (T (T (T (C h22 (T (h y x x) (C h21 (h v23 x x)))) (S (h x v19 (M v24 v24)))) h12) h10) (T (T (T (C h22 (T h21 (C h21 (h v19 x x)))) (S (h x v19 (M v20 v20)))) h15) h18)) (C (T (T (T (C h9 (T h5 (C h0 h8))) (S h12)) h15) h18) (T (T (T (C h9 (T h17 (C h0 h16))) (S h15)) h12) h10))))) (S (h v4 y x))))) h1

@[equational_result]
theorem Equation3354_implies_Equation41 (G: Type _) [Magma G] (h: Equation3354 G) : Equation41 G := fun x y z =>
  let v0 := M x x
  have h1 := S (h z (M y v0) x)
  let v2 := M y x
  have h3 := R x
  have h4 := h y x x
  have h5 := S h4
  have h6 := h x x v2
  have h7 := C h3 (T h6 (C h3 h5))
  have h8 := h x x x
  have h9 := C h3 (S h8)
  have h10 := h x x v0
  let v11 := M y z
  have h12 := h y v0 v11
  have h13 := h y v11 x
  have h14 := R v11
  have h15 := h x v11 x
  have h16 := R v0
  have h17 := h x v0 v11
  have h18 := T (T (T (T h10 h9) h17) (C h16 (C h16 (T (T h15 (C h14 (C h14 (T (T (T h10 h9) h7) h5)))) (S h13))))) (S h12)
  have h19 := C h18 (C h18 (T (T (T (T (T (T h10 h9) h7) h5) (h y x z)) (C h3 (C h3 (h y z x)))) (S (h z x (M z v2)))))
  have h20 := h x v0 x
  have h21 := R z
  T (T (T (T (T (T (T (h x x (M x v11)) (C h3 (S (h x x v11)))) h20) h19) h1) (C h21 (T (T h12 (C h16 (C h16 (T (T h13 (C h14 (C h14 (T (T (T h4 (C h3 (T (C h3 h4) (S h6)))) (C h3 h8)) (S h10))))) (S h15))))) (S h17)))) (C h21 (T (T h20 h19) h1))) (S (h y z v0))

@[equational_result]
theorem Equation952_implies_Equation1137 (G: Type _) [Magma G] (h: Equation952 G) : Equation1137 G := fun x y z =>
  let v0 := M z z
  let v1 := M y v0
  let v2 := M v1 x
  let v3 := M y v2
  let v4 := M v1 v1
  have h5 := R v1
  have h6 := h v2 y y
  let v7 := M v3 (M y y)
  have h8 := R (M (M v1 v7) v4)
  have h9 := R (M y x)
  have h10 := R x
  let v11 := M z y
  let v12 := M z v2
  have h13 := h z y v0
  let v14 := M (M v0 z) (M v0 y)
  let v15 := M z v1
  T (T (T (T (T (T (T (T (T (T (h x x v1) (C h10 (C (h v2 v1 z) (R v2)))) (S (h (M v12 v15) x v1))) (C (R v12) (T (T (h v15 x v0) (C h10 (C (T (T (T (T (C (R v0) (C h13 h5)) (S (h v14 v0 y))) (h v14 x y)) (C h10 (C (T (S h13) (h z y z)) h9))) (S (h (M v0 v11) x y))) (R (M v0 x))))) (S (h v11 x v0))))) (h (M v12 v11) x y)) (C h10 (C (T (S (h v2 y z)) h6) h9))) (S (h v7 x y))) (h v7 v1 v1)) (C h5 h8)) (C h5 (T h8 (C (T (C h5 (T (h v7 v0 y) (C (h v0 v2 y) (C (S h6) h5)))) (S (h (M v1 v3) v1 v2))) (R v4))))) (S (h v3 v1 v1))

@[equational_result]
theorem Equation1764_implies_Equation1913 (G: Type _) [Magma G] (h: Equation1764 G) : Equation1913 G := fun x y z =>
  let v0 := M z y
  let v1 := M x z
  let v2 := M y v1
  let v3 := M v2 v0
  have h4 := h v0 v0 (M (M v2 y) z)
  have h5 := S h4
  have h6 := R v0
  have h7 := h v2 z y
  have h8 := C h7 (C h7 h6)
  have h9 := R v3
  have h10 := R v1
  have h11 := h y v3 v1
  have h12 := S h7
  let v13 := M v3 v1
  have h14 := h v13 x y
  have h15 := R x
  have h16 := h y v0 v1
  have h17 := R v13
  have h18 := h v0 v3 v1
  have h19 := R (M x y)
  have h20 := h z x y
  have h21 := T (T h20 (C h19 (C (T h18 (C h17 (S h16))) h15))) (S h14)
  let v22 := M v1 v0
  T (T (h x v0 z) (C (R (M v0 z)) (T (h v22 v3 z) (C (R (M v3 z)) (T (T (T (C (T (T (C (R v22) h21) (S (h v2 v1 v0))) (C (T h11 (C (T (T h14 (C h19 (C (T (C h17 h16) (S h18)) h15))) (S h20)) (T h8 h5))) h10)) h9) (C (C (T (C h21 (T h4 (C h12 (C h12 h6)))) (S h11)) h10) h9)) h8) h5))))) (S (h v3 v0 z))

@[equational_result]
theorem Equation2170_implies_Equation14 (G: Type _) [Magma G] (h: Equation2170 G) : Equation14 G := fun x y =>
  let v0 := M x y
  have h1 := h y x y
  have h2 := S h1
  let v3 := M y x
  have h4 := R v3
  let v5 := M y v0
  let v6 := M v0 y
  have h7 := h v6 v5 v0
  let v8 := M v0 v5
  have h9 := R v8
  have h10 := h v0 y v0
  have h11 := C (T (C h10 h9) (S h7)) h4
  have h12 := h v8 x y
  have h13 := T (T h12 h11) h2
  let v14 := M v8 v0
  have h15 := S h12
  have h16 := h x y v0
  have h17 := h v6 v5 y
  have h18 := R v5
  have h19 := h v3 v0 y
  have h20 := h y y v0
  have h21 := h v5 x y
  let v22 := M v5 x
  have h23 := R v22
  T (T (T (T (T h16 (C h23 (T (T h17 (C (T (T (T (S h20) h1) (C (T h7 (C (S h10) h9)) h4)) h15) (T (C h1 h18) (S h19)))) (S h21)))) (h (M v22 v5) v0 v5)) (C (T (T (C h13 (T (C h23 (T (T h21 (C (T (T (T h12 h11) h2) h20) (T h19 (C h2 h18)))) (S h17))) (S h16))) (h v3 v0 v8)) (C h15 (R v14))) (R (M v5 v0)))) (S (h v14 v0 v5))) (C h13 (R v0))

@[equational_result]
theorem Equation952_implies_Equation455 (G: Type _) [Magma G] (h: Equation952 G) : Equation455 G := fun x y z =>
  let v0 := M z y
  let v1 := M z v0
  let v2 := M y v1
  have h3 := h v2 v1 z
  have h4 := S h3
  let v5 := M z v2
  let v6 := M v5 (M z v1)
  have h7 := R x
  have h8 := R v1
  have h9 := h v1 x v0
  let v10 := M x v2
  have h11 := R v10
  let v12 := M v1 v10
  let v13 := M x v1
  have h14 := h x x z
  let v15 := M z x
  T (T h14 (C h7 (T (h (M v15 v15) v1 x) (C h8 (T (T (C (S h14) (R v13)) (C h7 (T (T (T (T (h v13 x v10) (C h7 (C (T (T (T (T (h (M v10 v13) x v1) (C h7 (C (T (S (h v2 v1 x)) h3) (R (M v1 x))))) (S (h v6 x v1))) (h v6 v10 v1)) (C h11 (C h4 (R v12)))) (R (M v10 x))))) (S (h (M v2 v12) x v10))) (C (R v2) (C h9 h11))) (S (h (M (M v0 v1) (M v0 x)) v2 x))))) (S h9)))))) (C h7 (T (C h8 (T (T (T (T (h v1 x y) (C h7 (C (h v2 y z) (R (M y x))))) (S (h (M v5 v0) x y))) (C (R v5) (T (h v0 v2 z) (C h3 (R (M v1 v5)))))) (S (h v6 v5 v1)))) h4))

@[equational_result]
theorem Equation2779_implies_Equation2741 (G: Type _) [Magma G] (h: Equation2779 G) : Equation2741 G := fun x y z =>
  let v0 := M x z
  let v1 := M y y
  let v2 := M v1 v0
  let v3 := M v2 z
  have h4 := h v3 y v0
  have h5 := h y y y
  have h6 := S h5
  let v7 := M v1 v1
  have h8 := R v1
  let v9 := M (M y v0) (M v3 v0)
  have h10 := h y v3 v3
  let v11 := M (M v3 v3) (M y v3)
  have h12 := R x
  have h13 := R v3
  have h14 := h x v2 z
  have h15 := h v1 v3 v0
  have h16 := S h15
  have h17 := C h14 h13
  let v18 := M v3 y
  T (T (T (T (h x x v3) (C (C (R (M x v3)) (T (T h17 h16) (h v1 v3 y))) h12)) (S (h (M v18 (M v1 y)) x v3))) (C (T (T (h v18 v0 v1) (C (C (R (M v0 v1)) (T (T (T (T (T (h (M v18 v1) x v3) (C (C (T h17 h16) (S (h y v3 y))) h12)) (C (C (T h15 (C (S h14) h13)) h10) h12)) (S (h v11 x v3))) (h v11 v1 v3)) (C (T (C (C h8 h4) (S h10)) (S (h v9 y y))) h8))) (R v0))) (S (h v9 v0 v1))) (T (C (T (T (h v1 v1 v1) (C (C (R v7) (T (h v7 v1 y) (C (T (C (C h8 h5) h6) (S (h v7 y y))) h8))) h8)) (S (h v7 v1 v1))) (R y)) h6))) (S h4)

@[equational_result]
theorem Equation492_implies_Equation1793 (G: Type _) [Magma G] (h: Equation492 G) : Equation1793 G := fun x y z =>
  let v0 := M z y
  let v1 := M v0 x
  let v2 := M y z
  let v3 := M v2 v1
  have h4 := h v3 v0 y
  have h5 := h v0 z v0
  have h6 := h z y z
  have h7 := R v0
  have h8 := h y v0 z
  have h9 := R z
  have h10 := R y
  have h11 := h z y v0
  have h12 := h v2 v1 v2
  have h13 := S h12
  have h14 := R v3
  have h15 := h v1 v3 v2
  have h16 := C h10 (T (C h10 (T h5 (C h9 (C h7 (C h7 (T (C h7 h6) (S h8))))))) (S h11))
  have h17 := R v2
  have h18 := R x
  have h19 := R v1
  T (T (h x v0 y) (C h7 (T (T (T (C h18 (T (T h16 (h v2 v1 v3)) (C h19 (T (T (C h17 (C h14 (C h14 (T h15 (C h14 h13))))) (S (h v3 v2 v3))) (C h17 (T (h v1 v2 x) (C h17 (T (C h19 (C h18 (C h18 (T (h v2 x v1) (C h18 (T (C h17 (C h19 (C h19 (T (h x v1 v2) (C h19 (T (C h18 (C h17 (T h4 (C h7 (T (C h14 (T h16 h12)) (S h15)))))) (S (h v2 x v0)))))))) (S (h v1 v2 v1)))))))) (S (h x v1 x)))))))))) (S (h v1 x v2))) h15) (C h14 (T h13 (C h10 (T h11 (C h10 (T (C h9 (C h7 (C h7 (T h8 (C h7 (S h6)))))) (S h5)))))))))) (S h4)

@[equational_result]
theorem Equation2196_implies_Equation2335 (G: Type _) [Magma G] (h: Equation2196 G) : Equation2335 G := fun x y z =>
  let v0 := M x z
  let v1 := M y v0
  let v2 := M y v1
  let v3 := M v2 z
  let v4 := M (M v2 v3) v3
  let v5 := M v3 v2
  let v6 := M v5 v2
  let v7 := M z v2
  let v8 := M v7 v2
  let v9 := M (M v1 v3) v3
  let v10 := M (M v0 v0) v0
  have h11 := S (h v10 (M z v0) v0)
  have h12 := C (h x z v0) (h z v0 v0)
  let v13 := M v0 z
  let v14 := M v13 z
  have h15 := h x z v2
  T (T (T (T (T (h x z z) (C (R (M (M z z) z)) (T (T (T (T h12 h11) (h v10 x x)) (C (R (M (M x x) x)) (T (T (T (C (R v10) h15) (S (h v8 v0 v0))) (h v8 v0 z)) (C (R v14) (S h15))))) (S (h v14 x x))))) (S (h v13 z z))) (C (T h12 h11) (R z))) (C (T (T (h v10 v1 v3) (C (R v9) (S (h y v0 v0)))) (C (T (h v9 v2 v3) (C (R v4) (S (h y v1 v3)))) (R y))) (T (T (T (h z v2 v0) (C (R (M (M v2 v0) v0)) (T (T (h v7 v2 x) (C (R (M (M v2 x) x)) (T (h v8 v3 v2) (C (R v6) (S (h v2 z v2)))))) (S (h v6 v2 x))))) (S (h v5 v2 v0))) (C (R v3) (T (C (h y v1 v2) (h v1 v2 v3)) (S (h v4 (M v1 v2) v2))))))) (S (h v3 v4 y))

@[equational_result]
theorem Equation3211_implies_Equation1943 (G: Type _) [Magma G] (h: Equation3211 G) : Equation1943 G := fun x y z =>
  let v0 := M x z
  let v1 := M y z
  let v2 := M y v1
  have h3 := R y
  have h4 := R v2
  have h5 := h y v2 v1
  have h6 := S h5
  have h7 := h v1 y v1
  have h8 := h v1 v2 y
  have h9 := R v1
  have h10 := h v2 v1 v2
  have h11 := h v1 y v2
  have h12 := h v1 z v1
  have h13 := S h12
  have h14 := R z
  have h15 := h z y z
  have h16 := C (S h15) h9
  have h17 := h y v1 z
  have h18 := C (C (C (T h17 h16) h9) h9) h14
  have h19 := h z y v1
  have h20 := S h17
  have h21 := C h15 h9
  T (h x v0 z) (C (T (T (T (S (h z x z)) h19) (C (T (T (T h18 h13) h8) (C (T (T (T (T (C (T (C (T (T (T (C (T h10 (C (C (C (T (C h7 h4) h6) h4) h4) h9)) h3) (S h11)) h12) (C (C (C (T h21 h20) h9) h9) h14)) h3) (S h19)) h9) h21) h20) (h y y v2)) (C (C (T (C (T (T (C (T (T h17 h16) (C (T h19 (C (T (T (T h18 h13) h11) (C (T (C (C (C (T h5 (C (S h7) h4)) h4) h4) h9) (S h10)) h3)) h3)) h9)) h4) (S h8)) h7) h4) h6) h3) h3)) h4)) h3)) (S (h v2 y y))) (R v0))

@[equational_result]
theorem Equation3557_implies_Equation41 (G: Type _) [Magma G] (h: Equation3557 G) : Equation41 G := fun x y z =>
  let v0 := M y z
  let v1 := M x x
  let v2 := M z y
  let v3 := M (M v0 v2) v1
  have h4 := h y z v1
  have h5 := R z
  let v6 := M v2 v1
  have h7 := R v1
  have h8 := R x
  have h9 := h x x x
  have h10 := S h9
  have h11 := h (M v1 x) x x
  have h12 := T (T h11 (C h8 (C h10 h8))) h10
  have h13 := h x x v1
  have h14 := C h8 (C (S h13) h8)
  let v15 := M v1 v1
  have h16 := h v15 x x
  have h17 := C (T (T (T h16 h14) (C h8 (C h9 h8))) (S h11)) h7
  have h18 := S h16
  have h19 := C h8 (C h13 h8)
  T (T (T (T (T (T (T (T h13 (h x v15 v1)) (C (R v15) (T (T h17 (C h12 (T (T (T h9 h19) h18) (C (h v1 v1 z) h8)))) (S (h (M v15 z) v1 x))))) (S (h z v15 v1))) (C h5 (T (T (T (T (T (h v1 v1 x) (C (T (T h9 h19) h18) (T (T h16 h14) h10))) h17) (C h12 (T (T h9 (C h8 (C (h x x v0) h8))) (S (h (M v1 v0) x x))))) (S (h v0 v1 x))) (C h4 h7)))) (S (h v6 z v1))) (h v6 z v3)) (C h5 (T (C (S h4) (R v3)) (S (h v2 v0 v1))))) (S (h y z v0))

@[equational_result]
theorem Equation522_implies_Equation711 (G: Type _) [Magma G] (h: Equation522 G) : Equation711 G := fun x y z =>
  let v0 := M x z
  let v1 := M v0 z
  let v2 := M y v1
  have h3 := S (h x v2 v2)
  have h4 := R v2
  let v5 := M y v2
  have h6 := h x v5 z
  have h7 := h v0 v1 x
  have h8 := h x v0 z
  have h9 := R v0
  have h10 := h z v0 v0
  have h11 := R x
  have h12 := R v1
  have h13 := h v0 v1 z
  have h14 := h z v1 v1
  have h15 := R z
  have h16 := R v5
  have h17 := h v1 v5 z
  have h18 := C h4 (C h4 (C (T (T h17 (C h16 (C h16 (C h15 (T (C h12 (T (T h14 (C h12 (S h13))) (C h12 (C h11 (T h10 (C h9 (S h8))))))) (S h7)))))) (S h6)) h4))
  have h19 := h y v2 v1
  have h20 := R y
  have h21 := T (T h6 (C h16 (C h16 (C h15 (T h7 (C h12 (T (T (C h12 (C h11 (T (C h9 h8) (S h10)))) (C h12 h13)) (S h14)))))))) (S h17)
  T (h x y y) (C h20 (T (C h20 (C h20 (C h11 (T (T h19 h18) (C h4 (T (C h4 (T (T (T (T (C h21 h4) (C h12 (T (h v2 x y) (C h21 (C h11 (C h20 (T (C h4 (T h19 h18)) h3))))))) (S (h y v1 x))) h19) h18)) h3)))))) (S (h v2 y x))))

@[equational_result]
theorem Equation1710_implies_Equation1865 (G: Type _) [Magma G] (h: Equation1710 G) : Equation1865 G := fun x y z =>
  let v0 := M y y
  let v1 := M z z
  let v2 := M v1 v1
  let v3 := M v2 v0
  let v4 := M x v0
  let v5 := M v4 v1
  have h6 := R v3
  let v7 := M v0 v5
  let v8 := M x x
  have h9 := h v1 v4 v4
  let v10 := M (M v4 v4) v4
  let v11 := M (M v5 v5) v5
  have h12 := S (h y y v1)
  let v13 := M v2 y
  let v14 := M v8 v4
  T (T (T (T (T (h x v0 v0) (C (T (h (M v0 x) v4 x) (C (S (h v0 x y)) (R v14))) (R (M (M v0 v0) v0)))) (S (h v14 v0 v0))) (h v14 v5 v3)) (C (T (T (T (T (S (h v1 v4 x)) (h v1 v0 v1)) (C (T (h (M v0 v1) v2 v1) (C (S (h v1 v1 y)) (S (h v1 v1 z)))) (T (h v3 v13 y) (C (T (C (T (T (h v13 v0 x) (C (T h12 (h y y y)) (R (M v8 v0)))) (S (h (M v0 y) v0 x))) h6) (S (h y v0 v1))) h12)))) (h v3 v11 v5)) (C (T (C (T (T (h v11 v1 x) (C (T (T (T (C h9 (R v11)) (S (h v10 v5 v5))) (h v10 v5 y)) (C (S h9) (R v7))) (R (M v8 v1)))) (S (h v7 v1 x))) h6) (S (h v5 v0 v1))) (S (h v5 v5 v5)))) (R (M (M v3 v3) v5)))) (S (h v5 v5 v3))

@[equational_result]
theorem Equation1964_implies_Equation3737 (G: Type _) [Magma G] (h: Equation1964 G) : Equation3737 G := fun x y z =>
  let v0 := M y z
  let v1 := M x z
  let v2 := M v1 v0
  have h3 := h v2 x x
  let v4 := M x x
  have h5 := R v4
  let v6 := M x v2
  have h7 := h v6 x v1
  let v8 := M x v1
  have h9 := R v8
  have h10 := R v6
  have h11 := h z v1 y
  have h12 := R x
  have h13 := h (M v1 y) x v2
  have h14 := h y x v1
  have h15 := C h12 (T (T h14 (C (C h12 (T h13 (C (C h12 (S h11)) h10))) h9)) (S h7))
  have h16 := T (T h7 (C (C h12 (T (C (C h12 h11) h10) (S h13))) h9)) (S h14)
  have h17 := C h12 h16
  let v18 := M z v2
  have h19 := R v2
  T (T (T (T (T h15 (h (M x v6) v2 z)) (C (C h19 (T (T (C (T (T (T (h z v2 y) (C (C h19 (T (h v0 x v1) (C h16 h9))) (R (M v2 y)))) (S (h v8 v2 y))) (C h12 (T (h v1 z v2) (C (T (C h11 (R (M v2 v1))) (S (h y v2 v1))) (R v18))))) h17) (S (h v18 x y))) (C (R z) (T h3 (C h17 h5))))) (R (M v2 z)))) (S (h (M (M x y) v4) v2 z))) (C h15 h5)) (S h3)

@[equational_result]
theorem Equation3791_implies_Equation4023 (G: Type _) [Magma G] (h: Equation3791 G) : Equation4023 G := fun x y z =>
  let v0 := M z x
  let v1 := M z v0
  have h2 := h v1 y z
  let v3 := M x y
  let v4 := M y z
  let v5 := M z v1
  have h6 := h y z x
  have h7 := h x y z
  let v8 := M v1 y
  let v9 := M y v1
  let v10 := M v1 v1
  have h11 := R v1
  let v12 := M v3 v1
  let v13 := M x x
  T (T (T (T (T (T (h x y x) (C (h x x x) (h y x x))) (S (h v13 v3 v13))) (h v13 v3 v4)) (C (T (T (T (C h6 (T (h x x y) (C (T (T (T (h y x y) (C (h y y v1) (T (T (T (T (h x y v1) (h (M v1 x) v9 v8)) (C (T (T (C (T (T (T (h v1 y v3) (C (R v12) (T (T (T (h y v3 v0) (C (h v0 y z) (T (S h6) (h y z v0)))) (S (h v4 (M v0 y) v1))) (S (h z v0 y))))) (h v12 v1 v1)) (C (T (T (C h11 (T (C h7 h11) (S (h v4 z v0)))) (S (h v0 v4 z))) (S h7)) (R v10))) (h v1 x y)) (S (h v10 v9 v3))) (S (h v1 y v1))) (S (h v1 v1 y)))) (S (h y v1 v1))) (h y v1 y)))) (S (h v9 (M y y) v8))) (S (h v1 y y))) (R v3)))) (S (h v0 v8 v3))) (C (h z x y) h2)) (S (h v3 v5 v4))) (T (C h7 h6) (S (h v4 v3 v0))))) (S (h v5 v4 v3))) (S h2)

@[equational_result]
theorem Equation1507_implies_Equation759 (G: Type _) [Magma G] (h: Equation1507 G) : Equation759 G := fun x y z =>
  let v0 := M y x
  let v1 := M v0 z
  let v2 := M z v1
  let v3 := M y v2
  have h4 := R (M z (M z z))
  let v5 := M z v2
  have h6 := R (M x (M x z))
  have h7 := h z v0 v3
  have h8 := S h7
  let v9 := M v3 (M v3 v0)
  have h10 := h v9 v1 v3
  let v11 := M v3 (M v3 v1)
  have h12 := R v11
  have h13 := h v11 z x
  have h14 := h x y v2
  let v15 := M v2 (M v2 y)
  let v16 := M z v0
  let v17 := M z v16
  T (T (h x y x) (C (T (T (T (T (T (h v0 z z) (C (T (T (h v16 z x) (C (T (T (T (T (h v17 x x) (C (T (T (T (C h14 (R v17)) (S (h v15 v0 z))) (h v15 v0 v3)) (C (S h14) (R v9))) (R (M x (M x x))))) (S (h v9 x x))) h10) (C h8 h12)) h6)) (S h13)) h4)) (C (T (T h13 (C (T (T (T (C h7 h12) (S h10)) (h v9 v1 z)) (C h8 (R v5))) h6)) (S (h v5 z x))) h4)) (S (h v2 z z))) (C (h z v2 y) (h v1 z v2))) (S (h (M y v3) (M v2 z) v2))) (R (M x (M x y))))) (S (h v3 y x))

@[equational_result]
theorem Equation1507_implies_Equation4162 (G: Type _) [Magma G] (h: Equation1507 G) : Equation4162 G := fun x y z =>
  let v0 := M y x
  let v1 := M v0 z
  let v2 := M v1 z
  have h3 := C (S (h v1 v2 v1)) (S (h z v1 v2))
  let v4 := M v1 (M v1 v2)
  have h5 := h v4 (M v2 v1) v2
  let v6 := M v0 (M v0 v0)
  have h7 := h x y v2
  let v8 := M v2 (M v2 y)
  let v9 := M v2 v0
  let v10 := M v2 v9
  let v11 := M x y
  let v12 := M x v11
  have h13 := h y x z
  let v14 := M z (M z x)
  let v15 := M v1 (M v1 v11)
  T (T (T (T (T (T (T (T (T (C (h x v11 v1) (h y x v11)) (S (h v15 (M v11 x) v11))) (h v15 y x)) (C (T (T (T (T (C h13 (R v15)) (S (h v14 v11 v1))) (h v14 v11 x)) (C (T (S h13) (h y x y)) (R (M x v12)))) (S (h (M y v0) v11 x))) (R v12))) (S (h v0 y x))) (h v0 v2 v1)) (C (T (h v9 v2 v1) (C (T (T (h v10 x x) (C (T (T (T (C h7 (R v10)) (S (h v8 v0 v2))) (h v8 v0 v0)) (C (S h7) (R v6))) (R (M x (M x x))))) (S (h v6 x x))) (R v4))) (T (T h5 h3) (C (R v1) (h z v0 v0))))) (S (h v4 v6 v1))) h5) h3

@[equational_result]
theorem Equation2779_implies_Equation3214 (G: Type _) [Magma G] (h: Equation2779 G) : Equation3214 G := fun x y z =>
  have h0 := R x
  let v1 := M y z
  let v2 := M v1 z
  let v3 := M v2 y
  have h4 := h v3 v2 z
  have h5 := S h4
  have h6 := R v2
  let v7 := M v3 z
  let v8 := M (M v2 z) v7
  have h9 := h v2 x v1
  let v10 := M v3 x
  have h11 := R v10
  let v12 := M v10 v2
  let v13 := M v2 x
  have h14 := h x x z
  let v15 := M x z
  T (T h14 (C (T (h (M v15 v15) v2 x) (C (T (T (C (R v13) (S h14)) (C (T (T (T (T (h v13 x v10) (C (C (R (M x v10)) (T (T (T (T (h (M v13 v10) x v2) (C (C (R (M x v2)) (T (S (h v3 v2 x)) h4)) h0)) (S (h v8 x v2))) (h v8 v10 v2)) (C (C (R v12) h5) h11))) h0)) (S (h (M v12 v3) x v10))) (C (C h11 h9) (R v3))) (S (h (M (M x v1) (M v2 v1)) v3 x))) h0)) (S h9)) h6)) h0)) (C (T (C (T (T (T (T (h v2 x y) (C (C (R (M x y)) (h v3 y z)) h0)) (S (h (M v1 v7) x y))) (C (T (h v1 v3 z) (C (R (M v7 v2)) h4)) (R v7))) (S (h v8 v7 v2))) h6) h5) h0)

@[equational_result]
theorem Equation3211_implies_Equation3601 (G: Type _) [Magma G] (h: Equation3211 G) : Equation3601 G := fun x y z =>
  let v0 := M y x
  let v1 := M v0 z
  have h2 := R v1
  let v3 := M x y
  have h4 := R v3
  have h5 := R z
  let v6 := M z v1
  have h7 := h v1 z v6
  have h8 := S h7
  have h9 := R v6
  have h10 := h z v6 v1
  have h11 := h v1 z v1
  have h12 := h v6 v1 v6
  have h13 := C (T h12 (C (C (C (T (C h11 h9) (S h10)) h9) h9) h2)) h5
  have h14 := R v0
  have h15 := h z v0 z
  have h16 := h v0 v1 z
  have h17 := T h16 (C (S h15) h2)
  have h18 := R y
  have h19 := R x
  T (h v3 v1 z) (C (T (C (T (C (C (T h7 (C (T (C (C (C (T h10 (C (S h11) h9)) h9) h9) h2) (S h12)) h5)) h5) h5) (C (C (T (T (T h13 h8) (h v1 z v3)) (C (T (C (C (C (T (h z v3 v0) (C (T (T (C (T (C (C (C (T (h x y v0) (C (T (C (C (C (T (h y v6 x) (C (T (C (C (C (T (C h15 h2) (S h16)) h19) h19) h18) (S (h x y x))) h9)) h17) h14) h19) (S (h v0 x v6))) h18)) h18) h17) h14) (S (h v6 v0 y))) h5) h13) h8) h4)) h4) h4) h2) (S (h v3 v1 v3))) h5)) h5) h5)) h4) (S (h z v3 z))) h2)

@[equational_result]
theorem Equation2944_implies_Equation1670 (G: Type _) [Magma G] (h: Equation2944 G) : Equation1670 G := fun x y z =>
  let v0 := M z y
  let v1 := M v0 z
  let v2 := M x y
  let v3 := M v2 v1
  have h4 := R v3
  have h5 := R v1
  let v6 := M (M x (M x z)) z
  have h7 := h z v6 v0
  have h8 := S h7
  have h9 := R v0
  have h10 := h z x z
  have h11 := R v6
  have h12 := C (C (T h10 (C h11 h10)) h9) h9
  have h13 := S h10
  have h14 := C (C h9 (C h9 (T h7 (C (C (T (C h11 h13) h13) h9) h9)))) h5
  have h15 := S (h v0 x v0)
  let v16 := M (M x (M x v0)) v0
  have h17 := C (C (T (C (R v16) h15) h15) h5) h5
  have h18 := h v0 v16 v1
  have h19 := R y
  have h20 := S (h x x x)
  let v21 := M (M x (M x x)) x
  T (T (h x v21 y) (C (C (T (C (R v21) h20) h20) h19) h19)) (C (R v2) (T (T (h y z v3) (C (C (C (R z) (T (T (T h18 h17) h14) (C (T (T (T (C (T (T h18 h17) h14) (C h9 (T h12 h8))) (S (h (M (M z v0) v0) v0 v1))) h12) h8) h5))) h4) h4)) (S (h v1 z v3))))

@[equational_result]
theorem Equation1304_implies_Equation1507 (G: Type _) [Magma G] (h: Equation1304 G) : Equation1507 G := fun x y z =>
  let v0 := M y x
  let v1 := M z y
  let v2 := M z v1
  let v3 := M v0 v2
  have h4 := R v3
  have h5 := R v0
  let v6 := M v0 x
  let v7 := M (M v6 x) v0
  have h8 := R v2
  have h9 := h v0 v0 x
  let v10 := M (M (M z x) x) z
  have h11 := R y
  have h12 := h z z x
  let v13 := M v6 y
  let v14 := M (M v1 y) y
  have h15 := h y v14 v13
  have h16 := R v14
  have h17 := R v13
  have h18 := h y y x
  have h19 := T h18 (C h18 h17)
  have h20 := h z y y
  have h21 := S h18
  have h22 := R x
  T (T (h x v3 v0) (C h4 (C (T (C (T (T (T (C h22 (C h19 h22)) (S (h y x v13))) h15) (C h16 (T (C (T (C h21 h17) h21) h16) (S h20)))) h5) (C (T (T (T (C h16 (T h20 (C h19 h16))) (S h15)) (h y v3 v1)) (C h4 (T (T (C (C (T (C h11 (C (T h12 (C h12 (R v10))) h11)) (S (h z y v10))) (R v1)) h4) (C h8 (C (T h9 (C h9 (R v7))) h8))) (S (h v0 v2 v7))))) h5)) h4))) (S (h v3 v3 v0))

@[equational_result]
theorem Equation914_implies_Equation1996 (G: Type _) [Magma G] (h: Equation914 G) : Equation1996 G := fun x y z =>
  let v0 := M y x
  have h1 := h v0 y y
  let v2 := M y y
  let v3 := M x x
  have h4 := R y
  let v5 := M z z
  let v6 := M v0 v5
  have h7 := h v5 v0 y
  have h8 := R v0
  let v9 := M v6 v2
  let v10 := M y v5
  let v11 := M v10 v0
  have h12 := h v10 v11 z
  have h13 := R v5
  have h14 := R v11
  have h15 := h y v11 v0
  T (T (h x y v5) (C h4 (T (C h8 (C h7 h13)) (S (h v9 v0 z))))) (C (T (T h15 (C h14 (T (T (T (h (M (M v11 y) (M v0 v0)) v11 v5) (C h14 (T (C (S h15) (C (h v5 y z) h13)) (S (h (M v10 v5) y z))))) (C h14 (C h12 h13))) (S (h (M (M v11 v10) v5) v11 z))))) (S h12)) (T (T (T (T (h v9 v0 y) (C h8 (T (T (C (S h7) (R v2)) (h (M v5 v2) z v5)) (C (R z) (T (C (S (h z z y)) (R (M v5 v5))) (S (h z z z))))))) (h v6 y v3)) (C h4 (T (T (T (T (C (S (h x y z)) (R (M v3 v3))) (S (h x x x))) (h x y x)) (C h4 (C h1 (R v3)))) (S (h (M (M y v0) v2) y x))))) (S h1)))

@[equational_result]
theorem Equation1537_implies_Equation658 (G: Type _) [Magma G] (h: Equation1537 G) : Equation658 G := fun x y z =>
  let v0 := M z z
  let v1 := M v0 y
  let v2 := M y v1
  let v3 := M x v2
  have h4 := h z z z
  have h5 := R v0
  have h6 := h z z v0
  have h7 := R z
  have h8 := h v0 z v2
  have h9 := h v0 z y
  have h10 := R v2
  have h11 := R y
  have h12 := R (M x x)
  have h13 := T (T (h v0 x z) (C h12 (T (T (C h7 (T (C h5 h4) (S h6))) h8) (C h5 (C h10 (S h9)))))) (S (h v2 x v0))
  let v14 := M v3 v3
  have h15 := R v3
  have h16 := C h5 (C h15 (T (T (T (T (T (h v14 x y) (C h12 (C h11 (T (T (C (R v14) (T (h y z v1) (C h13 (R (M v1 v2))))) (S (h v1 v3 v2))) (C h13 h11))))) (S (h v2 x y))) (h v2 v0 v0)) (C (R (M v0 v0)) (T (T (C h5 (C h10 h9)) (S h8)) (C h7 (T h6 (C h5 (S h4))))))) (S (h v0 v0 z))))
  have h17 := h v3 z v3
  T (T (h x y v0) (C (R (M y y)) (T (T (T (C h5 (T (T (T (C (R x) h13) h17) h16) (C h13 (C h15 h13)))) (S (h v3 z v2))) h17) h16))) (S (h v3 y v0))

@[equational_result]
theorem Equation2958_implies_Equation1467 (G: Type _) [Magma G] (h: Equation2958 G) : Equation1467 G := fun x y z =>
  let v0 := M y z
  let v1 := M z v0
  let v2 := M x y
  let v3 := M v2 v1
  have h4 := R x
  let v5 := M v3 x
  have h6 := S (h v3 x v3)
  let v7 := M (M x (M x v3)) v3
  have h8 := R z
  let v9 := M v1 z
  have h10 := S (h v1 x v1)
  let v11 := M (M x (M x v1)) v1
  have h12 := R v0
  have h13 := S (h z x z)
  let v14 := M (M x (M x z)) z
  let v15 := M (M x v2) y
  have h16 := R y
  have h17 := h y x y
  let v18 := M (M y (M y x)) x
  have h19 := h x y x
  T (T (h x v2 x) (C (T (T (C (C (R v2) (T (T (T (T (T (C (C (T h19 (C (R v18) h19)) h16) h4) (S (h y v18 x))) (h y y z)) (C (T (C (C (T h17 (C (R v15) h17)) h12) h16) (S (h v0 v15 y))) h8)) (C (T (T (T (h v0 v14 z) (C (C (T (C (R v14) h13) h13) h12) h8)) (h v9 v11 v1)) (C (C (T (C (R v11) h10) h10) (R v9)) (R v1))) h8)) (S (h v1 v1 z)))) h4) (h v5 v7 v3)) (C (C (T (C (R v7) h6) h6) (R v5)) (R v3))) h4)) (S (h v3 v3 x))

@[equational_result]
theorem Equation684_implies_Equation4007 (G: Type _) [Magma G] (h: Equation684 G) : Equation4007 G := fun x y z =>
  let v0 := M y x
  let v1 := M z v0
  let v2 := M z (M v1 v0)
  let v3 := M v1 z
  have h4 := h z z v0
  have h5 := R v3
  have h6 := S (h z z x)
  let v7 := M z (M (M z x) x)
  have h8 := R z
  have h9 := R v1
  have h10 := S (h v3 v3 x)
  let v11 := M v3 (M (M v3 x) x)
  let v12 := M v0 x
  let v13 := M v0 (M v12 x)
  have h14 := h v0 v0 x
  let v15 := M y v12
  have h16 := h y y x
  have h17 := R y
  let v18 := M x y
  let v19 := M v18 (M (M v18 x) x)
  let v20 := M y v18
  have h21 := h v18 v18 x
  T (T (T (T (h v18 y v18) (C h17 (T (T (T (C (R v18) (C (R v20) (T h21 (C h21 (R v19))))) (S (h v20 v18 v19))) (C h17 (C (R x) (T h16 (C h16 (R v15)))))) (S (h x y v15))))) (h v0 z v0)) (C h8 (T (T (T (T (C (R v0) (C h9 (T h14 (C h14 (R v13))))) (S (h v1 v0 v13))) (h v1 v3 v11)) (C h5 (T (T (C h9 (T (C h10 (R v11)) h10)) (C h9 (T (h v3 z v7) (C h8 (C h5 (T (C h6 (R v7)) h6)))))) (S (h z v1 z))))) (C h5 (T h4 (C h4 (R v2))))))) (S (h v3 z v2))

@[equational_result]
theorem Equation2944_implies_Equation1165 (G: Type _) [Magma G] (h: Equation2944 G) : Equation1165 G := fun x y z =>
  let v0 := M y x
  let v1 := M z v0
  let v2 := M v1 z
  let v3 := M y v2
  have h4 := R v3
  have h5 := R v2
  let v6 := M (M x (M x z)) z
  have h7 := h z v6 v0
  have h8 := S h7
  have h9 := R v0
  have h10 := h z x z
  have h11 := R v6
  have h12 := C (C (T h10 (C h11 h10)) h9) h9
  have h13 := R v1
  have h14 := S h10
  have h15 := C (C h13 (C h13 (T h7 (C (C (T (C h11 h14) h14) h9) h9)))) h5
  have h16 := S (h v1 x v1)
  let v17 := M (M x (M x v1)) v1
  have h18 := C (C (T (C (R v17) h16) h16) h5) h5
  have h19 := h v1 v17 v2
  let v20 := M (M x (M x y)) y
  have h21 := h y x y
  T (h x y v0) (C (T (C (C (T h21 (C (R v20) h21)) h9) h9) (S (h y v20 v0))) (T (T (h v0 z v3) (C (C (C (R z) (T (T (T h19 h18) h15) (C (T (T (T (C (T (T h19 h18) h15) (C h13 (T h12 h8))) (S (h (M v1 v0) v1 v2))) h12) h8) h5))) h4) h4)) (S (h v2 z v3))))

@[equational_result]
theorem Equation3620_implies_Equation3776 (G: Type _) [Magma G] (h: Equation3620 G) : Equation3776 G := fun x y z =>
  let v0 := M y z
  let v1 := M z x
  let v2 := M v0 v1
  have h3 := R v2
  have h4 := h y z v1
  have h5 := S h4
  have h6 := h v1 (M (M v1 z) y) v1
  have h7 := R v1
  have h8 := R z
  let v9 := M v2 x
  let v10 := M x y
  have h11 := h z x v10
  let v12 := M v10 x
  let v13 := M v12 z
  have h14 := R y
  have h15 := h v12 z y
  let v16 := M v0 v12
  have h17 := R v0
  have h18 := h x y x
  have h19 := h x v12 v0
  T (T (T (T h18 h19) (h v0 (M v16 x) v0)) (C h17 (T (T (T (T (T (T (C (T (S h19) (S h18)) h17) (C (R v10) (T (T h4 h6) (C h11 (C h5 h7))))) (S (h v2 v13 v10))) (C h3 (T (T (T (T h15 (h y v16 y)) (C h14 (T (T (T (C (S h15) h14) (h v13 y x)) (C (R x) (S h11))) (h x v1 v0)))) (S (h v9 z y))) (C (h v2 x v2) h8)))) (S (h z (M v9 v2) v2))) (C h8 (C (T (h v2 x z) (C h8 (T (T (C h7 (C h4 h7)) (S h6)) h5))) h3))) (S (h v2 v0 z))))) (S (h v0 v1 v0))

@[equational_result]
theorem Equation3791_implies_Equation4109 (G: Type _) [Magma G] (h: Equation3791 G) : Equation4109 G := fun x y z =>
  let v0 := M y z
  let v1 := M v0 z
  have h2 := S (h y z v1)
  let v3 := M z v1
  let v4 := M v1 y
  have h5 := h v1 y z
  have h6 := h z v1 y
  have h7 := S h5
  have h8 := h v0 z v1
  have h9 := S h8
  let v10 := M v1 v0
  have h11 := h v10 v3 v1
  have h12 := h v1 v0 z
  have h13 := h z v1 v0
  have h14 := h v4 v1 v0
  have h15 := h v0 v10 v3
  have h16 := T (T h12 (C (T (T h6 (h v0 v4 v3)) (C h7 h2)) (T (T h8 (h v10 v3 v0)) (C (T (T (T (T (T h15 (C h7 h9)) h14) (C (T (S h6) h13) h12)) (S h11)) h9) h7)))) (S (h v0 v1 v4))
  T (T (T (T (T (T (h x x v1) (h (M v1 x) (M x v1) (M x x))) (C (S (h x v1 x)) (S (h v1 x x)))) (S (h v1 v1 x))) (C (T (T (T (T (T (T h8 h11) (C (T (S h13) h6) (S h12))) (S h14)) (C h5 h8)) (S h15)) (C (R v0) h16)) (T (T h8 (h v10 v3 v4)) (C (T (C (R v4) h16) (S (h y v0 v1))) (T (T (C h6 h5) (S (h v4 v3 v0))) h2))))) (S (h (M v0 v1) (M y v0) v0))) (S (h v1 y v0))

@[equational_result]
theorem Equation684_implies_Equation2482 (G: Type _) [Magma G] (h: Equation684 G) : Equation2482 G := fun x y z =>
  let v0 := M y z
  let v1 := M v0 y
  let v2 := M x v1
  let v3 := M v2 z
  have h4 := S (h v3 v3 x)
  let v5 := M v3 (M (M v3 x) x)
  let v6 := M z v3
  have h7 := S (h z z x)
  let v8 := M z (M (M z x) x)
  have h9 := T (C h7 (R v8)) h7
  have h10 := R z
  have h11 := S (h v1 v1 v3)
  let v12 := M v1 (M (M v1 v3) v3)
  have h13 := R v0
  let v14 := M y (M (M y x) x)
  have h15 := h y y x
  have h16 := R y
  let v17 := M v1 (M (M v1 x) x)
  let v18 := M y v1
  have h19 := h v1 v1 x
  T (T (h x v1 v12) (C (T (T (h v1 y v1) (C h16 (T (T (T (T (T (C (R v1) (C (R v18) (T h19 (C h19 (R v17))))) (S (h v18 v1 v17))) (C h16 (C h13 (T h15 (C h15 (R v14)))))) (S (h v0 y v14))) (h v0 z v8)) (C h10 (C h13 h9))))) (S (h z y z))) (T (T (T (T (C (R x) (T (C h11 (R v12)) h11)) (h v2 z v8)) (C h10 (C (R v2) h9))) (h v6 v3 v5)) (C (R v3) (C (R v6) (T (C h4 (R v5)) h4)))))) (S (h v3 z v3))

@[equational_result]
theorem Equation711_implies_Equation2519 (G: Type _) [Magma G] (h: Equation711 G) : Equation2519 G := fun x y z =>
  let v0 := M z (M (M z x) x)
  let v1 := M x z
  have h2 := h z z x
  have h3 := R v1
  let v4 := M v1 y
  let v5 := M y v4
  let v6 := M v5 z
  let v7 := M y (M (M y x) x)
  have h8 := h y v1 v7
  have h9 := S h8
  have h10 := R v7
  have h11 := h y y x
  have h12 := C h3 (C h3 (T h11 (C h11 h10)))
  have h13 := R v4
  have h14 := S h11
  have h15 := R v5
  have h16 := C h15 (C (C (T h8 (C h3 (C h3 (T (C h14 h10) h14)))) h13) h13)
  have h17 := S (h v4 v4 x)
  let v18 := M v4 (M (M v4 x) x)
  have h19 := C h15 (C h15 (T (C h17 (R v18)) h17))
  have h20 := h v4 v5 v18
  have h21 := R v6
  T (h x v1 z) (C (T (T (h v1 v6 y) (C h21 (C h21 (C (T (T (T h20 h19) h16) (C h15 (T (T (T (C (C (T h12 h9) h13) (T (T h20 h19) h16)) (S (h (M v1 v4) v5 v4))) h12) h9))) (R y))))) (S (h v5 v6 y))) (T (C h3 (C h3 (T h2 (C h2 (R v0))))) (S (h z v1 v0))))

@[equational_result]
theorem Equation711_implies_Equation4640 (G: Type _) [Magma G] (h: Equation711 G) : Equation4640 G := fun x y z =>
  let v0 := M (M y z) z
  let v1 := M v0 (M (M v0 x) x)
  have h2 := h v0 x v1
  have h3 := S h2
  have h4 := R v1
  have h5 := h v0 v0 x
  have h6 := R x
  have h7 := C h6 (C h6 (T h5 (C h5 h4)))
  have h8 := h y x z
  let v9 := M y v0
  let v10 := M x y
  have h11 := S (h y v10 v9)
  have h12 := h y y z
  have h13 := R v10
  have h14 := C h13 (C h13 (T h12 (C h12 (R v9))))
  have h15 := S h5
  have h16 := T (T h2 (C h6 (C h6 (T (C h15 h4) h15)))) (S h8)
  let v17 := M x (M (M x x) x)
  have h18 := h x v10 v17
  have h19 := R v17
  have h20 := h x x x
  have h21 := C h13 (C (C (T (C h13 (C h13 (T h20 (C h20 h19)))) (S h18)) h16) h16)
  have h22 := S h20
  have h23 := C h13 (C h13 (T (C h22 h19) h22))
  T (T (T (T (T (T (C h13 (T (T (T h18 h23) (h (M v10 (M v10 x)) v10 v0)) (C (C (T h18 h23) (T (T h8 h7) h3)) (T (T (T (T (T h21 h14) h11) h8) h7) h3)))) h21) h14) h11) h8) h7) h3

@[equational_result]
theorem Equation492_implies_Equation2335 (G: Type _) [Magma G] (h: Equation492 G) : Equation2335 G := fun x y z =>
  let v0 := M x z
  let v1 := M y v0
  let v2 := M y v1
  let v3 := M v2 z
  have h4 := R v0
  have h5 := h v0 v0 y
  have h6 := h y v0 v1
  have h7 := h v0 v1 y
  have h8 := h y v0 y
  have h9 := R v1
  have h10 := R y
  have h11 := h v1 y v1
  have h12 := C h4 (T (C h10 (C h9 (C h9 (T h7 (C h9 (S h8)))))) (S h11))
  have h13 := S (h y v1 v1)
  have h14 := R v2
  have h15 := C h9 (C h10 (T (h v1 v1 y) (C h9 (C h9 (T (C h10 (T (h v2 v1 v2) (C h9 (C h14 (C h14 (T (C h14 (C h10 h5)) (S (h y v2 v0)))))))) (S (h v1 y v2)))))))
  have h16 := h v1 v0 y
  have h17 := R x
  have h18 := R z
  T (T (T (h x v0 z) (C h4 (T (C h17 (C h18 (C h18 (T (h v0 z x) (C h18 (T (C h4 (C h17 (T (h v0 v2 v0) (C (T (C h10 (T h16 (C h4 (T (T (T (T (T h15 h13) h6) h12) (C h4 (T h16 (C h4 (T (T (T h15 h13) h6) h12))))) (C h4 (C h4 (T (C h4 (T h11 (C h10 (C h9 (C h9 (T (C h9 h8) (S h7))))))) (S h6)))))))) (S (h v0 y v0))) (C h4 (S h5)))))) (S (h x v0 v0)))))))) (S (h z x z))))) (C h4 (T (h z v3 v2) (C (R v3) (S (h v2 z v2)))))) (S (h v3 v0 y))

@[equational_result]
theorem Equation492_implies_Equation4013 (G: Type _) [Magma G] (h: Equation492 G) : Equation4013 G := fun x y z =>
  let v0 := M y z
  let v1 := M z v0
  let v2 := M v1 x
  let v3 := M x y
  have h4 := h x v1 v3
  have h5 := S h4
  have h6 := h v0 y v0
  have h7 := h y z y
  have h8 := R v0
  have h9 := h z v0 y
  have h10 := R y
  have h11 := R z
  have h12 := C h11 (T (C h10 (C h8 (C h8 (T h9 (C h8 (S h7)))))) (S h6))
  have h13 := h y z v0
  have h14 := h y v3 x
  have h15 := h x y x
  have h16 := R v3
  have h17 := R x
  have h18 := h v3 x v3
  have h19 := S h13
  have h20 := C h11 (T h6 (C h10 (C h8 (C h8 (T (C h8 h7) (S h9))))))
  have h21 := R v1
  have h22 := C (T h13 h12) (T (T (T (C h16 (C h16 (C h21 (T h4 (C h21 (T (C h17 (C h16 (C h16 (T (T (T h20 h19) h14) (C h16 (S h15)))))) (S h18))))))) (S (h v3 v3 v1))) h18) (C h17 (C h16 (C h16 (T (T (T (C h16 h15) (S h14)) h13) h12)))))
  have h23 := R v2
  have h24 := h y v2 v3
  T (C h17 (T h24 (C h23 (T (T (T h22 h5) (h x v1 v2)) (C h21 (T (C h17 (C h23 (C h23 (T (T (T h20 h19) h24) (C h23 (T h22 h5)))))) (S (h v2 x v2)))))))) (S (h v2 x v1))

@[equational_result]
theorem Equation1181_implies_Equation14 (G: Type _) [Magma G] (h: Equation1181 G) : Equation14 G := fun x y =>
  let v0 := M x y
  let v1 := M y v0
  have h2 := h v1 v0 v1
  have h3 := R x
  have h4 := R v0
  have h5 := h v1 v0 y
  let v6 := M y v1
  let v7 := M (M y v6) v0
  have h8 := R v1
  have h9 := R y
  have h10 := h v0 x v0
  let v11 := M (M v0 (M v0 v0)) x
  have h12 := h v0 y y
  have h13 := S h12
  have h14 := h (M v6 y) y y
  have h15 := h (M v1 y) x y
  let v16 := M v0 x
  have h17 := h x v0 v0
  T (T h17 (C h4 (T (T (T (T (T (h (M (M v0 v16) v0) v1 v0) (C h8 (C (T (T (T (C h4 (S h17)) (h v16 v0 x)) (C h4 (C (T (T (T (T (T (C h3 (T (C h3 (C (T h12 (C h9 (T h14 (C h9 (C (C h9 h13) h9))))) h3)) (S h15))) (C h3 (T (T (T h15 (C h3 (T (C (T (C h9 (T (C h9 (C (C h9 h12) h9)) (S h14))) h13) h3) (C (C h3 (h y x x)) h3)))) (S (h (M (M x v0) x) x x))) (C (C h3 h10) h3)))) (S (h v11 x x))) (h v11 y x)) (C h9 (C (C h3 (S h10)) h9))) (S (h y y x))) h4))) (C h4 h5)) h8))) (S (h v7 v1 v0))) (h v7 x v0)) (C h3 (C (T (C h4 (S h5)) (C h4 h2)) h3))) (S (h (M (M v1 (M v1 v1)) v0) x v0))))) (S h2)

@[equational_result]
theorem Equation2196_implies_Equation1470 (G: Type _) [Magma G] (h: Equation2196 G) : Equation1470 G := fun x y z =>
  let v0 := M z y
  let v1 := M z v0
  let v2 := M x y
  let v3 := M v2 v1
  let v4 := M v3 v1
  let v5 := M v4 v1
  let v6 := M (M v1 y) y
  let v7 := M (M v0 v0) v0
  let v8 := M (M y v1) v1
  have h9 := h x y v1
  let v10 := M y z
  let v11 := M y v2
  have h12 := S (h v4 v11 v2)
  have h13 := h x y v2
  have h14 := C h13 (h y v2 v1)
  let v15 := M v2 y
  let v16 := M v15 y
  T (T (T (T (T (T h13 (C (R (M v11 v2)) (T (T (T (T h14 h12) (h v4 x x)) (C (R (M (M x x) x)) (T (T (T (C (R v4) h9) (S (h v8 v2 v1))) (h v8 v2 y)) (C (R v16) (S h9))))) (S (h v16 x x))))) (S (h v15 y v2))) (C (T h14 h12) (T (T (T (T (h y z v3) (C (R (M (M z v3) v3)) (T (T (T (T (h v10 z x) (C (R (M (M z x) x)) (T (T (T (T (h (M v10 z) v2 x) (C (R (M (M v2 x) x)) (T (S (h x y z)) h9))) (S (h v8 v2 x))) (h v8 v0 v0)) (C (R v7) (S (h z y v1)))))) (S (h v7 z x))) (h v7 v1 y)) (C (R v6) (S (h z v0 v0)))))) (S (h v6 z v3))) (h v6 v3 v1)) (C (R v5) (S (h v2 v1 y)))))) (S (h v5 v2 v1))) (h v5 (M v1 v3) v3)) (C (S (h v2 v1 v3)) (S (h v1 v3 v1)))

@[equational_result]
theorem Equation2779_implies_Equation4612 (G: Type _) [Magma G] (h: Equation2779 G) : Equation4612 G := fun x y z =>
  let v0 := M x x
  let v1 := M v0 y
  let v2 := M y z
  let v3 := M v2 z
  have h4 := h v3 v2 v1
  have h5 := R v2
  let v6 := M y v3
  have h7 := h v2 v2 v0
  let v8 := M v2 v0
  have h9 := h y v0 v1
  have h10 := R v0
  let v11 := M v0 v0
  have h12 := h x x x
  have h13 := h v0 v0 v3
  let v14 := M v1 v0
  let v15 := M v0 v3
  let v16 := M v15 v15
  T (T (T (T (T (T (T (T (h v1 z v1) (C (C (R (M z v1)) (T (T (T (h (M v1 v1) x v0) (C (C (R (M x v0)) (T (S (h v0 v0 y)) h13)) (R x))) (S (h v16 x v0))) (h v16 v1 v0))) (R z))) (S (h (M v14 (M v16 v0)) z v1))) (C (R v14) (S h13))) (C (T (C (C (T (T (h v0 v0 v0) (C (C (R v11) (T (h v11 v0 x) (C (T (C (C h10 h12) (S h12)) (S (h v11 x x))) h10))) h10)) (S (h v11 v0 v0))) h9) h10) (S (h (M (M v0 v1) (M y v1)) v0 v0))) h10)) (S h9)) (h y v2 v3)) (C (T (C (C (T h7 (C (T (h (M v8 v8) v3 v2) (C (T (C (R (M v3 v2)) (S h7)) (S (h y v2 z))) (R v3))) h5)) h4) (R v6)) (S (h (M (M v2 v1) (M v3 v1)) v6 v2))) h5)) (S h4)

