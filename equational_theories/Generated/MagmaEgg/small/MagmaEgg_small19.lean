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
theorem Equation2105_implies_Equation4491 (G: Type _) [Magma G] (h: Equation2105 G) : Equation4491 G := fun x y z =>
  let v0 := M y y
  let v1 := M x v0
  let v2 := M (M z x) z
  have h3 := R v0
  have h4 := R v2
  have h5 := S (h v0 y x)
  let v6 := M x x
  have h7 := R v6
  have h8 := R y
  have h9 := h y y y
  have h10 := C (S h9) h3
  have h11 := h y v0 y
  let v12 := M v2 v2
  have h13 := R z
  T (T (h v1 z v1) (C (T (h (M (M z v1) z) v2 y) (C (C (T (T (T (C h4 (C (C h13 (T (C (T (h x x y) (C (C (T (T (h v6 y x) (C (C (T (T (T (C h9 h7) (S (h y v0 x))) h11) h10) h8) h7)) h5) (R x)) h3)) h3) (S (h x v0 y)))) h13)) (h v12 y x)) (C (C (T (T (T (C h9 (R v12)) (S (h y v0 v2))) h11) h10) h8) h7)) h5) h4) h3)) (R (M v1 v1)))) (S (h v2 v0 v1))

@[equational_result]
theorem Equation2196_implies_Equation3370 (G: Type _) [Magma G] (h: Equation2196 G) : Equation3370 G := fun x y z =>
  let v0 := M z x
  let v1 := M z v0
  let v2 := M y v1
  let v3 := M (M v2 v1) v1
  let v4 := M v1 y
  let v5 := M v4 y
  have h6 := h z v0 v0
  let v7 := M (M v0 v0) v0
  let v8 := M v0 x
  let v9 := M x z
  T (T (T (T (T (C (T (T (T (T (h x z y) (C (R (M (M z y) y)) (T (T (T (T (h v9 z x) (C (R v8) (T (h (M v9 z) v0 x) (C (T (T (h (M v8 x) v1 x) (C (R (M (M v1 x) x)) (T (S (h z v0 x)) h6))) (S (h v7 v1 x))) (S (h z x z)))))) (S (h v7 z x))) (h v7 v1 y)) (C (R v5) (S h6))))) (S (h v5 z y))) (h v5 (M v0 v1) v1)) (C (S (h z v0 v1)) (S (h v0 v1 y)))) (R y)) (h v4 y x)) (C (R (M (M y x) x)) (T (h v5 v2 v1) (C (R v3) (S (h y v1 y)))))) (S (h v3 y x))) (h v3 (M v1 v2) v2)) (C (S (h y v1 v2)) (S (h v1 v2 v1)))

@[equational_result]
theorem Equation3131_implies_Equation1152 (G: Type _) [Magma G] (h: Equation3131 G) : Equation1152 G := fun x y z =>
  let v0 := M x y
  let v1 := M z v0
  let v2 := M v1 z
  let v3 := M y v2
  have h4 := R v2
  have h5 := R v1
  have h6 := h v1 v2 v1
  have h7 := h z v1 v1
  have h8 := h z v2 z
  have h9 := S h8
  have h10 := R z
  have h11 := h v0 z z
  have h12 := C (C h11 h10) h4
  T (T (T (h x v2 v2) (C (C (C (T (C (T (h v2 v1 v1) (C (C (T (C (C (T (T (T h6 (C (S h7) h4)) (C (T h8 (C (C (S h11) h10) h4)) h4)) (C (T (T (T h12 h9) (h z v0 v2)) (C (T (T (C (T h12 h9) h4) (C h7 h4)) (S h6)) (R v0))) h4)) h4) h5) (S (h v0 v1 v2))) h5) h5)) (R x)) (S (h y x v1))) h4) h4) h4)) (C (C (C (T (h y v3 y) (C (S (h v2 y y)) (R v3))) h4) h4) h4)) (S (h v3 v2 v2))

@[equational_result]
theorem Equation3131_implies_Equation2186 (G: Type _) [Magma G] (h: Equation3131 G) : Equation2186 G := fun x y z =>
  let v0 := M z x
  let v1 := M y z
  let v2 := M v1 y
  let v3 := M v2 v0
  have h4 := h v2 y v3
  have h5 := R y
  have h6 := R v3
  have h7 := R v2
  have h8 := h y v1 v1
  have h9 := h v1 v2 v1
  have h10 := h z y v3
  have h11 := R v0
  have h12 := R v1
  T (T (h x z v0) (C (C (C (T (h v0 v3 y) (C (C (T (C (C (T (h v3 v0 v1) (C (T (C (C (T (C (h v0 v2 v2) h6) (S (h v2 v3 v2))) h12) h12) (C (T (C (T (T (T h4 (C (C (C (T (C h8 h7) (S h9)) h6) h6) h5)) (S h10)) (h z y y)) h12) (S (h y v1 y))) h12)) h11)) h11) h5) (S (h v1 y v0))) h5) h6)) h11) h11) (T (T h10 (C (C (C (T h9 (C (S h8) h7)) h6) h6) h5)) (S h4)))) (S (h v3 v2 v0))

@[equational_result]
theorem Equation3193_implies_Equation832 (G: Type _) [Magma G] (h: Equation3193 G) : Equation832 G := fun x y =>
  let v0 := M x x
  have h1 := R v0
  have h2 := h x x x
  have h3 := R x
  have h4 := h v0 v0 x
  have h5 := S h4
  have h6 := h v0 x x
  have h7 := C h6 h1
  have h8 := h x v0 v0
  have h9 := S (h y y x)
  have h10 := R y
  let v11 := M y x
  have h12 := S (h v11 v11 y)
  have h13 := R v11
  have h14 := h v11 y x
  have h15 := C (C (T (C (T (T (C h14 h13) h12) h14) h13) h12) h10) h10
  have h16 := h y v11 v11
  have h17 := C (S h6) h1
  have h18 := T (C (C (T (T h4 h17) (C (T h4 h17) h1)) h3) h3) (S h8)
  T h2 (C h18 (T (T (T h2 (C h18 h3)) (h v0 y y)) (C (C (T (C (T (T (T (C (T h16 h15) h10) h9) h16) h15) h10) h9) (T (C (T h8 (C (C (T (T (C (T h7 h5) h1) h7) h5) h3) h3)) h3) (S h2))) h1)))

@[equational_result]
theorem Equation3791_implies_Equation3959 (G: Type _) [Magma G] (h: Equation3791 G) : Equation3959 G := fun x y z =>
  let v0 := M x z
  let v1 := M v0 x
  let v2 := M y v0
  let v3 := M x y
  have h4 := h v0 x y
  let v5 := M v3 y
  have h6 := h y v0 x
  have h7 := C (S h6) (S h4)
  have h8 := h v1 v2 v3
  have h9 := h x y v0
  let v10 := M v2 x
  let v11 := M x v2
  T (T (T h9 (h v1 v2 v2)) (C (T (C h6 h4) (S h8)) (T (T (T (T (T (T (T (h v2 v2 x) (h v11 v10 v3)) (C (T (C (T (T h9 h8) h7) (R v11)) (S (h v1 x v2))) (T (C (R v10) h9) (S (h x v1 v2))))) (S (h x x v1))) (h x x z)) (h (M z x) v0 v3)) (C (S (h y z x)) (T (T (T (h v0 v3 y) (h v2 v5 v1)) (C (T h8 h7) (T (C (R v5) h4) (S (h y v2 v3))))) (S (h v1 y v2))))) (S (h z v1 y))))) (S (h v2 z v1))

@[equational_result]
theorem Equation3791_implies_Equation4525 (G: Type _) [Magma G] (h: Equation3791 G) : Equation4525 G := fun x y z =>
  let v0 := M y x
  let v1 := M z x
  let v2 := M x v0
  let v3 := M y z
  have h4 := S (h y x v3)
  let v5 := M v3 x
  let v6 := M x v3
  let v7 := M v3 y
  have h8 := h v0 v7 v6
  have h9 := h x v3 y
  let v10 := M y v0
  let v11 := M v0 v0
  T (T (T (T (T (T (T (T (T (T h9 h8) (C (S (h v3 y x)) h4)) (h v7 v0 v0)) (C (S h9) (R v11))) (h v6 v11 v10)) (C (T (C (R v10) (T (T (T h9 h8) (C (T (T (T (C (h x v3 x) (h y x x)) (S (h v5 (M x y) (M x x)))) (C (R v5) (h x y z))) (S (h x v1 v3))) h4)) (S (h v1 y x)))) (S (h v0 v1 y))) (T (S (h v0 y v0)) (h v0 y x)))) (S (h v1 v2 v0))) (C (h z x v0) (h x v0 z))) (S (h v2 v1 (M v0 z)))) (S (h v0 z x))

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
theorem Equation1537_implies_Equation4497 (G: Type _) [Magma G] (h: Equation1537 G) : Equation4497 G := fun x y z =>
  let v0 := M y y
  let v1 := M x v0
  let v2 := M v1 v1
  have h3 := h y y y
  have h4 := S h3
  have h5 := R v2
  have h6 := h y z v0
  let v7 := M z z
  have h8 := R v7
  have h9 := R y
  have h10 := R (M x x)
  have h11 := R v1
  have h12 := C h11 (T (T (h v7 x y) (C h10 (C h9 (T (T (T (C h8 h3) (S h6)) (h y v1 v0)) (C h5 h4))))) (S (h v2 x y)))
  have h13 := R v0
  have h14 := S (h v1 y v1)
  have h15 := C h13 (T (C h11 (T (T (h v0 v1 y) (C h5 (C h9 (T (T (T (C h13 h3) (S (h y y v0))) h6) (C h8 h4))))) (S (h v7 v1 y)))) h12)
  T (h v1 z v0) (C h8 (T (T (T (T h15 h14) (h v1 x v0)) (C h10 (T (T (T h15 h14) (h v1 y v7)) (C h13 (T (C h8 h12) (S (h v1 z v1))))))) (S (h x x v0))))

@[equational_result]
theorem Equation2105_implies_Equation2725 (G: Type _) [Magma G] (h: Equation2105 G) : Equation2725 G := fun x y z =>
  let v0 := M y x
  let v1 := M z z
  let v2 := M (M v0 v1) y
  let v3 := M v0 v0
  have h4 := R v3
  have h5 := R v1
  have h6 := R v2
  have h7 := h v1 z x
  have h8 := R (M x x)
  have h9 := R z
  have h10 := h z z z
  have h11 := S h10
  have h12 := h z v1 z
  let v13 := M v2 v2
  T (T (h x y v0) (C (T (h (M v0 y) v2 z) (C (C (T (T (T (C h6 (C (T (h v0 v1 z) (C (T (C (C (T (T h7 (C (C (T (T (T (C h10 h5) (S h12)) (h z v1 v0)) (C h11 h4)) h9) h8)) (S (h v3 z x))) (R v0)) h5) (S (h v0 v0 z))) h5)) (R y))) (h v13 z x)) (C (C (T (T (T (C h10 (R v13)) (S (h z v1 v2))) h12) (C h11 h5)) h9) h8)) (S h7)) h6) h5)) h4)) (S (h v2 v1 v0))

@[equational_result]
theorem Equation2958_implies_Equation1152 (G: Type _) [Magma G] (h: Equation2958 G) : Equation1152 G := fun x y z =>
  let v0 := M x y
  let v1 := M (M z v0) z
  let v2 := M y v1
  have h3 := R x
  let v4 := M v2 x
  have h5 := S (h v2 x v2)
  let v6 := M (M x (M x v2)) v2
  let v7 := M v1 x
  have h8 := S (h v1 x v1)
  let v9 := M (M x (M x v1)) v1
  have h10 := S (h z x z)
  let v11 := M (M x (M x z)) z
  have h12 := R y
  have h13 := S (h x x x)
  let v14 := M (M x (M x x)) x
  T (T (h x y x) (C (T (T (C (C h12 (T (C (T (T (T (h y v14 x) (C (T (T (C (T (C (R v14) h13) h13) h12) (h v0 v11 z)) (C (C (T (C (R v11) h10) h10) (R v0)) (R z))) h3)) (h v7 v9 v1)) (C (C (T (C (R v9) h8) h8) (R v7)) (R v1))) h3) (S (h v1 v1 x)))) h3) (h v4 v6 v2)) (C (C (T (C (R v6) h5) h5) (R v4)) (R v2))) h3)) (S (h v2 v2 x))

@[equational_result]
theorem Equation2958_implies_Equation2279 (G: Type _) [Magma G] (h: Equation2958 G) : Equation2279 G := fun x y z =>
  let v0 := M z y
  have h1 := R v0
  have h2 := R z
  let v3 := M z v0
  have h4 := S (h z x z)
  let v5 := M (M x (M x z)) z
  have h6 := T (C (R v5) h4) h4
  have h7 := R y
  have h8 := S (h v0 x v0)
  let v9 := M (M x (M x v0)) v0
  let v10 := M y v0
  let v11 := M x v10
  have h12 := R v11
  let v13 := M (M x (M x x)) x
  have h14 := h x x x
  T (T (h x x v10) (C (T (C (C (T h14 (C (R v13) h14)) h12) (R x)) (S (h v11 v13 x))) (R v10))) (C h12 (T (T (C (T (h y v9 v0) (C (T (T (C (T (C (R v9) h8) h8) h7) (C (T (h v0 v5 z) (C (C h6 h1) h2)) h7)) (S (h z z y))) h1)) h1) (C (T (h v3 v5 z) (C (C h6 (R v3)) h2)) h1)) (S (h z z v0))))

@[equational_result]
theorem Equation3404_implies_Equation3591 (G: Type _) [Magma G] (h: Equation3404 G) : Equation3591 G := fun x y z =>
  let v0 := M x z
  let v1 := M v0 y
  have h2 := S (h v1 v0 z)
  have h3 := S (h y z x)
  have h4 := R z
  let v5 := M x y
  have h6 := h v5 x z
  have h7 := R y
  have h8 := R v0
  have h9 := R x
  let v10 := M z v1
  T (T (T (h x y x) (C h9 (C h7 (T (T (h x x v1) (C (R v1) (T (T (T (C h9 (h v1 x z)) (S (h v10 z x))) (h v10 z v0)) (C h8 h2)))) (S (h v0 v0 v1)))))) (C h9 (T (T (T (T (C h7 (T (T (T (T (T (T (h v0 v0 y) (C h7 (T (T (T (C h8 (h y v0 x)) (S (h v5 x v0))) h6) (C h4 h3)))) (S (h z z y))) (h z z z)) (C h4 (T (T (T (C h4 (h z z x)) (S (h v0 x z))) (h v0 x y)) (C h7 (S (h z y x)))))) (S (h y y z))) (h y y x))) (S (h v5 x y))) h6) (C h4 (T h3 (h y z v0)))) h2))) (S (h z v1 x))

@[equational_result]
theorem Equation489_implies_Equation1152 (G: Type _) [Magma G] (h: Equation489 G) : Equation1152 G := fun x y z =>
  let v0 := M x y
  let v1 := M z v0
  let v2 := M v1 z
  let v3 := M y v2
  have h4 := R z
  have h5 := R v3
  have h6 := R v1
  have h7 := R v0
  have h8 := R y
  have h9 := R v2
  T (T (h x y v0) (C h8 (S (h v0 x y)))) (C h8 (T (h v0 v1 v0) (C h6 (T (C h7 (T (T (C h7 (C h6 (T (h v0 v2 v1) (C h9 (C h7 (T (C h6 (C h9 (T (h v1 v3 z) (C h5 (C h6 (T (C h4 (C h5 (T (h z y v0) (C h8 (C h4 (T (C h7 (C h8 (T (h v0 z v1) (C h4 (C h7 (T (C h6 (C h4 (T (h v1 y y) (C h8 (C h6 (T (C h8 (C h8 (T (h y v3 v0) (C h5 (C h8 (T (C h7 (C h5 (T (h v0 v3 v1) (C h5 (C h7 (T (C h6 (C h5 (T (h v1 z v2) (C h4 (S (h v2 v1 z)))))) (S (h v3 v1 z)))))))) (S (h v3 v0 v3)))))))) (S (h y y v3)))))))) (S (h z v1 y)))))))) (S (h y v0 z)))))))) (S (h v3 z y)))))))) (S (h v2 v1 v3)))))))) (S (h v1 v0 v2))) (h v1 z v0))) (S (h z v0 v1))))))

@[equational_result]
theorem Equation492_implies_Equation3370 (G: Type _) [Magma G] (h: Equation492 G) : Equation3370 G := fun x y z =>
  let v0 := M z x
  let v1 := M z v0
  let v2 := M y v1
  have h3 := S (h x x z)
  have h4 := C (R z) h3
  have h5 := R v1
  have h6 := h z v1 x
  have h7 := R v0
  have h8 := R v2
  have h9 := R y
  let v10 := M x y
  have h11 := R v10
  T (T (h v10 v1 x) (C h5 (T (T (T (T (C h11 h3) (C h11 (h x y x))) (S (h y v10 x))) (h y v2 v2)) (C h8 (C h9 (T (C h8 (C h8 (C h9 (T (h v1 y v2) (C h9 (T (C h5 (C h8 (T (T (T (C h8 (h y v1 y)) (S (h v1 v2 y))) (h v1 x z)) (C (T (T (T (h x v0 z) (C h7 (S (h z x z)))) (C h7 (T h6 (C h5 (T (T h4 (h v0 v1 z)) (C h5 (T (T (S (h z v0 z)) h6) (C h5 h4)))))))) (S (h v1 v0 v1))) (R (M v1 v1)))))) (S (h v2 v1 v1)))))))) (S (h v2 v2 y)))))))) (S (h v2 v1 y))

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
theorem Equation684_implies_Equation2199 (G: Type _) [Magma G] (h: Equation684 G) : Equation2199 G := fun x y z =>
  let v0 := M y x
  let v1 := M (M y z) z
  let v2 := M v1 v0
  let v3 := M v2 (M (M v2 x) x)
  have h4 := h v2 v2 x
  have h5 := R v1
  let v6 := M v0 (M (M v0 x) x)
  have h7 := h v0 v0 x
  have h8 := T h7 (C h7 (R v6))
  have h9 := R v2
  have h10 := R v0
  let v11 := M v2 v0
  have h12 := R y
  let v13 := M x (M (M x x) x)
  have h14 := h x x x
  T (T (T (h x y x) (C h12 (T (C (R x) (C h10 (T h14 (C h14 (R v13))))) (S (h v0 x v13))))) (C h12 (T (T (h v0 v2 v0) (C h9 (T (C h10 (C (R v11) h8)) (S (h v11 v0 v6))))) (C h9 (T (C h9 (T (T (h v0 v1 v0) (C h5 (T (C h10 (C h9 h8)) (S (h v2 v0 v6))))) (C h5 (T h4 (C h4 (R v3)))))) (S (h v1 v2 v3))))))) (S (h v2 y z))

@[equational_result]
theorem Equation2196_implies_Equation1983 (G: Type _) [Magma G] (h: Equation2196 G) : Equation1983 G := fun x y z =>
  let v0 := M z y
  let v1 := M z x
  let v2 := M y v0
  let v3 := M v2 v1
  have h4 := S (h v2 v1 v3)
  let v5 := M v1 v3
  let v6 := M (M v3 v0) v0
  let v7 := M v0 v2
  have h8 := R v6
  let v9 := M v5 v3
  have h10 := h z x v3
  let v11 := M (M x v3) v3
  let v12 := M v1 x
  let v13 := M x z
  have h14 := R v12
  T (T (T (T (h x z x) (C h14 (T (T (T (T (T (h v13 z x) (C h14 (T (T (T (T (h (M v13 z) v1 x) (C (R (M v12 x)) (T (S (h z x z)) h10))) (S (h v11 v1 x))) (h v11 v1 v3)) (C (R v9) (S h10))))) (S (h v9 z x))) (h v9 v3 v0)) (C h8 h4)) (C h8 (T (C (h y v0 v2) (T (h v0 v2 v0) (C (S (h z y v0)) (R v7)))) (S (h z v7 v2))))))) (S (h v6 z x))) (h v6 v5 v3)) (C h4 (S (h v1 v3 v0)))

@[equational_result]
theorem Equation2880_implies_Equation2068 (G: Type _) [Magma G] (h: Equation2880 G) : Equation2068 G := fun x y z =>
  let v0 := M z z
  let v1 := M x y
  let v2 := M v1 y
  let v3 := M v2 v0
  have h4 := R v3
  have h5 := R v0
  have h6 := h v2 x v0
  let v7 := M (M v2 (M x x)) v0
  have h8 := R x
  have h9 := R y
  have h10 := h x v3 v0
  let v11 := M (M x (M v3 v3)) v0
  let v12 := M x (M y y)
  T (T (h x y v3) (C (C (T (T (T (T (T (T (h v12 z x) (C (C (T (T (T (T (T (h (M v12 v0) z x) (C (T (C (S (h x y v0)) h8) (C h10 h8)) h8)) (S (h v11 z x))) (h v11 z y)) (C (C (S h10) h9) h9)) h6) h8) h8)) (S (h v7 z x))) (h v7 z v0)) (C (T (C (T (S h6) (h v2 z v0)) h5) (S (h v3 z v0))) h5)) (C (h v3 v1 v0) h5)) (S (h (M v3 (M v1 v1)) z v0))) h4) h4)) (S (h v3 v1 v3))

@[equational_result]
theorem Equation3791_implies_Equation3940 (G: Type _) [Magma G] (h: Equation3791 G) : Equation3940 G := fun x y z =>
  let v0 := M z y
  let v1 := M x v0
  have h2 := h v1 z y
  have h3 := S h2
  have h4 := R v0
  have h5 := h y v1 z
  have h6 := C (S h5) h4
  let v7 := M v1 z
  let v8 := M v0 v7
  let v9 := M v0 v0
  have h10 := R v7
  have h11 := C h5 h4
  T (T (T (T (T (h x y v7) (h (M v7 x) (M y v7) v7)) (C (T (C h10 (h v7 x v0)) (S (h z v8 v1))) (T (T (T (T (T (T (C (h y v7 z) (T h2 h11)) (S (h (M v7 z) v8 v0))) (S (h z v0 v7))) (h z v0 v1)) (C (T (T (T h2 h11) (h v8 v0 v0)) (C (T (T (T (C (T (h z y v1) (C h10 h5)) (R v8)) (S (h v8 v0 v7))) h6) h3) (R v9))) (h v0 v1 z))) (S (h v9 (M z v0) v7))) (S (h v0 z v0))))) (S (h v8 v0 z))) h6) h3

@[equational_result]
theorem Equation1507_implies_Equation2186 (G: Type _) [Magma G] (h: Equation1507 G) : Equation2186 G := fun x y z =>
  let v0 := M z x
  let v1 := M y z
  let v2 := M v1 y
  have h3 := h z y v1
  let v4 := M v2 v1
  let v5 := M z v0
  let v6 := M v0 (M v0 z)
  let v7 := M z v5
  have h8 := h x z v0
  let v9 := M v2 v0
  let v10 := M v9 (M v9 v0)
  let v11 := M v0 v9
  have h12 := h v0 v2 v1
  have h13 := R v9
  T (T (T h8 (C (T (T (T (T (T (T h12 (C h13 (S h3))) (C (h v9 v0 v9) (T (h z v9 v0) (C (T (C h13 h3) (S h12)) (R (M v0 v11)))))) (S (h v10 v11 v0))) (h v10 x v1)) (C (T (T (T (C h8 (R v10)) (S (h v6 v0 v9))) (h v6 v0 z)) (C (S h8) (R v7))) (R (M v1 (M v1 x))))) (S (h v7 x v1))) (R v6))) (S (h v5 z v0))) (C (T (h z v4 v2) (C (T (C (R v4) h3) (S (h v1 v2 v1))) (S (h y v1 v2)))) (R v0))

@[equational_result]
theorem Equation1993_implies_Equation1710 (G: Type _) [Magma G] (h: Equation1993 G) : Equation1710 G := fun x y z =>
  let v0 := M z z
  let v1 := M v0 y
  let v2 := M y x
  let v3 := M v2 v1
  let v4 := M v3 v0
  let v5 := M v1 v0
  have h6 := h v0 y v1
  let v7 := M v1 v1
  let v8 := M y v7
  let v9 := M x x
  have h10 := R (M v2 v9)
  have h11 := h y x v3
  have h12 := h (M x (M v3 v3)) v2 x
  have h13 := R (M v0 v7)
  T (T (T (h x v0 v1) (C h13 (T (T (h (M x v0) v2 x) (C h10 (T (S (h y x z)) h11))) (S h12)))) (C h13 (T (T (T h12 (C h10 (S h11))) (C h10 (T (T (T (T (h y v0 v0) (C (R (M v0 (M v0 v0))) (T (T (T (T (h (M y v0) v1 x) (C (R (M v1 v9)) (T (S (h v0 y z)) h6))) (S (h v8 v1 x))) (h v8 v1 z)) (C (R v5) (S h6))))) (S (h v5 v0 v0))) (h v5 v3 z)) (C (R v4) (S (h v2 v1 z)))))) (S (h v4 v2 x))))) (S (h v3 v0 v1))

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
theorem Equation2105_implies_Equation1740 (G: Type _) [Magma G] (h: Equation2105 G) : Equation1740 G := fun x y z =>
  let v0 := M (M z x) z
  let v1 := M y y
  let v2 := M v1 v0
  let v3 := M v0 v0
  have h4 := R v3
  have h5 := R v1
  have h6 := R v2
  have h7 := S (h v1 y x)
  have h8 := R (M x x)
  have h9 := R y
  have h10 := h y y y
  have h11 := C (S h10) h5
  have h12 := h y v1 y
  let v13 := M v2 v2
  have h14 := C (T (T (h v3 y x) (C (C (T (T (T (C h10 h4) (S (h y v1 v0))) h12) h11) h9) h8)) h7) (R v0)
  T (T (T (T (T (h x z z) (C (T (h v0 v0 y) (C h14 h5)) (R (M z z)))) (S (h v0 v1 z))) (h v0 v0 v0)) (C (T (h (M v3 v0) v2 y) (C (C (T (T (T (C h6 h14) (h v13 y x)) (C (C (T (T (T (C h10 (R v13)) (S (h y v1 v2))) h12) h11) h9) h8)) h7) h6) h5)) h4)) (S (h v2 v1 v0))

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
theorem Equation2958_implies_Equation2373 (G: Type _) [Magma G] (h: Equation2958 G) : Equation2373 G := fun x y z =>
  let v0 := M x z
  let v1 := M z v0
  let v2 := M (M y v1) y
  have h3 := R z
  let v4 := M v2 z
  have h5 := S (h v2 x v2)
  let v6 := M (M x (M x v2)) v2
  have h7 := S (h y x y)
  let v8 := M (M x (M x y)) y
  have h9 := R v0
  have h10 := S (h z z z)
  let v11 := M (M z (M z z)) z
  let v12 := M (M x (M x x)) x
  have h13 := h x x x
  T (T (h x x z) (C (T (T (T (T (T (C (C (T h13 (C (R v12) h13)) h9) (R x)) (S (h v0 v12 x))) (h v0 v11 z)) (C (T (T (C (T (C (R v11) h10) h10) h9) (h v1 v8 y)) (C (C (T (C (R v8) h7) h7) (R v1)) (R y))) h3)) (h v4 v6 v2)) (C (C (T (C (R v6) h5) h5) (R v4)) (R v2))) h3)) (S (h v2 v2 z))

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
theorem Equation3804_implies_Equation3737 (G: Type _) [Magma G] (h: Equation3804 G) : Equation3737 G := fun x y z =>
  let v0 := M y z
  let v1 := M x z
  let v2 := M v1 v0
  let v3 := M v0 v0
  have h4 := h x z y
  have h5 := S h4
  let v6 := M x y
  have h7 := h v0 v6 (M y y)
  have h8 := h y z y
  have h9 := h x y y
  have h10 := T (T (C h9 h8) (S h7)) h5
  let v11 := M x x
  let v12 := M z z
  let v13 := M v0 v11
  T (T (T (T (T (T (h x y x) (h v6 v11 v0)) (C (R v13) h10)) (h v13 v1 v2)) (C (T (T (T (C (R v2) (h x z z)) (S (h v12 v0 v1))) (h v12 v0 v6)) (C h10 (T (h v12 v6 v0) (C h5 (S (h y z z)))))) (T (T (T (T (T (T (S (h v1 v11 v0)) (S (h x z x))) h4) h7) (C (S h9) (S h8))) (h v6 v0 v0)) (C (R v3) h10)))) (S (h v3 v2 v1))) (S (h v1 v0 v0))

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
theorem Equation1507_implies_Equation522 (G: Type _) [Magma G] (h: Equation1507 G) : Equation522 G := fun x y z =>
  let v0 := M x z
  let v1 := M z v0
  let v2 := M y (M y v1)
  let v3 := M x v0
  have h4 := R (M x v3)
  have h5 := h v0 z z
  let v6 := M z (M z z)
  let v7 := M z v1
  let v8 := M z v7
  have h9 := h z x v2
  let v10 := M v2 (M v2 x)
  let v11 := M z x
  T (T (T (T (T (T (h x z v2) (C (T (T (h v11 z x) (C (T (T (T (T (h (M z v11) v0 x) (C (T (S (h z x z)) h9) h4)) (S (h v10 v0 x))) (h v10 v0 z)) (C (S h9) (R v7))) (R v3))) (S (h v7 z x))) (R (M v2 (M v2 z))))) (S (h v1 z v2))) (C (R z) (T (C (h x v0 z) (h z x v0)) (S (h v7 (M v0 x) v0))))) (h v8 v0 x)) (C (T (T (T (C h5 (R v8)) (S (h v6 v1 z))) (h v6 v1 y)) (C (S h5) (R v2))) h4)) (S (h v2 v0 x))

@[equational_result]
theorem Equation1507_implies_Equation1670 (G: Type _) [Magma G] (h: Equation1507 G) : Equation1670 G := fun x y z =>
  let v0 := M z y
  let v1 := M v0 z
  let v2 := M x y
  let v3 := M v2 v1
  let v4 := M v1 (M v1 v3)
  let v5 := M v1 (M v1 v2)
  let v6 := M v1 y
  have h7 := S (h y z v0)
  have h8 := R v6
  have h9 := h y v1 v0
  have h10 := h y x v3
  let v11 := M v3 (M v3 x)
  let v12 := M v1 x
  T (T (T (T (h x v1 v3) (C (T (T (T (T (h v12 v1 v0) (C (T (T (T (T (h (M v1 v12) v2 x) (C (T (S (h y x v1)) h10) (R (M x (M x v2))))) (S (h v11 v2 x))) (h v11 v2 v1)) (C (S h10) (R v5))) (T (T h7 h9) (C h8 (T (T h7 h9) (C h8 h7)))))) (S (h v5 y v6))) (h v5 v3 v1)) (C (S (h v1 v2 v1)) (R v4))) (R (M v3 (M v3 v1))))) (S (h v4 v1 v3))) (h v4 (M v3 v2) v3)) (C (S (h v2 v3 v1)) (S (h v1 v2 v3)))

@[equational_result]
theorem Equation2196_implies_Equation1374 (G: Type _) [Magma G] (h: Equation2196 G) : Equation1374 G := fun x y z =>
  let v0 := M z y
  let v1 := M v0 z
  let v2 := M v1 x
  let v3 := M y v2
  have h4 := S (h y v2 v3)
  let v5 := M v2 v3
  let v6 := M (M v3 v0) v0
  let v7 := M v5 v3
  have h8 := h v1 x v3
  let v9 := M (M x v3) v3
  let v10 := M x y
  have h11 := h z y v2
  let v12 := M v3 v2
  T (T (T (T (h x y v0) (C (R (M (M y v0) v0)) (T (T (T (T (h v10 y y) (C (T (T (T (T (h (M (M y y) y) v0 x) (C (R (M (M v0 x) x)) (T (S (h z y y)) h11))) (S (h v12 v0 x))) (h v12 v0 z)) (C (R (M v1 z)) (S h11))) (T (T (T (T (h (M v10 y) v2 x) (C (R (M (M v2 x) x)) (T (S (h v1 x y)) h8))) (S (h v9 v2 x))) (h v9 v2 v3)) (C (R v7) (S h8))))) (S (h v7 v1 z))) (h v7 v3 v0)) (C (R v6) h4)))) (S (h v6 y v0))) (h v6 v5 v3)) (C h4 (S (h v2 v3 v0)))

@[equational_result]
theorem Equation2196_implies_Equation2573 (G: Type _) [Magma G] (h: Equation2196 G) : Equation2573 G := fun x y z =>
  let v0 := M z x
  let v1 := M v0 y
  let v2 := M y v1
  let v3 := M v2 z
  let v4 := M v3 z
  have h5 := h y v1 v3
  let v6 := M (M v1 v3) v3
  have h7 := R (M (M z y) y)
  let v8 := M (M v0 v0) v0
  have h9 := h z x v3
  let v10 := M (M x v3) v3
  let v11 := M v0 x
  let v12 := M x z
  T (T (T (h x z y) (C h7 (T (T (T (T (h v12 z x) (C (R v11) (T (T (T (T (h (M v12 z) v0 x) (C (R (M v11 x)) (T (S (h z x z)) h9))) (S (h v10 v0 x))) (h v10 v0 v0)) (C (R v8) (S h9))))) (S (h v8 z x))) (h v8 (M x v0) v0)) (C (S (h z x v0)) (S (h x v0 v0)))))) (C h7 (T (T (h v0 y x) (C (R (M (M y x) x)) (T (T (T (C (h v0 y v1) h5) (S (h v6 v2 v1))) (h v6 v2 z)) (C (R v4) (S h5))))) (S (h v4 y x))))) (S (h v3 z y))

@[equational_result]
theorem Equation2958_implies_Equation4458 (G: Type _) [Magma G] (h: Equation2958 G) : Equation4458 G := fun x y z =>
  let v0 := M y x
  let v1 := M z y
  let v2 := M v1 z
  have h3 := R v0
  let v4 := M v2 v0
  have h5 := S (h v2 x v2)
  let v6 := M (M x (M x v2)) v2
  have h7 := R y
  have h8 := S (h z x z)
  let v9 := M (M x (M x z)) z
  have h10 := R x
  have h11 := S (h y x y)
  let v12 := M (M x (M x y)) y
  have h13 := S (h v0 v1 v0)
  let v14 := M (M v1 (M v1 v0)) v0
  T (C (T (T (T (h x v14 v0) (C (T (T (T (T (C (T (C (R v14) h13) h13) h10) (C (T (h v0 v12 y) (C (C (T (C (R v12) h11) h11) h3) h7)) h10)) (S (h y y x))) (h y v9 z)) (C (C (T (C (R v9) h8) h8) h7) (R z))) h3)) (h v4 v6 v2)) (C (C (T (C (R v6) h5) h5) (R v4)) (R v2))) h3) (S (h v2 v2 v0))

@[equational_result]
theorem Equation3120_implies_Equation4421 (G: Type _) [Magma G] (h: Equation3120 G) : Equation4421 G := fun x y z =>
  let v0 := M z y
  let v1 := M v0 z
  have h2 := S (h v1 v1 v0)
  have h3 := R v0
  have h4 := h y z v1
  have h5 := C h4 h3
  have h6 := C (S (h y z v0)) h3
  have h7 := h z v0 v0
  have h8 := R y
  have h9 := R z
  have h10 := C (T (T (T (T (C (C (C (T (h v0 z z) (C (T (C (C (T (T (T (C (T (T h7 h6) h5) h3) h2) (h v1 v1 y)) (C (C (S h4) h8) h8)) h9) h9) (S (h y y z))) h9)) h8) h3) h3) (S (h z y v0))) h7) h6) h5) h3
  have h11 := h y v0 v0
  let v12 := M x y
  have h13 := R v12
  T (T (T (T (C (T (h x v12 v12) (C (T (T (S (h y x v12)) (h y z y)) (C (R (M v1 y)) (T (T h11 h10) h2))) h13)) h13) (S (h y v1 v12))) h11) h10) h2

@[equational_result]
theorem Equation3147_implies_Equation4098 (G: Type _) [Magma G] (h: Equation3147 G) : Equation4098 G := fun x y z =>
  have h0 := R z
  let v1 := M y y
  have h2 := S (h v1 v1 v1)
  have h3 := R v1
  have h4 := h v1 y v1
  let v5 := M v1 z
  let v6 := M v5 z
  have h7 := R v5
  have h8 := R v6
  have h9 := C h4 h3
  have h10 := C (T h9 h2) h3
  have h11 := R x
  let v12 := M x x
  T (T (T (C (T (h x v1 x) (C (T (T (S (h v1 y x)) (h v1 v12 v1)) (C (S (h v12 x v1)) h3)) h11)) h11) (S (h v1 x x))) (h v1 v5 z)) (C (C (T (C (T (T (C (T (T (T (h v5 v1 v5) (C (S (h v1 y v5)) h7)) (C (T h4 (C h10 h3)) h7)) (C (C (T (T (T h9 h2) (h v1 v1 v6)) (C (T (T (C h10 h8) (C (T (T h9 h2) (h v1 y v6)) h8)) (S (h v6 v1 v6))) h8)) h3) h7)) h7) (S (h v1 v6 v5))) h4) h3) h2) h0) h0)

@[equational_result]
theorem Equation4176_implies_Equation3323 (G: Type _) [Magma G] (h: Equation4176 G) : Equation3323 G := fun x y z =>
  let v0 := M z z
  let v1 := M y v0
  have h2 := R y
  have h3 := R v0
  have h4 := S (h y v0 z)
  let v5 := M v0 z
  have h6 := h z v5 y
  have h7 := S (h z v5 z)
  have h8 := R z
  have h9 := h z z z
  let v10 := M v0 v0
  have h11 := h y v0 v0
  have h12 := R x
  T (T (T (h x y v0) (C (C h11 h12) h3)) (S (h x (M v10 y) v0))) (C h12 (T (T (C (T (T (T (T (T (T (h v0 v0 z) (C (T (T (C (h v0 z z) h3) (S (h z v0 v0))) (h z v0 z)) h8)) h7) h6) (C (T h4 h11) h2)) (S (h v0 v10 y))) (C (T (T (T (T h9 (C (C h9 h8) h8)) h7) h6) (C h4 h2)) (T (h v0 v0 y) (C (T (C (h v0 y v0) h3) (S (h v0 v1 v0))) h2)))) h2) (S (h (M (M v0 v1) y) v1 y))) (S (h y v0 v1))))

@[equational_result]
theorem Equation4176_implies_Equation3388 (G: Type _) [Magma G] (h: Equation4176 G) : Equation3388 G := fun x y z =>
  let v0 := M x y
  let v1 := M z y
  let v2 := M x v1
  have h3 := R z
  let v4 := M z v2
  have h5 := R v4
  have h6 := R v2
  let v7 := M y v2
  have h8 := R v1
  have h9 := h v1 z v2
  have h10 := h v2 v4 v1
  have h11 := h x v1 z
  let v12 := M (M v1 z) x
  T (T (h x y v0) (C (T (T (T (C (T (h y v0 v1) (C (S (h v1 x y)) h8)) (R x)) (S (h v1 v1 x))) (h v1 v1 z)) (C (T (T (T (C h9 h8) (S h10)) (C (T (T h11 (h v12 z v2)) (C (T (T (T (T (T (h v4 v12 z) (C (C (S h11) h5) h3)) (C (T (h v2 v4 v2) (C (S (h v2 z v2)) h6)) h3)) (S (h v2 v2 z))) (h v2 v2 v4)) (C (T (C (T (T (T h10 (C (S h9) h8)) (C (T (C (h z y v2) h3) (S (h v2 v7 z))) h8)) (S (h v7 x v1))) h6) (S (h x y v2))) h5)) h6)) h5)) (S (h v2 v0 v4))) h3)) (R v0))) (S (h z v2 v0))

@[equational_result]
theorem Equation4176_implies_Equation4362 (G: Type _) [Magma G] (h: Equation4176 G) : Equation4362 G := fun x y z =>
  let v0 := M y z
  let v1 := M x v0
  let v2 := M x z
  have h3 := R v1
  have h4 := R y
  have h5 := R v0
  have h6 := R x
  let v7 := M z x
  let v8 := M v2 x
  have h9 := R v2
  have h10 := C (S (h v2 x v0)) h9
  have h11 := h v0 v1 v2
  T (T (h x v0 v1) (C (T (T (T (C (T h11 h10) h6) (S (h v2 v2 x))) (h v2 v2 y)) (C (T (T (T (C (h v2 y z) h9) (S (h z v0 v2))) (h z v0 v1)) (C (T (T (T (T (C (T (T (T (T h11 h10) (C (h v2 x z) h9)) (S (h z v2 v2))) (h z v2 x)) (R z)) (S (h x v8 z))) (h x v8 v0)) (C (C (T (T (C (T (T (T (C (h x z x) h6) (S (h x v7 x))) (h x v7 y)) (C (S (h y z x)) h4)) h5) (C (h v0 y z) h5)) (S (h z v0 v0))) h6) h5)) (S (h x z v0))) h3)) h4)) h3)) (S (h y v2 v1))

@[equational_result]
theorem Equation627_implies_Equation100 (G: Type _) [Magma G] (h: Equation627 G) : Equation100 G := fun x y =>
  let v0 := M x x
  let v1 := M v0 y
  have h2 := R v1
  have h3 := h x x v0
  let v4 := M v0 x
  let v5 := M y v4
  have h6 := h v0 y v5
  have h7 := S h6
  have h8 := R v5
  have h9 := h y x x
  have h10 := R v0
  have h11 := C h10 (C h10 (T h9 (C h9 h8)))
  have h12 := h x x x
  have h13 := S h12
  let v14 := M x v4
  have h15 := R v14
  have h16 := R x
  have h17 := h x x v14
  have h18 := h x v0 v1
  have h19 := S h9
  have h20 := C h10 (C h10 (T (C h19 h8) h19))
  T (T (T (T h3 (C h16 (T (C h16 (C (T (C h16 (C h16 (T h12 (C h12 h15)))) (S h17)) (T (T h6 h20) (C (T h6 h20) h2)))) (S h18)))) h6) h20) (C (T (C h16 (T h18 (C h16 (C (T h17 (C h16 (C h16 (T (C h13 h15) h13)))) (T (T (C (T h11 h7) h2) h11) h7))))) (S h3)) h2)

@[equational_result]
theorem Equation684_implies_Equation4182 (G: Type _) [Magma G] (h: Equation684 G) : Equation4182 G := fun x y z =>
  let v0 := M y z
  let v1 := M x (M (M x v0) v0)
  let v2 := M v0 z
  let v3 := M v2 x
  have h4 := h x x v0
  have h5 := R v3
  have h6 := S (h x x x)
  let v7 := M x (M (M x x) x)
  have h8 := R x
  have h9 := S (h v3 v3 x)
  let v10 := M v3 x
  let v11 := M v3 (M v10 x)
  have h12 := R v2
  have h13 := S (h v2 v2 x)
  let v14 := M v2 v10
  let v15 := M v3 v2
  T (T (C h8 (T (T (h y v3 v2) (C h5 (T (T (S (h v15 y z)) (h v15 v2 v14)) (C h12 (C (R v15) (T (C h13 (R v14)) h13)))))) (S (h v2 v3 v2)))) (C h8 (T (T (h v2 v3 v11) (C h5 (T (C h12 (T (T (T (C h9 (R v11)) h9) (h v3 x v7)) (C h8 (C h5 (T (C h6 (R v7)) h6))))) (S (h x v2 x))))) (C h5 (T h4 (C h4 (R v1))))))) (S (h v3 x v1))

@[equational_result]
theorem Equation731_implies_Equation981 (G: Type _) [Magma G] (h: Equation731 G) : Equation981 G := fun x y z =>
  let v0 := M y x
  let v1 := M z z
  let v2 := M y (M v1 v0)
  let v3 := M (M y y) v2
  have h4 := h v2 v1 v1
  have h5 := R x
  let v6 := M v1 (M (M v1 v1) v2)
  have h7 := R y
  have h8 := h v0 v1 v2
  have h9 := h x v1 x
  let v10 := M (M x x) x
  have h11 := R v1
  have h12 := R v2
  T (T (h x v2 v2) (C h12 (C h12 (T (T (T (T (T (T (h (M (M v2 v2) x) v1 z) (C h11 (S (h x v1 v2)))) (C h11 h9)) (S (h v10 v1 z))) (h v10 x z)) (C h5 (C h5 (T (T (T (T (T (T (h (M v1 v10) y z) (C h7 (T (C h7 (S h9)) h8))) (C h7 (T (T (S h8) (h v0 y z)) (C h7 h4)))) (S (h v6 y z))) (h v6 x z)) (C h5 (C h5 (T (S h4) (h v2 v1 y))))) (S (h (M v1 v3) x z)))))) (S (h v3 x z)))))) (S (h v2 v2 y))

@[equational_result]
theorem Equation1090_implies_Equation3794 (G: Type _) [Magma G] (h: Equation1090 G) : Equation3794 G := fun x y z =>
  let v0 := M z x
  let v1 := M v0 (M z y)
  have h2 := R y
  let v3 := M v0 x
  let v4 := M (M x v3) x
  have h5 := h z v0 v4
  have h6 := R v4
  have h7 := h x v0 x
  have h8 := R z
  have h9 := R v0
  let v10 := M x y
  have h11 := S (h y v10 x)
  let v12 := M (M y (M v10 x)) x
  have h13 := R v10
  have h14 := S h7
  T (T (h v10 v0 y) (C h9 (C (T (T (T (T (T (C h13 (C (C (T h5 (C h9 (T (C (C h8 h14) h6) h14))) (T (h x v10 v12) (C h13 (T (C (C (R x) h11) (R v12)) h11)))) h2)) (S (h v3 v10 y))) (C h9 (T h7 (C (C h8 h7) h6)))) (S h5)) (h z v1 y)) (C (R v1) (C (S (h v0 z y)) h2))) h2))) (S (h v1 v0 y))

@[equational_result]
theorem Equation1507_implies_Equation1793 (G: Type _) [Magma G] (h: Equation1507 G) : Equation1793 G := fun x y z =>
  let v0 := M z y
  let v1 := M v0 x
  let v2 := M y z
  let v3 := M v2 v1
  let v4 := M v1 (M v1 v3)
  let v5 := M v2 (M v2 v2)
  have h6 := h z y y
  let v7 := M y (M y y)
  let v8 := M v1 v2
  let v9 := M v1 v8
  let v10 := M x (M x v0)
  T (T (T (T (T (T (h x v0 x) (C (R v1) (T (T (h v10 y x) (C (T (C (h y z y) (R v10)) (S (h (M y v2) v0 x))) (R (M x (M x y))))) (S (h v2 y x))))) (h v8 v1 x)) (C (T (T (T (T (h v9 z x) (C (T (T (T (C h6 (R v9)) (S (h v7 v2 v1))) (h v7 v2 v2)) (C (S h6) (R v5))) (R (M x (M x z))))) (S (h v5 z x))) (h v5 v3 v1)) (C (S (h v1 v2 v2)) (R v4))) (R (M x (M x v1))))) (S (h v4 v1 x))) (h v4 (M v3 v2) v3)) (C (S (h v2 v3 v1)) (S (h v1 v2 v3)))

@[equational_result]
theorem Equation2735_implies_Equation2 (G: Type _) [Magma G] (h: Equation2735 G) : Equation2 G := fun x y =>
  have h0 := R y
  let v1 := M y y
  let v2 := M v1 v1
  have h3 := h y y v2
  have h4 := h v2 y y
  have h5 := R (M v1 (M v2 v2))
  let v6 := M x x
  let v7 := M v6 v1
  have h8 := h y x v7
  have h9 := T (S h8) h3
  have h10 := R v1
  have h11 := h v7 y y
  have h12 := S h3
  have h13 := R v6
  let v14 := M v7 v7
  let v15 := M v6 v6
  have h16 := T h12 h8
  T (T (h x x y) (C (T (T (h v15 v1 y) (C (T (T (T (C (T (T (T (T h4 (C (T h5 (C h10 h16)) h0)) (S h11)) (C h13 (C h3 h3))) (C h13 (C h16 h16))) (S (h x x v15))) (S (h v14 x x))) (h v14 x y)) (C (T (T (T (T (C h13 (C h9 h9)) (C h13 (C h12 h12))) h11) (C (T (C h10 h9) h5) h0)) (S h4)) h3)) h0)) (S (h v2 v1 y))) h0)) (S (h y y y))

@[equational_result]
theorem Equation2956_implies_Equation1884 (G: Type _) [Magma G] (h: Equation2956 G) : Equation1884 G := fun x y =>
  let v0 := M x x
  have h1 := R v0
  have h2 := h y x x
  have h3 := S h2
  let v4 := M x v0
  let v5 := M v4 y
  have h6 := R v5
  have h7 := h v0 v5 y
  have h8 := R x
  let v9 := M y v0
  let v10 := M (M v0 (M v0 v9)) x
  have h11 := h x v0 v9
  let v12 := M v9 v0
  have h13 := S (h v12 v9 v0)
  have h14 := R v12
  have h15 := S (h v9 x x)
  let v16 := M v4 v9
  have h17 := C (T (h v12 v16 v9) (C (C (T (C (R v16) h15) h15) h14) h14)) h14
  T (T (T (h x v12 v12) (C (T (C (T (T (T (T (T (C h14 (T h17 h13)) h17) h13) (C (C (T h2 (C h6 h2)) h1) h1)) (S h7)) (C (T h11 (C (R v10) h11)) h8)) h8) (S (h x v10 x))) h8)) h7) (C (C (T (C h6 h3) h3) h1) h1)

@[equational_result]
theorem Equation2958_implies_Equation2199 (G: Type _) [Magma G] (h: Equation2958 G) : Equation2199 G := fun x y z =>
  let v0 := M y x
  let v1 := M y z
  let v2 := M v1 z
  let v3 := M v2 v0
  have h4 := R y
  have h5 := R v3
  let v6 := M v3 y
  have h7 := S (h v3 x v3)
  let v8 := M (M x (M x v3)) v3
  have h9 := S (h y x y)
  let v10 := M (M x (M x y)) y
  have h11 := S (h v2 x v2)
  let v12 := M (M x (M x v2)) v2
  have h13 := S (h y v0 y)
  let v14 := M (M v0 (M v0 y)) y
  T (T (h x v14 y) (C (T (T (T (T (T (C (T (C (R v14) h13) h13) (R x)) (h v0 v12 v2)) (C (C (T (C (R v12) h11) h11) (R v0)) (R v2))) (C h5 (T (C (T (h v1 v10 y) (C (C (T (C (R v10) h9) h9) (R v1)) h4)) (R z)) (S (h y y z))))) (h v6 v8 v3)) (C (C (T (C (R v8) h7) h7) (R v6)) h5)) h4)) (S (h v3 v3 y))

@[equational_result]
theorem Equation492_implies_Equation1507 (G: Type _) [Magma G] (h: Equation492 G) : Equation1507 G := fun x y z =>
  let v0 := M z y
  have h1 := h v0 y z
  have h2 := h v0 v0 z
  let v3 := M z v0
  have h4 := h v3 v0 v3
  have h5 := h y y z
  have h6 := R z
  have h7 := R v3
  have h8 := h z v3 y
  have h9 := R v0
  have h10 := h v0 z v3
  have h11 := h z v0 v0
  have h12 := S h10
  have h13 := C h6 (T h4 (C h9 (C h7 (C h7 (T (C h7 (C h6 h5)) (S h8))))))
  have h14 := R y
  let v15 := M y x
  T (h x v15 y) (C (R v15) (T (T (S (h y x y)) (h y z z)) (C h6 (T (C h14 (T (T (T (C h6 (C h6 (T (h z y z) (C h14 (T (T (T h13 h12) h1) (C h14 (T (C h9 (C h6 (T h2 (C h9 (C h9 (T h13 h12)))))) (S h11)))))))) (S (h z z y))) h11) (C h9 (C h6 (T (C h9 (C h9 (T h10 (C h6 (T (C h9 (C h7 (C h7 (T h8 (C h7 (C h6 (S h5))))))) (S h4)))))) (S h2)))))) (S h1)))))

@[equational_result]
theorem Equation492_implies_Equation3120 (G: Type _) [Magma G] (h: Equation492 G) : Equation3120 G := fun x y z =>
  let v0 := M y x
  let v1 := M v0 y
  let v2 := M v1 z
  let v3 := M v2 z
  have h4 := h z v2 v1
  have h5 := S h4
  have h6 := h v1 z v1
  have h7 := C (R v0) (S (h y x y))
  have h8 := h x v0 y
  have h9 := R v2
  have h10 := R v1
  have h11 := R v3
  have h12 := T (h v3 v3 v1) (C h11 (C h11 (T (C h10 (C h10 (C h9 (T h4 (C h9 (S h6)))))) (S (h v1 v1 v2)))))
  have h13 := C h9 (T (T (T (T (C (T h8 h7) (C (R x) h12)) (S (h x v1 v3))) h8) h7) h6)
  have h14 := h v2 v3 x
  have h15 := R z
  T (T (T (T (T h8 h7) (h v1 z v2)) (C h15 (T (C h10 (C h9 h12)) (S (h v2 v1 v3))))) (C h15 (T h14 (C h11 (T (T (T (T h13 h5) (h z v3 v2)) (C h11 (S (h v2 z v2)))) (C h11 (T h14 (C h11 (T h13 h5))))))))) (S (h v3 z v3))

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
theorem Equation1165_implies_Equation4007 (G: Type _) [Magma G] (h: Equation1165 G) : Equation4007 G := fun x y z =>
  let v0 := M y x
  let v1 := M z v0
  let v2 := M v1 z
  have h3 := R x
  have h4 := h z v1 y
  have h5 := R y
  have h6 := h x y z
  have h7 := R v1
  have h8 := T (C h7 (C h6 h5)) (S h4)
  have h9 := h v0 x v2
  let v10 := M (M v2 (M x v0)) v2
  let v11 := M x y
  have h12 := R v11
  let v13 := M v11 v0
  T (T (T (T (h v11 v13 y) (C (R v13) (C (S (h x y v11)) h5))) (h (M v13 v11) x x)) (C h3 (C (C h3 (T (T (T (C h3 (C (C h12 h9) h12)) (S (h v10 x v11))) (h v10 x z)) (C h3 (T (C (T (C (R z) (T (S h9) (C (T (h y x v1) (C h3 (C h8 h7))) h3))) (S (h v1 z x))) (T h4 (C h7 (C (S h6) h5)))) (C h7 h8))))) h3))) (S (h v2 x x))

