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
theorem Equation2958_implies_Equation2349 (G: Type _) [Magma G] (h: Equation2958 G) : Equation2349 G := fun x y z =>
  let v0 := M z x
  let v1 := M y (M y v0)
  let v2 := M (M y (M y v1)) v1
  let v3 := M v1 z
  have h4 := R v1
  have h5 := R v3
  have h6 := h v1 y v1
  let v7 := M v1 v3
  have h8 := R z
  have h9 := S (h v1 x v1)
  let v10 := M (M x (M x v1)) v1
  T (T (T (T (h x v3 z) (C (T (T (C (T (C h5 (T (C (h v3 y v0) h8) (S (h v0 v1 z)))) (S (h z y v0))) (R x)) (h v0 v1 v3)) (C (S (h v7 y v0)) (T (h v3 v10 v1) (C (C (T (C (R v10) h9) h9) h5) h4)))) h8)) (S (h (M v7 v1) v1 z))) (C (C (T h6 (C (R v2) h6)) h5) h4)) (S (h v3 v2 v1))

@[equational_result]
theorem Equation4009_implies_Equation41 (G: Type _) [Magma G] (h: Equation4009 G) : Equation41 G := fun x y z =>
  let v0 := M x x
  let v1 := M z z
  let v2 := M x v1
  let v3 := M y z
  let v4 := M y y
  have h5 := R x
  have h6 := R z
  let v7 := M v0 v0
  let v8 := M x (M v1 v1)
  let v9 := M z v7
  T (T (T (T (T (T (T (h x x z) (C (T (T (T (h z v0 x) (C (C h5 (T (h v0 v0 z) (h v9 v0 z))) h6)) (S (h z v9 x))) (C h6 (T (T (h z v7 v8) (C (T (C (R v8) (T (S (h v7 x v0)) (S (h x x v0)))) (S (h v0 v1 x))) h6)) (S (h z z v0))))) h5)) (S (h x z z))) (h x z x)) (h v2 x (M v3 (M v4 v4)))) (C (S (h v0 v4 v3)) (R v2))) (S (h v2 y v0))) (S (h y z x))

@[equational_result]
theorem Equation4176_implies_Equation3537 (G: Type _) [Magma G] (h: Equation4176 G) : Equation3537 G := fun x y z =>
  let v0 := M z z
  let v1 := M v0 y
  have h2 := R z
  have h3 := R x
  have h4 := R v1
  have h5 := S (h y z z)
  let v6 := M x v1
  have h7 := S (h z z z)
  T (T (T (T (h x y v1) (h (M (M y v1) x) v1 z)) (C (C h5 (T (C (T (T (T (T (T (T (h y v1 z) (C (S (h z v0 y)) h2)) (C (T (h z v0 z) (C h7 h2)) h2)) h7) (h z z x)) (C (T (T (T (C (h z x v1) h2) (S (h v1 v6 z))) (h v1 v6 v1)) (C (S (h v1 x v1)) h4)) h3)) (S (h v1 v1 x))) h3) (C (T (T (h v1 v1 z) (C (C h5 h4) h2)) (S (h v1 y z))) h3))) h2)) (S (h (M (M v1 y) x) y z))) (S (h x v1 y))

@[equational_result]
theorem Equation2741_implies_Equation31 (G: Type _) [Magma G] (h: Equation2741 G) : Equation31 G := fun x y =>
  let v0 := M y y
  let v1 := M v0 x
  have h2 := h v1 x v1
  have h3 := R v1
  have h4 := R v0
  let v5 := M v0 v0
  have h6 := R v5
  have h7 := h v0 y v0
  have h8 := C (C h4 (S h7)) h4
  let v9 := M v0 v5
  have h10 := h v9 y v0
  have h11 := h x v0 v1
  T (T h11 (C (T (T (T (h (M v5 (M x v1)) y v1) (C (C h4 (S h11)) h3)) (C (T (T (C (T (T (T (T (T h7 (C (T (T h10 h8) (C h6 h7)) h4)) (S (h v9 v0 v0))) h10) h8) (C h6 (h v0 y x))) (R x)) (S (h (M v0 v1) v0 x))) (C h4 h2)) h3)) (S (h (M (M x x) (M v1 v1)) y v1))) h3)) (S h2)

@[equational_result]
theorem Equation2146_implies_Equation2132 (G: Type _) [Magma G] (h: Equation2146 G) : Equation2132 G := fun x y z =>
  let v0 := M y y
  let v1 := M v0 x
  let v2 := M z z
  let v3 := M v2 v0
  have h4 := h y v0 y
  let v5 := M v0 v0
  let v6 := M v5 y
  let v7 := M x x
  have h8 := R (M v7 y)
  have h9 := h v5 x y
  have h10 := R v1
  let v11 := M v7 v0
  have h12 := R v11
  T (T (h x y x) (C h10 (T (T (h v7 x v0) (C h12 (T (T (h v11 x y) (C h8 (T (C h12 h4) (S (h v6 x v0))))) (S h9)))) (S (h v0 x v0))))) (C h10 (T (T (h v0 v1 v0) (C (R (M (M v1 v1) v0)) (T (T h9 (C h8 (T (h v6 z v0) (C (R v3) (S h4))))) (S (h v3 x y))))) (S (h v2 v1 v0))))

@[equational_result]
theorem Equation2196_implies_Equation2279 (G: Type _) [Magma G] (h: Equation2196 G) : Equation2279 G := fun x y z =>
  let v0 := M z y
  let v1 := M y v0
  let v2 := M v0 v1
  have h3 := h z y v0
  have h4 := S h3
  let v5 := M x v1
  have h6 := R v5
  let v7 := M (M x y) y
  let v8 := M v5 x
  have h9 := h v5 x y
  have h10 := h x v1 v0
  T (T (T (T (T (T (T h10 (C h4 h6)) (C (T (h z v5 x) (C (R (M v8 x)) (T (C h3 h6) (S h10)))) h9)) (S (h v7 v8 x))) (h v7 v8 v7)) (C (R (M (M v8 v7) v7)) (T (S h9) (h v5 x v1)))) (S (h (M v5 v1) v8 v7))) (C h6 (T (C (h y v0 v1) (T (h v0 v1 v0) (C h4 (R v2)))) (S (h z v2 v1))))

@[equational_result]
theorem Equation3193_implies_Equation3877 (G: Type _) [Magma G] (h: Equation3193 G) : Equation3877 G := fun x y =>
  let v0 := M x x
  let v1 := M y v0
  let v2 := M v1 x
  have h3 := R x
  have h4 := R v1
  have h5 := h v1 y v0
  have h6 := C (S h5) h4
  have h7 := h v1 v1 y
  have h8 := S (h y y v0)
  have h9 := R y
  have h10 := S h7
  have h11 := C h5 h4
  have h12 := C (C (T (T (C (T h11 h10) h4) h11) h10) h9) h9
  have h13 := h y v1 v1
  T (h v0 y y) (C (C (T (C (T (T (T (C (T h13 h12) h9) h8) h13) h12) h9) h8) (R v0)) (T (C (T (h x v2 x) (C (C (C (T (C (C (T (T h7 h6) (C (T h7 h6) h4)) h3) h3) (S (h x v1 v1))) (R v2)) h3) h3)) h3) (S (h x x v2))))

@[equational_result]
theorem Equation3404_implies_Equation3692 (G: Type _) [Magma G] (h: Equation3404 G) : Equation3692 G := fun x y z =>
  let v0 := M z z
  let v1 := M y y
  have h2 := h y y v0
  have h3 := R v0
  let v4 := M y (M v0 y)
  let v5 := M v1 v0
  have h6 := h z z z
  have h7 := R z
  T (T (T (T (T (T (T (h x x z) (C h7 (T (C (R x) (h z x z)) (S (h v0 z x))))) (C h7 (T (h v0 z y) (C (R y) (S (h z y z)))))) (S (h y y z))) h2) (h v0 v4 v0)) (C h3 (T (T (C (R v4) (T (C h3 (T (T (T h6 (h z (M z v0) v5)) (C (R v5) (C (T (C h7 h6) (S (h v0 z z))) (R (M v5 z))))) (S (h z (M v0 z) v5)))) (S (h z z v0)))) (h v4 v0 v0)) (C h3 (C h3 (S h2)))))) (S (h v1 v0 v0))

@[equational_result]
theorem Equation3791_implies_Equation3334 (G: Type _) [Magma G] (h: Equation3791 G) : Equation3334 G := fun x y z =>
  let v0 := M z y
  let v1 := M z v0
  let v2 := M x y
  let v3 := M v0 x
  let v4 := M y z
  let v5 := M z z
  let v6 := M v0 y
  have h7 := h z z y
  T (T (T (T (h x y v0) (h v3 (M y v0) v2)) (C (R (M v2 v3)) (T (T (T (T (T (S (h v0 x y)) (h v0 x z)) (C (T (T (T (h z v0 z) (h v5 (M v0 z) v1)) (C (S (h v0 z z)) (T (S (h z z v0)) h7))) (S (h z v4 v0))) (R (M x z)))) (S (h v4 x z))) (h v4 x y)) (C (T (T (T (h y v4 v0) (C (R v6) (S h7))) (h v6 v5 v4)) (C (S (h z v0 y)) (S (h z y z)))) (R v2))))) (S (h v3 (M v1 v0) v2))) (S (h x v1 v0))

@[equational_result]
theorem Equation3973_implies_Equation4307 (G: Type _) [Magma G] (h: Equation3973 G) : Equation4307 G := fun x y z =>
  let v0 := M x y
  let v1 := M z y
  have h2 := h z v1 v0
  let v3 := M v1 (M v0 z)
  have h4 := R y
  let v5 := M z v1
  let v6 := M v0 (M v5 x)
  have h7 := R v1
  let v8 := M x v0
  let v9 := M y (M v8 z)
  let v10 := M v0 (M v1 x)
  have h11 := h x v0 v1
  T (T (T (T (T (T (T (T h11 (h v10 v1 v1)) (C (C h7 (T (C (T (h z y v8) (C (R v9) h11)) (R v10)) (S (h v1 v9 v10)))) h7)) (S (h v9 v1 v1))) (C (C h4 (T (C (h x v0 v5) (R z)) (S (h v1 v6 z)))) h7)) (S (h v6 y v1))) (C (C (R v0) (T (C h2 (R x)) (S (h y v3 x)))) h4)) (S (h v3 v0 y))) (S h2)

@[equational_result]
theorem Equation4197_implies_Equation3729 (G: Type _) [Magma G] (h: Equation4197 G) : Equation3729 G := fun x y z =>
  let v0 := M z z
  let v1 := M x y
  let v2 := M v1 v0
  have h3 := R v2
  have h4 := R v0
  have h5 := h x y v0
  have h6 := h (M (M v0 x) y) v0 v2
  have h7 := R y
  have h8 := h v0 x v1
  have h9 := R v1
  have h10 := h y v0 x
  have h11 := h v0 v1 y
  T (T (T h5 h6) (C (C (C h3 (T (T (T (T (T (T (T (C (T h8 (C (S h10) h9)) h7) (S h11)) (h v0 v1 v0)) (C (C (T (C (h z z z) h4) (S (h z z v0))) h9) h4)) (h (M v0 v1) v0 v2)) (C (C (C h3 (T h11 (C (T (C h10 h9) (S h8)) h7))) h4) h3)) (S h6)) (S h5))) h4) h3)) (S (h v1 v0 v2))

@[equational_result]
theorem Equation505_implies_Equation2 (G: Type _) [Magma G] (h: Equation505 G) : Equation2 G := fun x y =>
  let v0 := M y x
  let v1 := M x v0
  have h2 := h y y (M y v1)
  have h3 := S h2
  have h4 := h y y v1
  have h5 := R y
  let v6 := M x x
  have h7 := R v6
  have h8 := h x y x
  have h9 := C h5 (C h5 h8)
  have h10 := C h5 (C h5 (S h8))
  have h11 := R x
  T (T (T (T (h x x (M v0 v6)) (C h11 (C h11 (T (T (T (S (h v0 x x)) (C (T h4 h10) (T (h x x v6) (C h11 (S (h x x x)))))) (C (T (T (T h9 (S h4)) h2) (C h5 h10)) h7)) (C (T (T (T (C h5 h9) h3) (h y y v0)) (C h5 (S (h y y x)))) h7))))) (S (h (M y y) x x))) (C h5 h4)) h3

@[equational_result]
theorem Equation2319_implies_Equation11 (G: Type _) [Magma G] (h: Equation2319 G) : Equation11 G := fun x y =>
  let v0 := M y y
  let v1 := M x v0
  let v2 := M v1 v1
  have h3 := h x v2 y
  have h4 := R v2
  have h5 := h x v1 y
  let v6 := M x v2
  have h7 := C (S h5) h4
  have h8 := h v0 v0 v0
  have h9 := R x
  have h10 := h x v0 v1
  let v11 := M v0 v6
  have h12 := h x v0 v0
  T h12 (C (T (T (T (T (T (T (T (h (M v0 (M x (M v0 v0))) x y) (C (T (C h9 (S h12)) (C h9 h10)) h9)) (S (h v11 x y))) (h v11 v1 y)) (C (T (C (C h9 h8) (S h10)) (C (C h9 (S h8)) (T (T h3 h7) (C (T h3 h7) h4)))) (R v1))) (S (h v6 v1 v1))) (C h5 h4)) (S h3)) (R v0))

@[equational_result]
theorem Equation3120_implies_Equation4216 (G: Type _) [Magma G] (h: Equation3120 G) : Equation4216 G := fun x y z =>
  let v0 := M z y
  let v1 := M v0 z
  let v2 := M v1 x
  have h3 := h y z v2
  have h4 := R v2
  have h5 := R z
  have h6 := h v0 v1 v1
  have h7 := R v1
  have h8 := h z v0 v1
  have h9 := h v1 z v2
  have h10 := T (T h9 (C (C (C (T (C h8 h7) (S h6)) h5) h4) h4)) (S h3)
  have h11 := R x
  have h12 := C (T (h v1 v2 v2) (C (S (h x v1 v2)) h4)) h11
  T (T (C h11 (T (T h3 (C (C (C (T h6 (C (S h8) h7)) h5) h4) h4)) (S h9))) (C (T (T (h x v1 v1) (C (T (C (C h12 h7) h7) (S (h v2 x v1))) h10)) (C h12 (R y))) h10)) (S (h v2 x y))

@[equational_result]
theorem Equation2196_implies_Equation711 (G: Type _) [Magma G] (h: Equation2196 G) : Equation711 G := fun x y z =>
  let v0 := M x z
  let v1 := M v0 z
  let v2 := M y v1
  have h3 := R v2
  let v4 := M v1 x
  have h5 := R v4
  have h6 := h v1 x z
  let v7 := M (M v1 v2) v2
  have h8 := h v0 z v0
  have h9 := S h8
  let v10 := M (M z v0) v0
  have h11 := R (M (M v0 x) x)
  let v12 := M (M v1 v0) v0
  have h13 := S h6
  T (T (T (T (T (T (h x z v0) (C (T (h v10 v1 v4) (C (T (C h13 h5) h13) h9)) (R v0))) (h v12 v0 x)) (C h11 (T (C (R v12) h8) (S (h v10 v1 v0))))) (C h11 (T (h v10 v1 v2) (C (R v7) h9)))) (S (h v7 v0 x))) (C (T (C (T h6 (C h6 h5)) h3) (S (h y v1 v4))) h3)

@[equational_result]
theorem Equation3791_implies_Equation3364 (G: Type _) [Magma G] (h: Equation3791 G) : Equation3364 G := fun x y z =>
  let v0 := M x z
  let v1 := M z v0
  let v2 := M v0 x
  have h3 := h z v0 x
  have h4 := h x z v0
  let v5 := M y z
  have h6 := S h4
  have h7 := h v0 x z
  have h8 := R v1
  T (T (T (T (T (h x y z) (h (M z x) v5 (M x y))) (C (S (h y z x)) (T (T (T (T (T (T (S (h z x y)) (h z x z)) (C (T (T (h z z v0) (C (T (T (h v0 z v0) (C (R (M v0 v0)) (T (T h3 (h v0 v2 v1)) (C (S h7) h6)))) (S (h v0 v2 v0))) h8)) (C (S h3) h8)) h4)) (S (h v1 v2 v1))) (C h3 h7)) (S (h v2 v1 v0))) h6))) (h v5 v0 v1)) (C (S (h v0 y z)) (T (C h4 h3) (S (h v1 v0 v2))))) (S (h y v1 v0))

@[equational_result]
theorem Equation3804_implies_Equation3398 (G: Type _) [Magma G] (h: Equation3804 G) : Equation3398 G := fun x y z =>
  let v0 := M x z
  let v1 := M y v0
  let v2 := M x v1
  let v3 := M z v1
  let v4 := M x y
  let v5 := M y z
  let v6 := M v3 x
  T (T (T (h x y v3) (C (T (T (T (h v3 y x) (h v4 v6 v1)) (C (T (T (C (T (T (T (h y v0 z) (h (M z v0) v5 v0)) (C (R (M v0 v5)) (S (h x v0 z)))) (S (h x v5 v0))) (R v6)) (S (h v3 v5 x))) (S (h y v1 z))) (T (T (T (h v4 v1 x) (h v2 (M v4 x) v4)) (C (S (h v4 y x)) (R (M v2 v4)))) (S (h v2 y v4))))) (S (h v2 v1 y))) (h x v3 v1))) (C (R (M v2 v1)) (T (T (h (M v1 v3) v2 v3) (C (R (M v3 v2)) (S (h z v3 v1)))) (S (h z v2 v3))))) (S (h z v1 v2))

@[equational_result]
theorem Equation3804_implies_Equation3591 (G: Type _) [Magma G] (h: Equation3804 G) : Equation3591 G := fun x y z =>
  let v0 := M x z
  let v1 := M v0 y
  let v2 := M x y
  let v3 := M z y
  let v4 := M v2 v3
  have h5 := R v4
  let v6 := M x v1
  let v7 := M z v1
  T (T (T (T (T (T (T (h x y v1) (h (M v1 y) v6 v7)) (C (R (M v7 v6)) (S (h z y v1)))) (C (T (T (h v7 v6 v1) (C (R (M v1 v6)) (T (C (R v7) (T (T (T (h v0 y x) (h v2 (M v0 x) v0)) (C (S (h v0 z x)) (R (M v2 v0)))) (S (h v2 z v0)))) (S (h v2 v1 z))))) (S (h v2 v6 v1))) (T (T (h z y y) (h (M y y) v3 v2)) (C h5 (S (h x y y)))))) (S (h v4 v6 v2))) (C h5 (h x v1 y))) (S (h (M y v1) v3 v2))) (S (h z v1 y))

@[equational_result]
theorem Equation1507_implies_Equation3120 (G: Type _) [Magma G] (h: Equation1507 G) : Equation3120 G := fun x y z =>
  let v0 := M y x
  let v1 := M v0 y
  let v2 := M v1 z
  have h3 := h x y v0
  have h4 := R v2
  have h5 := h y v0 v2
  let v6 := M v2 (M v2 v0)
  let v7 := M x v1
  let v8 := M x v7
  let v9 := M v1 v0
  T (T (T (T (h x v9 v1) (C (T (C (R v9) h3) (S (h v0 v1 v0))) (S (h y v0 v1)))) (h v1 x v1)) (C (T (h v7 x v2) (C (T (T (h v8 y x) (C (T (T (T (C h5 (R v8)) (S (h v6 v1 x))) (h v6 v1 v0)) (C (S h5) (S h3))) (R (M x (M x y))))) (S (h x y x))) (C h4 (T (C h4 h3) (S (h z v1 v0)))))) (R (M v1 (M v1 x))))) (S (h (M v2 z) x v1))

@[equational_result]
theorem Equation1537_implies_Equation1902 (G: Type _) [Magma G] (h: Equation1537 G) : Equation1902 G := fun x y z =>
  let v0 := M z z
  let v1 := M x y
  let v2 := M y v1
  let v3 := M v2 v0
  have h4 := S (h v0 x v2)
  have h5 := h x z y
  have h6 := R v2
  have h7 := R (M x x)
  have h8 := R v3
  let v9 := M v2 v2
  have h10 := C h6 (T (T (h v9 x v2) (C h7 (C h6 (T (S (h x v2 y)) h5)))) h4)
  have h11 := R v0
  T (T (T (T (T h5 (C h11 (T (h v2 z v2) (C h11 h10)))) (S (h v2 z v0))) (h v2 v1 v2)) (C (R (M v1 v1)) (T (h (M v2 v9) z v3) (C h11 (C h8 (T (T (T (C h10 h8) (h (M v3 v3) x v2)) (C h7 (C h6 (T (S (h x v3 y)) h5)))) h4)))))) (S (h v3 v1 v0))

@[equational_result]
theorem Equation2315_implies_Equation2 (G: Type _) [Magma G] (h: Equation2315 G) : Equation2 G := fun x y =>
  let v0 := M x (M y x)
  let v1 := M x v0
  have h2 := R x
  have h3 := h x x y
  have h4 := R y
  have h5 := h v0 y x
  let v6 := M x x
  let v7 := M x (M y v6)
  let v8 := M y (M v0 (M x y))
  have h9 := h y x x
  let v10 := M x v6
  have h11 := h v10 y y
  let v12 := M y (M v10 (M y y))
  T (T (h x x v1) (C (T (T (T (T (T (C h2 (C h2 (S h3))) h11) (C (T (T (h v12 x v7) (C (C h2 (T (C (R v12) (S h9)) (S h11))) h2)) (S (h x x x))) h4)) (C (T (T h3 (C (C h2 (T h5 (C (R v8) h9))) h2)) (S (h v8 x v7))) h4)) (S h5)) (C h2 (C h4 h3))) h2)) (S (h y x v1))

@[equational_result]
theorem Equation2958_implies_Equation2573 (G: Type _) [Magma G] (h: Equation2958 G) : Equation2573 G := fun x y z =>
  let v0 := M z x
  let v1 := M v0 y
  have h2 := R v1
  let v3 := M (M x (M x v1)) v1
  have h4 := h v1 x v1
  let v5 := M (M x (M x v0)) v0
  have h6 := R v0
  have h7 := h v0 x v0
  have h8 := T h7 (C (R v5) h7)
  let v9 := M v0 v1
  have h10 := S (h z v1 z)
  let v11 := M (M v1 (M v1 z)) z
  T (h x v11 z) (C (T (T (C (T (C (R v11) h10) h10) (R x)) (h v0 v0 v1)) (C (T (T (T (C (C h8 (R v9)) h6) (S (h v9 v5 v0))) (C (T (h v0 v0 y) (C (T (T (T (C (C h8 h2) h6) (S (h v1 v5 v0))) h4) (C (R v3) h4)) (R y))) h2)) (S (h y v3 v1))) h2)) (R z))

@[equational_result]
theorem Equation2956_implies_Equation3877 (G: Type _) [Magma G] (h: Equation2956 G) : Equation3877 G := fun x y =>
  let v0 := M x x
  have h1 := R x
  have h2 := R v0
  let v3 := M (M x v0) x
  have h4 := h x x x
  have h5 := T h4 (C (R v3) h4)
  have h6 := C (T (C (C h5 h2) h2) (S (h v0 v3 x))) h2
  have h7 := h v0 x x
  have h8 := S (h x v3 x)
  have h9 := C (C h5 h1) h1
  let v10 := M y v0
  have h11 := S (h y v0 v10)
  let v12 := M (M v0 (M v0 v10)) y
  T (h v0 v12 y) (C (C (T (C (R v12) h11) h11) h2) (T (C (T (h x v0 x) (C (T (T (T (C (T (T (C h2 (T h9 h8)) h9) h8) h1) h7) h6) (C h2 (T h7 h6))) h1)) h1) (S (h x v0 v0))))

@[equational_result]
theorem Equation3404_implies_Equation4497 (G: Type _) [Magma G] (h: Equation3404 G) : Equation4497 G := fun x y z =>
  let v0 := M y y
  let v1 := M x v0
  let v2 := M z z
  let v3 := M v2 x
  have h4 := R v1
  have h5 := R x
  have h6 := R y
  have h7 := h y y y
  T (T (T (T (C h5 (T (T (T (T h7 (C h6 (T (C h6 h7) (S (h v0 y y))))) (C h6 (T (h v0 y x) (C h5 (S (h y x y)))))) (S (h x x y))) (h x x v2))) (S (h v3 v2 x))) (h v3 v2 v1)) (C h4 (T (C (R v2) (C (T (h x v0 v1) (C h4 (T (T (T (h v0 (M v1 x) v1) (C h4 (C (T (h v1 x z) (C (R z) (S (h v0 z x)))) (R (M v1 v0))))) (S (h v0 (M z (M v0 z)) v1))) (S (h z z v0))))) (R v3))) (S (h x (M v1 v2) v2))))) (S (h v2 x v1))

@[equational_result]
theorem Equation2741_implies_Equation4109 (G: Type _) [Magma G] (h: Equation2741 G) : Equation4109 G := fun x y z =>
  have h0 := R z
  let v1 := M y z
  let v2 := M v1 z
  let v3 := M x x
  have h4 := R v3
  let v5 := M v2 v2
  let v6 := M y y
  let v7 := M v3 v3
  have h8 := h v3 v2 v3
  T (T (T h8 (C (T (T (T (h (M v5 v7) x v3) (C (T (C h4 (S h8)) (C h4 (h v3 x v3))) h4)) (S (h (M v3 v7) x v3))) (C h4 (T (T (h v7 x x) (C (T (C h4 (S (h x x x))) (C h4 (h x y x))) (R x))) (S (h (M v6 v3) x x))))) h4)) (S (h v6 x v3))) (C (T (h y x z) (C (T (T (T (C h4 (T (h v1 v5 z) (C (S (h v2 v2 v2)) h0))) (h (M v3 (M v2 z)) x z)) (C (C h4 (S (h v2 x z))) h0)) (S (h v1 x z))) h0)) (R y))

@[equational_result]
theorem Equation2958_implies_Equation3370 (G: Type _) [Magma G] (h: Equation2958 G) : Equation3370 G := fun x y z =>
  let v0 := M z (M z x)
  have h1 := R v0
  let v2 := M (M x (M x x)) x
  have h3 := R x
  have h4 := h x x x
  let v5 := M (M x (M x v0)) v0
  let v6 := M v0 x
  have h7 := h v0 x v0
  let v8 := M x y
  have h9 := R v8
  let v10 := M (M x (M x v8)) v8
  let v11 := M v8 v0
  have h12 := h v8 x v8
  T (h v8 v8 v0) (C (T (T (T (T (C (C (T h12 (C (R v10) h12)) (R v11)) h9) (S (h v11 v10 v8))) (C h9 (T (T (h v0 v0 x) (C (T (C (C (T h7 (C (R v5) h7)) (R v6)) h1) (S (h v6 v5 v0))) h3)) (S (h x z x))))) (C (C (T h4 (C (R v2) h4)) (R y)) h3)) (S (h y v2 x))) h1)

@[equational_result]
theorem Equation3804_implies_Equation4477 (G: Type _) [Magma G] (h: Equation3804 G) : Equation4477 G := fun x y z =>
  let v0 := M x z
  let v1 := M y y
  let v2 := M v1 y
  let v3 := M x v1
  let v4 := M y v3
  have h5 := R v3
  have h6 := h x v1 v1
  have h7 := h y y y
  T (T (T (T (T (T (T h6 (C (S h7) h5)) (h v1 v3 y)) (h v4 v2 v1)) (C (S (h v1 y y)) (S (h y v3 y)))) (h v2 v4 v0)) (C (T (C (T (T (h x z v3) (C (R (M v3 z)) (T (h x v3 v1) (C (T (C h7 h5) (S h6)) h5)))) (S (h v3 z v3))) (R v4)) (S (h y z v3))) (T (C (R v2) (T (h x z x) (C (R v0) (T (T (T (h x x y) (h (M y x) (M x y) v1)) (C (S (h x y y)) (S (h y x y)))) (S (h y y x)))))) (S (h v0 y v1))))) (S (h v0 z y))

@[equational_result]
theorem Equation2677_implies_Equation3331 (G: Type _) [Magma G] (h: Equation2677 G) : Equation3331 G := fun x y z =>
  let v0 := M y z
  let v1 := M z v0
  let v2 := M x v1
  have h3 := R y
  let v4 := M v2 y
  have h5 := R x
  let v6 := M x y
  have h7 := h v2 v6 z
  let v8 := M (M v2 v6) (M v6 z)
  let v9 := M v2 v1
  let v10 := M v2 v2
  T (T (C (T (T (h x v1 x) (C (C (h v2 v2 v1) (R (M v1 x))) h5)) (S (h (M v10 v9) v1 x))) h3) (C (C (R v10) (T (T (h v9 v0 v2) (C (C (T (T (T (T (C (C h7 (R v1)) (R v0)) (S (h v8 z v0))) (h v8 z x)) (C (C (T (S h7) (h v2 y z)) (R (M z x))) h5)) (S (h (M v4 v0) z x))) (R (M v0 v2))) (R v2))) (S (h v4 v0 v2)))) h3)) (S (h v2 v2 y))

@[equational_result]
theorem Equation2725_implies_Equation4098 (G: Type _) [Magma G] (h: Equation2725 G) : Equation4098 G := fun x y z =>
  have h0 := R z
  let v1 := M y y
  let v2 := M v1 z
  let v3 := M v2 z
  have h4 := R v2
  let v5 := M x x
  have h6 := h z v5 z
  have h7 := R v5
  let v8 := M z z
  have h9 := R v8
  have h10 := h v5 v2 y
  have h11 := h z v1 x
  have h12 := h z v1 y
  have h13 := h v1 v2 y
  have h14 := h v8 v2 x
  have h15 := C (S h11) h4
  T (T (T (T h10 h15) (C (T h6 (C (C (C (T (T (T h10 h15) (C h12 h4)) (S h13)) h0) h9) h7)) h4)) (S h14)) (C (T (T (h z z v3) (C (C (T h14 (C (T (C (C (C (T (T (T h13 (C (S h12) h4)) (C h11 h4)) (S h10)) h0) h9) h7) (S h6)) h4)) (R (M v3 v3))) h0)) (S (h v2 z v3))) h0)

@[equational_result]
theorem Equation2958_implies_Equation1876 (G: Type _) [Magma G] (h: Equation2958 G) : Equation1876 G := fun x y z =>
  let v0 := M z y
  have h1 := R z
  let v2 := M v0 z
  have h3 := S (h v0 x v0)
  let v4 := M (M x (M x v0)) v0
  have h5 := S (h z x z)
  let v6 := M (M x (M x z)) z
  let v7 := M y z
  let v8 := M x v7
  have h9 := R v8
  let v10 := M (M x (M x x)) x
  have h11 := h x x x
  T (T (h x x v7) (C (T (C (C (T h11 (C (R v10) h11)) h9) (R x)) (S (h v8 v10 x))) (R v7))) (C h9 (T (C (T (T (T (h y v6 z) (C (C (T (C (R v6) h5) h5) (R y)) h1)) (h v2 v4 v0)) (C (C (T (C (R v4) h3) h3) (R v2)) (R v0))) h1) (S (h v0 v0 z))))

@[equational_result]
theorem Equation3186_implies_Equation2 (G: Type _) [Magma G] (h: Equation3186 G) : Equation2 G := fun x y =>
  let v0 := M x y
  have h1 := h y v0 y
  have h2 := R y
  have h3 := h y x y
  have h4 := R x
  let v5 := M v0 x
  have h6 := h y (M v5 y) y
  have h7 := h x x y
  have h8 := C (C h7 h2) h2
  let v9 := M x x
  have h10 := R v9
  have h11 := C (C (S h7) h2) h2
  have h12 := h y v5 y
  T (T (T (T (h x (M v9 v0) x) (C (C (T (T (T (S (h v0 x x)) (C (T (h x v9 x) (C (S (h x x x)) h4)) (T h12 h11))) (C h10 (T (T (T h8 (S h12)) h6) (C h11 h2)))) (C h10 (T (T (T (C h8 h2) (S h6)) h1) (C (S h3) h2)))) h4) h4)) (S (h (M y y) x x))) (C h3 h2)) (S h1)

@[equational_result]
theorem Equation684_implies_Equation3553 (G: Type _) [Magma G] (h: Equation684 G) : Equation3553 G := fun x y z =>
  let v0 := M x y
  let v1 := M (M x z) z
  let v2 := M y v1
  have h3 := R v2
  have h4 := S (h x y v1)
  have h5 := h v2 x z
  have h6 := R y
  have h7 := R x
  let v8 := M y (M (M y x) x)
  have h9 := h y y x
  have h10 := S (h v2 v2 x)
  let v11 := M v2 (M (M v2 x) x)
  T (C h7 (T (T (h y v2 v11) (C h3 (T (C h6 (T (T (C h10 (R v11)) h10) h5)) h4))) (C h3 (T (h x y v2) (C (T (h y x y) (C h7 (T (C h6 (C (R v0) (T h9 (C h9 (R v8))))) (S (h v0 y v8))))) (C h7 (T (C (T (C h6 h5) h4) h3) (S (h y x z))))))))) (S (h v2 x v0))

@[equational_result]
theorem Equation2741_implies_Equation3489 (G: Type _) [Magma G] (h: Equation2741 G) : Equation3489 G := fun x y z =>
  let v0 := M y z
  let v1 := M v0 z
  have h2 := R v1
  let v3 := M x x
  have h4 := R v3
  let v5 := M y y
  have h6 := h v1 x v1
  let v7 := M v3 (M v1 v1)
  have h8 := S (h x x x)
  let v9 := M v3 v3
  let v10 := M y v1
  have h11 := h v3 v10 v1
  T (T (T (T h11 (C (T (T (h (M (M v10 v10) (M v3 v1)) x v1) (C (T (T (C h4 (S h11)) (h v9 v3 x)) (C (T (C (R v9) h8) h8) (R x))) h2)) (C h4 h6)) h2)) (S (h v7 x v1))) (h v7 y v1)) (C (T (T (T (C (R v5) (S h6)) (h (M v5 v1) x z)) (C (C h4 (S (h v0 y z))) (R z))) (S (h y x z))) h2)

@[equational_result]
theorem Equation3131_implies_Equation4162 (G: Type _) [Magma G] (h: Equation3131 G) : Equation4162 G := fun x y z =>
  let v0 := M y x
  let v1 := M (M v0 z) z
  have h2 := h v1 x v1
  have h3 := R x
  have h4 := R v1
  have h5 := h x y z
  have h6 := S h5
  have h7 := h y v1 v1
  have h8 := R v0
  have h9 := S (h y v0 y)
  have h10 := h x y y
  have h11 := C h10 h8
  T (T (T (C (T (h x v0 v0) (C (T (T (T (T (C (T (C (C (T (h v0 x x) (C (C (C (T h11 h9) h3) h3) h3)) h3) h8) (S (h x v0 x))) h8) h11) h9) (h y v1 v0)) (C (C (T (C (T h6 h10) h8) h9) h8) (T h2 (C (T (C (C (C h5 h4) h4) h4) (S h7)) h3)))) h8)) (R y)) (S (h v0 y v0))) (C (T h7 (C (C (C h6 h4) h4) h4)) h3)) (S h2)

@[equational_result]
theorem Equation3193_implies_Equation619 (G: Type _) [Magma G] (h: Equation3193 G) : Equation619 G := fun x y =>
  have h0 := R x
  have h1 := S (h y y x)
  have h2 := R y
  let v3 := M y x
  have h4 := S (h v3 v3 y)
  have h5 := R v3
  have h6 := h v3 y x
  have h7 := C (C (T (C (T (T (C h6 h5) h4) h6) h5) h4) h2) h2
  have h8 := h y v3 v3
  let v9 := M v3 x
  let v10 := M x v9
  have h11 := R v10
  have h12 := C (S (h v10 x v9)) h11
  have h13 := h v10 v10 x
  have h14 := T (C (C (T (T h13 h12) (C (T h13 h12) h11)) h0) h0) (S (h x v10 v10))
  have h15 := h x x v9
  T h15 (C h14 (T h15 (C h14 (T (h x y y) (C (C (T (C (T (T (T (C (T h8 h7) h2) h1) h8) h7) h2) h1) h0) h0)))))

@[equational_result]
theorem Equation3193_implies_Equation1478 (G: Type _) [Magma G] (h: Equation3193 G) : Equation1478 G := fun x y =>
  have h0 := R x
  let v1 := M x x
  have h2 := R v1
  have h3 := C (S (h v1 x x)) h2
  have h4 := h v1 v1 x
  have h5 := C (T (C (C (T (T h4 h3) (C (T h4 h3) h2)) h0) h0) (S (h x v1 v1))) h0
  have h6 := h x x x
  have h7 := S (h y y x)
  have h8 := R y
  let v9 := M y x
  have h10 := S (h v9 v9 y)
  have h11 := R v9
  have h12 := C (h v9 y x) h11
  have h13 := C (C (T (T (C (T h12 h10) h11) h12) h10) h8) h8
  have h14 := h y v9 v9
  T (h x y y) (C (C (T (C (T (T (T (C (T h14 h13) h8) h7) h14) h13) h8) h7) h0) (T (T h6 h5) (C h0 (T h6 h5))))

@[equational_result]
theorem Equation3211_implies_Equation2519 (G: Type _) [Magma G] (h: Equation3211 G) : Equation2519 G := fun x y z =>
  let v0 := M x z
  let v1 := M v0 y
  let v2 := M y v1
  let v3 := M v2 z
  have h4 := R v3
  have h5 := R z
  have h6 := R v1
  have h7 := h y v0 y
  have h8 := h v0 v1 y
  have h9 := T h8 (C (S h7) h6)
  have h10 := R x
  have h11 := C (T (C h7 h6) (S h8)) h5
  have h12 := C (T (C (C h11 h10) h10) (S (h x x z))) h5
  have h13 := h z v3 x
  T (T (h x v2 z) (C (T (T (T (C (C h11 h5) h10) (S (h z x z))) h13) (C (T (T h12 (h v0 z v3)) (C (T (C (C (T (C (T h13 (C h12 h4)) h4) (C (C h9 h4) h4)) h4) h9) (S (h v3 v2 v3))) h5)) h4)) (R v2))) (S (h v3 v2 z))

@[equational_result]
theorem Equation3211_implies_Equation4305 (G: Type _) [Magma G] (h: Equation3211 G) : Equation4305 G := fun x y z =>
  let v0 := M y z
  have h1 := R v0
  let v2 := M x y
  let v3 := M x v2
  have h4 := R v3
  have h5 := R z
  have h6 := h y v0 z
  have h7 := h z y z
  have h8 := T (C h7 h1) (S h6)
  have h9 := R v2
  have h10 := C (S h7) h1
  T (h v3 v0 z) (C (T (C (T (C (C (C (T h6 h10) h5) h5) h5) (C (C (T (T (C h8 h5) (h v0 z v3)) (C (T (C (C (C (T (h z v3 (M z v0)) (C (C (T (C (C (T (C (T (h x v2 y) (C (T (T (S (h y x y)) h6) h10) h9)) h9) (C (C h8 h9) h9)) h8) h8) (S (h y y v2))) h5) h4)) h4) h4) h1) (S (h v3 v0 v3))) h5)) h5) h5)) h4) (S (h z v3 z))) h1)

@[equational_result]
theorem Equation2196_implies_Equation4544 (G: Type _) [Magma G] (h: Equation2196 G) : Equation4544 G := fun x y z =>
  let v0 := M z y
  let v1 := M v0 x
  let v2 := M y z
  let v3 := M x v2
  have h4 := h v0 x v3
  let v5 := M (M x v3) v3
  let v6 := M (M v2 v2) v2
  T (T (h v3 v2 v2) (C (T (T (T (T (h v6 y x) (C (R (M (M y x) x)) (T (C (R v6) (h y z y)) (S (h (M v0 y) v2 v2))))) (S (h v0 y x))) (C (h z y v0) (h y v0 v1))) (S (h (M (M v0 v1) v1) (M y v0) v0))) (T (T (T (T (h (M v3 v2) v1 x) (C (R (M (M v1 x) x)) (T (S (h v0 x v2)) h4))) (S (h v5 v1 x))) (h v5 v1 v0)) (C (T (h (M (M v1 v0) v0) (M x v1) v1) (C (S (h v0 x v1)) (S (h x v1 v0)))) (S h4))))) (S (h v1 v0 v1))

@[equational_result]
theorem Equation4216_implies_Equation3997 (G: Type _) [Magma G] (h: Equation4216 G) : Equation3997 G := fun x y z =>
  let v0 := M x z
  let v1 := M v0 x
  have h2 := S (h z v0 v1)
  have h3 := C (T (h x z x) (h v1 x v0)) (R z)
  have h4 := h v0 z x
  have h5 := S h4
  let v6 := M (M x y) x
  have h7 := R v6
  let v8 := M v1 v0
  have h9 := R y
  let v10 := M (M x v0) x
  have h11 := R v10
  T (T (T (T (T (h x y x) (h v6 x y)) (C (C (T (T (h y x v0) (C (T (T (T (T (T h5 h3) h2) (h z v0 x)) (h v10 z v0)) (C (T (h (M v0 z) v0 x) (C h11 h4)) h11)) h9)) (S (h y v8 v10))) h9) h7)) (S (h v6 v8 y))) (C h7 (T (T h5 h3) h2))) (S (h (M z v0) y x))

@[equational_result]
theorem Equation914_implies_Equation11 (G: Type _) [Magma G] (h: Equation914 G) : Equation11 G := fun x y =>
  let v0 := M y y
  let v1 := M x v0
  have h2 := h v1 v1 v1
  let v3 := M v1 v1
  have h4 := R v0
  let v5 := M v0 v0
  have h6 := R v5
  have h7 := h v0 v0 y
  have h8 := C h4 (C (S h7) h4)
  let v9 := M v5 v0
  have h10 := h v9 v0 y
  have h11 := R v1
  have h12 := h x v1 v0
  T (T h12 (C h11 (T (T (T (h (M (M v1 x) v5) v1 y) (C h11 (C (S h12) h4))) (C h11 (T (T (C (R x) (T (T (T (T (T h7 (C h4 (T (T h10 h8) (C h7 h6)))) (S (h v9 v0 v0))) h10) h8) (C (h v0 x y) h6))) (S (h (M v1 v0) x v0))) (C h2 h4)))) (S (h (M v3 v3) v1 y))))) (S h2)

@[equational_result]
theorem Equation2146_implies_Equation3161 (G: Type _) [Magma G] (h: Equation2146 G) : Equation3161 G := fun x y z =>
  let v0 := M y y
  let v1 := M v0 z
  let v2 := M v1 x
  let v3 := M v2 z
  let v4 := M v3 v3
  let v5 := M v4 v0
  have h6 := h y v0 y
  let v7 := M (M v0 v0) y
  let v8 := M x x
  let v9 := M v8 v0
  have h10 := R v9
  let v11 := M (M v2 v2) v3
  T (T (h x x x) (C (T (T (h (M v8 x) x v2) (C (R (M v8 v2)) (T (T (S (h v1 x x)) (h v1 v2 v3)) (C (R v11) (S (h v2 y z)))))) (S (h v11 x v2))) (T (T (h v8 x v0) (C h10 (T (T (h v9 x y) (C (R (M v8 y)) (T (T (T (C h10 h6) (S (h v7 x v0))) (h v7 v3 v0)) (C (R v5) (S h6))))) (S (h v5 x y))))) (S (h v4 x v0))))) (S (h v3 v2 v3))

@[equational_result]
theorem Equation2741_implies_Equation1673 (G: Type _) [Magma G] (h: Equation2741 G) : Equation1673 G := fun x y z =>
  let v0 := M z z
  let v1 := M v0 y
  have h2 := h v1 x v1
  have h3 := R v1
  let v4 := M v1 v1
  have h5 := h y v0 v1
  have h6 := R v0
  let v7 := M v0 v0
  let v8 := M x y
  have h9 := h v8 v1 v8
  have h10 := R v8
  have h11 := h v0 v0 v8
  T (h x z y) (C (T (C (T (T h11 (C (T (T (h (M v7 (M v0 v8)) z v8) (C (C h6 (S h11)) h10)) (C (R v7) h9)) h10)) (S (h (M v4 (M v8 v8)) v0 v8))) h10) (S h9)) (T (T (T h5 (C (T (h (M v7 (M y v1)) z v1) (C (C h6 (S h5)) h3)) h3)) (C (T (C (T (h v1 v1 v1) (C (R (M v4 v4)) h2)) h3) (S (h (M (M x x) v4) v4 v1))) h3)) (S h2)))

@[equational_result]
theorem Equation2789_implies_Equation1964 (G: Type _) [Magma G] (h: Equation2789 G) : Equation1964 G := fun x y z =>
  let v0 := M y z
  let v1 := M z x
  let v2 := M y v1
  let v3 := M v2 v0
  have h4 := h v3 (M (M x v3) (M x v2)) v3
  have h5 := R v3
  have h6 := h v2 x v3
  have h7 := S h6
  have h8 := T h4 (C (C h7 h7) h5)
  have h9 := T (C h8 (R v2)) (S (h v0 v2 v2))
  have h10 := h z y v1
  T (T (T (T (h x z z) (C (T (T (T (C (C h10 h10) (R v1)) (S (h v1 v3 v1))) (h v1 v3 v2)) (C (C h9 (S h10)) (T (h v2 v3 v3) (C (T (C (R (M v3 v3)) h9) (S (h v0 v2 v0))) h8)))) (R z))) (S (h (M (M v2 v2) v3) v0 z))) (C (C h6 h6) h5)) (S h4)

@[equational_result]
theorem Equation3211_implies_Equation4162 (G: Type _) [Magma G] (h: Equation3211 G) : Equation4162 G := fun x y z =>
  let v0 := M y x
  let v1 := M v0 z
  let v2 := M v1 z
  have h3 := S (h v2 v1 z)
  have h4 := R v1
  have h5 := R v2
  have h6 := R z
  have h7 := h v0 v0 z
  have h8 := C (S h7) h6
  have h9 := h z v2 v0
  have h10 := C (T h9 (C (T (T h8 (h v1 z v2)) (C (T (C (C (C (T h9 (C h8 h5)) h5) h5) h4) (S (h v2 v1 v2))) h6)) h5)) h4
  have h11 := C (S (h z v0 z)) h4
  have h12 := h v0 v1 z
  have h13 := R v0
  T (T (T (T (T (C (T (h x v0 v0) (C (C (T (C (C h7 h13) (T (T (T h12 h11) h10) h3)) (S (h v0 v2 v0))) (R x)) h13)) (R y)) (S (h v0 y x))) h12) h11) h10) h3

@[equational_result]
theorem Equation3804_implies_Equation3895 (G: Type _) [Magma G] (h: Equation3804 G) : Equation3895 G := fun x y z =>
  let v0 := M y z
  let v1 := M y v0
  have h2 := h v1 z y
  have h3 := S h2
  let v4 := M v1 y
  have h5 := h v0 v4 v0
  have h6 := h v0 v0 v1
  have h7 := R (M v0 v1)
  have h8 := h v1 v0 y
  have h9 := h v0 v4 v1
  let v10 := M v1 z
  have h11 := T (T h2 h5) (C h3 (T (T (T h6 (C h8 h7)) (S h9)) h3))
  let v12 := M v10 x
  let v13 := M x v10
  T (T (T (T (T (T (h x x v10) (h v12 v13 v10)) (C (T (C h11 (R v13)) (S (h x v10 v10))) (T (C (R v12) h11) (S (h v10 x v10))))) (S (h v10 v10 x))) (C h2 (T (T (T h2 h9) (C (S h8) h7)) (S h6)))) (S h5)) h3

@[equational_result]
theorem Equation3754_implies_Equation41 (G: Type _) [Magma G] (h: Equation3754 G) : Equation41 G := fun x y z =>
  let v0 := M x x
  let v1 := M x y
  let v2 := M z y
  have h3 := h x x v0
  let v4 := M v0 x
  have h5 := h x x x
  have h6 := h x x y
  have h7 := S h6
  have h8 := h y x z
  have h9 := S h8
  have h10 := R v0
  have h11 := C h10 h9
  have h12 := h (M v1 v2) v0 v0
  have h13 := h x y x
  have h14 := T h6 (C h10 h8)
  T (T (T (T (T (T (T (T h5 (C h14 h14)) (S h12)) (C h9 h10)) (S h13)) (h x y y)) (C h8 (T h8 (C (T (T (T (T (T h13 (C h8 h10)) h12) (C (T (T (T (T h11 h7) h5) (C h3 h3)) (S (h v4 v0 v0))) (T (T h11 h7) h5))) (S (h v0 v4 v0))) (S h3)) (R v2))))) (S (h v2 v1 v0))) (S (h y z x))

@[equational_result]
theorem Equation1492_implies_Equation3150 (G: Type _) [Magma G] (h: Equation1492 G) : Equation3150 G := fun x y =>
  let v0 := M y y
  have h1 := h y v0
  let v2 := M v0 (M v0 v0)
  have h3 := h v2 y
  let v4 := M y v0
  have h5 := R v4
  have h6 := R v2
  have h7 := h y y
  have h8 := h v4 v0
  have h9 := h v0 y
  let v10 := M v0 y
  have h11 := R v10
  have h12 := R (M v10 x)
  have h13 := T h1 (C h11 (T (T h3 (C (T (C h7 h6) (S h8)) h5)) (S h9)))
  let v14 := M v10 (M v10 v10)
  T (T (h x v10) (C h12 (T (T (h v14 y) (C (T (T (C h13 (R v14)) (S (h v0 v10))) (C (R y) h13)) h5)) (S (h (M v10 v0) y))))) (C h12 (T (C h11 (T (T h9 (C (T h8 (C (S h7) h6)) h5)) (S h3))) (S h1)))

@[equational_result]
theorem Equation1507_implies_Equation4421 (G: Type _) [Magma G] (h: Equation1507 G) : Equation4421 G := fun x y z =>
  let v0 := M x y
  let v1 := M x v0
  let v2 := M z y
  let v3 := M v2 z
  let v4 := M v0 v3
  let v5 := M v0 v4
  have h6 := h z v2 y
  let v7 := M y (M y v2)
  let v8 := M v3 (M v3 x)
  let v9 := M v2 (M v2 v1)
  T (T (T (T (C (h x v1 v2) (h v0 x v1)) (S (h v9 (M v1 x) v1))) (h v9 v0 v1)) (C (T (T (T (T (C (h v0 x v3) (R v9)) (S (h v8 v1 v2))) (h v8 v0 x)) (C (T (T (T (S (h y x v3)) (h y z x)) (C (T (T (T (C h6 (h y z v2)) (S (h v7 v3 v2))) (h v7 v3 v0)) (C (S h6) (R v5))) (R (M x (M x z))))) (S (h v5 z x))) (R (M x v1)))) (S (h v4 v0 x))) (R (M v1 (M v1 v0))))) (S (h v3 v0 v1))

@[equational_result]
theorem Equation2519_implies_Equation4013 (G: Type _) [Magma G] (h: Equation2519 G) : Equation4013 G := fun x y z =>
  let v0 := M y z
  let v1 := M (M z v0) x
  have h2 := R x
  have h3 := R z
  have h4 := R v1
  have h5 := h y v1 x
  let v6 := M y x
  let v7 := M v1 (M v6 v1)
  have h8 := h y x z
  let v9 := M x y
  have h10 := S (h y v9 x)
  let v11 := M v6 v9
  T (T (T (T (T (T (T (h v9 x v11) (C (C h2 h10) (R v11))) (h (M v9 v11) x x)) (C (T (C h2 (T (C h10 h2) (C h8 h2))) (C h2 (T (C (S h8) h2) (C h5 h2)))) h2)) (S (h v7 x x))) (h v7 z x)) (C (C h3 (T (T (C (S h5) h3) (h v0 v1 z)) (C (C h4 (T (C (C (R v0) (h z x v0)) h4) (S (h x v0 v1)))) h3))) h2)) (S (h v1 z x))

@[equational_result]
theorem Equation2958_implies_Equation2519 (G: Type _) [Magma G] (h: Equation2958 G) : Equation2519 G := fun x y z =>
  let v0 := M x z
  let v1 := M v0 y
  have h2 := R v1
  let v3 := M (M x (M x v1)) v1
  have h4 := h v1 x v1
  let v5 := M (M x (M x v0)) v0
  have h6 := R v0
  have h7 := h v0 x v0
  have h8 := T h7 (C (R v5) h7)
  let v9 := M v0 v1
  let v10 := M y v1
  let v11 := M (M v10 (M v10 x)) x
  have h12 := h x v10 x
  T (h x x z) (C (T (T (T (C (C (T h12 (C (R v11) h12)) h6) (R x)) (S (h v0 v11 x))) (h v0 v0 v1)) (C (T (T (T (C (C h8 (R v9)) h6) (S (h v9 v5 v0))) (C (T (h v0 v0 y) (C (T (T (T (C (C h8 h2) h6) (S (h v1 v5 v0))) h4) (C (R v3) h4)) (R y))) h2)) (S (h y v3 v1))) h2)) (R z))

@[equational_result]
theorem Equation3364_implies_Equation4216 (G: Type _) [Magma G] (h: Equation3364 G) : Equation4216 G := fun x y z =>
  have h0 := R x
  let v1 := M z y
  let v2 := M y v1
  let v3 := M x (M v1 x)
  let v4 := M z v1
  let v5 := M v1 z
  let v6 := M v5 (M x v5)
  let v7 := M v5 z
  have h8 := h z v7 v5
  let v9 := M v5 (M z v5)
  T (T (T (T (T (T (T (h x y v5) (h y v6 v1)) (C (R v6) (T (T (T (T (T (S (h z v1 y)) (h z v1 v5)) (h v1 v9 v5)) (C (R v9) (T (h v5 (M v1 v5) z) (C (h v1 v5 z) h8)))) (S (h v7 v9 v9))) (S h8)))) (S (h v5 v6 z))) (S (h x v5 v5))) (C h0 (T (T (h v1 z x) (h z v3 v1)) (C (R v3) (h v1 v4 x))))) (S (h v4 x v3))) (C (T (C (R z) (T (h z y y) (h y v2 v1))) (S (h v1 z v2))) h0)

@[equational_result]
theorem Equation3567_implies_Equation4182 (G: Type _) [Magma G] (h: Equation3567 G) : Equation4182 G := fun x y z =>
  let v0 := M y z
  let v1 := M v0 z
  have h2 := R v0
  have h3 := h y z x
  let v4 := M v1 v0
  let v5 := M (M x y) x
  have h6 := R x
  let v7 := M v1 x
  let v8 := M (M v7 y) v7
  let v9 := M v7 v1
  T (T (T (T (T (T (T (T (h x y v1) (h y v9 v7)) (h v9 v8 x)) (C (R v8) (C (S (h x x v1)) h6))) (S (h x v8 x))) (S (h y x v7))) (h y x v0)) (C h6 (T (T (h (M v0 y) v0 v0) (C h2 (C (T (T (S (h z v0 y)) (h z v0 v0)) (C h2 (T (C (R v1) (T (T (T h3 (h z v5 v0)) (h v5 v4 z)) (C (R v4) (C (S h3) (R z))))) (S (h v0 v1 v1))))) h2))) (S (h (M v0 v1) v0 v0))))) (S (h v1 x v0))

@[equational_result]
theorem Equation3959_implies_Equation3588 (G: Type _) [Magma G] (h: Equation3959 G) : Equation3588 G := fun x y z =>
  let v0 := M x y
  let v1 := M v0 z
  have h2 := h z v1 x
  let v3 := M v1 (M z x)
  have h4 := h v3 x v0
  have h5 := R v0
  let v6 := M z v1
  have h7 := h v0 v0 z
  have h8 := R z
  have h9 := h v0 z z
  have h10 := R v6
  have h11 := h x y v0
  T (T (T (T (T h11 (h (M y (M x v0)) v0 v0)) (C (T (T (T (T (T (T (T (C h5 (S h11)) h7) (C (T (T (T (h v0 v1 z) (C (C (R v1) h9) h8)) (S (h v6 v1 z))) (C h10 h9)) h8)) (S (h v6 v6 z))) (h v6 v6 v0)) (C (C h10 (T (T (h v6 v0 z) (C (C h5 (S h9)) h8)) (S h7))) h5)) (S (h v0 v6 v0))) (C h5 (T h2 h4))) h5)) (S (h (M x (M v3 v0)) v0 v0))) (S h4)) (S h2)

@[equational_result]
theorem Equation492_implies_Equation1165 (G: Type _) [Magma G] (h: Equation492 G) : Equation1165 G := fun x y z =>
  let v0 := M y x
  let v1 := M z v0
  let v2 := M v1 z
  let v3 := M y v2
  have h4 := h z v0 z
  have h5 := R v1
  have h6 := h v0 v1 z
  have h7 := T h6 (C h5 (S h4))
  have h8 := R v3
  have h9 := R y
  have h10 := C h9 (T (C h5 h4) (S h6))
  have h11 := R x
  have h12 := C h9 (T (C h11 (C h11 h10)) (S (h x x y)))
  have h13 := h y v3 x
  T (T (h x v2 y) (C (R v2) (T (T (T (C h11 (C h9 h10)) (S (h y x y))) h13) (C h8 (T (T h12 (h v0 y v3)) (C h9 (T (C h7 (C h8 (T (C h8 (T h13 (C h8 h12))) (C h8 (C h8 h7))))) (S (h v3 v2 v3))))))))) (S (h v3 v2 y))

@[equational_result]
theorem Equation522_implies_Equation4450 (G: Type _) [Magma G] (h: Equation522 G) : Equation4450 G := fun x y z =>
  let v0 := M y z
  let v1 := M v0 z
  have h2 := h v1 v1 v0
  have h3 := h v0 v1 z
  have h4 := R v1
  have h5 := h z v1 v1
  have h6 := R v0
  have h7 := C h6 (T h5 (C h4 (S h3)))
  have h8 := R z
  let v9 := M y x
  let v10 := M x v9
  have h11 := R x
  T (T (T (T (T (T (h v10 x x) (C h11 (C h11 (C h11 (T (C (R v10) (h x v10 v9)) (S (h v9 v10 v10))))))) (S (h y x x))) (h y v1 z)) (C h4 (C h4 (T (C h8 (T (h v0 z z) (C h8 (T (T (T (C h8 (C h8 h7)) (S (h v1 z v0))) h2) (C h4 (C h4 (C h6 (T (C h4 h3) (S h5))))))))) (S (h v1 z v1)))))) (C h4 (C h4 h7))) (S h2)

@[equational_result]
theorem Equation1504_implies_Equation2373 (G: Type _) [Magma G] (h: Equation1504 G) : Equation2373 G := fun x y z =>
  let v0 := M x z
  let v1 := M z v0
  let v2 := M y v1
  have h3 := R v2
  have h4 := C h3 (S (h y y y))
  have h5 := h v1 y (M y y)
  let v6 := M v2 x
  let v7 := M x v6
  have h8 := R v7
  let v9 := M v2 y
  T (T (T (T (h x v2 x) (C (T (h v6 x x) (C (T (T (h v7 v1 x) (C (T (T (T (T (C (T h5 h4) h8) (S (h y v2 x))) (h y v2 (M y v2))) (C (R v9) (S (h v2 y v2)))) (C (T (C h3 (h y v2 y)) (S (h v1 y v9))) h3)) (R (M x (M v1 x))))) (S (h v2 v1 x))) (T (T (h (M x (M x x)) v0 x) (C (T (S (h z x x)) (h z x z)) (R (M x (M v0 x))))) (S (h v1 v0 x))))) h8)) (S (h v1 v2 x))) h5) h4

@[equational_result]
theorem Equation1908_implies_Equation19 (G: Type _) [Magma G] (h: Equation1908 G) : Equation19 G := fun x y z =>
  let v0 := M z x
  let v1 := M y v0
  let v2 := M x (M v1 z)
  let v3 := M v2 x
  let v4 := M z v1
  have h5 := R y
  let v6 := M y (M v0 x)
  let v7 := M v6 y
  have h8 := R z
  let v9 := M x (M x y)
  let v10 := M v9 x
  T (T (T (h x z v10) (C (C h8 (T (C (h x x y) (R v10)) (S (h x v9 x)))) (R v0))) (C (C h8 (T (h x v2 v1) (C (S (h v1 x z)) (R v3)))) (T (T (T (h v0 y v7) (C (C h5 (T (C (h v0 y x) (R v7)) (S (h y v6 v0)))) (R v1))) (C (C h5 (h y z v0)) (T (h v1 z y) (C (T (C (h z y x) (R (M v1 y))) (S (h y v1 z))) (R v4))))) (S (h v4 y (M z y)))))) (S (h v1 z v3))

@[equational_result]
theorem Equation2741_implies_Equation4612 (G: Type _) [Magma G] (h: Equation2741 G) : Equation4612 G := fun x y z =>
  let v0 := M y z
  let v1 := M v0 z
  have h2 := h v1 y y
  have h3 := R y
  let v4 := M y y
  let v5 := M x x
  have h6 := R v5
  let v7 := M v5 v5
  have h8 := S (h v7 v5 x)
  have h9 := R x
  have h10 := h x x x
  have h11 := C (T h10 (C (R v7) h10)) h9
  T (C (T (T (T (T (T h11 h8) (C (T (T h11 h8) (C h6 (T (T (T (T h11 h8) (h v7 x x)) (C (T (C h6 (S h10)) (C h6 (h x y x))) h9)) (S (h (M v4 v5) x x))))) h6)) (S (h v4 x v5))) (C (T (T (T (h y x z) (C (C (T h11 h8) (h v0 x z)) (R z))) (S (h (M v5 v1) v5 z))) (C h6 h2)) h3)) (S (h (M v4 (M v1 y)) x y))) h3) (S h2)

@[equational_result]
theorem Equation3791_implies_Equation3620 (G: Type _) [Magma G] (h: Equation3791 G) : Equation3620 G := fun x y z =>
  let v0 := M z y
  let v1 := M v0 x
  let v2 := M v1 v0
  let v3 := M v0 z
  let v4 := M x y
  let v5 := M v4 v1
  have h6 := h y v0 x
  have h7 := C (R v1) h6
  have h8 := h x y v0
  have h9 := T h8 h7
  let v10 := M v0 v1
  have h11 := R v10
  T (T (T (T (T (T (T (T (T h8 h7) (h v1 v5 v0)) (C h11 (T (C (S h6) (R v0)) (S (h v0 z y))))) (h v10 v3 v4)) (C (T (T (T (T (C h9 h11) (S (h v5 v0 v1))) (h v5 v0 v4)) (C (T (C h9 (R v5)) (S (h v5 v4 v1))) (h v0 v4 v1))) (S (h v4 v2 v5))) (R (M v3 v4)))) (S (h v2 v3 v4))) (C (h v1 v0 z) (h v0 z v1))) (S (h v3 v2 (M z v1)))) (S (h z v1 v0))

@[equational_result]
theorem Equation3804_implies_Equation4013 (G: Type _) [Magma G] (h: Equation3804 G) : Equation4013 G := fun x y z =>
  let v0 := M y z
  let v1 := M z v0
  have h2 := S (h v1 x v0)
  have h3 := h y v0 z
  have h4 := C (R (M v0 x)) h3
  have h5 := h y x v0
  let v6 := M y v1
  let v7 := M v1 x
  let v8 := M x y
  T (T (T (T (T (T (h x y z) (h (M z y) (M x z) v0)) (C (T (T (C (T (h y z v1) (C (T (T (h v1 z v0) (C (R (M v0 z)) (S h3))) (S (h y z v0))) (R v6))) (T (T (h x z x) (C (T (T (h x z y) (h v0 v8 (M y y))) (C (S (h x y y)) (S (h y z y)))) (T (h x x y) (C (T (T h5 h4) h2) (R v8))))) (S (h v7 v0 v8)))) (S (h v7 v6 v0))) (S (h y x v1))) (S (h y y z)))) (S (h y x y))) h5) h4) h2

@[equational_result]
theorem Equation489_implies_Equation1358 (G: Type _) [Magma G] (h: Equation489 G) : Equation1358 G := fun x y z =>
  let v0 := M z x
  let v1 := M v0 z
  let v2 := M v1 y
  have h3 := S (h v2 v1 y)
  have h4 := R y
  have h5 := h v1 y v2
  let v6 := M v2 y
  have h7 := R v0
  have h8 := R v2
  have h9 := R v1
  have h10 := R x
  T (T (T (h x v0 x) (C h7 (T (C h10 (T (T (C h10 (C h7 (T (h x v1 v1) (C h9 (C h10 (T (C h9 (C h9 (T (h v1 v2 v1) (C h8 (C h9 (C h9 (T (C h8 (T h5 (C h4 (T (T h3 (h v2 v0 v2)) (C h7 (C h8 (T (C h8 (C h7 (T (h v2 y v6) (C h4 (S (h v6 v2 y)))))) (S (h v0 v2 y))))))))) (S (h y v2 v0))))))))) (S (h v1 v1 v2)))))))) (S (h v0 x v1))) (h v0 z x))) (S (h z x v0))))) h5) (C h4 h3)

@[equational_result]
theorem Equation627_implies_Equation4395 (G: Type _) [Magma G] (h: Equation627 G) : Equation4395 G := fun x y =>
  have h0 := R x
  let v1 := M x x
  let v2 := M v1 x
  let v3 := M y v2
  have h4 := S (h x y v3)
  have h5 := h y x x
  have h6 := C h0 (C h0 (T h5 (C h5 (R v3))))
  let v7 := M x y
  have h8 := S (h v7 x v2)
  let v9 := M v7 (M (M x v2) v2)
  let v10 := M x v7
  have h11 := S (h v7 v1 v10)
  let v12 := M v7 (M (M v1 v10) v10)
  let v13 := M y (M (M v2 y) y)
  have h14 := h y v2 y
  T (T (T (T (C h0 (C h0 (T h14 (C h14 (R v13))))) (S (h x y v13))) (h x v7 v12)) (C h0 (T (T (C h0 (T (C h11 (R v12)) h11)) h6) h4))) (C (T (h x v7 v9) (C h0 (T (T (C h0 (T (C h8 (R v9)) h8)) h6) h4))) h0)

