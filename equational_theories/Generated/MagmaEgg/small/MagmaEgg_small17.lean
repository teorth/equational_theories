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
theorem Equation1507_implies_Equation1467 (G: Type _) [Magma G] (h: Equation1507 G) : Equation1467 G := fun x y z =>
  let v0 := M y z
  let v1 := M z v0
  let v2 := M v1 (M v1 y)
  let v3 := M v1 z
  let v4 := M x y
  let v5 := M z (M z v4)
  let v6 := M x v4
  let v7 := M v4 v1
  have h8 := h y x v7
  let v9 := M v7 (M v7 x)
  let v10 := M y x
  T (h x y v1) (C (T (T (T (T (h v10 y x) (C (T (T (T (T (h (M y v10) v4 x) (C (T (S (h y x y)) h8) (R (M x v6)))) (S (h v9 v4 x))) (h v9 v4 z)) (C (S h8) (R v5))) (R v6))) (S (h v5 y x))) (h v5 (M v4 x) v4)) (C (S (h x v4 z)) (S (h y x v4)))) (T (h v2 v3 v1) (C (T (C (R v3) (T (h v2 v0 z) (C (S (h z y v1)) (R (M z v1))))) (S (h z v1 z))) (S (h v0 z v1)))))

@[equational_result]
theorem Equation1507_implies_Equation3601 (G: Type _) [Magma G] (h: Equation1507 G) : Equation3601 G := fun x y z =>
  let v0 := M y x
  let v1 := M v0 z
  let v2 := M z v1
  have h3 := h z v2 v0
  let v4 := M v2 z
  let v5 := M v0 (M v0 v2)
  have h6 := h z v0 v2
  let v7 := M v2 (M v2 v0)
  let v8 := M x y
  T (T (T (T (T (T (T (h v8 x v1) (C (T (h (M x v8) v0 x) (C (S (h x y x)) (T (T (h (M x (M x v0)) v1 x) (C (T (S (h z v0 x)) h6) (R (M x (M x v1))))) (S (h v7 v1 x))))) (R (M v1 (M v1 x))))) (S (h v7 x v1))) (h v7 v4 v5)) (C (T (T (C (R v4) (T (h v7 v1 z) (C (S h6) (R (M z v2))))) (S (h z v2 z))) h3) (R (M v5 (M v5 v4))))) (S (h v5 v4 v5))) (h v5 v4 v2)) (C (S h3) (S (h v1 z v2)))

@[equational_result]
theorem Equation3126_implies_Equation5 (G: Type _) [Magma G] (h: Equation3126 G) : Equation5 G := fun x y =>
  have h0 := R x
  let v1 := M y x
  let v2 := M v1 v1
  have h3 := h y v2 x
  have h4 := R y
  have h5 := R v2
  have h6 := h x y v1
  let v7 := M v1 y
  have h8 := h y v7 x
  have h9 := R v7
  have h10 := h x y y
  let v11 := M v1 x
  have h12 := h y v11 x
  have h13 := R v11
  have h14 := h x y x
  let v15 := M (M (M x y) v1) x
  T (T (T (T (h x y v15) (C (T (T (T (C (C (C (h y x v1) h0) (R v15)) h4) (S (h y v15 x))) h12) (C (C (S h14) h13) h4)) h0)) (C (T (T (T (C (C h14 h13) h4) (S h12)) h8) (C (C (S h10) h9) h4)) h0)) (C (T (T (T (C (C h10 h9) h4) (S h8)) h3) (C (C (S h6) h5) h4)) h0)) (C (T (C (C h6 h5) h4) (S h3)) h0)

@[equational_result]
theorem Equation492_implies_Equation1943 (G: Type _) [Magma G] (h: Equation492 G) : Equation1943 G := fun x y z =>
  let v0 := M x z
  have h1 := R v0
  let v2 := M y z
  let v3 := M y v2
  have h4 := h y v2 y
  have h5 := R v3
  have h6 := h v2 v3 y
  have h7 := h z z y
  have h8 := R y
  have h9 := h y v3 z
  have h10 := R v2
  T (h x v3 v0) (C h5 (T (C (R x) (C h1 (T (C h1 (T (C h8 (T (h v2 z y) (C (R z) (T (T (T (T (C h10 (C h8 (T (h v2 v2 v3) (C h10 (C h10 (T (T (C h5 (T (C h5 (C h8 h7)) (S h9))) (C h5 h4)) (S h6))))))) (S (h y v2 v2))) h9) (C h5 (C h8 (S h7)))) (C h5 (T h6 (C h5 (S h4)))))))) (S (h z y v3)))) (C h1 (T (h z v0 x) (C h1 (S (h x z x)))))))) (S (h v0 x v0))))

@[equational_result]
theorem Equation492_implies_Equation2186 (G: Type _) [Magma G] (h: Equation492 G) : Equation2186 G := fun x y z =>
  let v0 := M y z
  let v1 := M v0 y
  let v2 := M z x
  let v3 := M v1 v2
  have h4 := R x
  have h5 := h y z y
  have h6 := R v0
  have h7 := C h6 (S h5)
  have h8 := h z v0 y
  have h9 := R v1
  have h10 := R v3
  have h11 := C h10 (C (T (C h6 h5) (S h8)) (T (C h4 (C h4 (C h9 (C (T h8 h7) h4)))) (S (h x x v1))))
  have h12 := h v1 v3 x
  have h13 := R v2
  T (T (h x v2 z) (C h13 (T (T (T (T (T (S (h z x z)) h8) h7) h12) h11) (C h10 (T (h v2 v1 v3) (C h9 (T (C h13 (C h10 (C h10 (T h12 h11)))) (S (h v3 v2 v3))))))))) (S (h v3 v2 v1))

@[equational_result]
theorem Equation914_implies_Equation3692 (G: Type _) [Magma G] (h: Equation914 G) : Equation3692 G := fun x y z =>
  let v0 := M y y
  let v1 := M z z
  have h2 := h (M v0 v1) y v0
  have h3 := S h2
  have h4 := R (M v0 v0)
  have h5 := h y y z
  have h6 := C h5 h4
  have h7 := h y y y
  have h8 := S h7
  have h9 := R y
  have h10 := C h9 (T (C (S h5) h4) h8)
  have h11 := R v0
  let v12 := M x x
  have h13 := h v12 v0 x
  T (T (T (T (T h13 (C h11 (T (h (M (M v0 v12) v12) v0 x) (C (T (C h9 (T h7 h6)) h3) (C (S h13) (R v12)))))) (S (h v1 v0 v12))) (h v1 y v0)) (C h9 (T (C (T (C h9 (T (h v1 v0 z) (C h11 (T (T (C (T h2 h10) (R v1)) h2) h10)))) h8) h4) h6))) h3

@[equational_result]
theorem Equation1967_implies_Equation962 (G: Type _) [Magma G] (h: Equation1967 G) : Equation962 G := fun x y z =>
  let v0 := M z y
  let v1 := M x z
  let v2 := M v0 v1
  let v3 := M y v2
  let v4 := M v0 y
  have h5 := R (M v0 v3)
  let v6 := M v3 v2
  have h7 := S (h v1 y z)
  let v8 := M x v2
  T (T (h x y v0) (C (T (T (T (C (T (T (h y x z) (C (C (R x) (T (h v0 v2 x) (C (S (h z v0 x)) (R v8)))) (R (M z x)))) (S (h v8 x z))) (R (M v0 x))) (S (h v1 x v0))) (h v1 v3 v0)) (C (T (T (h v6 v3 v0) (C (C (R v3) (T (C (T (T (h v0 v0 (M y (M z v1))) (C (C (R v0) h7) h7)) (C (R v2) (h v1 y v0))) (R v6)) (S (h v4 v2 v3)))) h5)) (S (h y v3 v0))) h5)) (R v4))) (S (h v3 y v0))

@[equational_result]
theorem Equation3398_implies_Equation4647 (G: Type _) [Magma G] (h: Equation3398 G) : Equation4647 G := fun x y z =>
  let v0 := M z y
  have h1 := R v0
  have h2 := h y y y
  let v3 := M x y
  have h4 := h y y v3
  have h5 := S h4
  have h6 := h x y y
  have h7 := R v3
  have h8 := C h7 h6
  have h9 := R y
  have h10 := h x v3 y
  have h11 := h x x y
  let v12 := M x x
  T (T (T (T (T (h v3 x v3) (C h7 (T (h x (M v3 v3) y) (C h9 (C (T (T (T (T h8 h5) h2) (C h9 (T (C h9 (T h4 (C h7 (S h6)))) (S h10)))) (S h11)) h7))))) (S (h v12 y v3))) (h v12 y v0)) (C h1 (T (C h9 (C (T (T (T (T h11 (C h9 (T h10 (C h9 (T h8 h5))))) (S h2)) (h y y v0)) (C h1 (S (h z y y)))) h1)) (S (h z (M v0 v0) y))))) (S (h v0 z v0))

@[equational_result]
theorem Equation3804_implies_Equation3567 (G: Type _) [Magma G] (h: Equation3804 G) : Equation3567 G := fun x y z =>
  let v0 := M z x
  let v1 := M v0 z
  have h2 := S (h y v1 v0)
  have h3 := h v0 x z
  have h4 := C h3 (R (M y v0))
  have h5 := h y x v0
  let v6 := M y v1
  let v7 := M v1 x
  let v8 := M x y
  T (T (T (T (T (T (h x y z) (h (M z y) (M x z) v0)) (C (S (h x x z)) (T (T (C (T (T (h z y y) (C (T (h y y x) (C (R v8) (T (T h5 h4) h2))) (T (T (h z y x) (h v8 v0 (M x x))) (C (S (h z x x)) (S (h x y x)))))) (S (h v0 v6 v8))) (T (h z x v1) (C (R v7) (T (T (h z v1 v0) (C (S h3) (R (M z v0)))) (S (h z x v0)))))) (S (h v7 v6 v0))) (S (h y x v1))))) (S (h y x x))) h5) h4) h2

@[equational_result]
theorem Equation4013_implies_Equation3370 (G: Type _) [Magma G] (h: Equation4013 G) : Equation3370 G := fun x y z =>
  let v0 := M z x
  let v1 := M z v0
  have h2 := R y
  have h3 := R v0
  let v4 := M v0 v1
  have h5 := h z x y
  let v6 := M x y
  let v7 := M y v6
  let v8 := M v6 (M x v6)
  let v9 := M v1 (M y v1)
  T (T (T (T (T (T (T (T (h x y v1) (h v9 x v6)) (h v8 v9 y)) (C (C h2 (S (h y y v1))) (R v8))) (S (h v8 y y))) (S (h y x v6))) (h y x v0)) (C (T (T (h v0 (M x v0) v0) (C (C h3 (T (T (S (h v0 z x)) (h v0 z v0)) (C (T (C (T (T (T h5 (h v7 z v0)) (h v4 v7 z)) (C (C (R z) (S h5)) (R v4))) (R v1)) (S (h v1 v0 v1))) h3))) h3)) (S (h v0 (M v1 v0) v0))) h2)) (S (h y v1 v0))

@[equational_result]
theorem Equation895_implies_Equation14 (G: Type _) [Magma G] (h: Equation895 G) : Equation14 G := fun x y =>
  let v0 := M x y
  let v1 := M y v0
  have h2 := h v1 v1 (M (M v0 x) (M v1 x))
  have h3 := S h2
  have h4 := h v0 v1 x
  have h5 := R v1
  have h6 := C h5 (C h4 h4)
  have h7 := h y v0 v0
  have h8 := S h7
  have h9 := S h4
  have h10 := T h2 (C h5 (C h9 h9))
  have h11 := R v0
  have h12 := C h11 h10
  T (T (T (T (h x v0 y) (C h11 (C (T (h v0 v1 v1) (C h10 (T (T (T (C (T h12 h8) (T (C h10 h5) (C (T (T h6 h3) (C (T h7 (C h11 (T h6 h3))) h11)) h5))) (S (h (M v0 v1) y v0))) h12) h8))) (R (M v0 y))))) (S (h (M v1 (M v0 v0)) v0 y))) h6) h3

@[equational_result]
theorem Equation1507_implies_Equation2917 (G: Type _) [Magma G] (h: Equation1507 G) : Equation2917 G := fun x y z =>
  let v0 := M x y
  let v1 := M y v0
  let v2 := M v1 z
  let v3 := M v2 z
  let v4 := M v2 (M v2 v3)
  let v5 := M y (M y v2)
  let v6 := M y v1
  have h7 := h y x v3
  let v8 := M v3 (M v3 x)
  let v9 := M z x
  T (T (T (T (h x z y) (C (T (T (T (T (h v9 z z) (C (T (T (T (T (T (T (h (M z v9) v0 x) (C (T (S (h y x z)) h7) (R (M x (M x v0))))) (S (h v8 v0 x))) (h v8 v0 y)) (C (S h7) (R v6))) (h (M y v6) v2 y)) (C (S (h z v1 y)) (R v5))) (R (M z (M z z))))) (S (h v5 z z))) (h v5 v3 v2)) (C (S (h z v2 y)) (R v4))) (R (M y (M y z))))) (S (h v4 z y))) (h v4 (M v3 v2) v3)) (C (S (h v2 v3 v2)) (S (h z v2 v3)))

@[equational_result]
theorem Equation2196_implies_Equation4007 (G: Type _) [Magma G] (h: Equation2196 G) : Equation4007 G := fun x y z =>
  let v0 := M y x
  let v1 := M z v0
  let v2 := M v1 z
  have h3 := h z v2 v0
  let v4 := M z v2
  let v5 := M (M v2 v0) v0
  let v6 := M (M v0 v2) v2
  have h7 := h y x v0
  let v8 := M (M x v0) v0
  let v9 := M v0 x
  let v10 := M x y
  T (T (T (T (T (T (T (h v10 y x) (C (R v9) (T (T (T (T (h (M v10 y) v0 x) (C (R (M v9 x)) (T (S (h y x y)) h7))) (S (h v8 v0 x))) (h v8 v0 v2)) (C (R v6) (S h7))))) (S (h v6 y x))) (h v6 v4 v5)) (C (R (M (M v4 v5) v5)) (T (T (C (T (h v6 v1 z) (C (R (M v2 z)) (S (h z v0 v2)))) (R v4)) (S (h z v2 z))) h3))) (S (h v5 v4 v5))) (h v5 v4 v2)) (C (S (h v1 z v2)) (S h3))

@[equational_result]
theorem Equation2196_implies_Equation4013 (G: Type _) [Magma G] (h: Equation2196 G) : Equation4013 G := fun x y z =>
  let v0 := M y z
  let v1 := M z v0
  let v2 := M v1 x
  let v3 := M v2 x
  have h4 := h z v0 v2
  let v5 := M (M v0 v2) v2
  let v6 := M x y
  let v7 := M v6 y
  let v8 := M v7 y
  have h9 := h x y y
  let v10 := M (M y y) y
  let v11 := M (M v6 v1) v1
  T (T (T (T (T (T (C (h x y v6) (h y v6 v1)) (S (h v11 (M y v6) v6))) (h v11 x x)) (C (R (M (M x x) x)) (T (T (T (C (R v11) h9) (S (h v10 v6 v1))) (h v10 v6 y)) (C (R v8) (S h9))))) (S (h v8 x x))) (C (R v7) (T (T (h y z x) (C (R (M (M z x) x)) (T (T (T (C (h y z v0) h4) (S (h v5 v1 v0))) (h v5 v1 x)) (C (R v3) (S h4))))) (S (h v3 z x))))) (S (h v2 x y))

@[equational_result]
theorem Equation2779_implies_Equation3794 (G: Type _) [Magma G] (h: Equation2779 G) : Equation3794 G := fun x y z =>
  let v0 := M x y
  let v1 := M z y
  let v2 := M z x
  let v3 := M v2 v1
  have h4 := h v3 y v0
  have h5 := R y
  let v6 := M (M y v0) (M v3 v0)
  have h7 := R x
  have h8 := R v0
  let v9 := M v3 y
  let v10 := M x v1
  T (T (C (T (T (h x x v1) (C (C (R v10) (T (T (h v10 x v3) (C (C (R (M x v3)) (T (T (T (h (M v10 v3) x x) (C (C (R (M x x)) (S (h v2 x v1))) h7)) (S (h z x x))) (h z v3 y))) h7)) (S (h (M v9 v1) x v3)))) h7)) (S (h v9 x v1))) h5) (C (T (T (h v9 x v0) (C (C (R (M x v0)) (T (h (M v9 v0) v0 v3) (C (T (C (C h8 h4) (S (h x v3 y))) (S (h v6 x y))) h8))) h7)) (S (h v6 x v0))) h5)) (S h4)

@[equational_result]
theorem Equation3791_implies_Equation4297 (G: Type _) [Magma G] (h: Equation3791 G) : Equation4297 G := fun x y z =>
  let v0 := M z z
  have h1 := h v0 x y
  have h2 := S h1
  let v3 := M x y
  let v4 := M y v0
  let v5 := M v4 v3
  have h6 := R v4
  have h7 := h x y v0
  have h8 := R v5
  let v9 := M v0 y
  have h10 := R v9
  have h11 := h z z z
  T (T (T (T (T (h x v3 v0) (C h1 (T (T (T (h v3 v0 v4) (C h8 (T (T (T (C h11 (T (h y v0 v0) (C h10 (S h11)))) (S (h v0 v9 v0))) (C (T (T (T (h z z y) (h (M y z) (M z y) v0)) (C (S (h z y z)) (S (h y z z)))) (S (h y y z))) h10)) (S (h y v0 y))))) (C h2 h6)) (S h7)))) (C h8 (T h7 (C h1 h6)))) (S (h v3 v5 v4))) (C (R v3) h2)) (S (h y v0 x))

@[equational_result]
theorem Equation1507_implies_Equation1320 (G: Type _) [Magma G] (h: Equation1507 G) : Equation1320 G := fun x y z =>
  let v0 := M y x
  let v1 := M v0 z
  let v2 := M v1 z
  let v3 := M y v2
  let v4 := M v2 (M v2 y)
  let v5 := M y v3
  let v6 := M v3 (M v3 v1)
  let v7 := M x (M x v0)
  have h8 := h x y v2
  let v9 := M z v0
  let v10 := M z v9
  T (T h8 (C (T (T (h v0 z z) (C (T (T (T (T (h v9 z v3) (C (T (T (T (T (h v10 x x) (C (T (T (T (C h8 (R v10)) (S (h v4 v0 z))) (h v4 v0 x)) (C (S h8) (R v7))) (R (M x (M x x))))) (S (h v7 x x))) (h v7 v1 v3)) (C (S (h z v0 x)) (R v6))) (R (M v3 (M v3 z))))) (S (h v6 z v3))) (h v6 v2 y)) (C (S (h z v1 v3)) (R v5))) (R (M z (M z z))))) (S (h v5 z z))) (R v4))) (S (h v3 y v2))

@[equational_result]
theorem Equation1537_implies_Equation695 (G: Type _) [Magma G] (h: Equation1537 G) : Equation695 G := fun x y z =>
  let v0 := M z z
  let v1 := M v0 y
  let v2 := M x v1
  let v3 := M y v2
  have h4 := S (h v0 x z)
  have h5 := h z z z
  have h6 := R v0
  have h7 := R z
  have h8 := C h7 (T (h z z v0) (C h6 (S h5)))
  let v9 := M v3 v3
  have h10 := R (M x x)
  let v11 := M y y
  have h12 := R v11
  T (T (h x y v1) (C h12 (T (T (C (T (C h6 (T (h y z y) (C h6 (C (R y) (T (T (h v11 x z) (C h10 (T (C h7 (T (C h12 h5) (S (h z y v0)))) h8))) h4))))) (S (h y z v0))) (R v2)) (h v3 z v3)) (C h6 (C (R v3) (T (T (h v9 x z) (C h10 (T (C h7 (T (C (R v9) h5) (S (h z v3 v0)))) h8))) h4)))))) (S (h v3 y v0))

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
theorem Equation2196_implies_Equation1340 (G: Type _) [Magma G] (h: Equation2196 G) : Equation1340 G := fun x y z =>
  let v0 := M (M y z) z
  let v1 := M v0 x
  let v2 := M y v1
  have h3 := h v2 v1 v2
  let v4 := M v2 v1
  let v5 := M v4 v1
  have h6 := h x v1 v2
  have h7 := S (h v0 x v1)
  let v8 := M x v1
  let v9 := M (M v1 v2) v2
  let v10 := M v0 y
  have h11 := R (M (M v1 x) x)
  T (T h6 (C (R v9) (T (T (h v8 v1 v1) (C (R (M (M v1 v1) v1)) (T (T (T (h (M v8 v1) v1 x) (C h11 h7)) (C h11 (T (h v0 v2 v1) (C (R v5) (T (T (T (C (T (h v0 y z) (C (h v0 y v1) (R v10))) h3) (S (h v9 v4 v10))) (h v9 v8 v1)) (C h7 (S h6))))))) (S (h v5 v1 x))))) (S (h v4 v1 v1))))) (S h3)

@[equational_result]
theorem Equation3211_implies_Equation2279 (G: Type _) [Magma G] (h: Equation3211 G) : Equation2279 G := fun x y z =>
  let v0 := M z y
  have h1 := h z v0 y
  have h2 := S h1
  have h3 := R v0
  have h4 := h y z y
  have h5 := C h4 h3
  have h6 := T h5 h2
  let v7 := M y v0
  let v8 := M x v7
  have h9 := R x
  have h10 := R v8
  let v11 := M v8 z
  have h12 := R v11
  T (h x v7 v8) (C (T (C (C (C (T (h v7 v8 x) (C (T (C (C (C (T (h v8 x v7) (C (T (T (T (C (T (T (C h10 h6) (h v11 v7 v11)) (C (C (C (T (C (T (T h5 h2) (h z v8 z)) h12) (S (h v8 v11 z))) h12) h12) h6)) h10) (S (h z v8 v11))) h1) (C (S h4) h3)) h9)) h9) h9) (R v7)) (S (h x v7 x))) h10)) h10) h10) h9) (S (h v8 x v8))) h6)

@[equational_result]
theorem Equation3791_implies_Equation4026 (G: Type _) [Magma G] (h: Equation3791 G) : Equation4026 G := fun x y z =>
  let v0 := M x y
  let v1 := M z y
  let v2 := M z v1
  have h3 := h v2 x y
  let v4 := M y v2
  let v5 := M v0 v0
  let v6 := M v2 x
  have h7 := T (T h3 (h v4 v0 v6)) (C (S (h x y v2)) (S (h y v2 x)))
  let v8 := M y v0
  let v9 := M v1 v0
  T (T (T (T (h x y v0) (C (T (T (T (h v0 x v1) (h v9 (M x v1) v6)) (C (T (T (C h7 (R v9)) (S (h v4 v1 v0))) (S (h v2 z y))) (S (h v1 v2 x)))) (S (h z v1 v2))) (R v8))) (h v2 v8 v0)) (C (R (M v0 v2)) (T (T (T (T (S (h v0 x y)) (h v0 x v0)) (h v5 (M x v0) v6)) (C (T (T (C h7 (R v5)) (S (h v4 v0 v0))) (S h3)) (S (h v0 v2 x)))) (S (h x v0 v2))))) (S (h v2 x v0))

@[equational_result]
theorem Equation4176_implies_Equation3334 (G: Type _) [Magma G] (h: Equation4176 G) : Equation3334 G := fun x y z =>
  let v0 := M z y
  let v1 := M z v0
  have h2 := R v1
  have h3 := S (h v1 v1 z)
  have h4 := R z
  have h5 := S (h v1 z v0)
  have h6 := C h5 h2
  have h7 := h v0 v1 v1
  have h8 := R v0
  have h9 := h z y z
  let v10 := M (M y z) z
  let v11 := M v0 v0
  T (T (h x y v1) (C (C (T (T (h y v1 z) (C (T (T (T (T (T (C (T (C (h z v0 v0) h4) (S (h v0 v11 z))) (R y)) (S (h v11 z y))) (C (T (C (T (T h9 (h v10 z v0)) (C (T (T (T (h v1 v10 z) (C (C (S h9) h2) h4)) (C (T h7 h6) h4)) h3) h8)) h8) (C h5 h8)) h4)) (S (h v0 v1 z))) h7) h6) h4)) h3) (R x)) h2)) (S (h x v1 v1))

@[equational_result]
theorem Equation1131_implies_Equation2928 (G: Type _) [Magma G] (h: Equation1131 G) : Equation2928 G := fun x y z =>
  let v0 := M x z
  let v1 := M y v0
  have h2 := R v1
  have h3 := R y
  have h4 := h z y z
  let v5 := M (M y (M z z)) z
  have h6 := h x y v1
  have h7 := h z y x
  have h8 := T (C h3 (C h7 h2)) (S h6)
  have h9 := R z
  have h10 := S h7
  have h11 := T h6 (C h3 (C h10 h2))
  have h12 := R x
  have h13 := h z y v0
  T (T h6 (C h3 (C (T (T h10 h13) (C h3 (T (T (T (T (T (h (M (M y (M v0 z)) v0) x y) (C h12 (C (T (C h11 (S h13)) (C h8 h9)) h3))) (C h12 (C (T (C h11 h9) (C h8 h4)) h3))) (S (h v5 x y))) (h v5 v1 y)) (C h2 (C (C h2 (S h4)) h3))))) h2))) (S (h (M (M v1 z) y) y v1))

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
theorem Equation1764_implies_Equation2722 (G: Type _) [Magma G] (h: Equation1764 G) : Equation2722 G := fun x y z =>
  let v0 := M z y
  let v1 := M y x
  let v2 := M v1 v0
  let v3 := M v2 z
  let v4 := M z v0
  have h5 := S (h v1 z y)
  let v6 := M v2 v3
  have h7 := R (M v3 v0)
  let v8 := M v2 x
  T (T (h x z v0) (C (R v4) (T (T (T (C (R (M x v0)) (T (T (h z x y) (C (R (M x y)) (C (T (h v0 v2 x) (C (R v8) (S (h y v0 x)))) (R x)))) (S (h v8 x y)))) (S (h v1 x v0))) (h v1 v3 v0)) (C h7 (T (T (h v6 v3 v0) (C h7 (C (T (C (R v6) (T (T (h v0 v0 (M (M v1 y) z)) (C h5 (C h5 (R v0)))) (C (h v1 z v0) (R v2)))) (S (h v4 v2 v3))) (R v3)))) (S (h z v3 v0))))))) (S (h v3 z v0))

@[equational_result]
theorem Equation2105_implies_Equation3201 (G: Type _) [Magma G] (h: Equation2105 G) : Equation3201 G := fun x y z =>
  let v0 := M y z
  let v1 := M v0 y
  let v2 := M v1 z
  let v3 := M v2 x
  have h4 := S (h z y x)
  let v5 := M x x
  have h6 := R v5
  have h7 := R v1
  have h8 := S (h (M v1 v1) v1 x)
  have h9 := C (h z y v1) h7
  have h10 := C (T (C h4 h7) h9) h6
  have h11 := h v5 v1 x
  have h12 := C h7 (T (T (h v1 v5 x) (C (T (C (C (T (T h11 h10) h8) h7) h6) (S (h v1 v1 x))) h6)) h4)
  T (T (h x x v0) (C (T (T (C (T (T (T h11 h10) h8) h12) (R x)) (h v3 v3 v1)) (C (C (T (T (T (h (M v3 v3) v1 x) (C (T (C (S (h z y v3)) h7) h9) h6)) h8) h12) (R v3)) h12)) (R (M v0 v0)))) (S (h v3 v2 v0))

@[equational_result]
theorem Equation3131_implies_Equation1504 (G: Type _) [Magma G] (h: Equation3131 G) : Equation1504 G := fun x y z =>
  let v0 := M y z
  let v1 := M z v0
  let v2 := M y x
  let v3 := M v2 v1
  have h4 := R v0
  have h5 := R v3
  have h6 := R v1
  have h7 := h v0 z z
  have h8 := C (S h7) h6
  have h9 := h z v1 z
  have h10 := R y
  have h11 := C (T (C h7 h6) (S h9)) h4
  T (T (h x y y) (C (C (C (T (h v2 v3 v2) (C (S (h v1 v2 v2)) h5)) h10) h10) (T (T (h y v0 v3) (C (C (C (T (T (T (C (T (h v0 v1 v1) (C (C (T (C (T (C (C (T h9 h8) h4) h4) (C (T (T h11 (h v1 v0 v0)) (C (C h11 h4) h4)) h4)) h6) (S (h v0 v1 v0))) h6) h6)) h10) (S (h z y v1))) h9) h8) h5) h5) h4)) (S (h v1 v0 v3))))) (S (h v3 v1 y))

@[equational_result]
theorem Equation3398_implies_Equation3297 (G: Type _) [Magma G] (h: Equation3398 G) : Equation3297 G := fun x y z =>
  have h0 := h z z y
  let v1 := M z y
  let v2 := M z v1
  have h3 := R v2
  have h4 := C h3 (S (h z v1 v1))
  have h5 := h v1 v1 v2
  let v6 := M y v2
  have h7 := R v1
  have h8 := R v6
  T (T (T (T (T (T (T (T (T (T (T (h x x v2) (h v2 (M x (M x v2)) v6)) (C h8 (C (T (C (R x) (T (h x v2 v6) (C h8 (S (h y x v2))))) (S (h y v6 x))) (R (M v2 v6))))) (S (h v2 (M y v6) v6))) (S (h y y v2))) (h y y v1)) (C h7 (S (h z y y)))) h5) h4) (C h3 (T (h z v1 z) (C (R z) (T (T (T (C h7 h0) (h v1 v6 v1)) (C h7 (T (T (T (C h8 (C h7 (h z y v1))) (S (h v1 v1 v6))) h5) h4))) (S (h z v2 v1))))))) (S (h z z v2))) h0

@[equational_result]
theorem Equation492_implies_Equation4640 (G: Type _) [Magma G] (h: Equation492 G) : Equation4640 G := fun x y z =>
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
  let v12 := M x y
  T (T (T (T (C (R v12) (h x y x)) (S (h y v12 x))) (h y z v0)) (C (R z) (T (T (T (C h7 (C h6 (T (h v1 v1 y) (C h10 (C h10 (T h8 h5)))))) (S (h v0 y v1))) h11) (C h10 (T (T (T (T h9 h3) (h z v1 v0)) (C h10 (S (h v0 z v0)))) (C h10 (T h11 (C h10 (T h9 h3))))))))) (S (h v1 z v1))

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
theorem Equation2958_implies_Equation1943 (G: Type _) [Magma G] (h: Equation2958 G) : Equation1943 G := fun x y z =>
  let v0 := M x z
  let v1 := M y (M y z)
  let v2 := M v1 v0
  let v3 := M (M v1 v2) v0
  have h4 := R v2
  have h5 := h v0 v1 v0
  have h6 := R z
  have h7 := S (h v2 x v2)
  let v8 := M (M x (M x v2)) v2
  let v9 := M (M x (M x x)) x
  have h10 := R x
  have h11 := h x x x
  have h12 := S (h v0 y v0)
  let v13 := M (M y (M y v0)) v0
  T (T (h x v13 v0) (C (T (T (T (T (T (C (T (C (R v13) h12) h12) h10) (C (C (T h11 (C (R v9) h11)) h6) h10)) (S (h z v9 x))) (h z v8 v2)) (C (T (C (T (C (R v8) h7) h7) h6) (S (h v0 y z))) h4)) (C (T h5 (C (R v3) h5)) h4)) (R v0))) (S (h v2 v3 v0))

@[equational_result]
theorem Equation3211_implies_Equation1304 (G: Type _) [Magma G] (h: Equation3211 G) : Equation1304 G := fun x y z =>
  let v0 := M x z
  let v1 := M v0 z
  let v2 := M v1 y
  let v3 := M y v2
  have h4 := R v0
  have h5 := R v3
  have h6 := R z
  have h7 := R v2
  have h8 := h y v1 y
  have h9 := h v1 v2 y
  have h10 := T h9 (C (S h8) h7)
  have h11 := h z v3 x
  have h12 := R x
  have h13 := h x x z
  T (T (T (h x v0 z) (C (S (h z x z)) h4)) (C (T (T h11 (C (C (T (C (C (T (C h8 h7) (S h9)) h12) h12) (S h13)) h6) h5)) (C (T (h v0 v0 v3) (C (C (T (C (T (T (T (C (C (T h13 (C (C h10 h12) h12)) h6) h5) (S h11)) (h z v0 z)) (C (C (C h10 h6) h6) h4)) h5) (S (h v0 v3 z))) h4) h4)) h5)) h4)) (S (h v3 v0 v0))

@[equational_result]
theorem Equation3404_implies_Equation4106 (G: Type _) [Magma G] (h: Equation3404 G) : Equation4106 G := fun x y z =>
  let v0 := M y z
  let v1 := M v0 y
  have h2 := R v0
  let v3 := M v1 v0
  have h4 := R y
  have h5 := R z
  let v6 := M x x
  have h7 := R x
  have h8 := h x x x
  T (T (T (T (T (T (T h8 (C h7 (C h7 h8))) (C h7 (T (T (S (h v6 x x)) (h v6 x v0)) (C h2 (S (h x v0 x)))))) (S (h v0 v0 x))) (h v0 v0 y)) (C h4 (T (T (T (T (T (T (T (C h2 (h y v0 v0)) (S (h v1 v0 v0))) (h v1 v0 z)) (C h5 (S (h y z v0)))) (h z v0 y)) (C h4 (C h2 (h y z y)))) (S (h (M z (M y y)) v0 y))) (C (C h5 (T (T (T (h y y v0) (C h2 (T (C h4 (h v0 y v1)) (S (h v3 v1 y))))) (S (h y v3 v0))) (S (h z v1 y)))) h2)))) (S (h z (M z (M z v1)) y))) (S (h v1 z z))

@[equational_result]
theorem Equation3791_implies_Equation4143 (G: Type _) [Magma G] (h: Equation3791 G) : Equation4143 G := fun x y z =>
  let v0 := M x z
  let v1 := M v0 y
  have h2 := S (h v1 z y)
  let v3 := M z y
  let v4 := M v1 v0
  have h5 := S (h z y x)
  let v6 := M y x
  have h7 := h y x z
  T (T (T (T (T (h x y y) (h v6 (M y y) (M x y))) (C (T (T (T (T (S (h y y x)) (h y y v0)) (C (h v0 y v0) (h y v0 v0))) (S (h (M y v0) v1 (M v0 v0)))) (S (h v0 v0 y))) (T (S (h y x y)) h7))) (S (h v0 v3 v0))) (C (T (T (T (T (T (T (h x z y) (h v6 v3 v0)) (C h5 (S h7))) (h v3 v6 v1)) (C (R (M v1 v3)) (T (T (T (h v6 v1 v0) (C h5 (R v4))) (h v3 v4 (M y v1))) (C h2 (S (h v0 y v1)))))) (S (h v3 (M v1 z) v1))) (S (h y v1 z))) (R v3))) h2

@[equational_result]
theorem Equation492_implies_Equation2399 (G: Type _) [Magma G] (h: Equation492 G) : Equation2399 G := fun x y z =>
  let v0 := M z x
  let v1 := M z v0
  let v2 := M y v1
  let v3 := M v2 y
  have h4 := h y v1 y
  have h5 := R v2
  have h6 := h v1 v2 y
  have h7 := T h6 (C h5 (S h4))
  have h8 := R z
  have h9 := R v0
  have h10 := h z v3 x
  have h11 := R x
  have h12 := h x x z
  have h13 := R v3
  T (T (T (h x v0 z) (C h9 (S (h z x z)))) (C h9 (T (T h10 (C h13 (C h8 (T (C h11 (C h11 (T (C h5 h4) (S h6)))) (S h12))))) (C h13 (T (h v0 v0 v3) (C h9 (C h9 (T (C h13 (T (T (T (C h13 (C h8 (T h12 (C h11 (C h11 h7))))) (S h10)) (h z v0 z)) (C h9 (C h8 (C h8 h7))))) (S (h v0 v3 z)))))))))) (S (h v3 v0 v0))

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
theorem Equation1740_implies_Equation3692 (G: Type _) [Magma G] (h: Equation1740 G) : Equation3692 G := fun x y z =>
  let v0 := M z z
  let v1 := M y y
  let v2 := M v1 v0
  let v3 := M x x
  have h4 := R v3
  let v5 := M v0 v0
  have h6 := R v0
  let v7 := M v5 v0
  let v8 := M v0 v3
  let v9 := M x v3
  T (T (T (T (T (C (T (T (h x z v3) (C h6 (C (T (h (M v3 x) x v3) (C h4 (C (S (h x x x)) h4))) h4))) (S (h v9 z v3))) (R x)) (h (M v9 x) x v3)) (C h4 (T (C (S (h v3 x x)) h4) (C (h v3 x v0) h4)))) (S (h (M v8 v0) x v3))) (C (T (T (h v8 x v3) (C h4 (C (T (T (T (C h4 (C (h v0 x v0) h4)) (S (h v7 x v3))) (h v7 x v0)) (C h4 (C (S (h v0 z v0)) h6))) h4))) (S (h v5 x v3))) (T (T (h v0 x v1) (C h4 (C (h v2 y z) (R v1)))) (S (h (M (M z v2) z) x v1))))) (S (h v2 v0 z))

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
theorem Equation1943_implies_Equation2335 (G: Type _) [Magma G] (h: Equation1943 G) : Equation2335 G := fun x y z =>
  let v0 := M x z
  let v1 := M y (M y v0)
  let v2 := M v1 z
  have h3 := h z y v0
  have h4 := R v1
  let v5 := M x v0
  have h6 := R (M x v5)
  let v7 := M z (M z z)
  let v8 := M v1 v2
  let v9 := M v1 v8
  T (T (T (T (h x y v0) (C h4 (T (T (T (h v5 x v0) (C h6 (S (h x x z)))) (C h6 (h x v1 z))) (S (h v8 x v0))))) (h v9 z v1)) (C (R (M z (M z v1))) (T (T (T (T (T (C (R v9) (h v1 z z)) (S (h v7 v1 v2))) (h v7 x v0)) (C h6 (T (S (h x z z)) (h x v2 z)))) (S (h (M v2 (M v2 z)) x v0))) (C (R v2) (T (C (C h4 h3) h3) (S (h v1 v1 (M z v0)))))))) (S (h v2 z v1))

@[equational_result]
theorem Equation2196_implies_Equation3417 (G: Type _) [Magma G] (h: Equation2196 G) : Equation3417 G := fun x y z =>
  let v0 := M y x
  let v1 := M z v0
  have h2 := R v1
  have h3 := h z v0 v0
  let v4 := M x v0
  let v5 := M (M v0 v0) v0
  have h6 := h y x v0
  let v7 := M (M v0 v1) v1
  let v8 := M v4 v0
  let v9 := M v0 x
  have h10 := R v9
  let v11 := M x y
  T (T (T (T (h v11 y x) (C h10 (T (h (M v11 y) v0 x) (C (T (T (h (M v9 x) v1 x) (C (R (M (M v1 x) x)) (T (S (h z v0 x)) h3))) (S (h v5 v1 x))) (S (h y x y)))))) (C h10 (T (T (T (C (R v5) h6) (S (h v8 v0 v0))) (h v8 v0 v1)) (C (R v7) (S h6))))) (S (h v7 y x))) (C (T (C (T (C h6 (h x v0 v0)) (S (h v5 v4 v0))) h2) (S h3)) h2)

@[equational_result]
theorem Equation4210_implies_Equation4332 (G: Type _) [Magma G] (h: Equation4210 G) : Equation4332 G := fun x y z =>
  let v0 := M y z
  have h1 := R v0
  have h2 := R y
  have h3 := h y y y
  let v4 := M y x
  have h5 := h y y v4
  have h6 := S h5
  have h7 := R v4
  have h8 := h y x y
  have h9 := C h8 h7
  have h10 := h v4 x y
  have h11 := h x x y
  let v12 := M x x
  T (T (T (T (T (h x v4 v4) (C (T (h (M v4 v4) x y) (C (C h7 (T (T (T (T h9 h6) h3) (C (T (C (T h5 (C (S h8) h7)) h2) (S h10)) h2)) (S h11))) h2)) h7)) (S (h y v12 v4))) (h y v12 v0)) (C (T (C (C h1 (T (T (T (T h11 (C (T h10 (C (T h9 h6) h2)) h2)) (S h3)) (h y y v0)) (C (S (h y z y)) h1))) h2) (S (h (M v0 v0) z y))) h1)) (S (h z v0 v0))

@[equational_result]
theorem Equation492_implies_Equation2373 (G: Type _) [Magma G] (h: Equation492 G) : Equation2373 G := fun x y z =>
  let v0 := M x z
  let v1 := M z v0
  have h2 := h y v1 y
  let v3 := M y v1
  have h4 := R v3
  have h5 := C h4 (S h2)
  have h6 := h v1 v3 y
  have h7 := R v0
  have h8 := h z v0 v1
  have h9 := h v0 v1 z
  have h10 := h z v0 z
  have h11 := R v1
  have h12 := R z
  have h13 := h v1 z v1
  T (T (T (h x z v0) (C h12 (T (C (R x) (T (C h7 (C h7 (T h8 (C h7 (T (T (T (C h12 (C h11 (C h11 (T h9 (C h11 (S h10)))))) (S h13)) h6) h5))))) (C h7 (C h7 (T (T (T (C h7 (T (T (T (C h4 h2) (S h6)) h13) (C h12 (C h11 (C h11 (T (C h11 h10) (S h9))))))) (S h8)) (h z v0 x)) (C h7 (S (h x z x)))))))) (S (h v0 x v0))))) h6) h5

@[equational_result]
theorem Equation684_implies_Equation2180 (G: Type _) [Magma G] (h: Equation684 G) : Equation2180 G := fun x y z =>
  let v0 := M x z
  have h1 := S (h z z v0)
  let v2 := M z (M (M z v0) v0)
  let v3 := M y z
  let v4 := M v3 y
  have h5 := S (h v4 v4 x)
  let v6 := M v4 (M (M v4 x) x)
  let v7 := M y v4
  have h8 := S (h y y x)
  let v9 := M y (M (M y x) x)
  have h10 := R v3
  have h11 := R y
  let v12 := M z (M (M z x) x)
  have h13 := h z z x
  T (h x z v2) (C (T (T (h z y z) (C h11 (T (T (T (T (T (C (R z) (C h10 (T h13 (C h13 (R v12))))) (S (h v3 z v12))) (h v3 y v9)) (C h11 (C h10 (T (C h8 (R v9)) h8)))) (h v7 v4 v6)) (C (R v4) (C (R v7) (T (C h5 (R v6)) h5)))))) (S (h v4 y v4))) (C (R x) (T (C h1 (R v2)) h1)))

@[equational_result]
theorem Equation1181_implies_Equation1943 (G: Type _) [Magma G] (h: Equation1181 G) : Equation1943 G := fun x y z =>
  let v0 := M x z
  have h1 := R v0
  let v2 := M y (M y z)
  have h3 := h v2 z v2
  have h4 := R z
  have h5 := h z v2 y
  have h6 := R x
  let v7 := M v2 v0
  have h8 := h z x v7
  let v9 := M (M v7 (M v7 z)) x
  have h10 := h x v2 y
  T (T h10 (C (T h3 (C h4 (C (S h5) h4))) (T (T (h (M (M y (M y x)) v2) x v2) (C h6 (C (T (T (T (T (T (C (R v2) (S h10)) (h (M v2 x) x x)) (C h6 (T (C (C h6 (S (h z x y))) h6) (C (C h6 h8) h6)))) (S (h v9 x x))) (h v9 v0 x)) (C h1 (C (C h6 (S h8)) h1))) h6))) (S (h v0 x v0))))) (C (T (C h4 (C h5 h4)) (S h3)) h1)

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
theorem Equation1710_implies_Equation3692 (G: Type _) [Magma G] (h: Equation1710 G) : Equation3692 G := fun x y z =>
  let v0 := M z z
  let v1 := M (M y y) v0
  let v2 := M x x
  have h3 := h z z z
  have h4 := S h3
  let v5 := M v0 z
  let v6 := M v2 v2
  let v7 := M v6 v0
  let v8 := M v0 v0
  have h9 := R v6
  let v10 := M v2 x
  have h11 := h x x x
  let v12 := M v0 v2
  T (T (T (T (T (h v2 v0 z) (C (T (T (h v12 x x) (C (T (T (T (C h11 (R v12)) (S (h v10 v2 z))) (h v10 v2 x)) (C (S h11) h9)) (R v10))) (S (h v6 x x))) (R v8))) (C h9 (T (h v8 v5 z) (C (S (h z v0 z)) h4)))) (h v7 z x)) (C (T (T (T (C h3 (R v7)) (S (h v5 v0 v2))) (h v5 v0 y)) (C h4 (R v1))) (R (M v2 z)))) (S (h v1 z x))

@[equational_result]
theorem Equation2196_implies_Equation3364 (G: Type _) [Magma G] (h: Equation2196 G) : Equation3364 G := fun x y z =>
  let v0 := M x z
  let v1 := M z v0
  let v2 := M y v1
  let v3 := M v2 v1
  have h4 := h x v2 y
  have h5 := R v2
  have h6 := h x z v0
  have h7 := C (S h6) h5
  have h8 := h y v1 v0
  let v9 := M v2 y
  let v10 := M v9 y
  have h11 := R v10
  let v12 := M x y
  have h13 := T h4 (C h11 (T (C h6 h5) (S h8)))
  let v14 := M (M y v12) v12
  T (C h6 (T (T (T (T (T (T h8 h7) (C h13 (h v2 y v12))) (S (h v14 v9 y))) (h v14 x x)) (C (R (M (M x x) x)) (T (T (T (C (R v14) h13) (S (h v10 y v12))) (h v10 y v1)) (C (R v3) (T (C h11 (T h8 h7)) (S h4)))))) (S (h v3 x x)))) (S (h v2 v1 v0))

@[equational_result]
theorem Equation2958_implies_Equation2992 (G: Type _) [Magma G] (h: Equation2958 G) : Equation2992 G := fun x y z =>
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
  let v11 := M v10 x
  have h12 := S (h v10 v11 v10)
  let v13 := M (M v11 (M v11 v10)) v10
  T (h x v13 v10) (C (C (T (C (R v13) h12) h12) (R x)) (T (C (T (T (T (h y v9 v0) (C (T (T (C (T (C (R v9) h8) h8) h7) (C (T (h v0 v5 z) (C (C h6 h1) h2)) h7)) (S (h z z y))) h1)) (h v3 v5 z)) (C (C h6 (R v3)) h2)) h1) (S (h z z v0))))

@[equational_result]
theorem Equation3385_implies_Equation3994 (G: Type _) [Magma G] (h: Equation3385 G) : Equation3994 G := fun x y z =>
  let v0 := M x y
  let v1 := M z v0
  let v2 := M v1 z
  have h3 := R v2
  let v4 := M v0 z
  have h5 := R v1
  have h6 := R z
  have h7 := R v0
  T (T (T (T (h x y v0) (h v0 (M x (M y v0)) v2)) (C h3 (C h7 (C (T (T (T (C (R x) (T (h y v0 v0) (C h7 (S (h v0 x y))))) (S (h v0 v0 x))) (h v0 v0 v1)) (C h5 (T (T (T (S (h v0 z v0)) (h v0 z v2)) (C h3 (T (C h7 (T (T (T (h z v2 v2) (C h3 (C h6 (C (T (T (T (h v1 z z) (h z (M v1 (M z z)) v2)) (C h3 (C h6 (C (T (C h5 (h z z v0)) (S (h v0 z v1))) h3)))) (S (h z v4 v2))) h3)))) (S (h z (M z v4) v2))) (S (h z v0 z)))) (h v0 v1 z)))) (S (h z v0 v2))))) h3)))) (S (h v0 (M v1 v1) v2))) (S (h v1 z v0))

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
theorem Equation1964_implies_Equation928 (G: Type _) [Magma G] (h: Equation1964 G) : Equation928 G := fun x y z =>
  let v0 := M y z
  let v1 := M x z
  let v2 := M v0 v1
  let v3 := M y v2
  have h4 := h v3 v3 v0
  have h5 := R (M v3 v0)
  let v6 := M v0 v3
  have h7 := h v1 y v0
  have h8 := h z v0 x
  have h9 := h x v3 v0
  let v10 := M v0 x
  have h11 := R v3
  T (T h9 (C (C h11 (T (T (h v10 x v2) (C (T (T (C (R x) (S h8)) h7) (C (T (T h4 (C (C h11 (T (C (C (R y) h8) h11) (S (h v10 y v2)))) h5)) (S h9)) (T (h (M y v0) v0 v3) (C (T (C (T (h v0 z v2) (C (T (C h8 (R (M v2 v0))) (S (h x v2 v0))) (R (M z v2)))) (S h7)) (S (h v2 x z))) (R v6))))) (R (M x v2)))) (S (h v6 x v2)))) h5)) (S h4)

@[equational_result]
theorem Equation2552_implies_Equation1964 (G: Type _) [Magma G] (h: Equation2552 G) : Equation1964 G := fun x y z =>
  let v0 := M y z
  let v1 := M z x
  let v2 := M (M y v1) v0
  have h3 := R v0
  have h4 := R y
  let v5 := M x (M (M x v1) z)
  have h6 := R v1
  have h7 := R x
  have h8 := h z x v1
  let v9 := M x (M (M x v0) y)
  have h10 := h y x v0
  have h11 := S (h z v2 v1)
  let v12 := M v2 (M (M v2 v1) z)
  T (T (T (T (h x v12 v1) (C (T (C (R v12) (C h11 h7)) h11) h6)) (h (M z v1) y v0)) (C (C h4 (T (T (C (T (C (T h10 (C (R v9) (C h10 (R z)))) h3) (S (h z v9 v0))) (T (C (T h8 (C (R v5) (C h8 h7))) h6) (S (h x v5 v1)))) (h v1 y v2)) (C (C h4 (S (h v0 y v1))) (R v2)))) h3)) (S (h v2 y v0))

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
theorem Equation2779_implies_Equation3770 (G: Type _) [Magma G] (h: Equation2779 G) : Equation3770 G := fun x y z =>
  let v0 := M x z
  let v1 := M (M y z) v0
  have h2 := h v1 x v1
  have h3 := R x
  have h4 := h x y z
  have h5 := S h4
  have h6 := h v1 v1 y
  let v7 := M x y
  have h8 := R v7
  have h9 := S (h x x z)
  let v10 := M v7 x
  let v11 := M v0 v0
  have h12 := h v7 x x
  T (T (T (T h12 (C (T (h (M (M x x) v10) v11 x) (C (C h9 (S h12)) (T (h v11 v7 x) (C (C (T (h v10 x x) (C (T (C (C h4 h4) (T (C (C h8 h4) h3) (S (h v1 x y)))) (S h6)) h3)) h9) h8)))) h3)) (S (h (M (M v1 x) x) x v7))) (C (T (C (T h6 (C (C h5 h5) h2)) h3) (S (h (M (M x v1) (M v1 v1)) x x))) h3)) (S h2)

@[equational_result]
theorem Equation4013_implies_Equation4023 (G: Type _) [Magma G] (h: Equation4013 G) : Equation4023 G := fun x y z =>
  have h0 := R y
  have h1 := h z x y
  have h2 := R z
  have h3 := C h2 (S h1)
  let v4 := M y (M x y)
  let v5 := M z x
  let v6 := M z v5
  let v7 := M x (M x x)
  let v8 := M v6 (M y v6)
  let v9 := M v5 v6
  have h10 := T (T (T h1 (h v4 z v5)) (h v9 v4 z)) (C h3 (R v9))
  let v11 := M x v5
  have h12 := R v11
  T (T (T (T (T (T (T (T (h x y v6) (h v8 x v5)) (C (T (T (T (T (T (C h10 h12) (S (h v11 v5 v6))) (C h12 h10)) (S (h (M v6 v9) z x))) (S (h z v5 v6))) (C h2 (h z x x))) (R v8))) (S (h v8 v7 z))) (S (h v7 y v6))) (C (C (R x) (h x x y)) h0)) (S (h y v4 x))) (h y v4 z)) (C h3 h0)

@[equational_result]
theorem Equation684_implies_Equation1467 (G: Type _) [Magma G] (h: Equation684 G) : Equation1467 G := fun x y z =>
  let v0 := M y z
  let v1 := M z v0
  let v2 := M x y
  let v3 := M v2 v1
  have h4 := S (h v3 v3 x)
  let v5 := M v3 (M (M v3 x) x)
  let v6 := M v1 v3
  have h7 := S (h v1 v1 x)
  let v8 := M v1 (M (M v1 x) x)
  have h9 := R v1
  have h10 := S (h y y v0)
  let v11 := M y (M (M y v0) v0)
  have h12 := S (h z z x)
  let v13 := M z (M (M z x) x)
  T (T (T (h x y v11) (C (T (h y z v13) (C (R z) (C (R y) (T (C h12 (R v13)) h12)))) (C (R x) (T (C h10 (R v11)) h10)))) (C h9 (T (T (T (h v2 v1 v8) (C h9 (C (R v2) (T (C h7 (R v8)) h7)))) (h v6 v3 v5)) (C (R v3) (C (R v6) (T (C h4 (R v5)) h4)))))) (S (h v3 v1 v3))

@[equational_result]
theorem Equation684_implies_Equation2958 (G: Type _) [Magma G] (h: Equation684 G) : Equation2958 G := fun x y z =>
  let v0 := M y z
  let v1 := M y v0
  let v2 := M v1 x
  let v3 := M v2 z
  have h4 := S (h v3 v3 x)
  let v5 := M v3 (M (M v3 x) x)
  let v6 := M z v3
  have h7 := S (h z z x)
  let v8 := M z (M (M z x) x)
  have h9 := T (C h7 (R v8)) h7
  have h10 := R v2
  have h11 := R z
  let v12 := M x (M (M x x) x)
  have h13 := h x x x
  T (T (T (h x v1 x) (C (R v1) (T (C (R x) (C h10 (T h13 (C h13 (R v12))))) (S (h v2 x v12))))) (C (T (C (R y) (T (h v0 z v8) (C h11 (C (R v0) h9)))) (S (h z y z))) (T (T (T (h v2 z v8) (C h11 (C h10 h9))) (h v6 v3 v5)) (C (R v3) (C (R v6) (T (C h4 (R v5)) h4)))))) (S (h v3 z v3))

@[equational_result]
theorem Equation1504_implies_Equation692 (G: Type _) [Magma G] (h: Equation1504 G) : Equation692 G := fun x y z =>
  let v0 := M z y
  let v1 := M v0 z
  let v2 := M x v1
  let v3 := M y v2
  have h4 := S (h v3 v2 x)
  have h5 := R (M x (M v2 x))
  have h6 := C (R v0) (S (h z v0 z))
  have h7 := h y z v1
  have h8 := C (R v2) (C (R y) (C (R x) (T h7 h6)))
  have h9 := h v1 x y
  let v10 := M v3 x
  let v11 := M x v10
  T (T (h x v3 v3) (C (T (h v10 x z) (C (T (T (h v11 v2 x) (C (T (T (T (C (T (h v2 y v0) (C (R v3) (T (T (S (h y z y)) h7) h6))) (R v11)) (S (h v1 v3 x))) h9) h8) h5)) h4) (T (T (h (M z (M x z)) v2 x) (C (T (T (S (h v1 x z)) h9) h8) h5)) h4))) (R (M v3 (M v3 v3))))) (S (h v3 v3 v3))

@[equational_result]
theorem Equation1699_implies_Equation14 (G: Type _) [Magma G] (h: Equation1699 G) : Equation14 G := fun x y =>
  let v0 := M y y
  let v1 := M v0 y
  let v2 := M x y
  let v3 := M y v2
  let v4 := M y v3
  have h5 := R v1
  let v6 := M (M v2 v3) v3
  have h7 := R v6
  have h8 := h y x v3
  let v9 := M (M x v3) v3
  let v10 := M y x
  T (T (h x v10 v1) (C (T (T (h (M v10 x) v3 x) (C (T (S (h v2 y x)) (h v2 y v3)) (R (M (M v3 x) x)))) (S (h (M v4 v3) v3 x))) (T (T (T (C (S (h x y y)) h5) (C (R x) (T (C (R v0) (T (T (h y v2 v3) (C (T (T (h (M v2 y) v2 x) (C (T (S (h y x y)) h8) (R (M (M v2 x) x)))) (S (h v9 v2 x))) h7)) (C (T (h v9 v2 v3) (C (S h8) h7)) h7))) (S (h y y v6))))) (h v2 y y)) (C (h v3 y y) h5)))) (S (h v3 v4 v1))

@[equational_result]
theorem Equation3211_implies_Equation2196 (G: Type _) [Magma G] (h: Equation3211 G) : Equation2196 G := fun x y z =>
  let v0 := M x y
  have h1 := R z
  let v2 := M y z
  have h3 := S (h v2 y z)
  have h4 := R y
  have h5 := R v2
  let v6 := M v2 z
  have h7 := R v6
  have h8 := C (T (C (C (C (T (h v2 v6 z) (C (S (h z v2 z)) h7)) h7) h7) h1) (S (h v6 z v6))) h5
  have h9 := h z v2 v6
  have h10 := C (T h9 h8) h4
  have h11 := h y z y
  T (h x v0 y) (C (T (T (S (h y x y)) h11) (C (T (C (T (T (T (C (T (T h10 h3) (C (T (h y y v2) (C (C (T (T (C (T (C (T h11 (C (C (C (T h10 h3) h4) h4) h1)) h5) (S (h z v2 y))) h5) (C (h z y z) h5)) (S (h y v2 z))) h4) h4)) h1)) h4) (S (h z y y))) h9) h8) h4) h3) h1)) (R v0))

