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
theorem Equation1504_implies_Equation2180 (G: Type _) [Magma G] (h: Equation1504 G) : Equation2180 G := fun x y z =>
  let v0 := M x z
  let v1 := M y z
  let v2 := M v1 y
  let v3 := M v2 v0
  have h4 := h z y v2
  have h5 := h y v1 y
  have h6 := R v1
  let v7 := M y x
  T (T (h x y y) (C (T (h v7 x x) (C (T (T (h (M x v7) v1 x) (C (T (T (S (h z y x)) h4) (C h6 (S h5))) (R (M x (M v1 x))))) (S (h y v1 x))) (T (T (h (M x (M x x)) v0 x) (C (T (T (S (h z x x)) (h z x v2)) (C (R v0) (C (R v2) (C (R x) (T (C h6 h5) (S h4)))))) (R (M x (M v0 x))))) (S (h v3 v0 x))))) (R (M y (M y y))))) (S (h v3 y y))

@[equational_result]
theorem Equation2196_implies_Equation3567 (G: Type _) [Magma G] (h: Equation2196 G) : Equation3567 G := fun x y z =>
  let v0 := M z x
  let v1 := M v0 z
  let v2 := M y v1
  let v3 := M x y
  have h4 := h x y y
  let v5 := M (M y y) y
  let v6 := M (M x v0) v0
  let v7 := M (M v3 v1) v1
  T (T (T (T (T (C (h x y v3) (h y v3 v1)) (S (h v7 (M y v3) v3))) (h v7 x v0)) (C (R v6) (T (C (R v7) h4) (S (h v5 v3 v1))))) (C (T (h v6 v0 z) (C (R (M v1 z)) (S (h z x v0)))) (T (T (h v5 v3 x) (C (R (M (M v3 x) x)) (T (S h4) (h x y v1)))) (S (h (M v2 v1) v3 x))))) (S (h v2 v1 z))

@[equational_result]
theorem Equation3120_implies_Equation3211 (G: Type _) [Magma G] (h: Equation3120 G) : Equation3211 G := fun x y z =>
  let v0 := M y z
  let v1 := M v0 z
  let v2 := M v1 x
  let v3 := M v2 y
  have h4 := R v3
  have h5 := R v0
  have h6 := S (h v1 z v1)
  have h7 := R v1
  have h8 := C (C (C (T (h v0 v1 v1) (C (S (h z v0 v1)) h7)) (R z)) h7) h7
  have h9 := h v1 v1 v0
  T (T (h x v1 v3) (C (C (C (T (h v2 v3 v3) (C (S (h y v2 v3)) h4)) (T (T h9 (C (T (T (C (T (T (T h8 h6) h9) (C (C (T h8 h6) h5) h5)) h5) (S (h z v0 v0))) (h z y v0)) h5)) (S (h y v0 v0)))) h4) h4)) (S (h v3 y v3))

@[equational_result]
theorem Equation522_implies_Equation492 (G: Type _) [Magma G] (h: Equation522 G) : Equation492 G := fun x y z =>
  let v0 := M z y
  let v1 := M z v0
  let v2 := M x v1
  let v3 := M y v2
  have h4 := R v3
  have h5 := S (h v1 v1 z)
  have h6 := R v1
  have h7 := C h6 (C h6 (C (R z) (T (h v0 v1 v1) (C h6 (S (h z v1 v0))))))
  have h8 := R v0
  have h9 := h v1 v0 v1
  T (T (h x v3 v1) (C h4 (C h4 (C (T (T h9 (C h8 (T (T (C h8 (T (T (T h7 h5) h9) (C h8 (C h8 (T h7 h5))))) (S (h z v0 v0))) (h z v0 y)))) (S (h y v0 v0))) (T (h v2 v3 v3) (C h4 (S (h y v3 v2)))))))) (S (h v3 v3 y))

@[equational_result]
theorem Equation928_implies_Equation16 (G: Type _) [Magma G] (h: Equation928 G) : Equation16 G := fun x y =>
  let v0 := M y x
  let v1 := M y v0
  have h2 := h v0 v1 x
  have h3 := S h2
  have h4 := R v1
  let v5 := M v0 x
  have h6 := h v1 v1 (M (M v1 x) v5)
  have h7 := R v0
  let v8 := M x x
  have h9 := h x v0 x
  have h10 := R y
  T (T (h x y x) (C h10 (T (T (h (M v0 v8) y v0) (C h10 (T (T (C h4 (C (T (C h7 (C h9 h9)) (S (h v0 v0 (M v5 v8)))) h7)) (C h4 (C h2 h2))) (S h6)))) (C (h y y x) (T h6 (C h4 (C h3 h3))))))) (S (h v1 y (M v0 v0)))

@[equational_result]
theorem Equation2725_implies_Equation3692 (G: Type _) [Magma G] (h: Equation2725 G) : Equation3692 G := fun x y z =>
  let v0 := M z z
  let v1 := M y y
  have h2 := R v1
  let v3 := M x x
  let v4 := M v1 v0
  have h5 := h v1 v4 y
  have h6 := R v4
  have h7 := h v0 v1 y
  have h8 := S (h v0 v4 y)
  have h9 := h v0 v1 z
  have h10 := C (T (S (h v0 v1 x)) h9) h6
  have h11 := h v3 v4 y
  T (T (T (T (T h11 h10) h8) h7) (C (R (M v4 v1)) (T (T h5 (C (T (S h7) h9) h6)) h8))) (C (T (C (T (h v4 v3 y) (C (C (T (C (T (T (T h11 h10) h8) h7) h6) (S h5)) h2) (R v3))) h2) (S (h v1 v1 x))) (R v0))

@[equational_result]
theorem Equation684_implies_Equation2944 (G: Type _) [Magma G] (h: Equation684 G) : Equation2944 G := fun x y z =>
  let v0 := M y x
  let v1 := M y v0
  let v2 := M (M v1 z) z
  have h3 := S (h v2 v2 x)
  let v4 := M v2 (M (M v2 x) x)
  let v5 := M x v2
  have h6 := R x
  let v7 := M x (M (M x x) x)
  have h8 := h x x x
  T (T (T (T (T (h x y x) (C (R y) (T (C h6 (C (R v0) (T h8 (C h8 (R v7))))) (S (h v0 x v7))))) (h v1 x v2)) (R (M x (M v1 (M v5 v2))))) (C h6 (T (T (S (h v5 v1 z)) (h v5 v2 v4)) (C (R v2) (C (R v5) (T (C h3 (R v4)) h3)))))) (S (h v2 x v2))

@[equational_result]
theorem Equation952_implies_Equation3398 (G: Type _) [Magma G] (h: Equation952 G) : Equation3398 G := fun x y z =>
  let v0 := M x y
  let v1 := M x z
  let v2 := M z (M y v1)
  have h3 := h y x v2
  let v4 := M (M v2 y) (M v2 x)
  have h5 := R v0
  have h6 := h y y z
  let v7 := M z y
  let v8 := M v7 v7
  T (T (h v0 y v0) (C (R y) (C (T (T (T (T (h (M v0 v0) x y) (C (R x) (C (T (S (h y y x)) h6) (R (M y x))))) (S (h v8 x y))) (h v8 v0 y)) (C h5 (T (T (T (C (S h6) (C h3 h5)) (S (h v4 y x))) (h v4 z x)) (C (R z) (C (S h3) (R v1)))))) (R (M v0 y))))) (S (h v2 y v0))

@[equational_result]
theorem Equation1761_implies_Equation3794 (G: Type _) [Magma G] (h: Equation1761 G) : Equation3794 G := fun x y z =>
  let v0 := M z y
  let v1 := M (M z x) v0
  have h2 := R v1
  let v3 := M v1 z
  have h4 := h x v0 v1
  have h5 := h z x v0
  let v6 := M v0 v1
  have h7 := T (C (R v6) h5) (S h4)
  let v8 := M x y
  let v9 := M v8 z
  T (T (h v8 z v1) (C (R (M z v1)) (C (T (T (h v9 x v1) (C (R (M x v1)) (T (C (T (C (R v9) (T h4 (C (T (h v6 z y) (C (R v0) (C h7 (R y)))) (S h5)))) (S (h v0 v8 z))) h2) (C (T (h v0 v1 z) (C (R v3) h7)) h2)))) (S (h v3 x v1))) h2))) (S (h v1 z v1))

@[equational_result]
theorem Equation2789_implies_Equation2755 (G: Type _) [Magma G] (h: Equation2789 G) : Equation2755 G := fun x y z =>
  have h0 := R z
  let v1 := M z x
  have h2 := S (h y x v1)
  let v3 := M x y
  have h4 := h x (M (M x x) v3) x
  have h5 := R x
  have h6 := h y x x
  have h7 := T (C (C h6 h6) h5) (S h4)
  let v8 := M y y
  have h9 := h y x z
  have h10 := S h6
  T (T (T h4 (C (C h10 h10) h5)) (h (M v8 x) v8 z)) (C (T (T (T (C (T (C (C h9 h9) h0) (S (h z (M (M x z) v3) z))) (C (R v8) h7)) (C h0 h7)) (h v1 (M (M x v1) v3) v1)) (C (C h2 h2) (R v1))) h0)

@[equational_result]
theorem Equation3147_implies_Equation2474 (G: Type _) [Magma G] (h: Equation3147 G) : Equation2474 G := fun x y z =>
  let v0 := M y y
  have h1 := h z v0 z
  have h2 := R z
  have h3 := h v0 y z
  let v4 := M v0 z
  have h5 := h x v0 x
  have h6 := R x
  have h7 := h v0 y x
  have h8 := R v0
  have h9 := h v0 v0 v0
  have h10 := h v0 y v0
  T (h x x v4) (C (C (T (C (T (T (C (T (T h5 (C (T (T (S h7) h9) (C (S h10) h8)) h6)) (C (C (T h3 (C (C (T (C h10 h8) (S h9)) h2) (T h1 (C (S h3) h2)))) h8) h6)) h6) (S (h v0 v4 x))) h7) h6) (S h5)) (R v4)) (T (C h3 h2) (S h1)))

@[equational_result]
theorem Equation3398_implies_Equation4620 (G: Type _) [Magma G] (h: Equation3398 G) : Equation4620 G := fun x y z =>
  let v0 := M x x
  let v1 := M z y
  have h2 := R v1
  have h3 := R y
  have h4 := R v0
  have h5 := h v0 y v0
  have h6 := h x x x
  have h7 := h x x v0
  T (T (T (T h5 (C h4 (C h3 (T (C h4 h6) (S h7))))) (C h4 (T (h y v0 v0) (C h4 (T (C h4 (C h3 (T h7 (C h4 (S h6))))) (S h5)))))) (C h4 (T (T (C h4 (T (h v0 y v1) (C h2 (S (h z v0 y))))) (S (h z v1 v0))) (C (R z) (T (h z y v1) (C h2 (T (C h3 (T (h z v1 x) (C (R x) (T (C h2 (h z x y)) (S (h x y v1)))))) (S (h x x y))))))))) (S (h v1 z v0))

@[equational_result]
theorem Equation3791_implies_Equation4007 (G: Type _) [Magma G] (h: Equation3791 G) : Equation4007 G := fun x y z =>
  let v0 := M x y
  let v1 := M y x
  let v2 := M z v1
  let v3 := M x x
  have h4 := h y x x
  let v5 := M v1 x
  let v6 := M y v1
  T (T (T (T (T (T (T (T (T (T (h x y v1) (h v5 v6 v0)) (C (S (h y v1 x)) (S (h v1 x y)))) (h v6 v5 (M v1 v1))) (C (S (h v1 y v1)) (S (h x v1 v1)))) (S (h y x v1))) h4) (h v0 v3 z)) (C (h z v0 v2) (T (T (h v3 z v1) (C (T (T (C h4 (h x x y)) (S (h v3 v1 v0))) (S (h x y x))) (R v2))) (h v0 v2 z)))) (S (h (M v0 v2) (M z v0) (M v2 z)))) (S (h v2 z v0))

@[equational_result]
theorem Equation4176_implies_Equation4512 (G: Type _) [Magma G] (h: Equation4176 G) : Equation4512 G := fun x y z =>
  let v0 := M y z
  let v1 := M x y
  have h2 := h z v0 x
  have h3 := R x
  have h4 := h x y z
  let v5 := M y v1
  have h6 := R y
  let v7 := M v0 y
  T (T (T (T (h x v0 y) (C (T (T (h v7 x y) (C (C (T (h x y y) (C (T (C (T (h y y y) (C (T (T (T (C (h y y z) h6) (S (h z v0 y))) h2) (C (S h4) h3)) h6)) h3) (S (h y v1 x))) h6)) (R v7)) h6)) (S (h v7 v5 y))) h6)) (S (h v5 v0 y))) (C (T (h y v1 v1) (C (T (T (S (h v1 x y)) (C h4 h3)) (S h2)) (R v1))) (R v0))) (S (h v1 z v0))

@[equational_result]
theorem Equation4524_implies_Equation4365 (G: Type _) [Magma G] (h: Equation4524 G) : Equation4365 G := fun x y z w =>
  let v0 := M z w
  let v1 := M y x
  have h2 := R y
  let v3 := M v1 z
  have h4 := R v1
  have h5 := h y v1 z
  have h6 := h x y z
  T (T (T (T (T (T (T (T (T (T h6 (S (h x y v3))) (C (R x) (T (T (T (T h5 (C (S h6) h4)) (h (M x (M y z)) y x)) (C (T (T (C h2 h6) (h y v1 y)) (S h5)) h2)) (S (h v3 y x))))) (h x v3 v1)) (h (M v3 x) v1 z)) (C (T (h v1 v3 x) (S (h v1 v3 y))) h4)) (S (h (M v3 y) v1 z))) (S (h y v3 v1))) (C h2 (S (h z v1 v0)))) (h y z (M v1 v0))) (S (h y z w))

@[equational_result]
theorem Equation684_implies_Equation3370 (G: Type _) [Magma G] (h: Equation684 G) : Equation3370 G := fun x y z =>
  let v0 := M z x
  let v1 := M z v0
  let v2 := M y v1
  have h3 := S (h v2 v2 x)
  let v4 := M v2 (M (M v2 x) x)
  let v5 := M v1 v2
  have h6 := S (h v1 v1 x)
  let v7 := M v1 (M (M v1 x) x)
  let v8 := M x (M (M x x) x)
  have h9 := h x x x
  T (C (T (h x z x) (C (R z) (T (C (R x) (C (R v0) (T h9 (C h9 (R v8))))) (S (h v0 x v8))))) (T (T (T (h y v1 v7) (C (R v1) (C (R y) (T (C h6 (R v7)) h6)))) (h v5 v2 v4)) (C (R v2) (C (R v5) (T (C h3 (R v4)) h3))))) (S (h v2 v1 v2))

@[equational_result]
theorem Equation1182_implies_Equation2 (G: Type _) [Magma G] (h: Equation1182 G) : Equation2 G := fun x y =>
  have h0 := R y
  let v1 := M y y
  have h2 := R x
  let v3 := M (M y (M y v1)) y
  let v4 := M (M x (M x y)) x
  let v5 := M (M x (M x v4)) x
  let v6 := M y x
  let v7 := M (M x (M x v6)) x
  T (T (T (T (T (T (T (T (h x x y) (C h2 (C (C h0 (h v6 y x)) h0))) (S (h v7 x y))) (h v7 x x)) (C h2 (C (T (T (T (T (T (C h2 (S (h v6 x x))) (C h2 (C (T (h y x x) (C h2 (h v4 x x))) h2))) (S (h v5 x x))) (h v5 x y)) (C h2 (C (T (C h0 (S (h v4 y x))) (S (h y y x))) h0))) (C h2 (h v1 x y))) h2))) (S (h v3 x x))) (h v3 x y)) (C h2 (C (C h0 (S (h v1 y y))) h0))) (S (h y x y))

@[equational_result]
theorem Equation1507_implies_Equation4013 (G: Type _) [Magma G] (h: Equation1507 G) : Equation4013 G := fun x y z =>
  let v0 := M y z
  let v1 := M z v0
  let v2 := M v1 x
  let v3 := M x y
  have h4 := R (M x (M x v3))
  have h5 := h y x v3
  let v6 := M v3 x
  let v7 := M v3 v6
  let v8 := M v0 (M v0 v3)
  T (T (T (T (C (h x v3 v0) h5) (S (h v8 v6 v3))) (h v8 y v2)) (C (T (T (T (T (T (C h5 (R v8)) (S (h v7 v3 v0))) (h v7 v3 x)) (C (S h5) h4)) (C (h y x v1) h4)) (S (h (M v1 v2) v3 x))) (T (h (M v2 (M v2 y)) v0 z) (C (S (h z y v2)) (R (M z v1)))))) (S (h v2 v1 z))

@[equational_result]
theorem Equation2196_implies_Equation572 (G: Type _) [Magma G] (h: Equation2196 G) : Equation572 G := fun x y z =>
  let v0 := M x y
  let v1 := M z v0
  let v2 := M z v1
  let v3 := M y v2
  let v4 := M (M v3 v2) v2
  let v5 := M (M v2 y) y
  have h6 := R (M (M y x) x)
  let v7 := M v0 v2
  T (T (T (T (T (h x y x) (C h6 (T (T (h v0 v2 y) (C (T (T (h v5 (M v1 v2) v2) (C (S (h z v1 v2)) (S (h v1 v2 y)))) (C (h z v0 v2) (R v1))) (h v7 v2 y))) (S (h v5 (M v7 v2) v1))))) (C h6 (T (h v5 v3 v2) (C (R v4) (S (h y v2 y)))))) (S (h v4 y x))) (h v4 (M v2 v3) v3)) (C (S (h y v2 v3)) (S (h v2 v3 v2)))

@[equational_result]
theorem Equation2958_implies_Equation4162 (G: Type _) [Magma G] (h: Equation2958 G) : Equation4162 G := fun x y z =>
  let v0 := M y x
  let v1 := M (M x (M x v0)) v0
  let v2 := M v0 z
  have h3 := R v0
  have h4 := h v0 x v0
  have h5 := R v1
  have h6 := R y
  let v7 := M v0 y
  have h8 := S h4
  have h9 := S (h y x y)
  let v10 := M (M x (M x y)) y
  T (T (T (C (T (T (T (h x v10 y) (C (C (T (C (R v10) h9) h9) (R x)) h6)) (h v7 v1 v0)) (C (C (T (C h5 h8) h8) (R v7)) h3)) h6) (S (h v0 v0 y))) (h v0 v0 z)) (C (T (C (C (T h4 (C h5 h4)) (R v2)) h3) (S (h v2 v1 v0))) (R z))

@[equational_result]
theorem Equation3804_implies_Equation4197 (G: Type _) [Magma G] (h: Equation3804 G) : Equation4197 G := fun x y z =>
  let v0 := M z x
  let v1 := M v0 y
  let v2 := M x y
  let v3 := M v1 x
  let v4 := M x z
  have h5 := h x y x
  have h6 := h z x x
  have h7 := h v2 v0 (M x x)
  have h8 := h z y x
  T (T (T (T (h x y v1) (C (h v1 y x) (T (T (T (h x v1 v2) (C (R (M v2 v1)) (h x v2 y))) (S (h (M y v2) v1 v2))) (S (h v0 v2 y))))) (C (R (M v2 v3)) (T (T (T (T (T (C h6 h5) (S h7)) (S h8)) (h z y z)) (C (T (T h8 h7) (C (S h6) (S h5))) (h z z x))) (S (h v4 v2 v0))))) (S (h v4 v3 v2))) (S (h v1 z x))

@[equational_result]
theorem Equation3953_implies_Equation41 (G: Type _) [Magma G] (h: Equation3953 G) : Equation41 G := fun x y z =>
  let v0 := M z (M y y)
  have h1 := h y z v0
  have h2 := S h1
  let v3 := M y z
  have h4 := R v3
  let v5 := M x x
  let v6 := M v0 v0
  have h7 := h x x v5
  let v8 := M x v5
  T (T (T (T (T (T (T (T (T (h x x v3) (C (h x v5 v5) h4)) (S (h x (M v5 v5) v3))) (C (R x) (T (T (T (C h7 (R v5)) (S (h x v8 v5))) (h x v8 v6)) (C (S h7) (R v6))))) (h x (M v5 v6) v6)) (C (S (h v0 v5 v5)) h2)) (C (S (h y z v5)) h4)) (C (T (h y z v3) (C (R v0) h1)) h4)) (S (h v0 v0 v3))) h2

@[equational_result]
theorem Equation4453_implies_Equation4680 (G: Type _) [Magma G] (h: Equation4453 G) : Equation4680 G := fun x y z w =>
  have h0 := h z w y
  let v1 := M w z
  let v2 := M y v1
  have h3 := h v1 z y
  have h4 := R v1
  let v5 := M y z
  have h6 := R z
  T (T (T (T (T (T (T (T (T (T (S (h y z x)) (h y z (M w v1))) (C (S (h v1 y w)) h6)) (S (h v2 z v1))) (S (h v1 (M z v2) y))) (C h4 (T (S (h v2 v1 z)) (h v2 v1 w)))) (h v1 (M w v2) y)) (h v2 w v5)) (C (T (T (T (T (S (h z v2 y)) (C h6 (T (T (S h3) (h v1 z z)) (C h0 h6)))) (h z (M v5 w) w)) (C h4 (S h0))) h3) (R w))) (S (h z w v2))) h0

@[equational_result]
theorem Equation522_implies_Equation2373 (G: Type _) [Magma G] (h: Equation522 G) : Equation2373 G := fun x y z =>
  let v0 := M x z
  let v1 := M z v0
  let v2 := M y v1
  have h3 := R v2
  have h4 := h x v1 z
  have h5 := R v1
  let v6 := M v2 y
  have h7 := S (h v1 v6 z)
  have h8 := R v6
  have h9 := C h8 (C h8 (C (R z) (T (h v0 v1 v1) (C h5 (S (h z v1 v0))))))
  have h10 := h x v6 z
  T (T (T (T h10 h9) h7) (h v1 v2 x)) (C h3 (T (T (C h3 (T (C (T (T h10 h9) h7) (C h5 h4)) (S (h v1 v1 v1)))) (C h3 (T (h v1 v2 v1) (C h3 (T (C h3 (S h4)) (C h3 (h x y z))))))) (S (h y v2 v2))))

@[equational_result]
theorem Equation2196_implies_Equation2944 (G: Type _) [Magma G] (h: Equation2196 G) : Equation2944 G := fun x y z =>
  let v0 := M y x
  let v1 := M y v0
  let v2 := M v1 z
  let v3 := M v2 z
  let v4 := M (M v0 v2) v2
  have h5 := h y x v3
  let v6 := M (M x v3) v3
  let v7 := M v0 x
  have h8 := R (M v7 x)
  let v9 := M x y
  have h10 := R v7
  T (T (h x y x) (C h10 (T (T (T (T (h v9 y x) (C h10 (T (T (T (T (T (h (M v9 y) v0 x) (C h8 (S (h y x y)))) (C h8 h5)) (S (h v6 v0 x))) (h v6 v0 v2)) (C (R v4) (S h5))))) (S (h v4 y x))) (h v4 v1 z)) (C (R v3) (S (h y v0 v2)))))) (S (h v3 y x))

@[equational_result]
theorem Equation2714_implies_Equation3182 (G: Type _) [Magma G] (h: Equation2714 G) : Equation3182 G := fun x y z =>
  have h0 := R z
  let v1 := M y z
  let v2 := M v1 x
  let v3 := M v2 y
  let v4 := M x v3
  have h5 := h v2 x v3
  let v6 := M v3 z
  have h7 := S (h v3 x v6)
  let v8 := M v2 v2
  T (h x v6 z) (C (T (T (C (T (C (T (h v6 v2 v2) (C (C (T (h (M v2 v6) v3 z) (C (S (h y v2 v6)) h0)) (R v8)) (R v2))) (R x)) (S (h v8 v1 x))) (T (C (T (h v6 (M v4 (M x v6)) v6) (C (C h7 h7) (R v6))) h0) (S (h v3 v3 z)))) (C (C h5 h5) (R v3))) (S (h v3 (M (M x v2) v4) v3))) h0)

@[equational_result]
theorem Equation2958_implies_Equation14 (G: Type _) [Magma G] (h: Equation2958 G) : Equation14 G := fun x y =>
  let v0 := M x y
  let v1 := M y v0
  have h2 := R y
  let v3 := M v1 y
  have h4 := S (h v1 x v1)
  let v5 := M (M x (M x v1)) v1
  have h6 := R v0
  have h7 := S (h y x y)
  let v8 := M (M x v0) y
  let v9 := M (M x (M x x)) x
  have h10 := h x x x
  T (T (h x x y) (C (T (T (T (T (T (C (C (T h10 (C (R v9) h10)) h6) (R x)) (S (h v0 v9 x))) (h v0 v8 y)) (C (C (T (C (R v8) h7) h7) h6) h2)) (h v3 v5 v1)) (C (C (T (C (R v5) h4) h4) (R v3)) (R v1))) h2)) (S (h v1 v1 y))

@[equational_result]
theorem Equation3385_implies_Equation4362 (G: Type _) [Magma G] (h: Equation3385 G) : Equation4362 G := fun x y z =>
  let v0 := M y z
  let v1 := M v0 z
  have h2 := R v0
  have h3 := R y
  have h4 := R x
  have h5 := R v1
  let v6 := M v0 v0
  T (T (T (T (T (h x v0 v6) (C (R v6) (T (C h4 (T (C h2 (T (h v0 v0 y) (C h3 (T (C h2 (h v0 y z)) (S (h z v0 v0)))))) (S (h y z v0)))) (h x v0 v0)))) (S (h v0 x v6))) (h v0 x y)) (C h3 (T (C h2 (h x y z)) (S (h z x v0))))) (C h3 (T (T (T (h z x v1) (C h5 (S (h x v0 z)))) (C h5 (C h4 (T (h y z z) (C (R z) (T (C h3 (T (h z z v0) (C h2 (S (h z y z))))) (S (h v0 z y)))))))) (S (h x z v1))))

@[equational_result]
theorem Equation3404_implies_Equation4491 (G: Type _) [Magma G] (h: Equation3404 G) : Equation4491 G := fun x y z =>
  let v0 := M z x
  let v1 := M v0 z
  have h2 := h x v1 z
  have h3 := R v1
  have h4 := R y
  let v5 := M y y
  have h6 := R v5
  have h7 := R x
  let v8 := M x v5
  have h9 := h y y y
  T (T (T (T (C h7 (T (T (T (T (T h9 (C h4 (T (C h4 h9) (S (h v5 y y))))) (C h4 (h v5 y x))) (S (h v8 x y))) (h v8 x v5)) (C h6 (C h7 (T (C h6 (h x v5 z)) (S (h v0 z v5))))))) (S (h v1 v5 x))) (C h3 (T (T (h y y z) (C (R z) (T (C h4 (h z y v0)) (S (h v1 v0 y))))) (S h2)))) (C h3 h2)) (S (h v0 z v1))

@[equational_result]
theorem Equation3567_implies_Equation4013 (G: Type _) [Magma G] (h: Equation3567 G) : Equation4013 G := fun x y z =>
  let v0 := M y z
  let v1 := M z v0
  have h2 := R y
  have h3 := h z v0 z
  have h4 := R z
  have h5 := h z z y
  have h6 := R v0
  have h7 := h (M v0 y) v0 z
  have h8 := C (T (h y y v0) (C h2 (T (T h7 (C h6 (C (S h5) h4))) (S h3)))) h2
  have h9 := R x
  let v10 := M (M v0 x) v0
  T (T (T (T (T (T (T (T (T (h x y v0) (h y v10 y)) (C (R v10) h8)) (S (h v1 v10 y))) (S (h x v1 v0))) (C h9 (T (T h3 (C h6 (C h5 h4))) (S h7)))) (S (h y x v0))) (h y x y)) (C h9 h8)) (S (h v1 x y))

@[equational_result]
theorem Equation952_implies_Equation4673 (G: Type _) [Magma G] (h: Equation952 G) : Equation4673 G := fun x y z =>
  let v0 := M x y
  let v1 := M v0 z
  let v2 := M x z
  have h3 := S (h z z x)
  have h4 := h v1 z v0
  have h5 := h z v0 v2
  let v6 := M (M v2 z) (M v2 v0)
  have h7 := R v1
  let v8 := M v2 v2
  T (T h4 (C (R z) (T (h (M (M v0 v1) v1) v8 z) (C (T (h v8 v1 z) (C h7 (T (T (T (C h3 (C h5 h7)) (S (h v6 z v0))) (h v6 v2 v0)) (C (R v2) (T (C (S h5) (R (M v0 v2))) (S (h y z x))))))) (C (S h4) h3))))) (S (h (M v2 y) z v1))

@[equational_result]
theorem Equation2741_implies_Equation1865 (G: Type _) [Magma G] (h: Equation2741 G) : Equation1865 G := fun x y z =>
  let v0 := M z z
  let v1 := M y y
  let v2 := M x v1
  let v3 := M v2 v0
  have h4 := h v0 x v3
  have h5 := R v3
  let v6 := M x x
  have h7 := h v3 x v3
  let v8 := M v6 (M v3 v3)
  have h9 := h v1 x v3
  T (h x (M v2 v2) v1) (C (S (h v2 v2 v2)) (T (T (T (T (T h9 (C (T (T (h (M v6 (M v1 v3)) y v3) (C (C (R v1) (S h9)) h5)) (C (R (M v1 v1)) h7)) h5)) (S (h v8 v1 v3))) (h v8 v0 v3)) (C (T (T (C (R (M v0 v0)) (S h7)) (C (C (R v0) h4) h5)) (S (h (M v6 (M v0 v3)) z v3))) h5)) (S h4)))

@[equational_result]
theorem Equation2958_implies_Equation3567 (G: Type _) [Magma G] (h: Equation2958 G) : Equation3567 G := fun x y z =>
  let v0 := M (M z x) z
  let v1 := M (M x (M x x)) x
  have h2 := R x
  have h3 := h x x x
  let v4 := M (M x (M x z)) z
  have h5 := h z x z
  let v6 := M x y
  have h7 := R v6
  let v8 := M (M x (M x v6)) v6
  let v9 := M v6 v0
  have h10 := h v6 x v6
  T (h v6 v6 v0) (C (T (T (T (T (C (C (T h10 (C (R v8) h10)) (R v9)) h7) (S (h v9 v8 v6))) (C h7 (T (C (C (T h5 (C (R v4) h5)) h2) (R z)) (S (h x v4 z))))) (C (C (T h3 (C (R v1) h3)) (R y)) h2)) (S (h y v1 x))) (R v0))

@[equational_result]
theorem Equation2958_implies_Equation4182 (G: Type _) [Magma G] (h: Equation2958 G) : Equation4182 G := fun x y z =>
  let v0 := M y z
  let v1 := M v0 z
  let v2 := M v1 x
  let v3 := M (M x (M x y)) y
  have h4 := h y x y
  let v5 := M v2 v1
  have h6 := S (h v2 x v2)
  let v7 := M (M x (M x v2)) v2
  have h8 := S (h v1 x v1)
  let v9 := M (M x (M x v1)) v1
  T (C (T (T (T (h x v9 v1) (C (C (T (C (R v9) h8) h8) (R x)) (R v1))) (h v5 v7 v2)) (C (C (T (C (R v7) h6) h6) (R v5)) (R v2))) (T (h y y z) (C (T (C (C (T h4 (C (R v3) h4)) (R v0)) (R y)) (S (h v0 v3 y))) (R z)))) (S (h v2 v2 v1))

@[equational_result]
theorem Equation3120_implies_Equation1358 (G: Type _) [Magma G] (h: Equation3120 G) : Equation1358 G := fun x y z =>
  let v0 := M z x
  let v1 := M v0 z
  let v2 := M v1 y
  have h3 := R v2
  have h4 := h x z v1
  let v5 := M y v2
  have h6 := S (h v1 z v5)
  have h7 := R v5
  have h8 := R v1
  have h9 := C (C (C (T (h v0 v1 v1) (C (S (h z v0 v1)) h8)) (R z)) h7) h7
  have h10 := h x z v5
  T (T (T (T h10 h9) h6) (h v1 x v2)) (C (T (T (C (T (C (C h4 h8) (T (T h10 h9) h6)) (S (h v1 v1 v1))) h3) (C (T (h v1 v1 v2) (C (T (C (S h4) h3) (C (h x z y) h3)) h3)) h3)) (S (h y v2 v2))) h3)

@[equational_result]
theorem Equation3804_implies_Equation3617 (G: Type _) [Magma G] (h: Equation3804 G) : Equation3617 G := fun x y z =>
  let v0 := M z x
  let v1 := M v0 y
  have h2 := h z x z
  let v3 := M z z
  have h4 := h v0 v3 y
  let v5 := M v1 v1
  have h6 := R v5
  let v7 := M x y
  let v8 := M y y
  T (T (T (T (T (T (h x y y) (h v8 v7 v1)) (C (R (M v1 v7)) (T (h v8 v1 v1) (C h6 (S (h v0 y y)))))) (S (h v5 v7 v1))) (h v5 v7 v0)) (C (T (T (T (h v0 v7 y) (h (M y v7) v1 v7)) (C (R (M v7 v1)) (S (h x v7 y)))) (S (h x v1 v7))) (T (T (T (C h6 (T h2 h4)) (S (h (M y v3) v1 v1))) (S h4)) (S h2)))) (S (h z v1 x))

@[equational_result]
theorem Equation492_implies_Equation1374 (G: Type _) [Magma G] (h: Equation492 G) : Equation1374 G := fun x y z =>
  let v0 := M z y
  let v1 := M v0 z
  let v2 := M v1 x
  let v3 := M y v2
  have h4 := T (C (R v0) (h z y z)) (S (h y v0 z))
  have h5 := R v2
  have h6 := R v3
  have h7 := R v1
  have h8 := R x
  T (h x v1 v2) (C h4 (T (C h8 (C h5 (C h5 (T (h v1 v2 x) (C h5 (T (C h7 (C h8 (C h8 (T (h v2 x v1) (C h8 (T (C h5 (T (T (C h4 h5) (h v3 v1 v3)) (C h7 (C h6 (C h6 (T (C h6 (T (h v1 v2 y) (C h5 (C h4 (R (M y v3)))))) (S (h v2 v3 y)))))))) (S (h v1 v2 v3)))))))) (S (h x v1 x)))))))) (S (h v2 x v2))))

@[equational_result]
theorem Equation684_implies_Equation1293 (G: Type _) [Magma G] (h: Equation684 G) : Equation1293 G := fun x y z =>
  let v0 := M x y
  let v1 := M v0 z
  let v2 := M y (M (M y v1) v1)
  let v3 := M v1 z
  let v4 := M y v3
  have h5 := h y y v1
  have h6 := R v4
  have h7 := S (h y v0 z)
  have h8 := S (h v4 v4 x)
  let v9 := M v4 (M (M v4 x) x)
  have h10 := R y
  T (T (h x y v4) (C h10 (T (T (T (C (R x) (T (C (T (C h10 (h v4 v0 z)) (S (h v0 y v3))) h6) h7)) (h v0 v4 v9)) (C h6 (T (C (R v0) (T (C h8 (R v9)) h8)) h7))) (C h6 (T h5 (C h5 (R v2))))))) (S (h v4 y v2))

@[equational_result]
theorem Equation2522_implies_Equation2925 (G: Type _) [Magma G] (h: Equation2522 G) : Equation2925 G := fun x y z =>
  have h0 := R z
  let v1 := M x z
  let v2 := M y v1
  let v3 := M v2 y
  have h4 := h v3 x y
  have h5 := R x
  have h6 := R y
  have h7 := h x z v2
  let v8 := M z (M (M x v2) v2)
  have h9 := h x z x
  T h9 (C (T (T (h (M z (M (M x x) x)) x z) (C (T (T (T (C h5 (C (S h9) h0)) (h (M x v1) x x)) (C (C h5 (T (C (T (T (T (C (C h5 (C h7 h0)) h5) (S (h v8 x z))) (h v8 y z)) (C (C h6 (C (S h7) h0)) h6)) h5) (C h4 h5))) h5)) (S (h (M x (M (M v3 y) y)) x x))) h5)) (S h4)) h0)

@[equational_result]
theorem Equation2789_implies_Equation1740 (G: Type _) [Magma G] (h: Equation2789 G) : Equation1740 G := fun x y z =>
  let v0 := M z x
  let v1 := M v0 z
  have h2 := S (h y x v1)
  let v3 := M x y
  have h4 := R z
  have h5 := h z x v0
  have h6 := h x (M (M x x) v3) x
  have h7 := R x
  have h8 := h y x x
  have h9 := S h8
  T (T (T (T (T h6 (C (C h9 h9) h7)) (h (M (M y y) x) z z)) (C (T (T (C (R (M z z)) (C h4 (T (C (C h8 h8) h7) (S h6)))) (C (C h5 h5) (R v0))) (S (h v0 (M (M x v0) (M x z)) v0))) h4)) (h v1 (M (M x v1) v3) v1)) (C (C h2 h2) (R v1))

@[equational_result]
theorem Equation3735_implies_Equation3738 (G: Type _) [Magma G] (h: Equation3735 G) : Equation3738 G := fun x y z w =>
  let v0 := M y w
  let v1 := M x z
  let v2 := M v1 v0
  let v3 := M x y
  have h4 := R v2
  let v5 := M y x
  have h6 := S (h y x x)
  have h7 := h x y v2
  let v8 := M x v2
  have h9 := h x y z
  T (T (T (T (T (T h9 (h v1 v5 v0)) (C h4 (T (T (T (T (T (h v5 v1 x) (C (R (M v5 x)) (T (S h9) h7))) (S (h v5 v8 x))) (h v5 v8 v3)) (C h6 (S h7))) h6))) (h v2 v5 x)) (C (R (M v2 x)) (T (T (C (h y x w) h4) (S (h v0 v1 v3))) (h v0 v1 v1)))) (S (h v2 (M v0 v1) x))) (S (h v1 v0 v0))

@[equational_result]
theorem Equation3791_implies_Equation4200 (G: Type _) [Magma G] (h: Equation3791 G) : Equation4200 G := fun x y z =>
  let v0 := M z x
  let v1 := M v0 z
  let v2 := M v1 y
  let v3 := M y z
  have h4 := S (h v0 z x)
  let v5 := M x v0
  have h6 := h x v0 z
  have h7 := h z x v0
  T (T (T (T (h x y z) (h v0 v3 v2)) (C (T (T (T (T (T (C (R v2) (T (T h7 (h v1 v5 v0)) (C (S h6) h4))) (S (h y v5 v1))) (h y v5 v0)) (C (R (M v0 y)) (T (T (h v5 v0 v0) (C (T (T (C h7 h6) (S (h v5 v0 v1))) h4) (R (M v0 v0)))) (S (h z v0 v0))))) (S (h y z v0))) (h y z v1)) (R (M v3 v2)))) (S (h (M z v1) v3 v2))) (S (h v1 y z))

@[equational_result]
theorem Equation684_implies_Equation1561 (G: Type _) [Magma G] (h: Equation684 G) : Equation1561 G := fun x y z =>
  let v0 := M z y
  let v1 := M y z
  let v2 := M v1 (M x v0)
  have h3 := S (h v0 v0 v2)
  let v4 := M v0 (M (M v0 v2) v2)
  have h5 := S (h v1 v1 x)
  let v6 := M v1 (M (M v1 x) x)
  let v7 := M z v1
  have h8 := S (h z z x)
  let v9 := M z (M (M z x) x)
  have h10 := R z
  T (h x v0 v4) (C (T (C h10 (T (T (T (h y z v9) (C h10 (C (R y) (T (C h8 (R v9)) h8)))) (h v7 v1 v6)) (C (R v1) (C (R v7) (T (C h5 (R v6)) h5))))) (S (h v1 z v1))) (C (R x) (T (C h3 (R v4)) h3)))

@[equational_result]
theorem Equation949_implies_Equation2586 (G: Type _) [Magma G] (h: Equation949 G) : Equation2586 G := fun x y z =>
  let v0 := M z y
  have h1 := h z z v0
  let v2 := M v0 x
  let v3 := M y v2
  let v4 := M v3 z
  have h5 := h v3 v4 v3
  let v6 := M (M v3 v3) (M v4 v3)
  have h7 := R v3
  T (T (T (T (h x x v0) (C (R x) (C (h v2 v0 y) (R (M x v0))))) (S (h (M v3 (M v0 y)) x v0))) (C h7 (T (C (R v0) (T (h y v3 z) (C h5 (R (M v0 v4))))) (S (h v6 v0 v4))))) (C h7 (T (T (h v6 z v4) (C (R z) (T (C (S h5) (C h1 (R v4))) (S (h (M (M v0 z) (M z v0)) v3 z))))) (S h1)))

@[equational_result]
theorem Equation2105_implies_Equation31 (G: Type _) [Magma G] (h: Equation2105 G) : Equation31 G := fun x y =>
  let v0 := M y y
  let v1 := M v0 x
  let v2 := M v1 v1
  have h3 := R v2
  have h4 := R v0
  have h5 := R v1
  have h6 := S (h v0 y x)
  let v7 := M x x
  have h8 := R v7
  have h9 := R y
  have h10 := h y y y
  have h11 := C (S h10) h4
  have h12 := h y v0 y
  T (T (h x x v1) (C (T (h (M v7 x) v1 y) (C (C (T (T (T (C h5 (C (T (T (h v7 y x) (C (C (T (T (T (C h10 h8) (S (h y v0 x))) h12) h11) h9) h8)) h6) (R x))) (h v2 y x)) (C (C (T (T (T (C h10 h3) (S (h y v0 v1))) h12) h11) h9) h8)) h6) h5) h4)) h3)) (S (h v1 v0 v1))

@[equational_result]
theorem Equation2495_implies_Equation2 (G: Type _) [Magma G] (h: Equation2495 G) : Equation2 G := fun x y =>
  let v0 := M y (M (M y y) y)
  have h1 := R x
  let v2 := M (M v0 v0) v0
  have h3 := R v2
  let v4 := M (M x x) x
  have h5 := h x v4 v4
  let v6 := M v4 v4
  have h7 := h x v6 v2
  let v8 := M x v4
  let v9 := M (M v8 v8) v8
  have h10 := R v9
  T (T (h x (M x v2) y) (C (T (T (T (T (C (T (T (C h1 h3) (C h5 h3)) (S h7)) (R v4)) (h v8 x x)) (C (C h1 h10) h1)) (C (T (T (T (C h5 h10) (S (h x v6 v9))) h7) (C (S h5) h3)) h1)) (S (h v0 x x))) (R y))) (S (h y y y))

@[equational_result]
theorem Equation3159_implies_Equation1035 (G: Type _) [Magma G] (h: Equation3159 G) : Equation1035 G := fun x y =>
  have h0 := R x
  let v1 := M x x
  have h2 := h x x v1
  have h3 := S h2
  have h4 := h x v1 x
  have h5 := T h4 (C h3 h0)
  let v6 := M y v1
  have h7 := R y
  have h8 := R v6
  have h9 := T (C h2 h0) (S h4)
  have h10 := T (C (T (h y v6 v6) (C (C (C (T (C (T (h v6 x x) (C (T (C (C h9 h0) h8) (R (M v1 v6))) h8)) h8) (S (h v6 x v6))) h8) h7) h7)) h7) (S (h y v6 y))
  T h4 (C h3 (T (T (T (h x y y) (C (C (C h10 h7) h5) h0)) (C (C (R (M y y)) h9) h0)) (C (C h10 h5) h0)))

@[equational_result]
theorem Equation3804_implies_Equation3323 (G: Type _) [Magma G] (h: Equation3804 G) : Equation3323 G := fun x y z =>
  let v0 := M z z
  let v1 := M y v0
  let v2 := M x x
  have h3 := h y v0 v0
  have h4 := R v1
  have h5 := h z z z
  let v6 := M x v0
  have h7 := R v6
  have h8 := S h5
  let v9 := M x y
  T (T (T (T (h x y x) (h v9 v2 v1)) (C (R (M v1 v2)) (T (T (T (T (T (T (C (h x y y) (h y v0 y)) (S (h v1 v9 (M y y)))) (S (h x v0 y))) (h x v0 v0)) (C h8 h7)) (h v0 v6 v1)) (C (T (C (T h3 (C h8 h4)) h7) (S (h x v1 v0))) (T (C h5 h4) (S h3)))))) (S (h (M x v1) v2 v1))) (S (h x v1 x))

@[equational_result]
theorem Equation3804_implies_Equation3791 (G: Type _) [Magma G] (h: Equation3804 G) : Equation3791 G := fun x y z =>
  have h0 := h y x z
  have h1 := h y x y
  let v2 := M y y
  have h3 := R v2
  have h4 := S h0
  let v5 := M y z
  let v6 := M z x
  let v7 := M v6 v5
  let v8 := M x y
  have h9 := h x y y
  T (T (T (T (T (T (T (T h9 (h v2 v8 v6)) (C (T (h v6 v8 v5) (C (T (T (T (T (h v5 v8 v2) (C (S h9) (S (h y z y)))) (h v8 v5 v6)) (C h4 (S (h z y x)))) (S (h z x y))) (R v7))) (R (M v2 v6)))) (S (h v2 v7 v6))) (C (h y y y) (T (T h4 h1) (C h0 h3)))) (S (h v7 v2 v2))) (C h4 h3)) (S h1)) h0

@[equational_result]
theorem Equation492_implies_Equation2958 (G: Type _) [Magma G] (h: Equation492 G) : Equation2958 G := fun x y z =>
  let v0 := M y z
  let v1 := M y v0
  have h2 := h y v0 y
  have h3 := R v1
  have h4 := h v0 v1 y
  have h5 := h z z y
  have h6 := R y
  have h7 := h y v1 z
  have h8 := R v0
  let v9 := M v1 x
  T (h x v9 v1) (C (R v9) (T (T (S (h v1 x v1)) (C h6 (T (h v0 z y) (C (R z) (T (T (T (T (C h8 (C h6 (T (h v0 v0 v1) (C h8 (C h8 (T (T (C h3 (T (C h3 (C h6 h5)) (S h7))) (C h3 h2)) (S h4))))))) (S (h y v0 v0))) h7) (C h3 (C h6 (S h5)))) (C h3 (T h4 (C h3 (S h2))))))))) (S (h z y v1))))

@[equational_result]
theorem Equation522_implies_Equation1304 (G: Type _) [Magma G] (h: Equation522 G) : Equation1304 G := fun x y z =>
  let v0 := M x z
  let v1 := M v0 z
  let v2 := M y (M v1 y)
  have h3 := S (h v1 v2 z)
  have h4 := R v1
  have h5 := h z v0 v0
  have h6 := h x v0 z
  have h7 := R v0
  have h8 := R v2
  have h9 := C h8 (C h8 (C (R z) (T (h v0 v1 x) (C h4 (T (T (C h4 (C (R x) (T (C h7 h6) (S h5)))) (C h4 (h v0 v1 z))) (S (h z v1 v1)))))))
  have h10 := h x v2 z
  T (T (T (T h10 h9) h3) (C h7 (T h5 (C h7 (T (T (T (T (S h6) h10) h9) h3) (h v1 v2 y)))))) (S (h v2 v0 v2))

@[equational_result]
theorem Equation1913_implies_Equation3973 (G: Type _) [Magma G] (h: Equation1913 G) : Equation3973 G := fun x y z =>
  let v0 := M z x
  let v1 := M y v0
  let v2 := M x y
  let v3 := M v2 v1
  let v4 := M v0 v2
  let v5 := M v1 z
  have h6 := h y z v1
  have h7 := R v5
  have h8 := R (M y v1)
  have h9 := h z y x
  have h10 := S h9
  have h11 := h x v1 y
  T (T (C (R x) (T h6 (C (T (C h9 h8) (S h11)) h7))) (C (T (h x v0 y) (C (R v4) (T (h v1 v1 v2) (C (C (R v1) h10) (R v3))))) (T (T (C (T h11 (C h10 h8)) h7) (S h6)) (h y v2 v0)))) (S (h v5 v4 v3))

@[equational_result]
theorem Equation2741_implies_Equation3692 (G: Type _) [Magma G] (h: Equation2741 G) : Equation3692 G := fun x y z =>
  let v0 := M z z
  have h1 := h (M (M y y) v0) v0 z
  have h2 := R z
  have h3 := h z y z
  have h4 := R (M v0 v0)
  have h5 := h z z z
  have h6 := S (h x x x)
  let v7 := M x x
  let v8 := M v7 v7
  have h9 := h v7 x z
  T (T (T (T h9 (C (T (h (M v7 (M v7 z)) x z) (C (T (T (C (R v7) (S h9)) (h v8 v7 x)) (C (T (C (R v8) h6) h6) (R x))) (T h3 (C (T h1 (C (T (C h4 (S h3)) (S h5)) h2)) h2)))) h2)) (S (h v0 x z))) (C (T h5 (C h4 h3)) h2)) (S h1)

@[equational_result]
theorem Equation3120_implies_Equation2399 (G: Type _) [Magma G] (h: Equation3120 G) : Equation2399 G := fun x y z =>
  let v0 := M z x
  let v1 := M z v0
  let v2 := M (M y v1) y
  have h3 := R v0
  have h4 := S (h v1 z v2)
  have h5 := R v2
  have h6 := R v1
  have h7 := h z v0 v0
  have h8 := h x z v0
  have h9 := C (C (C (T (h v0 x v1) (C (T (T (C (C (T (C h8 h3) (S h7)) (R x)) h6) (C (h v0 z v1) h6)) (S (h z v1 v1))) h6)) (R z)) h5) h5
  have h10 := h x z v2
  T (T (T (T h10 h9) h4) (C (T h7 (C (T (T (T (T (S h8) h10) h9) h4) (h v1 y v2)) h3)) h3)) (S (h v2 v2 v0))

@[equational_result]
theorem Equation3791_implies_Equation3823 (G: Type _) [Magma G] (h: Equation3791 G) : Equation3823 G := fun x y z =>
  let v0 := M x y
  let v1 := M y x
  let v2 := M z z
  have h3 := h x x y
  have h4 := h x y x
  let v5 := M x x
  have h6 := h y x x
  let v7 := M z x
  let v8 := M y z
  T (T (T (T (T (T (T (T (h x y z) (h v7 v8 v0)) (C (S (h y z x)) (S (h z x y)))) (h v8 v7 v2)) (C (S (h z y z)) (S (h x z z)))) (S (h y x z))) h6) (C (T (T h4 (h v5 v1 v1)) (C (T (T (C h6 h3) (S (h v5 v1 v0))) (S h4)) (T (T (T (h v1 v1 z) (C (h z v1 z) (h v1 z z))) (S (h (M v1 z) (M z v1) v2))) (S (h z z v1))))) h3)) (S (h v2 v1 v0))

@[equational_result]
theorem Equation4013_implies_Equation3553 (G: Type _) [Magma G] (h: Equation4013 G) : Equation3553 G := fun x y z =>
  let v0 := M x z
  let v1 := M v0 z
  let v2 := M x (M v1 x)
  let v3 := M y (M y y)
  have h4 := R v1
  let v5 := M y v1
  let v6 := M v5 (M y v5)
  let v7 := M x (M z x)
  let v8 := M z v1
  T (T (T (T (T (T (T (T (T (h x y v5) (h v6 x z)) (C (T (T (T (T (T (h z v0 z) (h v8 z z)) (C (C (R z) (h z z x)) (R v8))) (S (h v8 v7 z))) (S (h v7 v0 z))) (S (h v0 z x))) (R v6))) (h v1 v6 y)) (C (C (R y) (S (h y y v5))) h4)) (h v3 v1 v1)) (C (C h4 (h v1 v1 x)) (R v3))) (S (h v3 v2 v1))) (S (h v2 y y))) (S (h y v1 x))

@[equational_result]
theorem Equation895_implies_Equation2982 (G: Type _) [Magma G] (h: Equation895 G) : Equation2982 G := fun x y z =>
  let v0 := M z x
  let v1 := M y v0
  let v2 := M v1 z
  let v3 := M v2 y
  have h4 := S (h y v3 x)
  have h5 := R v3
  have h6 := h x v0 x
  have h7 := R x
  T (T (h x z v2) (C (R z) (C (T (T (T (C h7 (C (R v1) (T (h z x x) (C h7 (T (C (R v0) (C h6 h6)) (S (h v0 v0 (M (M x x) (M v0 x))))))))) (S (h y x v0))) (h y v3 v3)) (C h5 (T (C (T (C (R y) (T (h v3 v3 (M (M y x) (M v3 x))) (C h5 (C h4 h4)))) (S (h v2 y y))) (R (M v3 v3))) (S (h v2 v2 y))))) (R (M z v2))))) (S (h v3 z v2))

@[equational_result]
theorem Equation1506_implies_Equation72 (G: Type _) [Magma G] (h: Equation1506 G) : Equation72 G := fun x y =>
  let v0 := M x x
  let v1 := M y v0
  have h2 := R v1
  have h3 := h v0 y x
  have h4 := S h3
  have h5 := h x x x
  have h6 := S h5
  let v7 := M x v0
  have h8 := h v7 v0 x
  let v9 := M x v7
  have h10 := R (M x v9)
  have h11 := h v9 v1 x
  T (T (T (T (T h5 (C h3 (T h8 (C h6 h10)))) (S h11)) (h v9 x v1)) (C (T (C (R x) (T (T h11 (C h4 (T (C h5 h10) (S h8)))) h6)) (h v0 v0 y)) (T (C h2 h4) (C h2 (h v0 y y))))) (S (h (M y v1) (M v0 v0) v1))

@[equational_result]
theorem Equation2888_implies_Equation2685 (G: Type _) [Magma G] (h: Equation2888 G) : Equation2685 G := fun x y z =>
  let v0 := M z y
  let v1 := M x y
  let v2 := M v1 v0
  let v3 := M v2 z
  have h4 := h v3 v0 z
  have h5 := R z
  have h6 := R v0
  let v7 := M v0 z
  have h8 := R y
  have h9 := h v2 z v0
  have h10 := h v2 v2 v0
  have h11 := h x v0 z
  T (T h11 (C (T (T (T (C (T (T (T (T (h (M x v7) z y) (C (S h11) h8)) (h v1 z y)) (C (C h10 h5) h8)) (S (h (M (M v2 (M v2 v0)) v2) z y))) h6) (S h10)) h9) (C (T (T (T (h (M (M v2 (M z v0)) z) z y) (C (C (S h9) h5) h8)) (C h4 h8)) (S (h (M v3 v7) z y))) h6)) h5)) (S h4)

@[equational_result]
theorem Equation3804_implies_Equation3364 (G: Type _) [Magma G] (h: Equation3804 G) : Equation3364 G := fun x y z =>
  let v0 := M x z
  let v1 := M z v0
  let v2 := M x y
  let v3 := M x v1
  have h4 := h x y v1
  have h5 := R v3
  have h6 := h v1 y v0
  have h7 := h x v0 z
  have h8 := R (M v0 y)
  have h9 := h x y v0
  T (T (T (h x y y) (C (h y y x) (T (T (T h4 (C (T (T h6 (C h8 (S h7))) (S h9)) h5)) (h v2 v3 v3)) (C (T (C (T (T (h x v1 v0) (C (R (M v0 v1)) h7)) (S (h v1 v1 v0))) h5) (S (h x v1 v1))) (T (C (T (T h9 (C h8 h7)) (S h6)) h5) (S h4)))))) (S (h v3 (M y x) v2))) (S (h y v1 x))

@[equational_result]
theorem Equation3940_implies_Equation3334 (G: Type _) [Magma G] (h: Equation3940 G) : Equation3334 G := fun x y z =>
  let v0 := M z y
  let v1 := M z v0
  have h2 := R z
  let v3 := M z v1
  let v4 := M v1 v0
  let v5 := M v1 v1
  have h6 := h v1 v0 z
  T (T (T (T (T (T (h x y z) (C (h x v0 v1) h2)) (S (h (M x v4) v0 z))) (C (C (R x) (T (T h6 (h v5 z v3)) (C (T (T (C (T (T (T (C (C h2 (h z y z)) (R v1)) (S (h z z v1))) (h z z v5)) (C (C h2 (S h6)) (R v5))) (S (h z v0 z))) (S (h (M z v4) v1 v1))) (S (h z v0 v1))) (R v3)))) (R v0))) (h (M x (M v1 v3)) v0 z)) (C (S (h x v3 v1)) h2)) (S (h x v1 z))

@[equational_result]
theorem Equation4197_implies_Equation4673 (G: Type _) [Magma G] (h: Equation4197 G) : Equation4673 G := fun x y z =>
  have h0 := R y
  let v1 := M x y
  let v2 := M x v1
  have h3 := R v2
  have h4 := R z
  have h5 := R v1
  let v6 := M v1 v1
  have h7 := R v6
  T (T (T (T (T (T (h v1 z v6) (C (C (T (C (T (h v1 v1 y) (C (T (C (h y v1 x) h5) (S (h v1 x v1))) h0)) h5) (S (h x y v1))) h4) h7)) (C (h v1 z v1) h7)) (S (h z v1 v6))) (h z v1 y)) (C (T (C (h y z x) h5) (S (h z x v1))) h0)) (C (T (T (T (h z x v2) (C (S (h v1 z x)) h3)) (C (C (T (h x y x) (C (T (C (T (h x x v1) (C (S (h y x x)) h5)) h0) (S (h x v1 y))) (R x))) h4) h3)) (S (h x z v2))) h0)

@[equational_result]
theorem Equation949_implies_Equation3607 (G: Type _) [Magma G] (h: Equation949 G) : Equation3607 G := fun x y z =>
  let v0 := M x y
  let v1 := M y z
  let v2 := M v1 x
  let v3 := M v1 v0
  have h4 := h y v1 v0
  let v5 := M (M v0 y) v3
  have h6 := R v1
  have h7 := h v0 z v2
  let v8 := M (M v2 v0) (M z v2)
  T h7 (C (R z) (T (T (h v8 v1 v0) (C h6 (T (R (M (M v0 v8) v3)) (C (T (T (T (T (C (R v0) (T (h v8 y z) (C h4 (C (S h7) h6)))) (S (h v5 v0 v1))) (h v5 x v1)) (C (R x) (C (T (S h4) (h y v1 x)) (R (M x v1))))) (S (h (M v0 v2) x v1))) (R v3))))) (S (h v2 v1 v0))))

@[equational_result]
theorem Equation3195_implies_Equation1358 (G: Type _) [Magma G] (h: Equation3195 G) : Equation1358 G := fun x y z =>
  let v0 := M z x
  let v1 := M v0 z
  let v2 := M v1 y
  have h3 := R v2
  have h4 := R v1
  have h5 := R z
  have h6 := R v0
  let v7 := M y v2
  have h8 := R v7
  let v9 := M y z
  T (h x v1 v2) (C (T (C (T (C (C (C (T (h v0 v1 v1) (C (T (C (T (T (C (C (T (h v1 v1 v7) (C (C (T (C (C (T (h v1 z v0) (C (C (T (C (C (T (h z v9 y) (C (S (h v9 y z)) (R y))) h6) h5) (S (h v0 y z))) h4) h6)) h8) h4) (S (h v7 v0 v1))) h4) h8)) h4) h4) (S (h v1 v7 v1))) (h v1 v0 z)) h6) (S (h z v1 v0))) h4)) h5) h3) h4) (S (h v2 z v1))) (R x)) (S (h y z x))) h3)

@[equational_result]
theorem Equation3603_implies_Equation41 (G: Type _) [Magma G] (h: Equation3603 G) : Equation41 G := fun x y z =>
  let v0 := M (M z z) y
  have h1 := h y z v0
  let v2 := M y z
  have h3 := R v2
  let v4 := M x x
  let v5 := M v0 v0
  have h6 := R v5
  have h7 := h x x v4
  let v8 := M v4 x
  have h9 := R v4
  T (T (T (T (T (T (T (T (T (T (T h7 (C h9 (h v4 x v4))) (S (h (M v4 v4) x v4))) (C (T (T (T (C h9 h7) (S (h v8 x v4))) (h v8 x v5)) (C h6 (S h7))) (R x))) (h (M v5 v4) x v5)) (C h6 (S (h v4 v0 v4)))) (S (h v0 x v5))) (h v0 x v2)) (C h3 (S (h y z v4)))) (C h3 (T (h y z v2) (C h1 (R v0))))) (S (h v0 v0 v2))) (S h1)

@[equational_result]
theorem Equation3195_implies_Equation2992 (G: Type _) [Magma G] (h: Equation3195 G) : Equation2992 G := fun x y z =>
  let v0 := M z y
  have h1 := R v0
  have h2 := R z
  let v3 := M y v0
  have h4 := R v3
  let v5 := M v3 x
  let v6 := M v5 z
  have h7 := R v6
  let v8 := M y v3
  T (h x v5 v3) (C (S (h v5 v3 x)) (T (C (T (h y v0 z) (C (T (T (S (h v0 z y)) (h v0 v3 z)) (C (C (T (C (C (T (h v3 v6 v3) (C (C (T (C (C (T (h v6 v0 v3) (C (C (T (C (C (T (h v0 y v3) (C (C (T (C (h v8 y v3) (R y)) (S (h v3 v8 y))) h1) h4)) h4) h1) (S (h v3 v3 v0))) h7) h4)) h4) h7) (S (h v3 v3 v6))) h4) h4)) h2) h4) (S (h z v3 v3))) h1) h2)) h2)) h1) (S (h z z v0))))

@[equational_result]
theorem Equation952_implies_Equation1996 (G: Type _) [Magma G] (h: Equation952 G) : Equation1996 G := fun x y z =>
  let v0 := M z z
  let v1 := M y x
  let v2 := M y v0
  let v3 := M v0 v0
  have h4 := R v0
  have h5 := h z z y
  have h6 := h z z z
  let v7 := M y z
  let v8 := M v7 v7
  have h9 := h x v0 y
  T (T h9 (C h4 (T (h (M v1 v2) v0 v0) (C (h v0 x y) (C (S h9) (T (T (h v3 v0 v0) (C h4 (C (T (T (C h4 (T (T (h v3 x z) (C (R x) (C (T (S h6) h5) (R (M z x))))) (S (h v8 x z)))) (C h4 (T (h v8 z z) (C h6 (C (S h5) h4))))) (S (h v3 v0 z))) (R v3)))) (S (h v0 v0 v0)))))))) (S (h (M v2 v1) v0 x))

@[equational_result]
theorem Equation2105_implies_Equation3286 (G: Type _) [Magma G] (h: Equation2105 G) : Equation3286 G := fun x y z =>
  let v0 := M z z
  let v1 := M y v0
  let v2 := M x x
  have h3 := R v2
  have h4 := h v2 x x
  have h5 := R x
  have h6 := h x x x
  have h7 := S h6
  have h8 := h x v2 x
  let v9 := M y y
  let v10 := M v1 v1
  T (T (T (T h4 (C (C (T (C h6 h3) (S h8)) h5) h3)) (C (C (T (h x v2 v1) (C h7 (R v10))) h5) h3)) (S (h v10 x x))) (C (T (C (T (h y y x) (C (C (T (T (T (h v9 x x) (C (C (T (C h6 (R v9)) (S (h x v2 y))) h5) h3)) (C (C (T h8 (C h7 h3)) h5) h3)) (S h4)) (R y)) h3)) (R v0)) (S (h y v2 z))) (R v1))

@[equational_result]
theorem Equation2789_implies_Equation4176 (G: Type _) [Magma G] (h: Equation2789 G) : Equation4176 G := fun x y z =>
  let v0 := M x y
  let v1 := M x x
  have h2 := h v0 (M (M x v0) v1) v0
  have h3 := R v0
  have h4 := h x x v0
  have h5 := T (C (C h4 h4) h3) (S h2)
  have h6 := R x
  have h7 := C h5 h6
  have h8 := h y x x
  have h9 := S h4
  have h10 := C (C h9 h9) h3
  T (T (T h2 h10) (h (M v1 v0) y z)) (C (C (R (M y z)) (T (C (T (T (T h8 h7) (h (M v0 x) x y)) (C (T (C h3 (T (T (C h6 (T (C (T h2 h10) h6) (S h8))) h2) h10)) (C h3 h5)) (T h8 h7))) h5) (S (h x v0 v0)))) (R z))

@[equational_result]
theorem Equation2958_implies_Equation1340 (G: Type _) [Magma G] (h: Equation2958 G) : Equation1340 G := fun x y z =>
  let v0 := M y z
  let v1 := M v0 z
  let v2 := M v1 x
  have h3 := R v2
  have h4 := S (h y x y)
  let v5 := M (M x (M x y)) y
  have h6 := S (h v1 x v1)
  let v7 := M (M x (M x v1)) v1
  let v8 := M y v2
  have h9 := S (h v2 v8 v2)
  let v10 := M (M v8 (M v8 v2)) v2
  T (h x v10 v2) (C (T (T (T (C (T (T (T (C (R v10) h9) h9) (h v2 v7 v1)) (C (C (T (C (R v7) h6) h6) h3) (R v1))) (R x)) (S (h v1 v1 x))) (C (T (h v0 v5 y) (C (C (T (C (R v5) h4) h4) (R v0)) (R y))) (R z))) (S (h y y z))) h3)

@[equational_result]
theorem Equation3404_implies_Equation3943 (G: Type _) [Magma G] (h: Equation3404 G) : Equation3943 G := fun x y z =>
  let v0 := M z z
  let v1 := M x v0
  have h2 := S (h z x z)
  have h3 := R v1
  have h4 := R z
  let v5 := M v1 y
  have h6 := R y
  have h7 := S (h z z z)
  T (T (T (T (h x y v1) (h v1 (M y (M v1 x)) z)) (C h4 (C (C h6 (T (T (T (T (T (T (T (T (T (h v1 x z) (C h4 (S (h v0 z x)))) (C h4 (T (h v0 z z) (C h4 h7)))) h7) (h z z y)) (C h6 (T (T (T (C h4 (h y z v1)) (S (h v5 v1 z))) (h v5 v1 v1)) (C h3 (S (h y v1 v1)))))) (S (h v1 v1 y))) (h v1 v1 z)) (C h4 (C h3 h2))) (S (h x v1 z)))) h2))) (S (h x (M y (M x v1)) z))) (S (h v1 y x))

@[equational_result]
theorem Equation2196_implies_Equation16 (G: Type _) [Magma G] (h: Equation2196 G) : Equation16 G := fun x y =>
  let v0 := M y x
  let v1 := M y v0
  have h2 := h y v0 v1
  have h3 := S h2
  let v4 := M v0 v1
  let v5 := M (M v1 y) y
  let v6 := M v4 v1
  have h7 := R (M (M v1 x) x)
  let v8 := M x y
  T (T (T (T (h x y v1) (C (R (M (M y v1) v1)) (T (T (T (T (h v8 y y) (C (R (M (M y y) y)) (T (h (M v8 y) v0 x) (C (T (T (T (h (M (M v0 x) x) v1 x) (C h7 (S (h y v0 x)))) (C h7 h2)) (S (h v6 v1 x))) (S (h y x y)))))) (S (h v6 y y))) (h v6 v1 y)) (C (R v5) h3)))) (S (h v5 y v1))) (h v5 v4 v1)) (C h3 (S (h v0 v1 y)))

