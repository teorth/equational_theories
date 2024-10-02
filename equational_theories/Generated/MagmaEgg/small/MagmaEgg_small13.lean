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
theorem Equation3804_implies_Equation4424 (G: Type _) [Magma G] (h: Equation3804 G) : Equation4424 G := fun x y z =>
  let v0 := M z z
  have h1 := h v0 y v0
  have h2 := h z z z
  let v3 := M v0 y
  have h4 := R v3
  let v5 := M x y
  let v6 := M v0 v5
  T (T (T (T (T (T (h x v5 v0) (h v6 (M x v0) v3)) (C (T (S (h x y v0)) (h x y x)) (T (C (R v6) (T h1 (C h4 (S h2)))) (S (h v3 v5 v0))))) (S (h v3 (M x x) v5))) (C h4 (T (T (T (h x x z) (h (M z x) (M x z) v0)) (C (S (h x z z)) (S (h z x z)))) (S (h z z x))))) (C h4 h2)) (S h1)

@[equational_result]
theorem Equation4095_implies_Equation4099 (G: Type _) [Magma G] (h: Equation4095 G) : Equation4099 G := fun x y z w =>
  have h0 := h y x x
  have h1 := S h0
  let v2 := M x x
  have h3 := C (R (M v2 x)) (R x)
  have h4 := h (M y y) x x
  have h5 := h x x x
  have h6 := T h5 h1
  have h7 := C h6 h6
  have h8 := R v2
  have h9 := S h5
  have h10 := T h0 h9
  T (h x v2 w) (C (T (T (T (C (C (T (T (T h5 h3) (S h4)) (C h10 h10)) h8) h8) (S (h x v2 v2))) (h x v2 z)) (C (T (T (T (T (C (T (T (T h7 h4) h3) h9) h8) h7) h4) h3) h1) (R z))) (R w))

@[equational_result]
theorem Equation627_implies_Equation2852 (G: Type _) [Magma G] (h: Equation627 G) : Equation2852 G := fun x y =>
  let v0 := M x y
  let v1 := M x v0
  let v2 := M y (M (M v1 x) x)
  have h3 := h x y v2
  have h4 := R v2
  have h5 := h y v1 x
  have h6 := R x
  have h7 := S (h v0 v1 v0)
  let v8 := M v0 (M (M v1 v0) v0)
  have h9 := T (T (C h6 (T (C h7 (R v8)) h7)) (C h6 (C h6 (T h5 (C h5 h4))))) (S h3)
  have h10 := S h5
  have h11 := h x v0 v8
  T h11 (C (T h11 (C (T h3 (C h6 (C h6 (T (C h10 h4) h10)))) h9)) h9)

@[equational_result]
theorem Equation1507_implies_Equation711 (G: Type _) [Magma G] (h: Equation1507 G) : Equation711 G := fun x y z =>
  let v0 := M x z
  let v1 := M v0 z
  let v2 := M y (M y v1)
  let v3 := M v2 (M v2 v0)
  let v4 := M x v0
  have h5 := h z x v2
  let v6 := M v2 (M v2 x)
  let v7 := M z x
  T (T (h x z y) (C (T (T (T (T (h v7 z x) (C (T (T (T (T (h (M z v7) v0 x) (C (T (S (h z x z)) h5) (R (M x v4)))) (S (h v6 v0 x))) (h v6 v0 v2)) (C (S h5) (R v3))) (R v4))) (S (h v3 z x))) (h v3 v1 y)) (C (S (h z v0 v2)) (R v2))) (R (M y (M y z))))) (S (h v2 z y))

@[equational_result]
theorem Equation2170_implies_Equation4162 (G: Type _) [Magma G] (h: Equation2170 G) : Equation4162 G := fun x y z =>
  let v0 := M x y
  let v1 := M y x
  let v2 := M v1 z
  let v3 := M v2 z
  have h4 := R (M v0 v2)
  have h5 := h z y x
  have h6 := R v0
  have h7 := S h5
  have h8 := h v2 x y
  have h9 := h v1 v0 v2
  T (T (T (h v0 v2 v0) (C (C h7 h6) h4)) (C (T (T (C (T (h z v1 z) (C (T (C h8 h5) (S h9)) (C (R z) (T h9 (C (S h8) h7))))) h6) (S (h (M z v3) y x))) (C h5 (R v3))) h4)) (S (h v3 v2 v0))

@[equational_result]
theorem Equation2519_implies_Equation3131 (G: Type _) [Magma G] (h: Equation2519 G) : Equation3131 G := fun x y z =>
  let v0 := M y x
  let v1 := M v0 z
  let v2 := M v1 z
  let v3 := M v2 y
  have h4 := R v1
  have h5 := R v3
  have h6 := R z
  have h7 := R v0
  have h8 := R v2
  T (T (h x v1 y) (C (T (T (C (C h7 (T (h z v2 v0) (C (C h8 (T (C (C h6 (h v0 z z)) h8) (S (h z z v2)))) h7))) (T (C (C (R x) (h y z x)) h4) (S (h z x v1)))) (S (h v2 v0 z))) (C h4 (T (h z v3 v1) (C (C h5 (T (C (C h6 (h v1 y z)) h5) (S (h y z v3)))) h4)))) (R y))) (S (h v3 v1 y))

@[equational_result]
theorem Equation2958_implies_Equation4216 (G: Type _) [Magma G] (h: Equation2958 G) : Equation4216 G := fun x y z =>
  have h0 := R x
  have h1 := R y
  have h2 := S (h z x z)
  let v3 := M (M x (M x z)) z
  let v4 := M (M x (M x x)) x
  have h5 := h x x x
  let v6 := M x y
  let v7 := M (M x (M x v6)) v6
  let v8 := M v6 x
  have h9 := h v6 x v6
  T (h v6 v6 x) (C (T (T (T (T (T (C (C (T h9 (C (R v7) h9)) (R v8)) (R v6)) (S (h v8 v7 v6))) (C (C (T h5 (C (R v4) h5)) h1) h0)) (S (h y v4 x))) (h y v3 z)) (C (C (T (C (R v3) h2) h2) h1) (R z))) h0)

@[equational_result]
theorem Equation962_implies_Equation1967 (G: Type _) [Magma G] (h: Equation962 G) : Equation1967 G := fun x y z =>
  let v0 := M z y
  let v1 := M z x
  let v2 := M y v1
  let v3 := M v2 v0
  let v4 := M v3 v0
  have h5 := S (h z v1 y)
  have h6 := R v0
  have h7 := R v2
  have h8 := R x
  T (T (h x x v0) (C h8 (C (R (M v0 x)) (T (T (T (C h8 (T (h v0 v1 y) (C (R v1) (C h7 (T (C h6 (T (h y v3 v1) (C (R v3) (C h5 h7)))) (S (h z v0 v2))))))) (S (h v2 x z))) (C (R y) (T (h v1 v0 v3) (C h6 (C (R v4) h5))))) (S (h v4 y z)))))) (S (h v3 x v0))

@[equational_result]
theorem Equation1507_implies_Equation3364 (G: Type _) [Magma G] (h: Equation1507 G) : Equation3364 G := fun x y z =>
  let v0 := M x z
  let v1 := M z v0
  let v2 := M y v1
  let v3 := M y (M y v2)
  have h4 := h v1 y v1
  let v5 := M v1 (M v1 y)
  let v6 := M x y
  T (T (T (T (h v6 x v2) (C (T (T (T (T (h (M x v6) v2 x) (C (T (S (h v1 y x)) h4) (R (M x (M x v2))))) (S (h v5 v2 x))) (h v5 v2 y)) (C (S h4) (R v3))) (T (h (M v2 (M v2 x)) v0 z) (C (S (h z x v2)) (R (M z v1)))))) (S (h v3 v1 z))) (h v3 (M v2 y) v2)) (C (S (h y v2 y)) (S (h v1 y v2)))

@[equational_result]
theorem Equation2180_implies_Equation1358 (G: Type _) [Magma G] (h: Equation2180 G) : Equation1358 G := fun x y z =>
  let v0 := M z x
  let v1 := M v0 z
  let v2 := M v1 y
  have h3 := C (S (h y y z)) (R v2)
  have h4 := h v1 (M y z) y
  have h5 := T h4 h3
  have h6 := R x
  let v7 := M x z
  T (T (T (T (h x z z) (C (R (M (M z z) z)) (T (h v7 z x) (C (R v1) (T (T (h (M v7 x) x v1) (C (C (C h6 h5) h6) (T (T (S (h v0 x z)) (h v0 v0 z)) (C (S (h z z x)) h5)))) (S (h z x (M y v2)))))))) (S (h v1 z z))) h4) h3

@[equational_result]
theorem Equation2180_implies_Equation1504 (G: Type _) [Magma G] (h: Equation2180 G) : Equation1504 G := fun x y z =>
  let v0 := M y z
  let v1 := M z v0
  have h2 := R x
  have h3 := T (h y v1 z) (C (S (h z z v0)) (R v0))
  let v4 := M y x
  let v5 := M x v4
  let v6 := M v5 x
  T (h x (M v4 v1) v4) (C (S (h v4 v4 v1)) (T (T (h v5 x x) (C (R (M (M x x) x)) (T (T (T (h v6 x y) (C (C (C h2 h3) h2) (T (T (C (R v6) (h y y x)) (S (h (M v4 y) x v4))) (C (R v4) h3)))) (S (h v4 x v1))) (C h3 h2)))) (S (h v1 x x))))

@[equational_result]
theorem Equation2956_implies_Equation4385 (G: Type _) [Magma G] (h: Equation2956 G) : Equation4385 G := fun x y =>
  have h0 := R x
  have h1 := S (h y x x)
  let v2 := M (M x (M x x)) y
  have h3 := C (C (T (C (R v2) h1) h1) h0) h0
  have h4 := h x v2 y
  let v5 := M y x
  let v6 := M (M v5 (M v5 v5)) v5
  have h7 := h v5 v5 v5
  let v8 := M (M v5 (M v5 x)) v5
  have h9 := h v5 v5 x
  T (T (T (T (C h0 (T (T (C (T h4 h3) h0) (C (C (T h9 (C (R v8) h9)) h0) h0)) (S (h x v8 v5)))) (C (T (T h4 h3) (C (T h7 (C (R v6) h7)) h0)) h0)) (S (h x v6 v5))) h4) h3

@[equational_result]
theorem Equation2958_implies_Equation1470 (G: Type _) [Magma G] (h: Equation2958 G) : Equation1470 G := fun x y z =>
  let v0 := M z (M z y)
  have h1 := R y
  let v2 := M v0 y
  have h3 := S (h v0 x v0)
  let v4 := M (M x (M x v0)) v0
  let v5 := M x y
  have h6 := R v5
  let v7 := M (M x (M x x)) x
  have h8 := h x x x
  T (T (h x x y) (C (T (C (C (T h8 (C (R v7) h8)) h6) (R x)) (S (h v5 v7 x))) h1)) (C h6 (T (T (h y z y) (C (T (h v2 v4 v0) (C (C (T (C (R v4) h3) h3) (R v2)) (R v0))) h1)) (S (h v0 v0 y))))

@[equational_result]
theorem Equation3404_implies_Equation4135 (G: Type _) [Magma G] (h: Equation3404 G) : Equation4135 G := fun x y z =>
  let v0 := M x y
  let v1 := M v0 z
  let v2 := M v1 z
  have h3 := R z
  let v4 := M v2 v0
  have h5 := R v1
  have h6 := h x y z
  have h7 := R v2
  let v8 := M y (M z x)
  have h9 := h v8 v2 z
  have h10 := h z v8 v1
  T (T (T h6 h10) (C h5 (T h9 (C h3 (T (C h7 (T h10 (C h5 (T (T (T (T h9 (C h3 (C h7 (S h6)))) (h z v4 v1)) (C h5 (T (T (h v4 v2 z) (C h3 (S (h v0 z v2)))) (h z v1 v1)))) (S (h v2 v1 v1)))))) (S (h v1 v1 v2))))))) (S (h v1 z v1))

@[equational_result]
theorem Equation3804_implies_Equation3414 (G: Type _) [Magma G] (h: Equation3804 G) : Equation3414 G := fun x y z =>
  let v0 := M x y
  let v1 := M z v0
  have h2 := S (h z v1 v1)
  let v3 := M z v1
  let v4 := M v1 v1
  let v5 := M v0 v0
  have h6 := h x y y
  T (T (T (T (T (T (T (T (T h6 (h (M y y) v0 v0)) (C (R v5) (S h6))) (h v5 v0 v1)) (C (R (M v1 v0)) (T (h v5 v1 v1) (C (R v4) (S (h z v0 v0)))))) (S (h v4 v0 v1))) (h v4 v0 v3)) (C (R (M v3 v0)) h2)) (C (T (T (T (h v3 v0 v1) (C (h v1 v0 z) (R (M v3 v1)))) (S (h v3 (M v1 z) v1))) (S (h v1 v1 z))) (R v3))) h2

@[equational_result]
theorem Equation684_implies_Equation3364 (G: Type _) [Magma G] (h: Equation684 G) : Equation3364 G := fun x y z =>
  let v0 := M z (M x z)
  let v1 := M y v0
  have h2 := S (h v1 v1 x)
  let v3 := M v1 (M (M v1 x) x)
  let v4 := M v0 v1
  have h5 := S (h v0 v0 x)
  let v6 := M v0 (M (M v0 x) x)
  have h7 := S (h z z x)
  let v8 := M z (M (M z x) x)
  T (C (T (h x z v8) (C (R z) (C (R x) (T (C h7 (R v8)) h7)))) (T (T (T (h y v0 v6) (C (R v0) (C (R y) (T (C h5 (R v6)) h5)))) (h v4 v1 v3)) (C (R v1) (C (R v4) (T (C h2 (R v3)) h2))))) (S (h v1 v0 v1))

@[equational_result]
theorem Equation1057_implies_Equation4 (G: Type _) [Magma G] (h: Equation1057 G) : Equation4 G := fun x y =>
  have h0 := h y x x
  have h1 := S h0
  have h2 := R x
  let v3 := M x y
  let v4 := M x v3
  have h5 := h x y v4
  have h6 := S h5
  have h7 := R v4
  have h8 := C h2 (C h0 h7)
  let v9 := M y v4
  have h10 := R v9
  T (T (T h5 (C h2 (C h1 h7))) (C h2 (C (R y) (T (h v4 x v9) (C h7 (T (T (C (T (T (C h2 (T (C h10 (C (T (h x v3 v9) (C h2 (C (S (h v3 y x)) h10))) (R v3))) (S (h v9 x v3)))) h8) h6) h10) h8) h6)))))) (C h2 h1)

@[equational_result]
theorem Equation1902_implies_Equation2725 (G: Type _) [Magma G] (h: Equation1902 G) : Equation2725 G := fun x y z =>
  let v0 := M y x
  let v1 := M z z
  let v2 := M v0 v1
  let v3 := M v2 y
  have h4 := R (M y y)
  have h5 := R (M x x)
  have h6 := R v1
  let v7 := M y v3
  let v8 := M x v0
  T (T (T (h x v0 y) (C (R (M v0 v8)) h4)) (C (C (R v0) (T (T (T (h v8 v1 x) (C (T (C h6 (S (h y x z))) (C h6 (h y v3 z))) h5)) (S (h (M v3 v7) v1 x))) (C (R v3) (T (T (h v7 v1 x) (C (C h6 (S (h v2 y z))) h5)) (S (h v0 v1 x)))))) h4)) (S (h v3 v0 y))

@[equational_result]
theorem Equation3573_implies_Equation3979 (G: Type _) [Magma G] (h: Equation3573 G) : Equation3979 G := fun x y z =>
  let v0 := M z z
  let v1 := M v0 v0
  let v2 := M v0 y
  have h3 := R v2
  have h4 := R x
  let v5 := M x x
  let v6 := M x y
  let v7 := M (M v6 v6) x
  T (T (T (T (T (T (T (h x y v6) (h y v7 z)) (h v7 v2 v5)) (C h3 (T (S (h x (M v5 v5) v6)) (S (h v5 x x))))) (S (h x v2 x))) (C h4 (T (h v0 y z) (h y v1 z)))) (C h4 (T (T (T (h v1 v2 z) (C h3 (S (h v0 v0 z)))) (h v2 v1 z)) (C (R v1) (S (h y v0 z)))))) (S (h (M y v0) x v0))

@[equational_result]
theorem Equation3791_implies_Equation4413 (G: Type _) [Magma G] (h: Equation3791 G) : Equation4413 G := fun x y z =>
  let v0 := M y z
  let v1 := M x y
  have h2 := h z x y
  have h3 := h v1 z x
  let v4 := M x v1
  let v5 := M z x
  have h6 := h x v1 z
  let v7 := M v0 v0
  have h8 := R v7
  T (T (T (T h6 (C (T (T (T (T h2 (h v0 v1 v5)) (C (S (h x y z)) (S (h y z x)))) (h v1 v0 v0)) (C (S h2) h8)) h3)) (S (h v7 v4 v5))) (C h8 (T (T (T h6 (h v5 (M v1 z) v4)) (C (S h3) (T (S (h z x v1)) h2))) (S (h z v0 v1))))) (S (h v0 z v0))

@[equational_result]
theorem Equation3804_implies_Equation3553 (G: Type _) [Magma G] (h: Equation3804 G) : Equation3553 G := fun x y z =>
  let v0 := M x z
  let v1 := M v0 z
  have h2 := h y v1 z
  let v3 := M x y
  let v4 := M y z
  let v5 := M z v1
  let v6 := M v3 v0
  have h7 := R v6
  T (T (T (T (T (T (h x y x) (h v3 (M x x) v0)) (C (S (h x z x)) h7)) (h v0 v6 (M y v1))) (C (T (C (T (T (T h2 (h v5 v4 v1)) (C (R (M v1 v4)) (S (h v0 v1 z)))) (S (h v0 v4 v1))) h7) (S (h v3 v4 v0))) (T (C (h x z y) h2) (S (h v5 v3 v4))))) (S (h v5 v4 v3))) (S h2)

@[equational_result]
theorem Equation3804_implies_Equation4216 (G: Type _) [Magma G] (h: Equation3804 G) : Equation4216 G := fun x y z =>
  let v0 := M z y
  let v1 := M v0 z
  let v2 := M x y
  have h3 := h z y z
  have h4 := h v0 z z
  have h5 := h v0 v1 (M z z)
  have h6 := h x y z
  T (T (T (h x y x) (C (T (T (T h6 (h v0 (M x z) v0)) (C (S h6) (R (M v0 v0)))) (C (R v2) (T (T (T (h v0 v0 v1) (C (T (C h4 h3) (S h5)) (T h5 (C (S h4) (S h3))))) (C (S (h v0 y z)) (R (M v1 v0)))) (S (h v1 y v0))))) (h x x y))) (S (h (M y x) (M v1 y) v2))) (S (h v1 x y))

@[equational_result]
theorem Equation1293_implies_Equation2925 (G: Type _) [Magma G] (h: Equation1293 G) : Equation2925 G := fun x y z =>
  let v0 := M x z
  let v1 := M y v0
  let v2 := M (M v1 y) z
  have h3 := R v2
  let v4 := M v2 z
  have h5 := h v1 v1 x
  have h6 := S h5
  let v7 := M (M (M v1 v1) x) x
  have h8 := R v7
  T (T (h x z v2) (C (R z) (C (C (T (T (h v0 v1 v2) (C (R v1) (C (C (T (T (T (C (R v0) (T h5 (C h5 h8))) (S (h y v0 v7))) (h y v4 v7)) (C (R v4) (T (C (T (C (S (h v1 y z)) h8) h6) h8) h6))) h3) h3))) (S (h v4 v1 v2))) h3) h3))) (S (h v2 z v2))

@[equational_result]
theorem Equation1507_implies_Equation4216 (G: Type _) [Magma G] (h: Equation1507 G) : Equation4216 G := fun x y z =>
  let v0 := M z y
  let v1 := M v0 z
  let v2 := M v1 x
  let v3 := M v1 v2
  let v4 := M x y
  let v5 := M x v4
  have h6 := R v5
  let v7 := M y v1
  T (T (T (h v4 x v1) (C (T (T (h v5 y x) (C (T (C (T (T (h y v2 x) (C (T (T (C (R v2) (h y z v0)) (S (h x v1 v0))) (h x v1 y)) (R (M x (M x v2))))) (S (h (M y v7) v2 x))) h6) (S (h v7 y x))) h6)) (S (h v1 y x))) (R v3))) (h (M v1 v3) (M v2 v1) v2)) (C (S (h v1 v2 v1)) (S (h x v1 v2)))

@[equational_result]
theorem Equation2958_implies_Equation711 (G: Type _) [Magma G] (h: Equation2958 G) : Equation711 G := fun x y z =>
  let v0 := M x z
  let v1 := M v0 z
  let v2 := M y v1
  let v3 := M y v2
  let v4 := M v3 v2
  have h5 := S (h v3 x v3)
  let v6 := M (M x (M x v3)) v3
  let v7 := M (M x (M x x)) x
  have h8 := h x x x
  T (T (T (T (h x x z) (C (T (C (C (T h8 (C (R v7) h8)) (R v0)) (R x)) (S (h v0 v7 x))) (R z))) (h v1 v3 v2)) (C (T (T (S (h v4 y v1)) (h v4 v6 v3)) (C (C (T (C (R v6) h5) h5) (R v4)) (R v3))) (R v2))) (S (h v3 v3 v2))

@[equational_result]
theorem Equation3404_implies_Equation4541 (G: Type _) [Magma G] (h: Equation3404 G) : Equation4541 G := fun x y z =>
  let v0 := M z x
  have h1 := R y
  let v2 := M y z
  let v3 := M x v2
  have h4 := R v2
  have h5 := R x
  let v6 := M v0 z
  T (T (T (h x v2 y) (C h1 (T (C h4 (T (h y x y) (C h1 (T (T (T (C h5 (T (T (T (h y y x) (C h5 (T (C h1 (h x y z)) (S (h v0 z y))))) (h x v6 z)) (C (R z) (T (h v6 v0 x) (C h5 (S (h z x v0))))))) (S (h v0 z x))) (h v0 z v2)) (C h4 (S (h x v2 z))))))) (S (h v3 y v2))))) (C h1 (T (h v3 y y) (C h1 (C h1 (S (h z x y))))))) (S (h v0 y y))

@[equational_result]
theorem Equation914_implies_Equation3286 (G: Type _) [Magma G] (h: Equation914 G) : Equation3286 G := fun x y z =>
  let v0 := M z z
  let v1 := M y v0
  have h2 := h y y v1
  have h3 := R y
  let v4 := M (M y y) (M v1 v1)
  let v5 := M x x
  have h6 := R v5
  have h7 := S (h x x x)
  let v8 := M v5 v5
  have h9 := h v5 y z
  T (T (T (T h9 (C h3 (T (T (h (M (M y v5) v0) y x) (C h3 (T (T (C (S h9) h6) (h v8 x v5)) (C (R x) (T (C h7 (R v8)) h7))))) (C h2 h6)))) (S (h v4 y x))) (h v4 y z)) (C h3 (C (S h2) (R v0)))

@[equational_result]
theorem Equation2146_implies_Equation1496 (G: Type _) [Magma G] (h: Equation2146 G) : Equation1496 G := fun x y z =>
  let v0 := M z z
  let v1 := M y v0
  let v2 := M y x
  let v3 := M v2 v1
  let v4 := M (M v3 v3) v0
  let v5 := M x x
  let v6 := M v5 v3
  T (T (h x y x) (C (T (T (h (M (M y y) x) x v2) (C (R (M v5 v2)) (T (T (S (h y y x)) (h y x v3)) (C (R v6) (T (C (h y z v0) (R v3)) (S (h v2 v0 v1))))))) (S (h v6 x v2))) (T (T (T (C (h x z v0) (h x v3 v0)) (S (h v4 v0 (M x v0)))) (h v4 v0 (M v3 v0))) (C (S (h v3 z v0)) (S (h v3 v3 v0)))))) (S (h v3 x v3))

@[equational_result]
theorem Equation2958_implies_Equation2170 (G: Type _) [Magma G] (h: Equation2958 G) : Equation2170 G := fun x y z =>
  have h0 := R y
  let v1 := M (M x (M x y)) y
  have h2 := h y x y
  let v3 := M y z
  let v4 := M (M x (M x v3)) v3
  let v5 := M v3 y
  have h6 := h v3 x v3
  let v7 := M v3 x
  have h8 := S (h v3 v7 v3)
  let v9 := M (M v7 (M v7 v3)) v3
  T (h x v9 v3) (C (C (T (C (R v9) h8) h8) (R x)) (T (h v3 v3 y) (C (T (T (T (C (C (T h6 (C (R v4) h6)) (R v5)) (R v3)) (S (h v5 v4 v3))) (C (C (T h2 (C (R v1) h2)) (R z)) h0)) (S (h z v1 y))) h0)))

@[equational_result]
theorem Equation3804_implies_Equation3810 (G: Type _) [Magma G] (h: Equation3804 G) : Equation3810 G := fun x y z =>
  let v0 := M x y
  let v1 := M z y
  let v2 := M v0 v1
  have h3 := R v2
  let v4 := M x x
  have h5 := h x y x
  have h6 := h z y x
  let v7 := M v0 v0
  have h8 := R v7
  T (T (T (T h5 (h v0 v4 v0)) (C (S h5) h8)) (h v0 v7 v1)) (C (T (T (C h6 h8) (S (h v0 (M z x) v0))) (S h6)) (T (T (T (T (C h5 (T (T (h z y y) (h (M y y) v1 v0)) (C h3 (S (h x y y))))) (S (h v2 v4 v0))) (C h3 (h x x y))) (S (h (M y x) v1 v0))) (S (h z x y))))

@[equational_result]
theorem Equation3804_implies_Equation4109 (G: Type _) [Magma G] (h: Equation3804 G) : Equation4109 G := fun x y z =>
  let v0 := M y z
  let v1 := M v0 z
  have h2 := h v1 z y
  let v3 := M z v0
  have h4 := h y z z
  let v5 := M z z
  T (T (T (T (T (T (h x x y) (C (h y x x) (h x y x))) (S (h (M x y) (M y x) (M x x)))) (S (h y y x))) (h y y z)) (C (R (M z y)) (T (T (T (T (T (T h4 (h v5 v0 z)) (C (R v3) (T (h v5 z v0) (C (R v1) (S h4))))) (h v3 (M v1 v0) v1)) (C (T (S (h v1 z v0)) h2) (S (h v0 v0 z)))) (S (h v0 (M v1 y) v0))) (S h2)))) (S (h v1 y z))

@[equational_result]
theorem Equation3973_implies_Equation4023 (G: Type _) [Magma G] (h: Equation3973 G) : Equation4023 G := fun x y z =>
  let v0 := M z x
  let v1 := M z v0
  let v2 := M v1 y
  let v3 := M z v1
  have h4 := R v2
  have h5 := R z
  have h6 := h z x v1
  let v7 := M x (M v1 z)
  T (T (T (T (h x y z) (h (M y v0) z v2)) (C (C h5 (C h4 (T (T (h y v0 v2) (C (C (T (T (T h6 (h v7 v1 v0)) (C (C (R v1) (T (h v0 v7 z) (C (S h6) h5))) (R v0))) (S (h z v1 v0))) (R (M v2 y))) h4)) (S (h y v3 v2))))) h4)) (S (h (M y v3) z v2))) (S (h v1 y z))

@[equational_result]
theorem Equation3159_implies_Equation3877 (G: Type _) [Magma G] (h: Equation3159 G) : Equation3877 G := fun x y =>
  have h0 := R x
  let v1 := M x x
  have h2 := h x x v1
  have h3 := h x v1 x
  let v4 := M y v1
  have h5 := R y
  have h6 := R v4
  have h7 := S h3
  have h8 := C h2 h0
  have h9 := T (C (T (h y v4 v4) (C (C (C (T (C (T (h v4 x x) (C (T (C (C (T h8 h7) h0) h6) (R (M v1 v4))) h6)) h6) (S (h v4 x v4))) h6) h5) h5)) h5) (S (h y v4 y))
  T (T (T (T h8 h7) (h x y y)) (C (C (C h9 h5) h0) h0)) (C (C h9 (T h3 (C (S h2) h0))) h0)

@[equational_result]
theorem Equation3404_implies_Equation4325 (G: Type _) [Magma G] (h: Equation3404 G) : Equation4325 G := fun x y z =>
  let v0 := M y x
  have h1 := R x
  have h2 := R y
  let v3 := M z z
  let v4 := M y v3
  have h5 := R v3
  let v6 := M v0 y
  T (T (T (T (T (C h1 (h y x v0)) (S (h v6 v0 x))) (h v6 v0 y)) (C h2 (S (h y y v0)))) (C h2 (T (T (T (h y y v3) (C h5 (T (C h2 (h v3 y y)) (S (h v4 y y))))) (C h5 (T (h v4 y x) (C h1 (S (h v3 x y)))))) (S (h x x v3))))) (C h2 (T (T (h x x x) (C h1 (T (T (T (C h1 (h x x y)) (S (h v0 y x))) (h v0 y z)) (C (R z) (S (h x z y)))))) (S (h z z x))))

@[equational_result]
theorem Equation4092_implies_Equation369 (G: Type _) [Magma G] (h: Equation4092 G) : Equation369 G := fun x y z =>
  have h0 := R z
  let v1 := M y y
  let v2 := M v1 z
  let v3 := M x x
  have h4 := R v2
  have h5 := R x
  have h6 := h x v1 v3
  have h7 := R v3
  have h8 := h v1 y x
  have h9 := h v1 y v3
  T (h x v2 z) (C (T (T (T (T (T (C (T (T (S (h z y v2)) (h z x x)) (C (T (T (T (T (C (T (T h6 (C (S h8) h7)) (S h9)) h0) (S (h v1 y z))) h9) (C h8 h7)) (S h6)) h5)) h5) (S (h x x x))) (h x v3 v2)) (C (S (h v3 x x)) h4)) (C (h v3 x y) h4)) (S (h y v3 v2))) h0)

@[equational_result]
theorem Equation1507_implies_Equation1983 (G: Type _) [Magma G] (h: Equation1507 G) : Equation1983 G := fun x y z =>
  let v0 := M z y
  let v1 := M y v0
  let v2 := M z x
  let v3 := M v1 v2
  let v4 := M v0 (M v0 z)
  let v5 := M v1 v3
  have h6 := h x z v0
  let v7 := M v2 (M v2 v2)
  T (T h6 (C (T (T (T (T (C (h z v2 v2) (h x z v2)) (S (h v7 (M v2 z) v2))) (h v7 x x)) (C (T (T (T (C h6 (R v7)) (S (h v4 v2 v2))) (h v4 v2 v1)) (C (S h6) (R v5))) (R (M x (M x x))))) (S (h v5 x x))) (T (h v4 v0 y) (C (S (h y z v0)) (R (M y v1)))))) (S (h v3 v1 y))

@[equational_result]
theorem Equation1507_implies_Equation2958 (G: Type _) [Magma G] (h: Equation1507 G) : Equation2958 G := fun x y z =>
  let v0 := M y z
  let v1 := M y v0
  let v2 := M v1 x
  let v3 := M z v1
  let v4 := M v2 (M v2 y)
  have h5 := h v1 z y
  have h6 := h v0 y v2
  let v7 := M v0 (M v0 v1)
  let v8 := M v1 (M v1 v1)
  T (h x v1 v1) (C (R v2) (T (T (T (T (h v8 v0 x) (C (T (T (T (C h6 (R v8)) (S (h v4 v1 v1))) (h v4 v1 v0)) (C (S h6) (R v7))) (R (M x (M x v0))))) (S (h v7 v0 x))) (C (R v0) (T (C h6 (T h5 (C (R v3) h5))) (S (h v4 v1 v3))))) (S (h z y v2))))

@[equational_result]
theorem Equation2170_implies_Equation1793 (G: Type _) [Magma G] (h: Equation2170 G) : Equation1793 G := fun x y z =>
  let v0 := M y z
  let v1 := M z y
  let v2 := M v1 x
  let v3 := M v0 v2
  have h4 := R v2
  have h5 := R v3
  have h6 := h x z y
  have h7 := S h6
  T (T (h x v3 v0) (C (T (T (T (C (R (M v3 v0)) h6) (S (h v0 v0 v2))) (h v0 v2 v1)) (C (C (T (C (T (h v2 v2 v0) (C (C h7 h4) h5)) (T (h v1 v0 v2) (C (S (h v2 y z)) h7))) (S (h v3 x v2))) (R v0)) (T (C (T (h v1 v2 v0) (C (C h7 (R v1)) h5)) h4) (S (h v3 x v1))))) (R (M v0 v3)))) (S (h v3 v3 v0))

@[equational_result]
theorem Equation684_implies_Equation1340 (G: Type _) [Magma G] (h: Equation684 G) : Equation1340 G := fun x y z =>
  let v0 := M (M y z) z
  let v1 := M v0 x
  have h2 := R v1
  let v3 := M v1 v0
  let v4 := M v0 (M v1 x)
  have h5 := h v0 v0 x
  have h6 := R v0
  let v7 := M x (M (M x x) x)
  have h8 := h x x x
  T (T (h x v0 x) (C h6 (T (C (R x) (C h2 (T h8 (C h8 (R v7))))) (S (h v1 x v7))))) (C (T (T (T (h v0 v1 v0) (C h2 (T (T (C h6 (C (R v3) (T h5 (C h5 (R v4))))) (S (h v3 v0 v4))) (h v3 y z)))) (R (M v1 (M y (M v3 v0))))) (S (h y v1 v0))) h2)

@[equational_result]
theorem Equation684_implies_Equation4013 (G: Type _) [Magma G] (h: Equation684 G) : Equation4013 G := fun x y z =>
  let v0 := M z (M y z)
  let v1 := M v0 x
  have h2 := S (h v1 v1 x)
  let v3 := M v1 (M (M v1 x) x)
  let v4 := M x v1
  have h5 := S (h x x x)
  let v6 := M x (M (M x x) x)
  have h7 := R x
  have h8 := S (h z z x)
  let v9 := M z (M (M z x) x)
  T (T (C h7 (T (h y z v9) (C (R z) (C (R y) (T (C h8 (R v9)) h8))))) (C h7 (T (T (T (h v0 x v6) (C h7 (C (R v0) (T (C h5 (R v6)) h5)))) (h v4 v1 v3)) (C (R v1) (C (R v4) (T (C h2 (R v3)) h2)))))) (S (h v1 x v1))

@[equational_result]
theorem Equation1537_implies_Equation11 (G: Type _) [Magma G] (h: Equation1537 G) : Equation11 G := fun x y =>
  let v0 := M y y
  let v1 := M x v0
  have h2 := S (h v0 x y)
  have h3 := h y y y
  have h4 := R v0
  have h5 := C h4 (S h3)
  have h6 := h y y v0
  let v7 := M v1 v1
  have h8 := R y
  let v9 := M x x
  have h10 := R v9
  T (T (T (h x y x) (C h4 (C (R x) (T (T (h v9 x y) (C h10 (C h8 (T (T (T (C h10 h3) (S (h y x v0))) h6) h5)))) h2)))) (C h4 (T (h v1 y v1) (C h4 (C (R v1) (T (T (h v7 x y) (C h10 (C h8 (T (T (T (C (R v7) h3) (S (h y v1 v0))) h6) h5)))) h2)))))) (S (h v1 y v0))

@[equational_result]
theorem Equation2196_implies_Equation3120 (G: Type _) [Magma G] (h: Equation2196 G) : Equation3120 G := fun x y z =>
  let v0 := M y x
  let v1 := M v0 y
  let v2 := M (M v1 z) z
  let v3 := M v1 y
  have h4 := h y x v2
  let v5 := M (M x v2) v2
  let v6 := M v0 x
  let v7 := M x y
  T (T (T (T (h x y v2) (C (R (M (M y v2) v2)) (T (T (h v7 y x) (C (R v6) (T (T (T (T (h (M v7 y) v0 x) (C (R (M v6 x)) (T (S (h y x y)) h4))) (S (h v5 v0 x))) (h v5 v0 y)) (C (R v3) (S h4))))) (S (h v3 y x))))) (S (h v1 y v2))) (C (h v0 y v1) (h y v1 z))) (S (h v2 (M y v1) v1))

@[equational_result]
theorem Equation2519_implies_Equation4007 (G: Type _) [Magma G] (h: Equation2519 G) : Equation4007 G := fun x y z =>
  let v0 := M y x
  let v1 := M (M z v0) z
  have h2 := R z
  have h3 := R v1
  let v4 := M x y
  have h5 := h v0 v4 z
  have h6 := R v4
  let v7 := M v0 v4
  T (T (T (T (h v4 x v7) (C (C (R x) (S (h y v4 x))) (R v7))) (h (M v4 v7) z z)) (C (C h2 (T (T (T (C (T (C (C h6 (C h5 h6)) h2) (S (h (M v4 (M (M v0 z) v4)) v4 z))) h2) (S h5)) (h v0 v1 z)) (C (C h3 (T (C (C (R v0) (h z z v0)) h3) (S (h z v0 v1)))) h2))) h2)) (S (h v1 z z))

@[equational_result]
theorem Equation3145_implies_Equation4611 (G: Type _) [Magma G] (h: Equation3145 G) : Equation4611 G := fun x y z =>
  have h0 := R y
  let v1 := M x x
  let v2 := M v1 y
  have h3 := R v1
  have h4 := h v2 x v2
  have h5 := R v2
  have h6 := h v1 x v2
  have h7 := h v2 v1 v1
  have h8 := S h7
  have h9 := C h6 h5
  T (T (T (C (T (T (T h6 (C (C (T (C (h v1 x v1) h3) (S (h v1 v1 v1))) h5) h3)) (C (T (T (T h9 h8) h4) (C (C (T h9 h8) h5) h5)) h3)) (C (T (C (C (T h7 (C (S h6) h5)) h5) h5) (S h4)) h3)) h0) (S (h y x v1))) (h y v2 z)) (C (C (S (h y x v2)) (R z)) h0)

@[equational_result]
theorem Equation3567_implies_Equation4026 (G: Type _) [Magma G] (h: Equation3567 G) : Equation4026 G := fun x y z =>
  let v0 := M z y
  let v1 := M z v0
  let v2 := M (M x v1) x
  let v3 := M (M x x) x
  have h4 := R v1
  have h5 := R v3
  let v6 := M (M x z) x
  let v7 := M v1 z
  T (T (T (T (T (T (T (T (T (h x y x) (h y v3 z)) (C h5 (T (T (T (T (T (h v0 z z) (h z v7 z)) (C (R v7) (C (h z z x) (R z)))) (S (h v6 v7 z))) (S (h v0 v6 z))) (S (h z v0 x))))) (h v3 v1 x)) (C h4 (C (S (h x x x)) (R x)))) (h v1 v3 v1)) (C h5 (C (h v1 v1 x) h4))) (S (h v2 v3 v1))) (S (h x v2 x))) (S (h v1 x x))

@[equational_result]
theorem Equation4176_implies_Equation3331 (G: Type _) [Magma G] (h: Equation4176 G) : Equation3331 G := fun x y z =>
  let v0 := M y z
  let v1 := M z v0
  let v2 := M x v1
  have h3 := R x
  have h4 := R z
  let v5 := M x y
  have h6 := R v1
  have h7 := h x y v2
  let v8 := M y v2
  T (T h7 (C (T (T (T (T (T (h v8 x v1) (C (T (T (h v2 v8 x) (C (T (S h7) (h x y z)) h3)) (S (h z v0 x))) h6)) (h v1 v1 x)) (C (T (C (h v1 x y) h6) (S (h y v5 v1))) h3)) (C (T (h y v5 z) (C (S (h z x y)) h4)) h3)) (C (T (C (h z x v1) h4) (S (h v1 v2 z))) h3)) (R v2))) (S (h x v1 v2))

@[equational_result]
theorem Equation3591_implies_Equation4023 (G: Type _) [Magma G] (h: Equation3591 G) : Equation4023 G := fun x y z =>
  let v0 := M z x
  let v1 := M z v0
  let v2 := M v1 y
  let v3 := M v1 x
  have h4 := R x
  have h5 := h z x v0
  have h6 := S h5
  have h7 := R v3
  let v8 := M x x
  T (T (T (T (h x y x) (h x (M v8 y) v2)) (C (R v2) (C (R (M x v2)) (T (T (h v8 y x) (C h4 (C (C (T (T (h x x v0) (C (R v0) (C (T (C h4 (T (T h5 (h v0 v3 v3)) (C h7 (T (C h6 h7) h6)))) (S (h v1 v0 x))) h4))) (S (h v1 x v0))) h4) (R y)))) (S (h v3 y x)))))) (S (h x (M v3 y) v2))) (S (h v1 y x))

@[equational_result]
theorem Equation4176_implies_Equation3414 (G: Type _) [Magma G] (h: Equation4176 G) : Equation3414 G := fun x y z =>
  let v0 := M x y
  let v1 := M z v0
  have h2 := R v1
  have h3 := R z
  let v4 := M z v1
  have h5 := R v4
  let v6 := M v0 v4
  have h7 := h x y z
  let v8 := M (M y z) x
  have h9 := h v4 v8 z
  have h10 := h v8 z v1
  T (T (T h7 h10) (C (T h9 (C (T (C (T h10 (C (T (T (T (T h9 (C (C (S h7) h5) h3)) (h v6 z v1)) (C (T (T (h v4 v6 z) (C (S (h z v0 v4)) h3)) (h v1 z v1)) h2)) (S (h v1 v4 v1))) h2)) h5) (S (h v1 v1 v4))) h3)) h2)) (S (h z v1 v1))

@[equational_result]
theorem Equation492_implies_Equation4421 (G: Type _) [Magma G] (h: Equation492 G) : Equation4421 G := fun x y z =>
  let v0 := M x (M x y)
  let v1 := M z y
  have h2 := R v0
  have h3 := h y v1 z
  have h4 := h z y z
  have h5 := R v1
  have h6 := T (C h5 h4) (S h3)
  have h7 := R z
  T (h v0 v1 z) (C h5 (T (C h2 (T (C h7 (C h7 (C h7 (T h3 (C h5 (S h4)))))) (C h7 (C h7 (T (T (C h7 h6) (h v1 z v0)) (C h7 (T (C h5 (C h2 (C h2 (T (h z v0 (M v1 z)) (C h2 (C h7 (T (C h6 (C h6 (T (h v0 v0 y) (C h2 (C h2 (S (h y y x))))))) (S (h y y v0))))))))) (S (h v0 v1 v0))))))))) (S (h z v0 z))))

@[equational_result]
theorem Equation2196_implies_Equation2482 (G: Type _) [Magma G] (h: Equation2196 G) : Equation2482 G := fun x y z =>
  let v0 := M y z
  let v1 := M v0 y
  let v2 := M x v1
  let v3 := M v2 z
  let v4 := M v3 z
  have h5 := h x v1 v3
  let v6 := M (M v1 v3) v3
  let v7 := M (M v2 v3) v3
  T (T (h x v1 y) (C (T (C (R (M v1 y)) (h y z v0)) (S (h (M (M z v0) v0) v0 y))) (T (T (T (T (C (h x v1 v2) (h v1 v2 v3)) (S (h v7 (M v1 v2) v2))) (h v7 x x)) (C (R (M (M x x) x)) (T (T (T (C (R v7) h5) (S (h v6 v2 v3))) (h v6 v2 z)) (C (R v4) (S h5))))) (S (h v4 x x))))) (S (h v3 z v0))

@[equational_result]
theorem Equation3940_implies_Equation3526 (G: Type _) [Magma G] (h: Equation3940 G) : Equation3526 G := fun x y z =>
  let v0 := M y z
  let v1 := M v0 z
  let v2 := M x v1
  let v3 := M v0 v1
  have h4 := R y
  let v5 := M y v1
  have h6 := R v5
  have h7 := h y z v0
  have h8 := S h7
  let v9 := M v0 y
  T (T (T (T (h x y v0) (h (M x v9) v0 v2)) (C (C (T (T (h x v9 y) (C (C (R x) (C h4 (T (C (T (T h7 (h v5 v0 v5)) (C (T (C h6 h8) h8) h6)) h4) (S (h v0 v1 y))))) h4)) (S (h x v3 y))) (R (M v2 v0))) (R v2))) (S (h (M x v3) v0 v2))) (S (h x v1 v0))

@[equational_result]
theorem Equation4092_implies_Equation4609 (G: Type _) [Magma G] (h: Equation4092 G) : Equation4609 G := fun x y z =>
  have h0 := R z
  let v1 := M y y
  let v2 := M v1 z
  have h3 := R x
  let v4 := M x x
  have h5 := h x v4 v4
  have h6 := R v4
  have h7 := h v4 x x
  have h8 := h v4 x v4
  have h9 := S h7
  T (T (T (T (C (T (h x v4 x) (C h9 h3)) (R y)) (S (h x v4 y))) (h x x z)) (C (T (C (T (T (T (T h5 (C h9 h6)) (S h8)) (h v4 x z)) (C (T (T h8 (C h7 h6)) (S h5)) h0)) h3) (S (h z x x))) h0)) (C (T (T (h z v1 v2) (C (T (S (h v1 y z)) (h v1 y y)) (R v2))) (S (h y v1 v2))) h0)

@[equational_result]
theorem Equation4176_implies_Equation4620 (G: Type _) [Magma G] (h: Equation4176 G) : Equation4620 G := fun x y z =>
  let v0 := M z y
  have h1 := S (h v0 z y)
  have h2 := R z
  let v3 := M y v0
  let v4 := M x x
  let v5 := M v4 y
  let v6 := M y v5
  T (T (T (T (h v4 y v5) (h (M v6 v4) v5 x)) (C (C (S (h y x x)) (T (T (T (T (h v6 v4 y) (C (T (T (T (h v5 v6 z) (C (S (h z y v5)) h2)) (C (h z y v0) h2)) (S (h v0 v3 z))) (R y))) (S (h v3 z y))) (C (T (h y v0 v0) (C h1 (R v0))) h2)) (S (h v0 v0 z)))) (R x))) (S (h (M v0 v0) y x))) h1

@[equational_result]
theorem Equation684_implies_Equation4413 (G: Type _) [Magma G] (h: Equation684 G) : Equation4413 G := fun x y z =>
  let v0 := M (M y z) z
  have h1 := S (h v0 v0 x)
  let v2 := M v0 (M (M v0 x) x)
  let v3 := M x v0
  have h4 := R x
  have h5 := S (h y y v0)
  let v6 := M y (M (M y v0) v0)
  let v7 := M x y
  T (T (T (T (T (C h4 (T (h v7 y v6) (C (R y) (C (R v7) (T (C h5 (R v6)) h5))))) (S (h y x y))) (h y x v0)) (R (M x (M y (M v3 v0))))) (C h4 (T (T (S (h v3 y z)) (h v3 v0 v2)) (C (R v0) (C (R v3) (T (C h1 (R v2)) h1)))))) (S (h v0 x v0))

@[equational_result]
theorem Equation1314_implies_Equation2 (G: Type _) [Magma G] (h: Equation1314 G) : Equation2 G := fun x y =>
  have h0 := R y
  let v1 := M (M (M x y) y) x
  have h2 := h x x x
  have h3 := S h2
  let v4 := M (M (M x x) x) x
  have h5 := R v4
  have h6 := T (C h3 h5) h3
  have h7 := R x
  have h8 := C h7 (T (C h6 (R v1)) (S (h y x x)))
  have h9 := h v4 x v1
  have h10 := C (T (T (T (T (T h2 (C h7 (T (h v4 x v4) (C h7 (T (C h6 h5) h3))))) (C h7 (C (T h2 (C h2 h5)) h7))) (S (h v4 x x))) h9) h8) h0
  T (T h2 (C h7 (T (T (T h9 h8) h10) (C h10 h0)))) (S (h y x y))

@[equational_result]
theorem Equation1537_implies_Equation4098 (G: Type _) [Magma G] (h: Equation1537 G) : Equation4098 G := fun x y z =>
  let v0 := M y y
  have h1 := h x x x
  have h2 := S h1
  have h3 := R v0
  let v4 := M x x
  have h5 := R x
  have h6 := R v4
  let v7 := M z z
  let v8 := M v0 z
  let v9 := M v8 v8
  T (T (T (T (h v4 x x) (C h6 (C h5 (T (C h6 h1) (S (h x x v4)))))) (C h6 (C h5 (T (h x v8 v4) (C (R v9) h2))))) (S (h v9 x x))) (C (R v8) (T (C h3 (T (h z y z) (C h3 (C (R z) (T (T (T (h v7 x x) (C h6 (C h5 (T (C (R v7) h1) (S (h x z v4)))))) (C h6 (C h5 (T (h x y v4) (C h3 h2))))) (S (h v0 x x))))))) (S (h z y v0))))

@[equational_result]
theorem Equation1739_implies_Equation2 (G: Type _) [Magma G] (h: Equation1739 G) : Equation2 G := fun x y =>
  let v0 := M y y
  have h1 := R x
  have h2 := R y
  have h3 := h y x y
  have h4 := h v0 y y
  let v5 := M x x
  have h6 := R v5
  let v7 := M y v0
  have h8 := h (M v7 y) x v0
  have h9 := T (T h8 (C h6 (C (S h4) h1))) (S h3)
  T (T (h x y x) (C (R v0) (T (C h6 (T (T (T h3 (C h6 (C (h v0 x y) h1))) (S (h (M v7 x) x v5))) (C (C h2 (T (T h4 (C (C h2 (T (T h3 (C h6 (C h4 h1))) (S h8))) h9)) (C (C h2 h9) h2))) h1))) (S (h (M v0 y) x y))))) (S (h y y y))

@[equational_result]
theorem Equation2776_implies_Equation1098 (G: Type _) [Magma G] (h: Equation2776 G) : Equation1098 G := fun x y z =>
  let v0 := M z y
  let v1 := M x v0
  let v2 := M v1 z
  have h3 := h y x y
  let v4 := M y v2
  have h5 := h v2 x v4
  let v6 := M (M x v4) (M v2 x)
  T (T (T (h x v0 x) (C (C (R (M v0 x)) (h v1 z v0)) (R x))) (S (h (M (M z v0) v2) v0 x))) (C (T (T (T (T (C (T (h z y v2) (C (R (M v4 v0)) h5)) (R v0)) (S (h v6 v4 v0))) (h v6 v4 y)) (C (T (C (C (R v4) h3) (S h5)) (S (h (M (M x y) (M y x)) y v2))) (R y))) (S h3)) (R v2))

@[equational_result]
theorem Equation3120_implies_Equation4162 (G: Type _) [Magma G] (h: Equation3120 G) : Equation4162 G := fun x y z =>
  let v0 := M y x
  let v1 := M (M v0 z) z
  have h2 := R y
  have h3 := R z
  have h4 := R x
  have h5 := h y v0 v0
  have h6 := R v0
  have h7 := h x y v0
  have h8 := C (T (C h7 h6) (S h5)) h4
  have h9 := C (C h8 h3) h3
  have h10 := h v0 x z
  have h11 := T h10 h9
  T (C (T (h x y y) (C (T (T (T (C (C (C (T h5 (C (S h7) h6)) h4) h2) h2) (S (h v0 x y))) (h v0 x v0)) (C (C (T (T h8 h10) h9) h11) h11)) h2)) h2) (S (h v1 v1 y))

@[equational_result]
theorem Equation4087_implies_Equation4609 (G: Type _) [Magma G] (h: Equation4087 G) : Equation4609 G := fun x y z =>
  let v0 := M x x
  have h1 := h y v0 x
  have h2 := S h1
  have h3 := R v0
  have h4 := h x x y
  let v5 := M v0 y
  have h6 := h x v5 v0
  have h7 := R v5
  have h8 := h x x z
  have h9 := h z v0 x
  T (T (T (T (T (T (T (C (T h6 (C h2 h7)) (R y)) (S (h y y v5))) h1) (C (S h4) h3)) (C h8 h3)) (S h9)) (h z z v0)) (C (T (C (T (T (T (T (T (T (T h9 (C (T (S h8) h4) h3)) h2) (h y v5 v0)) (C (S (h y v0 y)) h7)) (C h1 h7)) (S h6)) h4) h3) h2) (R z))

@[equational_result]
theorem Equation877_implies_Equation2 (G: Type _) [Magma G] (h: Equation877 G) : Equation2 G := fun x y =>
  let v0 := M y y
  let v1 := M v0 v0
  have h2 := h y v1 y
  let v3 := M x x
  let v4 := M v3 v3
  have h5 := h x v4 x
  have h6 := S h5
  have h7 := R (M (M v4 v4) v0)
  have h8 := R x
  have h9 := h x (M v3 v0) y
  have h10 := S h9
  have h11 := T h6 h9
  T (T (T (T (T (T (h x x x) (C h8 (T (h v4 x v4) (C h5 (T (C h11 h11) (C h10 h10)))))) (S (h v4 x x))) (h v4 x y)) (C h8 h7)) (C h8 (T (T h7 (C h6 (C h2 h2))) (S (h v1 x v1))))) (S (h y x y))

@[equational_result]
theorem Equation3159_implies_Equation3674 (G: Type _) [Magma G] (h: Equation3159 G) : Equation3674 G := fun x y =>
  have h0 := R x
  let v1 := M x x
  have h2 := h x x v1
  have h3 := h x v1 x
  let v4 := M y x
  have h5 := S (h y v4 y)
  have h6 := R y
  have h7 := R v4
  have h8 := S h3
  have h9 := C h2 h0
  have h10 := C (C (C (T (C (T (h v4 x x) (C (T (C (C (T h9 h8) h0) h7) (R (M v1 v4))) h7)) h7) (S (h v4 x v4))) h7) h6) h6
  have h11 := h y v4 v4
  T (T (T h9 h8) (h x y y)) (C (C (T (C (T (T (T (C (T h11 h10) h6) h5) h11) h10) h6) h5) h0) (T h3 (C (S h2) h0)))

@[equational_result]
theorem Equation4013_implies_Equation3567 (G: Type _) [Magma G] (h: Equation4013 G) : Equation3567 G := fun x y z =>
  let v0 := M z x
  let v1 := M v0 z
  have h2 := R y
  have h3 := R x
  have h4 := h v0 z z
  have h5 := R v0
  have h6 := h z z x
  have h7 := R z
  have h8 := h v0 (M x v0) z
  have h9 := C h3 (T (h x x v0) (C (T (T h8 (C (C h7 (S h6)) h5)) (S h4)) h3))
  let v10 := M v0 (M y v0)
  T (T (T (T (T (T (T (T (T (h x y v0) (h v10 x x)) (C h9 (R v10))) (S (h v10 v1 x))) (S (h v1 y v0))) (C (T (T h4 (C (C h7 h6) h5)) (S h8)) h2)) (S (h y x v0))) (h y x x)) (C h9 h2)) (S (h y v1 x))

@[equational_result]
theorem Equation522_implies_Equation4640 (G: Type _) [Magma G] (h: Equation522 G) : Equation4640 G := fun x y z =>
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
  T (T (T (T (T (C (R v9) (h x v9 y)) (S (h y v9 v9))) (h y v1 z)) (C h4 (C h4 (T (C h8 (T (h v0 z z) (C h8 (T (T (T (C h8 (C h8 h7)) (S (h v1 z v0))) h2) (C h4 (C h4 (C h6 (T (C h4 h3) (S h5))))))))) (S (h v1 z v1)))))) (C h4 (C h4 h7))) (S h2)

@[equational_result]
theorem Equation684_implies_Equation3601 (G: Type _) [Magma G] (h: Equation684 G) : Equation3601 G := fun x y z =>
  have h0 := S (h z z y)
  let v1 := M z (M (M z y) y)
  let v2 := M y x
  let v3 := M y (M v2 x)
  have h4 := h y y x
  have h5 := R y
  let v6 := M x y
  let v7 := M v6 (M (M v6 x) x)
  let v8 := M y v6
  have h9 := h v6 v6 x
  T (T (T (h v6 y v6) (C h5 (T (T (T (C (R v6) (C (R v8) (T h9 (C h9 (R v7))))) (S (h v8 v6 v7))) (C h5 (C (R x) (T h4 (C h4 (R v3)))))) (S (h x y v3))))) (h v2 z v1)) (C (R z) (C (R v2) (T (C h0 (R v1)) h0)))

@[equational_result]
theorem Equation1492_implies_Equation1519 (G: Type _) [Magma G] (h: Equation1492 G) : Equation1519 G := fun x y =>
  let v0 := M y y
  let v1 := M x v0
  let v2 := M v0 v1
  let v3 := M v2 v2
  let v4 := M v2 v3
  have h5 := R (M v1 (M v1 v1))
  let v6 := M v0 (M v0 v0)
  let v7 := M y v0
  let v8 := M x x
  have h9 := T (T (T (h (M x v8) v1) (C (S (h v0 x)) h5)) (C (T (T (T (T (h v0 y) (C (T (h v7 v0) (C (S (h y y)) (R v6))) (R v7))) (S (h v6 y))) (h v6 v2)) (C (S (h v1 v0)) (R v4))) h5)) (S (h v4 v1))
  T (T (h x x) (C (T (T (h v8 x) (C h9 h9)) (S (h v3 v2))) h9)) (S (h v2 v2))

@[equational_result]
theorem Equation1496_implies_Equation481 (G: Type _) [Magma G] (h: Equation1496 G) : Equation481 G := fun x y z =>
  let v0 := M y (M z z)
  let v1 := M x v0
  let v2 := M y v1
  let v3 := M v2 (M v1 v1)
  let v4 := M x x
  have h5 := R (M v1 v4)
  have h6 := h v0 x v2
  let v7 := M v2 v2
  have h8 := h (M x v7) v1 x
  let v9 := M x v4
  T (T (h x x v2) (C (T (T (h v4 x x) (C (T (T (h v9 v1 x) (C (T (S (h v0 x x)) h6) h5)) (S h8)) (R v9))) (S (h v7 x x))) (T (T h8 (C (T (T (S h6) (h v0 v2 v1)) (C (S (h v1 y z)) (R v3))) h5)) (S (h v3 v1 x))))) (S (h v2 v2 v1))

@[equational_result]
theorem Equation1507_implies_Equation1374 (G: Type _) [Magma G] (h: Equation1507 G) : Equation1374 G := fun x y z =>
  let v0 := M z y
  let v1 := M v0 z
  let v2 := M v1 x
  let v3 := M x v2
  let v4 := M y v2
  have h5 := h x v1 v0
  have h6 := h y z v0
  have h7 := R v2
  have h8 := T (C h7 h6) (S h5)
  let v9 := M y v4
  let v10 := M z (M z x)
  T (T (T h5 (C h7 (S h6))) (C (T (h v2 x z) (C (R v3) (T (T (h v10 y x) (C (T (C (T (h y v2 y) (C h8 (R v9))) (R v10)) (S (h v9 x z))) (R (M x (M x y))))) (S (h v4 y x))))) (T (h y v2 x) (C h8 (R (M x v3)))))) (S (h v4 v3 x))

@[equational_result]
theorem Equation2135_implies_Equation2128 (G: Type _) [Magma G] (h: Equation2135 G) : Equation2128 G := fun x y =>
  let v0 := M y y
  let v1 := M v0 x
  let v2 := M v1 v0
  let v3 := M v2 v2
  let v4 := M v3 v2
  let v5 := M (M v0 v0) v0
  let v6 := M v0 y
  have h7 := R (M (M v1 v1) v1)
  let v8 := M x x
  have h9 := T (T (T (h (M v8 x) v1) (C h7 (S (h v0 x)))) (C h7 (T (h v0 v2) (C (R v4) (T (C (T (T (h v0 y) (C (R v6) (T (h v6 v0) (C (R v5) (S (h y y)))))) (S (h v5 y))) (R v2)) (S (h v1 v0))))))) (S (h v4 v1))
  T (T (h x x) (C h9 (T (T (h v8 x) (C h9 h9)) (S (h v3 v2))))) (S (h v2 v2))

@[equational_result]
theorem Equation3289_implies_Equation4346 (G: Type _) [Magma G] (h: Equation3289 G) : Equation4346 G := fun x y z =>
  let v0 := M z z
  have h1 := R v0
  let v2 := M y y
  have h3 := h y v2 y
  have h4 := S h3
  have h5 := h y y y
  have h6 := R v2
  have h7 := C h6 h5
  have h8 := h y y x
  have h9 := h x v2 y
  have h10 := C h6 (S h5)
  T (T (T (T (T (T (T (C (R x) (T (T (T h3 h10) (C h6 (T h3 h10))) (C h6 (T (C h6 h8) (S h9))))) (S (h x x v2))) h9) (C h6 (S h8))) h7) h4) (h y y v2)) (C (R y) (T (T (T (T (T h7 h4) (h y v0 z)) (C h1 (S (h z z y)))) (C h1 (h z z z))) (S (h z v0 z))))

@[equational_result]
theorem Equation4013_implies_Equation3334 (G: Type _) [Magma G] (h: Equation4013 G) : Equation3334 G := fun x y z =>
  let v0 := M z (M z y)
  have h1 := R z
  let v2 := M z (M z z)
  have h3 := h z y v0
  let v4 := M v0 (M y v0)
  let v5 := M v0 (M x v0)
  let v6 := M x y
  let v7 := M v6 (M y v6)
  T (T (T (T (T (T (T (h x y v6) (h v7 x v0)) (h v5 v7 z)) (C (C h1 (S (h z y v6))) (R v5))) (h v0 v5 x)) (C (C (R x) (S (h x x v0))) (C h1 (T (T (T (T (T (T h3 (h v4 z z)) (h v2 v4 z)) (C (C h1 (S h3)) (R v2))) (h v0 v2 z)) (C (C h1 (S (h z z z))) (R v0))) (S (h v0 z z)))))) (S (h (M z (M v0 z)) x x))) (S (h x v0 z))

@[equational_result]
theorem Equation909_implies_Equation1434 (G: Type _) [Magma G] (h: Equation909 G) : Equation1434 G := fun x y =>
  let v0 := M y x
  let v1 := M y v0
  have h2 := h v1 x
  let v3 := M x v1
  have h4 := h v0 y
  have h5 := R x
  let v6 := M x x
  have h7 := R v6
  have h8 := S (h x x)
  have h9 := h x v6
  have h10 := S h9
  let v11 := M v6 x
  T (T (T h9 (C h7 (T (h (M v11 v11) v6) (C h7 (C h10 h10))))) (C h7 (T (h (M v6 v6) x) (C h5 (C h8 h8))))) (C h7 (T (C h5 (T (C h5 (T (T (T (h x y) (C (R y) (C h4 h4))) (S (h (M v1 v1) y))) (C h2 h2))) (S (h (M v3 v3) x)))) (S h2)))

@[equational_result]
theorem Equation928_implies_Equation1964 (G: Type _) [Magma G] (h: Equation928 G) : Equation1964 G := fun x y z =>
  let v0 := M z x
  let v1 := M y z
  have h2 := h z v1 x
  let v3 := M x x
  have h4 := S (h x v0 x)
  have h5 := R z
  let v6 := M y v0
  let v7 := M v6 x
  have h8 := R v6
  T (T (h x v6 x) (C h8 (R (M v7 v3)))) (C h8 (T (T (C (T (h v7 y v0) (C (R y) (S (h z v6 x)))) (T (h v3 z v0) (C h5 (T (C (T (C h5 (T (h v0 v0 (M (M v0 x) v3)) (C (R v0) (C h4 h4)))) (S (h x z x))) (R (M v3 v0))) (S (h z x x)))))) (C (R v1) (C h2 h2))) (S (h v1 v1 (M (M v1 x) v0)))))

@[equational_result]
theorem Equation1384_implies_Equation4461 (G: Type _) [Magma G] (h: Equation1384 G) : Equation4461 G := fun x y z =>
  let v0 := M z z
  let v1 := M v0 y
  let v2 := M v1 v1
  have h3 := h y v2 z
  have h4 := S h3
  have h5 := h y v1 z
  have h6 := R v2
  have h7 := C h6 h5
  have h8 := S (h (M v2 y) x v1)
  have h9 := R x
  have h10 := C h6 (S h5)
  have h11 := C h9 (C (T (T h3 h10) (C h6 (T h3 h10))) h9)
  have h12 := h y v0 y
  T (T (T (T (T h11 h8) h7) h4) h12) (C (R v0) (T (T (T (T (T (h (M (M (M y y) y) v0) x z) (C h9 (C (S h12) h9))) h11) h8) h7) h4))

