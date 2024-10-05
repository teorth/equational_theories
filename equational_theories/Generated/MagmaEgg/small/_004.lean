import equational_theories.AllEquations
import equational_theories.Magma

private def congr_op {G: Type _} [Magma G] {a b c d: G} (h1: a = b) (h2: c = d): a ◇ c = b ◇ d := by
  rw [h1, h2]
private abbrev T := @Eq.trans
private abbrev S := @Eq.symm
private abbrev R := @Eq.refl
private abbrev M := @Magma.op
private abbrev C := @congr_op

@[equational_result]
theorem Equation2135_implies_Equation3150 (G: Type _) [Magma G] (h: Equation2135 G) : Equation3150 G := fun x y =>
  let v0 := M (M y y) y
  let v1 := M v0 x
  let v2 := M v1 y
  let v3 := M v2 v2
  let v4 := M v3 v2
  let v5 := M x x
  have h6 := T (T (h (M v5 x) v1) (C (R (M (M v1 v1) v1)) (T (T (S (h v0 x)) (h v0 v2)) (C (R v4) (S (h v1 y)))))) (S (h v4 v1))
  T (T (h x x) (C h6 (T (T (h v5 x) (C h6 h6)) (S (h v3 v2))))) (S (h v2 v2))

@[equational_result]
theorem Equation3290_implies_Equation3303 (G: Type _) [Magma G] (h: Equation3290 G) : Equation3303 G := fun x y z w =>
  let v0 := M w w
  have h1 := h w v0 w
  have h2 := R w
  let v3 := M x x
  let v4 := M y (M z v0)
  have h5 := S (h x v3 x)
  T (T (T (T (h x v4 v3) (C (R v4) (T (T h5 (h x v3 v3)) (C (R v3) (T (T h5 (h x w v3)) (C h2 h5)))))) (S (h w v4 v3))) (h w y v0)) (C (R y) (T (T (S h1) (h w z w)) (C (R z) (T (C h2 h1) (S (h w w v0))))))

@[equational_result]
theorem Equation3218_implies_Equation5 (G: Type _) [Magma G] (h: Equation3218 G) : Equation5 G := fun x y =>
  let v0 := M y x
  have h1 := R y
  have h2 := S (h v0 v0 v0)
  have h3 := R v0
  have h4 := S (h v0 v0 x)
  have h5 := C (h x y x) h3
  have h6 := C (C (C (T h5 h4) h3) h3) h3
  have h7 := h v0 x v0
  T (h x y y) (C (T (C (C (C (T (h y x v0) (C (T (C (T (T (T (C (T (T (T h5 h4) h7) h6) h3) h2) h7) h6) h3) h2) h1)) h1) h1) h1) (S (h y v0 y))) (R x))

@[equational_result]
theorem Equation508_implies_Equation1996 (G: Type _) [Magma G] (h: Equation508 G) : Equation1996 G := fun x y z =>
  let v0 := M z z
  have h1 := h v0 y z
  have h2 := S h1
  have h3 := R y
  have h4 := h y y v0
  let v5 := M y v0
  T (h x v5 y) (C (R v5) (T (C (T (C h3 h1) (S h4)) (R (M x (M y y)))) (C h3 (T (C (R x) (T (T (C h3 (T (T h4 (C h3 h2)) (C h3 (T (h v0 v0 v0) (C (R v0) (S (h v0 v0 z))))))) h2) (h v0 x z))) (S (h x x v0))))))

@[equational_result]
theorem Equation2663_implies_Equation263 (G: Type _) [Magma G] (h: Equation2663 G) : Equation263 G := fun x y =>
  have h0 := R x
  let v1 := M x y
  let v2 := M v1 y
  have h3 := h v2 x
  let v4 := M v2 x
  have h5 := h v1 y
  have h6 := h x x
  have h7 := S h6
  let v8 := M x x
  T h6 (C (T (T (h (M v8 v8) x) (C (T (T (C h7 h7) (C (T (T (T (h x y) (C (C h5 h5) (R y))) (S (h (M v2 v2) y))) (C h3 h3)) h0)) (S (h (M v4 v4) x))) h0)) (S h3)) h0)

@[equational_result]
theorem Equation3159_implies_Equation1884 (G: Type _) [Magma G] (h: Equation3159 G) : Equation1884 G := fun x y =>
  have h0 := R x
  let v1 := M x x
  have h2 := h x x v1
  have h3 := h x v1 x
  have h4 := T h3 (C (S h2) h0)
  have h5 := S (h y x y)
  have h6 := R y
  have h7 := C (T (C (C (T (C h2 h0) (S h3)) h0) h6) (R (M v1 y))) h6
  have h8 := h y x x
  T (h x y y) (C (C (T (C (T (T (T (C (T h8 h7) h6) h5) h8) h7) h6) h5) h4) h4)

@[equational_result]
theorem Equation3810_implies_Equation4620 (G: Type _) [Magma G] (h: Equation3810 G) : Equation4620 G := fun x y z =>
  let v0 := M x x
  let v1 := M z y
  let v2 := M v0 v1
  let v3 := M v0 z
  let v4 := M v0 y
  have h5 := S (h v0 y z)
  let v6 := M z v0
  T (T (T (T (h v0 y v1) (C (h v1 y v0) (T (C (h z y v0) (T (T (T (h x x x) (h v0 v0 z)) (h v6 v6 v1)) (C h5 h5))) (S (h v4 v3 v4))))) (S (h v3 v2 v4))) (R (M v3 v2))) (S (h v1 z v0))

@[equational_result]
theorem Equation857_implies_Equation4 (G: Type _) [Magma G] (h: Equation857 G) : Equation4 G := fun x y =>
  let v0 := M x x
  let v1 := M v0 v0
  have h2 := h v0 x x
  let v3 := M x y
  let v4 := M y y
  let v5 := M y v3
  T (h x y v3) (C (R x) (T (T (T (C (R v5) (T (h v4 y y) (C (h v4 x x) (R (M v4 v4))))) (S (h v5 v4 v1))) (C (R y) (T (h v3 x x) (C (R v3) (T (C (R v0) (T h2 (C h2 (R v1)))) (S (h v0 v0 v1))))))) (S (h y x y))))

@[equational_result]
theorem Equation2757_implies_Equation5 (G: Type _) [Magma G] (h: Equation2757 G) : Equation5 G := fun x y =>
  let v0 := M y x
  let v1 := M x x
  let v2 := M v1 v1
  have h3 := h v1 x x
  let v4 := M y y
  let v5 := M v0 y
  T (h x y v0) (C (T (T (T (C (T (h v4 y y) (C (R (M v4 v4)) (h v4 x x))) (R v5)) (S (h v5 v4 v2))) (C (T (h v0 x x) (C (T (C (T h3 (C (R v2) h3)) (R v1)) (S (h v1 v1 v2))) (R v0))) (R y))) (S (h y x y))) (R x))

@[equational_result]
theorem Equation3607_implies_Equation4369 (G: Type _) [Magma G] (h: Equation3607 G) : Equation4369 G := fun x y z =>
  let v0 := M y z
  let v1 := M x v0
  let v2 := M y x
  have h3 := R z
  let v4 := M z v2
  have h5 := h x v0 v4
  let v6 := M (M v0 v4) x
  T (T h5 (h v4 v6 z)) (C h3 (T (C (T (h v6 z v2) (C (R v2) (S h5))) (T (T (C h3 (h y x v0)) (S (h (M v1 y) y z))) (C (h v1 y x) (R y)))) (S (h y x (M v2 v1)))))

@[equational_result]
theorem Equation3979_implies_Equation3573 (G: Type _) [Magma G] (h: Equation3979 G) : Equation3573 G := fun x y z =>
  let v0 := M z z
  let v1 := M v0 v0
  let v2 := M x v0
  have h3 := h v1 x z
  have h4 := h x v0 z
  let v5 := M y v0
  T (T (T (T (T (T (h x y z) (h v5 x z)) (C (T h4 h3) (R v5))) (S (h v5 v2 v0))) (S (h v2 y z))) (C (T (T (T (T (T h4 h3) (h v2 v1 z)) (C (S (h v0 v0 z)) (R v2))) (h v1 v2 z)) (C (S (h v0 x z)) (R v1))) (R y))) (S (h y (M v0 x) v0))

@[equational_result]
theorem Equation1301_implies_Equation2511 (G: Type _) [Magma G] (h: Equation1301 G) : Equation2511 G := fun x y z =>
  let v0 := M (M x y) z
  let v1 := M y v0
  let v2 := M v1 z
  have h3 := R z
  let v4 := M (M v2 v2) z
  let v5 := M (M v1 v1) v0
  have h6 := R v0
  have h7 := h y v1 v0
  T (T (h x z y) (C h3 (T (T (T (C h6 (T h7 (C (C h7 h6) (R v5)))) (S (h v1 v0 v5))) (h v1 v4 z)) (C (R v4) (C (S (h v1 v2 z)) h3))))) (S (h v2 z v2))

@[equational_result]
theorem Equation1726_implies_Equation3147 (G: Type _) [Magma G] (h: Equation1726 G) : Equation3147 G := fun x y z =>
  let v0 := M y y
  let v1 := M v0 x
  let v2 := M (M v1 z) z
  have h3 := h v2 y v2
  have h4 := h v1 v2 z
  have h5 := R v0
  let v6 := M x x
  have h7 := R v6
  T (T (h x y x) (C h5 (T (C (T (T (h v6 x v1) (C h7 (C (T (T (T (C h7 h4) (S (h v2 x v2))) h3) (C h5 (S h4))) (R v1)))) (S (h v0 x v1))) (R x)) h4))) (S h3)

@[equational_result]
theorem Equation3607_implies_Equation4146 (G: Type _) [Magma G] (h: Equation3607 G) : Equation4146 G := fun x y z =>
  let v0 := M x z
  let v1 := M v0 z
  let v2 := M (M y v0) v1
  have h3 := R v0
  have h4 := R v1
  have h5 := h y v0 z
  let v6 := M z (M v1 y)
  T (T (T (T (h x y v0) (C h3 (C h5 (R x)))) (C h3 (T (T (h v6 x z) (C (R z) (T (h v0 v6 v1) (C h4 (C (C (S h5) h4) h3))))) (S (h (M v2 v0) v0 z))))) (S (h v0 v2 v0))) (S (h v1 y v0))

@[equational_result]
theorem Equation4156_implies_Equation41 (G: Type _) [Magma G] (h: Equation4156 G) : Equation41 G := fun x y z =>
  have h0 := R z
  let v1 := M x x
  have h2 := R v1
  have h3 := h y z y
  let v4 := M z y
  let v5 := M y z
  T (T (h x x z) (C (T (T (T (h v1 x v5) (C (T (C (T (h x v1 x) (C (S (h x x x)) (R x))) h2) (S (h x x v1))) (R v5))) (h v1 v5 y)) (C (T (C (T (T (T (C h3 h2) (S (h y v4 v1))) (h y v4 z)) (C (S h3) h0)) h2) (S (h z y v1))) (R y))) h0)) (S (h y z z))

@[equational_result]
theorem Equation2197_implies_Equation2 (G: Type _) [Magma G] (h: Equation2197 G) : Equation2 G := fun x y =>
  let v0 := M y x
  let v1 := M v0 x
  have h2 := S (h v1 x x)
  let v3 := M v1 x
  let v4 := M x x
  let v5 := M v4 x
  let v6 := M v5 x
  have h7 := h v5 x x
  T (T (h x y x) (C (R v1) (T (T (T (T (T (h v4 x x) (C (T h7 (C h7 (R v6))) h7)) (S (h v5 v5 v6))) (h v5 v5 v3)) (C (T (C h2 (R v3)) (S (h v1 y x))) h2)) (S (h v0 y x))))) (S (h y y x))

@[equational_result]
theorem Equation3008_implies_Equation1710 (G: Type _) [Magma G] (h: Equation3008 G) : Equation1710 G := fun x y z =>
  let v0 := M z z
  let v1 := M v0 y
  have h2 := R v0
  let v3 := M v0 v0
  have h4 := h v0 v3 z
  have h5 := R v3
  have h6 := h v0 v0 z
  have h7 := T h4 (C (S h6) h5)
  T (h x v1 z) (C (C (T (C (C (T (T h6 (C (T (C (C h7 h7) h2) (S (h (M v0 v3) v0 v0))) h2)) (C (T (C h6 h5) (S h4)) h2)) (R y)) h2) (S (h y v0 z))) (R x)) (R v1))

@[equational_result]
theorem Equation3159_implies_Equation4385 (G: Type _) [Magma G] (h: Equation3159 G) : Equation4385 G := fun x y =>
  have h0 := R x
  have h1 := S (h y x y)
  have h2 := R y
  let v3 := M x x
  have h4 := S (h x v3 x)
  have h5 := C (h x x v3) h0
  have h6 := T h5 h4
  have h7 := C (T (C (C h6 h0) h2) (R (M v3 y))) h2
  have h8 := h y x x
  T (T (T (T (C h0 h6) h5) h4) (h x y y)) (C (C (T (C (T (T (T (C (T h8 h7) h2) h1) h8) h7) h2) h1) h0) h0)

@[equational_result]
theorem Equation3791_implies_Equation3973 (G: Type _) [Magma G] (h: Equation3791 G) : Equation3973 G := fun x y z =>
  let v0 := M x y
  let v1 := M z x
  let v2 := M y v1
  have h3 := h x y v1
  T (T h3 (C (T (T (h v1 x y) (h v2 v0 (M v1 x))) (C (S h3) (S (h y v1 x)))) (T (T (T (h y v1 v0) (h (M v0 y) (M v1 v0) v2)) (C (T (T (T (S (h v1 v0 y)) (C (h z x y) (h x y z))) (S (h v0 v1 (M y z)))) (S (h y z x))) (S (h v0 y v1)))) (S (h z v0 y))))) (S (h v2 z v0))

@[equational_result]
theorem Equation1943_implies_Equation711 (G: Type _) [Magma G] (h: Equation1943 G) : Equation711 G := fun x y z =>
  let v0 := M x z
  let v1 := M v0 z
  let v2 := M y (M y v1)
  let v3 := M v2 v0
  have h4 := R (M v2 v3)
  let v5 := M z (M z z)
  let v6 := M x v0
  T (T (T (h x v2 v0) (C h4 (T (T (T (T (h v6 x v0) (C (R (M x v6)) (T (S (h x x z)) (h x z z)))) (S (h v5 x v0))) (h v5 y v1)) (C (R v2) (S (h v0 z z)))))) (C h4 (R v3))) (S (h v2 v2 v0))

@[equational_result]
theorem Equation1304_implies_Equation2917 (G: Type _) [Magma G] (h: Equation1304 G) : Equation2917 G := fun x y z =>
  let v0 := M y (M x y)
  let v1 := M (M v0 z) z
  let v2 := M (M (M v1 x) x) v1
  have h3 := R x
  have h4 := h v1 v1 x
  have h5 := R y
  have h6 := S (h x x x)
  let v7 := M (M (M x x) x) x
  T (T (T (T (h x y v7) (C h5 (C (T (C h6 (R v7)) h6) h5))) (h v0 x z)) (C h3 (C (T h4 (C h4 (R v2))) h3))) (S (h v1 x v2))

@[equational_result]
theorem Equation3159_implies_Equation832 (G: Type _) [Magma G] (h: Equation3159 G) : Equation832 G := fun x y =>
  have h0 := R x
  let v1 := M x x
  have h2 := h x x v1
  have h3 := S h2
  have h4 := h x v1 x
  have h5 := S (h y x y)
  have h6 := R y
  have h7 := C (T (C (C (T (C h2 h0) (S h4)) h0) h6) (R (M v1 y))) h6
  have h8 := h y x x
  T h4 (C h3 (T (h x y y) (C (C (T (C (T (T (T (C (T h8 h7) h6) h5) h8) h7) h6) h5) h0) (T h4 (C h3 h0)))))

@[equational_result]
theorem Equation3275_implies_Equation3301 (G: Type _) [Magma G] (h: Equation3275 G) : Equation3301 G := fun x y z w =>
  have h0 := h z y w
  let v1 := M y (M z (M w y))
  have h2 := R z
  have h3 := R v1
  have h4 := S h0
  let v5 := M x x
  T (T (T (T (T (T (h x v5 v1) (C (R v5) (T (S (h v1 x x)) (C h3 (T (T h4 (h z v1 x)) (C h3 (T (C h2 (C (R x) h4)) (S (h x z z))))))))) (S (h v1 v5 v1))) (C h3 h4)) (C h3 (T (h z z z) (C h2 (C h2 h0))))) (S (h z v1 z))) h0

@[equational_result]
theorem Equation3350_implies_Equation4229 (G: Type _) [Magma G] (h: Equation3350 G) : Equation4229 G := fun x y z =>
  let v0 := M z z
  let v1 := M v0 y
  let v2 := M v1 x
  let v3 := M v0 v0
  let v4 := M v1 v3
  let v5 := M v2 v2
  let v6 := M x v0
  T (T (T (T (T (T (h x y z) (h y v6 v0)) (C (R v6) (T (T (T (h y v3 v0) (C (R v3) (S (h v0 y z)))) (h v3 v1 v0)) (C (R v1) (T (S (h v0 v3 z)) (S (h v0 v0 z))))))) (h v6 v4 v5)) (C (R v4) (T (S (h v5 v6 v2)) (S (h x v5 z))))) (S (h x v4 v2))) (S (h v1 x v0))

@[equational_result]
theorem Equation3973_implies_Equation4684 (G: Type _) [Magma G] (h: Equation3973 G) : Equation4684 G := fun x y z =>
  let v0 := M x y
  let v1 := M v0 z
  let v2 := M y v1
  have h3 := R z
  let v4 := M z y
  have h5 := R v4
  let v6 := M v4 x
  let v7 := M v6 v0
  T (T (T (C (T (h x y v4) (C (T (T (T (h y v6 x) (h v7 x z)) (C (T (h x (M z v7) v4) (C (S (h v0 z v6)) h5)) h3)) (S (h y v1 z))) h5)) h3) (S (h y v2 z))) (h y v2 x)) (C (S (h z y v0)) (R x))

@[equational_result]
theorem Equation4101_implies_Equation4113 (G: Type _) [Magma G] (h: Equation4101 G) : Equation4113 G := fun x y z w =>
  have h0 := h w y z
  let v1 := M (M (M y z) w) y
  have h2 := R v1
  have h3 := R w
  have h4 := S h0
  let v5 := M x x
  T (T (T (T (T (T (h x v5 v1) (C (T (S (h v1 x x)) (C (T (T h4 (h w v1 x)) (C (T (C (C h4 (R x)) h3) (S (h x w w))) h2)) h2)) (R v5))) (S (h v1 v5 v1))) (C h4 h2)) (C (T (h w w w) (C (C h0 h3) h3)) h2)) (S (h w v1 w))) h0

@[equational_result]
theorem Equation695_implies_Equation1993 (G: Type _) [Magma G] (h: Equation695 G) : Equation1993 G := fun x y z =>
  let v0 := M z z
  let v1 := M v0 v0
  have h2 := h v0 v1 z
  have h3 := h v0 v0 z
  have h4 := R v1
  have h5 := R v0
  have h6 := T h2 (C h4 (S h3))
  let v7 := M y v0
  T (h x v7 z) (C (R v7) (C (R x) (T (C h5 (C (R y) (T (T h3 (C h5 (T (C h5 (C h6 h6)) (S (h (M v1 v0) v0 v0))))) (C h5 (T (C h4 h3) (S h2)))))) (S (h y v0 z)))))

@[equational_result]
theorem Equation3145_implies_Equation1672 (G: Type _) [Magma G] (h: Equation3145 G) : Equation1672 G := fun x y z =>
  let v0 := M z z
  let v1 := M v0 x
  have h2 := S (h v0 v0 v1)
  have h3 := R v0
  have h4 := R v1
  have h5 := C (S (h v0 z v0)) h3
  have h6 := h v0 v0 v0
  have h7 := C (T h6 h5) h3
  T (h x v1 y) (C (C (S (h x z v1)) (R y)) (T (h x z v0) (C (T (C (T (h v1 z v0) (C (T (T (T (T (C (C (T (T h6 h5) h7) h4) h3) h2) h6) h5) h7) h4)) h3) h2) (R x))))

@[equational_result]
theorem Equation3159_implies_Equation1478 (G: Type _) [Magma G] (h: Equation3159 G) : Equation1478 G := fun x y =>
  have h0 := R x
  let v1 := M x x
  have h2 := h x x v1
  have h3 := S h2
  have h4 := h x v1 x
  have h5 := T h4 (C h3 h0)
  have h6 := T (C h2 h0) (S h4)
  have h7 := R y
  have h8 := T (C (T (h y x x) (C (T (C (C h6 h0) h7) (R (M v1 y))) h7)) h7) (S (h y x y))
  T (T (h x y y) (C (C (C h8 h7) h5) h0)) (C (C h8 h6) (T h4 (C h3 h5)))

@[equational_result]
theorem Equation3973_implies_Equation3334 (G: Type _) [Magma G] (h: Equation3973 G) : Equation3334 G := fun x y z =>
  let v0 := M z y
  let v1 := M z v0
  let v2 := M v1 (M v0 x)
  have h3 := R v0
  have h4 := R v1
  have h5 := h v0 x z
  let v6 := M (M x v1) z
  T (T (T (T (h x y v0) (C (C (R y) h5) h3)) (C (T (T (h y v6 z) (C (T (h v6 v0 v1) (C (C h3 (C h4 (S h5))) h4)) (R z))) (S (h v0 (M v0 v2) z))) h3)) (S (h v2 v0 v0))) (S (h x v1 v0))

@[equational_result]
theorem Equation641_implies_Equation4 (G: Type _) [Magma G] (h: Equation641 G) : Equation4 G := fun x y =>
  let v0 := M x y
  have h1 := h y x (M (M v0 x) x)
  have h2 := h x v0 x
  have h3 := R y
  have h4 := T (C h3 h2) (S h1)
  have h5 := R x
  have h6 := h y v0 y
  have h7 := C h3 (S h2)
  T (T (h x y (M (M y y) y)) (C h5 (T (C (T h1 h7) (C h4 (C (T (C h3 (T (T h1 h7) (C h6 h5))) (C h3 (C (S h6) h5))) h3))) (S (h (M y x) y y))))) (C h5 h4)

@[equational_result]
theorem Equation934_implies_Equation4200 (G: Type _) [Magma G] (h: Equation934 G) : Equation4200 G := fun x y z =>
  let v0 := M z x
  let v1 := M v0 z
  let v2 := M v1 y
  have h3 := h v2 x v1
  let v4 := M (M x v1) (M v1 v2)
  have h5 := R v0
  have h6 := R z
  let v7 := M x y
  have h8 := h y z v7
  T (C (R x) (T (T (T (T h8 (C h6 (T (h (M (M z v7) (M v7 y)) v0 z) (C h5 (C (R v1) (S h8)))))) (C h6 (C h5 h3))) (S (h v4 z x))) (R v4))) (S h3)

@[equational_result]
theorem Equation1493_implies_Equation2 (G: Type _) [Magma G] (h: Equation1493 G) : Equation2 G := fun x y =>
  let v0 := M y x
  let v1 := M y v0
  let v2 := M y y
  let v3 := M y v2
  have h4 := S (h v3 y x)
  let v5 := M y v3
  let v6 := M y v1
  have h7 := h v1 y x
  T (T (h x y x) (C (T (T (T (T (T (h v0 y x) (C h7 (T h7 (C (R v6) h7)))) (S (h v1 v6 v1))) (h v1 v5 v1)) (C h4 (T (C (R v5) h4) (S (h v3 y y))))) (S (h v2 y y))) (R v1))) (S (h y y x))

@[equational_result]
theorem Equation1507_implies_Equation2170 (G: Type _) [Magma G] (h: Equation1507 G) : Equation2170 G := fun x y z =>
  let v0 := M y z
  let v1 := M v0 x
  let v2 := M z y
  have h3 := h z y y
  let v4 := M y (M y y)
  let v5 := M v0 (M v0 v0)
  T (h x v0 v0) (C (R v1) (T (T (h v5 z v1) (C (T (T (T (T (C h3 (R v5)) (S (h v4 v0 v0))) (h v4 v0 x)) (C (T (S h3) (h z y z)) (R (M x (M x v0))))) (S (h (M z v2) v0 x))) (R (M v1 (M v1 z))))) (S (h v2 z v1))))

@[equational_result]
theorem Equation3791_implies_Equation4176 (G: Type _) [Magma G] (h: Equation3791 G) : Equation4176 G := fun x y z =>
  let v0 := M x y
  let v1 := M y z
  let v2 := M v1 x
  let v3 := M y v1
  have h4 := h z x y
  let v5 := M z x
  have h6 := T (T (T (C (h y z x) (h v1 x y)) (S (h v5 v3 v0))) (C h4 (R v3))) (S (h v0 y v1))
  T (T (T (h x y z) (h v5 v1 (M v1 v2))) (C (T (T (C h6 h4) (S (h y v1 v0))) (h y v1 x)) (T (C (R v1) h6) (S (h z v0 y))))) (S (h v2 z v0))

@[equational_result]
theorem Equation1639_implies_Equation27 (G: Type _) [Magma G] (h: Equation1639 G) : Equation27 G := fun x y z =>
  let v0 := M x x
  let v1 := M v0 x
  let v2 := M x y
  have h3 := h x x v1
  have h4 := h x x x
  have h5 := R v0
  have h6 := T h3 (C h5 (S h4))
  T (h x z v2) (C (T (h v0 y y) (C (T (T (T (C (C h6 h6) (h v0 x x)) (S (h v1 v0 v1))) (C h5 h4)) (S h3)) (T (C (R (M y y)) (h y x x)) (S (h y y v1))))) (T (C (R (M z z)) (h v2 x x)) (S (h z v2 v1))))

@[equational_result]
theorem Equation1929_implies_Equation508 (G: Type _) [Magma G] (h: Equation1929 G) : Equation508 G := fun x y z =>
  let v0 := M z z
  let v1 := M x v0
  let v2 := M y (M y v1)
  have h3 := h v1 y v2
  let v4 := M x x
  have h5 := R v4
  have h6 := R v1
  T (T (h x x v1) (C (T (C (R x) (T (T (h v4 v1 x) (C (T (C h6 (T (C h3 h5) (S (h v2 v2 x)))) (C h6 (T (h v2 v2 z) (C (S h3) (R v0))))) h5)) (S (h v0 v1 x)))) h3) (R (M v1 v1)))) (S (h v2 v2 v1))

@[equational_result]
theorem Equation1537_implies_Equation2998 (G: Type _) [Magma G] (h: Equation1537 G) : Equation2998 G := fun x y z =>
  have h0 := R x
  have h1 := S (h z x y)
  let v2 := M y (M z y)
  have h3 := R v2
  let v4 := M x x
  have h5 := R v4
  have h6 := T (T (h v4 x v2) (C h5 (T (C h3 h1) (C h3 (h z v2 y))))) (S (h (M v2 v2) x v2))
  T (T (T (h x x v4) (C h5 (S (h x x x)))) (C h6 h0)) (C (C h3 (T (T (h v2 x v4) (C h5 (T (C h5 (C h3 h6)) (S (h v2 x v2))))) h1)) h0)

@[equational_result]
theorem Equation1707_implies_Equation692 (G: Type _) [Magma G] (h: Equation1707 G) : Equation692 G := fun x y z =>
  let v0 := M z y
  let v1 := M v0 z
  let v2 := M x v1
  let v3 := M y v2
  have h4 := h z v0 z
  let v5 := M (M z v0) z
  let v6 := M v2 x
  T (T (h x v2 v2) (C (T (T (h v6 z x) (C (T (T (T (C h4 (R v6)) (S (h v5 v1 x))) (h v5 v1 v3)) (C (S h4) (C (S (h v2 y z)) (R v3)))) (R (M (M x z) x)))) (S (h (M v2 v3) z x))) (R (M (M v2 v2) v2)))) (S (h v3 v2 v2))

@[equational_result]
theorem Equation1537_implies_Equation2389 (G: Type _) [Magma G] (h: Equation1537 G) : Equation2389 G := fun x y z =>
  have h0 := R x
  let v1 := M z (M y z)
  have h2 := R v1
  have h3 := S (h y x z)
  let v4 := M x x
  have h5 := R v4
  have h6 := T (T (h v4 x v1) (C h5 (T (C h2 h3) (C h2 (h y v1 z))))) (S (h (M v1 v1) x v1))
  T (T (T (h x x v4) (C h5 (S (h x x x)))) (C h6 h0)) (C (C (T (T (h v1 x v4) (C h5 (T (C h5 (C h2 h6)) (S (h v1 x v1))))) h3) h2) h0)

@[equational_result]
theorem Equation1909_implies_Equation2 (G: Type _) [Magma G] (h: Equation1909 G) : Equation2 G := fun x y =>
  let v0 := M y y
  have h1 := R v0
  have h2 := h y x x
  let v3 := M x x
  have h4 := R v3
  let v5 := M y x
  have h6 := h v5 y y
  have h7 := R x
  let v8 := M v5 y
  have h9 := h v5 x y
  T (T (h x y x) (C (T (T (T (C (T (T h2 (C (C h7 h9) h4)) (S (h (M x v8) x v3))) h4) (S h9)) h6) (C (T (T (h (M y v8) x v0) (C (C h7 (S h6)) h4)) (S h2)) h1)) h1)) (S (h y y y))

@[equational_result]
theorem Equation2554_implies_Equation2430 (G: Type _) [Magma G] (h: Equation2554 G) : Equation2430 G := fun x y z w =>
  let v0 := M w w
  let v1 := M z v0
  let v2 := M (M v0 z) v0
  have h3 := C (R w) (S (h w w x))
  let v4 := M (M w x) w
  have h5 := T (T (C (T (h z w v4) (C h3 (R z))) (R v0)) (h v2 w v4)) (C h3 (R v2))
  T (h x v1 y) (C (T (T (C h5 (R (M (M v1 y) v1))) (C (R (M v0 v2)) (C (T (C h5 (R y)) (S (h y v0 z))) (R v1)))) (S (h (M y v1) v0 z))) (R x))

@[equational_result]
theorem Equation1665_implies_Equation27 (G: Type _) [Magma G] (h: Equation1665 G) : Equation27 G := fun x y z =>
  let v0 := M x y
  let v1 := M v0 z
  let v2 := M (M v1 v1) v1
  let v3 := M v1 v2
  let v4 := M (M x v0) z
  have h5 := h v0 z x
  let v6 := M (M y x) x
  let v7 := M x v6
  T (T (T (h x y v7) (C (R v0) (C (T (C (R v7) (h x x y)) (S (h x v6 x))) (R y)))) (C h5 (T h5 (C (T (h v1 v2 v1) (C (R v3) (S (h v1 v1 v1)))) (R v4))))) (S (h v1 v4 v3))

@[equational_result]
theorem Equation522_implies_Equation26 (G: Type _) [Magma G] (h: Equation522 G) : Equation26 G := fun x y =>
  let v0 := M x y
  let v1 := M v0 y
  have h2 := h v1 v1 v0
  have h3 := h v0 v1 y
  have h4 := R v1
  have h5 := h y v1 v1
  have h6 := R v0
  have h7 := C h6 (T h5 (C h4 (S h3)))
  have h8 := R y
  T (T (T (h x v1 y) (C h4 (C h4 (T (C h8 (T (h v0 y y) (C h8 (T (T (T (C h8 (C h8 h7)) (S (h v1 y v0))) h2) (C h4 (C h4 (C h6 (T (C h4 h3) (S h5))))))))) (S (h v1 y v1)))))) (C h4 (C h4 h7))) (S h2)

@[equational_result]
theorem Equation2780_implies_Equation2 (G: Type _) [Magma G] (h: Equation2780 G) : Equation2 G := fun x y =>
  have h0 := R x
  let v1 := M y x
  let v2 := M x x
  have h3 := R v2
  let v4 := M v1 x
  have h5 := h x y x
  let v6 := M v1 v2
  let v7 := M v2 x
  T (T (T (T (T (T (h x x x) (C (C h3 (h v2 x x)) h0)) (S (h (M v2 v7) x x))) (C h3 (T (T (h v7 x x) (C (C h3 (T (T (T (C (C h3 h5) h0) (S (h v6 x x))) (h v6 y x)) (C (C (R v1) (S h5)) h0))) h0)) (S (h v4 x x))))) (h (M v2 v4) x x)) (C (C h3 (S (h v1 x x))) h0)) (S (h y x x))

@[equational_result]
theorem Equation953_implies_Equation2 (G: Type _) [Magma G] (h: Equation953 G) : Equation2 G := fun x y =>
  let v0 := M y y
  have h1 := R v0
  have h2 := R x
  let v3 := M x x
  have h4 := R v3
  let v5 := M (M y x) v0
  T (T (T (T (T (T (h x x x) (C h2 (C (h v3 x x) h4))) (S (h (M (M x v3) v3) x x))) (C (T (T (T (T (C (h x x y) h4) (h (M (M x v5) v3) x x)) (C h2 (C (T (S (h v5 x x)) (h v5 x y)) h4))) (S (h (M (M y v5) v0) x x))) (C (S (h x y y)) h1)) h4)) (h (M (M x v0) v3) x y)) (C h2 (C (S (h v0 y x)) h1))) (S (h y x y))

@[equational_result]
theorem Equation1060_implies_Equation1257 (G: Type _) [Magma G] (h: Equation1060 G) : Equation1257 G := fun x y z w =>
  let v0 := M y y
  let v1 := M v0 z
  let v2 := M v1 w
  have h3 := C (S (h y y x)) (R y)
  let v4 := M v0 (M z v0)
  let v5 := M y (M x y)
  have h6 := T (T (C (R v0) (T (h z y v5) (C (R z) h3))) (h v4 y v5)) (C (R v4) h3)
  have h7 := R v1
  T (h x v1 w) (C (R x) (T (T (C (C h7 (T (C (R w) h6) (S (h w v0 z)))) h7) (C (R v2) h6)) (S (h v2 v0 z))))

@[equational_result]
theorem Equation1740_implies_Equation978 (G: Type _) [Magma G] (h: Equation1740 G) : Equation978 G := fun x y z =>
  let v0 := M x y
  let v1 := M z z
  let v2 := M v1 v0
  let v3 := M y v2
  have h4 := R v1
  have h5 := R (M x x)
  T (T (h x v3 v0) (C (R (M v3 v3)) (C (T (T (h (M v0 x) x v1) (C h5 (T (C (S (h y z x)) h4) (C (T (h y z v3) (C h4 (C (T (T (h (M v3 y) x v1) (C h5 (C (S (h v2 z y)) h4))) (S (h v0 x v1))) (R v3)))) h4)))) (S (h (M v0 v3) x v1))) (R v0)))) (S (h v3 v3 v0))

@[equational_result]
theorem Equation1756_implies_Equation2 (G: Type _) [Magma G] (h: Equation1756 G) : Equation2 G := fun x y =>
  let v0 := M x x
  let v1 := M x y
  have h2 := h x v0 v0
  have h3 := S h2
  let v4 := M v0 v0
  have h5 := h v0 v4 x
  let v6 := M v4 x
  let v7 := M v6 v6
  have h8 := h v6 v7 v7
  let v9 := M v7 v7
  T (T h2 (C (T (T (T (C (R v0) (T h5 (C h8 h3))) (S (h v9 x x))) (h v9 x y)) (C (R v1) (T (C (S h8) h2) (S h5)))) (T (h v4 y y) (C (R (M y y)) (C h3 (R y)))))) (S (h y v1 v0))

@[equational_result]
theorem Equation489_implies_Equation1504 (G: Type _) [Magma G] (h: Equation489 G) : Equation1504 G := fun x y z =>
  let v0 := M y x
  let v1 := M y z
  let v2 := M z v1
  have h3 := C (R z) (S (h v1 y z))
  have h4 := h y z v1
  have h5 := T h4 h3
  have h6 := h v0 y x
  have h7 := R x
  have h8 := R v0
  T (h x v0 y) (C h8 (T (C h7 (T (T (T (C h5 (C h8 (T (T (T h4 h3) (h v2 y x)) (C (R y) (C (R v2) (T (C h7 h6) (S (h y x v0)))))))) (S (h v0 v2 y))) h6) (C h5 (R (M v0 (M x v0)))))) (S (h v2 x v0))))

@[equational_result]
theorem Equation1462_implies_Equation27 (G: Type _) [Magma G] (h: Equation1462 G) : Equation27 G := fun x y z =>
  let v0 := M x y
  let v1 := M v0 z
  have h2 := h v1 v1 v1
  have h3 := h v0 z v1
  let v4 := M v1 v1
  have h5 := R v4
  have h6 := T h2 (C h5 (S h3))
  have h7 := R x
  let v8 := M v0 v0
  have h9 := T (h v0 v0 v0) (C (R v8) (S (h x y v0)))
  T (T (T (T (T (h x y x) (C h9 (C h7 h9))) (S (h v8 x x))) (C (T (T (h v0 z x) (C h6 (C h7 h6))) (S (h v4 v0 x))) (R v0))) (C h5 h3)) (S h2)

@[equational_result]
theorem Equation3716_implies_Equation3921 (G: Type _) [Magma G] (h: Equation3716 G) : Equation3921 G := fun x y z =>
  let v0 := M x z
  let v1 := M v0 y
  let v2 := M x x
  have h3 := R v1
  have h4 := h x x x
  have h5 := S h4
  let v6 := M v2 v2
  let v7 := M (M x v0) y
  have h8 := R (M y v7)
  T (T (T (T (h x y v7) (C h4 h8)) (C (C h4 h4) h8)) (S (h v6 y v7))) (C (T (T (T (T (T (T (T h5 (h x x z)) (C h4 (R v0))) (h v6 v0 y)) (C (C h5 h5) h3)) (C h5 h3)) (R (M v2 v1))) (S (h x v0 y))) (R y))

@[equational_result]
theorem Equation2741_implies_Equation2474 (G: Type _) [Magma G] (h: Equation2741 G) : Equation2474 G := fun x y z =>
  let v0 := M y y
  let v1 := M v0 z
  let v2 := M x v1
  have h3 := h z y v2
  have h4 := R v2
  let v5 := M x x
  have h6 := h v1 v2 v2
  let v7 := M v2 v2
  T (h x v7 v1) (C (S (h v2 v2 v2)) (T (T h6 (C (T (T (T (h (M v7 (M v1 v2)) x v2) (C (C (R v5) (S h6)) h4)) (C (T (h (M v5 v1) y z) (C (C (R v0) (S (h v0 x z))) h3)) h4)) (S (h (M v0 (M z v2)) v0 v2))) h4)) (S h3)))

@[equational_result]
theorem Equation3159_implies_Equation364 (G: Type _) [Magma G] (h: Equation3159 G) : Equation364 G := fun x y =>
  have h0 := R x
  let v1 := M y x
  have h2 := S (h y v1 y)
  have h3 := R y
  have h4 := R v1
  let v5 := M x x
  have h6 := S (h x v5 x)
  have h7 := C (h x x v5) h0
  have h8 := C (C (C (T (C (T (h v1 x x) (C (T (C (C (T h7 h6) h0) h4) (R (M v5 v1))) h4)) h4) (S (h v1 x v1))) h4) h3) h3
  have h9 := h y v1 v1
  T (T (T h7 h6) (h x y y)) (C (C (T (C (T (T (T (C (T h9 h8) h3) h2) h9) h8) h3) h2) h0) h0)

@[equational_result]
theorem Equation3161_implies_Equation2132 (G: Type _) [Magma G] (h: Equation3161 G) : Equation2132 G := fun x y z =>
  let v0 := M z z
  have h1 := T (C (h y z v0) (R y)) (S (h v0 v0 y))
  let v2 := M y y
  let v3 := M v2 x
  have h4 := R v3
  have h5 := h v3 z v0
  have h6 := h v0 v0 v3
  have h7 := R v0
  T (h x v3 v2) (C (T (C (T (T (T (T (T (C (R (M v3 v3)) h1) (C (T (C h5 h4) (S h6)) h7)) (C (h v0 z v0) h7)) (S (h v0 v0 v0))) h6) (C (S h5) h4)) (R x)) (S (h v3 y x))) h1)

@[equational_result]
theorem Equation522_implies_Equation4421 (G: Type _) [Magma G] (h: Equation522 G) : Equation4421 G := fun x y z =>
  let v0 := M z y
  let v1 := M x y
  have h2 := R v1
  let v3 := M x v1
  have h4 := h v1 v3 v3
  have h5 := h x v3 v1
  have h6 := R v3
  have h7 := R x
  T (T (T (T (T (h v3 v1 v3) (C h2 (T (C h2 (T (T (T (C h6 (C h6 (C h7 (T h4 (C h6 (S h5)))))) (S (h v3 v3 x))) (h v3 v1 x)) (C h2 (C h2 (C h7 (T (C h6 h5) (S h4))))))) (S (h x v1 v1))))) (C h2 (h x v1 y))) (S (h y v1 v1))) (h y v0 v0)) (C (R v0) (S (h z v0 y)))

@[equational_result]
theorem Equation911_implies_Equation2 (G: Type _) [Magma G] (h: Equation911 G) : Equation2 G := fun x y =>
  let v0 := M x x
  have h1 := R v0
  let v2 := M x y
  have h3 := R x
  let v4 := M x v2
  have h5 := R v2
  have h6 := h x x y
  let v7 := M v0 v2
  let v8 := M x v0
  T (T (T (T (T (T (h x x x) (C h3 (C (h v0 x y) h1))) (S (h (M v8 v2) x x))) (C (T (T (h v8 x x) (C h3 (C (T (T (T (C h3 (C h6 h1)) (S (h v7 x x))) (h v7 x y)) (C h3 (C (S h6) h5))) h1))) (S (h v4 x x))) h5)) (h (M v4 v2) x x)) (C h3 (C (S (h v2 x y)) h1))) (S (h y x x))

@[equational_result]
theorem Equation1929_implies_Equation3297 (G: Type _) [Magma G] (h: Equation1929 G) : Equation3297 G := fun x y z =>
  let v0 := M z (M z y)
  let v1 := M y v0
  have h2 := R (M v1 v1)
  have h3 := h v0 v0 x
  let v4 := M x x
  have h5 := R v4
  have h6 := h y z v0
  have h7 := R y
  have h8 := S (h v4 y x)
  have h9 := C h7 (T h3 (C (S h6) h5))
  T (T (h v4 v1 v1) (C (T (T (T (C h9 (T (C h9 h5) h8)) h8) (h v4 y v1)) (C (C h7 (T (C h6 h5) (S h3))) h2)) h2)) (S (h v1 v1 v1))

@[equational_result]
theorem Equation3992_implies_Equation41 (G: Type _) [Magma G] (h: Equation3992 G) : Equation41 G := fun x y z =>
  let v0 := M x x
  have h1 := h y z v0
  let v2 := M y z
  have h3 := R v2
  have h4 := h x x v2
  have h5 := S h4
  let v6 := M v2 v0
  have h7 := R v6
  have h8 := C (T (T (C (C (R x) h4) h7) (S (h v6 x x))) h5) h3
  have h9 := h v2 v0 (M x v0)
  T (T (T (T (T h4 (h v6 x v2)) (C (C h3 h5) h7)) (C (T (T h9 h8) (C (R v0) h1)) (T h9 h8))) (S (h (M v0 v2) y v0))) (S h1)

@[equational_result]
theorem Equation2740_implies_Equation2 (G: Type _) [Magma G] (h: Equation2740 G) : Equation2 G := fun x y =>
  have h0 := R x
  let v1 := M y y
  let v2 := M x x
  have h3 := R v2
  have h4 := h x y y
  have h5 := R v1
  let v6 := M v1 (M x y)
  let v7 := M v6 y
  T (T (T (T (T (T (h x x x) (C (C h3 (h v2 y x)) h0)) (S (h (M v1 (M v2 x)) x y))) (C h5 (T (T (T (T (C h3 h4) (h (M v2 v7) x x)) (C (C h3 (T (S (h v6 x y)) (h v6 y y))) h0)) (S (h (M v1 v7) x y))) (C h5 (S h4))))) (h (M v1 (M v1 x)) x y)) (C (C h3 (S (h v1 y x))) h0)) (S (h y x y))

@[equational_result]
theorem Equation3383_implies_Equation41 (G: Type _) [Magma G] (h: Equation3383 G) : Equation41 G := fun x y z =>
  let v0 := M y z
  have h1 := h y z v0
  have h2 := S h1
  let v3 := M y (M z y)
  have h4 := R v3
  have h5 := R z
  let v6 := M x x
  have h7 := R x
  T (T (T (T (h x x z) (C h5 (T (T (T (T (h x v6 v3) (C h4 (T (C h7 (T (h v6 x x) (C h7 (S (h x x v6))))) (S (h x x x))))) (h v3 v6 x)) (C h7 (T (C h4 (S (h y z v6))) (C h4 h1)))) (S (h v3 v0 x))))) (C h5 (T (h v3 v0 v0) (C (R v0) (C h4 h2))))) (S (h v0 v3 z))) h2

@[equational_result]
theorem Equation948_implies_Equation2 (G: Type _) [Magma G] (h: Equation948 G) : Equation2 G := fun x y =>
  let v0 := M x x
  have h1 := R v0
  let v2 := M y y
  have h3 := R x
  have h4 := R v2
  have h5 := h x y y
  let v6 := M (M y x) v2
  let v7 := M y v6
  T (T (T (T (T (T (h x x x) (C h3 (C (h v0 y x) h1))) (S (h (M (M x v0) v2) x y))) (C (T (T (T (T (C h5 h1) (h (M v7 v0) x x)) (C h3 (C (T (S (h v6 x y)) (h v6 y y)) h1))) (S (h (M v7 v2) x y))) (C (S h5) h4)) h4)) (h (M (M x v2) v2) x y)) (C h3 (C (S (h v2 y x)) h1))) (S (h y x y))

@[equational_result]
theorem Equation1773_implies_Equation2 (G: Type _) [Magma G] (h: Equation1773 G) : Equation2 G := fun x y =>
  have h0 := S (h y x y)
  have h1 := R x
  let v2 := M x y
  have h3 := R v2
  have h4 := h x x y
  let v5 := M x x
  let v6 := M v5 x
  let v7 := M v2 x
  T (T h4 (C h3 (C (T (T (h v5 y y) (C (R (M y y)) (C (T (T (h (M y v5) x y) (C h3 (C (T (T (T (C (h x x x) (C (h y x x) (R v5))) (S (h v7 v5 v6))) (h v7 v2 v6)) (C (S h4) (C h0 h3))) h1))) (S (h (M y v2) x y))) (R y)))) (S (h v2 y y))) h1))) h0

@[equational_result]
theorem Equation1901_implies_Equation2 (G: Type _) [Magma G] (h: Equation1901 G) : Equation2 G := fun x y =>
  have h0 := S (h y x y)
  let v1 := M y x
  have h2 := R v1
  have h3 := h x x y
  let v4 := M x x
  let v5 := M x v4
  let v6 := M x v1
  have h7 := R x
  T (T h3 (C (C h7 (T (T (h v4 y y) (C (C (R y) (T (T (h (M v4 y) x y) (C (C h7 (T (T (T (C (C (R v4) (h y x x)) (h x x x)) (S (h v6 v4 v5))) (h v6 v1 v5)) (C (C h2 h0) (S h3)))) h2)) (S (h (M v1 y) x y)))) (R (M y y)))) (S (h v1 y y)))) h2)) h0

@[equational_result]
theorem Equation2494_implies_Equation4647 (G: Type _) [Magma G] (h: Equation2494 G) : Equation4647 G := fun x y z =>
  let v0 := M (M z y) z
  let v1 := M (M v0 v0) v0
  have h2 := h v0 v1
  have h3 := R x
  have h4 := R v0
  have h5 := R z
  let v6 := M (M y y) y
  have h7 := h y v6
  have h8 := S h7
  T (T (C (C h3 (T (T (T (T h7 (h (M (M v6 v6) v6) v0)) (C (C h4 (T (T (T (C (C h8 h8) h8) (h v6 z)) (C (C h5 h8) h5)) h2)) h4)) (S (h v1 v0))) (C (C h2 h2) h2))) h3) (S (h (M (M v1 v1) v1) x))) (S h2)

@[equational_result]
theorem Equation3550_implies_Equation41 (G: Type _) [Magma G] (h: Equation3550 G) : Equation41 G := fun x y z =>
  let v0 := M x x
  have h1 := h y z v0
  let v2 := M y z
  let v3 := M v2 v0
  have h4 := h x x v2
  have h5 := S h4
  let v6 := M v0 v2
  have h7 := R v6
  have h8 := R v2
  have h9 := T (h v0 v2 (M v0 x)) (C h8 (T (T (C h7 (C h4 (R x))) (S (h x v6 x))) h5))
  T (T (T (T (T (T h4 (h x v6 v2)) (C h7 (C h5 h8))) (C h9 h9)) (C (R v3) (C h1 (R v0)))) (S (h z v3 v0))) (S h1)

@[equational_result]
theorem Equation543_implies_Equation1964 (G: Type _) [Magma G] (h: Equation543 G) : Equation1964 G := fun x y z =>
  let v0 := M y (M z x)
  let v1 := M v0 (M y z)
  have h2 := h y z v1
  have h3 := S h2
  have h4 := h v0 y z
  have h5 := R v1
  have h6 := R z
  have h7 := C h6 (C h5 h4)
  have h8 := R v0
  T (T (h x v0 y) (C h8 (C (R y) (T (T (T (C (R x) (T (C h8 (T h2 (C h6 (C h5 (S h4))))) (C h8 (T (T h7 h3) (h y z x))))) (S (h z x v0))) (h z v1 v0)) (C h5 (C h8 (T h7 h3))))))) (S (h v1 v0 y))

@[equational_result]
theorem Equation1097_implies_Equation2 (G: Type _) [Magma G] (h: Equation1097 G) : Equation2 G := fun x y =>
  let v0 := M x y
  let v1 := M x v0
  have h2 := R y
  have h3 := R v0
  let v4 := M x x
  have h5 := h x x (M x v4)
  have h6 := R x
  have h7 := h x x x
  have h8 := h x x (M y v4)
  have h9 := h y x x
  T (T (T (T h8 (C h6 (C (S h9) h6))) (h (M x (M y x)) y x)) (C h2 (C (T (T (C (T (T (T (C h6 (C h9 h6)) (S h8)) h5) (C h6 (C (S h7) h6))) h3) (C (T (C h6 (C h7 h6)) (S h5)) h3)) (h v1 y x)) h2))) (S (h y y (M v1 v0)))

@[equational_result]
theorem Equation1503_implies_Equation2 (G: Type _) [Magma G] (h: Equation1503 G) : Equation2 G := fun x y =>
  let v0 := M x x
  let v1 := M x v0
  let v2 := M y y
  have h3 := S (h v2 y y)
  let v4 := M y v2
  have h5 := h v0 x x
  have h6 := R y
  have h7 := h x x y
  T (T (T (T (T h7 (C (T (h v0 y y) (C (T (T (T (T (T (h (M y v0) v1 y) (C (S (h v0 x y)) (C h6 (S h5)))) (S h7)) (h x x x)) (C h5 (C (R x) h5))) (S (h v1 v1 x))) (R v4))) (C h6 h5))) (S (h v4 v1 y))) (h v4 v4 v1)) (C h3 (C (R v1) h3))) (S (h y y v1))

@[equational_result]
theorem Equation2551_implies_Equation2 (G: Type _) [Magma G] (h: Equation2551 G) : Equation2 G := fun x y =>
  let v0 := M y x
  let v1 := M v0 x
  have h2 := R y
  let v3 := M x x
  have h4 := h x x (M v3 x)
  have h5 := R x
  have h6 := h x x x
  have h7 := R v0
  have h8 := h x x (M v3 y)
  have h9 := h y x x
  T (T (T (T h8 (C (C h5 (S h9)) h5)) (h (M (M x y) x) y x)) (C (C h2 (T (T (C h7 (T (T (T (C (C h5 h9) h5) (S h8)) h4) (C (C h5 (S h6)) h5))) (C h7 (T (C (C h5 h6) h5) (S h4)))) (h v1 y x))) h2)) (S (h y y (M v0 v1)))

@[equational_result]
theorem Equation1967_implies_Equation2586 (G: Type _) [Magma G] (h: Equation1967 G) : Equation2586 G := fun x y z =>
  let v0 := M z y
  let v1 := M v0 x
  let v2 := M y v1
  let v3 := M v2 z
  have h4 := R v3
  let v5 := M v2 v1
  have h6 := S (h x y z)
  T (T (h x v2 v0) (C (C (R v2) (T (h v1 z v2) (C (C (R z) (T (T (h v5 v3 v0) (C (C h4 (T (C (T (T (h v0 v0 (M y (M z x))) (C (C (R v0) h6) h6)) (C (R v1) (h x y v0))) (R v5)) (S (h (M v0 y) v1 v2)))) (R (M v0 v3)))) (S (h y v3 v0)))) h4))) (R (M v0 v2)))) (S (h v3 v2 v0))

@[equational_result]
theorem Equation2145_implies_Equation2 (G: Type _) [Magma G] (h: Equation2145 G) : Equation2 G := fun x y =>
  let v0 := M x x
  let v1 := M v0 x
  let v2 := M y y
  have h3 := S (h v2 y y)
  let v4 := M v2 y
  have h5 := h v0 x x
  have h6 := h x x y
  have h7 := R y
  T (T (T (T (T h6 (C (C h5 h7) (T (h v0 y y) (C (R v4) (T (T (T (T (T (h (M v0 y) v1 y) (C (C (S h5) h7) (S (h v0 x y)))) (S h6)) (h x x x)) (C (C h5 (R x)) h5)) (S (h v1 v1 x))))))) (S (h v4 v1 y))) (h v4 v4 v1)) (C (C h3 (R v1)) h3)) (S (h y y v1))

@[equational_result]
theorem Equation2714_implies_Equation1171 (G: Type _) [Magma G] (h: Equation2714 G) : Equation1171 G := fun x y z =>
  let v0 := M y z
  let v1 := M z v0
  let v2 := M v1 x
  let v3 := M y v2
  have h4 := R v2
  let v5 := M v0 v3
  have h6 := S (h y x v0)
  T (T (h x v0 v2) (C (C (T (T (T (C (h v0 z v2) (R x)) (S (h (M z v2) v1 x))) (C (T (h z v0 v3) (C (C (T (C (T (h v0 (M (M x y) (M x v0)) v0) (C (C h6 h6) (R v0))) (R z)) (S (h y y z))) (R v5)) (R v3))) h4)) (S (h v5 y v2))) (R (M v0 v2))) h4)) (S (h v3 v0 v2))

@[equational_result]
theorem Equation3159_implies_Equation218 (G: Type _) [Magma G] (h: Equation3159 G) : Equation218 G := fun x y =>
  have h0 := R x
  let v1 := M x x
  have h2 := h x x v1
  have h3 := h x v1 x
  let v4 := M y v1
  have h5 := S (h y v4 y)
  have h6 := R y
  have h7 := R v4
  have h8 := C (C (C (T (C (T (h v4 x x) (C (T (C (C (T (C h2 h0) (S h3)) h0) h7) (R (M v1 v4))) h7)) h7) (S (h v4 x v4))) h7) h6) h6
  have h9 := h y v4 v4
  T (h x y y) (C (C (T (C (T (T (T (C (T h9 h8) h6) h5) h9) h8) h6) h5) (T h3 (C (S h2) h0))) h0)

@[equational_result]
theorem Equation3607_implies_Equation3526 (G: Type _) [Magma G] (h: Equation3607 G) : Equation3526 G := fun x y z =>
  let v0 := M y z
  let v1 := M v0 z
  let v2 := M x v1
  let v3 := M v1 z
  have h4 := R z
  have h5 := R v2
  have h6 := h y z v1
  let v7 := M (M z v1) y
  T (T (T (T (h x y z) (h z (M v0 x) v2)) (C h5 (C (C (T (T (h v0 x v2) (C h5 (C (R (M x v2)) (T (T (T h6 (h v1 v7 v0)) (C (R v0) (C (T (h v7 v0 z) (C h4 (S h6))) (R v1)))) (S (h v1 z v0)))))) (S (h v3 x v2))) h5) h4))) (S (h z (M v3 x) v2))) (S (h x v1 z))

@[equational_result]
theorem Equation1073_implies_Equation4332 (G: Type _) [Magma G] (h: Equation1073 G) : Equation4332 G := fun x y z =>
  let v0 := M z (M y z)
  let v1 := M v0 (M v0 v0)
  have h2 := h v0 v1
  have h3 := R x
  have h4 := R v0
  have h5 := R z
  let v6 := M y (M y y)
  have h7 := h y v6
  have h8 := S h7
  T (T (C h3 (C (T (T (T (T h7 (h (M v6 (M v6 v6)) v0)) (C h4 (C (T (T (T (C h8 (C h8 h8)) (h v6 z)) (C h5 (C h8 h5))) h2) h4))) (S (h v1 v0))) (C h2 (C h2 h2))) h3)) (S (h (M v1 (M v1 v1)) x))) (S h2)

@[equational_result]
theorem Equation2171_implies_Equation2 (G: Type _) [Magma G] (h: Equation2171 G) : Equation2 G := fun x y =>
  let v0 := M x x
  let v1 := M y y
  let v2 := M v1 y
  have h3 := R (M v0 v0)
  let v4 := M x y
  have h5 := h v0 v0 v4
  have h6 := R (M v4 v4)
  have h7 := h v4 x x
  have h8 := h v4 x y
  have h9 := h v1 v4 v4
  T (T (T (h x (M v0 x) v0) (C (C (S (h x x x)) (R x)) h3)) (C (T (T (T (T h5 (C (S h7) h6)) (C h8 h6)) (S h9)) (C (T (h y y y) (C (R v2) (T (T (T h9 (C (S h8) h6)) (C h7 h6)) (S h5)))) (R y))) h3)) (S (h y v2 v0))

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
theorem Equation2146_implies_Equation1496 (G: Type _) [Magma G] (h: Equation2146 G) : Equation1496 G := fun x y z =>
  let v0 := M z z
  let v1 := M y v0
  let v2 := M y x
  let v3 := M v2 v1
  let v4 := M (M v3 v3) v0
  let v5 := M x x
  let v6 := M v5 v3
  T (T (h x y x) (C (T (T (h (M (M y y) x) x v2) (C (R (M v5 v2)) (T (T (S (h y y x)) (h y x v3)) (C (R v6) (T (C (h y z v0) (R v3)) (S (h v2 v0 v1))))))) (S (h v6 x v2))) (T (T (T (C (h x z v0) (h x v3 v0)) (S (h v4 v0 (M x v0)))) (h v4 v0 (M v3 v0))) (C (S (h v3 z v0)) (S (h v3 v3 v0)))))) (S (h v3 x v3))

