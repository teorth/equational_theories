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
theorem Equation1913_implies_Equation2776 (G: Type _) [Magma G] (h: Equation1913 G) : Equation2776 G := fun x y z =>
  let v0 := M x y
  let v1 := M y z
  let v2 := M v1 v0
  let v3 := M v2 z
  let v4 := M z v0
  T (T (h x v3 v2) (C (C (R v3) (T (C (T (h x z y) (C (R v4) (h v1 v3 v0))) (h v2 v0 z)) (S (h (M v3 v2) v4 (M v0 v3))))) (R (M v2 v3)))) (S (h v3 v3 v2))

@[equational_result]
theorem Equation1977_implies_Equation692 (G: Type _) [Magma G] (h: Equation1977 G) : Equation692 G := fun x y z =>
  let v0 := M z y
  let v1 := M v0 z
  let v2 := M x v1
  let v3 := M y v2
  let v4 := M v3 (M v1 v3)
  T (h x v3 v1) (C (T (T (h v4 x v0) (C (R (M x (M v0 x))) (T (C (R v4) (h v0 y z)) (S (h (M y v0) v3 v1))))) (S (h y x v0))) (R v2))

@[equational_result]
theorem Equation2585_implies_Equation2 (G: Type _) [Magma G] (h: Equation2585 G) : Equation2 G := fun x y =>
  let v0 := M x y
  let v1 := M y (M v0 x)
  have h2 := R y
  let v3 := M x (M (M x x) x)
  T (T (T (h x y (M y (M v0 v3))) (C (C h2 (T (C (S (h v3 y x)) (R x)) (S (h x x x)))) h2)) (C (C h2 (T (h x y x) (C (h v1 y x) h2))) h2)) (S (h y y (M y (M v0 v1))))

@[equational_result]
theorem Equation2605_implies_Equation31 (G: Type _) [Magma G] (h: Equation2605 G) : Equation31 G := fun x y =>
  let v0 := M x (M (M x x) x)
  let v1 := M y y
  have h2 := R v1
  have h3 := R y
  have h4 := h v0 x x
  T (h x v1 v0) (C (T (T (C h2 (T (C (S h4) h2) (S (h v1 x x)))) (C (C h3 (T (h y x x) (C h4 h3))) h2)) (S (h v1 y v0))) (R x))

@[equational_result]
theorem Equation3145_implies_Equation312 (G: Type _) [Magma G] (h: Equation3145 G) : Equation312 G := fun x y =>
  let v0 := M x x
  have h1 := R v0
  have h2 := R y
  have h3 := S (h v0 v0 v0)
  have h4 := C (h v0 x v0) h1
  have h5 := C (T h4 h3) h1
  have h6 := h v0 v0 y
  T h6 (C (T (C (T (T (T (T h5 h4) h3) h6) (C (C (T (T h5 h4) h3) h2) h1)) h2) (S (h y x v0))) h1)

@[equational_result]
theorem Equation3350_implies_Equation3979 (G: Type _) [Magma G] (h: Equation3350 G) : Equation3979 G := fun x y z =>
  let v0 := M x x
  let v1 := M z z
  let v2 := M y v1
  let v3 := M y v0
  let v4 := M x (M v2 v2)
  T (T (T (T (T (T (h x y v2) (h y v4 z)) (C (R v4) (T (h y v1 x) (h v1 v3 z)))) (S (h v3 v4 v1))) (S (h x v3 v2))) (C (R x) (T (h y v0 z) (h v0 v2 x)))) (S (h v2 x v0))

@[equational_result]
theorem Equation3363_implies_Equation3431 (G: Type _) [Magma G] (h: Equation3363 G) : Equation3431 G := fun x y z w =>
  let v0 := M x y
  let v1 := M w v0
  have h2 := R v1
  have h3 := h x y w
  T (T (T (T h3 (h y v1 x)) (C h2 (T (T (T (C (R x) (S h3)) (h x v0 y)) (C (R v0) (T (S (h x y x)) h3))) (S (h w v0 y))))) (C h2 (h w v0 z))) (S (h z v1 v0))

@[equational_result]
theorem Equation3370_implies_Equation3526 (G: Type _) [Magma G] (h: Equation3370 G) : Equation3526 G := fun x y z =>
  let v0 := M y z
  let v1 := M v0 z
  let v2 := M x v1
  let v3 := M v2 (M v2 x)
  have h4 := R y
  T (T (T (T (h x y v2) (h y v3 y)) (C (R v3) (C h4 (T (h y y z) (C h4 (T (C (R z) (h z y y)) (S (h v0 z y)))))))) (S (h v1 v3 y))) (S (h x v1 v2))

@[equational_result]
theorem Equation3770_implies_Equation3537 (G: Type _) [Magma G] (h: Equation3770 G) : Equation3537 G := fun x y z =>
  let v0 := M z z
  have h1 := h z z z
  have h2 := S h1
  let v3 := M y v0
  have h4 := R v3
  T (T (h x y v0) (C (T (T (T (h y v0 v0) (C h2 h4)) (h v0 v3 v0)) (C (T (C h4 h1) (S (h v0 y v0))) h2)) (R (M x v0)))) (S (h x (M v0 y) v0))

@[equational_result]
theorem Equation3791_implies_Equation4620 (G: Type _) [Magma G] (h: Equation3791 G) : Equation4620 G := fun x y z =>
  let v0 := M z y
  let v1 := M y v0
  let v2 := M x x
  let v3 := M v0 v2
  T (T (T (T (T (T (h v2 y v0) (h v3 v1 v2)) (C (T (C (h x x x) (R v3)) (S (h v2 v0 v2))) (R (M v1 v2)))) (S (h v0 v1 v2))) (C (h z y v0) (h y v0 z))) (S (h v1 v0 (M v0 z)))) (S (h v0 z y))

@[equational_result]
theorem Equation3979_implies_Equation3537 (G: Type _) [Magma G] (h: Equation3979 G) : Equation3537 G := fun x y z =>
  let v0 := M z z
  let v1 := M v0 v0
  have h2 := R v1
  let v3 := M y (M x x)
  have h4 := h y v0 z
  T (T (h x y z) (C (T (T (T (T (T h4 (h v1 y z)) (C (T h4 (h v1 y x)) h2)) (S (h v1 v3 v0))) (h v1 v3 z)) (C (S (h v0 y x)) h2)) (R x))) (S (h x (M v0 y) v0))

@[equational_result]
theorem Equation4013_implies_Equation3364 (G: Type _) [Magma G] (h: Equation4013 G) : Equation3364 G := fun x y z =>
  let v0 := M z (M x z)
  have h1 := R y
  let v2 := M x (M x x)
  let v3 := M v0 (M y v0)
  T (T (T (T (T (T (h x y v0) (h v3 x x)) (h v2 v3 y)) (C (C h1 (S (h y y v0))) (R v2))) (S (h v2 y y))) (C (C (R x) (h x x z)) h1)) (S (h y v0 x))

@[equational_result]
theorem Equation4182_implies_Equation3364 (G: Type _) [Magma G] (h: Equation4182 G) : Equation3364 G := fun x y z =>
  let v0 := M x z
  have h1 := R y
  let v2 := M v0 z
  let v3 := M x y
  let v4 := M (M y v3) v3
  T (T (T (T (T (T (h x y v3) (h v4 x z)) (h v2 v4 y)) (C (C (S (h y y v3)) h1) (R v2))) (S (h v2 y y))) (C (h v0 z v0) h1)) (S (h y (M z v0) v0))

@[equational_result]
theorem Equation4216_implies_Equation4026 (G: Type _) [Magma G] (h: Equation4216 G) : Equation4026 G := fun x y z =>
  have h0 := R x
  let v1 := M z y
  let v2 := M z v1
  let v3 := M v2 z
  let v4 := M v1 y
  T (T (T (T (h x y v1) (C (T (h v4 v1 z) (C (T (h v2 z v1) (C (S (h v1 y z)) (R v2))) (R v4))) h0)) (S (h x v2 v4))) (h x v2 v3)) (C (T (S (h v3 z v2)) (S (h z v1 z))) h0)

@[equational_result]
theorem Equation1165_implies_Equation1876 (G: Type _) [Magma G] (h: Equation1165 G) : Equation1876 G := fun x y z =>
  let v0 := M x (M y z)
  let v1 := M v0 (M z y)
  have h2 := R y
  have h3 := R v1
  T (T (h x v0 y) (C (R v0) (C (T (T (S (h z y x)) (h z y v1)) (C h2 (C (T (C h3 (C (h y z v0) (R z))) (S (h v0 v1 z))) h3))) h2))) (S (h v1 v0 y))

@[equational_result]
theorem Equation1561_implies_Equation4544 (G: Type _) [Magma G] (h: Equation1561 G) : Equation4544 G := fun x y z =>
  let v0 := M z y
  have h1 := R v0
  let v2 := M y z
  let v3 := M x v2
  have h4 := h v3 z y
  let v5 := M v2 v3
  T (T h4 (C h1 (T (h (M v3 v2) v5 v3) (C (T (C (R v5) h4) (S (h v0 v2 v3))) (S (h v3 v3 v2)))))) (C h1 (S (h x z y)))

@[equational_result]
theorem Equation1726_implies_Equation4098 (G: Type _) [Magma G] (h: Equation1726 G) : Equation4098 G := fun x y z =>
  let v0 := M y y
  let v1 := M (M v0 z) z
  have h2 := h v0 y z
  have h3 := T h2 (C h2 (R v1))
  let v4 := M x x
  T (T (h v4 z v0) (C (R (M z z)) (T (T (C (T (C (R v4) h3) (S (h v0 x v1))) h3) (S (h v0 y v1))) (h v0 v1 z)))) (S (h v1 z v1))

@[equational_result]
theorem Equation2076_implies_Equation2891 (G: Type _) [Magma G] (h: Equation2076 G) : Equation2891 G := fun x y z =>
  let v0 := M y z
  let v1 := M x v0
  let v2 := M (M v1 z) y
  have h3 := h v2 v0 y
  let v4 := M v0 y
  let v5 := M z y
  T (T (h x v0 y) (C (T (C (T (h v1 z y) (C h3 (R v5))) (h y z y)) (S (h (M (M v2 v0) y) v4 v5))) (R v4))) (S h3)

@[equational_result]
theorem Equation3131_implies_Equation692 (G: Type _) [Magma G] (h: Equation3131 G) : Equation692 G := fun x y z =>
  let v0 := M z y
  let v1 := M v0 z
  let v2 := M x v1
  let v3 := M y v2
  have h4 := R v3
  T (h x v2 x) (C (T (T (T (S (h v1 x x)) (h v1 z v3)) (C (C (C (T (C (h z v0 v0) (R v1)) (S (h v0 v1 v0))) h4) h4) (R z))) (S (h y z v3))) (R v2))

@[equational_result]
theorem Equation3350_implies_Equation4497 (G: Type _) [Magma G] (h: Equation3350 G) : Equation4497 G := fun x y z =>
  let v0 := M z z
  let v1 := M v0 v0
  let v2 := M x (M x x)
  have h3 := R v2
  let v4 := M y y
  T (T (T (T (T (T (T (T (h x v4 x) (h v4 v2 v0)) (C h3 (S (h v0 v4 z)))) (S (h v0 v2 y))) (h v0 v2 v0)) (C h3 (h v0 v1 z))) (S (h v1 v2 v0))) (S (h x v1 x))) (S (h v0 x z))

@[equational_result]
theorem Equation1165_implies_Equation725 (G: Type _) [Magma G] (h: Equation1165 G) : Equation725 G := fun x y z =>
  let v0 := M z x
  let v1 := M y (M v0 z)
  let v2 := M y v1
  have h3 := R v2
  have h4 := R v1
  have h5 := R z
  T (T (h x z v2) (C h5 (C (C h3 (T (h v0 z v1) (C h5 (C (T (C h4 (C (h z v0 y) (R v0))) (S (h y v1 v0))) h4)))) h3))) (S (h v2 z v2))

@[equational_result]
theorem Equation1266_implies_Equation378 (G: Type _) [Magma G] (h: Equation1266 G) : Equation378 G := fun x y =>
  let v0 := M (M (M x x) x) x
  have h1 := S (h y x v0)
  have h2 := R y
  have h3 := h x x x
  have h4 := C h2 (C (T h3 (C h3 (R v0))) h2)
  let v5 := M x y
  have h6 := R v5
  T (h v5 y v5) (C h6 (T (T (C (T (T (C (T h4 h1) h6) h4) h1) h6) h4) h1))

@[equational_result]
theorem Equation1275_implies_Equation3451 (G: Type _) [Magma G] (h: Equation1275 G) : Equation3451 G := fun x y z w u =>
  let v0 := M u y
  let v1 := M (M (M v0 v0) v0) v0
  let v2 := M (M (M y y) y) y
  have h3 := h y (M (M v2 v2) v2)
  T (T (T (T (T (C (R x) h3) (S (h v2 x))) (h v2 u)) (C (R u) (S h3))) (h v0 z)) (C (R z) (T (h v1 w) (C (R w) (S (h v0 (M (M v1 v1) v1))))))

@[equational_result]
theorem Equation1537_implies_Equation14 (G: Type _) [Magma G] (h: Equation1537 G) : Equation14 G := fun x y =>
  let v0 := M x x
  let v1 := M y (M x y)
  have h2 := h x x y
  have h3 := R v1
  have h4 := R v0
  T (T h2 (C h4 (T (h v1 x v1) (C h4 (C h3 (T (T (h (M v1 v1) x v1) (C h4 (T (C h3 (S (h x v1 y))) (C h3 h2)))) (S (h v0 x v1)))))))) (S (h v1 x v0))

@[equational_result]
theorem Equation1537_implies_Equation31 (G: Type _) [Magma G] (h: Equation1537 G) : Equation31 G := fun x y =>
  let v0 := M x x
  have h1 := h y y y
  have h2 := R v0
  let v3 := M y y
  have h4 := R v3
  T (h x y v3) (C h4 (T (C h4 (C (R x) (T (T (h v3 x y) (C h2 (C (R y) (T (T (T (C h4 h1) (S (h y y v3))) (h y x v3)) (C h2 (S h1)))))) (S (h v0 x y))))) (S (h x y x))))

@[equational_result]
theorem Equation2170_implies_Equation4544 (G: Type _) [Magma G] (h: Equation2170 G) : Equation4544 G := fun x y z =>
  let v0 := M z y
  let v1 := M v0 x
  have h2 := S (h v1 z y)
  let v3 := M y z
  have h4 := R v3
  let v5 := M v1 v0
  T (T (C (h x z y) h4) (C (T (C (h v1 v1 v0) (T (h v3 v0 v1) (C h2 (R v5)))) (S (h (M v0 v1) v5 v1))) h4)) h2

@[equational_result]
theorem Equation2958_implies_Equation16 (G: Type _) [Magma G] (h: Equation2958 G) : Equation16 G := fun x y =>
  let v0 := M y x
  let v1 := M y v0
  let v2 := M v1 v0
  have h3 := S (h v1 x v1)
  let v4 := M (M x (M x v1)) v1
  T (T (h x v1 v0) (C (T (T (S (h v2 y x)) (h v2 v4 v1)) (C (C (T (C (R v4) h3) h3) (R v2)) (R v1))) (R v0))) (S (h v1 v1 v0))

@[equational_result]
theorem Equation3128_implies_Equation749 (G: Type _) [Magma G] (h: Equation3128 G) : Equation749 G := fun x y z =>
  let v0 := M (M x z) y
  let v1 := M z v0
  let v2 := M y v1
  have h3 := R y
  T (T (h x v0 y) (C (C (T (T (S (h z x y)) (h z v2 y)) (C (C (T (C (C (T (h v2 v2 y) (C (S (h v1 y v2)) h3)) (R z)) h3) (S (h v0 z y))) (R v2)) h3)) (R v0)) h3)) (S (h v2 v0 y))

@[equational_result]
theorem Equation3364_implies_Equation4013 (G: Type _) [Magma G] (h: Equation3364 G) : Equation4013 G := fun x y z =>
  let v0 := M y z
  let v1 := M z v0
  have h2 := R v1
  let v3 := M y (M x y)
  T (T (T (T (T (T (h x y y) (h y v3 v1)) (C (R v3) (C h2 (h y v1 z)))) (S (h v1 v3 v1))) (S (h x v1 y))) (C (R x) (T (h z v0 v1) (C (R v0) (C h2 (S (h y z z))))))) (S (h v1 x v0))

@[equational_result]
theorem Equation3718_implies_Equation3935 (G: Type _) [Magma G] (h: Equation3718 G) : Equation3935 G := fun x y z =>
  let v0 := M z x
  let v1 := M x v0
  let v2 := M v1 v1
  let v3 := M x y
  let v4 := M x x
  T (T (T (T (T (h x y x) (R (M v4 v3))) (C (T (T (h x x y) (C (R v4) (h y x z))) (S (h x v0 (M y y)))) (R v3))) (h v1 v3 v2)) (C (R v2) (S (h v1 y x)))) (S (h v1 y v1))

@[equational_result]
theorem Equation3810_implies_Equation3323 (G: Type _) [Magma G] (h: Equation3810 G) : Equation3323 G := fun x y z =>
  let v0 := M z z
  let v1 := M v0 y
  have h2 := R v1
  have h3 := h z z z
  have h4 := S h3
  T (T (h x y v0) (C (T (T (T (h v0 y v0) (C h2 h4)) (h v1 v0 v0)) (C h4 (T (C h3 h2) (S (h y v0 v0))))) (R (M v0 x)))) (S (h x (M y v0) v0))

@[equational_result]
theorem Equation3810_implies_Equation3943 (G: Type _) [Magma G] (h: Equation3810 G) : Equation3943 G := fun x y z =>
  let v0 := M z z
  let v1 := M v0 x
  have h2 := R v1
  have h3 := h z z z
  have h4 := S h3
  T (T (h x y v0) (C (R (M v0 y)) (T (T (T (h v0 x v0) (C h2 h4)) (h v1 v0 v0)) (C h4 (T (C h3 h2) (S (h x v0 v0))))))) (S (h (M x v0) y v0))

@[equational_result]
theorem Equation4162_implies_Equation4007 (G: Type _) [Magma G] (h: Equation4162 G) : Equation4007 G := fun x y z =>
  have h0 := R z
  let v1 := M y x
  have h2 := S (h x y v1)
  let v3 := M v1 v1
  have h4 := R y
  T (T (T (h x y v3) (C (T (T (h v1 v3 y) (C (C h2 h4) h4)) (S (h y x y))) (R v3))) (h v1 v3 z)) (C (T (C (T h2 (h x y z)) h0) (S (h z v1 z))) h0)

@[equational_result]
theorem Equation4210_implies_Equation4146 (G: Type _) [Magma G] (h: Equation4210 G) : Equation4146 G := fun x y z =>
  let v0 := M x z
  let v1 := M v0 z
  let v2 := M v0 y
  T (T (T (T (h x y v0) (h (M v2 x) v0 x)) (C (C (R (M x v0)) (T (T (h v2 x v0) (C (C (T (h v0 x v1) (C (S (h x z v0)) (R v1))) (R v2)) (R v0))) (S (h v2 v1 v0)))) (R x))) (S (h (M v2 v1) v0 x))) (S (h v1 y v0))

@[equational_result]
theorem Equation3128_implies_Equation775 (G: Type _) [Magma G] (h: Equation3128 G) : Equation775 G := fun x y z =>
  let v0 := M z x
  let v1 := M v0 y
  let v2 := M z v1
  let v3 := M y v2
  have h4 := R y
  T (T (T (h x v1 y) (C (C (T (C (C (C (T (h v0 v0 z) (C (S (h x z v0)) (R z))) h4) (R x)) h4) (S (h z x y))) (R v1)) h4)) (C (h v2 y v3) h4)) (S (h v3 v3 y))

@[equational_result]
theorem Equation3212_implies_Equation2 (G: Type _) [Magma G] (h: Equation3212 G) : Equation2 G := fun x y =>
  let v0 := M (M x y) y
  let v1 := M x x
  let v2 := M v1 x
  have h3 := R x
  have h4 := S (h x v1 x)
  T (T (h x (M v2 x) x) (C (T (T (C h4 h3) (h v1 x y)) (C (C (h v0 x x) (T (C (h x x x) h3) h4)) (R y))) h3)) (S (h y (M v2 v0) x))

@[equational_result]
theorem Equation3770_implies_Equation4612 (G: Type _) [Magma G] (h: Equation3770 G) : Equation4612 G := fun x y z =>
  let v0 := M y z
  let v1 := M v0 z
  let v2 := M x x
  let v3 := M z x
  have h4 := h x z x
  T (T (T (T (h v2 y v0) (C (h y v0 z) (R (M v2 v0)))) (S (h v2 v1 v0))) (C (T (T (T (h x x z) (C h4 h4)) (S (h v3 v3 v2))) (S (h z z x))) (R v1))) (S (h v0 z z))

@[equational_result]
theorem Equation3791_implies_Equation3294 (G: Type _) [Magma G] (h: Equation3791 G) : Equation3294 G := fun x y z =>
  let v0 := M y z
  let v1 := M z v0
  let v2 := M y v1
  T (T (T (T (T (T (h x x v2) (h (M v2 x) (M x v2) (M x x))) (C (S (h x v2 x)) (S (h v2 x x)))) (S (h v2 v2 x))) (h v2 v2 (M v0 y))) (C (T (C (h v0 y z) (R v2)) (S (h v0 y v1))) (S (h v1 v0 y)))) (S (h y v1 v0))

@[equational_result]
theorem Equation3791_implies_Equation4325 (G: Type _) [Magma G] (h: Equation3791 G) : Equation4325 G := fun x y z =>
  let v0 := M y x
  let v1 := M z z
  let v2 := M v1 v0
  let v3 := M v0 y
  T (T (T (T (T (T (h x v0 y) (h v0 v3 (M x v0))) (C (S (h v0 y x)) (S (h y x v0)))) (h v3 v0 v1)) (C (R (M v1 v3)) (T (h v0 v1 v1) (C (R v2) (S (h z z z)))))) (S (h v3 v2 v1))) (S (h y v1 v0))

@[equational_result]
theorem Equation2105_implies_Equation3497 (G: Type _) [Magma G] (h: Equation2105 G) : Equation3497 G := fun x y z =>
  let v0 := M x x
  let v1 := M (M z y) z
  let v2 := M y v1
  have h3 := R v0
  T (T (T (h v0 x x) (C (C (T (C (h x x x) h3) (S (h x v0 x))) (R x)) h3)) (C (T (h v0 v2 x) (C (C (T (C (C (h y z x) (R v1)) h3) (S (h v0 v1 x))) (R v2)) h3)) h3)) (S (h v2 v0 x))

@[equational_result]
theorem Equation2239_implies_Equation4153 (G: Type _) [Magma G] (h: Equation2239 G) : Equation4153 G := fun x y z w u =>
  let v0 := M x z
  let v1 := M v0 (M v0 (M v0 v0))
  let v2 := M x (M x (M x x))
  have h3 := h x (M v2 (M v2 v2))
  T (T (T (T (T (C h3 (R y)) (S (h v2 y))) (h v2 z)) (C (S h3) (R z))) (h v0 u)) (C (T (h v1 w) (C (S (h v0 (M v1 (M v1 v1)))) (R w))) (R u))

@[equational_result]
theorem Equation3128_implies_Equation1117 (G: Type _) [Magma G] (h: Equation3128 G) : Equation1117 G := fun x y z =>
  let v0 := M x z
  let v1 := M y v0
  let v2 := M v1 z
  let v3 := M y v2
  have h4 := R y
  T (T (T (h x z y) (C (C (T (C (T (T (C (h z x v0) (R x)) (S (h v0 v0 x))) (h v0 y v1)) h4) (S (h v1 v1 y))) (R z)) h4)) (C (h v2 y v3) h4)) (S (h v3 v3 y))

@[equational_result]
theorem Equation3185_implies_Equation3973 (G: Type _) [Magma G] (h: Equation3185 G) : Equation3973 G := fun x y z =>
  let v0 := M z x
  let v1 := M y v0
  let v2 := M v1 z
  have h3 := R v1
  have h4 := R v2
  T (C (T (h x v1 v2) (C (C (T (T (C (T (C (h v1 v1 z) h4) (S (h z v2 v1))) (R x)) (h v0 v1 y)) (C (S (h y y v0)) h3)) h4) h3)) (R y)) (S (h v2 y v1))

@[equational_result]
theorem Equation3211_implies_Equation692 (G: Type _) [Magma G] (h: Equation3211 G) : Equation692 G := fun x y z =>
  let v0 := M z y
  let v1 := M v0 z
  let v2 := M x v1
  have h3 := R v2
  have h4 := R v0
  T (T (h x v2 v1) (C (S (h v1 x v1)) h3)) (C (T (C (T (h v0 y v0) (C (C (C (T (C (h y z y) h4) (S (h z v0 y))) h4) h4) (R y))) (R z)) (S (h y z v0))) h3)

@[equational_result]
theorem Equation3791_implies_Equation4497 (G: Type _) [Magma G] (h: Equation3791 G) : Equation4497 G := fun x y z =>
  let v0 := M z z
  let v1 := M x z
  let v2 := M z v0
  T (T (T (T (T (T (C (R x) (T (T (T (h y y z) (C (h z y z) (h y z z))) (S (h (M y z) (M z y) v0))) (S (h z z y)))) (h x v0 z)) (C (h z x z) (h v0 z z))) (S (h v1 v2 v0))) (C (h x z v0) (h z v0 x))) (S (h v2 v1 (M v0 x)))) (S (h v0 x z))

@[equational_result]
theorem Equation3810_implies_Equation4297 (G: Type _) [Magma G] (h: Equation3810 G) : Equation4297 G := fun x y z =>
  let v0 := M x y
  let v1 := M x v0
  let v2 := M x z
  have h3 := h z v0 x
  let v4 := M x x
  T (T (T (h x v0 x) (h v1 v4 v0)) (C (T (h v0 v4 v0) (C (S (h x y x)) (T (T (T (h v0 v0 z) (C h3 h3)) (S (h v2 v2 v1))) (S (h z z x))))) (S (h v0 y x)))) (S (h y (M z z) v0))

@[equational_result]
theorem Equation4085_implies_Equation4099 (G: Type _) [Magma G] (h: Equation4085 G) : Equation4099 G := fun x y z w =>
  let v0 := M x x
  let v1 := M v0 x
  have h2 := R v1
  have h3 := S (h x v0 x)
  have h4 := C (h x x v0) (R x)
  T (h x x w) (C (T (T (T h4 h3) (h x x z)) (C (T (T (T (T h4 h3) (h x v1 v1)) (C (C (T (S (h x x x)) (h x x y)) h2) h2)) (S (h y v1 v1))) (R z))) (R w))

@[equational_result]
theorem Equation4216_implies_Equation3567 (G: Type _) [Magma G] (h: Equation4216 G) : Equation3567 G := fun x y z =>
  let v0 := M z x
  let v1 := M v0 z
  have h2 := R v1
  let v3 := M (M y y) y
  T (T (T (T (T (T (h x y y) (h v3 x v1)) (C (C (h v1 x z) h2) (R v3))) (S (h v3 v1 v1))) (S (h v1 y y))) (C (T (h v0 z v1) (C (C (S (h z x z)) h2) (R v0))) (R y))) (S (h y v1 v0))

@[equational_result]
theorem Equation572_implies_Equation1374 (G: Type _) [Magma G] (h: Equation572 G) : Equation1374 G := fun x y z =>
  let v0 := M z y
  let v1 := M v0 z
  let v2 := M v1 x
  let v3 := M y v2
  have h4 := R v3
  T (h x y v3) (C (R y) (T (C h4 (T (T (C h4 (C (R x) (T (T (h y v0 y) (C (R v0) (S (h z y y)))) (h v1 x y)))) (S (h y v3 x))) (h y v2 v2))) (S (h v2 v3 v2))))

@[equational_result]
theorem Equation1072_implies_Equation3451 (G: Type _) [Magma G] (h: Equation1072 G) : Equation3451 G := fun x y z w u =>
  let v0 := M u y
  let v1 := M (M v0 (M v0 v0)) v0
  let v2 := M (M y (M y y)) y
  have h3 := h y (M v2 (M v2 v2))
  T (T (T (T (T (C (R x) h3) (S (h v2 x))) (h v2 u)) (C (R u) (S h3))) (h v0 z)) (C (R z) (T (h v1 w) (C (R w) (S (h v0 (M v1 (M v1 v1)))))))

@[equational_result]
theorem Equation1090_implies_Equation2779 (G: Type _) [Magma G] (h: Equation1090 G) : Equation2779 G := fun x y z =>
  let v0 := M y z
  let v1 := M (M z (M v0 x)) x
  have h2 := h z v0 x
  let v3 := M v0 (M x z)
  have h4 := R v3
  T (T (h x v3 z) (C h4 (C (S (h v0 x z)) (R z)))) (C h4 (T (C (R v0) (T h2 (C (C (R y) h2) (R v1)))) (S (h y v0 v1))))

@[equational_result]
theorem Equation1368_implies_Equation2805 (G: Type _) [Magma G] (h: Equation1368 G) : Equation2805 G := fun x y z =>
  let v0 := M z x
  have h1 := h y v0 y
  let v2 := M y z
  let v3 := M v2 v0
  have h4 := h x v3 x
  T h4 (C (R v3) (T (T (h (M (M (M x v3) x) x) v0 v2) (C (R v0) (T (T (C (S h4) (R v2)) (C (R x) (C h1 (R z)))) (S (h (M (M (M y v0) y) y) x z))))) (S h1)))

@[equational_result]
theorem Equation1571_implies_Equation3810 (G: Type _) [Magma G] (h: Equation1571 G) : Equation3810 G := fun x y z =>
  let v0 := M z y
  let v1 := M x y
  have h2 := S (h z v1 v0)
  let v3 := M v1 v0
  have h4 := S (h v0 x y)
  T (h v1 v1 (M x (M v0 y))) (C h4 (T (T (C (R v1) h4) (h v3 v3 (M v1 (M z v0)))) (C h2 (T (C (R v3) (T h2 (h z x y))) (S (h x v1 v0))))))

@[equational_result]
theorem Equation1764_implies_Equation3091 (G: Type _) [Magma G] (h: Equation1764 G) : Equation3091 G := fun x y z =>
  let v0 := M x y
  let v1 := M (M v0 z) y
  let v2 := M v1 z
  have h3 := S (h v2 x y)
  T (T (h x v1 y) (C (R (M v1 y)) (C (T (h v0 v0 (M (M v2 y) x)) (C h3 (T (T (C h3 (R v0)) (C (R v2) (h v0 y z))) (S (h y v1 z))))) (R v1)))) (S (h v2 v1 y))

@[equational_result]
theorem Equation1929_implies_Equation3895 (G: Type _) [Magma G] (h: Equation1929 G) : Equation3895 G := fun x y z =>
  let v0 := M y (M y z)
  let v1 := M v0 z
  let v2 := M x x
  have h3 := S (h v2 x x)
  let v4 := M x (M x v2)
  T (T (h v2 v4 z) (C (T (T (T (C (R v4) h3) h3) (h v2 v0 v1)) (C (C (R v0) (S (h z y x))) (R (M v1 v1)))) (R (M z z)))) (S (h v1 v1 z))

@[equational_result]
theorem Equation2113_implies_Equation4364 (G: Type _) [Magma G] (h: Equation2113 G) : Equation4364 G := fun x y z =>
  let v0 := M z x
  let v1 := M y v0
  let v2 := M y z
  have h3 := h v2 y v0
  let v4 := M v2 v1
  T (C (T (T (T (h x z x) (C (C (T (h v0 v2 v1) (C (S (h z y v0)) (R v4))) (R x)) (R v0))) (S (h v4 z x))) (C h3 (R v1))) h3) (S (h v1 (M (M y v2) v0) v1))

@[equational_result]
theorem Equation2442_implies_Equation4153 (G: Type _) [Magma G] (h: Equation2442 G) : Equation4153 G := fun x y z w u =>
  let v0 := M x z
  let v1 := M v0 (M (M v0 v0) v0)
  let v2 := M x (M (M x x) x)
  have h3 := h x (M (M v2 v2) v2)
  T (T (T (T (T (C h3 (R y)) (S (h v2 y))) (h v2 z)) (C (S h3) (R z))) (h v0 u)) (C (T (h v1 w) (C (S (h v0 (M (M v1 v1) v1))) (R w))) (R u))

@[equational_result]
theorem Equation2568_implies_Equation2 (G: Type _) [Magma G] (h: Equation2568 G) : Equation2 G := fun x y =>
  let v0 := M (M x y) y
  let v1 := M y v0
  have h2 := R y
  let v3 := M x v0
  T (T (T (h x y (M x (M (M x v3) v3))) (C (C h2 (T (C (S (h v3 x x)) (R x)) (S (h y x x)))) h2)) (C (C h2 (T (h y y x) (C (h v1 y x) h2))) h2)) (S (h y y (M y (M (M x v1) v1))))

@[equational_result]
theorem Equation2586_implies_Equation1790 (G: Type _) [Magma G] (h: Equation2586 G) : Equation1790 G := fun x y z =>
  let v0 := M (M z x) y
  let v1 := M (M y z) v0
  have h2 := R v0
  have h3 := R v1
  T (T (h x y v0) (C (C (R y) (T (T (T (C (C h2 (h y x z)) (R x)) (S (h z v0 x))) (h z v0 v1)) (C (C h2 (T (C (C h3 (h v0 z y)) (R z)) (S (h y v1 z)))) h3))) h2)) (S (h v1 y v0))

@[equational_result]
theorem Equation3364_implies_Equation3553 (G: Type _) [Magma G] (h: Equation3364 G) : Equation3553 G := fun x y z =>
  let v0 := M x z
  let v1 := M v0 z
  let v2 := M z v1
  have h3 := R y
  let v4 := M x v0
  T (T (T (T (h x y v0) (C h3 (T (h v0 v4 z) (C (R v4) (T (h z v1 v0) (C (R v1) (S (h x v0 z)))))))) (S (h v1 y v4))) (h v1 y v2)) (C h3 (T (S (h z v2 v1)) (S (h v0 z z))))

@[equational_result]
theorem Equation3553_implies_Equation3334 (G: Type _) [Magma G] (h: Equation3553 G) : Equation3334 G := fun x y z =>
  let v0 := M z y
  let v1 := M z v0
  let v2 := M (M x z) z
  have h3 := R v1
  let v4 := M (M z x) x
  T (T (T (T (h x y z) (h y v2 v1)) (C (R v2) (C (T (h y v1 v4) (C h3 (T (C (S (h z y x)) (R v4)) (S (h z v0 x))))) h3))) (S (h v1 v2 v1))) (S (h x v1 z))

@[equational_result]
theorem Equation4022_implies_Equation41 (G: Type _) [Magma G] (h: Equation4022 G) : Equation41 G := fun x y z =>
  have h0 := R y
  have h1 := h y (M y x) x
  have h2 := h y z x
  let v3 := M x x
  let v4 := M y z
  T (T (T (T (T (h x x y) (C (T h1 (S h2)) (R x))) (h v4 x v3)) (S (h v4 y v3))) (C (T (T h2 (S h1)) (C h0 (T (h y x x) (S (h y y x))))) h0)) (S (h y z y))

@[equational_result]
theorem Equation4532_implies_Equation4365 (G: Type _) [Magma G] (h: Equation4532 G) : Equation4365 G := fun x y z w =>
  let v0 := M y z
  let v1 := M x v0
  let v2 := M z w
  have h3 := h x y z
  have h4 := h v2 y z
  T (T (T (T (T (T (T (T h3 (S (h v1 y z))) (C h3 (R v0))) (S (h x v0 y))) (C (R x) (S h4))) (h x v2 v0)) (C (T h4 (S h3)) (R v2))) (h v1 z w)) (S (h y z w))

@[equational_result]
theorem Equation546_implies_Equation3607 (G: Type _) [Magma G] (h: Equation546 G) : Equation3607 G := fun x y z =>
  let v0 := M y z
  let v1 := M v0 x
  let v2 := M z v1
  have h3 := R v1
  have h4 := R v2
  T (C (R x) (T (T (h y v1 v2) (C h3 (C h4 (C (R y) (T (C h4 (h v1 v1 z)) (S (h z v2 v1))))))) (C h3 (C h4 (T (h v0 v1 x) (C h3 (S (h x x v0)))))))) (S (h v2 x v1))

@[equational_result]
theorem Equation1304_implies_Equation4450 (G: Type _) [Magma G] (h: Equation1304 G) : Equation4450 G := fun x y z =>
  let v0 := M (M y z) z
  let v1 := M (M (M v0 x) x) v0
  have h2 := R x
  have h3 := h v0 v0 x
  let v4 := M (M (M y x) x) y
  have h5 := h y y x
  T (T (T (T (C h2 (C (T h5 (C h5 (R v4))) h2)) (S (h y x v4))) (h y x z)) (C h2 (C (T h3 (C h3 (R v1))) h2))) (S (h v0 x v1))

@[equational_result]
theorem Equation2062_implies_Equation263 (G: Type _) [Magma G] (h: Equation2062 G) : Equation263 G := fun x y =>
  let v0 := M x y
  let v1 := M v0 y
  let v2 := M v1 x
  have h3 := h x y y
  have h4 := T (C (C h3 (R v0)) h3) (S (h v1 v0 v0))
  T (T (h x y v0) (C (T (h v1 x v0) (C (R (M v2 x)) (S h3))) (T (h (M x v0) x x) (C (C h4 (R x)) h4)))) (S (h v2 x v1))

@[equational_result]
theorem Equation3571_implies_Equation41 (G: Type _) [Magma G] (h: Equation3571 G) : Equation41 G := fun x y z =>
  let v0 := M y z
  have h1 := R y
  let v2 := M (M y x) y
  have h3 := T (T (T (R v2) (C (T (h y x x) (S (h x x x))) h1)) (h (M x x) y x)) (S (h v0 y x))
  T (T (T (T (h x x y) (h x v2 y)) (C h3 (C (C h1 h3) h1))) (S (h z (M v0 y) y))) (S (h y z y))

@[equational_result]
theorem Equation3573_implies_Equation4229 (G: Type _) [Magma G] (h: Equation3573 G) : Equation4229 G := fun x y z =>
  let v0 := M z z
  let v1 := M v0 y
  let v2 := M v0 v0
  let v3 := M v1 x
  let v4 := M (M v3 v3) x
  T (T (T (T (T (T (h x y v3) (h y v4 z)) (h v4 v1 v0)) (C (R v1) (T (S (h x v2 v3)) (S (h v0 x z))))) (S (h x v1 z))) (C (R x) (T (h v0 y z) (h y v2 z)))) (S (h v1 x v0))

@[equational_result]
theorem Equation3753_implies_Equation41 (G: Type _) [Magma G] (h: Equation3753 G) : Equation41 G := fun x y z =>
  have h0 := h z y z
  have h1 := S h0
  let v2 := M y z
  have h3 := h x y z
  T (T (T (T (T (T (T (T (T (T (T (h x x x) (C (h x x y) (h x x z))) (S (h (M x y) (M x x) (M x z)))) (S (h y x x))) (h y x y)) (C h3 h3)) (S (h v2 (M y x) v2))) (S (h z y x))) h0) (h v2 v2 v2)) (C h1 h1)) (S (h y z y))

@[equational_result]
theorem Equation3161_implies_Equation3692 (G: Type _) [Magma G] (h: Equation3161 G) : Equation3692 G := fun x y z =>
  let v0 := M z z
  have h1 := R v0
  let v2 := M y y
  have h3 := R x
  have h4 := h x z v0
  have h5 := h v0 v0 x
  T (T (T (T (T (C h4 h3) (S h5)) (h v0 v0 v0)) (C (S (h v0 z v0)) h1)) (C (T h5 (C (S h4) h3)) h1)) (C (T (C (h x y v2) h3) (S (h v2 v2 x))) h1)

@[equational_result]
theorem Equation3211_implies_Equation2522 (G: Type _) [Magma G] (h: Equation3211 G) : Equation2522 G := fun x y z =>
  have h0 := R y
  let v1 := M (M x z) z
  let v2 := M y v1
  have h3 := R x
  have h4 := R v2
  T (h x y v2) (C (T (C (C (C (T (h y v2 x) (C (T (C (C (C (T (h v2 x z) (C (T (C (h v1 y v1) h4) (S (h y v2 v1))) h3)) h3) h3) h0) (S (h x y x))) h4)) h4) h4) h3) (S (h v2 x v2))) h0)

@[equational_result]
theorem Equation3770_implies_Equation4325 (G: Type _) [Magma G] (h: Equation3770 G) : Equation4325 G := fun x y z =>
  let v0 := M y x
  let v1 := M z z
  have h2 := S (h z v0 z)
  let v3 := M v0 z
  let v4 := M x x
  T (T (T (h x v0 x) (h (M v0 x) v4 v0)) (C (T (h v4 v0 v0) (C (T (T (T (h v0 v0 z) (h v3 v3 v1)) (C h2 h2)) (S (h z z v0))) (S (h y x x)))) (S (h y v0 x)))) (S (h y v1 v0))

@[equational_result]
theorem Equation3810_implies_Equation3692 (G: Type _) [Magma G] (h: Equation3810 G) : Equation3692 G := fun x y z =>
  let v0 := M z z
  have h1 := S (h x y y)
  let v2 := M y x
  have h3 := S (h x z z)
  let v4 := M z x
  T (T (h x x x) (C (R (M x x)) (T (T (T (h x x z) (h v4 v4 v0)) (C h3 h3)) (S (h z z x))))) (C (T (T (T (h x x y) (h v2 v2 (M y y))) (C h1 h1)) (S (h y y x))) (R v0))

@[equational_result]
theorem Equation492_implies_Equation1181 (G: Type _) [Magma G] (h: Equation492 G) : Equation1181 G := fun x y z =>
  let v0 := M z (M z x)
  let v1 := M v0 y
  have h2 := R v1
  have h3 := R x
  have h4 := R y
  T (h x y v1) (C h4 (T (C h3 (C h2 (C h2 (T (h y v1 x) (C h2 (T (C h4 (C h3 (C h3 (T (h v1 x z) (C h3 (T (C h2 (h v0 y v0)) (S (h y v1 v0)))))))) (S (h x y x)))))))) (S (h v1 x v1))))

@[equational_result]
theorem Equation556_implies_Equation2538 (G: Type _) [Magma G] (h: Equation556 G) : Equation2538 G := fun x y z =>
  let v0 := M y x
  let v1 := M v0 z
  let v2 := M y v1
  let v3 := M v2 z
  have h4 := R z
  T (T (h x z v1) (C h4 (T (T (C (R v1) (T (T (C h4 (C (R x) (T (h v1 z v1) (C h4 (S (h v0 v1 z)))))) (S (h y z x))) (h y v2 v1))) (S (h v2 v1 v2))) (h v2 v3 z)))) (S (h v3 z v3))

@[equational_result]
theorem Equation711_implies_Equation4413 (G: Type _) [Magma G] (h: Equation711 G) : Equation4413 G := fun x y z =>
  let v0 := M (M y z) z
  let v1 := M v0 (M (M v0 x) x)
  have h2 := h v0 v0 x
  have h3 := R x
  let v4 := M y v0
  have h5 := h y y z
  T (T (T (T (C h3 (C h3 (T h5 (C h5 (R v4))))) (S (h y x v4))) (h y x z)) (C h3 (C h3 (T h2 (C h2 (R v1)))))) (S (h v0 x v1))

@[equational_result]
theorem Equation914_implies_Equation3895 (G: Type _) [Magma G] (h: Equation914 G) : Equation3895 G := fun x y z =>
  let v0 := M x x
  have h1 := R v0
  let v2 := M y z
  let v3 := M y v2
  have h4 := h v0 v3 x
  have h5 := R v3
  T h4 (C h5 (T (T (T (T (h (M (M v3 v0) v0) v3 x) (C h5 (C (S h4) h1))) (h (M v3 (M v0 v0)) y x)) (C (R y) (C (S (h v2 y v0)) h1))) (S (h z y x))))

@[equational_result]
theorem Equation1520_implies_Equation2 (G: Type _) [Magma G] (h: Equation1520 G) : Equation2 G := fun x y =>
  let v0 := M y y
  have h1 := R (M v0 v0)
  let v2 := M x x
  have h3 := R (M v2 v2)
  T (T (T (T (T (T (T (h x v2 (M x v2)) (C h3 (C (R x) (S (h x x x))))) (C h3 (h v2 x x))) (S (h v2 v2 v2))) (h v2 v0 v2)) (C h1 (S (h v0 x x)))) (C h1 (C (R y) (h y y x)))) (S (h y v0 (M y (M y x))))

@[equational_result]
theorem Equation1710_implies_Equation695 (G: Type _) [Magma G] (h: Equation1710 G) : Equation695 G := fun x y z =>
  let v0 := M z z
  let v1 := M v0 y
  let v2 := M x v1
  let v3 := M y v2
  let v4 := M x x
  let v5 := M v0 v3
  T (T (h x v0 x) (C (T (T (h (M v0 x) v2 x) (C (T (T (S (h v1 x z)) (h v1 v3 z)) (C (S (h v2 y z)) (R v5))) (R (M v4 v2)))) (S (h v5 v2 x))) (R (M v4 v0)))) (S (h v3 v0 x))

@[equational_result]
theorem Equation2105_implies_Equation11 (G: Type _) [Magma G] (h: Equation2105 G) : Equation11 G := fun x y =>
  let v0 := M y y
  have h1 := R v0
  let v2 := M x x
  have h3 := R v2
  have h4 := h y y y
  T (h x v0 y) (C (T (C (C (T (T (h v0 y x) (C (C (T (T (T (C h4 h1) (S (h y v0 y))) (h y v0 x)) (C (S h4) h3)) (R y)) h3)) (S (h v2 y x))) (R x)) h1) (S (h x x y))) h1)

@[equational_result]
theorem Equation2369_implies_Equation2 (G: Type _) [Magma G] (h: Equation2369 G) : Equation2 G := fun x y =>
  have h0 := R x
  have h1 := h x x y
  let v2 := M x x
  let v3 := M x (M y v2)
  T (T (h x x x) (C (C h0 (T (T (h (M x v2) x x) (C (C h0 (C h0 (T (T (T (C (C h0 (C h0 h1)) h0) (S (h v3 x x))) (h v3 x y)) (C (C h0 (C (R y) (S h1))) h0)))) h0)) (S (h (M x (M y x)) x x)))) h0)) (S (h y x x))

@[equational_result]
theorem Equation2888_implies_Equation3331 (G: Type _) [Magma G] (h: Equation2888 G) : Equation3331 G := fun x y z =>
  let v0 := M y z
  let v1 := M z v0
  have h2 := h x z v0
  have h3 := R z
  let v4 := M x y
  have h5 := h v4 z v1
  T h5 (C (T (T (h (M (M v4 (M z v1)) z) z v0) (C (T (T (C (S h5) h3) (C (C h2 (R y)) h3)) (S (h (M (M x v1) z) y z))) (R v0))) (S h2)) (R v1))

@[equational_result]
theorem Equation3810_implies_Equation4007 (G: Type _) [Magma G] (h: Equation3810 G) : Equation4007 G := fun x y z =>
  let v0 := M y x
  let v1 := M z v0
  let v2 := M z z
  have h3 := S (h y x y)
  let v4 := M y y
  T (T (T (T (h x y y) (h v4 v0 v1)) (C (h v1 v0 z) (T (C (h z v0 z) (T (T (T (h y y y) (h v4 v4 v0)) (C h3 h3)) (h v0 v0 z))) (S (h v1 v2 v1))))) (S (h v2 (M z v1) v1))) (S (h v1 z z))

@[equational_result]
theorem Equation4444_implies_Equation4680 (G: Type _) [Magma G] (h: Equation4444 G) : Equation4680 G := fun x y z w =>
  let v0 := M x y
  let v1 := M v0 z
  have h2 := h y x z
  let v3 := M y z
  have h4 := h y x v3
  have h5 := S h2
  T (T (T (T (T (T (T (T h5 (h y x v1)) (C (R v0) h5)) (h v0 y x)) (C h4 (R x))) (S (h v3 v0 x))) (C (R v3) (T (S h4) h2))) (S (h z y v1))) (h z y w)

@[equational_result]
theorem Equation572_implies_Equation1152 (G: Type _) [Magma G] (h: Equation572 G) : Equation1152 G := fun x y z =>
  let v0 := M x y
  let v1 := M z v0
  let v2 := M v1 z
  let v3 := M y v2
  have h4 := R v3
  T (T (h x y v3) (C (R y) (C h4 (C h4 (T (h v0 v3 v0) (C h4 (T (C (T (h v0 v1 v0) (C (R v1) (S (h z v0 v0)))) (R (M v0 (M v0 v3)))) (S (h y v2 v0))))))))) (S (h v3 y v3))

@[equational_result]
theorem Equation887_implies_Equation2105 (G: Type _) [Magma G] (h: Equation887 G) : Equation2105 G := fun x y z =>
  let v0 := M y x
  let v1 := M (M v0 y) (M z z)
  have h2 := h v0 v0 v0
  let v3 := M v0 v0
  T (T (h x v0 y) (C (R v0) (C (T (T (T (C (R x) h2) (S (h y x v3))) (h y v1 v3)) (C (R v1) (T (C (S (h v0 y z)) (R (M v3 v3))) (S h2)))) (R (M y y))))) (S (h v1 v0 y))

@[equational_result]
theorem Equation1506_implies_Equation55 (G: Type _) [Magma G] (h: Equation1506 G) : Equation55 G := fun x y =>
  let v0 := M y x
  let v1 := M y v0
  let v2 := M x v1
  have h3 := h x y y
  have h4 := T (C h3 (C (R v0) h3)) (S (h v1 v0 v0))
  T (T (h x v0 y) (C (T (h (M v0 x) x x) (C h4 (C (R x) h4))) (T (h v1 v0 x) (C (S h3) (R (M x v2)))))) (S (h v2 v1 x))

@[equational_result]
theorem Equation1571_implies_Equation4679 (G: Type _) [Magma G] (h: Equation1571 G) : Equation4679 G := fun x y z =>
  let v0 := M y z
  let v1 := M x y
  let v2 := M v1 z
  let v3 := M v2 v0
  have h4 := S (h v0 v1 z)
  T (h v2 v2 (M v1 (M v0 z))) (C h4 (T (T (T (C (R v2) h4) (h v3 x y)) (C (R v1) (C (R x) (T (C (R v3) (h y v1 z)) (S (h v1 v2 v0)))))) (S (h x x y))))

@[equational_result]
theorem Equation2269_implies_Equation323 (G: Type _) [Magma G] (h: Equation2269 G) : Equation323 G := fun x y =>
  let v0 := M x y
  have h1 := R v0
  let v2 := M y (M x (M x x))
  have h3 := S (h x v2 y)
  have h4 := R x
  have h5 := h y x x
  have h6 := C (C h4 (T h5 (C (R v2) h5))) h4
  have h7 := C h1 (T h6 h3)
  T (h v0 v0 x) (C (T (T (T (C h1 h7) h7) h6) h3) h1)

@[equational_result]
theorem Equation2944_implies_Equation4413 (G: Type _) [Magma G] (h: Equation2944 G) : Equation4413 G := fun x y z =>
  have h0 := R z
  have h1 := S (h y x y)
  let v2 := M x (M x y)
  let v3 := M v2 y
  have h4 := R x
  have h5 := S (h v2 x v2)
  let v6 := M (M x (M x v2)) v2
  T (T (T (T (h v2 v6 x) (C (C (T (C (R v6) h5) h5) h4) h4)) (S (h y x x))) (h y v3 z)) (C (C (T (C (R v3) h1) h1) h0) h0)

@[equational_result]
theorem Equation3211_implies_Equation4358 (G: Type _) [Magma G] (h: Equation3211 G) : Equation4358 G := fun x y z =>
  let v0 := M y z
  let v1 := M z y
  let v2 := M x v1
  have h3 := R v0
  have h4 := R y
  T (C (T (h x v2 v1) (C (T (S (h v1 x v1)) (C (T (h z y v0) (C (T (C (C (C (T (h y v0 z) (C (S (h z y z)) h3)) h3) h3) (R z)) (S (h v0 z v0))) h4)) h4)) (R v2))) h3) (S (h v2 v0 y))

@[equational_result]
theorem Equation3791_implies_Equation3932 (G: Type _) [Magma G] (h: Equation3791 G) : Equation3932 G := fun x y z =>
  let v0 := M y z
  let v1 := M x v0
  let v2 := M v0 y
  T (T (T (T (T (T (h x y v0) (R (M (M v0 x) (M y v0)))) (C (h v0 x v0) (h y v0 v0))) (S (h v1 v2 (M v0 v0)))) (h v1 v2 v0)) (C (R (M v0 v1)) (T (T (C (h v0 y z) (h y z v0)) (S (h v0 v2 (M z v0)))) (S (h z v0 y))))) (S (h v1 z v0))

@[equational_result]
theorem Equation3791_implies_Equation4461 (G: Type _) [Magma G] (h: Equation3791 G) : Equation4461 G := fun x y z =>
  let v0 := M z z
  let v1 := M y x
  let v2 := M v0 y
  T (T (T (T (h x v1 y) (h v1 (M v1 y) (M x v1))) (C (S (h v1 y x)) (S (h y x v1)))) (C (T (T (T (h v1 y v0) (C (R (M v0 v1)) (T (h y v0 v0) (C (R v2) (S (h z z z)))))) (S (h v1 v2 v0))) (S (h x v0 y))) (R v1))) (S (h v0 y x))

@[equational_result]
theorem Equation3804_implies_Equation3350 (G: Type _) [Magma G] (h: Equation3804 G) : Equation3350 G := fun x y z =>
  let v0 := M z z
  let v1 := M x v0
  have h2 := h x y v0
  have h3 := R v1
  T (T (T (h x y y) (C (h y y x) (T (T h2 (h (M v0 y) v1 v1)) (C (T (C (T (h x v0 v0) (C (S (h z z z)) h3)) h3) (S (h x v1 v0))) (S h2))))) (S (h (M x v1) (M y x) (M x y)))) (S (h y v1 x))

@[equational_result]
theorem Equation4182_implies_Equation3370 (G: Type _) [Magma G] (h: Equation4182 G) : Equation3370 G := fun x y z =>
  let v0 := M z x
  have h1 := R x
  let v2 := M (M x x) x
  let v3 := M (M y z) z
  T (T (T (T (T (T (h x y z) (h v3 x x)) (C (C (h x x x) h1) (R v3))) (S (h v3 v2 x))) (S (h v2 y z))) (C (C (T (h x x z) (C (T (C (h x z x) (R z)) (S (h z v0 x))) h1)) h1) (R y))) (S (h y (M z v0) x))

@[equational_result]
theorem Equation716_implies_Equation919 (G: Type _) [Magma G] (h: Equation716 G) : Equation919 G := fun x y =>
  let v0 := M y y
  let v1 := M y x
  let v2 := M y (M v0 v1)
  have h3 := h v2 v0
  let v4 := M v0 v0
  have h5 := R y
  have h6 := h x v0
  T (T h6 (C (R v0) (T (T (h (M v0 (M v4 x)) y) (C h5 (T (T (C h5 (S h6)) (h v1 y)) (C h5 h3)))) (S (h (M v0 (M v4 v2)) y))))) (S h3)

@[equational_result]
theorem Equation1084_implies_Equation2 (G: Type _) [Magma G] (h: Equation1084 G) : Equation2 G := fun x y =>
  have h0 := h x y x
  let v1 := M x (M y x)
  let v2 := M v1 x
  let v3 := M y (M y y)
  let v4 := M (M x (M x x)) x
  T (T h0 (C (R y) (T (T (T (C (R v1) (T (h x x x) (C (h x y y) (R v4)))) (S (h y v1 v4))) (h y v3 v2)) (C (R v3) (T (C (S (h y y y)) (R v2)) (S h0)))))) (S (h y y x))

@[equational_result]
theorem Equation1090_implies_Equation4362 (G: Type _) [Magma G] (h: Equation1090 G) : Equation4362 G := fun x y z =>
  let v0 := M x z
  let v1 := M y v0
  have h2 := S (h v0 y v1)
  let v3 := M (M v0 (M y v1)) v1
  let v4 := M x (M y z)
  have h5 := R v4
  T (h v4 y v3) (C (R y) (T (C (T (T (C h5 h2) (C h5 (C (h x y z) (R z)))) (S (h y v4 z))) (R v3)) h2))

@[equational_result]
theorem Equation1993_implies_Equation3008 (G: Type _) [Magma G] (h: Equation1993 G) : Equation3008 G := fun x y z =>
  let v0 := M z z
  let v1 := M y v0
  let v2 := M v1 x
  let v3 := M v2 y
  let v4 := M v3 v0
  T (T (h x v0 v2) (C (R (M v0 (M v2 v2))) (T (T (h (M x v0) v2 x) (C (R (M v2 (M x x))) (T (T (S (h v1 x z)) (h v1 v3 z)) (C (R v4) (S (h v2 y z)))))) (S (h v4 v2 x))))) (S (h v3 v0 v2))

@[equational_result]
theorem Equation2714_implies_Equation1996 (G: Type _) [Magma G] (h: Equation2714 G) : Equation1996 G := fun x y z =>
  let v0 := M z z
  let v1 := M (M y v0) (M y x)
  have h2 := R x
  have h3 := S (h v1 x v0)
  have h4 := S (h z x x)
  T (T (T (h x (M (M x z) (M x x)) x) (C (C h4 h4) h2)) (C (T (h v0 (M (M x v1) (M x v0)) v0) (C (C h3 h3) (h v0 y x))) h2)) (S (h v1 v1 x))

@[equational_result]
theorem Equation3195_implies_Equation2573 (G: Type _) [Magma G] (h: Equation3195 G) : Equation2573 G := fun x y z =>
  let v0 := M z x
  let v1 := M v0 y
  let v2 := M y v1
  have h3 := R v0
  T (h x v0 z) (C (T (C (C (R (M v0 z)) (T (h v0 y v1) (C (T (T (C (T (C (h v2 y v1) (R y)) (S (h v1 v2 y))) h3) (C (h v1 v0 y) h3)) (S (h y v1 v0))) (R v1)))) (R x)) (S (h v2 z x))) (R z))

@[equational_result]
theorem Equation3329_implies_Equation38 (G: Type _) [Magma G] (h: Equation3329 G) : Equation38 G := fun x y =>
  let v0 := M x x
  let v1 := M x y
  have h2 := R x
  have h3 := R v0
  T (T (T (T (h x x v0) (h x (M v0 v0) v1)) (C h2 (C (R v1) (C (T (h v0 v0 y) (C h3 (T (C (R y) (T (C h3 (h x x v1)) (S (h v0 v1 x)))) (S (h y x v0))))) h2)))) (S (h x (M v0 (M y x)) v1))) (S (h x y v0))

@[equational_result]
theorem Equation3770_implies_Equation3500 (G: Type _) [Magma G] (h: Equation3770 G) : Equation3500 G := fun x y z =>
  let v0 := M z z
  let v1 := M y v0
  let v2 := M v0 z
  have h3 := h x y v0
  T (T (T (T (h x x y) (C h3 h3)) (S (h v1 v1 (M x v0)))) (C (T (T (h y v0 z) (h v2 (M y z) v2)) (C (S (h v0 y z)) (T (S (h v0 v0 z)) (S (h z z z))))) (R v1))) (S (h y (M v0 y) v0))

@[equational_result]
theorem Equation3770_implies_Equation4135 (G: Type _) [Magma G] (h: Equation3770 G) : Equation4135 G := fun x y z =>
  let v0 := M x y
  let v1 := M v0 z
  let v2 := M z z
  let v3 := M v0 v0
  have h4 := h x y y
  T (T (T (T (T (T h4 (h (M y y) v0 v0)) (C (R v3) (S h4))) (h v3 v0 v1)) (C (h v0 v1 z) (T (C (h v0 v0 z) (h v0 z z)) (S (h v2 v1 v1))))) (S (h v2 (M v1 z) v1))) (S (h v1 z z))

@[equational_result]
theorem Equation4229_implies_Equation3350 (G: Type _) [Magma G] (h: Equation4229 G) : Equation3350 G := fun x y z =>
  let v0 := M z z
  let v1 := M x v0
  let v2 := M (M v0 v0) v1
  let v3 := M (M y y) y
  T (T (T (T (T (T (h x y y) (h v3 x z)) (C (T (T (h v0 x v0) (C (S (h x v0 z)) (R v0))) (h v1 v0 z)) (R v3))) (h v2 v3 v0)) (C (T (S (h v3 v0 z)) (S (h v0 y y))) (R v2))) (S (h v2 y z))) (S (h y v1 v0))

@[equational_result]
theorem Equation840_implies_Equation378 (G: Type _) [Magma G] (h: Equation840 G) : Equation378 G := fun x y =>
  let v0 := M x y
  have h1 := h y x (M v0 v0)
  have h2 := h v0 v0 v0
  have h3 := R y
  have h4 := T (C h3 h2) (S h1)
  have h5 := R v0
  let v6 := M y y
  T (T (h v0 y v6) (C h5 (T (T (T (C h4 (R (M v6 v6))) (S (h y y y))) h1) (C h3 (S h2))))) (C h5 h4)

@[equational_result]
theorem Equation1098_implies_Equation1913 (G: Type _) [Magma G] (h: Equation1098 G) : Equation1913 G := fun x y z =>
  let v0 := M y (M x z)
  let v1 := M v0 (M z y)
  have h2 := R v0
  have h3 := R v1
  T (T (h x v0 y) (C h2 (C (T (T (T (C (R x) (C (h y z x) h2)) (S (h z x v0))) (h z v1 v0)) (C h3 (C (T (C (R z) (C (h v0 y z) h3)) (S (h y z v1))) h2))) (R y)))) (S (h v1 v0 y))

@[equational_result]
theorem Equation1319_implies_Equation2 (G: Type _) [Magma G] (h: Equation1319 G) : Equation2 G := fun x y =>
  have h0 := R x
  have h1 := h x x y
  let v2 := M x x
  let v3 := M (M v2 y) x
  T (T (h x x x) (C h0 (C (T (T (h (M v2 x) x x) (C h0 (C (C (T (T (T (C h0 (C (C h1 h0) h0)) (S (h v3 x x))) (h v3 x y)) (C h0 (C (C (S h1) (R y)) h0))) h0) h0))) (S (h (M (M x y) x) x x))) h0))) (S (h y x x))

@[equational_result]
theorem Equation1537_implies_Equation3903 (G: Type _) [Magma G] (h: Equation1537 G) : Equation3903 G := fun x y z =>
  let v0 := M x x
  let v1 := M y (M z y)
  let v2 := M v1 z
  have h3 := R v0
  T (T (h v0 v2 x) (C (R (M v2 v2)) (T (T (C (R x) (T (C h3 (h x x x)) (S (h x x v0)))) (h v0 x v2)) (C h3 (C (R v2) (T (C h3 (C (R v1) (h z x y))) (S (h v0 x v1)))))))) (S (h v2 v2 v0))

@[equational_result]
theorem Equation2724_implies_Equation31 (G: Type _) [Magma G] (h: Equation2724 G) : Equation31 G := fun x y =>
  let v0 := M y y
  let v1 := M x v0
  have h2 := h v0 v1 y
  have h3 := R v0
  have h4 := h v0 x y
  let v5 := M x x
  have h6 := R v5
  T (h x x v0) (C (T (C (T (T (h v5 v1 y) (C (S (h v0 x x)) h6)) (C (T h2 (C (S h4) h3)) h6)) (T (C h4 h3) (S h2))) (S (h v0 v0 x))) (R x))

@[equational_result]
theorem Equation3131_implies_Equation1358 (G: Type _) [Magma G] (h: Equation3131 G) : Equation1358 G := fun x y z =>
  let v0 := M z x
  let v1 := M v0 z
  let v2 := M v1 y
  let v3 := M y v2
  have h4 := R v3
  T (h x v2 x) (C (T (C (R (M (M v2 x) x)) (T (T (h x z v3) (C (C (C (T (h v0 v1 v0) (C (S (h z v0 v0)) (R v1))) h4) h4) (R z))) (S (h v1 z v3)))) (S (h y v1 x))) (R v2))

