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
theorem Equation3791_implies_Equation4541 (G: Type _) [Magma G] (h: Equation3791 G) : Equation4541 G := fun x y z =>
  let v0 := M z x
  let v1 := M y z
  T (T (T (T (h x v1 z) (h v0 (M v1 z) (M x v1))) (C (T (S (h v1 z x)) (h v1 z v0)) (T (T (S (h z x v1)) (h z x y)) (C (R v1) (h x y z))))) (S (h (M z v0) v1 (M v0 v1)))) (S (h v0 y z))

@[equational_result]
theorem Equation3804_implies_Equation3388 (G: Type _) [Magma G] (h: Equation3804 G) : Equation3388 G := fun x y z =>
  let v0 := M z y
  let v1 := M x v0
  let v2 := M x y
  T (T (T (h x y v1) (C (T (T (T (h v1 y x) (h v2 (M v1 x) v1)) (C (S (h v1 v0 x)) (R (M v2 v1)))) (S (h v2 v0 v1))) (h x v1 y))) (S (h (M y v1) v0 v2))) (S (h z v1 y))

@[equational_result]
theorem Equation508_implies_Equation3906 (G: Type _) [Magma G] (h: Equation508 G) : Equation3906 G := fun x y z =>
  let v0 := M z z
  let v1 := M x x
  let v2 := M y v0
  have h3 := R v2
  T (h v1 v2 z) (C h3 (T (T (T (C h3 (T (T (C (R v1) (h v0 v1 z)) (S (h v1 v1 v0))) (h v1 v2 x))) (S (h v2 v2 v1))) (C (R y) (h v0 y z))) (S (h y y v0))))

@[equational_result]
theorem Equation572_implies_Equation1293 (G: Type _) [Magma G] (h: Equation572 G) : Equation1293 G := fun x y z =>
  let v0 := M x y
  let v1 := M v0 z
  let v2 := M v1 z
  have h3 := R v2
  have h4 := R z
  T (h x y z) (C (R y) (T (C h4 (C h4 (T (h v0 z v2) (C h4 (C h3 (T (C h3 (h v1 z z)) (S (h z v2 z)))))))) (S (h v2 z z))))

@[equational_result]
theorem Equation1761_implies_Equation4109 (G: Type _) [Magma G] (h: Equation1761 G) : Equation4109 G := fun x y z =>
  let v0 := M (M y z) z
  let v1 := M v0 y
  let v2 := M (M x v1) z
  have h3 := h x v1 z
  T (C (T h3 (C (T (C (R v1) (T (h z z v0) (C (R (M z v0)) (S (h y z z))))) (S (h z v0 y))) (R v2))) h3) (S (h v1 z v2))

@[equational_result]
theorem Equation2958_implies_Equation4026 (G: Type _) [Magma G] (h: Equation2958 G) : Equation4026 G := fun x y z =>
  let v0 := M (M z (M z y)) x
  have h1 := R v0
  have h2 := S (h v0 y v0)
  let v3 := M (M y (M y v0)) v0
  T (C (T (h x v3 v0) (C (T (C (T (C (R v3) h2) h2) (R x)) (C h1 (h x z y))) h1)) (R y)) (S (h v0 v0 y))

@[equational_result]
theorem Equation3131_implies_Equation684 (G: Type _) [Magma G] (h: Equation3131 G) : Equation684 G := fun x y z =>
  let v0 := M (M y z) z
  let v1 := M x v0
  let v2 := M y v1
  have h3 := R v1
  have h4 := R z
  T (T (T (h x v1 x) (C (S (h v0 x x)) h3)) (C (C (C (T (h y v2 y) (C (S (h v1 y y)) (R v2))) h4) h4) h3)) (S (h v2 v1 z))

@[equational_result]
theorem Equation3404_implies_Equation4461 (G: Type _) [Magma G] (h: Equation3404 G) : Equation4461 G := fun x y z =>
  have h0 := R y
  let v1 := M y x
  have h2 := R x
  T (T (C h2 (h y x y)) (S (h (M y y) y x))) (C (T (T (h y y x) (C h2 (T (T (T (C h0 (h x y y)) (S (h v1 y y))) (h v1 y z)) (C (R z) (S (h x z y)))))) (S (h z z x))) h0)

@[equational_result]
theorem Equation3791_implies_Equation3286 (G: Type _) [Magma G] (h: Equation3791 G) : Equation3286 G := fun x y z =>
  let v0 := M z z
  let v1 := M y v0
  T (T (T (T (T (T (h x x v1) (h (M v1 x) (M x v1) (M x x))) (C (S (h x v1 x)) (S (h v1 x x)))) (S (h v1 v1 x))) (h v1 v1 v0)) (C (T (C (h z z z) (R v1)) (S (h v0 y v0))) (R (M v1 v0)))) (S (h y v1 v0))

@[equational_result]
theorem Equation3791_implies_Equation4098 (G: Type _) [Magma G] (h: Equation3791 G) : Equation4098 G := fun x y z =>
  let v0 := M y y
  let v1 := M v0 z
  T (T (T (h x x z) (h (M z x) (M x z) (M x x))) (C (T (T (T (S (h x z x)) (h x z v0)) (C (R (M v0 x)) (T (h z v0 v0) (C (R v1) (S (h y y y)))))) (S (h x v1 v0))) (S (h z x x)))) (S (h v1 z x))

@[equational_result]
theorem Equation3932_implies_Equation3323 (G: Type _) [Magma G] (h: Equation3932 G) : Equation3323 G := fun x y z =>
  let v0 := M z z
  let v1 := M y v0
  have h2 := h x v1 x
  let v3 := M x (M v1 x)
  T (T (T (h x y v0) (C (T (T (T h2 (h v3 x z)) (C (C (R v3) (h x z z)) (R z))) (S (h v3 (M x v0) z))) (R v0))) (S (h v3 x v0))) (S h2)

@[equational_result]
theorem Equation4193_implies_Equation41 (G: Type _) [Magma G] (h: Equation4193 G) : Equation41 G := fun x y z =>
  let v0 := M y z
  have h1 := R v0
  let v2 := M v0 y
  have h3 := R (M (M v0 x) x)
  T (T (T (h x x v0) (C h3 h1)) (C (T (T (T h3 (C (T (h v0 x x) (S (h v0 y x))) (R x))) (h v2 x x)) (S (h v2 y x))) h1)) (S (h y z v0))

@[equational_result]
theorem Equation1504_implies_Equation1358 (G: Type _) [Magma G] (h: Equation1504 G) : Equation1358 G := fun x y z =>
  let v0 := M z x
  let v1 := M v0 z
  let v2 := M v1 y
  have h3 := R v0
  T (h x v2 (M y v2)) (C (T (C (R v2) (T (h x z x) (C h3 (C (T (h x z v1) (C h3 (S (h z v0 z)))) h3)))) (S (h y v1 v0))) (S (h v2 y v2)))

@[equational_result]
theorem Equation1527_implies_Equation2 (G: Type _) [Magma G] (h: Equation1527 G) : Equation2 G := fun x y =>
  let v0 := M y x
  let v1 := M x (M v0 x)
  let v2 := M x x
  have h3 := R x
  have h4 := R v2
  T (T (h x x v1) (C h4 (C h3 (T (C (T (T (h x x x) (C h4 (C h3 (h v2 x x)))) (S (h v2 x (M x (M v2 x))))) (R v1)) (S (h v0 x x)))))) (S (h y x x))

@[equational_result]
theorem Equation1761_implies_Equation2779 (G: Type _) [Magma G] (h: Equation1761 G) : Equation2779 G := fun x y z =>
  let v0 := M x z
  let v1 := M (M y z) v0
  let v2 := M v1 y
  have h3 := R v2
  T (T (h x z v2) (C (R (M z v2)) (C (T (h v0 v1 y) (C h3 (T (C (R (M v0 v1)) (h y z v0)) (S (h z v0 v1))))) h3))) (S (h v2 z v2))

@[equational_result]
theorem Equation2944_implies_Equation14 (G: Type _) [Magma G] (h: Equation2944 G) : Equation14 G := fun x y =>
  let v0 := M x y
  have h1 := R v0
  have h2 := S (h x x x)
  let v3 := M (M x (M x x)) x
  have h4 := C (C (T (C (R v3) h2) h2) h1) h1
  have h5 := h x v3 v0
  T (T h5 h4) (C (T (C (T h5 h4) h1) (S (h y x v0))) h1)

@[equational_result]
theorem Equation3617_implies_Equation4226 (G: Type _) [Magma G] (h: Equation3617 G) : Equation4226 G := fun x y z =>
  let v0 := M z z
  let v1 := M v0 x
  have h2 := h v1 y y
  let v3 := M (M y v1) y
  T (T (T (h x y v0) (C (R v0) (T (T (T h2 (h y v3 z)) (C (R z) (C (h z y z) (R v3)))) (S (h (M v0 y) v3 z))))) (S (h y v3 v0))) (S h2)

@[equational_result]
theorem Equation3762_implies_Equation3451 (G: Type _) [Magma G] (h: Equation3762 G) : Equation3451 G := fun x y z w u =>
  let v0 := M u y
  let v1 := M w v0
  have h2 := h v0 v0
  have h3 := T h2 (S (h w v0))
  have h4 := S (h u y)
  let v5 := M y y
  T (T (T (T (T (T (h x y) (h v5 v5)) (C h4 h4)) h2) (C h3 h3)) (h v1 v1)) (S (h z v1))

@[equational_result]
theorem Equation3776_implies_Equation3588 (G: Type _) [Magma G] (h: Equation3776 G) : Equation3588 G := fun x y z =>
  let v0 := M x y
  have h1 := S (h v0 z y)
  have h2 := h x y v0
  let v3 := M y v0
  let v4 := M z y
  let v5 := M v0 x
  T (T (T h2 (h v3 v5 v4)) (C (T (h v5 v4 v3) (C h1 (S h2))) h1)) (S (h z (M v0 z) v0))

@[equational_result]
theorem Equation3776_implies_Equation3994 (G: Type _) [Magma G] (h: Equation3776 G) : Equation3994 G := fun x y z =>
  let v0 := M x y
  have h1 := S (h z v0 x)
  have h2 := h x y v0
  let v3 := M v0 x
  let v4 := M y v0
  let v5 := M x z
  T (T (T h2 (h v4 v3 v5)) (C h1 (T (h v5 v4 v3) (C (S h2) h1)))) (S (h (M z v0) z v0))

@[equational_result]
theorem Equation3791_implies_Equation3906 (G: Type _) [Magma G] (h: Equation3791 G) : Equation3906 G := fun x y z =>
  let v0 := M z z
  let v1 := M y v0
  have h2 := R v1
  T (T (T (T (T (T (h x x y) (h (M y x) (M x y) (M x x))) (C (S (h x y x)) (S (h y x x)))) (S (h y y x))) (h y y v0)) (C (T (h v0 y v0) (C (S (h z z z)) h2)) h2)) (S (h v1 y v0))

@[equational_result]
theorem Equation3804_implies_Equation3703 (G: Type _) [Magma G] (h: Equation3804 G) : Equation3703 G := fun x y z =>
  have h0 := h z z y
  have h1 := S h0
  let v2 := M z x
  let v3 := M x z
  T (T (T (T (h x x z) (h v2 v3 (M (M y z) (M z y)))) (C (T (C h1 (R v3)) (S (h x z z))) (T (C (R v2) h1) (S (h z x z))))) (S (h z z x))) h0

@[equational_result]
theorem Equation3810_implies_Equation3729 (G: Type _) [Magma G] (h: Equation3810 G) : Equation3729 G := fun x y z =>
  have h0 := h x y z
  have h1 := h (M z y) (M z x) (M z z)
  have h2 := h y z z
  have h3 := h x z z
  let v4 := M x z
  T (T (T (T h0 h1) (C (S h3) (S h2))) (h v4 (M y z) v4)) (C (T (T (C h3 h2) (S h1)) (S h0)) (S (h z z x)))

@[equational_result]
theorem Equation1507_implies_Equation1358 (G: Type _) [Magma G] (h: Equation1507 G) : Equation1358 G := fun x y z =>
  let v0 := M z x
  let v1 := M v0 z
  let v2 := M v1 y
  let v3 := M y v2
  let v4 := M v3 y
  T (h x v4 v3) (C (T (C (R v4) (T (h x v2 y) (C (T (C (R v2) (h x z v0)) (S (h y v1 v0))) (R (M y v3))))) (S (h y v3 y))) (S (h v2 y v3)))

@[equational_result]
theorem Equation1558_implies_Equation1152 (G: Type _) [Magma G] (h: Equation1558 G) : Equation1152 G := fun x y z =>
  let v0 := M x y
  let v1 := M z v0
  let v2 := M v1 z
  let v3 := M y v2
  T (T (h x v0 v3) (C (R (M v0 v3)) (T (C (R x) (T (C (T (h v0 z v0) (C (R v1) (S (h z x y)))) (R v3)) (S (h y v1 z)))) (h v0 y v2)))) (S (h v3 v0 v3))

@[equational_result]
theorem Equation1725_implies_Equation2 (G: Type _) [Magma G] (h: Equation1725 G) : Equation2 G := fun x y =>
  have h0 := R x
  let v1 := M y x
  let v2 := M (M v1 x) x
  let v3 := M x x
  have h4 := R v3
  T (T (h x x v2) (C h4 (C (T (C (T (T (h x x x) (C h4 (C (h v3 x x) h0))) (S (h v3 x (M (M v3 x) x)))) (R v2)) (S (h v1 x x))) h0))) (S (h y x x))

@[equational_result]
theorem Equation1910_implies_Equation3770 (G: Type _) [Magma G] (h: Equation1910 G) : Equation3770 G := fun x y z =>
  let v0 := M y z
  let v1 := M v0 (M x z)
  let v2 := M v1 v0
  let v3 := M v1 z
  T (T (h (M x y) v1 v0) (C (C (R v1) (T (C (C (R x) (h y v1 z)) (T (h v0 v1 z) (C (S (h x v0 z)) (R v3)))) (S (h v2 x v3)))) (R v2))) (S (h v1 v1 v0))

@[equational_result]
theorem Equation1963_implies_Equation2 (G: Type _) [Magma G] (h: Equation1963 G) : Equation2 G := fun x y =>
  let v0 := M x x
  have h1 := R v0
  let v2 := M x y
  have h3 := R x
  let v4 := M x (M x v2)
  T (T (h x x v4) (C (C h3 (T (C (R v4) (T (T (h x x x) (C (C h3 (h v0 x y)) h1)) (S (h v0 x (M x (M y v0)))))) (S (h v2 x x)))) h1)) (S (h y x x))

@[equational_result]
theorem Equation2167_implies_Equation2573 (G: Type _) [Magma G] (h: Equation2167 G) : Equation2573 G := fun x y z =>
  let v0 := M z x
  let v1 := M v0 y
  let v2 := M y v1
  let v3 := M v2 z
  T (T (h x v3 v0) (C (T (C (T (C (R v3) (T (h v0 v0 y) (C (S (h y z x)) (R v1)))) (S (h z y v1))) (R x)) (h v0 v2 z)) (R (M v3 v0)))) (S (h v3 v3 v0))

@[equational_result]
theorem Equation3180_implies_Equation25 (G: Type _) [Magma G] (h: Equation3180 G) : Equation25 G := fun x y =>
  have h0 := R x
  let v1 := M x y
  let v2 := M v1 x
  have h3 := h v1 v2 v2
  have h4 := R v1
  have h5 := h v2 v1 x
  T (T (h x v1 v1) (C (T (T (S (h v1 x y)) h3) (C (S h5) h4)) h0)) (C (T (C h5 h4) (S h3)) h0)

@[equational_result]
theorem Equation4013_implies_Equation4026 (G: Type _) [Magma G] (h: Equation4013 G) : Equation4026 G := fun x y z =>
  let v0 := M z (M z y)
  let v1 := M x y
  let v2 := M y v1
  let v3 := M v1 v2
  T (T (T (T (T (T (h x y v1) (h v3 x y)) (h v2 v3 z)) (C (C (R z) (S (h z y v1))) (R v2))) (h v0 v2 x)) (C (C (R x) (S (h x x y))) (R v0))) (S (h v0 x x))

@[equational_result]
theorem Equation4124_implies_Equation4150 (G: Type _) [Magma G] (h: Equation4124 G) : Equation4150 G := fun x y z w =>
  have h0 := R y
  let v1 := M x z
  let v2 := M v1 v1
  let v3 := M x y
  let v4 := M x x
  T (T (T (T (h x y v3) (C (T (T (h v4 v3 z) (C (S (h x z v4)) (R v3))) (h v1 v3 v2)) h0)) (S (h v2 y v3))) (h v2 y w)) (C (S (h v1 w v2)) h0)

@[equational_result]
theorem Equation492_implies_Equation692 (G: Type _) [Magma G] (h: Equation492 G) : Equation692 G := fun x y z =>
  let v0 := M z y
  let v1 := M v0 z
  let v2 := M x v1
  have h3 := R v2
  T (h x y v2) (C (R y) (T (C (R x) (C h3 (C h3 (T (T (T (h y v0 z) (C (R v0) (S (h z y z)))) (h v1 v2 x)) (C h3 (S (h x v1 x))))))) (S (h v2 x v2))))

@[equational_result]
theorem Equation492_implies_Equation1358 (G: Type _) [Magma G] (h: Equation492 G) : Equation1358 G := fun x y z =>
  let v0 := M z x
  let v1 := M v0 z
  let v2 := M v1 y
  have h3 := R v2
  T (T (T (h x v0 z) (C (R v0) (S (h z x z)))) (h v1 y v2)) (C (R y) (T (C (R v1) (C h3 (C h3 (T (h y v2 v1) (C h3 (S (h v1 y v1))))))) (S (h v2 v1 v2))))

@[equational_result]
theorem Equation492_implies_Equation4162 (G: Type _) [Magma G] (h: Equation492 G) : Equation4162 G := fun x y z =>
  let v0 := M y x
  let v1 := M v0 z
  let v2 := M v1 z
  have h3 := R v1
  have h4 := R v0
  T (C (R x) (T (h y v2 v0) (C (R v2) (C (R y) (T (C h4 (C h4 (C h3 (T (h z v1 v0) (C h3 (S (h v0 z v0))))))) (S (h v0 v0 v1))))))) (S (h v2 x y))

@[equational_result]
theorem Equation1561_implies_Equation4007 (G: Type _) [Magma G] (h: Equation1561 G) : Equation4007 G := fun x y z =>
  let v0 := M x y
  let v1 := M y x
  let v2 := M z v1
  let v3 := M v2 z
  T (T (h v0 v1 v0) (C (R (M v1 v0)) (T (T (S (h v0 x y)) (h v0 v2 z)) (C (R v3) (C (R v0) (T (C (h z x y) (h v2 y x)) (S (h v1 v0 v2)))))))) (S (h v3 v1 v0))

@[equational_result]
theorem Equation1774_implies_Equation3810 (G: Type _) [Magma G] (h: Equation1774 G) : Equation3810 G := fun x y z =>
  let v0 := M z x
  let v1 := M (M z y) v0
  let v2 := M z v1
  let v3 := M v0 v1
  T (T (h (M x y) v0 v1) (C (R v3) (C (T (C (T (h v0 z v1) (C (R v2) (S (h y z v0)))) (C (h x z v1) (R y))) (S (h v3 v2 y))) (R v1)))) (S (h v1 v0 v1))

@[equational_result]
theorem Equation1964_implies_Equation3297 (G: Type _) [Magma G] (h: Equation1964 G) : Equation3297 G := fun x y z =>
  let v0 := M z (M z y)
  let v1 := M y v0
  let v2 := M z (M v1 x)
  have h3 := h x z v1
  T (C h3 (T h3 (C (R v2) (T (C (T (h z v0 z) (C (S (h y z z)) (R (M v0 z)))) (R v1)) (S (h z y v0)))))) (S (h v1 v2 z))

@[equational_result]
theorem Equation2117_implies_Equation2 (G: Type _) [Magma G] (h: Equation2117 G) : Equation2 G := fun x y =>
  let v0 := M x x
  have h1 := R v0
  have h2 := R x
  let v3 := M x y
  let v4 := M (M x v3) x
  T (T (h x v4 x) (C (C (T (C (R v4) (T (T (h x x x) (C (C (h v0 x x) h2) h1)) (S (h v0 (M (M x v0) x) x)))) (S (h v3 x x))) h2) h1)) (S (h y x x))

@[equational_result]
theorem Equation2196_implies_Equation2373 (G: Type _) [Magma G] (h: Equation2196 G) : Equation2373 G := fun x y z =>
  let v0 := M x z
  let v1 := M z v0
  let v2 := M y v1
  let v3 := M v2 y
  let v4 := M y v3
  T (h x v4 v3) (C (S (h v2 y v3)) (T (C (T (h x v2 y) (C (R (M v3 y)) (T (C (h x z v0) (R v2)) (S (h y v1 v0))))) (R v4)) (S (h y v3 y))))

@[equational_result]
theorem Equation2399_implies_Equation2271 (G: Type _) [Magma G] (h: Equation2399 G) : Equation2271 G := fun x y z =>
  let v0 := M x (M y (M y z))
  let v1 := M v0 z
  let v2 := M v1 (M x (M x v1))
  have h3 := R v0
  have h4 := h v1 v1 x
  T (T (h x v0 v0) (C (C h3 (T (T (C h3 (S (h z x y))) h4) (C (R v2) h4))) h3)) (S (h v1 v0 v2))

@[equational_result]
theorem Equation3711_implies_Equation4153 (G: Type _) [Magma G] (h: Equation3711 G) : Equation4153 G := fun x y z w u =>
  let v0 := M x z
  let v1 := M v0 w
  have h2 := h v0 v0
  have h3 := T h2 (S (h v0 w))
  have h4 := S (h x z)
  let v5 := M x x
  T (T (T (T (T (T (h x y) (h v5 v5)) (C h4 h4)) h2) (C h3 h3)) (h v1 v1)) (S (h v1 u))

@[equational_result]
theorem Equation3760_implies_Equation41 (G: Type _) [Magma G] (h: Equation3760 G) : Equation41 G := fun x y z =>
  have h0 := S (h y z z)
  let v1 := M z z
  have h2 := R v1
  let v3 := M x x
  have h4 := h x z x
  T (T (T (T (T (T (T (T (T (h x x z) (C (h x x x) h4)) (S (h v1 v3 v3))) (S h4)) (h x z z)) (C h2 h4)) (S (h v1 z v3))) (h v1 z (M y z))) (C h2 h0)) h0

@[equational_result]
theorem Equation4007_implies_Equation3414 (G: Type _) [Magma G] (h: Equation4007 G) : Equation3414 G := fun x y z =>
  let v0 := M z (M x y)
  let v1 := M z v0
  have h2 := R v1
  have h3 := R z
  have h4 := h x y x
  let v5 := M x (M y x)
  T (T (T h4 (h v5 x v1)) (C (C h2 (T (h x v5 z) (C (C h3 (S h4)) h3))) h2)) (S (h z v0 v1))

@[equational_result]
theorem Equation4117_implies_Equation4153 (G: Type _) [Magma G] (h: Equation4117 G) : Equation4153 G := fun x y z w u =>
  let v0 := M x z
  let v1 := M v0 v0
  have h2 := T (h x x) (S (h x z))
  let v3 := M x x
  T (T (T (T (h x y) (C (T (T (h v3 x) (S (h v3 v3))) (C h2 h2)) (R x))) (h v1 x)) (S (h v1 u))) (C (T (h v0 v0) (S (h v0 w))) (R u))

@[equational_result]
theorem Equation492_implies_Equation2180 (G: Type _) [Magma G] (h: Equation492 G) : Equation2180 G := fun x y z =>
  let v0 := M x z
  have h1 := R v0
  let v2 := M y z
  let v3 := M v2 y
  T (h x v3 v0) (C (R v3) (T (C (R x) (C h1 (C h1 (T (T (T (C (R v2) (h y z y)) (S (h z v2 y))) (h z v0 x)) (C h1 (S (h x z x))))))) (S (h v0 x v0))))

@[equational_result]
theorem Equation962_implies_Equation2586 (G: Type _) [Magma G] (h: Equation962 G) : Equation2586 G := fun x y z =>
  let v0 := M z y
  let v1 := M v0 x
  let v2 := M y v1
  let v3 := M v0 v2
  have h4 := R v0
  T (h x v2 v0) (C (R v2) (T (C (R v3) (C (T (h x y z) (C (R y) (C h4 (T (C (R x) (h z v1 y)) (S (h v2 x v0)))))) h4)) (S (h z v3 y))))

@[equational_result]
theorem Equation1640_implies_Equation153 (G: Type _) [Magma G] (h: Equation1640 G) : Equation153 G := fun x y =>
  let v0 := M x x
  have h1 := h x v0 (M v0 x)
  have h2 := R x
  have h3 := h x x x
  have h4 := R v0
  T (T (T h1 (C h4 (C (S h3) h2))) (h (M v0 v0) (M y y) (M v0 y))) (C (S (h v0 x x)) (C (S (h y x x)) (T (C h4 (C h3 h2)) (S h1))))

@[equational_result]
theorem Equation2552_implies_Equation952 (G: Type _) [Magma G] (h: Equation2552 G) : Equation952 G := fun x y z =>
  let v0 := M z y
  let v1 := M (M z x) v0
  let v2 := M x (M (M x v0) z)
  have h3 := h z x v0
  T (h x z v1) (C (T (T (C (R z) (S (h v0 z x))) (C (T h3 (C (R v2) (C h3 (R y)))) (R v0))) (S (h y v2 v0))) (R v1))

@[equational_result]
theorem Equation2714_implies_Equation1793 (G: Type _) [Magma G] (h: Equation2714 G) : Equation1793 G := fun x y z =>
  let v0 := M z y
  let v1 := M v0 x
  let v2 := M y z
  let v3 := M v2 v1
  T (T (h x y y) (C (C (T (T (T (C (h y z v1) (R x)) (S (h (M z v1) v0 x))) (C (h z y v3) (R v1))) (S (h (M y v3) v2 v1))) (R (M y y))) (R y))) (S (h v3 y y))

@[equational_result]
theorem Equation2722_implies_Equation1764 (G: Type _) [Magma G] (h: Equation2722 G) : Equation1764 G := fun x y z =>
  let v0 := M x z
  let v1 := M (M y z) (M v0 y)
  have h2 := R x
  let v3 := M v0 v1
  T (T (h x v0 x) (C (C (T (C (T (h v0 v1 v0) (C (C (S (h z y v0)) (R v3)) (R v0))) h2) (S (h v3 z x))) (R (M x v0))) h2)) (S (h v1 v0 x))

@[equational_result]
theorem Equation2944_implies_Equation2958 (G: Type _) [Magma G] (h: Equation2944 G) : Equation2958 G := fun x y z =>
  let v0 := M (M y (M y z)) x
  let v1 := M v0 z
  let v2 := M (M x (M x v1)) v1
  have h3 := R x
  have h4 := h v1 x v1
  T (T (h x v0 x) (C (C (T (T (C (R v0) (S (h z y x))) h4) (C (R v2) h4)) h3) h3)) (S (h v1 v2 x))

@[equational_result]
theorem Equation3131_implies_Equation1293 (G: Type _) [Magma G] (h: Equation3131 G) : Equation1293 G := fun x y z =>
  let v0 := M x y
  let v1 := M v0 z
  let v2 := M v1 z
  have h3 := R v2
  T (h x v0 x) (C (S (h y x x)) (T (h v0 z v2) (C (T (C (T (T (C (C (h z v0 z) (R v0)) h3) (S (h z v2 v0))) (h z v1 v1)) h3) (S (h v1 v2 v1))) (R z))))

@[equational_result]
theorem Equation3276_implies_Equation4346 (G: Type _) [Magma G] (h: Equation3276 G) : Equation4346 G := fun x y z =>
  let v0 := M y y
  let v1 := M z z
  let v2 := M y v1
  T (T (T (C (R x) (T (h y v0 v1) (C (R v0) (S (h v1 y z))))) (S (h v0 x v1))) (h v0 y v1)) (C (R y) (T (T (T (S (h v1 v0 z)) (h v1 v2 v0)) (C (R v2) (T (S (h v0 v1 y)) (h v0 z y)))) (S (h z v2 v0))))

@[equational_result]
theorem Equation3573_implies_Equation4497 (G: Type _) [Magma G] (h: Equation3573 G) : Equation4497 G := fun x y z =>
  let v0 := M z z
  let v1 := M v0 x
  let v2 := M v0 v0
  let v3 := M (M v1 v1) x
  let v4 := M y y
  T (T (T (T (T (h x v4 v1) (h v4 v3 v0)) (C (R v3) (T (h v2 v4 z) (C (R v4) (S (h v0 v0 z)))))) (S (h v2 v3 y))) (S (h x v2 v1))) (S (h v0 x z))

@[equational_result]
theorem Equation3791_implies_Equation3370 (G: Type _) [Magma G] (h: Equation3791 G) : Equation3370 G := fun x y z =>
  let v0 := M z x
  let v1 := M z v0
  let v2 := M v0 y
  let v3 := M y z
  T (T (T (T (h x y z) (h v0 v3 v1)) (C (h v1 v0 y) (T (T (T (C (h y z v0) (h z v0 y)) (S (h v1 v3 v2))) (S (h v0 y z))) (h v0 y v1)))) (S (h v2 (M v1 v0) (M y v1)))) (S (h y v1 v0))

@[equational_result]
theorem Equation3791_implies_Equation4358 (G: Type _) [Magma G] (h: Equation3791 G) : Equation4358 G := fun x y z =>
  let v0 := M z y
  let v1 := M y z
  have h2 := h z z y
  T (T (h x v1 v0) (C (R (M v0 x)) (T (T (T (S h2) (h z z z)) (C h2 (T (T h2 (h v1 v0 (M z z))) (C (S (h z y z)) (S (h y z z)))))) (S (h v0 v0 v1))))) (S (h x v0 v0))

@[equational_result]
theorem Equation4013_implies_Equation4182 (G: Type _) [Magma G] (h: Equation4013 G) : Equation4182 G := fun x y z =>
  let v0 := M y z
  let v1 := M (M v0 z) x
  let v2 := M y (M z y)
  let v3 := M v1 (M v0 v1)
  T (h x y z) (C (T (T (T (T (T (h z v0 v1) (h v3 z z)) (C (C (R z) (h z z y)) (R v3))) (S (h v3 v2 z))) (S (h v2 v0 v1))) (S (h v0 z y))) (R x))

@[equational_result]
theorem Equation4026_implies_Equation3370 (G: Type _) [Magma G] (h: Equation4026 G) : Equation3370 G := fun x y z =>
  let v0 := M z x
  let v1 := M z v0
  have h2 := C (R v1) (h v1 x z)
  let v3 := M v0 (M v0 y)
  T (T (T (T (T (T (T (T (h x y v0) (h v3 x v1)) (C h2 (R v3))) (S (h v3 v1 v1))) (S (h v1 y v0))) (S (h y x z))) (h y x v1)) (C h2 (R y))) (S (h y v1 v1))

@[equational_result]
theorem Equation4097_implies_Equation369 (G: Type _) [Magma G] (h: Equation4097 G) : Equation369 G := fun x y z =>
  have h0 := R z
  have h1 := h y x x
  have h2 := h x x x
  let v3 := M x x
  have h4 := S h2
  T (T (h x z (M y y)) (C (C (T (h z x x) h4) (T h1 h4)) h0)) (C (T (T (T (C (h x x v3) (R v3)) (S (h x v3 x))) h2) (S h1)) h0)

@[equational_result]
theorem Equation4133_implies_Equation4136 (G: Type _) [Magma G] (h: Equation4133 G) : Equation4136 G := fun x y z w =>
  let v0 := M x y
  let v1 := M v0 z
  have h2 := R v1
  have h3 := h x y z
  T (T (T (T h3 (h v1 x x)) (C (T (T (T (C (S h3) (R x)) (h v0 x x)) (C (T (S (h x y x)) h3) (R v0))) (S (h v0 z x))) h2)) (C (h v0 z w) h2)) (S (h v1 w v0))

@[equational_result]
theorem Equation4210_implies_Equation4362 (G: Type _) [Magma G] (h: Equation4210 G) : Equation4362 G := fun x y z =>
  let v0 := M x z
  let v1 := M y z
  let v2 := M x v1
  have h3 := R v2
  T (T (h x v1 x) (C (T (h v2 x y) (C (T (T (C (T (h y x v1) (C (S (h x z y)) (R v1))) h3) (C (h v0 v1 x) h3)) (S (h x v0 v2))) (R y))) (R x))) (S (h y v0 x))

@[equational_result]
theorem Equation4216_implies_Equation4146 (G: Type _) [Magma G] (h: Equation4216 G) : Equation4146 G := fun x y z =>
  let v0 := M x z
  let v1 := M v0 z
  let v2 := M v1 y
  let v3 := M v2 v1
  have h4 := R y
  T (T (T (T (h x y v1) (h v3 x y)) (C (T (C (T (h y x v0) (C (S (h v0 z x)) h4)) h4) (h v2 y v1)) (R v3))) (S (h v3 v1 v2))) (S (h v1 y v1))

@[equational_result]
theorem Equation4229_implies_Equation3573 (G: Type _) [Magma G] (h: Equation4229 G) : Equation3573 G := fun x y z =>
  let v0 := M z z
  let v1 := M v0 x
  have h2 := T (h v0 x z) (h v1 v0 z)
  let v3 := M y v1
  let v4 := M (M v3 v3) y
  T (T (T (T (T (T (h x y v3) (h v4 x z)) (C h2 (R v4))) (S (h v4 v1 v0))) (S (h v1 y v3))) (C h2 (R y))) (S (h y v1 v0))

@[equational_result]
theorem Equation543_implies_Equation1152 (G: Type _) [Magma G] (h: Equation543 G) : Equation1152 G := fun x y z =>
  let v0 := M z (M x y)
  let v1 := M y (M v0 z)
  have h2 := R v1
  have h3 := R y
  T (T (h x y v0) (C h3 (C (R v0) (T (T (S (h z x y)) (h z v1 y)) (C h2 (C h3 (T (C (R z) (C h2 (h y v0 z))) (S (h v0 z v1))))))))) (S (h v1 y v0))

@[equational_result]
theorem Equation2076_implies_Equation2079 (G: Type _) [Magma G] (h: Equation2076 G) : Equation2079 G := fun x y z =>
  let v0 := M (M x y) z
  let v1 := M z y
  let v2 := M v0 v1
  let v3 := M y z
  T (T (h x z v0) (C (C (T (C (T (h x y z) (C (h v0 v1 z) (R v3))) (h z y z)) (S (h (M v2 z) (M v1 z) v3))) (R v0)) (R (M z v0)))) (S (h v2 z v0))

@[equational_result]
theorem Equation3128_implies_Equation556 (G: Type _) [Magma G] (h: Equation3128 G) : Equation556 G := fun x y z =>
  let v0 := M x z
  let v1 := M y v0
  let v2 := M z v1
  let v3 := M y v2
  have h4 := R y
  T (T (T (h x v1 y) (C (C (T (C (C (T (h v1 v1 y) (C (S (h v0 y v1)) h4)) (R x)) h4) (S (h z x y))) (R v1)) h4)) (C (h v2 y v3) h4)) (S (h v3 v3 y))

@[equational_result]
theorem Equation3211_implies_Equation1152 (G: Type _) [Magma G] (h: Equation3211 G) : Equation1152 G := fun x y z =>
  let v0 := M x y
  let v1 := M z v0
  have h2 := R v0
  have h3 := R v1
  T (T (h x v0 y) (C (S (h y x y)) h2)) (C (R y) (T (h v0 z v1) (C (T (C (C (C (T (h z v1 v0) (C (S (h v0 z v0)) h3)) h3) h3) h2) (S (h v1 v0 v1))) (R z))))

@[equational_result]
theorem Equation3567_implies_Equation4216 (G: Type _) [Magma G] (h: Equation3567 G) : Equation4216 G := fun x y z =>
  let v0 := M (M z y) z
  have h1 := R x
  let v2 := M (M y y) y
  let v3 := M (M v0 x) v0
  T (T (T (T (T (T (h x y v0) (h y v3 y)) (h v3 v2 x)) (C (R v2) (C (S (h x x v0)) h1))) (S (h x v2 x))) (C h1 (C (h y y z) (R y)))) (S (h v0 x y))

@[equational_result]
theorem Equation3791_implies_Equation4450 (G: Type _) [Magma G] (h: Equation3791 G) : Equation4450 G := fun x y z =>
  let v0 := M y x
  let v1 := M y z
  let v2 := M v0 y
  T (T (T (T (T (T (h x v0 y) (h v0 v2 (M x v0))) (C (S (h v0 y x)) (S (h y x v0)))) (h v2 v0 v1)) (C (T (S (h z v0 y)) (h z v0 v1)) (h v0 v1 z))) (S (h (M v0 v1) (M z v0) (M v1 z)))) (S (h v1 z v0))

@[equational_result]
theorem Equation3804_implies_Equation4358 (G: Type _) [Magma G] (h: Equation3804 G) : Equation4358 G := fun x y z =>
  let v0 := M z y
  let v1 := M x v0
  let v2 := M v0 v0
  let v3 := M y y
  T (T (T (T (T (h x (M y z) v0) (C (S (h y y z)) (R v1))) (h v3 v1 v0)) (C (R (M v0 v1)) (T (h v3 v0 v0) (C (R v2) (S (h z y y)))))) (S (h v2 v1 v0))) (S (h x v0 v0))

@[equational_result]
theorem Equation3804_implies_Equation4458 (G: Type _) [Magma G] (h: Equation3804 G) : Equation4458 G := fun x y z =>
  let v0 := M z y
  let v1 := M v0 z
  let v2 := M y x
  T (T (T (h x v2 v0) (h (M v0 v2) (M x v0) v1)) (C (S (h x z v0)) (T (C (T (T (C (h z y y) (h y x y)) (S (h v2 v0 (M y y)))) (S (h z x y))) (R v1)) (S (h v0 x z))))) (S (h v0 z x))

@[equational_result]
theorem Equation4182_implies_Equation4023 (G: Type _) [Magma G] (h: Equation4182 G) : Equation4023 G := fun x y z =>
  let v0 := M z x
  let v1 := M z v0
  let v2 := M (M y v1) v1
  have h3 := R x
  T (T (T (T (h x y v1) (h v2 x x)) (C (C (T (h x x z) (C (T (C (h x z x) (R z)) (S (h z v0 x))) h3)) h3) (R v2))) (S (h v2 v1 x))) (S (h v1 y v1))

@[equational_result]
theorem Equation711_implies_Equation684 (G: Type _) [Magma G] (h: Equation711 G) : Equation684 G := fun x y z =>
  let v0 := M x (M (M y z) z)
  let v1 := M y v0
  let v2 := M v1 (M (M v1 x) x)
  have h3 := h v1 v1 x
  have h4 := R x
  T (T (h x x v0) (C h4 (C h4 (T (T (C (S (h y x z)) (R v0)) h3) (C h3 (R v2)))))) (S (h v1 x v2))

@[equational_result]
theorem Equation1571_implies_Equation4362 (G: Type _) [Magma G] (h: Equation1571 G) : Equation4362 G := fun x y z =>
  let v0 := M x z
  let v1 := M y v0
  have h2 := h x y v0
  have h3 := S (h v1 y z)
  let v4 := M y z
  T (C h2 (T (T (h v4 v4 (M y (M v1 z))) (C h3 (T (C (R v4) h3) (S (h x y z))))) (C (R v1) h2))) (S (h v1 v1 (M y (M x v0))))

@[equational_result]
theorem Equation2068_implies_Equation2688 (G: Type _) [Magma G] (h: Equation2068 G) : Equation2688 G := fun x y z =>
  let v0 := M z z
  let v1 := M x y
  let v2 := M v1 v0
  let v3 := M v2 y
  have h4 := R v0
  T (T (h x y z) (C (C (T (T (h v1 v0 x) (C (C (h v2 y z) h4) (R (M x x)))) (S (h (M v3 y) v0 x))) (R y)) h4)) (S (h v3 y z))

@[equational_result]
theorem Equation2170_implies_Equation3601 (G: Type _) [Magma G] (h: Equation2170 G) : Equation3601 G := fun x y z =>
  let v0 := M x y
  let v1 := M y x
  let v2 := M v1 z
  let v3 := M z v2
  T (T (h v0 v1 v0) (C (T (T (S (h v0 y x)) (h v0 v2 z)) (C (C (T (C (h v2 x y) (h z y x)) (S (h v1 v0 v2))) (R v0)) (R v3))) (R (M v0 v1)))) (S (h v3 v1 v0))

@[equational_result]
theorem Equation3356_implies_Equation3451 (G: Type _) [Magma G] (h: Equation3356 G) : Equation3451 G := fun x y z w u =>
  let v0 := M u y
  let v1 := M v0 v0
  have h2 := T (h y y) (S (h u y))
  let v3 := M y y
  T (T (T (T (h x y) (C (R y) (T (T (h y v3) (S (h v3 v3))) (C h2 h2)))) (h y v1)) (S (h z v1))) (C (R z) (T (h v0 v0) (S (h w v0))))

@[equational_result]
theorem Equation3573_implies_Equation3943 (G: Type _) [Magma G] (h: Equation3573 G) : Equation3943 G := fun x y z =>
  let v0 := M z z
  let v1 := M v0 v0
  let v2 := M v0 x
  have h3 := R y
  T (T (T (h x y z) (C h3 (T (h v0 x z) (h x v1 z)))) (C h3 (T (T (T (h v1 v2 z) (C (R v2) (S (h v0 v0 z)))) (h v2 v1 z)) (C (R v1) (S (h x v0 z)))))) (S (h (M x v0) y v0))

@[equational_result]
theorem Equation3601_implies_Equation4135 (G: Type _) [Magma G] (h: Equation3601 G) : Equation4135 G := fun x y z =>
  let v0 := M (M x y) z
  let v1 := M v0 z
  have h2 := R v1
  have h3 := R z
  have h4 := h x y x
  let v5 := M (M y x) x
  T (T (T h4 (h x v5 v1)) (C h2 (C (T (h v5 x z) (C h3 (C (S h4) h3))) h2))) (S (h v0 z v1))

@[equational_result]
theorem Equation3791_implies_Equation3903 (G: Type _) [Magma G] (h: Equation3791 G) : Equation3903 G := fun x y z =>
  let v0 := M z y
  let v1 := M y v0
  T (T (T (T (T (T (h x x z) (h (M z x) (M x z) (M x x))) (C (S (h x z x)) (S (h z x x)))) (S (h z z x))) (h z z v0)) (C (T (T (h v0 z y) (h v1 v0 (M v0 z))) (C (S (h z y v0)) (S (h y v0 z)))) (R (M z v0)))) (S (h v1 z v0))

@[equational_result]
theorem Equation3791_implies_Equation4612 (G: Type _) [Magma G] (h: Equation3791 G) : Equation4612 G := fun x y z =>
  let v0 := M y z
  let v1 := M y y
  T (T (T (T (C (T (T (T (h x x y) (C (h y x y) (h x y y))) (S (h (M x y) (M y x) v1))) (S (h y y x))) (R y)) (h v1 y v0)) (C (T (S (h z y y)) (h z y v0)) (h y v0 z))) (S (h (M y v0) (M z y) (M v0 z)))) (S (h v0 z y))

@[equational_result]
theorem Equation830_implies_Equation9 (G: Type _) [Magma G] (h: Equation830 G) : Equation9 G := fun x y =>
  let v0 := M y y
  let v1 := M x y
  let v2 := M x v1
  have h3 := R x
  T (h x v2 y) (C h3 (C (T (C h3 (h v2 v2 v2)) (S (h x v1 (M v2 v2)))) (T (C (R y) (T (h y y y) (C (h y x x) (R (M v0 v0))))) (S (h y (M (M y x) (M x x)) v0)))))

@[equational_result]
theorem Equation1064_implies_Equation11 (G: Type _) [Magma G] (h: Equation1064 G) : Equation11 G := fun x y =>
  let v0 := M (M x (M x x)) x
  let v1 := M y y
  have h2 := R y
  have h3 := h v0 x x
  have h4 := R v1
  T (h x v1 v0) (C (R x) (T (T (C (T (C h4 (S h3)) (S (h v1 x x))) h4) (C h4 (C (T (h y x x) (C h2 h3)) h2))) (S (h v1 y v0))))

@[equational_result]
theorem Equation1577_implies_Equation1590 (G: Type _) [Magma G] (h: Equation1577 G) : Equation1590 G := fun x y z =>
  let v0 := M y x
  let v1 := M z v0
  let v2 := M y z
  let v3 := M v2 v1
  let v4 := M z y
  T (T (h x v0 z) (C (R (M v0 z)) (C (R v0) (T (C (h z z y) (T (h x z y) (C (R v4) (h v1 z v2)))) (S (h (M z v3) v4 (M z v2))))))) (S (h v3 v0 z))

@[equational_result]
theorem Equation2196_implies_Equation1670 (G: Type _) [Magma G] (h: Equation2196 G) : Equation1670 G := fun x y z =>
  let v0 := M z y
  let v1 := M v0 z
  let v2 := M x y
  let v3 := M v2 v1
  T (T (h x y v1) (C (T (h (M (M y v1) v1) v0 z) (C (R (M v1 z)) (S (h z y v1)))) (T (C (h x y v2) (h y v2 v1)) (S (h (M v3 v1) (M y v2) v2))))) (S (h v3 v1 z))

@[equational_result]
theorem Equation2722_implies_Equation1098 (G: Type _) [Magma G] (h: Equation2722 G) : Equation1098 G := fun x y z =>
  let v0 := M z y
  let v1 := M x v0
  let v2 := M v1 z
  let v3 := M v2 v0
  have h4 := R v0
  T (h x v0 v2) (C (T (C (C h4 (T (h x y z) (C (C (T (C (h y z v1) (R x)) (S (h v2 v0 x))) h4) (R z)))) (R v3)) (S (h y z v3))) (R v2))

@[equational_result]
theorem Equation546_implies_Equation1967 (G: Type _) [Magma G] (h: Equation546 G) : Equation1967 G := fun x y z =>
  let v0 := M z y
  let v1 := M z x
  let v2 := M y v1
  have h3 := R v2
  have h4 := R x
  have h5 := R v0
  T (h x v2 v0) (C h3 (T (C h5 (C h4 (C h5 (T (h v2 x z) (C h4 (C (R z) (T (C h3 (h v1 v1 y)) (S (h y v2 v1))))))))) (S (h v0 v0 x))))

@[equational_result]
theorem Equation1089_implies_Equation2 (G: Type _) [Magma G] (h: Equation1089 G) : Equation2 G := fun x y =>
  let v0 := M y x
  let v1 := M (M x v0) y
  have h2 := R y
  let v3 := M (M x (M x x)) x
  T (T (T (h x y (M (M v3 v0) y)) (C h2 (C (T (C (R x) (S (h v3 y x))) (S (h x x x))) h2))) (C h2 (C (T (h x y x) (C h2 (h v1 y x))) h2))) (S (h y y (M (M v1 v0) y)))

@[equational_result]
theorem Equation1967_implies_Equation3607 (G: Type _) [Magma G] (h: Equation1967 G) : Equation3607 G := fun x y z =>
  let v0 := M y z
  let v1 := M z (M v0 x)
  let v2 := M v0 v1
  have h3 := R v2
  let v4 := M x y
  T (T (h v4 v1 v0) (C (C (R v1) (T (C (C (R y) (T (h z v1 v0) (C (S (h x z v0)) h3))) (R v4)) (S (h v2 y x)))) h3)) (S (h v1 v1 v0))

@[equational_result]
theorem Equation2102_implies_Equation2 (G: Type _) [Magma G] (h: Equation2102 G) : Equation2 G := fun x y =>
  let v0 := M y y
  let v1 := M y x
  let v2 := M v1 y
  have h3 := h x y x
  have h4 := R v2
  have h5 := h x y y
  T (T h5 (C (C (T (C (T (T (h y v1 y) (C (S h3) h4)) (C h5 h4)) h3) (S (h v0 v2 v1))) (R y)) (R v0))) (S (h y y y))

@[equational_result]
theorem Equation2113_implies_Equation4673 (G: Type _) [Magma G] (h: Equation2113 G) : Equation4673 G := fun x y z =>
  let v0 := M x z
  let v1 := M v0 y
  have h2 := h z v0 y
  have h3 := S (h v1 x y)
  let v4 := M x y
  T (C (T (T (h v4 (M (M x v1) y) v4) (C (T (C h3 (R v4)) (S (h z x y))) h3)) (C h2 (R v1))) h2) (S (h v1 (M (M v0 z) y) v1))

@[equational_result]
theorem Equation2753_implies_Equation28 (G: Type _) [Magma G] (h: Equation2753 G) : Equation28 G := fun x y =>
  let v0 := M y x
  let v1 := M v0 v0
  have h2 := S (h v0 v1 (M (M x x) (M x v0)))
  have h3 := R v0
  have h4 := C (R (M v1 v1)) (h v0 x x)
  have h5 := h v0 v0 v0
  T (h x v0 y) (C (T (C (T (T (T (C (T h5 h4) h3) h2) h5) h4) h3) h2) (R x))

@[equational_result]
theorem Equation3211_implies_Equation1504 (G: Type _) [Magma G] (h: Equation3211 G) : Equation1504 G := fun x y z =>
  let v0 := M y z
  let v1 := M z v0
  let v2 := M y x
  have h3 := R v2
  T (h x v1 v2) (C (T (C (C (C (T (T (T (C (h z y z) (R v0)) (S (h y v0 z))) (h y v2 x)) (C (S (h x y x)) h3)) h3) h3) (R x)) (S (h v2 x v2))) (R v1))

@[equational_result]
theorem Equation3211_implies_Equation2373 (G: Type _) [Magma G] (h: Equation3211 G) : Equation2373 G := fun x y z =>
  let v0 := M x z
  let v1 := M z v0
  let v2 := M y v1
  have h3 := R v2
  T (T (T (h x v0 z) (C (S (h z x z)) (R v0))) (h v1 y v2)) (C (T (C (C (C (T (h y v2 v1) (C (S (h v1 y v1)) h3)) h3) h3) (R v1)) (S (h v2 v1 v2))) (R y))

@[equational_result]
theorem Equation3211_implies_Equation2992 (G: Type _) [Magma G] (h: Equation3211 G) : Equation2992 G := fun x y z =>
  let v0 := M z y
  let v1 := M y v0
  let v2 := M v1 x
  have h3 := R v2
  T (h x z v2) (C (T (C (C (C (T (T (T (h z v0 y) (C (S (h y z y)) (R v0))) (h v1 v2 x)) (C (S (h x v1 x)) h3)) h3) h3) (R x)) (S (h v2 x v2))) (R z))

@[equational_result]
theorem Equation3791_implies_Equation3497 (G: Type _) [Magma G] (h: Equation3791 G) : Equation3497 G := fun x y z =>
  let v0 := M z y
  let v1 := M v0 z
  T (T (T (T (T (T (h x x y) (h (M y x) (M x y) (M x x))) (C (S (h x y x)) (S (h y x x)))) (S (h y y x))) (h y y v0)) (C (R (M v0 y)) (T (T (h y v0 z) (h v0 v1 (M y v0))) (C (S (h v0 z y)) (S (h z y v0)))))) (S (h y v1 v0))

@[equational_result]
theorem Equation3791_implies_Equation4106 (G: Type _) [Magma G] (h: Equation3791 G) : Equation4106 G := fun x y z =>
  let v0 := M y z
  let v1 := M v0 y
  let v2 := M v1 z
  T (T (T (T (T (T (h x x v2) (h (M v2 x) (M x v2) (M x x))) (C (S (h x v2 x)) (S (h v2 x x)))) (S (h v2 v2 x))) (h v2 v2 (M z v0))) (C (S (h v0 v1 z)) (T (C (R v2) (h z v0 y)) (S (h z v0 v1))))) (S (h v1 z v0))

@[equational_result]
theorem Equation3791_implies_Equation4182 (G: Type _) [Magma G] (h: Equation3791 G) : Equation4182 G := fun x y z =>
  let v0 := M y z
  let v1 := M v0 z
  let v2 := M x v0
  let v3 := M z x
  T (T (T (T (h x y z) (h v3 v0 v1)) (C (T (T (T (C (h v0 z x) (h z x v0)) (S (h v3 v1 v2))) (S (h x v0 z))) (h x v0 v1)) (h v0 v1 x))) (S (h (M v0 v1) v2 (M v1 x)))) (S (h v1 x v0))

@[equational_result]
theorem Equation3804_implies_Equation4023 (G: Type _) [Magma G] (h: Equation3804 G) : Equation4023 G := fun x y z =>
  let v0 := M z x
  let v1 := M z v0
  have h2 := h x x z
  T (T (h x y x) (C (R (M x y)) (T (T (T h2 (h v0 (M x z) v0)) (C (S h2) (T (T (T (h v0 v0 v1) (C (h v1 v0 z) (R (M v0 v1)))) (S (h v0 (M v1 z) v1))) (S (h v1 x z))))) (S (h v1 x x))))) (S (h v1 y x))

@[equational_result]
theorem Equation508_implies_Equation3692 (G: Type _) [Magma G] (h: Equation508 G) : Equation3692 G := fun x y z =>
  let v0 := M y y
  let v1 := M z z
  have h2 := R v0
  let v3 := M x x
  have h4 := h v3 v0 x
  T (T (T (T h4 (C h2 (T (T (C h2 (T (T (C (R v3) (h v3 v3 x)) (S (h v3 v3 v3))) h4)) (S (h v0 v0 v3))) (h v0 v0 y)))) (S (h v0 v0 v0))) (h v0 v0 v1)) (C h2 (S (h v1 v0 z)))

@[equational_result]
theorem Equation949_implies_Equation26 (G: Type _) [Magma G] (h: Equation949 G) : Equation26 G := fun x y =>
  let v0 := M x y
  have h1 := h y y v0
  let v2 := M v0 y
  have h3 := R v0
  have h4 := h x v0 v2
  T h4 (C h3 (T (T (h (M (M v2 x) (M v0 v2)) y v0) (C (R y) (T (C (S h4) (C h1 h3)) (S (h (M v2 (M y v0)) x y))))) (S h1)))

@[equational_result]
theorem Equation1304_implies_Equation1340 (G: Type _) [Magma G] (h: Equation1304 G) : Equation1340 G := fun x y z =>
  let v0 := M (M (M y z) z) x
  let v1 := M y v0
  let v2 := M (M (M v1 x) x) v1
  have h3 := R x
  have h4 := h v1 v1 x
  T (T (h x x v0) (C h3 (C (T (T (C (S (h y x z)) (R v0)) h4) (C h4 (R v2))) h3))) (S (h v1 x v2))

@[equational_result]
theorem Equation1507_implies_Equation2992 (G: Type _) [Magma G] (h: Equation1507 G) : Equation2992 G := fun x y z =>
  let v0 := M z y
  let v1 := M y v0
  let v2 := M v1 x
  let v3 := M v2 z
  let v4 := M v2 v3
  T (T (T (h x v1 y) (C (R v2) (T (C (h y z v2) (R (M y v1))) (S (h v4 v0 y))))) (h (M v2 v4) (M v3 v2) v3)) (C (S (h v2 v3 v2)) (S (h z v2 v3)))

@[equational_result]
theorem Equation1764_implies_Equation3973 (G: Type _) [Magma G] (h: Equation1764 G) : Equation3973 G := fun x y z =>
  let v0 := M z x
  let v1 := M x y
  let v2 := M (M y v0) z
  have h3 := R v1
  let v4 := M v2 v0
  T (T (h v1 v1 v0) (C (R (M v1 v0)) (C (T (C h3 (C (T (h z v2 v0) (C (R v4) (S (h y z v0)))) (R x))) (S (h v4 x y))) h3))) (S (h v2 v1 v0))

@[equational_result]
theorem Equation2519_implies_Equation1793 (G: Type _) [Magma G] (h: Equation2519 G) : Equation1793 G := fun x y z =>
  let v0 := M (M z y) x
  let v1 := M (M y z) v0
  have h2 := R y
  have h3 := R v1
  T (T (h x y v0) (C (C h2 (T (T (S (h z x y)) (h z v1 y)) (C (C h3 (T (C (C (R z) (h y v0 z)) h3) (S (h v0 z v1)))) h2))) (R v0))) (S (h v1 y v0))

@[equational_result]
theorem Equation2552_implies_Equation4673 (G: Type _) [Magma G] (h: Equation2552 G) : Equation4673 G := fun x y z =>
  let v0 := M x y
  let v1 := M x z
  let v2 := M x (M v1 v0)
  let v3 := M v1 y
  have h4 := R v3
  have h5 := h v0 x z
  T (C (T h5 (C (R v2) (T (T (h z x v3) (C (C (R x) (S (h y x z))) h4)) (C h5 h4)))) (R z)) (S (h v3 v2 z))

@[equational_result]
theorem Equation3364_implies_Equation3334 (G: Type _) [Magma G] (h: Equation3364 G) : Equation3334 G := fun x y z =>
  let v0 := M z y
  let v1 := M z v0
  let v2 := M x v1
  let v3 := M v1 v2
  have h4 := R x
  T (T (T (T (h x y v1) (h y v3 x)) (C (R v3) (T (C h4 (T (h y x v0) (C h4 (S (h z v0 y))))) (h x v2 v1)))) (S (h v1 v3 v2))) (S (h x v1 v1))

@[equational_result]
theorem Equation3770_implies_Equation4226 (G: Type _) [Magma G] (h: Equation3770 G) : Equation4226 G := fun x y z =>
  let v0 := M z z
  have h1 := h z z z
  have h2 := S h1
  let v3 := M x v0
  have h4 := R v3
  T (T (h x y v0) (C (R (M y v0)) (T (T (T (h x v0 v0) (C h2 h4)) (h v0 v3 v0)) (C (T (C h4 h1) (S (h v0 x v0))) h2)))) (S (h (M v0 x) y v0))

@[equational_result]
theorem Equation492_implies_Equation2992 (G: Type _) [Magma G] (h: Equation492 G) : Equation2992 G := fun x y z =>
  let v0 := M z y
  have h1 := R v0
  let v2 := M y v0
  let v3 := M v2 x
  have h4 := R v3
  T (T (h x v3 v2) (C h4 (S (h v2 x v2)))) (C h4 (T (C (R y) (T (h v0 z v0) (C (R z) (C h1 (C h1 (T (C h1 (h z y z)) (S (h y v0 z)))))))) (S (h z y v0))))

@[equational_result]
theorem Equation556_implies_Equation2928 (G: Type _) [Magma G] (h: Equation556 G) : Equation2928 G := fun x y z =>
  let v0 := M x z
  let v1 := M y v0
  let v2 := M v1 z
  let v3 := M v2 y
  have h4 := R y
  T (T (T (h x y v1) (C h4 (C (R v1) (T (C h4 (C (R x) (C h4 (T (h v0 z v0) (C (R z) (S (h x v0 z))))))) (S (h z y x)))))) (C h4 (h v2 v3 y))) (S (h v3 y v3))

@[equational_result]
theorem Equation556_implies_Equation2982 (G: Type _) [Magma G] (h: Equation556 G) : Equation2982 G := fun x y z =>
  let v0 := M y (M z x)
  let v1 := M v0 z
  let v2 := M v1 y
  have h3 := R y
  T (T (h x y v0) (C h3 (C (R v0) (T (T (S (h z y x)) (h z y v2)) (C h3 (C (R v2) (T (C h3 (C (R z) (T (h v2 y v2) (C h3 (S (h v1 v2 y)))))) (S (h v0 y z))))))))) (S (h v2 y v0))

@[equational_result]
theorem Equation1079_implies_Equation2 (G: Type _) [Magma G] (h: Equation1079 G) : Equation2 G := fun x y =>
  let v0 := M y (M y x)
  let v1 := M v0 y
  have h2 := R y
  let v3 := M v0 x
  T (T (T (h x y (M (M v3 (M v3 x)) x)) (C h2 (C (T (C (R x) (S (h v3 x x))) (S (h y x x))) h2))) (C h2 (C (T (h y y x) (C h2 (h v1 y x))) h2))) (S (h y y (M (M v1 (M v1 x)) y)))

@[equational_result]
theorem Equation1507_implies_Equation725 (G: Type _) [Magma G] (h: Equation1507 G) : Equation725 G := fun x y z =>
  let v0 := M z x
  let v1 := M v0 z
  let v2 := M y (M y v1)
  have h3 := h z v0 v2
  let v4 := M v2 (M v2 v0)
  T (T (h x z y) (C (T (T (T (C h3 (h x z v0)) (S (h v4 v1 v0))) (h v4 v1 y)) (C (S h3) (R v2))) (R (M y (M y z))))) (S (h v2 z y))

@[equational_result]
theorem Equation1558_implies_Equation4458 (G: Type _) [Magma G] (h: Equation1558 G) : Equation4458 G := fun x y z =>
  let v0 := M y x
  have h1 := h x y x
  have h2 := S h1
  have h3 := R y
  have h4 := h y v0 (M x v0)
  have h5 := T h4 (C h2 (C h3 h2))
  T (T (T (C h1 (C h3 h1)) (S h4)) (h y z y)) (C (R (M z y)) (T (C h5 (C (R z) h5)) (S (h z x v0))))

@[equational_result]
theorem Equation1577_implies_Equation778 (G: Type _) [Magma G] (h: Equation1577 G) : Equation778 G := fun x y z =>
  let v0 := M z y
  let v1 := M v0 x
  let v2 := M y (M z v1)
  have h3 := h v2 y v0
  let v4 := M y v0
  let v5 := M y z
  T (T (h x y v0) (C (R v4) (T (C (h y y z) (T (h v1 y z) (C (R v5) h3))) (S (h (M y (M v0 v2)) v5 v4))))) (S h3)

@[equational_result]
theorem Equation1710_implies_Equation1746 (G: Type _) [Magma G] (h: Equation1710 G) : Equation1746 G := fun x y z =>
  let v0 := M z z
  let v1 := M v0 x
  let v2 := M (M y y) v1
  have h3 := h x v0 x
  let v4 := M (M x x) v0
  T (T (h x x v0) (C (T (T (T (C h3 (h x x z)) (S (h v4 v1 x))) (h v4 v1 y)) (C (S h3) (R v2))) (R (M (M v0 v0) x)))) (S (h v2 x v0))

