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
theorem Equation4030_implies_Equation41 (G: Type _) [Magma G] (h: Equation4030 G) : Equation41 G := fun x y z =>
  let v0 := M x (M x x)
  T (T (T (h x x x) (h v0 x x)) (S (h v0 y x))) (S (h y z x))

@[equational_result]
theorem Equation634_implies_Equation4 (G: Type _) [Magma G] (h: Equation634 G) : Equation4 G := fun x y =>
  let v0 := M x y
  T (h x y (M (M y v0) x)) (C (R x) (S (h y v0 x)))

@[equational_result]
theorem Equation684_implies_Equation711 (G: Type _) [Magma G] (h: Equation684 G) : Equation711 G := fun x y z =>
  let v0 := M (M x z) z
  T (h x y v0) (C (R y) (S (h (M y v0) x z)))

@[equational_result]
theorem Equation765_implies_Equation3997 (G: Type _) [Magma G] (h: Equation765 G) : Equation3997 G := fun x y z =>
  let v0 := M x z
  T (C (R x) (h y z v0)) (S (h (M (M z v0) y) x z))

@[equational_result]
theorem Equation918_implies_Equation2 (G: Type _) [Magma G] (h: Equation918 G) : Equation2 G := fun x y =>
  let v0 := M x x
  T (T (h x x x) (C (R x) (C (R v0) (h v0 y x)))) (S (h y x (M (M y y) (M v0 x))))

@[equational_result]
theorem Equation1026_implies_Equation411 (G: Type _) [Magma G] (h: Equation1026 G) : Equation411 G := fun x =>
  let v0 := M x (M x x)
  T (h x v0) (C (R x) (C (S (h x x)) (R v0)))

@[equational_result]
theorem Equation1465_implies_Equation4134 (G: Type _) [Magma G] (h: Equation1465 G) : Equation4134 G := fun x y z =>
  let v0 := M x y
  T (h v0 z (M y x)) (C (R (M v0 z)) (S (h y x z)))

@[equational_result]
theorem Equation1561_implies_Equation4162 (G: Type _) [Magma G] (h: Equation1561 G) : Equation4162 G := fun x y z =>
  let v0 := M y x
  T (h (M x y) v0 z) (C (R (M v0 z)) (S (h z x y)))

@[equational_result]
theorem Equation1577_implies_Equation4200 (G: Type _) [Magma G] (h: Equation1577 G) : Equation4200 G := fun x y z =>
  let v0 := M z x
  T (h (M x y) v0 z) (C (R (M v0 z)) (S (h y z x)))

@[equational_result]
theorem Equation1590_implies_Equation3997 (G: Type _) [Magma G] (h: Equation1590 G) : Equation3997 G := fun x y z =>
  let v0 := M x z
  T (h (M x y) z v0) (C (R (M z v0)) (S (h y x z)))

@[equational_result]
theorem Equation1673_implies_Equation2474 (G: Type _) [Magma G] (h: Equation1673 G) : Equation2474 G := fun x y z =>
  let v0 := M (M y y) z
  T (h x v0 z) (C (R (M x v0)) (S (h z z y)))

@[equational_result]
theorem Equation1718_implies_Equation1746 (G: Type _) [Magma G] (h: Equation1718 G) : Equation1746 G := fun x y z =>
  let v0 := M (M x x) x
  T (h x y) (C (R (M y y)) (T (h v0 z) (C (R (M z z)) (S (h x v0)))))

@[equational_result]
theorem Equation1761_implies_Equation2573 (G: Type _) [Magma G] (h: Equation1761 G) : Equation2573 G := fun x y z =>
  let v0 := M (M z x) y
  T (h x y v0) (C (R (M y v0)) (S (h z x y)))

@[equational_result]
theorem Equation1764_implies_Equation3185 (G: Type _) [Magma G] (h: Equation1764 G) : Equation3185 G := fun x y z =>
  let v0 := M (M y z) x
  T (h x v0 z) (C (R (M v0 z)) (S (h y x z)))

@[equational_result]
theorem Equation1835_implies_Equation1865 (G: Type _) [Magma G] (h: Equation1835 G) : Equation1865 G := fun x y z =>
  let v0 := M x (M x x)
  T (h x z) (C (T (h v0 y) (C (S (h x v0)) (R (M y y)))) (R (M z z)))

@[equational_result]
theorem Equation1862_implies_Equation1874 (G: Type _) [Magma G] (h: Equation1862 G) : Equation1874 G := fun x y z w =>
  T (h x y w) (C (T (h (M x (M y y)) y z) (C (S (h x y y)) (R (M y z)))) (R (M y w)))

@[equational_result]
theorem Equation1967_implies_Equation546 (G: Type _) [Magma G] (h: Equation1967 G) : Equation546 G := fun x y z =>
  let v0 := M x (M z y)
  T (h x v0 z) (C (S (h y x z)) (R (M z v0)))

@[equational_result]
theorem Equation1968_implies_Equation2 (G: Type _) [Magma G] (h: Equation1968 G) : Equation2 G := fun x y =>
  let v0 := M x (M y x)
  T (T (h x x y) (C (h v0 x y) (R (M y y)))) (S (h y (M x (M y v0)) y))

@[equational_result]
theorem Equation2253_implies_Equation203 (G: Type _) [Magma G] (h: Equation2253 G) : Equation203 G := fun x =>
  have h0 := R x
  let v1 := M x x
  T (h x (M v1 (M x (M v1 v1)))) (C (C h0 (S (h v1 x))) h0)

@[equational_result]
theorem Equation2888_implies_Equation3534 (G: Type _) [Magma G] (h: Equation2888 G) : Equation3534 G := fun x y z =>
  let v0 := M z y
  T (C (h x v0 z) (R y)) (S (h (M x (M v0 z)) z y))

@[equational_result]
theorem Equation2891_implies_Equation3331 (G: Type _) [Magma G] (h: Equation2891 G) : Equation3331 G := fun x y z =>
  let v0 := M y z
  T (C (h x z v0) (R y)) (S (h (M x (M z v0)) y z))

@[equational_result]
theorem Equation2958_implies_Equation2944 (G: Type _) [Magma G] (h: Equation2958 G) : Equation2944 G := fun x y z =>
  let v0 := M y (M y x)
  T (h x v0 z) (C (S (h (M v0 z) y x)) (R z))

@[equational_result]
theorem Equation2981_implies_Equation5 (G: Type _) [Magma G] (h: Equation2981 G) : Equation5 G := fun x y =>
  let v0 := M y x
  T (h x (M x (M v0 y)) y) (C (S (h y x v0)) (R x))

@[equational_result]
theorem Equation3147_implies_Equation4612 (G: Type _) [Magma G] (h: Equation3147 G) : Equation4612 G := fun x y z =>
  have h0 := R z
  let v1 := M (M x x) y
  T (h v1 v1 z) (C (C (S (h y x v1)) h0) h0)

@[equational_result]
theorem Equation3182_implies_Equation2573 (G: Type _) [Magma G] (h: Equation3182 G) : Equation2573 G := fun x y z =>
  let v0 := M (M z x) y
  T (h x v0 z) (C (C (S (h y z x)) (R v0)) (R z))

@[equational_result]
theorem Equation3214_implies_Equation2558 (G: Type _) [Magma G] (h: Equation3214 G) : Equation2558 G := fun x y z =>
  let v0 := M (M y z) z
  T (h x v0 y) (C (C (S (h y y z)) (R v0)) (R x))

@[equational_result]
theorem Equation3370_implies_Equation3553 (G: Type _) [Magma G] (h: Equation3370 G) : Equation3553 G := fun x y z =>
  T (h x y z) (C (R y) (T (C (R z) (h z x x)) (S (h (M x z) z x))))

@[equational_result]
theorem Equation3372_implies_Equation41 (G: Type _) [Magma G] (h: Equation3372 G) : Equation41 G := fun x y z =>
  let v0 := M x (M x x)
  T (T (T (h x x x) (h x v0 x)) (S (h z v0 x))) (S (h y z x))

@[equational_result]
theorem Equation3575_implies_Equation41 (G: Type _) [Magma G] (h: Equation3575 G) : Equation41 G := fun x y z =>
  let v0 := M (M x x) x
  T (T (T (h x x x) (h x v0 x)) (S (h z v0 x))) (S (h y z x))

@[equational_result]
theorem Equation3718_implies_Equation4508 (G: Type _) [Magma G] (h: Equation3718 G) : Equation4508 G := fun x y z =>
  T (T (h x (M y z) (M z z)) (C (h x x x) (S (h z z y)))) (S (h (M x x) z z))

@[equational_result]
theorem Equation3959_implies_Equation3994 (G: Type _) [Magma G] (h: Equation3959 G) : Equation3994 G := fun x y z =>
  have h0 := R z
  have h1 := h x y z
  T (T h1 (h (M y (M x z)) z z)) (C (C h0 (S h1)) h0)

@[equational_result]
theorem Equation3959_implies_Equation3997 (G: Type _) [Magma G] (h: Equation3959 G) : Equation3997 G := fun x y z =>
  T (T (h x y z) (C (C (R y) (h x z z)) (R z))) (S (h (M z (M x z)) y z))

@[equational_result]
theorem Equation4182_implies_Equation4026 (G: Type _) [Magma G] (h: Equation4182 G) : Equation4026 G := fun x y z =>
  T (h x y z) (C (T (C (h y z y) (R z)) (S (h z (M z y) y))) (R x))

@[equational_result]
theorem Equation1225_implies_Equation99 (G: Type _) [Magma G] (h: Equation1225 G) : Equation99 G := fun x =>
  have h0 := R x
  let v1 := M x x
  T (h x (M (M (M v1 v1) x) v1)) (C h0 (C (S (h v1 x)) h0))

@[equational_result]
theorem Equation1723_implies_Equation2 (G: Type _) [Magma G] (h: Equation1723 G) : Equation2 G := fun x y =>
  let v0 := M (M x y) x
  T (T (h x y x) (C (R (M y y)) (h v0 y x))) (S (h y y (M (M v0 y) x)))

@[equational_result]
theorem Equation2000_implies_Equation16 (G: Type _) [Magma G] (h: Equation2000 G) : Equation16 G := fun x y =>
  let v0 := M y y
  T (h x y y) (C (T (C (h y x y) (R v0)) (S (h y (M x v0) y))) (R (M y x)))

@[equational_result]
theorem Equation3397_implies_Equation3431 (G: Type _) [Magma G] (h: Equation3397 G) : Equation3431 G := fun x y z w =>
  let v0 := M x y
  T (h x y z) (C (R z) (T (h y v0 w) (C (R w) (S (h x y v0)))))

@[equational_result]
theorem Equation3690_implies_Equation3677 (G: Type _) [Magma G] (h: Equation3690 G) : Equation3677 G := fun x y =>
  let v0 := M y x
  let v1 := M v0 v0
  T (T (h x v0 x) (C (R v1) (h x v0 y))) (S (h v0 v0 v1))

@[equational_result]
theorem Equation3758_implies_Equation387 (G: Type _) [Magma G] (h: Equation3758 G) : Equation387 G := fun x y =>
  let v0 := M y y
  T (T (T (h x y) (h v0 (M x x))) (C (S (h x x)) (R (M v0 v0)))) (S (h v0 x))

@[equational_result]
theorem Equation3758_implies_Equation4358 (G: Type _) [Magma G] (h: Equation3758 G) : Equation4358 G := fun x y z =>
  C (R x) (T (T (T (h y z) (C (h z z) (h y y))) (S (h (M y y) (M z z)))) (S (h z y)))

@[equational_result]
theorem Equation3791_implies_Equation3756 (G: Type _) [Magma G] (h: Equation3791 G) : Equation3756 G := fun x y z =>
  T (h x y y) (C (R (M y x)) (T (T (T (h y y z) (C (h z y z) (h y z z))) (S (h (M y z) (M z y) (M z z)))) (S (h z z y))))

@[equational_result]
theorem Equation3804_implies_Equation3740 (G: Type _) [Magma G] (h: Equation3804 G) : Equation3740 G := fun x y z =>
  T (T (h x y z) (h (M z y) (M x z) (M z z))) (C (S (h x z z)) (S (h z y z)))

@[equational_result]
theorem Equation3804_implies_Equation3776 (G: Type _) [Magma G] (h: Equation3804 G) : Equation3776 G := fun x y z =>
  T (T (h x y z) (C (h z y x) (h x z y))) (S (h (M y z) (M z x) (M x y)))

@[equational_result]
theorem Equation3827_implies_Equation41 (G: Type _) [Magma G] (h: Equation3827 G) : Equation41 G := fun x y z =>
  T (T (h x x y) (C (R (M y y)) (T (h y x x) (S (h y y x))))) (S (h y z y))

@[equational_result]
theorem Equation714_implies_Equation511 (G: Type _) [Magma G] (h: Equation714 G) : Equation511 G := fun x y =>
  have h0 := R y
  have h1 := h x y
  T h1 (C h0 (T (h (M y (M (M y x) y)) y) (C h0 (C h0 (C (S h1) h0)))))

@[equational_result]
theorem Equation1316_implies_Equation707 (G: Type _) [Magma G] (h: Equation1316 G) : Equation707 G := fun x y =>
  have h0 := R y
  have h1 := h x y
  T h1 (C h0 (T (h (M (M (M y x) y) y) y) (C h0 (C (C (S h1) h0) h0))))

@[equational_result]
theorem Equation1872_implies_Equation1874 (G: Type _) [Magma G] (h: Equation1872 G) : Equation1874 G := fun x y z w =>
  let v0 := M x (M y z)
  T (T (h x y z) (C (h v0 y w) (R (M y y)))) (S (h (M v0 (M y w)) y y))

@[equational_result]
theorem Equation2273_implies_Equation208 (G: Type _) [Magma G] (h: Equation2273 G) : Equation208 G := fun x y =>
  have h0 := R x
  T (h x y (M x (M x (M x x)))) (C (C h0 (C (R y) (S (h x x x)))) h0)

@[equational_result]
theorem Equation2281_implies_Equation211 (G: Type _) [Magma G] (h: Equation2281 G) : Equation211 G := fun x y =>
  have h0 := R x
  let v1 := M y y
  T (h x (M v1 (M v1 v1)) y) (C (C h0 (S (h v1 v1 y))) h0)

@[equational_result]
theorem Equation2331_implies_Equation2940 (G: Type _) [Magma G] (h: Equation2331 G) : Equation2940 G := fun x y =>
  have h0 := R y
  have h1 := h x y
  T h1 (C (T (h (M y (M y (M x y))) y) (C (C h0 (C h0 (S h1))) h0)) h0)

@[equational_result]
theorem Equation2442_implies_Equation27 (G: Type _) [Magma G] (h: Equation2442 G) : Equation27 G := fun x y z =>
  let v0 := M x (M (M x x) x)
  T (h x z) (C (T (h v0 y) (C (S (h x (M (M v0 v0) v0))) (R y))) (R z))

@[equational_result]
theorem Equation2456_implies_Equation203 (G: Type _) [Magma G] (h: Equation2456 G) : Equation203 G := fun x =>
  have h0 := R x
  T (h x (M x (M (M x x) x))) (C (C h0 (C (S (h x x)) h0)) h0)

@[equational_result]
theorem Equation3310_implies_Equation38 (G: Type _) [Magma G] (h: Equation3310 G) : Equation38 G := fun x y =>
  let v0 := M y x
  T (T (h x x (M v0 x)) (C (R x) (S (h x v0 x)))) (S (h x y x))

@[equational_result]
theorem Equation3398_implies_Equation3932 (G: Type _) [Magma G] (h: Equation3398 G) : Equation3932 G := fun x y z =>
  let v0 := M y z
  let v1 := M x v0
  T (T (h x y v0) (C (R v0) (h y v1 z))) (S (h v1 z v0))

@[equational_result]
theorem Equation3672_implies_Equation3665 (G: Type _) [Magma G] (h: Equation3672 G) : Equation3665 G := fun x y =>
  let v0 := M x y
  let v1 := M v0 v0
  T (T (h x x v0) (C (h x y v0) (R v1))) (S (h v0 v1 v0))

@[equational_result]
theorem Equation3682_implies_Equation3709 (G: Type _) [Magma G] (h: Equation3682 G) : Equation3709 G := fun x y z w =>
  let v0 := M x x
  T (T (T (T (h x x x) (C (h x x z) (R v0))) (S (h (M z z) v0 x))) (S (h z z z))) (h z y w)

@[equational_result]
theorem Equation3716_implies_Equation327 (G: Type _) [Magma G] (h: Equation3716 G) : Equation327 G := fun x y z =>
  let v0 := M y z
  T (T (T (h x y z) (h (M x x) v0 z)) (C (S (h x x x)) (R (M v0 z)))) (S (h x v0 z))

@[equational_result]
theorem Equation3790_implies_Equation395 (G: Type _) [Magma G] (h: Equation3790 G) : Equation395 G := fun x y z =>
  let v0 := M z x
  T (T (T (h x y z) (h v0 (M y y) x)) (C (R (M x v0)) (S (h y y y)))) (S (h v0 y x))

@[equational_result]
theorem Equation4143_implies_Equation4146 (G: Type _) [Magma G] (h: Equation4143 G) : Equation4146 G := fun x y z =>
  T (T (h x y z) (C (C (h x z z) (R y)) (R z))) (S (h (M (M x z) z) y z))

@[equational_result]
theorem Equation4210_implies_Equation3617 (G: Type _) [Magma G] (h: Equation4210 G) : Equation3617 G := fun x y z =>
  let v0 := M z x
  let v1 := M v0 y
  T (T (h x y v0) (C (h v1 x z) (R v0))) (S (h z v1 v0))

@[equational_result]
theorem Equation4616_implies_Equation4609 (G: Type _) [Magma G] (h: Equation4616 G) : Equation4609 G := fun x y z =>
  let v0 := M x x
  T (T (h x y v0) (C (S (h x y x)) (R v0))) (S (h y z v0))

@[equational_result]
theorem Equation894_implies_Equation2 (G: Type _) [Magma G] (h: Equation894 G) : Equation2 G := fun x y =>
  let v0 := M x x
  T (T (h x x x) (C (R x) (C (h v0 y x) (R v0)))) (S (h y x (M (M v0 x) (M y y))))

@[equational_result]
theorem Equation898_implies_Equation2316 (G: Type _) [Magma G] (h: Equation898 G) : Equation2316 G := fun x y z =>
  let v0 := M z y
  let v1 := M x v0
  let v2 := M y v1
  T (h x v2 v0) (C (R v2) (S (h z v1 y)))

@[equational_result]
theorem Equation952_implies_Equation2552 (G: Type _) [Magma G] (h: Equation952 G) : Equation2552 G := fun x y z =>
  let v0 := M y z
  let v1 := M v0 x
  let v2 := M y v1
  T (h x v2 v0) (C (R v2) (S (h z v1 y)))

@[equational_result]
theorem Equation968_implies_Equation765 (G: Type _) [Magma G] (h: Equation968 G) : Equation765 G := fun x y z =>
  have h0 := h x y y
  T h0 (C (R y) (T (h (M (M y y) (M y x)) z y) (C (R z) (C (R (M y z)) (S h0)))))

@[equational_result]
theorem Equation968_implies_Equation1577 (G: Type _) [Magma G] (h: Equation968 G) : Equation1577 G := fun x y z =>
  let v0 := M z x
  T (T (h x x z) (C (R x) (C (R v0) (h v0 z y)))) (S (h (M (M y z) (M y v0)) x z))

@[equational_result]
theorem Equation1254_implies_Equation107 (G: Type _) [Magma G] (h: Equation1254 G) : Equation107 G := fun x y =>
  have h0 := R x
  let v1 := M y y
  T (h x y (M (M v1 v1) v1)) (C h0 (C (S (h v1 y v1)) h0))

@[equational_result]
theorem Equation1914_implies_Equation2 (G: Type _) [Magma G] (h: Equation1914 G) : Equation2 G := fun x y =>
  let v0 := M y (M y x)
  T (T (h x (M y (M v0 x)) x) (C (S (h v0 y x)) (R (M x x)))) (S (h y y x))

@[equational_result]
theorem Equation2677_implies_Equation2891 (G: Type _) [Magma G] (h: Equation2677 G) : Equation2891 G := fun x y z =>
  have h0 := h x y y
  T h0 (C (T (h (M (M x y) (M y y)) y z) (C (C (S h0) (R (M y z))) (R z))) (R y))

@[equational_result]
theorem Equation2685_implies_Equation2888 (G: Type _) [Magma G] (h: Equation2685 G) : Equation2888 G := fun x y z =>
  have h0 := h x x z
  T h0 (C (T (h (M (M x x) (M z x)) z y) (C (C (S h0) (R (M y z))) (R y))) (R z))

@[equational_result]
theorem Equation2726_implies_Equation2 (G: Type _) [Magma G] (h: Equation2726 G) : Equation2 G := fun x y =>
  let v0 := M x x
  T (T (h x x x) (C (C (h v0 x y) (R v0)) (R x))) (S (h y (M (M x v0) (M y y)) x))

@[equational_result]
theorem Equation2754_implies_Equation2 (G: Type _) [Magma G] (h: Equation2754 G) : Equation2 G := fun x y =>
  let v0 := M x x
  T (T (h x x x) (C (C (R v0) (h v0 y x)) (R x))) (S (h y x (M (M y y) (M x v0))))

@[equational_result]
theorem Equation2779_implies_Equation1090 (G: Type _) [Magma G] (h: Equation2779 G) : Equation1090 G := fun x y z =>
  let v0 := M y z
  let v1 := M x v0
  let v2 := M v1 z
  T (h x v2 v0) (C (S (h y v1 z)) (R v2))

@[equational_result]
theorem Equation2789_implies_Equation31 (G: Type _) [Magma G] (h: Equation2789 G) : Equation31 G := fun x y =>
  have h0 := S (h y x x)
  T (h x (M (M x x) (M x y)) x) (C (C h0 h0) (R x))

@[equational_result]
theorem Equation2805_implies_Equation1368 (G: Type _) [Magma G] (h: Equation2805 G) : Equation1368 G := fun x y z =>
  let v0 := M z y
  let v1 := M v0 x
  let v2 := M v1 z
  T (h x v2 v0) (C (S (h y v1 z)) (R v2))

@[equational_result]
theorem Equation3559_implies_Equation355 (G: Type _) [Magma G] (h: Equation3559 G) : Equation355 G := fun x y z w =>
  let v0 := M w y
  T (T (T (h x y) (C (R y) (T (h (M y y) y) (S (h w y))))) (h y v0)) (S (h z v0))

@[equational_result]
theorem Equation3573_implies_Equation4226 (G: Type _) [Magma G] (h: Equation3573 G) : Equation4226 G := fun x y z =>
  let v0 := M z z
  T (T (h x y z) (C (R y) (T (h v0 x z) (h x (M v0 v0) z)))) (S (h (M v0 x) y v0))

@[equational_result]
theorem Equation3751_implies_Equation4358 (G: Type _) [Magma G] (h: Equation3751 G) : Equation4358 G := fun x y z =>
  have h0 := h z y
  let v1 := M y z
  C (R x) (T (T (T (h y z) (C h0 h0)) (S (h v1 v1))) (S h0))

@[equational_result]
theorem Equation3778_implies_Equation41 (G: Type _) [Magma G] (h: Equation3778 G) : Equation41 G := fun x y z =>
  have h0 := h x x x
  T (T h0 (C (T h0 (S (h z x x))) (R (M x x)))) (S (h y z x))

@[equational_result]
theorem Equation3791_implies_Equation3776 (G: Type _) [Magma G] (h: Equation3791 G) : Equation3776 G := fun x y z =>
  T (T (h x y z) (h (M z x) (M y z) (M x y))) (C (S (h y z x)) (S (h z x y)))

@[equational_result]
theorem Equation3812_implies_Equation41 (G: Type _) [Magma G] (h: Equation3812 G) : Equation41 G := fun x y z =>
  let v0 := M x x
  let v1 := M y y
  T (T (T (h x x y) (h (M y x) v1 v0)) (S (h (M y z) v1 v0))) (S (h y z y))

@[equational_result]
theorem Equation4331_implies_Equation4346 (G: Type _) [Magma G] (h: Equation4331 G) : Equation4346 G := fun x y z =>
  let v0 := M z z
  T (T (S (h v0 y x)) (C (R v0) (S (h z z y)))) (h v0 z y)

@[equational_result]
theorem Equation919_implies_Equation1528 (G: Type _) [Magma G] (h: Equation919 G) : Equation1528 G := fun x y =>
  let v0 := M y x
  let v1 := M y y
  T (T (h x y) (C (R y) (C (R v1) (h v0 y)))) (S (h (M v1 (M y v0)) y))

@[equational_result]
theorem Equation981_implies_Equation1543 (G: Type _) [Magma G] (h: Equation981 G) : Equation1543 G := fun x y z =>
  let v0 := M z x
  T (T (h x z x) (C (R z) (C (R (M x x)) (h v0 z y)))) (S (h (M (M y y) (M z v0)) z x))

@[equational_result]
theorem Equation1061_implies_Equation452 (G: Type _) [Magma G] (h: Equation1061 G) : Equation452 G := fun x y z =>
  let v0 := M z (M y z)
  T (h x y v0) (C (R x) (C (S (h y z y)) (R v0)))

@[equational_result]
theorem Equation1090_implies_Equation1910 (G: Type _) [Magma G] (h: Equation1090 G) : Equation1910 G := fun x y z =>
  let v0 := M y (M x z)
  T (h x v0 z) (C (R v0) (C (S (h y x z)) (R z)))

@[equational_result]
theorem Equation1120_implies_Equation714 (G: Type _) [Magma G] (h: Equation1120 G) : Equation714 G := fun x y =>
  have h0 := R y
  have h1 := h x y
  T h1 (C h0 (T (h (M (M y (M y x)) y) y) (C h0 (C (C h0 (S h1)) h0))))

@[equational_result]
theorem Equation1171_implies_Equation1983 (G: Type _) [Magma G] (h: Equation1171 G) : Equation1983 G := fun x y z =>
  let v0 := M y (M z y)
  T (h x v0 z) (C (R v0) (C (S (h z z y)) (R x)))

@[equational_result]
theorem Equation1243_implies_Equation105 (G: Type _) [Magma G] (h: Equation1243 G) : Equation105 G := fun x y =>
  let v0 := M (M y x) y
  let v1 := M x v0
  T (h x y (M (M v1 x) v1)) (C (R x) (S (h v0 x v1)))

@[equational_result]
theorem Equation1470_implies_Equation3534 (G: Type _) [Magma G] (h: Equation1470 G) : Equation3534 G := fun x y z =>
  let v0 := M z y
  let v1 := M x y
  T (h v1 (M x v1) v0) (C (S (h x y x)) (C (R v0) (S (h z y x))))

@[equational_result]
theorem Equation1742_implies_Equation1816 (G: Type _) [Magma G] (h: Equation1742 G) : Equation1816 G := fun x y z w =>
  let v0 := M (M w z) x
  T (T (h x z w) (C (R (M z z)) (h v0 z y))) (S (h (M (M y z) v0) z z))

@[equational_result]
theorem Equation2372_implies_Equation221 (G: Type _) [Magma G] (h: Equation2372 G) : Equation221 G := fun x y =>
  let v0 := M y (M x y)
  let v1 := M v0 x
  T (h x (M v1 (M x v1)) y) (C (S (h v0 v1 x)) (R x))

@[equational_result]
theorem Equation2482_implies_Equation1670 (G: Type _) [Magma G] (h: Equation2482 G) : Equation1670 G := fun x y z =>
  let v0 := M (M z y) z
  T (h x y v0) (C (C (R x) (S (h y z y))) (R v0))

@[equational_result]
theorem Equation2552_implies_Equation1774 (G: Type _) [Magma G] (h: Equation2552 G) : Equation1774 G := fun x y z =>
  let v0 := M (M y x) z
  T (h x y v0) (C (C (R y) (S (h z y x))) (R v0))

@[equational_result]
theorem Equation2779_implies_Equation3182 (G: Type _) [Magma G] (h: Equation2779 G) : Equation3182 G := fun x y z =>
  have h0 := h x z z
  T h0 (C (T (h (M (M z z) (M x z)) y z) (C (C (R (M y z)) (S h0)) (R y))) (R z))

@[equational_result]
theorem Equation3128_implies_Equation2511 (G: Type _) [Magma G] (h: Equation3128 G) : Equation2511 G := fun x y z =>
  let v0 := M (M x y) z
  T (h x v0 z) (C (C (S (h y x z)) (R v0)) (R z))

@[equational_result]
theorem Equation3404_implies_Equation3729 (G: Type _) [Magma G] (h: Equation3404 G) : Equation3729 G := fun x y z =>
  let v0 := M x y
  T (h x y v0) (C (R v0) (T (C (R y) (T (h v0 x z) (C (R z) (S (h y z x))))) (S (h z z y))))

@[equational_result]
theorem Equation3686_implies_Equation3693 (G: Type _) [Magma G] (h: Equation3686 G) : Equation3693 G := fun x y z w =>
  let v0 := M x x
  T (T (T (T (h x x x) (C (R v0) (h x z x))) (S (h (M z z) x v0))) (S (h z z z))) (h z y w)

@[equational_result]
theorem Equation3751_implies_Equation43 (G: Type _) [Magma G] (h: Equation3751 G) : Equation43 G := fun x y =>
  have h0 := h x y
  have h1 := S h0
  let v2 := M y x
  T (T (T h0 (h v2 v2)) (C h1 h1)) (S (h y x))

@[equational_result]
theorem Equation3774_implies_Equation41 (G: Type _) [Magma G] (h: Equation3774 G) : Equation41 G := fun x y z =>
  have h0 := S (h z x x)
  let v1 := M x x
  T (T (T (h x x x) (h v1 v1 v1)) (C h0 h0)) (S (h y z x))

@[equational_result]
theorem Equation3793_implies_Equation41 (G: Type _) [Magma G] (h: Equation3793 G) : Equation41 G := fun x y z =>
  have h0 := S (h x y x)
  let v1 := M x x
  T (T (T (h x x x) (h v1 v1 v1)) (C h0 h0)) (S (h y z x))

@[equational_result]
theorem Equation3795_implies_Equation41 (G: Type _) [Magma G] (h: Equation3795 G) : Equation41 G := fun x y z =>
  let v0 := M y z
  T (T (h x x v0) (C (T (h v0 x x) (S (h v0 y x))) (R (M v0 v0)))) (S (h y z v0))

@[equational_result]
theorem Equation3979_implies_Equation3323 (G: Type _) [Magma G] (h: Equation3979 G) : Equation3323 G := fun x y z =>
  let v0 := M z z
  T (T (h x y z) (C (T (h y v0 z) (h (M v0 v0) y z)) (R x))) (S (h x (M y v0) v0))

@[equational_result]
theorem Equation4176_implies_Equation3820 (G: Type _) [Magma G] (h: Equation4176 G) : Equation3820 G := fun x y z =>
  let v0 := M x y
  T (h x y v0) (C (T (C (T (h y v0 z) (C (S (h z x y)) (R z))) (R x)) (S (h z z x))) (R v0))

@[equational_result]
theorem Equation4274_implies_Equation4365 (G: Type _) [Magma G] (h: Equation4274 G) : Equation4365 G := fun x y z w =>
  T (T (T (T (S (h y x z)) (h y y (M y y))) (C (R y) (h y z x))) (S (h z y (M y x)))) (h z y w)

@[equational_result]
theorem Equation625_implies_Equation49 (G: Type _) [Magma G] (h: Equation625 G) : Equation49 G := fun x y =>
  have h0 := R x
  T (h x y (M y (M (M x x) y))) (C h0 (C h0 (C (S (h y x x)) h0)))

@[equational_result]
theorem Equation914_implies_Equation1929 (G: Type _) [Magma G] (h: Equation914 G) : Equation1929 G := fun x y z =>
  let v0 := M y x
  T (T (h x y x) (C (R y) (C (h v0 y z) (R (M x x))))) (S (h (M (M y v0) (M z z)) y x))

@[equational_result]
theorem Equation934_implies_Equation1590 (G: Type _) [Magma G] (h: Equation934 G) : Equation1590 G := fun x y z =>
  let v0 := M y x
  T (T (h x x y) (C (R x) (C (R (M x y)) (h v0 y z)))) (S (h (M (M y z) (M z v0)) x y))

@[equational_result]
theorem Equation1230_implies_Equation100 (G: Type _) [Magma G] (h: Equation1230 G) : Equation100 G := fun x y =>
  have h0 := R x
  T (h x (M (M (M x x) x) x) y) (C h0 (C (C (S (h x x x)) h0) (R y)))

@[equational_result]
theorem Equation1234_implies_Equation101 (G: Type _) [Magma G] (h: Equation1234 G) : Equation101 G := fun x y =>
  have h0 := R x
  T (h x (M (M (M x x) x) x) y) (C h0 (C (C (S (h x x x)) (R y)) h0))

@[equational_result]
theorem Equation1471_implies_Equation27 (G: Type _) [Magma G] (h: Equation1471 G) : Equation27 G := fun x y z =>
  let v0 := M x (M x x)
  let v1 := M x y
  T (T (h x y x) (C (h v1 z x) (R v0))) (S (h (M v1 z) v0 x))

@[equational_result]
theorem Equation1913_implies_Equation1098 (G: Type _) [Magma G] (h: Equation1913 G) : Equation1098 G := fun x y z =>
  let v0 := M x (M z y)
  T (h x z v0) (C (T (C (h z x y) (R (M x v0))) (S (h y v0 x))) (R (M v0 z)))

@[equational_result]
theorem Equation2277_implies_Equation211 (G: Type _) [Magma G] (h: Equation2277 G) : Equation211 G := fun x y =>
  have h0 := R x
  T (h x y (M y (M x (M x x)))) (C (C h0 (C (R y) (S (h y x x)))) h0)

@[equational_result]
theorem Equation2290_implies_Equation203 (G: Type _) [Magma G] (h: Equation2290 G) : Equation203 G := fun x =>
  let v0 := M x (M x x)
  T (h x (M x (M v0 (M v0 v0)))) (C (S (h v0 x)) (R x))

@[equational_result]
theorem Equation2389_implies_Equation31 (G: Type _) [Magma G] (h: Equation2389 G) : Equation31 G := fun x y =>
  let v0 := M x (M x (M x x))
  T (h x v0 y) (C (T (C (R v0) (C (R y) (S (h y x x)))) (S (h (M y y) x x))) (R x))

@[equational_result]
theorem Equation2507_implies_Equation2913 (G: Type _) [Magma G] (h: Equation2507 G) : Equation2913 G := fun x y =>
  have h0 := R y
  have h1 := h x y
  T h1 (C (T (h (M y (M (M x y) y)) y) (C (C h0 (C (S h1) h0)) h0)) h0)

@[equational_result]
theorem Equation2677_implies_Equation2079 (G: Type _) [Magma G] (h: Equation2677 G) : Equation2079 G := fun x y z =>
  let v0 := M x y
  T (T (h x y x) (C (C (h v0 z y) (R (M y x))) (R x))) (S (h (M (M v0 z) (M z y)) y x))

@[equational_result]
theorem Equation2685_implies_Equation2076 (G: Type _) [Magma G] (h: Equation2685 G) : Equation2076 G := fun x y z =>
  let v0 := M x y
  T (T (h x y x) (C (C (h v0 z y) (R v0)) (R x))) (S (h (M (M v0 z) (M y z)) y x))

@[equational_result]
theorem Equation2688_implies_Equation2068 (G: Type _) [Magma G] (h: Equation2688 G) : Equation2068 G := fun x y z =>
  let v0 := M x y
  T (T (h x y x) (C (C (h v0 y z) (R (M x x))) (R y))) (S (h (M (M v0 y) (M z z)) y x))

@[equational_result]
theorem Equation2776_implies_Equation1764 (G: Type _) [Magma G] (h: Equation2776 G) : Equation1764 G := fun x y z =>
  let v0 := M x z
  T (T (h x z x) (C (C (R (M z x)) (h v0 y z)) (R x))) (S (h (M (M y z) (M v0 y)) z x))

@[equational_result]
theorem Equation2779_implies_Equation1761 (G: Type _) [Magma G] (h: Equation2779 G) : Equation1761 G := fun x y z =>
  let v0 := M x y
  T (T (h x x y) (C (C (R v0) (h v0 y z)) (R x))) (S (h (M (M y z) (M v0 z)) x y))

@[equational_result]
theorem Equation2913_implies_Equation3116 (G: Type _) [Magma G] (h: Equation2913 G) : Equation3116 G := fun x y =>
  have h0 := R y
  have h1 := h x y
  T h1 (C (T (h (M (M y (M x y)) y) y) (C (C (C h0 (S h1)) h0) h0)) h0)

@[equational_result]
theorem Equation3419_implies_Equation41 (G: Type _) [Magma G] (h: Equation3419 G) : Equation41 G := fun x y z =>
  have h0 := R y
  T (T (h x x y) (C h0 (C h0 (T (h x y x) (S (h z y x)))))) (S (h y z y))

@[equational_result]
theorem Equation3553_implies_Equation3370 (G: Type _) [Magma G] (h: Equation3553 G) : Equation3370 G := fun x y z =>
  let v0 := M z x
  let v1 := M v0 x
  T (h x y v1) (C (R y) (T (C (S (h z x x)) (R v1)) (S (h z v0 x))))

@[equational_result]
theorem Equation3766_implies_Equation41 (G: Type _) [Magma G] (h: Equation3766 G) : Equation41 G := fun x y z =>
  let v0 := M x x
  have h1 := h x x x
  T (T (T h1 (C h1 (R v0))) (S (h (M z z) v0 x))) (S (h y z x))

@[equational_result]
theorem Equation3821_implies_Equation41 (G: Type _) [Magma G] (h: Equation3821 G) : Equation41 G := fun x y z =>
  let v0 := M x x
  T (T (T (h x x v0) (C (R (M v0 v0)) (h x v0 x))) (S (h v0 (M y x) v0))) (S (h y z x))

@[equational_result]
theorem Equation4129_implies_Equation4136 (G: Type _) [Magma G] (h: Equation4129 G) : Equation4136 G := fun x y z w =>
  let v0 := M x y
  T (h x y w) (C (T (h v0 x z) (C (S (h x y v0)) (R z))) (R w))

@[equational_result]
theorem Equation4162_implies_Equation3588 (G: Type _) [Magma G] (h: Equation4162 G) : Equation3588 G := fun x y z =>
  let v0 := M x y
  have h1 := R v0
  T (T (h x y v0) (C (C (h y x z) h1) h1)) (S (h z (M v0 z) v0))

@[equational_result]
theorem Equation4322_implies_Equation4365 (G: Type _) [Magma G] (h: Equation4322 G) : Equation4365 G := fun x y z w =>
  T (T (T (T (T (S (h y x z)) (h y x x)) (h x y (M z x))) (C (R y) (h x z y))) (S (h z y (M x y)))) (h z y w)

@[equational_result]
theorem Equation4344_implies_Equation4365 (G: Type _) [Magma G] (h: Equation4344 G) : Equation4365 G := fun x y z w =>
  T (T (T (T (T (S (h y x z)) (h y x y)) (h x y (M z z))) (C (R y) (h x z y))) (S (h z y (M x y)))) (h z y w)

@[equational_result]
theorem Equation4589_implies_Equation4680 (G: Type _) [Magma G] (h: Equation4589 G) : Equation4680 G := fun x y z w =>
  T (T (T (T (S (h y x z)) (h y (M y y) w)) (C (h y z z) (R w))) (S (h z (M z y) w))) (h z y w)

@[equational_result]
theorem Equation910_implies_Equation1925 (G: Type _) [Magma G] (h: Equation910 G) : Equation1925 G := fun x y =>
  let v0 := M y y
  let v1 := M y x
  T (T (h x y) (C (R y) (C (h v1 y) (R v0)))) (S (h (M (M y v1) v0) y))

@[equational_result]
theorem Equation1031_implies_Equation101 (G: Type _) [Magma G] (h: Equation1031 G) : Equation101 G := fun x y =>
  have h0 := R x
  T (h x y (M (M y (M x x)) y)) (C h0 (C (C h0 (S (h y x x))) h0))

@[equational_result]
theorem Equation1053_implies_Equation11 (G: Type _) [Magma G] (h: Equation1053 G) : Equation11 G := fun x y =>
  let v0 := M (M x (M x x)) x
  T (h x y v0) (C (R x) (T (C (C (R y) (S (h y x x))) (R v0)) (S (h (M y y) x x))))

@[equational_result]
theorem Equation1674_implies_Equation27 (G: Type _) [Magma G] (h: Equation1674 G) : Equation27 G := fun x y z =>
  let v0 := M (M x x) x
  let v1 := M x y
  T (T (h x y x) (C (h v1 z x) (R v0))) (S (h (M v1 z) v0 x))

@[equational_result]
theorem Equation1937_implies_Equation19 (G: Type _) [Magma G] (h: Equation1937 G) : Equation19 G := fun x y z =>
  let v0 := M x (M x x)
  let v1 := M z x
  T (T (h x x z) (C (R v0) (h v1 x y))) (S (h (M y v1) x v0))

@[equational_result]
theorem Equation2368_implies_Equation221 (G: Type _) [Magma G] (h: Equation2368 G) : Equation221 G := fun x y =>
  let v0 := M x y
  T (h x y (M x (M x (M v0 x)))) (C (C (R y) (S (h v0 x x))) (R x))

@[equational_result]
theorem Equation2741_implies_Equation1726 (G: Type _) [Magma G] (h: Equation2741 G) : Equation1726 G := fun x y z =>
  let v0 := M x z
  T (T (h x x z) (C (C (R (M x x)) (h v0 y z)) (R z))) (S (h (M (M y y) (M v0 z)) x z))

@[equational_result]
theorem Equation2755_implies_Equation2146 (G: Type _) [Magma G] (h: Equation2755 G) : Equation2146 G := fun x y z =>
  let v0 := M x z
  T (h x y v0) (C (C (R (M y y)) (T (C (h v0 v0 v0) (R x)) (S (h z (M v0 v0) x)))) (R v0))

@[equational_result]
theorem Equation3128_implies_Equation1355 (G: Type _) [Magma G] (h: Equation3128 G) : Equation1355 G := fun x y z =>
  let v0 := M (M (M z x) y) z
  let v1 := M y v0
  T (T (h x z y) (C (h v0 y v1) (R y))) (S (h v1 v1 y))

@[equational_result]
theorem Equation3417_implies_Equation3994 (G: Type _) [Magma G] (h: Equation3417 G) : Equation3994 G := fun x y z =>
  let v0 := M x y
  have h1 := R v0
  T (T (h x y v0) (C h1 (C h1 (h y x z)))) (S (h (M z v0) z v0))

@[equational_result]
theorem Equation895_implies_Equation11 (G: Type _) [Magma G] (h: Equation895 G) : Equation11 G := fun x y =>
  have h0 := S (h y x x)
  T (h x x (M (M y x) (M x x))) (C (R x) (C h0 h0))

@[equational_result]
theorem Equation928_implies_Equation11 (G: Type _) [Magma G] (h: Equation928 G) : Equation11 G := fun x y =>
  have h0 := S (h y x x)
  T (h x x (M (M x x) (M y x))) (C (R x) (C h0 h0))

@[equational_result]
theorem Equation1245_implies_Equation105 (G: Type _) [Magma G] (h: Equation1245 G) : Equation105 G := fun x y =>
  let v0 := M y x
  T (h x y (M (M (M x v0) x) x)) (C (R x) (C (S (h v0 x x)) (R y)))

@[equational_result]
theorem Equation1262_implies_Equation107 (G: Type _) [Magma G] (h: Equation1262 G) : Equation107 G := fun x y =>
  have h0 := R x
  T (h x y (M (M (M x x) x) y)) (C h0 (C (C (S (h y x x)) (R y)) h0))

@[equational_result]
theorem Equation2113_implies_Equation968 (G: Type _) [Magma G] (h: Equation2113 G) : Equation968 G := fun x y z =>
  let v0 := M z x
  let v1 := M z y
  T (h x v1 v0) (C (S (h y z x)) (R (M v1 v0)))

@[equational_result]
theorem Equation2318_implies_Equation211 (G: Type _) [Magma G] (h: Equation2318 G) : Equation211 G := fun x y =>
  let v0 := M x (M y y)
  T (h x (M x (M v0 (M x x))) y) (C (S (h v0 x x)) (R x))

@[equational_result]
theorem Equation2331_implies_Equation707 (G: Type _) [Magma G] (h: Equation2331 G) : Equation707 G := fun x y =>
  let v0 := M x y
  have h1 := R y
  T (T (h x y) (C (C h1 (C h1 (h v0 y))) h1)) (S (h (M y (M y (M v0 y))) y))

@[equational_result]
theorem Equation2402_implies_Equation31 (G: Type _) [Magma G] (h: Equation2402 G) : Equation31 G := fun x y =>
  have h0 := S (h y x x)
  let v1 := M x (M x (M x x))
  T (h x y v1) (C (C (R y) (T (C (R v1) h0) h0)) (R x))

@[equational_result]
theorem Equation2558_implies_Equation31 (G: Type _) [Magma G] (h: Equation2558 G) : Equation31 G := fun x y =>
  let v0 := M x (M (M x x) x)
  T (h x v0 y) (C (T (C (R v0) (C (S (h y x x)) (R y))) (S (h (M y y) x x))) (R x))

@[equational_result]
theorem Equation2673_implies_Equation2064 (G: Type _) [Magma G] (h: Equation2673 G) : Equation2064 G := fun x y =>
  let v0 := M y y
  let v1 := M x y
  T (T (h x y) (C (C (h v1 y) (R v0)) (R y))) (S (h (M (M v1 y) v0) y))

@[equational_result]
theorem Equation2737_implies_Equation1722 (G: Type _) [Magma G] (h: Equation2737 G) : Equation1722 G := fun x y =>
  let v0 := M x y
  let v1 := M y y
  T (T (h x y) (C (C (R v1) (h v0 y)) (R y))) (S (h (M v1 (M v0 y)) y))

@[equational_result]
theorem Equation3124_implies_Equation2 (G: Type _) [Magma G] (h: Equation3124 G) : Equation2 G := fun x y =>
  let v0 := M x y
  have h1 := R y
  T (T (T (h x v0 y) (C (S (h y x x)) h1)) (C (h y x y) h1)) (S (h y v0 y))

@[equational_result]
theorem Equation3380_implies_Equation3431 (G: Type _) [Magma G] (h: Equation3380 G) : Equation3431 G := fun x y z w =>
  have h0 := h x y w
  T (T h0 (h w (M x (M x y)) z)) (C (R z) (C (R w) (S h0)))

@[equational_result]
theorem Equation3398_implies_Equation4307 (G: Type _) [Magma G] (h: Equation3398 G) : Equation4307 G := fun x y z =>
  let v0 := M x y
  T (h x v0 z) (C (R z) (T (C (R v0) (h x z y)) (S (h z y v0))))

@[equational_result]
theorem Equation3711_implies_Equation383 (G: Type _) [Magma G] (h: Equation3711 G) : Equation383 G := fun x y z w =>
  let v0 := M x z
  have h1 := T (h x x) (S (h x z))
  T (T (T (h x y) (C h1 h1)) (h v0 v0)) (S (h v0 w))

@[equational_result]
theorem Equation3751_implies_Equation3724 (G: Type _) [Magma G] (h: Equation3751 G) : Equation3724 G := fun x y =>
  let v0 := M y x
  have h1 := h x y
  T h1 (C (T (T (T (h y x) (C h1 h1)) (S (h v0 v0))) (S h1)) (R v0))

@[equational_result]
theorem Equation3751_implies_Equation3749 (G: Type _) [Magma G] (h: Equation3751 G) : Equation3749 G := fun x y =>
  have h0 := h x y
  let v1 := M y x
  T h0 (C (R v1) (T (T (T (h y x) (C h0 h0)) (S (h v1 v1))) (S h0)))

@[equational_result]
theorem Equation3819_implies_Equation41 (G: Type _) [Magma G] (h: Equation3819 G) : Equation41 G := fun x y z =>
  let v0 := M x x
  have h1 := h x x x
  T (T (T h1 (C (R v0) h1)) (S (h v0 (M y y) x))) (S (h y z x))

@[equational_result]
theorem Equation3932_implies_Equation3729 (G: Type _) [Magma G] (h: Equation3932 G) : Equation3729 G := fun x y z =>
  let v0 := M z z
  T (h x y v0) (C (T (T (h x (M y v0) z) (C (C (R x) (S (h y z z))) (R z))) (S (h x y z))) (R v0))

@[equational_result]
theorem Equation4229_implies_Equation3537 (G: Type _) [Magma G] (h: Equation4229 G) : Equation3537 G := fun x y z =>
  let v0 := M z z
  let v1 := M v0 y
  T (T (h x y z) (C (T (h v0 y z) (h v1 v0 z)) (R x))) (S (h x v1 v0))

@[equational_result]
theorem Equation542_implies_Equation2 (G: Type _) [Magma G] (h: Equation542 G) : Equation2 G := fun x y =>
  let v0 := M y y
  have h1 := R v0
  T (T (T (h x v0 y) (C h1 (S (h v0 y x)))) (C h1 (h v0 y y))) (S (h y v0 y))

@[equational_result]
theorem Equation556_implies_Equation2370 (G: Type _) [Magma G] (h: Equation556 G) : Equation2370 G := fun x y z =>
  let v0 := M y (M z (M x y))
  let v1 := M v0 z
  T (T (h x z y) (C (R z) (h v0 v1 z))) (S (h v1 z v1))

@[equational_result]
theorem Equation1256_implies_Equation11 (G: Type _) [Magma G] (h: Equation1256 G) : Equation11 G := fun x y =>
  have h0 := S (h (M y y) x x)
  let v1 := M (M (M x x) x) x
  T (h x y v1) (C (R x) (T (C h0 (R v1)) h0))

@[equational_result]
theorem Equation1264_implies_Equation11 (G: Type _) [Magma G] (h: Equation1264 G) : Equation11 G := fun x y =>
  let v0 := M (M (M x x) x) x
  T (h x y v0) (C (R x) (T (C (C (S (h y x x)) (R y)) (R v0)) (S (h (M y y) x x))))

@[equational_result]
theorem Equation1316_implies_Equation2940 (G: Type _) [Magma G] (h: Equation1316 G) : Equation2940 G := fun x y =>
  let v0 := M y x
  have h1 := R y
  T (T (h x y) (C h1 (C (C (h v0 y) h1) h1))) (S (h (M (M (M y v0) y) y) y))

@[equational_result]
theorem Equation2310_implies_Equation208 (G: Type _) [Magma G] (h: Equation2310 G) : Equation208 G := fun x y =>
  let v0 := M x (M y x)
  T (h x (M x (M v0 (M x v0))) y) (C (S (h v0 x x)) (R x))

@[equational_result]
theorem Equation2314_implies_Equation221 (G: Type _) [Magma G] (h: Equation2314 G) : Equation221 G := fun x y =>
  have h0 := R x
  T (h x y (M y (M y (M x y)))) (C (C (R y) (C h0 (S (h y y x)))) h0)

@[equational_result]
theorem Equation2795_implies_Equation31 (G: Type _) [Magma G] (h: Equation2795 G) : Equation31 G := fun x y =>
  let v0 := M y y
  have h1 := S (h y v0 y)
  let v2 := M v0 y
  T (h x (M v2 v2) y) (C (C h1 h1) (R x))

@[equational_result]
theorem Equation2882_implies_Equation260 (G: Type _) [Magma G] (h: Equation2882 G) : Equation260 G := fun x y =>
  have h0 := R x
  T (h x (M (M y (M x x)) y) y) (C (C (C h0 (S (h y x x))) h0) h0)

@[equational_result]
theorem Equation2913_implies_Equation2507 (G: Type _) [Magma G] (h: Equation2913 G) : Equation2507 G := fun x y =>
  let v0 := M x y
  have h1 := R y
  T (T (h x y) (C (C (C h1 (h v0 y)) h1) h1)) (S (h (M (M y (M v0 y)) y) y))

@[equational_result]
theorem Equation3312_implies_Equation3338 (G: Type _) [Magma G] (h: Equation3312 G) : Equation3338 G := fun x y z w =>
  let v0 := M w y
  T (T (h x y w) (C (R x) (h x v0 z))) (S (h x (M z v0) x))

@[equational_result]
theorem Equation3397_implies_Equation4374 (G: Type _) [Magma G] (h: Equation3397 G) : Equation4374 G := fun x y z w =>
  let v0 := M y z
  have h1 := h y z v0
  T (T (T (C (R x) h1) (S (h z v0 x))) (h z v0 w)) (C (R w) (S h1))

@[equational_result]
theorem Equation3406_implies_Equation41 (G: Type _) [Magma G] (h: Equation3406 G) : Equation41 G := fun x y z =>
  let v0 := M y y
  T (T (h x x y) (C (R y) (T (h x v0 x) (S (h z v0 x))))) (S (h y z y))

@[equational_result]
theorem Equation4331_implies_Equation4337 (G: Type _) [Magma G] (h: Equation4331 G) : Equation4337 G := fun x y z w =>
  let v0 := M w w
  T (T (T (h x y x) (S (h v0 y x))) (C (R v0) (S (h w w y)))) (h v0 w z)

@[equational_result]
theorem Equation4616_implies_Equation4626 (G: Type _) [Magma G] (h: Equation4616 G) : Equation4626 G := fun x y z w =>
  let v0 := M x x
  T (T (T (h x y v0) (C (S (h x w x)) (R v0))) (S (h w x v0))) (h w x z)

@[equational_result]
theorem Equation714_implies_Equation1120 (G: Type _) [Magma G] (h: Equation714 G) : Equation1120 G := fun x y =>
  let v0 := M y x
  have h1 := R y
  T (T (h x y) (C h1 (C h1 (C (h v0 y) h1)))) (S (h (M y (M (M y v0) y)) y))

@[equational_result]
theorem Equation765_implies_Equation968 (G: Type _) [Magma G] (h: Equation765 G) : Equation968 G := fun x y z =>
  let v0 := M z y
  have h1 := h x y v0
  T h1 (C (R y) (C (R v0) (T (h (M (M y v0) x) z y) (C (R z) (S h1)))))

@[equational_result]
theorem Equation823_implies_Equation8 (G: Type _) [Magma G] (h: Equation823 G) : Equation8 G := fun x =>
  have h0 := S (h x x)
  let v1 := M x x
  T (h x (M v1 v1)) (C (R x) (C h0 h0))

@[equational_result]
theorem Equation858_implies_Equation11 (G: Type _) [Magma G] (h: Equation858 G) : Equation11 G := fun x y =>
  let v0 := M y y
  have h1 := S (h y v0 y)
  let v2 := M v0 y
  T (h x y (M v2 v2)) (C (R x) (C h1 h1))

@[equational_result]
theorem Equation1259_implies_Equation105 (G: Type _) [Magma G] (h: Equation1259 G) : Equation105 G := fun x y =>
  have h0 := R x
  T (h x y (M (M (M y x) y) y)) (C h0 (C (C (S (h y y x)) h0) (R y)))

@[equational_result]
theorem Equation1267_implies_Equation11 (G: Type _) [Magma G] (h: Equation1267 G) : Equation11 G := fun x y =>
  have h0 := S (h y x x)
  let v1 := M (M (M x x) x) x
  T (h x y v1) (C (R x) (C (T (C h0 (R v1)) h0) (R y)))

@[equational_result]
theorem Equation1459_implies_Equation2282 (G: Type _) [Magma G] (h: Equation1459 G) : Equation2282 G := fun x y z =>
  let v0 := M z z
  let v1 := M y v0
  T (h x v1 v0) (C (R (M x v1)) (S (h y v0 z)))

@[equational_result]
theorem Equation1740_implies_Equation2576 (G: Type _) [Magma G] (h: Equation1740 G) : Equation2576 G := fun x y z =>
  let v0 := M (M z x) z
  let v1 := M (M y v0) y
  T (T (h x x z) (C (R (M x x)) (h v0 v1 y))) (S (h v1 x v1))

@[equational_result]
theorem Equation2239_implies_Equation27 (G: Type _) [Magma G] (h: Equation2239 G) : Equation27 G := fun x y z =>
  let v0 := M x (M x (M x x))
  T (h x z) (C (T (h v0 y) (C (S (h x (M v0 (M v0 v0)))) (R y))) (R z))

@[equational_result]
theorem Equation2507_implies_Equation1289 (G: Type _) [Magma G] (h: Equation2507 G) : Equation1289 G := fun x y =>
  let v0 := M x y
  have h1 := R y
  T (T (h x y) (C (C h1 (C (h v0 y) h1)) h1)) (S (h (M y (M (M v0 y) y)) y))

