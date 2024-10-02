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
theorem Equation4268_implies_Equation4282 (G: Type _) [Magma G] (h: Equation4268 G) : Equation4282 G := fun x y z =>
  T (S (h x y)) (h x z)

@[equational_result]
theorem Equation4269_implies_Equation4316 (G: Type _) [Magma G] (h: Equation4269 G) : Equation4316 G := fun x y z =>
  T (S (h x y)) (h x z)

@[equational_result]
theorem Equation4270_implies_Equation4341 (G: Type _) [Magma G] (h: Equation4270 G) : Equation4341 G := fun x y z =>
  T (S (h x y)) (h x z)

@[equational_result]
theorem Equation4272_implies_Equation4351 (G: Type _) [Magma G] (h: Equation4272 G) : Equation4351 G := fun x y z =>
  T (S (h y x)) (h y z)

@[equational_result]
theorem Equation4273_implies_Equation4332 (G: Type _) [Magma G] (h: Equation4273 G) : Equation4332 G := fun x y z =>
  T (S (h y x)) (h y z)

@[equational_result]
theorem Equation4275_implies_Equation4307 (G: Type _) [Magma G] (h: Equation4275 G) : Equation4307 G := fun x y z =>
  T (S (h y x)) (h y z)

@[equational_result]
theorem Equation4389_implies_Equation4591 (G: Type _) [Magma G] (h: Equation4389 G) : Equation4591 G := fun x y =>
  T (S (h x x)) (h x y)

@[equational_result]
theorem Equation4583_implies_Equation4597 (G: Type _) [Magma G] (h: Equation4583 G) : Equation4597 G := fun x y z =>
  T (S (h x y)) (h x z)

@[equational_result]
theorem Equation4584_implies_Equation4631 (G: Type _) [Magma G] (h: Equation4584 G) : Equation4631 G := fun x y z =>
  T (S (h x y)) (h x z)

@[equational_result]
theorem Equation4585_implies_Equation4656 (G: Type _) [Magma G] (h: Equation4585 G) : Equation4656 G := fun x y z =>
  T (S (h x y)) (h x z)

@[equational_result]
theorem Equation4587_implies_Equation4666 (G: Type _) [Magma G] (h: Equation4587 G) : Equation4666 G := fun x y z =>
  T (S (h y x)) (h y z)

@[equational_result]
theorem Equation4588_implies_Equation4647 (G: Type _) [Magma G] (h: Equation4588 G) : Equation4647 G := fun x y z =>
  T (S (h y x)) (h y z)

@[equational_result]
theorem Equation4590_implies_Equation4622 (G: Type _) [Magma G] (h: Equation4590 G) : Equation4622 G := fun x y z =>
  T (S (h y x)) (h y z)

@[equational_result]
theorem Equation4271_implies_Equation4359 (G: Type _) [Magma G] (h: Equation4271 G) : Equation4359 G := fun x y z w =>
  T (S (h x y z)) (h x z w)

@[equational_result]
theorem Equation4278_implies_Equation4367 (G: Type _) [Magma G] (h: Equation4278 G) : Equation4367 G := fun x y z w =>
  T (S (h z x y)) (h z y w)

@[equational_result]
theorem Equation4279_implies_Equation4324 (G: Type _) [Magma G] (h: Equation4279 G) : Equation4324 G := fun x y z =>
  T (S (h x x y)) (h x y z)

@[equational_result]
theorem Equation4280_implies_Equation4346 (G: Type _) [Magma G] (h: Equation4280 G) : Equation4346 G := fun x y z =>
  T (S (h x x y)) (h x y z)

@[equational_result]
theorem Equation4287_implies_Equation4360 (G: Type _) [Magma G] (h: Equation4287 G) : Equation4360 G := fun x y z w =>
  T (S (h x z y)) (h x z w)

@[equational_result]
theorem Equation4300_implies_Equation4374 (G: Type _) [Magma G] (h: Equation4300 G) : Equation4374 G := fun x y z w =>
  T (S (h y z x)) (h y z w)

@[equational_result]
theorem Equation4315_implies_Equation4357 (G: Type _) [Magma G] (h: Equation4315 G) : Equation4357 G := fun x y z w =>
  T (S (h x y z)) (h x y w)

@[equational_result]
theorem Equation4330_implies_Equation4374 (G: Type _) [Magma G] (h: Equation4330 G) : Equation4374 G := fun x y z w =>
  T (S (h z y x)) (h z y w)

@[equational_result]
theorem Equation4339_implies_Equation4357 (G: Type _) [Magma G] (h: Equation4339 G) : Equation4357 G := fun x y z w =>
  T (S (h x y z)) (h x y w)

@[equational_result]
theorem Equation4340_implies_Equation4360 (G: Type _) [Magma G] (h: Equation4340 G) : Equation4360 G := fun x y z w =>
  T (S (h x z y)) (h x z w)

@[equational_result]
theorem Equation4586_implies_Equation4674 (G: Type _) [Magma G] (h: Equation4586 G) : Equation4674 G := fun x y z w =>
  T (S (h x y z)) (h x z w)

@[equational_result]
theorem Equation4592_implies_Equation4609 (G: Type _) [Magma G] (h: Equation4592 G) : Equation4609 G := fun x y z =>
  T (S (h x x y)) (h x y z)

@[equational_result]
theorem Equation4593_implies_Equation4682 (G: Type _) [Magma G] (h: Equation4593 G) : Equation4682 G := fun x y z w =>
  T (S (h z x y)) (h z y w)

@[equational_result]
theorem Equation4594_implies_Equation4639 (G: Type _) [Magma G] (h: Equation4594 G) : Equation4639 G := fun x y z =>
  T (S (h x x y)) (h x y z)

@[equational_result]
theorem Equation4602_implies_Equation4675 (G: Type _) [Magma G] (h: Equation4602 G) : Equation4675 G := fun x y z w =>
  T (S (h x z y)) (h x z w)

@[equational_result]
theorem Equation4615_implies_Equation4689 (G: Type _) [Magma G] (h: Equation4615 G) : Equation4689 G := fun x y z w =>
  T (S (h y z x)) (h y z w)

@[equational_result]
theorem Equation4630_implies_Equation4672 (G: Type _) [Magma G] (h: Equation4630 G) : Equation4672 G := fun x y z w =>
  T (S (h x y z)) (h x y w)

@[equational_result]
theorem Equation4645_implies_Equation4689 (G: Type _) [Magma G] (h: Equation4645 G) : Equation4689 G := fun x y z w =>
  T (S (h z y x)) (h z y w)

@[equational_result]
theorem Equation4654_implies_Equation4672 (G: Type _) [Magma G] (h: Equation4654 G) : Equation4672 G := fun x y z w =>
  T (S (h x y z)) (h x y w)

@[equational_result]
theorem Equation4655_implies_Equation4675 (G: Type _) [Magma G] (h: Equation4655 G) : Equation4675 G := fun x y z w =>
  T (S (h x z y)) (h x z w)

@[equational_result]
theorem Equation3102_implies_Equation3 (G: Type _) [Magma G] (h: Equation3102 G) : Equation3 G := fun x =>
  T (h x (M x x)) (C (S (h x x)) (R x))

@[equational_result]
theorem Equation3184_implies_Equation5 (G: Type _) [Magma G] (h: Equation3184 G) : Equation5 G := fun x y =>
  T (h x (M y x) y) (C (S (h y y x)) (R x))

@[equational_result]
theorem Equation3320_implies_Equation326 (G: Type _) [Magma G] (h: Equation3320 G) : Equation326 G := fun x y =>
  T (h x y (M y x)) (C (R x) (S (h y y x)))

@[equational_result]
theorem Equation4176_implies_Equation4458 (G: Type _) [Magma G] (h: Equation4176 G) : Equation4458 G := fun x y z =>
  T (h x (M y x) z) (C (S (h z y x)) (R z))

@[equational_result]
theorem Equation1033_implies_Equation9 (G: Type _) [Magma G] (h: Equation1033 G) : Equation9 G := fun x y =>
  T (h x (M x (M x y)) y) (C (R x) (C (S (h x x y)) (R y)))

@[equational_result]
theorem Equation1463_implies_Equation27 (G: Type _) [Magma G] (h: Equation1463 G) : Equation27 G := fun x y z =>
  T (h x y (M z x)) (C (R (M x y)) (S (h z x x)))

@[equational_result]
theorem Equation3142_implies_Equation23 (G: Type _) [Magma G] (h: Equation3142 G) : Equation23 G := fun x =>
  let v0 := M x x
  T (h x v0) (C (S (h v0 x)) (R x))

@[equational_result]
theorem Equation3269_implies_Equation3659 (G: Type _) [Magma G] (h: Equation3269 G) : Equation3659 G := fun x =>
  let v0 := M x x
  T (h x v0) (C (R v0) (S (h x x)))

@[equational_result]
theorem Equation4081_implies_Equation3659 (G: Type _) [Magma G] (h: Equation4081 G) : Equation3659 G := fun x =>
  let v0 := M x x
  T (h x v0) (C (S (h x x)) (R v0))

@[equational_result]
theorem Equation3139_implies_Equation3659 (G: Type _) [Magma G] (h: Equation3139 G) : Equation3659 G := fun x =>
  let v0 := M x x
  T (h v0 v0) (C (S (h v0 x)) (R v0))

@[equational_result]
theorem Equation778_implies_Equation4200 (G: Type _) [Magma G] (h: Equation778 G) : Equation4200 G := fun x y z =>
  let v0 := M z x
  T (C (R x) (h y z v0)) (S (h (M (M v0 z) y) x z))

@[equational_result]
theorem Equation1710_implies_Equation3161 (G: Type _) [Magma G] (h: Equation1710 G) : Equation3161 G := fun x y z =>
  let v0 := M (M y y) z
  T (h x v0 z) (C (R (M v0 x)) (S (h z z y)))

@[equational_result]
theorem Equation1964_implies_Equation1152 (G: Type _) [Magma G] (h: Equation1964 G) : Equation1152 G := fun x y z =>
  let v0 := M z (M x y)
  T (h x v0 z) (C (S (h y z x)) (R (M v0 z)))

@[equational_result]
theorem Equation1993_implies_Equation481 (G: Type _) [Magma G] (h: Equation1993 G) : Equation481 G := fun x y z =>
  let v0 := M y (M z z)
  T (h x v0 y) (C (S (h y y z)) (R (M x v0)))

@[equational_result]
theorem Equation1996_implies_Equation1137 (G: Type _) [Magma G] (h: Equation1996 G) : Equation1137 G := fun x y z =>
  let v0 := M y (M z z)
  T (h x v0 y) (C (S (h y y z)) (R (M v0 x)))

@[equational_result]
theorem Equation2076_implies_Equation3331 (G: Type _) [Magma G] (h: Equation2076 G) : Equation3331 G := fun x y z =>
  let v0 := M y z
  T (h (M x y) z v0) (C (S (h x y z)) (R (M z v0)))

@[equational_result]
theorem Equation2079_implies_Equation3534 (G: Type _) [Magma G] (h: Equation2079 G) : Equation3534 G := fun x y z =>
  let v0 := M z y
  T (h (M x y) z v0) (C (S (h x y z)) (R (M v0 z)))

@[equational_result]
theorem Equation3715_implies_Equation4470 (G: Type _) [Magma G] (h: Equation3715 G) : Equation4470 G := fun x y =>
  T (T (h x (M y y)) (C (h x x) (S (h y y)))) (S (h (M x x) y))

@[equational_result]
theorem Equation3758_implies_Equation4470 (G: Type _) [Magma G] (h: Equation3758 G) : Equation4470 G := fun x y =>
  T (T (h x (M y y)) (C (S (h y y)) (h x x))) (S (h (M x x) y))

@[equational_result]
theorem Equation489_implies_Equation14 (G: Type _) [Magma G] (h: Equation489 G) : Equation14 G := fun x y =>
  let v0 := M x y
  T (h x y v0) (C (R y) (S (h v0 x y)))

@[equational_result]
theorem Equation508_implies_Equation11 (G: Type _) [Magma G] (h: Equation508 G) : Equation11 G := fun x y =>
  let v0 := M y y
  T (h x x v0) (C (R x) (S (h v0 x y)))

@[equational_result]
theorem Equation692_implies_Equation1358 (G: Type _) [Magma G] (h: Equation692 G) : Equation1358 G := fun x y z =>
  let v0 := M (M z x) z
  T (h x y v0) (C (R y) (S (h (M v0 y) x z)))

@[equational_result]
theorem Equation695_implies_Equation2132 (G: Type _) [Magma G] (h: Equation695 G) : Equation2132 G := fun x y z =>
  let v0 := M (M y y) x
  T (h x v0 z) (C (R v0) (S (h (M z z) x y)))

@[equational_result]
theorem Equation850_implies_Equation11 (G: Type _) [Magma G] (h: Equation850 G) : Equation11 G := fun x y =>
  let v0 := M y y
  T (h x y v0) (C (R x) (S (h v0 y y)))

@[equational_result]
theorem Equation1523_implies_Equation3692 (G: Type _) [Magma G] (h: Equation1523 G) : Equation3692 G := fun x y z =>
  let v0 := M z z
  T (h (M x x) y v0) (C (R (M y y)) (S (h v0 x z)))

@[equational_result]
theorem Equation1724_implies_Equation4611 (G: Type _) [Magma G] (h: Equation1724 G) : Equation4611 G := fun x y z =>
  let v0 := M (M y z) y
  T (C (R (M x x)) (h y v0 z)) (S (h v0 x v0))

@[equational_result]
theorem Equation1726_implies_Equation4612 (G: Type _) [Magma G] (h: Equation1726 G) : Equation4612 G := fun x y z =>
  let v0 := M (M y z) z
  T (C (R (M x x)) (h y v0 z)) (S (h v0 x v0))

@[equational_result]
theorem Equation1740_implies_Equation4620 (G: Type _) [Magma G] (h: Equation1740 G) : Equation4620 G := fun x y z =>
  let v0 := M (M z y) z
  T (C (R (M x x)) (h y v0 z)) (S (h v0 x v0))

@[equational_result]
theorem Equation1855_implies_Equation4318 (G: Type _) [Magma G] (h: Equation1855 G) : Equation4318 G := fun x y z =>
  let v0 := M x (M y x)
  T (h v0 v0 z) (C (S (h x y v0)) (R (M z z)))

@[equational_result]
theorem Equation1902_implies_Equation4325 (G: Type _) [Magma G] (h: Equation1902 G) : Equation4325 G := fun x y z =>
  let v0 := M x (M y x)
  T (h v0 v0 z) (C (S (h y x v0)) (R (M z z)))

@[equational_result]
theorem Equation1929_implies_Equation4297 (G: Type _) [Magma G] (h: Equation1929 G) : Equation4297 G := fun x y z =>
  let v0 := M x (M x y)
  T (h v0 v0 z) (C (S (h y x v0)) (R (M z z)))

@[equational_result]
theorem Equation2074_implies_Equation3326 (G: Type _) [Magma G] (h: Equation2074 G) : Equation3326 G := fun x y z =>
  let v0 := M x y
  T (h v0 z (M y x)) (C (S (h x y z)) (R (M z v0)))

@[equational_result]
theorem Equation2170_implies_Equation3417 (G: Type _) [Magma G] (h: Equation2170 G) : Equation3417 G := fun x y z =>
  let v0 := M y x
  T (h (M x y) v0 z) (C (S (h z y x)) (R (M z v0)))

@[equational_result]
theorem Equation2761_implies_Equation31 (G: Type _) [Magma G] (h: Equation2761 G) : Equation31 G := fun x y =>
  let v0 := M y y
  T (h x v0 y) (C (S (h v0 y y)) (R x))

@[equational_result]
theorem Equation2992_implies_Equation2373 (G: Type _) [Magma G] (h: Equation2992 G) : Equation2373 G := fun x y z =>
  let v0 := M z (M x z)
  T (h x v0 y) (C (S (h (M y v0) z x)) (R y))

@[equational_result]
theorem Equation3008_implies_Equation1523 (G: Type _) [Magma G] (h: Equation3008 G) : Equation1523 G := fun x y z =>
  let v0 := M x (M z z)
  T (h x v0 y) (C (S (h (M y y) x z)) (R v0))

@[equational_result]
theorem Equation3147_implies_Equation31 (G: Type _) [Magma G] (h: Equation3147 G) : Equation31 G := fun x y =>
  let v0 := M y y
  T (h x v0 x) (C (S (h v0 y x)) (R x))

@[equational_result]
theorem Equation3159_implies_Equation3 (G: Type _) [Magma G] (h: Equation3159 G) : Equation3 G := fun x =>
  let v0 := M x x
  T (h x v0 x) (C (S (h x x v0)) (R x))

@[equational_result]
theorem Equation3211_implies_Equation14 (G: Type _) [Magma G] (h: Equation3211 G) : Equation14 G := fun x y =>
  let v0 := M x y
  T (h x v0 y) (C (S (h y x y)) (R v0))

@[equational_result]
theorem Equation3214_implies_Equation31 (G: Type _) [Magma G] (h: Equation3214 G) : Equation31 G := fun x y =>
  let v0 := M y y
  T (h x v0 y) (C (S (h v0 y y)) (R x))

@[equational_result]
theorem Equation3266_implies_Equation310 (G: Type _) [Magma G] (h: Equation3266 G) : Equation310 G := fun x y =>
  let v0 := M y y
  T (h x y v0) (C (R x) (S (h y v0 y)))

@[equational_result]
theorem Equation3331_implies_Equation3534 (G: Type _) [Magma G] (h: Equation3331 G) : Equation3534 G := fun x y z =>
  let v0 := M z y
  T (h x y v0) (C (R x) (S (h v0 z y)))

@[equational_result]
theorem Equation3350_implies_Equation3573 (G: Type _) [Magma G] (h: Equation3350 G) : Equation3573 G := fun x y z =>
  let v0 := M z z
  T (h x y v0) (C (R y) (S (h v0 x z)))

@[equational_result]
theorem Equation3364_implies_Equation3370 (G: Type _) [Magma G] (h: Equation3364 G) : Equation3370 G := fun x y z =>
  let v0 := M z x
  T (h x y v0) (C (R y) (S (h z v0 x)))

@[equational_result]
theorem Equation3385_implies_Equation3791 (G: Type _) [Magma G] (h: Equation3385 G) : Equation3791 G := fun x y z =>
  let v0 := M z x
  T (h x y v0) (C (R v0) (S (h y z x)))

@[equational_result]
theorem Equation3398_implies_Equation3810 (G: Type _) [Magma G] (h: Equation3398 G) : Equation3810 G := fun x y z =>
  let v0 := M z y
  T (h x y v0) (C (R v0) (S (h z x y)))

@[equational_result]
theorem Equation4096_implies_Equation367 (G: Type _) [Magma G] (h: Equation4096 G) : Equation367 G := fun x y =>
  let v0 := M y y
  T (h x v0 y) (C (S (h y y v0)) (R x))

@[equational_result]
theorem Equation4197_implies_Equation3791 (G: Type _) [Magma G] (h: Equation4197 G) : Equation3791 G := fun x y z =>
  let v0 := M y z
  T (h x y v0) (C (S (h z x y)) (R v0))

@[equational_result]
theorem Equation4200_implies_Equation3997 (G: Type _) [Magma G] (h: Equation4200 G) : Equation3997 G := fun x y z =>
  let v0 := M x z
  T (h x y v0) (C (S (h z v0 x)) (R y))

@[equational_result]
theorem Equation4210_implies_Equation3770 (G: Type _) [Magma G] (h: Equation4210 G) : Equation3770 G := fun x y z =>
  let v0 := M x z
  T (h x y v0) (C (S (h y z x)) (R v0))

@[equational_result]
theorem Equation4216_implies_Equation4182 (G: Type _) [Magma G] (h: Equation4216 G) : Equation4182 G := fun x y z =>
  let v0 := M y z
  T (h x y v0) (C (S (h v0 z y)) (R x))

@[equational_result]
theorem Equation4229_implies_Equation3979 (G: Type _) [Magma G] (h: Equation4229 G) : Equation3979 G := fun x y z =>
  let v0 := M z z
  T (h x y v0) (C (S (h y v0 z)) (R x))

@[equational_result]
theorem Equation1060_implies_Equation11 (G: Type _) [Magma G] (h: Equation1060 G) : Equation11 G := fun x y =>
  T (h x y (M y (M x y))) (C (R x) (C (S (h y y x)) (R y)))

@[equational_result]
theorem Equation2550_implies_Equation28 (G: Type _) [Magma G] (h: Equation2550 G) : Equation28 G := fun x y =>
  T (h x y (M (M y x) x)) (C (C (R y) (S (h x y x))) (R x))

@[equational_result]
theorem Equation1452_implies_Equation209 (G: Type _) [Magma G] (h: Equation1452 G) : Equation209 G := fun x y =>
  let v0 := M y x
  T (h x v0) (C (R (M x v0)) (S (h y x)))

@[equational_result]
theorem Equation1481_implies_Equation3955 (G: Type _) [Magma G] (h: Equation1481 G) : Equation3955 G := fun x y =>
  let v0 := M x y
  T (h v0 y) (C (R (M y v0)) (S (h y x)))

@[equational_result]
theorem Equation1630_implies_Equation23 (G: Type _) [Magma G] (h: Equation1630 G) : Equation23 G := fun x =>
  let v0 := M x x
  T (h x (M v0 x)) (C (R v0) (S (h x x)))

@[equational_result]
theorem Equation1884_implies_Equation8 (G: Type _) [Magma G] (h: Equation1884 G) : Equation8 G := fun x =>
  let v0 := M x x
  T (h x (M x v0)) (C (S (h x x)) (R v0))

@[equational_result]
theorem Equation2051_implies_Equation3511 (G: Type _) [Magma G] (h: Equation2051 G) : Equation3511 G := fun x y =>
  let v0 := M x y
  T (h v0 x) (C (S (h x y)) (R (M v0 x)))

@[equational_result]
theorem Equation2100_implies_Equation117 (G: Type _) [Magma G] (h: Equation2100 G) : Equation117 G := fun x y =>
  let v0 := M x y
  T (h x v0) (C (S (h y x)) (R (M v0 x)))

@[equational_result]
theorem Equation3120_implies_Equation14 (G: Type _) [Magma G] (h: Equation3120 G) : Equation14 G := fun x y =>
  let v0 := M x y
  T (h x v0 v0) (C (S (h y x v0)) (R v0))

@[equational_result]
theorem Equation3167_implies_Equation31 (G: Type _) [Magma G] (h: Equation3167 G) : Equation31 G := fun x y =>
  let v0 := M y y
  T (h x v0 v0) (C (S (h v0 y v0)) (R x))

@[equational_result]
theorem Equation3689_implies_Equation3693 (G: Type _) [Magma G] (h: Equation3689 G) : Equation3693 G := fun x y z w =>
  T (h x z w) (C (T (h z x x) (S (h y x x))) (R (M z w)))

@[equational_result]
theorem Equation3691_implies_Equation3693 (G: Type _) [Magma G] (h: Equation3691 G) : Equation3693 G := fun x y z w =>
  T (h x w z) (C (T (h w x x) (S (h y x x))) (R (M z w)))

@[equational_result]
theorem Equation3699_implies_Equation3709 (G: Type _) [Magma G] (h: Equation3699 G) : Equation3709 G := fun x y z w =>
  T (h x y z) (C (R (M y z)) (T (h y x x) (S (h w x x))))

@[equational_result]
theorem Equation3704_implies_Equation3709 (G: Type _) [Magma G] (h: Equation3704 G) : Equation3709 G := fun x y z w =>
  T (h x y z) (C (R (M y z)) (T (h z x x) (S (h w x x))))

@[equational_result]
theorem Equation3715_implies_Equation326 (G: Type _) [Magma G] (h: Equation3715 G) : Equation326 G := fun x y =>
  T (T (h x y) (C (R (M x x)) (h y y))) (S (h x (M y y)))

@[equational_result]
theorem Equation3715_implies_Equation375 (G: Type _) [Magma G] (h: Equation3715 G) : Equation375 G := fun x y =>
  T (T (h x y) (C (h x x) (R (M y y)))) (S (h (M x x) y))

@[equational_result]
theorem Equation3758_implies_Equation326 (G: Type _) [Magma G] (h: Equation3758 G) : Equation326 G := fun x y =>
  T (T (h x y) (C (h y y) (R (M x x)))) (S (h x (M y y)))

@[equational_result]
theorem Equation3758_implies_Equation375 (G: Type _) [Magma G] (h: Equation3758 G) : Equation375 G := fun x y =>
  T (T (h x y) (C (R (M y y)) (h x x))) (S (h (M x x) y))

@[equational_result]
theorem Equation4097_implies_Equation4099 (G: Type _) [Magma G] (h: Equation4097 G) : Equation4099 G := fun x y z w =>
  T (h x w z) (C (C (T (h w x x) (S (h y x x))) (R z)) (R w))

@[equational_result]
theorem Equation1224_implies_Equation99 (G: Type _) [Magma G] (h: Equation1224 G) : Equation99 G := fun x =>
  let v0 := M (M x x) x
  T (h x (M (M (M v0 v0) v0) x)) (C (R x) (S (h v0 x)))

@[equational_result]
theorem Equation3293_implies_Equation3303 (G: Type _) [Magma G] (h: Equation3293 G) : Equation3303 G := fun x y z w =>
  T (h x y z) (C (R y) (C (R z) (T (h y x x) (S (h w x x)))))

@[equational_result]
theorem Equation820_implies_Equation8 (G: Type _) [Magma G] (h: Equation820 G) : Equation8 G := fun x =>
  let v0 := M x x
  T (h x (M v0 v0)) (C (R x) (S (h v0 v0)))

@[equational_result]
theorem Equation2243_implies_Equation203 (G: Type _) [Magma G] (h: Equation2243 G) : Equation203 G := fun x =>
  have h0 := R x
  T (h x (M x (M x (M x x)))) (C (C h0 (C h0 (S (h x x)))) h0)

@[equational_result]
theorem Equation2554_implies_Equation31 (G: Type _) [Magma G] (h: Equation2554 G) : Equation31 G := fun x y =>
  T (h x y (M (M y x) y)) (C (C (R y) (S (h y y x))) (R x))

@[equational_result]
theorem Equation2592_implies_Equation3201 (G: Type _) [Magma G] (h: Equation2592 G) : Equation3201 G := fun x y z =>
  let v0 := M (M y z) y
  T (h x v0 z) (C (C (R v0) (S (h z z y))) (R x))

@[equational_result]
theorem Equation2714_implies_Equation31 (G: Type _) [Magma G] (h: Equation2714 G) : Equation31 G := fun x y =>
  have h0 := S (h y x x)
  T (h x (M (M x y) (M x x)) x) (C (C h0 h0) (R x))

@[equational_result]
theorem Equation2733_implies_Equation23 (G: Type _) [Magma G] (h: Equation2733 G) : Equation23 G := fun x =>
  let v0 := M x x
  T (h x (M v0 v0)) (C (S (h v0 v0)) (R x))

@[equational_result]
theorem Equation3751_implies_Equation3722 (G: Type _) [Magma G] (h: Equation3751 G) : Equation3722 G := fun x y =>
  let v0 := M x y
  have h1 := h y x
  T (T (h x y) (C h1 h1)) (S (h v0 v0))

@[equational_result]
theorem Equation4143_implies_Equation4135 (G: Type _) [Magma G] (h: Equation4143 G) : Equation4135 G := fun x y z =>
  let v0 := M x y
  T (T (h x y y) (h (M v0 y) y z)) (C (S (h v0 z y)) (R z))

@[equational_result]
theorem Equation1025_implies_Equation8 (G: Type _) [Magma G] (h: Equation1025 G) : Equation8 G := fun x =>
  have h0 := R x
  T (h x (M x (M x x))) (C h0 (C (S (h x x)) h0))

@[equational_result]
theorem Equation2679_implies_Equation260 (G: Type _) [Magma G] (h: Equation2679 G) : Equation260 G := fun x y =>
  let v0 := M x x
  T (h x y (M v0 v0)) (C (C (R (M x y)) (S (h x x x))) (R x))

@[equational_result]
theorem Equation3370_implies_Equation4200 (G: Type _) [Magma G] (h: Equation3370 G) : Equation4200 G := fun x y z =>
  let v0 := M z x
  T (T (h x y z) (C (R y) (h z v0 v0))) (S (h (M v0 z) y v0))

@[equational_result]
theorem Equation3388_implies_Equation3334 (G: Type _) [Magma G] (h: Equation3388 G) : Equation3334 G := fun x y z =>
  T (T (h x y z) (C (R z) (C (R x) (h z y z)))) (S (h x (M z (M z y)) z))

@[equational_result]
theorem Equation3388_implies_Equation3414 (G: Type _) [Magma G] (h: Equation3388 G) : Equation3414 G := fun x y z =>
  let v0 := M x y
  T (T (h x y x) (h x (M x v0) z)) (C (R z) (S (h z v0 x)))

@[equational_result]
theorem Equation3727_implies_Equation3726 (G: Type _) [Magma G] (h: Equation3727 G) : Equation3726 G := fun x y z =>
  have h0 := h x y x
  T (T h0 (h (M x y) (M x x) (M y z))) (C (S h0) (S (h y z x)))

@[equational_result]
theorem Equation4142_implies_Equation4150 (G: Type _) [Magma G] (h: Equation4142 G) : Equation4150 G := fun x y z w =>
  let v0 := M x z
  T (T (h x y z) (C (h v0 y w) (R y))) (S (h (M v0 w) y y))

@[equational_result]
theorem Equation1250_implies_Equation107 (G: Type _) [Magma G] (h: Equation1250 G) : Equation107 G := fun x y =>
  let v0 := M (M y y) x
  T (h x y (M (M (M x x) v0) x)) (C (R x) (S (h v0 x x)))

@[equational_result]
theorem Equation1458_implies_Equation215 (G: Type _) [Magma G] (h: Equation1458 G) : Equation215 G := fun x y z =>
  let v0 := M y z
  T (h x v0 z) (C (R (M x v0)) (S (h y z y)))

@[equational_result]
theorem Equation1656_implies_Equation26 (G: Type _) [Magma G] (h: Equation1656 G) : Equation26 G := fun x y =>
  let v0 := M x y
  T (h x y (M v0 y)) (C (R v0) (S (h y x y)))

@[equational_result]
theorem Equation1912_implies_Equation16 (G: Type _) [Magma G] (h: Equation1912 G) : Equation16 G := fun x y =>
  let v0 := M y x
  T (h x (M y v0) y) (C (S (h y y x)) (R v0))

@[equational_result]
theorem Equation2161_implies_Equation166 (G: Type _) [Magma G] (h: Equation2161 G) : Equation166 G := fun x y =>
  T (h x (M (M y x) y) (M y y)) (C (C (S (h y y x)) (R x)) (R (M x x)))

@[equational_result]
theorem Equation2182_implies_Equation138 (G: Type _) [Magma G] (h: Equation2182 G) : Equation138 G := fun x y z =>
  let v0 := M z y
  T (h x v0 z) (C (S (h y z y)) (R (M v0 x)))

@[equational_result]
theorem Equation3282_implies_Equation3286 (G: Type _) [Magma G] (h: Equation3282 G) : Equation3286 G := fun x y z =>
  have h0 := R y
  T (h x y) (C h0 (C h0 (T (h y x) (S (h z x)))))

@[equational_result]
theorem Equation3770_implies_Equation4146 (G: Type _) [Magma G] (h: Equation3770 G) : Equation4146 G := fun x y z =>
  let v0 := M x z
  T (T (h x y v0) (C (R (M y v0)) (h x v0 z))) (S (h (M v0 z) y v0))

@[equational_result]
theorem Equation4132_implies_Equation4136 (G: Type _) [Magma G] (h: Equation4132 G) : Equation4136 G := fun x y z w =>
  have h0 := h x y z
  T (T h0 (h (M (M x y) y) z w)) (C (C (S h0) (R z)) (R w))

@[equational_result]
theorem Equation4196_implies_Equation39 (G: Type _) [Magma G] (h: Equation4196 G) : Equation39 G := fun x y =>
  let v0 := M x y
  T (T (h x x (M x v0)) (C (S (h v0 x x)) (R x))) (S (h y x x))

@[equational_result]
theorem Equation1230_implies_Equation101 (G: Type _) [Magma G] (h: Equation1230 G) : Equation101 G := fun x y =>
  let v0 := M (M x y) x
  T (h x y (M (M (M v0 x) v0) x)) (C (R x) (S (h v0 x x)))

@[equational_result]
theorem Equation1442_implies_Equation3511 (G: Type _) [Magma G] (h: Equation1442 G) : Equation3511 G := fun x y =>
  have h0 := S (h x y)
  let v1 := M x y
  T (h v1 (M x v1)) (C h0 (C (R v1) h0))

@[equational_result]
theorem Equation1867_implies_Equation156 (G: Type _) [Magma G] (h: Equation1867 G) : Equation156 G := fun x y =>
  T (h x (M y (M x y)) (M y y)) (C (C (R x) (S (h y x y))) (R (M x x)))

@[equational_result]
theorem Equation2090_implies_Equation3955 (G: Type _) [Magma G] (h: Equation2090 G) : Equation3955 G := fun x y =>
  have h0 := S (h y x)
  let v1 := M x y
  T (h v1 (M v1 y)) (C (C h0 (R v1)) h0)

@[equational_result]
theorem Equation2180_implies_Equation14 (G: Type _) [Magma G] (h: Equation2180 G) : Equation14 G := fun x y =>
  let v0 := M x y
  T (h x (M y v0) y) (C (S (h y y v0)) (R v0))

@[equational_result]
theorem Equation2476_implies_Equation208 (G: Type _) [Magma G] (h: Equation2476 G) : Equation208 G := fun x y =>
  have h0 := R x
  T (h x (M y (M (M x x) y)) y) (C (C h0 (C (S (h y x x)) h0)) h0)

@[equational_result]
theorem Equation2503_implies_Equation3050 (G: Type _) [Magma G] (h: Equation2503 G) : Equation3050 G := fun x =>
  let v0 := M (M x x) x
  T (h x v0) (C (C (R v0) (S (h x x))) (R x))

@[equational_result]
theorem Equation2696_implies_Equation203 (G: Type _) [Magma G] (h: Equation2696 G) : Equation203 G := fun x =>
  let v0 := M x x
  T (h x (M v0 v0)) (C (C (S (h x x)) (R v0)) (R x))

@[equational_result]
theorem Equation3556_implies_Equation4065 (G: Type _) [Magma G] (h: Equation3556 G) : Equation4065 G := fun x =>
  have h0 := R x
  have h1 := h x x
  T (T h1 (C h0 (C h1 h0))) (S (h (M (M x x) x) x))

@[equational_result]
theorem Equation1227_implies_Equation100 (G: Type _) [Magma G] (h: Equation1227 G) : Equation100 G := fun x y =>
  let v0 := M x x
  T (h x (M (M (M v0 v0) x) x) y) (C (R x) (C (S (h v0 x x)) (R y)))

@[equational_result]
theorem Equation1558_implies_Equation14 (G: Type _) [Magma G] (h: Equation1558 G) : Equation14 G := fun x y =>
  have h0 := S (h y x y)
  let v1 := M x y
  T (h x v1 (M y v1)) (C h0 (C (R x) h0))

@[equational_result]
theorem Equation1571_implies_Equation2685 (G: Type _) [Magma G] (h: Equation1571 G) : Equation2685 G := fun x y z =>
  let v0 := M z y
  let v1 := M x y
  T (h x v1 v0) (C (R (M v1 v0)) (S (h z x y)))

@[equational_result]
theorem Equation1587_implies_Equation2805 (G: Type _) [Magma G] (h: Equation1587 G) : Equation2805 G := fun x y z =>
  let v0 := M z x
  let v1 := M y z
  T (h x v1 v0) (C (R (M v1 v0)) (S (h y z x)))

@[equational_result]
theorem Equation1660_implies_Equation1871 (G: Type _) [Magma G] (h: Equation1660 G) : Equation1871 G := fun x y z =>
  let v0 := M y z
  T (h x v0 (M (M z x) y)) (C (R (M x v0)) (C (S (h y z x)) (R x)))

@[equational_result]
theorem Equation1682_implies_Equation3050 (G: Type _) [Magma G] (h: Equation1682 G) : Equation3050 G := fun x =>
  let v0 := M (M x x) x
  T (h x v0) (C (R (M v0 x)) (S (h x x)))

@[equational_result]
theorem Equation1885_implies_Equation411 (G: Type _) [Magma G] (h: Equation1885 G) : Equation411 G := fun x =>
  let v0 := M x (M x x)
  T (h x v0) (C (S (h x x)) (R (M x v0)))

@[equational_result]
theorem Equation2706_implies_Equation23 (G: Type _) [Magma G] (h: Equation2706 G) : Equation23 G := fun x =>
  have h0 := S (h x x)
  let v1 := M x x
  T (h x (M v1 v1)) (C (C h0 h0) (R x))

@[equational_result]
theorem Equation3769_implies_Equation3786 (G: Type _) [Magma G] (h: Equation3769 G) : Equation3786 G := fun x y z =>
  have h0 := h x y x
  T (T h0 (h (M y x) (M x y) (M z x))) (C (S (h z x y)) (S h0))

@[equational_result]
theorem Equation3770_implies_Equation3526 (G: Type _) [Magma G] (h: Equation3770 G) : Equation3526 G := fun x y z =>
  let v0 := M y z
  T (T (h x y v0) (C (h y v0 z) (R (M x v0)))) (S (h x (M v0 z) v0))

@[equational_result]
theorem Equation3770_implies_Equation3794 (G: Type _) [Magma G] (h: Equation3770 G) : Equation3794 G := fun x y z =>
  T (T (h x y x) (h (M y x) (M x x) (M z x))) (C (S (h z x x)) (S (h z y x)))

@[equational_result]
theorem Equation840_implies_Equation10 (G: Type _) [Magma G] (h: Equation840 G) : Equation10 G := fun x y =>
  let v0 := M y x
  T (h x y (M v0 v0)) (C (R x) (S (h v0 v0 v0)))

@[equational_result]
theorem Equation887_implies_Equation14 (G: Type _) [Magma G] (h: Equation887 G) : Equation14 G := fun x y =>
  let v0 := M x y
  T (h x y (M v0 v0)) (C (R y) (S (h v0 v0 v0)))

@[equational_result]
theorem Equation914_implies_Equation16 (G: Type _) [Magma G] (h: Equation914 G) : Equation16 G := fun x y =>
  let v0 := M y x
  T (h x y (M v0 v0)) (C (R y) (S (h v0 v0 v0)))

@[equational_result]
theorem Equation928_implies_Equation3932 (G: Type _) [Magma G] (h: Equation928 G) : Equation3932 G := fun x y z =>
  let v0 := M y z
  let v1 := M x v0
  T (C (R x) (h y v1 z)) (S (h (M v1 z) x v0))

@[equational_result]
theorem Equation962_implies_Equation3607 (G: Type _) [Magma G] (h: Equation962 G) : Equation3607 G := fun x y z =>
  let v0 := M y z
  let v1 := M v0 x
  T (C (R x) (h y v1 z)) (S (h (M z v1) x v0))

@[equational_result]
theorem Equation1101_implies_Equation4325 (G: Type _) [Magma G] (h: Equation1101 G) : Equation4325 G := fun x y z =>
  let v0 := M y (M z z)
  have h1 := R x
  T (C h1 (C (h y v0 z) h1)) (S (h v0 x v0))

@[equational_result]
theorem Equation1181_implies_Equation4305 (G: Type _) [Magma G] (h: Equation1181 G) : Equation4305 G := fun x y z =>
  have h0 := R z
  let v1 := M x (M x y)
  T (h v1 z v1) (C h0 (C (S (h y v1 x)) h0))

@[equational_result]
theorem Equation1647_implies_Equation3306 (G: Type _) [Magma G] (h: Equation1647 G) : Equation3306 G := fun x y =>
  let v0 := M x y
  have h1 := S (h x y)
  T (h v0 (M v0 x)) (C h1 (C h1 (R v0)))

@[equational_result]
theorem Equation2116_implies_Equation898 (G: Type _) [Magma G] (h: Equation2116 G) : Equation898 G := fun x y z =>
  let v0 := M z y
  let v1 := M x z
  T (h x v0 v1) (C (S (h y z x)) (R (M v1 v0)))

@[equational_result]
theorem Equation2146_implies_Equation481 (G: Type _) [Magma G] (h: Equation2146 G) : Equation481 G := fun x y z =>
  let v0 := M z z
  let v1 := M y v0
  T (h x v0 v1) (C (S (h y z v0)) (R (M x v1)))

@[equational_result]
theorem Equation2152_implies_Equation1387 (G: Type _) [Magma G] (h: Equation2152 G) : Equation1387 G := fun x y z =>
  let v0 := M z z
  let v1 := M v0 y
  T (h x v0 v1) (C (S (h y z v0)) (R (M v1 x)))

@[equational_result]
theorem Equation2446_implies_Equation23 (G: Type _) [Magma G] (h: Equation2446 G) : Equation23 G := fun x =>
  have h0 := R x
  T (h x (M (M x x) x)) (C (C h0 (S (h x x))) h0)

@[equational_result]
theorem Equation2522_implies_Equation4640 (G: Type _) [Magma G] (h: Equation2522 G) : Equation4640 G := fun x y z =>
  let v0 := M (M y z) z
  have h1 := R x
  T (C (C h1 (h y v0 z)) h1) (S (h v0 x v0))

@[equational_result]
theorem Equation2602_implies_Equation4620 (G: Type _) [Magma G] (h: Equation2602 G) : Equation4620 G := fun x y z =>
  have h0 := R z
  let v1 := M (M x x) y
  T (h v1 z v1) (C (C h0 (S (h y v1 x))) h0)

@[equational_result]
theorem Equation2714_implies_Equation3617 (G: Type _) [Magma G] (h: Equation2714 G) : Equation3617 G := fun x y z =>
  let v0 := M z x
  let v1 := M v0 y
  T (C (h x z v1) (R y)) (S (h (M z v1) v0 y))

@[equational_result]
theorem Equation2722_implies_Equation3973 (G: Type _) [Magma G] (h: Equation2722 G) : Equation3973 G := fun x y z =>
  let v0 := M z x
  let v1 := M y v0
  T (C (h x z v1) (R y)) (S (h (M v1 z) v0 y))

@[equational_result]
theorem Equation2725_implies_Equation3500 (G: Type _) [Magma G] (h: Equation2725 G) : Equation3500 G := fun x y z =>
  let v0 := M z z
  let v1 := M v0 y
  T (h (M x x) v1 z) (C (S (h y v0 x)) (R v1))

@[equational_result]
theorem Equation2739_implies_Equation25 (G: Type _) [Magma G] (h: Equation2739 G) : Equation25 G := fun x y =>
  let v0 := M x y
  T (h x (M v0 v0) y) (C (S (h v0 v0 v0)) (R x))

@[equational_result]
theorem Equation3485_implies_Equation3500 (G: Type _) [Magma G] (h: Equation3485 G) : Equation3500 G := fun x y z =>
  have h0 := R y
  T (h x y) (C h0 (C (T (h y x) (S (h z x))) h0))

@[equational_result]
theorem Equation3825_implies_Equation41 (G: Type _) [Magma G] (h: Equation3825 G) : Equation41 G := fun x y z =>
  T (T (h x x y) (C (R (M y y)) (T (h x y x) (S (h z y x))))) (S (h y z y))

@[equational_result]
theorem Equation3891_implies_Equation3906 (G: Type _) [Magma G] (h: Equation3891 G) : Equation3906 G := fun x y z =>
  have h0 := R y
  T (h x y) (C (C h0 (T (h y x) (S (h z x)))) h0)

@[equational_result]
theorem Equation4094_implies_Equation4098 (G: Type _) [Magma G] (h: Equation4094 G) : Equation4098 G := fun x y z =>
  have h0 := R z
  T (h x z) (C (C (T (h z x) (S (h y x))) h0) h0)

@[equational_result]
theorem Equation522_implies_Equation4305 (G: Type _) [Magma G] (h: Equation522 G) : Equation4305 G := fun x y z =>
  let v0 := M z (M y z)
  have h1 := R x
  T (C h1 (C h1 (h y v0 z))) (S (h v0 x v0))

@[equational_result]
theorem Equation1496_implies_Equation3161 (G: Type _) [Magma G] (h: Equation1496 G) : Equation3161 G := fun x y z =>
  let v0 := M y y
  let v1 := M v0 z
  T (h x v1 v0) (C (R (M v1 x)) (S (h z v0 y)))

@[equational_result]
theorem Equation1780_implies_Equation16 (G: Type _) [Magma G] (h: Equation1780 G) : Equation16 G := fun x y =>
  have h0 := S (h y y x)
  let v1 := M y x
  T (h x v1 (M v1 y)) (C h0 (C h0 (R x)))

@[equational_result]
theorem Equation1850_implies_Equation4131 (G: Type _) [Magma G] (h: Equation1850 G) : Equation4131 G := fun x y =>
  have h0 := S (h y x)
  let v1 := M x y
  T (h v1 (M y v1)) (C (C (R v1) h0) h0)

@[equational_result]
theorem Equation1875_implies_Equation1668 (G: Type _) [Magma G] (h: Equation1875 G) : Equation1668 G := fun x y z =>
  let v0 := M z y
  T (h x (M y (M x z)) v0) (C (C (R x) (S (h y x z))) (R (M v0 x)))

@[equational_result]
theorem Equation2310_implies_Equation218 (G: Type _) [Magma G] (h: Equation2310 G) : Equation218 G := fun x y =>
  have h0 := R x
  T (h x y (M x (M x (M x x)))) (C (C (R y) (C h0 (S (h x x x)))) h0)

@[equational_result]
theorem Equation3185_implies_Equation1764 (G: Type _) [Magma G] (h: Equation3185 G) : Equation1764 G := fun x y z =>
  let v0 := M (M x z) y
  T (h x v0 z) (C (C (S (h y x z)) (R z)) (R v0))

@[equational_result]
theorem Equation3370_implies_Equation4023 (G: Type _) [Magma G] (h: Equation3370 G) : Equation4023 G := fun x y z =>
  T (T (h x y x) (C (R y) (C (R x) (h x x z)))) (S (h (M z (M z x)) y x))

@[equational_result]
theorem Equation3553_implies_Equation4146 (G: Type _) [Magma G] (h: Equation3553 G) : Equation4146 G := fun x y z =>
  let v0 := M (M x z) z
  T (T (h x y v0) (C (R y) (C (h x v0 z) (R v0)))) (S (h v0 y v0))

@[equational_result]
theorem Equation3620_implies_Equation3534 (G: Type _) [Magma G] (h: Equation3620 G) : Equation3534 G := fun x y z =>
  T (T (h x y z) (C (R z) (C (h z y z) (R x)))) (S (h x (M (M z y) z) z))

@[equational_result]
theorem Equation3718_implies_Equation329 (G: Type _) [Magma G] (h: Equation3718 G) : Equation329 G := fun x y z =>
  let v0 := M z y
  T (T (h x y v0) (C (R (M x x)) (h v0 y z))) (S (h x v0 (M v0 v0)))

@[equational_result]
theorem Equation3736_implies_Equation381 (G: Type _) [Magma G] (h: Equation3736 G) : Equation381 G := fun x y z =>
  let v0 := M x z
  T (T (h x y v0) (C (h x v0 z) (R (M y y)))) (S (h v0 y (M v0 v0)))

@[equational_result]
theorem Equation3776_implies_Equation3997 (G: Type _) [Magma G] (h: Equation3776 G) : Equation3997 G := fun x y z =>
  let v0 := M x z
  T (T (h x y v0) (C (R (M y v0)) (h v0 x z))) (S (h (M z v0) y v0))

@[equational_result]
theorem Equation3804_implies_Equation3534 (G: Type _) [Magma G] (h: Equation3804 G) : Equation3534 G := fun x y z =>
  let v0 := M z y
  T (T (h x y v0) (C (h v0 y z) (R (M x v0)))) (S (h x (M v0 z) v0))

@[equational_result]
theorem Equation3804_implies_Equation3997 (G: Type _) [Magma G] (h: Equation3804 G) : Equation3997 G := fun x y z =>
  let v0 := M x z
  T (T (h x y v0) (C (R (M v0 y)) (h x v0 z))) (S (h (M z v0) y v0))

@[equational_result]
theorem Equation3810_implies_Equation3334 (G: Type _) [Magma G] (h: Equation3810 G) : Equation3334 G := fun x y z =>
  let v0 := M z y
  T (T (h x y v0) (C (h v0 y z) (R (M v0 x)))) (S (h x (M z v0) v0))

@[equational_result]
theorem Equation3810_implies_Equation3737 (G: Type _) [Magma G] (h: Equation3810 G) : Equation3737 G := fun x y z =>
  T (T (h x y x) (h (M x y) (M x x) (M x z))) (C (S (h x z x)) (S (h y z x)))

@[equational_result]
theorem Equation3990_implies_Equation41 (G: Type _) [Magma G] (h: Equation3990 G) : Equation41 G := fun x y z =>
  T (T (h x x y) (C (T (h y (M x x) x) (S (h y (M y y) x))) (R y))) (S (h y z y))

@[equational_result]
theorem Equation4182_implies_Equation3526 (G: Type _) [Magma G] (h: Equation4182 G) : Equation3526 G := fun x y z =>
  T (T (h x y y) (C (C (h y y z) (R y)) (R x))) (S (h x (M (M y z) z) y))

@[equational_result]
theorem Equation4227_implies_Equation41 (G: Type _) [Magma G] (h: Equation4227 G) : Equation41 G := fun x y z =>
  let v0 := M y y
  T (T (h x x y) (C (T (h v0 x x) (S (h v0 y x))) (R y))) (S (h y z y))

@[equational_result]
theorem Equation4233_implies_Equation41 (G: Type _) [Magma G] (h: Equation4233 G) : Equation41 G := fun x y z =>
  let v0 := M (M x x) x
  T (T (T (h x x x) (h v0 x x)) (S (h v0 y x))) (S (h y z x))

@[equational_result]
theorem Equation978_implies_Equation3906 (G: Type _) [Magma G] (h: Equation978 G) : Equation3906 G := fun x y z =>
  let v0 := M z z
  let v1 := M y v0
  T (h (M x x) v1 z) (C (R v1) (S (h y v0 x)))

@[equational_result]
theorem Equation1022_implies_Equation99 (G: Type _) [Magma G] (h: Equation1022 G) : Equation99 G := fun x =>
  have h0 := R x
  T (h x (M (M x (M x x)) x)) (C h0 (C (C h0 (S (h x x))) h0))

@[equational_result]
theorem Equation1228_implies_Equation99 (G: Type _) [Magma G] (h: Equation1228 G) : Equation99 G := fun x =>
  have h0 := R x
  T (h x (M (M (M x x) x) x)) (C h0 (C (C (S (h x x)) h0) h0))

@[equational_result]
theorem Equation1659_implies_Equation26 (G: Type _) [Magma G] (h: Equation1659 G) : Equation26 G := fun x y =>
  let v0 := M y y
  T (h x y y) (C (R (M x y)) (T (C (R v0) (h y y x)) (S (h y y (M v0 x)))))

@[equational_result]
theorem Equation1873_implies_Equation26 (G: Type _) [Magma G] (h: Equation1873 G) : Equation26 G := fun x y =>
  have h0 := S (h y x y)
  let v1 := M x y
  T (h x (M y v1) v1) (C (C (R x) h0) h0)

@[equational_result]
theorem Equation2199_implies_Equation3997 (G: Type _) [Magma G] (h: Equation2199 G) : Equation3997 G := fun x y z =>
  let v0 := M x z
  T (h (M x y) (M (M x x) x) v0) (C (C (S (h z x x)) (R v0)) (S (h y x x)))

@[equational_result]
theorem Equation3605_implies_Equation41 (G: Type _) [Magma G] (h: Equation3605 G) : Equation41 G := fun x y z =>
  T (T (h x x y) (C (R y) (T (h (M x x) y x) (S (h (M z z) y x))))) (S (h y z y))

@[equational_result]
theorem Equation3620_implies_Equation3588 (G: Type _) [Magma G] (h: Equation3620 G) : Equation3588 G := fun x y z =>
  have h0 := R z
  have h1 := h x y z
  T (T h1 (h z (M (M z y) x) z)) (C h0 (C (S h1) h0))

@[equational_result]
theorem Equation3810_implies_Equation4023 (G: Type _) [Magma G] (h: Equation3810 G) : Equation4023 G := fun x y z =>
  let v0 := M z x
  T (T (h x y v0) (C (R (M v0 y)) (h v0 x z))) (S (h (M z v0) y v0))

@[equational_result]
theorem Equation4026_implies_Equation3334 (G: Type _) [Magma G] (h: Equation4026 G) : Equation3334 G := fun x y z =>
  let v0 := M z (M z y)
  T (T (h x y v0) (C (C (R v0) (h v0 y z)) (R x))) (S (h x v0 v0))

@[equational_result]
theorem Equation4026_implies_Equation4182 (G: Type _) [Magma G] (h: Equation4026 G) : Equation4182 G := fun x y z =>
  let v0 := M x (M x z)
  T (h x y v0) (C (T (C (R v0) (S (h y z x))) (S (h (M y z) z x))) (R x))

