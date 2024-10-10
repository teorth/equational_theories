import equational_theories.Equations.All
import equational_theories.Magma

private def congr_op {G: Type _} [Magma G] {a b c d: G} (h1: a = b) (h2: c = d): a ◇ c = b ◇ d := by
  rw [h1, h2]
private abbrev T := @Eq.trans
private abbrev S := @Eq.symm
private abbrev R := @Eq.refl
private abbrev M := @Magma.op
private abbrev C := @congr_op

@[equational_result]
theorem Equation3622_implies_Equation41 (G: Type _) [Magma G] (h: Equation3622 G) : Equation41 G := fun x y z =>
  have h0 := h y z x
  have h1 := R x
  T (T (T (h x x x) (C h1 (T (T (h (M x x) x x) (S (h (M y z) x x))) (C h0 h1)))) (S (h x (M (M x z) x) x))) (S h0)

@[equational_result]
theorem Equation4132_implies_Equation4672 (G: Type _) [Magma G] (h: Equation4132 G) : Equation4672 G := fun x y z w =>
  have h0 := h x y z
  let v1 := M x y
  have h2 := R z
  T (h v1 z w) (C (T (T (C (C h0 h2) h2) (S (h (M v1 y) z z))) (S h0)) (R w))

@[equational_result]
theorem Equation759_implies_Equation1181 (G: Type _) [Magma G] (h: Equation759 G) : Equation1181 G := fun x y z =>
  let v0 := M z x
  let v1 := M y (M (M z v0) y)
  have h2 := R v1
  T (T (h x z v1) (C (R z) (C h2 (C (h v0 z y) h2)))) (S (h v1 z v1))

@[equational_result]
theorem Equation934_implies_Equation778 (G: Type _) [Magma G] (h: Equation934 G) : Equation778 G := fun x y z =>
  let v0 := M z y
  let v1 := M v0 x
  have h2 := h x y v1
  T h2 (C (R y) (T (h (M (M y v1) (M v1 x)) z y) (C (R z) (C (R v0) (S h2)))))

@[equational_result]
theorem Equation1181_implies_Equation2349 (G: Type _) [Magma G] (h: Equation1181 G) : Equation2349 G := fun x y z =>
  let v0 := M z x
  let v1 := M (M y (M y v0)) z
  have h2 := R v1
  T (T (h x v1 z) (C h2 (C (C (R z) (h v0 z y)) h2))) (S (h v1 v1 z))

@[equational_result]
theorem Equation2917_implies_Equation2519 (G: Type _) [Magma G] (h: Equation2917 G) : Equation2519 G := fun x y z =>
  let v0 := M x z
  let v1 := M (M y (M v0 y)) z
  have h2 := R v1
  T (T (h x z v1) (C (C (C (R z) (h v0 y z)) h2) h2)) (S (h v1 z v1))

@[equational_result]
theorem Equation3110_implies_Equation2 (G: Type _) [Magma G] (h: Equation3110 G) : Equation2 G := fun x y =>
  let v0 := M x y
  let v1 := M v0 y
  have h2 := R y
  T (T (h x v1 y) (C (T (C (S (h y x x)) h2) (C (h y v0 y) h2)) h2)) (S (h y (M v1 y) y))

@[equational_result]
theorem Equation3118_implies_Equation5 (G: Type _) [Magma G] (h: Equation3118 G) : Equation5 G := fun x y =>
  have h0 := R x
  have h1 := R y
  let v2 := M y x
  T (h x y y) (C (T (C (C (C (T (h y v2 x) (C (S (h x y v2)) h1)) h0) h1) h1) (S (h y x y))) h0)

@[equational_result]
theorem Equation3591_implies_Equation3740 (G: Type _) [Magma G] (h: Equation3591 G) : Equation3740 G := fun x y z =>
  let v0 := M x z
  let v1 := M v0 v0
  T (T (h x y v0) (h v0 (M (M x v0) y) v0)) (C (R v0) (T (C (R v1) (C (h x v0 z) (R y))) (S (h z y v1))))

@[equational_result]
theorem Equation3940_implies_Equation3740 (G: Type _) [Magma G] (h: Equation3940 G) : Equation3740 G := fun x y z =>
  let v0 := M z y
  let v1 := M v0 v0
  T (T (h x y v0) (h (M x (M v0 y)) v0 v0)) (C (T (C (C (R x) (h v0 y z)) (R v1)) (S (h x z v1))) (R v0))

@[equational_result]
theorem Equation2103_implies_Equation19 (G: Type _) [Magma G] (h: Equation2103 G) : Equation19 G := fun x y z =>
  let v0 := M z x
  let v1 := M y v0
  T (T (T (h x (M x v1) z) (C (S (h v1 x x)) (R v0))) (C (h v1 v1 v1) (h v0 y y))) (S (h v1 (M v1 v1) (M v1 y)))

@[equational_result]
theorem Equation2308_implies_Equation2113 (G: Type _) [Magma G] (h: Equation2308 G) : Equation2113 G := fun x y z =>
  let v0 := M y z
  let v1 := M y x
  have h2 := h x v1 v0
  T h2 (C (T (h (M v1 (M x (M v1 v0))) y z) (C (C (R y) (S h2)) (R z))) (R v0))

@[equational_result]
theorem Equation2776_implies_Equation3185 (G: Type _) [Magma G] (h: Equation2776 G) : Equation3185 G := fun x y z =>
  let v0 := M y z
  let v1 := M v0 x
  have h2 := h x v1 y
  T h2 (C (T (h (M (M v1 y) (M x v1)) y z) (C (C (R v0) (S h2)) (R z))) (R y))

@[equational_result]
theorem Equation2925_implies_Equation2522 (G: Type _) [Magma G] (h: Equation2925 G) : Equation2522 G := fun x y z =>
  let v0 := M x z
  let v1 := M (M y (M v0 z)) y
  have h2 := R v1
  T (T (h x v1 z) (C (C (C h2 (h v0 y z)) h2) (R z))) (S (h v1 v1 z))

@[equational_result]
theorem Equation2741_implies_Equation26 (G: Type _) [Magma G] (h: Equation2741 G) : Equation26 G := fun x y =>
  have h0 := R y
  have h1 := h x x y
  let v2 := M x x
  T h1 (C (T (h (M v2 (M x y)) v2 y) (C (T (C (R (M v2 v2)) (S h1)) (S (h x x x))) h0)) h0)

@[equational_result]
theorem Equation2789_implies_Equation952 (G: Type _) [Magma G] (h: Equation2789 G) : Equation952 G := fun x y z =>
  let v0 := M (M z x) (M z y)
  have h1 := h v0 x y
  T (h x v0 v0) (C (T (C (C h1 h1) (S (h y z x))) (S (h y (M (M x y) (M x v0)) y))) (R v0))

@[equational_result]
theorem Equation3104_implies_Equation2 (G: Type _) [Magma G] (h: Equation3104 G) : Equation2 G := fun x y =>
  have h0 := S (h y (M x y) x)
  have h1 := R x
  have h2 := C (h y x y) h1
  T (T (T (h x (M (M (M y y) y) y) x) (C (T (T (C (T (T (C (S (h y y x)) h1) h2) h0) h1) h2) h0) h1)) h2) h0

@[equational_result]
theorem Equation1718_implies_Equation4622 (G: Type _) [Magma G] (h: Equation1718 G) : Equation4622 G := fun x y z =>
  let v0 := M z z
  let v1 := M v0 y
  let v2 := M (M y y) y
  T (C (R (M x x)) (T (h y v1) (C (R (M v1 v1)) (T (h v2 z) (C (R v0) (S (h y v2))))))) (S (h v1 x))

@[equational_result]
theorem Equation3417_implies_Equation4007 (G: Type _) [Magma G] (h: Equation3417 G) : Equation4007 G := fun x y z =>
  let v0 := M y x
  have h1 := R v0
  have h2 := h x y v0
  T (T (T h2 (C h1 (h v0 v0 v0))) (C h1 (T (C h1 (S h2)) (C h1 (h x y z))))) (S (h (M z v0) z v0))

@[equational_result]
theorem Equation3790_implies_Equation4490 (G: Type _) [Magma G] (h: Equation3790 G) : Equation4490 G := fun x y z =>
  let v0 := M z x
  have h1 := S (h y y y)
  let v2 := M y y
  T (T (T (T (h x v2 z) (C (R v0) h1)) (h v0 v2 x)) (C (R (M x v0)) h1)) (S (h v0 y x))

@[equational_result]
theorem Equation556_implies_Equation1355 (G: Type _) [Magma G] (h: Equation556 G) : Equation1355 G := fun x y z =>
  let v0 := M z x
  let v1 := M v0 y
  have h2 := R y
  T (h x y v1) (C h2 (C (R v1) (T (C h2 (C (R x) (T (h v1 y v1) (C h2 (S (h v0 v1 y)))))) (S (h z y x)))))

@[equational_result]
theorem Equation1080_implies_Equation2 (G: Type _) [Magma G] (h: Equation1080 G) : Equation2 G := fun x y =>
  let v0 := M (M x (M x x)) x
  let v1 := M (M v0 (M v0 x)) x
  T (T (h x x x) (C (R x) (T (h v0 x x) (C (T (h x y x) (C (R y) (h v0 y x))) (R v1))))) (S (h y x v1))

@[equational_result]
theorem Equation3736_implies_Equation4476 (G: Type _) [Magma G] (h: Equation3736 G) : Equation4476 G := fun x y z =>
  let v0 := M x z
  let v1 := M v0 v0
  let v2 := M y y
  T (T (T (h x v2 v0) (C (h x v0 z) (R (M v2 v2)))) (C (R (M v0 v1)) (S (h y y y)))) (S (h v0 y v1))

@[equational_result]
theorem Equation3791_implies_Equation4305 (G: Type _) [Magma G] (h: Equation3791 G) : Equation4305 G := fun x y z =>
  let v0 := M x y
  let v1 := M v0 z
  T (T (T (T (h x v0 z) (h (M z x) v1 (M x v0))) (C (S (h v0 z x)) (S (h z x v0)))) (C (R v1) (h z x y))) (S (h z (M y z) v0))

@[equational_result]
theorem Equation778_implies_Equation1590 (G: Type _) [Magma G] (h: Equation778 G) : Equation1590 G := fun x y z =>
  let v0 := M y z
  let v1 := M v0 (M z (M y x))
  have h2 := h x v0 v1
  T h2 (C (R v0) (T (h (M v1 (M (M v1 v0) x)) z y) (C (R z) (C (R y) (S h2)))))

@[equational_result]
theorem Equation4229_implies_Equation4226 (G: Type _) [Magma G] (h: Equation4229 G) : Equation4226 G := fun x y z =>
  let v0 := M z z
  let v1 := M v0 x
  let v2 := M (M x x) y
  T (T (T (T (h x y x) (h v2 x z)) (C (T (h v0 x z) (h v1 v0 z)) (R v2))) (S (h v2 v1 v0))) (S (h v1 y x))

@[equational_result]
theorem Equation765_implies_Equation1577 (G: Type _) [Magma G] (h: Equation765 G) : Equation1577 G := fun x y z =>
  let v0 := M y z
  let v1 := M v0 (M y (M z x))
  have h2 := h x v0 v1
  T h2 (C (R v0) (T (h (M v1 (M (M v0 v1) x)) y z) (C (R y) (C (R z) (S h2)))))

@[equational_result]
theorem Equation2942_implies_Equation5 (G: Type _) [Magma G] (h: Equation2942 G) : Equation5 G := fun x y =>
  let v0 := M y x
  let v1 := M (M x (M x y)) y
  have h2 := h y x y
  T (h x y y) (C (T (C (C (T h2 (C (R v1) h2)) (R v0)) (R y)) (S (h y v1 v0))) (R x))

@[equational_result]
theorem Equation4176_implies_Equation3591 (G: Type _) [Magma G] (h: Equation4176 G) : Equation3591 G := fun x y z =>
  let v0 := M x z
  have h1 := R v0
  let v2 := M y v0
  T (T (h x y v0) (C (T (h v2 x z) (C (T (h v0 v2 v0) (C (S (h v0 y v0)) h1)) (R z))) h1)) (S (h z (M v0 y) v0))

@[equational_result]
theorem Equation1640_implies_Equation3258 (G: Type _) [Magma G] (h: Equation1640 G) : Equation3258 G := fun x y =>
  let v0 := M x x
  have h1 := R v0
  let v2 := M v0 x
  T (h v0 (M y y) (M v2 y)) (C (T (C h1 (C (h x x x) (R x))) (S (h x v0 v2))) (C (S (h y v0 x)) h1))

@[equational_result]
theorem Equation556_implies_Equation1117 (G: Type _) [Magma G] (h: Equation556 G) : Equation1117 G := fun x y z =>
  let v0 := M x z
  have h1 := R y
  let v2 := M y v0
  T (h x y v2) (C h1 (C (R v2) (T (C h1 (C (R x) (C h1 (T (h v0 z v0) (C (R z) (S (h x v0 z))))))) (S (h z y x)))))

@[equational_result]
theorem Equation714_implies_Equation2338 (G: Type _) [Magma G] (h: Equation714 G) : Equation2338 G := fun x y =>
  let v0 := M y x
  let v1 := M y v0
  let v2 := M (M y v1) y
  have h3 := R y
  T (T (h x y) (C h3 (C h3 (C (T (T (h v0 y) (C h3 (C h3 (C (h v1 y) h3)))) (S (h (M y v2) y))) h3)))) (S (h v2 y))

@[equational_result]
theorem Equation981_implies_Equation731 (G: Type _) [Magma G] (h: Equation981 G) : Equation731 G := fun x y z =>
  let v0 := M z z
  let v1 := M y (M v0 x)
  have h2 := h x y v1
  have h3 := R y
  T h2 (C h3 (T (h (M (M v1 v1) (M y x)) y z) (C h3 (C (R v0) (S h2)))))

@[equational_result]
theorem Equation1790_implies_Equation26 (G: Type _) [Magma G] (h: Equation1790 G) : Equation26 G := fun x y =>
  let v0 := M x y
  let v1 := M v0 y
  have h2 := h x v0 y
  T (T h2 (C (R v1) (T (h (M (M y x) v0) y v1) (C (R (M y v1)) (C (S h2) (R y)))))) (S (h v1 v0 y))

@[equational_result]
theorem Equation1913_implies_Equation16 (G: Type _) [Magma G] (h: Equation1913 G) : Equation16 G := fun x y =>
  let v0 := M y x
  let v1 := M y v0
  have h2 := h x v0 y
  T (T h2 (C (T (h (M v0 (M x y)) y v1) (C (C (R y) (S h2)) (R (M v1 y)))) (R v1))) (S (h v1 v0 y))

@[equational_result]
theorem Equation2135_implies_Equation1519 (G: Type _) [Magma G] (h: Equation2135 G) : Equation1519 G := fun x y =>
  let v0 := M y y
  let v1 := M v0 y
  let v2 := M (M v0 v0) v0
  T (h x v0) (C (T (T (h v2 y) (C (R v1) (T (C (R v2) (h y y)) (S (h v1 v0))))) (S (h v0 y))) (R (M x v0)))

@[equational_result]
theorem Equation2511_implies_Equation3128 (G: Type _) [Magma G] (h: Equation2511 G) : Equation3128 G := fun x y z =>
  let v0 := M y x
  let v1 := M v0 z
  let v2 := M v1 y
  T (h x v1 z) (C (T (C (C (R v0) (T (h z v2 y) (C (C (R v2) (S (h v0 z y))) (R y)))) (S (h y x z))) (S (h v2 v0 y))) (R z))

@[equational_result]
theorem Equation3776_implies_Equation4684 (G: Type _) [Magma G] (h: Equation3776 G) : Equation4684 G := fun x y z =>
  let v0 := M z y
  let v1 := M x y
  let v2 := M y v1
  T (T (T (h v1 z y) (h v0 v2 z)) (C (T (T (h v2 z v1) (C (R (M z v1)) (S (h v1 x y)))) (S (h x z v1))) (R (M z v0)))) (S (h v0 x z))

@[equational_result]
theorem Equation3810_implies_Equation3895 (G: Type _) [Magma G] (h: Equation3810 G) : Equation3895 G := fun x y z =>
  let v0 := M y z
  let v1 := M v0 z
  have h2 := h z x v0
  T (T (T (T (h x x z) (C h2 h2)) (S (h v1 v1 (M v0 x)))) (C (R v1) (h v0 z y))) (S (h (M y v0) z v0))

@[equational_result]
theorem Equation1090_implies_Equation1117 (G: Type _) [Magma G] (h: Equation1090 G) : Equation1117 G := fun x y z =>
  let v0 := M (M y (M x z)) z
  have h1 := S (h v0 y x)
  let v2 := M (M v0 (M y x)) x
  T (h x y v2) (C (R y) (T (C (T (C (R x) h1) (S (h y x z))) (R v2)) h1))

@[equational_result]
theorem Equation2349_implies_Equation572 (G: Type _) [Magma G] (h: Equation2349 G) : Equation572 G := fun x y z =>
  let v0 := M z (M z (M x y))
  have h1 := S (h y x y)
  let v2 := M x (M x (M y y))
  have h3 := R v2
  T (h x v2 v0) (C (T (C h3 (T (C h3 (S (h y z x))) h1)) h1) (R v0))

@[equational_result]
theorem Equation1761_implies_Equation1910 (G: Type _) [Magma G] (h: Equation1761 G) : Equation1910 G := fun x y z =>
  let v0 := M y z
  let v1 := M x z
  let v2 := M (M y v1) v0
  T (T (h x z v0) (C (R (M z v0)) (T (h (M v1 v0) v2 z) (C (R (M v2 z)) (C (S (h y v1 v0)) (R z)))))) (S (h v2 z v0))

@[equational_result]
theorem Equation2131_implies_Equation2 (G: Type _) [Magma G] (h: Equation2131 G) : Equation2 G := fun x y =>
  let v0 := M y y
  have h1 := h v0 y y
  T (T (h x y x) (C (T (T (T (C h1 (h x y y)) (S (h v0 v0 (M v0 x)))) (h v0 v0 (M v0 y))) (C (S h1) (S (h y y y)))) (R (M x y)))) (S (h y y x))

@[equational_result]
theorem Equation2161_implies_Equation3877 (G: Type _) [Magma G] (h: Equation2161 G) : Equation3877 G := fun x y =>
  let v0 := M x x
  let v1 := M y v0
  have h2 := R v0
  T (h v0 (M (M v1 v1) y) (M y y)) (C (C (S (h y v1 v1)) h2) (T (C (C (h x y v0) (R x)) h2) (S (h x (M v1 x) v0))))

@[equational_result]
theorem Equation2913_implies_Equation1289 (G: Type _) [Magma G] (h: Equation2913 G) : Equation1289 G := fun x y =>
  let v0 := M x y
  let v1 := M v0 y
  let v2 := M y (M v1 y)
  have h3 := R y
  T (T (h x y) (C (C (C h3 (T (T (h v0 y) (C (C (C h3 (h v1 y)) h3) h3)) (S (h (M v2 y) y)))) h3) h3)) (S (h v2 y))

@[equational_result]
theorem Equation3128_implies_Equation1301 (G: Type _) [Magma G] (h: Equation3128 G) : Equation1301 G := fun x y z =>
  let v0 := M (M x z) y
  let v1 := M v0 z
  let v2 := M y v1
  T (T (h x v0 y) (C (T (T (C (T (S (h z x y)) (h z v0 v1)) (R v0)) (S (h v1 v1 v0))) (h v1 y v2)) (R y))) (S (h v2 v2 y))

@[equational_result]
theorem Equation3770_implies_Equation4210 (G: Type _) [Magma G] (h: Equation3770 G) : Equation4210 G := fun x y z =>
  let v0 := M z y
  let v1 := M v0 x
  T (T (T (T (T (h x y x) (h (M y x) (M x x) v1)) (C (S (h v0 x x)) (S (h v0 y x)))) (h v1 (M v0 y) v0)) (C (S (h z v0 y)) (R (M v1 v0)))) (S (h v1 z v0))

@[equational_result]
theorem Equation4229_implies_Equation3943 (G: Type _) [Magma G] (h: Equation4229 G) : Equation3943 G := fun x y z =>
  let v0 := M z z
  let v1 := M x v0
  let v2 := M v0 y
  T (T (T (T (h x y z) (h v2 x z)) (C (T (T (h v0 x v0) (C (S (h x v0 z)) (R v0))) (h v1 v0 z)) (R v2))) (S (h v2 v1 v0))) (S (h v1 y z))

@[equational_result]
theorem Equation1305_implies_Equation2 (G: Type _) [Magma G] (h: Equation1305 G) : Equation2 G := fun x y =>
  let v0 := M (M (M y x) x) x
  have h1 := R v0
  have h2 := h y y x
  T (T (h x y v0) (C (R y) (T (C (T (C (S (h y x x)) h1) (S h2)) h1) (C (T h2 (C h2 h1)) h1)))) (S (h y y v0))

@[equational_result]
theorem Equation3573_implies_Equation3350 (G: Type _) [Magma G] (h: Equation3573 G) : Equation3350 G := fun x y z =>
  let v0 := M z z
  have h1 := R y
  let v2 := M (M x x) x
  T (T (T (T (h x y z) (C h1 (T (h v0 x z) (h x (M v0 v0) x)))) (S (h v2 y v0))) (h v2 y z)) (C h1 (S (h x v0 x)))

@[equational_result]
theorem Equation3810_implies_Equation3398 (G: Type _) [Magma G] (h: Equation3810 G) : Equation3398 G := fun x y z =>
  let v0 := M x z
  let v1 := M y v0
  T (T (T (T (T (h x y y) (h (M y y) (M y x) v1)) (C (S (h x v0 y)) (S (h y v0 y)))) (h (M x v0) v1 v0)) (C (R (M v0 v1)) (S (h v0 z x)))) (S (h z v1 v0))

@[equational_result]
theorem Equation2113_implies_Equation1577 (G: Type _) [Magma G] (h: Equation2113 G) : Equation1577 G := fun x y z =>
  let v0 := M y z
  let v1 := M z x
  let v2 := M y v1
  let v3 := M v0 v2
  T (T (h x z v0) (C (C (T (h v1 v0 v2) (C (S (h z y v1)) (R v3))) (R v0)) (R (M z v0)))) (S (h v3 z v0))

@[equational_result]
theorem Equation3370_implies_Equation3331 (G: Type _) [Magma G] (h: Equation3370 G) : Equation3331 G := fun x y z =>
  let v0 := M y z
  let v1 := M z v0
  let v2 := M x (M x x)
  T (T (T (T (h x y x) (h y v2 z)) (C (R v2) (T (T (C (R z) (h z y y)) (S (h v0 z y))) (h v0 z z)))) (S (h v1 v2 z))) (S (h x v1 x))

@[equational_result]
theorem Equation3770_implies_Equation3489 (G: Type _) [Magma G] (h: Equation3770 G) : Equation3489 G := fun x y z =>
  let v0 := M y z
  let v1 := M v0 z
  let v2 := M v1 v0
  have h3 := h x v1 v0
  T (T (T (T (h x x v1) (C h3 h3)) (S (h v2 v2 (M x v0)))) (C (R v2) (S (h y v0 z)))) (S (h y v1 v0))

@[equational_result]
theorem Equation4176_implies_Equation4106 (G: Type _) [Magma G] (h: Equation4176 G) : Equation4106 G := fun x y z =>
  have h0 := R y
  let v1 := M y z
  let v2 := M z v1
  T (T (T (h x x y) (C (T (C (h x y z) (R x)) (S (h z v1 x))) h0)) (h v2 y z)) (C (T (h v1 v2 y) (C (S (h y z v1)) h0)) (R z))

@[equational_result]
theorem Equation1131_implies_Equation556 (G: Type _) [Magma G] (h: Equation1131 G) : Equation556 G := fun x y z =>
  let v0 := M y (M x z)
  let v1 := M y (M z v0)
  have h2 := R y
  T (T (h x y v0) (C h2 (C (T (T (S (h z y x)) (h z y v1)) (C h2 (C (S (h v0 y z)) (R v1)))) (R v0)))) (S (h v1 y v0))

@[equational_result]
theorem Equation1430_implies_Equation3457 (G: Type _) [Magma G] (h: Equation1430 G) : Equation3457 G := fun x y =>
  let v0 := M x x
  let v1 := M v0 y
  let v2 := M x v1
  have h3 := R v0
  T (h v0 (M y y) (M y (M v1 v2))) (C (T (C h3 (C (R x) (h x v0 y))) (S (h x v0 v2))) (C h3 (S (h y v1 v2))))

@[equational_result]
theorem Equation1557_implies_Equation2 (G: Type _) [Magma G] (h: Equation1557 G) : Equation2 G := fun x y =>
  have h0 := S (h y x x)
  let v1 := M x x
  have h2 := h v1 x x
  have h3 := h x x x
  T (T h3 (C (R v1) (T (T (T (C h3 h2) (S (h v1 v1 (M x v1)))) (h v1 v1 (M y v1))) (C h0 (S h2))))) h0

@[equational_result]
theorem Equation1649_implies_Equation27 (G: Type _) [Magma G] (h: Equation1649 G) : Equation27 G := fun x y z =>
  let v0 := M x y
  let v1 := M v0 z
  have h2 := h v0 z x
  have h3 := C (R v0) (S (h x y z))
  have h4 := h x y v1
  T (T (T h4 h3) (C h2 (T (T h4 h3) (C h2 (R x))))) (S (h v1 (M v1 x) x))

@[equational_result]
theorem Equation556_implies_Equation2383 (G: Type _) [Magma G] (h: Equation556 G) : Equation2383 G := fun x y z =>
  let v0 := M z (M y x)
  let v1 := M y v0
  let v2 := M v1 z
  T (T (h x z v0) (C (R z) (T (T (C (R v0) (T (S (h y z x)) (h y v1 v0))) (S (h v1 v0 v1))) (h v1 v2 z)))) (S (h v2 z v2))

@[equational_result]
theorem Equation659_implies_Equation4 (G: Type _) [Magma G] (h: Equation659 G) : Equation4 G := fun x y =>
  let v0 := M x (M (M x x) x)
  let v1 := M (M y y) y
  have h2 := h v0 x x
  T (h x y y) (C (R x) (T (C (R y) (T (h v1 x x) (C (R v1) (T h2 (C h2 (R v0)))))) (S (h y v1 v0))))

@[equational_result]
theorem Equation2136_implies_Equation2 (G: Type _) [Magma G] (h: Equation2136 G) : Equation2 G := fun x y =>
  let v0 := M x x
  let v1 := M v0 x
  let v2 := M y y
  T (T (T (T (T (h x x x) (C (R v1) (h v0 x x))) (S (h v1 x v1))) (h v1 v1 (M v2 x))) (C (R (M (M v1 v1) v1)) (S (h v2 x x)))) (S (h y v1 y))

@[equational_result]
theorem Equation3810_implies_Equation3297 (G: Type _) [Magma G] (h: Equation3810 G) : Equation3297 G := fun x y z =>
  let v0 := M z y
  let v1 := M z v0
  let v2 := M v0 v1
  have h3 := h v1 x v0
  T (T (T (T (h x x v1) (C h3 h3)) (S (h v2 v2 (M v0 x)))) (C (R v2) (S (h v0 y z)))) (S (h y v1 v0))

@[equational_result]
theorem Equation1508_implies_Equation2 (G: Type _) [Magma G] (h: Equation1508 G) : Equation2 G := fun x y =>
  let v0 := M x x
  let v1 := M x v0
  let v2 := M y y
  T (T (T (T (T (h x x x) (C (h v0 x x) (R v1))) (S (h v1 v1 x))) (h v1 (M x v2) v1)) (C (S (h v2 x x)) (R (M v1 (M v1 v1))))) (S (h y y v1))

@[equational_result]
theorem Equation1966_implies_Equation19 (G: Type _) [Magma G] (h: Equation1966 G) : Equation19 G := fun x y z =>
  let v0 := M z x
  let v1 := M y v0
  have h2 := h v0 x y
  have h3 := C (S (h x y z)) (R v0)
  have h4 := h x v1 z
  T (T (T h4 h3) (C (T (T h4 h3) (C (R x) h2)) h2)) (S (h v1 x (M x v1)))

@[equational_result]
theorem Equation2708_implies_Equation2 (G: Type _) [Magma G] (h: Equation2708 G) : Equation2 G := fun x y =>
  let v0 := M y y
  let v1 := M x y
  let v2 := M v1 v1
  have h3 := R v0
  have h4 := h y x y
  have h5 := S (h y x x)
  T (T (T (h x v2 v0) (C (C h5 h5) h3)) (C (C h4 h4) h3)) (S (h y v2 v0))

@[equational_result]
theorem Equation4182_implies_Equation3553 (G: Type _) [Magma G] (h: Equation4182 G) : Equation3553 G := fun x y z =>
  have h0 := R x
  let v1 := M (M x x) x
  let v2 := M (M y z) z
  T (T (T (T (T (T (h x y z) (h v2 x x)) (C (C (h x x x) h0) (R v2))) (S (h v2 v1 x))) (S (h v1 y z))) (C (C (h x x z) h0) (R y))) (S (h y (M (M x z) z) x))

@[equational_result]
theorem Equation1695_implies_Equation2947 (G: Type _) [Magma G] (h: Equation1695 G) : Equation2947 G := fun x y =>
  let v0 := M y y
  let v1 := M y v0
  let v2 := M (M v1 v1) v1
  T (h x v1) (C (R (M v1 x)) (T (T (h v2 v0) (C (T (C (h v0 y) (R v2)) (S (h (M v0 y) v1))) (R (M (M v0 v0) v0)))) (S (h y v0))))

@[equational_result]
theorem Equation1932_implies_Equation680 (G: Type _) [Magma G] (h: Equation1932 G) : Equation680 G := fun x y =>
  let v0 := M y y
  let v1 := M v0 y
  let v2 := M v1 (M v1 v1)
  T (h x v1) (C (T (T (h v2 v0) (C (R (M v0 (M v0 v0))) (T (C (R v2) (h v0 y)) (S (h (M y v0) v1))))) (S (h y v0))) (R (M x v1)))

@[equational_result]
theorem Equation891_implies_Equation2 (G: Type _) [Magma G] (h: Equation891 G) : Equation2 G := fun x y =>
  let v0 := M y x
  let v1 := M v0 v0
  let v2 := M y y
  have h3 := h y y x
  have h4 := R v2
  have h5 := S (h y x x)
  T (T (T (h x v2 v1) (C h4 (C h5 h5))) (C h4 (C h3 h3))) (S (h y v2 v1))

@[equational_result]
theorem Equation1867_implies_Equation4067 (G: Type _) [Magma G] (h: Equation1867 G) : Equation4067 G := fun x y =>
  let v0 := M x x
  have h1 := R v0
  let v2 := M v0 y
  let v3 := M v2 x
  T (h v0 (M y (M v3 v2)) (M y y)) (C (C h1 (S (h y v3 v2))) (T (C (C (R x) (h x x x)) h1) (S (h x (M x v0) v0))))

@[equational_result]
theorem Equation3370_implies_Equation4026 (G: Type _) [Magma G] (h: Equation3370 G) : Equation4026 G := fun x y z =>
  let v0 := M z (M z y)
  let v1 := M v0 (M v0 x)
  T (T (T (T (T (h x y v0) (h y v1 y)) (h v1 (M y (M y y)) x)) (C (C (R y) (h y y z)) (C (R x) (S (h x x v0))))) (S (h x (M y (M y v0)) x))) (S (h v0 x y))

@[equational_result]
theorem Equation1711_implies_Equation2 (G: Type _) [Magma G] (h: Equation1711 G) : Equation2 G := fun x y =>
  let v0 := M (M x x) x
  let v1 := M y y
  let v2 := M y x
  T (T (T (T (T (h x y y) (C (h v2 y x) (R (M v1 y)))) (S (h v0 (M y v2) y))) (h v0 (M x v1) v0)) (C (S (h v1 x x)) (R (M (M v0 v0) v0)))) (S (h y y v0))

@[equational_result]
theorem Equation3607_implies_Equation4135 (G: Type _) [Magma G] (h: Equation3607 G) : Equation4135 G := fun x y z =>
  let v0 := M x y
  let v1 := M v0 z
  have h2 := h x y v1
  let v3 := M (M y v1) x
  T (T (T h2 (h v1 v3 v0)) (C (R v0) (C (T (h v3 v0 z) (C (R z) (S h2))) (R v1)))) (S (h v1 z v0))

@[equational_result]
theorem Equation3790_implies_Equation3533 (G: Type _) [Magma G] (h: Equation3790 G) : Equation3533 G := fun x y z =>
  let v0 := M z y
  have h1 := h y y y
  let v2 := M y y
  T (T (T (h x y y) (C (R (M y x)) h1)) (S (h x v2 y))) (C (R x) (T (T (T (h y y z) (h v0 v2 x)) (C (R (M x v0)) (S h1))) (S (h v0 y x))))

@[equational_result]
theorem Equation928_implies_Equation2474 (G: Type _) [Magma G] (h: Equation928 G) : Equation2474 G := fun x y z =>
  let v0 := M y y
  let v1 := M v0 z
  let v2 := M x v1
  have h3 := R x
  have h4 := S (h y x x)
  T (T (T (h x x (M (M x x) (M y x))) (C h3 (C h4 h4))) (C h3 (h v0 v2 z))) (S (h (M v2 z) x v1))

@[equational_result]
theorem Equation3155_implies_Equation5 (G: Type _) [Magma G] (h: Equation3155 G) : Equation5 G := fun x y =>
  let v0 := M y x
  let v1 := M (M v0 v0) v0
  let v2 := M (M (M x x) x) x
  have h3 := h v2 x x
  T (h x v0 y) (C (T (C (T (h v1 x x) (C (T h3 (C h3 (R v2))) (R v1))) (R y)) (S (h y v2 v1))) (R x))

@[equational_result]
theorem Equation3370_implies_Equation4146 (G: Type _) [Magma G] (h: Equation3370 G) : Equation4146 G := fun x y z =>
  let v0 := M x z
  have h1 := R y
  let v2 := M x (M x x)
  T (T (T (T (T (h x y x) (C h1 (C (R x) (h x x x)))) (S (h v2 y x))) (h v2 y z)) (C h1 (T (C (R z) (S (h x z x))) (h z v0 v0)))) (S (h (M v0 z) y v0))

@[equational_result]
theorem Equation1933_implies_Equation2 (G: Type _) [Magma G] (h: Equation1933 G) : Equation2 G := fun x y =>
  let v0 := M x (M x x)
  let v1 := M y y
  let v2 := M x y
  T (T (T (T (T (h x y y) (C (R (M y v1)) (h v2 x x))) (S (h v0 y (M v2 x)))) (h v0 v0 (M v1 y))) (C (R (M v0 (M v0 v0))) (S (h v1 x y)))) (S (h y v0 y))

@[equational_result]
theorem Equation2952_implies_Equation5 (G: Type _) [Magma G] (h: Equation2952 G) : Equation5 G := fun x y =>
  let v0 := M y x
  let v1 := M v0 (M v0 v0)
  let v2 := M (M x (M x x)) x
  have h3 := h v2 x x
  T (h x v0 y) (C (T (C (T (h v1 x x) (C (T h3 (C (R v2) h3)) (R v1))) (R y)) (S (h y v2 v1))) (R x))

@[equational_result]
theorem Equation3736_implies_Equation3525 (G: Type _) [Magma G] (h: Equation3736 G) : Equation3525 G := fun x y z =>
  let v0 := M y y
  have h1 := h y y y
  let v2 := M x y
  let v3 := M v2 v2
  T (T (T (h x y v3) (C (R (M x v3)) h1)) (S (h x v0 v3))) (C (R x) (T (T h1 (C (h y y z) (R v0))) (S (h (M y z) y v0))))

@[equational_result]
theorem Equation2554_implies_Equation246 (G: Type _) [Magma G] (h: Equation2554 G) : Equation246 G := fun x y z =>
  let v0 := M z z
  let v1 := M (M z x) z
  have h2 := C (R z) (h z z x)
  let v3 := M (M v0 y) v0
  T (h x v0 y) (C (T (T (C h2 (R v3)) (S (h v3 z v1))) (C (T (C h2 (R y)) (S (h y z v1))) (R v0))) (R x))

@[equational_result]
theorem Equation3417_implies_Equation3601 (G: Type _) [Magma G] (h: Equation3417 G) : Equation3601 G := fun x y z =>
  let v0 := M y x
  have h1 := R z
  have h2 := h x y v0
  have h3 := R v0
  T (T (T (T (T h2 (C h3 (T (h v0 v0 v0) (C h3 (S h2))))) (S (h y x v0))) (h y x z)) (C h1 (C h1 (h x y z)))) (C h1 (S (h v0 z z)))

@[equational_result]
theorem Equation4229_implies_Equation4497 (G: Type _) [Magma G] (h: Equation4229 G) : Equation4497 G := fun x y z =>
  let v0 := M z z
  let v1 := M v0 x
  let v2 := M y y
  let v3 := M v2 v2
  let v4 := M (M v1 v1) x
  T (T (T (T (T (h x v2 y) (h v3 x v1)) (h v4 v3 z)) (C (h v0 v3 v2) (R v4))) (S (h v4 v0 v3))) (S (h v0 x v1))

@[equational_result]
theorem Equation539_implies_Equation2 (G: Type _) [Magma G] (h: Equation539 G) : Equation2 G := fun x y =>
  let v0 := M x (M y (M y x))
  let v1 := M x (M v0 (M v0 x))
  have h2 := R v1
  T (T (T (h x v1 v1) (C h2 (C h2 (T (C (R x) (S (h v0 x x))) (S (h y x x)))))) (C h2 (C h2 (T (h y y x) (C (R y) (h v0 y x)))))) (S (h y v1 v1))

@[equational_result]
theorem Equation1543_implies_Equation981 (G: Type _) [Magma G] (h: Equation1543 G) : Equation981 G := fun x y z =>
  let v0 := M y x
  let v1 := M z z
  let v2 := M v1 v0
  let v3 := M y v2
  T (T (h x y y) (C (R (M y y)) (C (R y) (T (T (h v0 x v1) (C (R (M x x)) (C (R v1) (h v2 z y)))) (S (h (M y v3) x v1)))))) (S (h v3 y y))

@[equational_result]
theorem Equation2714_implies_Equation2538 (G: Type _) [Magma G] (h: Equation2714 G) : Equation2538 G := fun x y z =>
  have h0 := R z
  let v1 := M y x
  let v2 := M v1 z
  let v3 := M y v2
  have h4 := h x x v3
  T (h x x z) (C (T (C (C h4 h4) (T (C (h x y v2) h0) (S (h v3 v1 z)))) (S (h v3 (M (M x x) (M x v3)) v3))) h0)

@[equational_result]
theorem Equation3810_implies_Equation3823 (G: Type _) [Magma G] (h: Equation3810 G) : Equation3823 G := fun x y z =>
  let v0 := M z z
  let v1 := M y x
  let v2 := M v0 z
  have h3 := h z v1 v0
  T (T (h x y y) (h (M y y) v1 v1)) (C (T (T (T (h v1 v1 z) (C h3 h3)) (S (h v2 v2 (M v0 v1)))) (S (h z z v0))) (S (h y x y)))

@[equational_result]
theorem Equation556_implies_Equation1131 (G: Type _) [Magma G] (h: Equation556 G) : Equation1131 G := fun x y z =>
  let v0 := M z x
  let v1 := M y v0
  let v2 := M v1 z
  have h3 := R z
  have h4 := R y
  T (h x y z) (C h4 (T (T (C h3 (C h4 (T (C (R x) (h z v0 x)) (S (h v0 x v0))))) (C h3 (h v1 v2 z))) (S (h v2 z v2))))

@[equational_result]
theorem Equation962_implies_Equation546 (G: Type _) [Magma G] (h: Equation962 G) : Equation546 G := fun x y z =>
  let v0 := M z y
  let v1 := M x v0
  let v2 := M z v1
  let v3 := M y v2
  let v4 := M v3 v0
  T (h x y v0) (C (R y) (C (T (C (R v0) (T (h y v4 v2) (C (R v4) (C (S (h z v2 y)) (R v3))))) (S (h z v0 v3))) (R v1)))

@[equational_result]
theorem Equation1506_implies_Equation723 (G: Type _) [Magma G] (h: Equation1506 G) : Equation723 G := fun x y z =>
  let v0 := M z x
  let v1 := M v0 x
  let v2 := M y v1
  have h3 := R v2
  T (T (h x v0 v2) (C (h v1 z y) (T (C h3 (T (C h3 (h x z v0)) (S (h v1 y v0)))) (C h3 (h v1 y y))))) (S (h (M y v2) (M z v1) v2))

@[equational_result]
theorem Equation1528_implies_Equation919 (G: Type _) [Magma G] (h: Equation1528 G) : Equation919 G := fun x y =>
  let v0 := M y x
  let v1 := M y y
  let v2 := M v1 v0
  let v3 := M y v2
  have h4 := R v1
  T (T (h x y) (C h4 (C (R y) (T (T (h v0 v1) (C (R (M v1 v1)) (C h4 (h v2 y)))) (S (h (M y v3) v1)))))) (S (h v3 y))

@[equational_result]
theorem Equation2062_implies_Equation2860 (G: Type _) [Magma G] (h: Equation2062 G) : Equation2860 G := fun x y z =>
  let v0 := M x y
  let v1 := M x v0
  let v2 := M v1 z
  have h3 := R v2
  have h4 := T (T (C (h x v0 y) h3) (S (h v1 v0 z))) (h v1 z z)
  T (T (h x v2 v2) (C (C h4 h3) h4)) (S (h (M v2 z) v2 v2))

@[equational_result]
theorem Equation1588_implies_Equation2 (G: Type _) [Magma G] (h: Equation1588 G) : Equation2 G := fun x y =>
  have h0 := S (h y x y)
  let v1 := M y y
  let v2 := M y v1
  have h3 := R v2
  let v4 := M x y
  T (T (h x x y) (C (R v4) (C (R y) (T (h v4 v4 v2) (C h0 (T (T (C h3 h0) (C h3 (h y y y))) (S (h y y v1)))))))) h0

@[equational_result]
theorem Equation2770_implies_Equation218 (G: Type _) [Magma G] (h: Equation2770 G) : Equation218 G := fun x y =>
  let v0 := M x x
  have h1 := h x v0 (M v0 v0)
  have h2 := R x
  have h3 := h v0 x x
  have h4 := T (C h3 h2) (S h1)
  T (T (T h1 (C (S h3) h2)) (h (M v0 x) (M v0 (M y y)) y)) (C (C (S (h y x x)) (C h4 h4)) h4)

@[equational_result]
theorem Equation3107_implies_Equation2 (G: Type _) [Magma G] (h: Equation3107 G) : Equation2 G := fun x y =>
  let v0 := M (M (M x x) x) x
  let v1 := M (M (M x v0) v0) x
  have h2 := R v1
  T (T (T (h x v1 v1) (C (C (T (C (S (h v0 x x)) (R x)) (S (h x x x))) h2) h2)) (C (C (T (h x x y) (C (h v0 x y) (R y))) h2) h2)) (S (h y v1 v1))

@[equational_result]
theorem Equation928_implies_Equation2538 (G: Type _) [Magma G] (h: Equation928 G) : Equation2538 G := fun x y z =>
  let v0 := M y x
  let v1 := M v0 z
  let v2 := M y v1
  have h3 := h x v0 x
  T (T (h x y x) (C (R y) (T (T (C (R v0) (C h3 h3)) (S (h v0 v0 (M (M v0 x) (M x x))))) (h v0 v2 z)))) (S (h (M v2 z) y v1))

@[equational_result]
theorem Equation1527_implies_Equation2 (G: Type _) [Magma G] (h: Equation1527 G) : Equation2 G := fun x y =>
  let v0 := M y x
  let v1 := M x (M v0 x)
  let v2 := M x x
  have h3 := R x
  have h4 := R v2
  T (T (h x x v1) (C h4 (C h3 (T (C (T (T (h x x x) (C h4 (C h3 (h v2 x x)))) (S (h v2 x (M x (M v2 x))))) (R v1)) (S (h v0 x x)))))) (S (h y x x))

@[equational_result]
theorem Equation1725_implies_Equation2 (G: Type _) [Magma G] (h: Equation1725 G) : Equation2 G := fun x y =>
  have h0 := R x
  let v1 := M y x
  let v2 := M (M v1 x) x
  let v3 := M x x
  have h4 := R v3
  T (T (h x x v2) (C h4 (C (T (C (T (T (h x x x) (C h4 (C (h v3 x x) h0))) (S (h v3 x (M (M v3 x) x)))) (R v2)) (S (h v1 x x))) h0))) (S (h y x x))

@[equational_result]
theorem Equation1963_implies_Equation2 (G: Type _) [Magma G] (h: Equation1963 G) : Equation2 G := fun x y =>
  let v0 := M x x
  have h1 := R v0
  let v2 := M x y
  have h3 := R x
  let v4 := M x (M x v2)
  T (T (h x x v4) (C (C h3 (T (C (R v4) (T (T (h x x x) (C (C h3 (h v0 x y)) h1)) (S (h v0 x (M x (M y v0)))))) (S (h v2 x x)))) h1)) (S (h y x x))

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
theorem Equation1774_implies_Equation3810 (G: Type _) [Magma G] (h: Equation1774 G) : Equation3810 G := fun x y z =>
  let v0 := M z x
  let v1 := M (M z y) v0
  let v2 := M z v1
  let v3 := M v0 v1
  T (T (h (M x y) v0 v1) (C (R v3) (C (T (C (T (h v0 z v1) (C (R v2) (S (h y z v0)))) (C (h x z v1) (R y))) (S (h v3 v2 y))) (R v1)))) (S (h v1 v0 v1))

@[equational_result]
theorem Equation2117_implies_Equation2 (G: Type _) [Magma G] (h: Equation2117 G) : Equation2 G := fun x y =>
  let v0 := M x x
  have h1 := R v0
  have h2 := R x
  let v3 := M x y
  let v4 := M (M x v3) x
  T (T (h x v4 x) (C (C (T (C (R v4) (T (T (h x x x) (C (C (h v0 x x) h2) h1)) (S (h v0 (M (M x v0) x) x)))) (S (h v3 x x))) h2) h1)) (S (h y x x))

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
