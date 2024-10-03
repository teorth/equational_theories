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
theorem Equation3791_implies_Equation43 (G: Type _) [Magma G] (h: Equation3791 G) : Equation43 G := fun x y =>
  have h0 := h y x x
  let v1 := M x x
  let v2 := M x y
  have h3 := h x y x
  T (T (T (T (T h3 (C (h x x x) h0)) (S (h v1 v2 v1))) (C (h x x y) h3)) (S (h v2 v1 (M y x)))) (S h0)

@[equational_result]
theorem Equation3791_implies_Equation3537 (G: Type _) [Magma G] (h: Equation3791 G) : Equation3537 G := fun x y z =>
  let v0 := M z z
  let v1 := M v0 y
  let v2 := M v0 x
  T (T (T (h x y v0) (C (R v2) (T (h y v0 v0) (C (R v1) (S (h z z z)))))) (R (M v2 (M v1 v0)))) (S (h x v1 v0))

@[equational_result]
theorem Equation4162_implies_Equation3601 (G: Type _) [Magma G] (h: Equation4162 G) : Equation3601 G := fun x y z =>
  let v0 := M y x
  have h1 := R v0
  have h2 := h x y v0
  T (T (T h2 (C (T (h v0 v0 v0) (C (S h2) h1)) h1)) (C (C (h x y z) h1) h1)) (S (h z (M v0 z) v0))

@[equational_result]
theorem Equation1293_implies_Equation3131 (G: Type _) [Magma G] (h: Equation1293 G) : Equation3131 G := fun x y z =>
  have h0 := S (h y y x)
  let v1 := M (M (M y y) x) x
  have h2 := R v1
  let v3 := M (M (M y x) z) z
  T (h x v3 v1) (C (R v3) (T (C (T (C (S (h y x z)) h2) h0) h2) h0))

@[equational_result]
theorem Equation1507_implies_Equation4413 (G: Type _) [Magma G] (h: Equation1507 G) : Equation4413 G := fun x y z =>
  let v0 := M x y
  let v1 := M x v0
  let v2 := M v1 x
  let v3 := M y z
  T (C (T (h x v1 v3) (C (R v2) (C (R v3) (S (h z y x))))) (h v0 x v1)) (S (h (M v3 z) v2 v1))

@[equational_result]
theorem Equation1943_implies_Equation684 (G: Type _) [Magma G] (h: Equation1943 G) : Equation684 G := fun x y z =>
  let v0 := M y z
  let v1 := M v0 z
  let v2 := M z (M z z)
  T (h x y v1) (C (T (C (T (h y z z) (C (R v2) (h v0 z z))) (R (M y v1))) (S (h y v2 v1))) (R (M x v1)))

@[equational_result]
theorem Equation2942_implies_Equation5 (G: Type _) [Magma G] (h: Equation2942 G) : Equation5 G := fun x y =>
  let v0 := M y x
  let v1 := M (M x (M x y)) y
  have h2 := h y x y
  T (h x y y) (C (T (C (C (T h2 (C (R v1) h2)) (R v0)) (R y)) (S (h y v1 v0))) (R x))

@[equational_result]
theorem Equation3350_implies_Equation3323 (G: Type _) [Magma G] (h: Equation3350 G) : Equation3323 G := fun x y z =>
  let v0 := M z z
  let v1 := M y v0
  let v2 := M x (M x x)
  T (T (T (T (h x y x) (h y v2 z)) (C (R v2) (T (h y v0 z) (h v0 v1 z)))) (S (h v1 v2 v0))) (S (h x v1 x))

@[equational_result]
theorem Equation3398_implies_Equation4369 (G: Type _) [Magma G] (h: Equation3398 G) : Equation4369 G := fun x y z =>
  let v0 := M y x
  let v1 := M z v0
  let v2 := M y z
  T (T (h x v2 v1) (C (R v1) (T (T (C (R v2) (T (S (h y z x)) (h y z z))) (S (h z z v2))) (h z z v0)))) (S (h z v0 v1))

@[equational_result]
theorem Equation3567_implies_Equation3534 (G: Type _) [Magma G] (h: Equation3567 G) : Equation3534 G := fun x y z =>
  let v0 := M (M z y) z
  let v1 := M x y
  let v2 := M (M v1 x) v1
  T (T (T (T (h x y v1) (h y v2 z)) (h v2 v0 x)) (C (R v0) (C (S (h x x v1)) (R x)))) (S (h x v0 x))

@[equational_result]
theorem Equation4176_implies_Equation3591 (G: Type _) [Magma G] (h: Equation4176 G) : Equation3591 G := fun x y z =>
  let v0 := M x z
  have h1 := R v0
  let v2 := M y v0
  T (T (h x y v0) (C (T (h v2 x z) (C (T (h v0 v2 v0) (C (S (h v0 y v0)) h1)) (R z))) h1)) (S (h z (M v0 y) v0))

@[equational_result]
theorem Equation492_implies_Equation2349 (G: Type _) [Magma G] (h: Equation492 G) : Equation2349 G := fun x y z =>
  let v0 := M z x
  let v1 := M y (M y v0)
  let v2 := M v1 z
  T (T (h x v0 z) (C (R v0) (T (T (S (h z x z)) (h z v2 v1)) (C (R v2) (S (h v1 z v1)))))) (S (h v2 v0 y))

@[equational_result]
theorem Equation1492_implies_Equation2128 (G: Type _) [Magma G] (h: Equation1492 G) : Equation2128 G := fun x y =>
  let v0 := M y y
  let v1 := M y v0
  let v2 := M v0 (M v0 v0)
  T (h x v0) (C (R (M v0 x)) (T (T (h v2 y) (C (T (C (h y y) (R v2)) (S (h v1 v0))) (R v1))) (S (h v0 y))))

@[equational_result]
theorem Equation1640_implies_Equation3258 (G: Type _) [Magma G] (h: Equation1640 G) : Equation3258 G := fun x y =>
  let v0 := M x x
  have h1 := R v0
  let v2 := M v0 x
  T (h v0 (M y y) (M v2 y)) (C (T (C h1 (C (h x x x) (R x))) (S (h x v0 v2))) (C (S (h y v0 x)) h1))

@[equational_result]
theorem Equation1699_implies_Equation2958 (G: Type _) [Magma G] (h: Equation1699 G) : Equation2958 G := fun x y z =>
  let v0 := M y z
  let v1 := M y v0
  let v2 := M v1 x
  let v3 := M v2 z
  let v4 := M (M y v3) v3
  T (h x v1 v4) (C (R v2) (T (C (S (h v0 y v3)) (R v4)) (S (h z y v3))))

@[equational_result]
theorem Equation1764_implies_Equation2776 (G: Type _) [Magma G] (h: Equation1764 G) : Equation2776 G := fun x y z =>
  let v0 := M x y
  let v1 := M (M y z) v0
  let v2 := M v1 z
  T (T (h x v1 y) (C (R (M v1 y)) (C (T (h v0 v1 z) (C (R v2) (S (h y v0 z)))) (R v1)))) (S (h v2 v1 y))

@[equational_result]
theorem Equation2339_implies_Equation2 (G: Type _) [Magma G] (h: Equation2339 G) : Equation2 G := fun x y =>
  let v0 := M x y
  let v1 := M x (M x (M x x))
  have h2 := R v1
  T (T (h x v1 v0) (C (C h2 (T (C h2 (S (h x x x))) (C h2 (h x x y)))) (R v0))) (S (h y v1 v0))

@[equational_result]
theorem Equation2776_implies_Equation1913 (G: Type _) [Magma G] (h: Equation2776 G) : Equation1913 G := fun x y z =>
  let v0 := M x z
  have h1 := h x y x
  T (T h1 (C (T (h (M (M y x) (M x y)) x z) (C (C (R v0) (S h1)) (h z y v0))) (R x))) (S (h (M (M y v0) (M z y)) v0 x))

@[equational_result]
theorem Equation2779_implies_Equation1910 (G: Type _) [Magma G] (h: Equation2779 G) : Equation1910 G := fun x y z =>
  let v0 := M y z
  let v1 := M x z
  have h2 := h x v0 z
  T h2 (C (T (h (M (M v0 z) v1) v1 v0) (C (T (C (R (M v1 v0)) (S h2)) (S (h y x z))) (R v1))) (R v0))

@[equational_result]
theorem Equation3735_implies_Equation327 (G: Type _) [Magma G] (h: Equation3735 G) : Equation327 G := fun x y z =>
  let v0 := M y z
  let v1 := M x v0
  T (T (T (h x y v0) (h v1 (M y x) (M v1 x))) (C (S (h x v1 v0)) (T (C (h y x z) (R v1)) (S (h v0 x (M x y)))))) (S (h x v0 v1))

@[equational_result]
theorem Equation3776_implies_Equation4200 (G: Type _) [Magma G] (h: Equation3776 G) : Equation4200 G := fun x y z =>
  let v0 := M x y
  let v1 := M z x
  let v2 := M v1 z
  T (T (h x y v0) (C (R (M y v0)) (T (T (h v0 x v1) (C (h x v1 z) (R (M v1 v0)))) (S (h v0 v2 v1))))) (S (h v2 y v0))

@[equational_result]
theorem Equation3785_implies_Equation41 (G: Type _) [Magma G] (h: Equation3785 G) : Equation41 G := fun x y z =>
  have h0 := h y z x
  have h1 := h x x x
  let v2 := M y z
  let v3 := M x x
  T (T (T (T h1 (h v3 v3 v2)) (S (h v3 v2 v2))) (C (T h1 (S (h x y x))) (T h0 (S (h y y x))))) (S h0)

@[equational_result]
theorem Equation3791_implies_Equation4491 (G: Type _) [Magma G] (h: Equation3791 G) : Equation4491 G := fun x y z =>
  let v0 := M y y
  let v1 := M z x
  let v2 := M v0 z
  T (T (T (h x v0 z) (h v1 v2 v0)) (C (R (M v0 v1)) (T (C (R v2) (h y y y)) (S (h z v0 v0))))) (S (h v1 z v0))

@[equational_result]
theorem Equation3979_implies_Equation3943 (G: Type _) [Magma G] (h: Equation3979 G) : Equation3943 G := fun x y z =>
  let v0 := M z z
  let v1 := M x v0
  let v2 := M y (M x x)
  T (T (T (T (h x y x) (h v2 x z)) (C (T (h x v0 z) (h (M v0 v0) x z)) (R v2))) (S (h v2 v1 v0))) (S (h v1 y x))

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
theorem Equation914_implies_Equation508 (G: Type _) [Magma G] (h: Equation914 G) : Equation508 G := fun x y z =>
  let v0 := M z z
  let v1 := M y (M x v0)
  have h2 := h x y v1
  have h3 := R y
  T h2 (C h3 (T (h (M (M y x) (M v1 v1)) y z) (C h3 (C (S h2) (R v0)))))

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
theorem Equation1967_implies_Equation949 (G: Type _) [Magma G] (h: Equation1967 G) : Equation949 G := fun x y z =>
  let v0 := M z x
  let v1 := M v0 (M y z)
  let v2 := M y v1
  T (T (h x v1 z) (C (C (R v1) (T (h v0 v1 y) (C (S (h z v0 y)) (R v2)))) (R (M z v1)))) (S (h v2 v1 z))

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
theorem Equation3398_implies_Equation4023 (G: Type _) [Magma G] (h: Equation3398 G) : Equation4023 G := fun x y z =>
  let v0 := M z x
  let v1 := M v0 y
  let v2 := M z v0
  T (T (h x y v1) (C (R v1) (T (T (T (S (h v0 x y)) (h v0 x v0)) (C (R v0) (S (h z v0 x)))) (h v0 v2 y)))) (S (h v2 y v1))

@[equational_result]
theorem Equation3404_implies_Equation3940 (G: Type _) [Magma G] (h: Equation3404 G) : Equation3940 G := fun x y z =>
  let v0 := M z y
  have h1 := R v0
  let v2 := M v0 x
  T (T (h x y v0) (C h1 (T (h y v2 z) (C (R z) (T (h v2 v0 v0) (C h1 (S (h x v0 v0)))))))) (S (h (M x v0) z v0))

@[equational_result]
theorem Equation3573_implies_Equation3537 (G: Type _) [Magma G] (h: Equation3573 G) : Equation3537 G := fun x y z =>
  let v0 := M z z
  let v1 := M v0 y
  let v2 := M (M x x) x
  T (T (T (T (h x y x) (h y v2 z)) (C (R v2) (T (h v0 y z) (h y (M v0 v0) z)))) (S (h v1 v2 v0))) (S (h x v1 x))

@[equational_result]
theorem Equation3776_implies_Equation4684 (G: Type _) [Magma G] (h: Equation3776 G) : Equation4684 G := fun x y z =>
  let v0 := M z y
  let v1 := M x y
  let v2 := M y v1
  T (T (T (h v1 z y) (h v0 v2 z)) (C (T (T (h v2 z v1) (C (R (M z v1)) (S (h v1 x y)))) (S (h x z v1))) (R (M z v0)))) (S (h v0 x z))

@[equational_result]
theorem Equation3804_implies_Equation4541 (G: Type _) [Magma G] (h: Equation3804 G) : Equation4541 G := fun x y z =>
  let v0 := M y z
  let v1 := M z x
  let v2 := M x v0
  T (T (T (h x v0 y) (C (T (h y v0 x) (C (R v2) (h y x z))) (h x y v0))) (S (h (M v0 y) (M v1 v0) v2))) (S (h v1 y v0))

@[equational_result]
theorem Equation3810_implies_Equation3895 (G: Type _) [Magma G] (h: Equation3810 G) : Equation3895 G := fun x y z =>
  let v0 := M y z
  let v1 := M v0 z
  have h2 := h z x v0
  T (T (T (T (h x x z) (C h2 h2)) (S (h v1 v1 (M v0 x)))) (C (R v1) (h v0 z y))) (S (h (M y v0) z v0))

@[equational_result]
theorem Equation4026_implies_Equation4023 (G: Type _) [Magma G] (h: Equation4026 G) : Equation4023 G := fun x y z =>
  let v0 := M z (M z x)
  let v1 := M v0 y
  let v2 := M v1 (M v1 y)
  T (T (T (T (h x y v1) (h v2 x v0)) (C (C (R v0) (h v0 x z)) (R v2))) (S (h v2 v0 v0))) (S (h v0 y v1))

@[equational_result]
theorem Equation546_implies_Equation562 (G: Type _) [Magma G] (h: Equation546 G) : Equation562 G := fun x y z =>
  let v0 := M z x
  let v1 := M y v0
  have h2 := R z
  T (h x y z) (C (R y) (C h2 (T (C (R x) (C h2 (T (h y v1 v0) (C (R v1) (S (h v0 v0 y)))))) (S (h v1 x z)))))

@[equational_result]
theorem Equation952_implies_Equation1774 (G: Type _) [Magma G] (h: Equation952 G) : Equation1774 G := fun x y z =>
  let v0 := M y x
  let v1 := M y z
  have h2 := h x v1 v1
  T h2 (C (R v1) (T (h (M (M v1 x) (M v1 v1)) v0 v1) (C (R v0) (T (C (S h2) (R (M v1 v0))) (S (h z x y))))))

@[equational_result]
theorem Equation1090_implies_Equation1117 (G: Type _) [Magma G] (h: Equation1090 G) : Equation1117 G := fun x y z =>
  let v0 := M (M y (M x z)) z
  have h1 := S (h v0 y x)
  let v2 := M (M v0 (M y x)) x
  T (h x y v2) (C (R y) (T (C (T (C (R x) h1) (S (h y x z))) (R v2)) h1))

@[equational_result]
theorem Equation1571_implies_Equation2076 (G: Type _) [Magma G] (h: Equation1571 G) : Equation2076 G := fun x y z =>
  let v0 := M y z
  let v1 := M x y
  let v2 := M v1 z
  let v3 := M v2 v0
  T (T (h x v0 y) (C (R (M v0 y)) (C (R v0) (T (h v1 v2 v0) (C (R v3) (S (h y v1 z))))))) (S (h v3 v0 y))

@[equational_result]
theorem Equation2349_implies_Equation572 (G: Type _) [Magma G] (h: Equation2349 G) : Equation572 G := fun x y z =>
  let v0 := M z (M z (M x y))
  have h1 := S (h y x y)
  let v2 := M x (M x (M y y))
  have h3 := R v2
  T (h x v2 v0) (C (T (C h3 (T (C h3 (S (h y z x))) h1)) h1) (R v0))

@[equational_result]
theorem Equation2552_implies_Equation2538 (G: Type _) [Magma G] (h: Equation2552 G) : Equation2538 G := fun x y z =>
  let v0 := M y (M (M y x) z)
  have h1 := S (h v0 x z)
  let v2 := M x (M (M x z) v0)
  T (h x v2 z) (C (T (C (R v2) (T (C h1 (R x)) (S (h z y x)))) h1) (R z))

@[equational_result]
theorem Equation2714_implies_Equation2558 (G: Type _) [Magma G] (h: Equation2714 G) : Equation2558 G := fun x y z =>
  let v0 := M y z
  let v1 := M v0 z
  have h2 := S (h z x x)
  T (h x (M (M x z) (M x x)) x) (C (T (T (C h2 h2) (C (h z y v1) (R z))) (S (h (M y v1) v0 z))) (R x))

@[equational_result]
theorem Equation3128_implies_Equation2928 (G: Type _) [Magma G] (h: Equation3128 G) : Equation2928 G := fun x y z =>
  have h0 := R y
  let v1 := M x z
  let v2 := M y v1
  T (h x z y) (C (C (T (C (T (T (C (h z x v1) (R x)) (S (h v1 v1 x))) (h v1 y v2)) h0) (S (h v2 v2 y))) (R z)) h0)

@[equational_result]
theorem Equation3185_implies_Equation1913 (G: Type _) [Magma G] (h: Equation3185 G) : Equation1913 G := fun x y z =>
  let v0 := M z y
  let v1 := M x z
  have h2 := R v1
  T (h x v0 v1) (C (C (T (C (C (C (T (h z v1 x) (C (S (h x x z)) h2)) (R y)) h2) (R x)) (S (h y x v1))) h2) (R v0))

@[equational_result]
theorem Equation3211_implies_Equation1293 (G: Type _) [Magma G] (h: Equation3211 G) : Equation1293 G := fun x y z =>
  let v0 := M x y
  let v1 := M (M v0 z) z
  let v2 := M y v1
  T (T (h x v0 y) (C (T (T (S (h y x y)) (h y v2 v1)) (C (S (h v1 y v1)) (R v2))) (R v0))) (S (h v2 v0 z))

@[equational_result]
theorem Equation3553_implies_Equation3526 (G: Type _) [Magma G] (h: Equation3553 G) : Equation3526 G := fun x y z =>
  let v0 := M (M y z) z
  let v1 := M x v0
  let v2 := M (M x v1) v1
  T (T (T (T (h x y v1) (h y v2 v0)) (C (R v2) (C (h y v0 z) (R v0)))) (S (h v0 v2 v0))) (S (h x v0 v1))

@[equational_result]
theorem Equation3735_implies_Equation381 (G: Type _) [Magma G] (h: Equation3735 G) : Equation381 G := fun x y z =>
  let v0 := M y x
  let v1 := M x z
  let v2 := M y v1
  have h3 := h x y y
  T (T (T (T h3 (C h3 (h y x v1))) (S (h (M x y) v2 v0))) (C (h x y z) (R v2))) (S (h v1 y v0))

@[equational_result]
theorem Equation3804_implies_Equation4512 (G: Type _) [Magma G] (h: Equation3804 G) : Equation4512 G := fun x y z =>
  let v0 := M x y
  let v1 := M y z
  let v2 := M x v1
  T (T (T (h x v1 v0) (C (h v0 v1 x) (T (h x v0 v1) (C (S (h x z y)) (R v2))))) (S (h (M x z) (M v0 x) v2))) (S (h v0 z x))

@[equational_result]
theorem Equation4013_implies_Equation3997 (G: Type _) [Magma G] (h: Equation4013 G) : Equation3997 G := fun x y z =>
  let v0 := M z (M x z)
  let v1 := M x y
  let v2 := M v1 (M y v1)
  T (T (T (T (h x y v1) (h v2 x z)) (h v0 v2 y)) (C (C (R y) (S (h y y v1))) (R v0))) (S (h v0 y y))

@[equational_result]
theorem Equation711_implies_Equation26 (G: Type _) [Magma G] (h: Equation711 G) : Equation26 G := fun x y =>
  let v0 := M (M x y) y
  let v1 := M v0 (M (M v0 x) x)
  have h2 := h v0 v0 x
  have h3 := R x
  T (T (h x x y) (C h3 (C h3 (T h2 (C h2 (R v1)))))) (S (h v0 x v1))

@[equational_result]
theorem Equation928_implies_Equation1053 (G: Type _) [Magma G] (h: Equation928 G) : Equation1053 G := fun x y z =>
  let v0 := M y z
  let v1 := M y v0
  have h2 := S (h y x x)
  T (h x x (M (M x x) (M y x))) (C (R x) (T (T (C h2 h2) (C (R y) (h y v1 z))) (S (h (M v1 z) y v0))))

@[equational_result]
theorem Equation1740_implies_Equation11 (G: Type _) [Magma G] (h: Equation1740 G) : Equation11 G := fun x y =>
  let v0 := M y y
  let v1 := M x v0
  have h2 := R (M v1 v1)
  T (T (h x v1 v1) (C h2 (T (h (M (M v1 x) v1) v1 v0) (C h2 (C (S (h x y v1)) (R v0)))))) (S (h v1 v1 v1))

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
theorem Equation3364_implies_Equation4023 (G: Type _) [Magma G] (h: Equation3364 G) : Equation4023 G := fun x y z =>
  let v0 := M z x
  let v1 := M z v0
  have h2 := R v1
  T (T (h x y v1) (C (R y) (T (C h2 (T (h x v1 v0) (C h2 (S (h z v0 x))))) (R (M v1 (M v1 v1)))))) (S (h v1 y v1))

@[equational_result]
theorem Equation3770_implies_Equation3617 (G: Type _) [Magma G] (h: Equation3770 G) : Equation3617 G := fun x y z =>
  let v0 := M z x
  let v1 := M v0 y
  T (T (T (T (T (h x y y) (h (M y y) (M x y) v1)) (C (S (h v0 x y)) (S (h v0 y y)))) (h (M v0 x) v1 v0)) (C (R (M v1 v0)) (S (h z v0 x)))) (S (h z v1 v0))

@[equational_result]
theorem Equation3791_implies_Equation3943 (G: Type _) [Magma G] (h: Equation3791 G) : Equation3943 G := fun x y z =>
  let v0 := M z z
  let v1 := M x v0
  let v2 := M y v0
  T (T (T (h x y v0) (R (M (M v0 x) v2))) (C (T (h v0 x v0) (C (S (h z z z)) (R v1))) (R v2))) (S (h v1 y v0))

@[equational_result]
theorem Equation3804_implies_Equation3943 (G: Type _) [Magma G] (h: Equation3804 G) : Equation3943 G := fun x y z =>
  let v0 := M z z
  let v1 := M x v0
  have h2 := R v1
  T (T (h x y v1) (C (R (M v1 y)) (T (h x v1 v0) (C (T (C (h z z z) h2) (S (h x v0 v0))) h2)))) (S (h v1 y v1))

@[equational_result]
theorem Equation3998_implies_Equation41 (G: Type _) [Magma G] (h: Equation3998 G) : Equation41 G := fun x y z =>
  have h0 := R z
  have h1 := R (M z (M x z))
  T (T (T (h x x z) (C h1 h0)) (C (T (T (T h1 (C h0 (T (h x z x) (S (h x x x))))) (h z (M x x) x)) (S (h z (M y z) x))) h0)) (S (h y z z))

@[equational_result]
theorem Equation4013_implies_Equation3331 (G: Type _) [Magma G] (h: Equation4013 G) : Equation3331 G := fun x y z =>
  let v0 := M y z
  let v1 := M z v0
  T (T (h x y v0) (C (C (R v0) (T (T (h y v0 v1) (C (T (S (h (M v0 v1) y z)) (S (h y z v0))) (R y))) (h v0 y z))) (R x))) (S (h x v1 v0))

@[equational_result]
theorem Equation4210_implies_Equation3526 (G: Type _) [Magma G] (h: Equation4210 G) : Equation3526 G := fun x y z =>
  let v0 := M y z
  let v1 := M x v0
  let v2 := M v0 z
  T (T (h x y v1) (C (T (T (T (S (h y v0 x)) (h y v0 v0)) (C (S (h v0 z y)) (R v0))) (h v2 v0 x)) (R v1))) (S (h x v2 v1))

@[equational_result]
theorem Equation4216_implies_Equation3526 (G: Type _) [Magma G] (h: Equation4216 G) : Equation3526 G := fun x y z =>
  let v0 := M y z
  let v1 := M v0 z
  have h2 := R v1
  T (T (h x y v1) (C (T (R (M (M v1 y) v1)) (C (T (h v1 y v0) (C (S (h v0 z y)) h2)) h2)) (R x))) (S (h x v1 v1))

@[equational_result]
theorem Equation1304_implies_Equation26 (G: Type _) [Magma G] (h: Equation1304 G) : Equation26 G := fun x y =>
  let v0 := M (M x y) y
  let v1 := M (M (M v0 x) x) v0
  have h2 := R x
  have h3 := h v0 v0 x
  T (T (h x x y) (C h2 (C (T h3 (C h3 (R v1))) h2))) (S (h v0 x v1))

@[equational_result]
theorem Equation2399_implies_Equation16 (G: Type _) [Magma G] (h: Equation2399 G) : Equation16 G := fun x y =>
  let v0 := M y (M y x)
  let v1 := M v0 (M x (M x v0))
  have h2 := R x
  have h3 := h v0 v0 x
  T (T (h x x y) (C (C h2 (T h3 (C (R v1) h3))) h2)) (S (h v0 x v1))

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
theorem Equation3979_implies_Equation4497 (G: Type _) [Magma G] (h: Equation3979 G) : Equation4497 G := fun x y z =>
  let v0 := M z z
  let v1 := M y y
  let v2 := M x v1
  let v3 := M v1 v1
  T (T (T (T (T (h x v1 y) (h v3 x y)) (h v2 v3 z)) (C (S (h v0 v1 y)) (R v2))) (S (h v2 v0 y))) (S (h v0 x y))

@[equational_result]
theorem Equation3988_implies_Equation41 (G: Type _) [Magma G] (h: Equation3988 G) : Equation41 G := fun x y z =>
  have h0 := h y z x
  let v1 := M y z
  T (T (T (T (T (h x x y) (C (T (h y (M x x) x) (S h0)) (R x))) (h v1 x y)) (S (h v1 y y))) (C (T h0 (S (h y (M y y) x))) (R y))) (S (h y z y))

@[equational_result]
theorem Equation4229_implies_Equation3943 (G: Type _) [Magma G] (h: Equation4229 G) : Equation3943 G := fun x y z =>
  let v0 := M z z
  let v1 := M x v0
  let v2 := M v0 y
  T (T (T (T (h x y z) (h v2 x z)) (C (T (T (h v0 x v0) (C (S (h x v0 z)) (R v0))) (h v1 v0 z)) (R v2))) (S (h v2 v1 v0))) (S (h v1 y z))

@[equational_result]
theorem Equation684_implies_Equation2522 (G: Type _) [Magma G] (h: Equation684 G) : Equation2522 G := fun x y z =>
  let v0 := M y (M (M x z) z)
  have h1 := S (h v0 v0 v0)
  let v2 := M v0 (M (M v0 v0) v0)
  T (h x v0 v2) (C (R v0) (T (C (R x) (T (C h1 (R v2)) h1)) (S (h y x z))))

@[equational_result]
theorem Equation1304_implies_Equation3211 (G: Type _) [Magma G] (h: Equation1304 G) : Equation3211 G := fun x y z =>
  let v0 := M (M (M y z) z) x
  have h1 := R v0
  have h2 := S (h x x x)
  let v3 := M (M (M x x) x) x
  T (h x v0 v3) (C h1 (T (C (T (C h2 (R v3)) h2) h1) (S (h y x z))))

@[equational_result]
theorem Equation1305_implies_Equation2 (G: Type _) [Magma G] (h: Equation1305 G) : Equation2 G := fun x y =>
  let v0 := M (M (M y x) x) x
  have h1 := R v0
  have h2 := h y y x
  T (T (h x y v0) (C (R y) (T (C (T (C (S (h y x x)) h1) (S h2)) h1) (C (T h2 (C h2 h1)) h1)))) (S (h y y v0))

@[equational_result]
theorem Equation1504_implies_Equation4458 (G: Type _) [Magma G] (h: Equation1504 G) : Equation4458 G := fun x y z =>
  let v0 := M y x
  let v1 := M z y
  let v2 := M v1 z
  T (C (T (h x y v1) (C (R v0) (T (T (S (h y z y)) (h y z v2)) (C (R v1) (S (h z v1 z)))))) (h v0 v1 v0)) (S (h v2 v0 (M v1 v0)))

@[equational_result]
theorem Equation1561_implies_Equation43 (G: Type _) [Magma G] (h: Equation1561 G) : Equation43 G := fun x y =>
  let v0 := M y x
  let v1 := M x y
  have h2 := h v1 y x
  let v3 := M v1 v1
  T (T h2 (C (R v0) (T (h v3 v3 v1) (C (T (C (R v3) h2) (S (h v0 v1 v1))) (S (h v1 v1 v1)))))) (S (h v0 y x))

@[equational_result]
theorem Equation2180_implies_Equation4458 (G: Type _) [Magma G] (h: Equation2180 G) : Equation4458 G := fun x y z =>
  let v0 := M y x
  let v1 := M z y
  let v2 := M x v0
  T (h v2 (M v1 v0) v1) (C (S (h v1 v1 v0)) (T (C (T (T (C (h x x v0) (R v0)) (S (h y v2 x))) (h y y x)) (R v1)) (S (h z v0 y))))

@[equational_result]
theorem Equation2399_implies_Equation492 (G: Type _) [Magma G] (h: Equation2399 G) : Equation492 G := fun x y z =>
  let v0 := M x (M z (M z y))
  have h1 := R v0
  have h2 := S (h x x x)
  let v3 := M x (M x (M x x))
  T (h x v0 v3) (C (T (C h1 (T (C (R v3) h2) h2)) (S (h y x z))) h1)

@[equational_result]
theorem Equation2944_implies_Equation16 (G: Type _) [Magma G] (h: Equation2944 G) : Equation16 G := fun x y =>
  let v0 := M y (M y x)
  let v1 := M (M x (M x v0)) v0
  have h2 := R x
  have h3 := h v0 x v0
  T (T (h x y x) (C (C (T h3 (C (R v1) h3)) h2) h2)) (S (h v0 v1 x))

@[equational_result]
theorem Equation3573_implies_Equation3350 (G: Type _) [Magma G] (h: Equation3573 G) : Equation3350 G := fun x y z =>
  let v0 := M z z
  have h1 := R y
  let v2 := M (M x x) x
  T (T (T (T (h x y z) (C h1 (T (h v0 x z) (h x (M v0 v0) x)))) (S (h v2 y v0))) (h v2 y z)) (C h1 (S (h x v0 x)))

@[equational_result]
theorem Equation3791_implies_Equation3323 (G: Type _) [Magma G] (h: Equation3791 G) : Equation3323 G := fun x y z =>
  let v0 := M z z
  let v1 := M y v0
  T (T (h x y v0) (C (R (M v0 x)) (T (T (h y v0 v0) (C (T (h v0 y v0) (C (S (h z z z)) (R v1))) (R (M v0 v0)))) (S (h v1 v0 v0))))) (S (h x v1 v0))

@[equational_result]
theorem Equation3804_implies_Equation3537 (G: Type _) [Magma G] (h: Equation3804 G) : Equation3537 G := fun x y z =>
  let v0 := M z z
  let v1 := M v0 y
  have h2 := R v1
  T (T (h x y v1) (C (T (h v1 y v0) (C h2 (T (C h2 (h z z z)) (S (h v0 y v0))))) (R (M x v1)))) (S (h x v1 v1))

@[equational_result]
theorem Equation3810_implies_Equation3398 (G: Type _) [Magma G] (h: Equation3810 G) : Equation3398 G := fun x y z =>
  let v0 := M x z
  let v1 := M y v0
  T (T (T (T (T (h x y y) (h (M y y) (M y x) v1)) (C (S (h x v0 y)) (S (h y v0 y)))) (h (M x v0) v1 v0)) (C (R (M v0 v1)) (S (h v0 z x)))) (S (h z v1 v0))

@[equational_result]
theorem Equation4182_implies_Equation4200 (G: Type _) [Magma G] (h: Equation4182 G) : Equation4200 G := fun x y z =>
  let v0 := M z x
  let v1 := M v0 z
  let v2 := M (M y x) x
  T (T (T (T (h x y x) (h v2 x z)) (C (T (T (C (h x z x) (R z)) (S (h z v0 x))) (h z v0 z)) (R v2))) (S (h v2 v1 z))) (S (h v1 y x))

@[equational_result]
theorem Equation2113_implies_Equation1577 (G: Type _) [Magma G] (h: Equation2113 G) : Equation1577 G := fun x y z =>
  let v0 := M y z
  let v1 := M z x
  let v2 := M y v1
  let v3 := M v0 v2
  T (T (h x z v0) (C (C (T (h v1 v0 v2) (C (S (h z y v1)) (R v3))) (R v0)) (R (M z v0)))) (S (h v3 z v0))

@[equational_result]
theorem Equation3320_implies_Equation3522 (G: Type _) [Magma G] (h: Equation3320 G) : Equation3522 G := fun x y =>
  let v0 := M y y
  have h1 := R x
  let v2 := M v0 y
  T (T (T (h x y (M y v2)) (C h1 (S (h y y v2)))) (h x v0 v2)) (C h1 (T (T (S (h v0 v0 y)) (C (R v0) (h y y y))) (S (h v0 y v0))))

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
theorem Equation3770_implies_Equation4109 (G: Type _) [Magma G] (h: Equation3770 G) : Equation4109 G := fun x y z =>
  let v0 := M y z
  let v1 := M v0 z
  let v2 := M v1 v0
  have h3 := h x v1 v0
  T (T (T (T (h x x v1) (C h3 h3)) (S (h v2 v2 (M x v0)))) (C (S (h y v0 z)) (R v2))) (S (h v1 y v0))

@[equational_result]
theorem Equation3804_implies_Equation3620 (G: Type _) [Magma G] (h: Equation3804 G) : Equation3620 G := fun x y z =>
  let v0 := M z y
  let v1 := M v0 x
  let v2 := M y v0
  T (T (T (T (T (h x y v0) (C (h v0 y x) (h x v0 y))) (S (h v2 v1 (M x y)))) (h v2 v1 v0)) (C (R (M v0 v1)) (S (h z v0 y)))) (S (h z v1 v0))

@[equational_result]
theorem Equation3810_implies_Equation3932 (G: Type _) [Magma G] (h: Equation3810 G) : Equation3932 G := fun x y z =>
  let v0 := M y z
  let v1 := M x v0
  T (T (T (T (T (h x y x) (h (M x y) (M x x) v1)) (C (S (h x v0 x)) (S (h y v0 x)))) (h v1 (M y v0) v0)) (C (S (h v0 z y)) (R (M v0 v1)))) (S (h v1 z v0))

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
theorem Equation3350_implies_Equation3537 (G: Type _) [Magma G] (h: Equation3350 G) : Equation3537 G := fun x y z =>
  let v0 := M z z
  let v1 := M v0 y
  let v2 := M x v0
  T (T (T (T (h x y z) (h y v2 z)) (C (R v2) (T (T (h y v0 v0) (C (R v0) (S (h v0 y z)))) (h v0 v1 z)))) (S (h v1 v2 v0))) (S (h x v1 z))

@[equational_result]
theorem Equation3755_implies_Equation395 (G: Type _) [Magma G] (h: Equation3755 G) : Equation395 G := fun x y z =>
  let v0 := M z x
  let v1 := M v0 y
  T (T (T (T (h x y v0) (h (M y x) v1 v1)) (C (T (T (C (R v1) (h y x z)) (S (h y v0 (M x y)))) (h y v0 y)) (R (M v1 v1)))) (S (h (M y v0) v1 v1))) (S (h v0 y v0))

@[equational_result]
theorem Equation3791_implies_Equation3737 (G: Type _) [Magma G] (h: Equation3791 G) : Equation3737 G := fun x y z =>
  let v0 := M z y
  let v1 := M y x
  T (h x y z) (C (T (T (T (T (T (h z x y) (C (h y z y) (h x y y))) (S (h v0 v1 (M y y)))) (C (h z y x) (h y x z))) (S (h v1 v0 (M x z)))) (S (h x z y))) (R (M y z)))

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
theorem Equation1902_implies_Equation31 (G: Type _) [Magma G] (h: Equation1902 G) : Equation31 G := fun x y =>
  let v0 := M y y
  let v1 := M v0 x
  let v2 := M v1 (M x v1)
  T (T (h x v1 v0) (C (T (T (R v2) (h v2 v0 v1)) (C (C (R v0) (S (h x v1 y))) (R (M v1 v1)))) (R (M v0 v0)))) (S (h v1 v1 v0))

@[equational_result]
theorem Equation2136_implies_Equation2 (G: Type _) [Magma G] (h: Equation2136 G) : Equation2 G := fun x y =>
  let v0 := M x x
  let v1 := M v0 x
  let v2 := M y y
  T (T (T (T (T (h x x x) (C (R v1) (h v0 x x))) (S (h v1 x v1))) (h v1 v1 (M v2 x))) (C (R (M (M v1 v1) v1)) (S (h v2 x x)))) (S (h y v1 y))

@[equational_result]
theorem Equation2170_implies_Equation43 (G: Type _) [Magma G] (h: Equation2170 G) : Equation43 G := fun x y =>
  let v0 := M y x
  let v1 := M x y
  let v2 := M v1 v1
  have h3 := h v1 x y
  T (T h3 (C (T (h v2 v2 v1) (C (S (h v1 v1 v1)) (T (C h3 (R v2)) (S (h v0 v1 v1))))) (R v0))) (S (h v0 x y))

@[equational_result]
theorem Equation3404_implies_Equation3588 (G: Type _) [Magma G] (h: Equation3404 G) : Equation3588 G := fun x y z =>
  let v0 := M x y
  let v1 := M y v0
  have h2 := R v0
  T (T (T (T (h x y v0) (C h2 (C (R y) (T (h v0 x v0) (C h2 (S (h y v0 x))))))) (S (h v1 y v0))) (h v1 y z)) (C (R z) (S (h v0 z y)))

@[equational_result]
theorem Equation3567_implies_Equation3370 (G: Type _) [Magma G] (h: Equation3567 G) : Equation3370 G := fun x y z =>
  let v0 := M z x
  let v1 := M (M x z) x
  let v2 := M (M z v0) z
  T (h x y z) (C (R y) (T (T (T (T (T (h v0 z z) (h z v2 z)) (C (R v2) (C (h z z x) (R z)))) (S (h v1 v2 z))) (S (h v0 v1 z))) (S (h z v0 x))))

@[equational_result]
theorem Equation3758_implies_Equation4544 (G: Type _) [Magma G] (h: Equation3758 G) : Equation4544 G := fun x y z =>
  let v0 := M z y
  T (T (T (T (C (R x) (T (T (T (h y z) (C (h z z) (h y y))) (S (h (M y y) (M z z)))) (S (h z y)))) (h x v0)) (h (M v0 v0) (M x x))) (C (S (h x x)) (S (h v0 v0)))) (S (h v0 x))

@[equational_result]
theorem Equation3791_implies_Equation3794 (G: Type _) [Magma G] (h: Equation3791 G) : Equation3794 G := fun x y z =>
  let v0 := M y x
  let v1 := M x z
  T (h x y z) (C (R (M z x)) (T (T (T (T (T (h y z x) (C (h x y x) (h z x x))) (S (h v0 v1 (M x x)))) (C (h y x z) (h x z y))) (S (h v1 v0 (M z y)))) (S (h z y x))))

@[equational_result]
theorem Equation3804_implies_Equation3959 (G: Type _) [Magma G] (h: Equation3804 G) : Equation3959 G := fun x y z =>
  let v0 := M x z
  let v1 := M y v0
  let v2 := M v0 x
  T (T (T (T (T (h x y v0) (C (h v0 y x) (h x v0 y))) (S (h v1 v2 (M x y)))) (h v1 v2 v0)) (C (S (h v0 z x)) (R (M v1 v0)))) (S (h v1 z v0))

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
theorem Equation1571_implies_Equation3770 (G: Type _) [Magma G] (h: Equation1571 G) : Equation3770 G := fun x y z =>
  let v0 := M x z
  let v1 := M y z
  let v2 := M v1 v0
  have h3 := h x v1 v0
  have h4 := R v2
  T (C h3 (T (T (h y v1 v0) (C h4 (S (h x y z)))) (C h4 h3))) (S (h v2 v2 (M v1 (M x v0))))

@[equational_result]
theorem Equation1761_implies_Equation1155 (G: Type _) [Magma G] (h: Equation1761 G) : Equation1155 G := fun x y z =>
  let v0 := M x z
  let v1 := M (M z v0) y
  let v2 := M y v1
  have h3 := R v2
  T (T (h x z v2) (C (R (M z v2)) (C (T (h v0 y v1) (C h3 (S (h z v0 y)))) h3))) (S (h v2 z v2))

@[equational_result]
theorem Equation1964_implies_Equation2576 (G: Type _) [Magma G] (h: Equation1964 G) : Equation2576 G := fun x y z =>
  let v0 := M z x
  let v1 := M y (M v0 z)
  let v2 := M v1 y
  have h3 := R v2
  T (T (h x v2 z) (C (C h3 (T (h v0 v1 y) (C (S (h z y v0)) h3))) (R (M v2 z)))) (S (h v2 v2 z))

@[equational_result]
theorem Equation1966_implies_Equation19 (G: Type _) [Magma G] (h: Equation1966 G) : Equation19 G := fun x y z =>
  let v0 := M z x
  let v1 := M y v0
  have h2 := h v0 x y
  have h3 := C (S (h x y z)) (R v0)
  have h4 := h x v1 z
  T (T (T h4 h3) (C (T (T h4 h3) (C (R x) h2)) h2)) (S (h v1 x (M x v1)))

@[equational_result]
theorem Equation2196_implies_Equation2917 (G: Type _) [Magma G] (h: Equation2196 G) : Equation2917 G := fun x y z =>
  let v0 := M x y
  let v1 := M y v0
  let v2 := M v0 v1
  T (T (h x v2 x) (C (R (M (M v2 x) x)) (T (T (C (h x y v0) (R v2)) (S (h v0 v1 v0))) (h v0 v1 z)))) (S (h (M (M v1 z) z) v2 x))

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
theorem Equation3567_implies_Equation3997 (G: Type _) [Magma G] (h: Equation3567 G) : Equation3997 G := fun x y z =>
  let v0 := M x z
  have h1 := R x
  T (T (h x y x) (C (R y) (C (T (h x x v0) (C h1 (T (T (h (M v0 x) v0 z) (C (R v0) (C (S (h z z x)) (R z)))) (S (h z v0 z))))) h1))) (S (h (M z v0) y x))

@[equational_result]
theorem Equation3763_implies_Equation41 (G: Type _) [Magma G] (h: Equation3763 G) : Equation41 G := fun x y z =>
  have h0 := h y z x
  have h1 := h x x x
  let v2 := M y z
  let v3 := M z v2
  let v4 := M x x
  T (T (T (T h1 (h v4 v4 v3)) (S (h v2 v4 v3))) (C (T h0 (S (h z z x))) (T h1 (S (h z x x))))) (S h0)

@[equational_result]
theorem Equation3770_implies_Equation4332 (G: Type _) [Magma G] (h: Equation3770 G) : Equation4332 G := fun x y z =>
  let v0 := M y x
  let v1 := M y z
  let v2 := M z v1
  let v3 := M x v1
  T (T (T (h x v0 v1) (h (M v0 v1) v3 v2)) (C (T (h v3 v2 (M y v1)) (C (S (h y z v1)) (S (h y x v1)))) (S (h z v0 v1)))) (S (h z v1 v0))

@[equational_result]
theorem Equation3791_implies_Equation4226 (G: Type _) [Magma G] (h: Equation3791 G) : Equation4226 G := fun x y z =>
  let v0 := M z z
  let v1 := M v0 x
  let v2 := M v1 y
  T (T (h x y v2) (C (T (T (h v2 x v0) (C (R (M v0 v2)) (T (h x v0 v0) (C (R v1) (S (h z z z)))))) (S (h v2 v1 v0))) (R (M y v2)))) (S (h v1 y v2))

@[equational_result]
theorem Equation3804_implies_Equation3294 (G: Type _) [Magma G] (h: Equation3804 G) : Equation3294 G := fun x y z =>
  let v0 := M y z
  let v1 := M z v0
  T (T (T (h x x v1) (C (T (T (T (h v1 x v0) (C (R (M v0 x)) (S (h y v0 z)))) (S (h y x v0))) (h y x x)) (h x v1 x))) (S (h (M x v1) (M y x) (M x x)))) (S (h y v1 x))

@[equational_result]
theorem Equation3804_implies_Equation3497 (G: Type _) [Magma G] (h: Equation3804 G) : Equation3497 G := fun x y z =>
  let v0 := M z y
  let v1 := M v0 z
  T (T (T (h x x y) (C (h y x x) (T (T (T (h x y v0) (C (h v0 y z) (R (M x v0)))) (S (h x v1 v0))) (h x v1 x)))) (S (h (M x v1) (M y x) (M x x)))) (S (h y v1 x))

@[equational_result]
theorem Equation3804_implies_Equation3903 (G: Type _) [Magma G] (h: Equation3804 G) : Equation3903 G := fun x y z =>
  let v0 := M z y
  let v1 := M y v0
  T (T (T (h x x z) (C (T (T (T (h z x v0) (C (R (M v0 x)) (h z v0 y))) (S (h v1 x v0))) (h v1 x x)) (h x z x))) (S (h (M x z) (M v1 x) (M x x)))) (S (h v1 z x))

@[equational_result]
theorem Equation4013_implies_Equation3534 (G: Type _) [Magma G] (h: Equation4013 G) : Equation3534 G := fun x y z =>
  let v0 := M z y
  have h1 := R y
  T (T (h x y y) (C (C h1 (T (h y y v0) (C (T (T (h v0 (M y v0) z) (C (C (R z) (S (h z z y))) (R v0))) (S (h v0 z z))) h1))) (R x))) (S (h x (M v0 z) y))

@[equational_result]
theorem Equation4176_implies_Equation3994 (G: Type _) [Magma G] (h: Equation4176 G) : Equation3994 G := fun x y z =>
  let v0 := M x y
  let v1 := M v0 x
  have h2 := R v0
  T (T (T (T (h x y v0) (C (C (T (h y v0 v0) (C (S (h v0 x y)) h2)) (R x)) h2)) (S (h x v1 v0))) (h x v1 z)) (C (S (h z v0 x)) (R z))

@[equational_result]
theorem Equation4182_implies_Equation3553 (G: Type _) [Magma G] (h: Equation4182 G) : Equation3553 G := fun x y z =>
  have h0 := R x
  let v1 := M (M x x) x
  let v2 := M (M y z) z
  T (T (T (T (T (T (h x y z) (h v2 x x)) (C (C (h x x x) h0) (R v2))) (S (h v2 v1 x))) (S (h v1 y z))) (C (C (h x x z) h0) (R y))) (S (h y (M (M x z) z) x))

@[equational_result]
theorem Equation508_implies_Equation3286 (G: Type _) [Magma G] (h: Equation508 G) : Equation3286 G := fun x y z =>
  let v0 := M x x
  let v1 := M z z
  let v2 := M y v1
  T (h v0 v2 z) (C (T (C (R y) (h v1 y z)) (S (h y y v1))) (T (C (R v2) (T (T (C (R v0) (h v1 v0 z)) (S (h v0 v0 v1))) (h v0 v2 x))) (S (h v2 v2 v0))))

@[equational_result]
theorem Equation1496_implies_Equation2132 (G: Type _) [Magma G] (h: Equation1496 G) : Equation2132 G := fun x y z =>
  let v0 := M z z
  let v1 := M y y
  let v2 := M v1 x
  let v3 := M v2 v0
  T (T (h x v3 v3) (C (T (T (C (R v3) (h x v1 y)) (S (h v0 v2 v1))) (h v0 v2 z)) (R (M v3 (M v3 v3))))) (S (h v3 v3 v3))

@[equational_result]
theorem Equation1558_implies_Equation692 (G: Type _) [Magma G] (h: Equation1558 G) : Equation692 G := fun x y z =>
  let v0 := M z y
  let v1 := M v0 z
  let v2 := M x v1
  have h3 := S (h y x v1)
  T (h x v0 z) (C (T (C (R v0) (T (h z v2 (M y v2)) (C h3 (C (R z) h3)))) (S (h y z y))) (R v2))

@[equational_result]
theorem Equation1695_implies_Equation2947 (G: Type _) [Magma G] (h: Equation1695 G) : Equation2947 G := fun x y =>
  let v0 := M y y
  let v1 := M y v0
  let v2 := M (M v1 v1) v1
  T (h x v1) (C (R (M v1 x)) (T (T (h v2 v0) (C (T (C (h v0 y) (R v2)) (S (h (M v0 y) v1))) (R (M (M v0 v0) v0)))) (S (h y v0))))

@[equational_result]
theorem Equation1761_implies_Equation3182 (G: Type _) [Magma G] (h: Equation1761 G) : Equation3182 G := fun x y z =>
  let v0 := M y z
  let v1 := M v0 x
  let v2 := M v1 y
  let v3 := M v2 z
  T (T (h x y v2) (C (R (M y v2)) (T (T (S (h v0 x y)) (h v0 v3 y)) (C (R (M v3 y)) (C (S (h v1 y z)) (R y)))))) (S (h v3 y v2))

