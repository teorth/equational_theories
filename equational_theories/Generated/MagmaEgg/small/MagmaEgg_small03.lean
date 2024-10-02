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
theorem Equation1757_implies_Equation2 (G: Type _) [Magma G] (h: Equation1757 G) : Equation2 G := fun x y =>
  let v0 := M y y
  have h1 := S (h y x x)
  T (T (T (h x (M x x) (M v0 x)) (C h1 h1)) (C (h y x y) (h y y y))) (S (h y (M x y) (M v0 y)))

@[equational_result]
theorem Equation1889_implies_Equation2 (G: Type _) [Magma G] (h: Equation1889 G) : Equation2 G := fun x y =>
  let v0 := M y y
  have h1 := S (h y x x)
  T (T (T (h x (M x v0) (M x x)) (C h1 h1)) (C (h y y y) (h y y x))) (S (h y (M y v0) (M y x)))

@[equational_result]
theorem Equation1892_implies_Equation2 (G: Type _) [Magma G] (h: Equation1892 G) : Equation2 G := fun x y =>
  let v0 := M y y
  let v1 := M x v0
  have h2 := R v0
  T (T (T (h x v1 y) (C (S (h y x x)) h2)) (C (h y x y) h2)) (S (h y v1 y))

@[equational_result]
theorem Equation1902_implies_Equation4332 (G: Type _) [Magma G] (h: Equation1902 G) : Equation4332 G := fun x y z =>
  let v0 := M z (M y z)
  let v1 := M x (M y x)
  T (T (h v1 v1 x) (C (T (S (h y x v1)) (h y z v0)) (R (M x x)))) (S (h v0 v0 x))

@[equational_result]
theorem Equation2076_implies_Equation3534 (G: Type _) [Magma G] (h: Equation2076 G) : Equation3534 G := fun x y z =>
  let v0 := M z y
  let v1 := M y v0
  T (h (M x y) v0 v1) (C (S (h x y v0)) (T (C (h v0 z y) (R v1)) (S (h (M v0 z) y v0))))

@[equational_result]
theorem Equation2132_implies_Equation3692 (G: Type _) [Magma G] (h: Equation2132 G) : Equation3692 G := fun x y z =>
  let v0 := M y y
  let v1 := M x x
  T (h v1 x z) (C (T (C (T (h v1 v1 y) (C (S (h v1 x x)) (R v0))) (R v1)) (S (h v0 x x))) (R (M z z)))

@[equational_result]
theorem Equation3011_implies_Equation31 (G: Type _) [Magma G] (h: Equation3011 G) : Equation31 G := fun x y =>
  let v0 := M y y
  let v1 := M v0 x
  let v2 := M v0 (M v1 v1)
  T (h x v0 v1) (C (T (C (h v2 v0 v1) (R v0)) (S (h v0 v2 y))) (R x))

@[equational_result]
theorem Equation3128_implies_Equation2982 (G: Type _) [Magma G] (h: Equation3128 G) : Equation2982 G := fun x y z =>
  have h0 := R y
  let v1 := M z x
  let v2 := M y v1
  T (h x z y) (C (C (T (C (h v1 y v2) h0) (S (h v2 v2 y))) (R z)) h0)

@[equational_result]
theorem Equation3276_implies_Equation3303 (G: Type _) [Magma G] (h: Equation3276 G) : Equation3303 G := fun x y z w =>
  let v0 := M x x
  T (T (T (h x v0 v0) (C (R v0) (T (S (h v0 x x)) (h v0 z x)))) (S (h z v0 v0))) (h z y w)

@[equational_result]
theorem Equation3737_implies_Equation3943 (G: Type _) [Magma G] (h: Equation3737 G) : Equation3943 G := fun x y z =>
  let v0 := M z z
  let v1 := M x v0
  T (T (h x y v0) (C (T (h x v0 v0) (C (R v1) (S (h z z z)))) (R (M y v0)))) (S (h v1 y v0))

@[equational_result]
theorem Equation3808_implies_Equation41 (G: Type _) [Magma G] (h: Equation3808 G) : Equation41 G := fun x y z =>
  let v0 := M z y
  T (T (T (T (h x x y) (C (T (h y x x) (S (h x x x))) (T (h x y x) (S (h z y x))))) (h (M x x) v0 y)) (S (h (M y z) v0 y))) (S (h y z y))

@[equational_result]
theorem Equation4225_implies_Equation41 (G: Type _) [Magma G] (h: Equation4225 G) : Equation41 G := fun x y z =>
  let v0 := M y y
  let v1 := M v0 y
  T (T (T (T (h x x y) (C (T (h v0 x x) (S (h v0 y x))) (R x))) (h v1 x x)) (S (h v1 y x))) (S (h y z y))

@[equational_result]
theorem Equation658_implies_Equation11 (G: Type _) [Magma G] (h: Equation658 G) : Equation11 G := fun x y =>
  let v0 := M y y
  let v1 := M x v0
  let v2 := M (M v1 v1) v0
  T (h x v0 v1) (C (R x) (T (C (R v0) (h v2 v0 v1)) (S (h v0 v2 y))))

@[equational_result]
theorem Equation1137_implies_Equation1996 (G: Type _) [Magma G] (h: Equation1137 G) : Equation1996 G := fun x y z =>
  let v0 := M z z
  let v1 := M y v0
  have h2 := h x v1 z
  T h2 (C (R v1) (T (h (M (M v1 v0) x) y z) (C (R y) (S h2))))

@[equational_result]
theorem Equation1293_implies_Equation14 (G: Type _) [Magma G] (h: Equation1293 G) : Equation14 G := fun x y =>
  let v0 := M x y
  have h1 := S (h v0 v0 x)
  let v2 := M (M (M v0 v0) x) x
  T (h x y v2) (C (R y) (T (C h1 (R v2)) h1))

@[equational_result]
theorem Equation2511_implies_Equation1131 (G: Type _) [Magma G] (h: Equation2511 G) : Equation1131 G := fun x y z =>
  let v0 := M z x
  let v1 := M (M y v0) z
  let v2 := M v0 v1
  T (h x v2 v1) (C (T (C (R v2) (S (h z x v1))) (S (h y v0 z))) (R v1))

@[equational_result]
theorem Equation2546_implies_Equation5 (G: Type _) [Magma G] (h: Equation2546 G) : Equation5 G := fun x y =>
  have h0 := S (h y x x)
  let v1 := M x (M (M x x) x)
  T (h x v1 y) (C (T (C (R v1) (T (C (S (h v1 x x)) (R y)) h0)) h0) (R x))

@[equational_result]
theorem Equation2876_implies_Equation2064 (G: Type _) [Magma G] (h: Equation2876 G) : Equation2064 G := fun x y =>
  let v0 := M y y
  have h1 := R y
  have h2 := h x v0
  T h2 (C (T (h (M (M x (M v0 v0)) v0) y) (C (C (S h2) h1) h1)) (R v0))

@[equational_result]
theorem Equation3276_implies_Equation320 (G: Type _) [Magma G] (h: Equation3276 G) : Equation320 G := fun x y z =>
  let v0 := M x x
  T (h x y x) (C (R y) (T (C (R x) (T (T (T (h x v0 v0) (C (R v0) (S (h v0 x x)))) (S (h v0 v0 x))) (h v0 z x))) (S (h z x v0))))

@[equational_result]
theorem Equation3350_implies_Equation4226 (G: Type _) [Magma G] (h: Equation3350 G) : Equation4226 G := fun x y z =>
  let v0 := M z z
  let v1 := M v0 x
  T (T (h x y z) (C (R y) (T (T (h x v0 v0) (C (R v0) (S (h v0 x z)))) (h v0 v1 z)))) (S (h v1 y v0))

@[equational_result]
theorem Equation3360_implies_Equation41 (G: Type _) [Magma G] (h: Equation3360 G) : Equation41 G := fun x y z =>
  let v0 := M y y
  let v1 := M z v0
  T (T (T (T (h x x y) (C (R x) (T (h x v0 x) (S (h z v0 x))))) (h x v1 x)) (S (h z v1 x))) (S (h y z y))

@[equational_result]
theorem Equation3762_implies_Equation355 (G: Type _) [Magma G] (h: Equation3762 G) : Equation355 G := fun x y z w =>
  let v0 := M w y
  have h1 := S (h w y)
  let v2 := M y y
  T (T (T (T (h x y) (h v2 v2)) (C h1 h1)) (h v0 v0)) (S (h z v0))

@[equational_result]
theorem Equation4143_implies_Equation4673 (G: Type _) [Magma G] (h: Equation4143 G) : Equation4673 G := fun x y z =>
  let v0 := M x z
  have h1 := h v0 y z
  have h2 := R z
  T (T (C (T (h x y z) (C h1 h2)) h2) (S (h (M (M v0 z) y) z z))) (S h1)

@[equational_result]
theorem Equation4216_implies_Equation3534 (G: Type _) [Magma G] (h: Equation4216 G) : Equation3534 G := fun x y z =>
  let v0 := M z y
  let v1 := M v0 z
  T (T (h x y z) (C (T (h v0 z v1) (C (C (S (h z y z)) (R v1)) (R v0))) (R x))) (S (h x v1 v0))

@[equational_result]
theorem Equation556_implies_Equation2511 (G: Type _) [Magma G] (h: Equation556 G) : Equation2511 G := fun x y z =>
  let v0 := M x y
  let v1 := M y (M v0 z)
  have h2 := R v1
  T (h x v1 y) (C h2 (T (C (R y) (C h2 (h v0 y z))) (S (h z y v1))))

@[equational_result]
theorem Equation746_implies_Equation2992 (G: Type _) [Magma G] (h: Equation746 G) : Equation2992 G := fun x y z =>
  let v0 := M z y
  let v1 := M (M y v0) x
  let v2 := M x v1
  T (h x v1 y) (C (R v1) (T (C (R y) (C (R v2) (h y v0 x))) (S (h z y v2))))

@[equational_result]
theorem Equation827_implies_Equation3 (G: Type _) [Magma G] (h: Equation827 G) : Equation3 G := fun x =>
  have h0 := S (h x x x)
  let v1 := M x x
  let v2 := M v1 v1
  T (h x v2 (M (M v2 x) v1)) (C (R x) (T (C h0 (S (h v2 x x))) h0))

@[equational_result]
theorem Equation1065_implies_Equation4 (G: Type _) [Magma G] (h: Equation1065 G) : Equation4 G := fun x y =>
  have h0 := S (h y x x)
  let v1 := M (M x (M x x)) x
  T (h x y v1) (C (R x) (T (C (T (C (R y) (S (h v1 x x))) h0) (R v1)) h0))

@[equational_result]
theorem Equation1323_implies_Equation1526 (G: Type _) [Magma G] (h: Equation1323 G) : Equation1526 G := fun x y =>
  have h0 := R y
  let v1 := M y y
  have h2 := h x v1
  T h2 (C (R v1) (T (h (M (M (M v1 v1) x) v1) y) (C h0 (C (S h2) h0))))

@[equational_result]
theorem Equation2602_implies_Equation1746 (G: Type _) [Magma G] (h: Equation2602 G) : Equation1746 G := fun x y z =>
  let v0 := M (M z z) x
  let v1 := M (M y y) v0
  have h2 := R x
  T (T (h x x z) (C (C h2 (h v0 v1 y)) h2)) (S (h v1 x v1))

@[equational_result]
theorem Equation3293_implies_Equation320 (G: Type _) [Magma G] (h: Equation3293 G) : Equation320 G := fun x y z =>
  let v0 := M z z
  let v1 := M y v0
  T (h x y v0) (C (R y) (T (T (C (R v0) (T (h y x x) (S (h z x x)))) (h v0 v1 v0)) (S (h z v1 v0))))

@[equational_result]
theorem Equation3364_implies_Equation3331 (G: Type _) [Magma G] (h: Equation3364 G) : Equation3331 G := fun x y z =>
  let v0 := M z (M y z)
  let v1 := M z (M x z)
  T (T (T (T (h x y z) (h y v1 v0)) (C (R v1) (C (R v0) (h y v0 z)))) (S (h v0 v1 v0))) (S (h x v0 z))

@[equational_result]
theorem Equation3364_implies_Equation3567 (G: Type _) [Magma G] (h: Equation3364 G) : Equation3567 G := fun x y z =>
  let v0 := M z x
  let v1 := M x v0
  T (h x y v0) (C (R y) (T (T (S (h z v0 x)) (C (R z) (T (h z x x) (h x v1 v0)))) (S (h v0 z v1))))

@[equational_result]
theorem Equation3364_implies_Equation4200 (G: Type _) [Magma G] (h: Equation3364 G) : Equation4200 G := fun x y z =>
  let v0 := M z x
  let v1 := M x v0
  let v2 := M v0 z
  T (T (h x y v0) (C (R y) (T (h v0 v1 z) (C (R v1) (h z v2 x))))) (S (h v2 y v1))

@[equational_result]
theorem Equation3402_implies_Equation41 (G: Type _) [Magma G] (h: Equation3402 G) : Equation41 G := fun x y z =>
  let v0 := M z y
  T (T (h x x y) (C (R y) (T (T (T (R (M x (M x y))) (C (R x) (T (h x y x) (S (h z y x))))) (h x v0 x)) (S (h z v0 x))))) (S (h y z y))

@[equational_result]
theorem Equation3715_implies_Equation3522 (G: Type _) [Magma G] (h: Equation3715 G) : Equation3522 G := fun x y =>
  let v0 := M y y
  have h1 := h y y
  T (T (T (h x y) (C (R (M x x)) h1)) (S (h x v0))) (C (R x) (T (T h1 (C h1 (R v0))) (S (h v0 y))))

@[equational_result]
theorem Equation4216_implies_Equation4013 (G: Type _) [Magma G] (h: Equation4216 G) : Equation4013 G := fun x y z =>
  let v0 := M y z
  let v1 := M v0 y
  T (h x y v0) (C (T (T (S (h v0 z y)) (C (T (h y z y) (h v1 y v0)) (R z))) (S (h z v0 v1))) (R x))

@[equational_result]
theorem Equation1059_implies_Equation10 (G: Type _) [Magma G] (h: Equation1059 G) : Equation10 G := fun x y =>
  have h0 := R x
  let v1 := M y x
  have h2 := R y
  T (h x y v1) (C h0 (C (T (C h2 (C (h v1 x y) h2)) (S (h y v1 (M x v1)))) h0))

@[equational_result]
theorem Equation1131_implies_Equation2511 (G: Type _) [Magma G] (h: Equation1131 G) : Equation2511 G := fun x y z =>
  let v0 := M x y
  let v1 := M y (M v0 z)
  let v2 := M v1 v0
  T (h x v1 v2) (C (R v1) (T (C (S (h y v1 x)) (R v2)) (S (h z y v0))))

@[equational_result]
theorem Equation2196_implies_Equation14 (G: Type _) [Magma G] (h: Equation2196 G) : Equation14 G := fun x y =>
  let v0 := M x y
  let v1 := M y v0
  let v2 := M v0 v1
  T (h x v2 v1) (C (S (h y v0 v1)) (T (C (h x y v0) (R v2)) (S (h v0 v1 v0))))

@[equational_result]
theorem Equation2480_implies_Equation25 (G: Type _) [Magma G] (h: Equation2480 G) : Equation25 G := fun x y =>
  have h0 := R x
  let v1 := M x y
  have h2 := R y
  T (h x y v1) (C (C h0 (T (C (C h2 (h v1 x y)) h2) (S (h y v1 (M v1 x))))) h0)

@[equational_result]
theorem Equation3715_implies_Equation3915 (G: Type _) [Magma G] (h: Equation3715 G) : Equation3915 G := fun x y =>
  let v0 := M x x
  have h1 := h x x
  T (T (T (h x y) (C h1 (R (M y y)))) (S (h v0 y))) (C (T (T h1 (C (R v0) h1)) (S (h x v0))) (R y))

@[equational_result]
theorem Equation3758_implies_Equation3915 (G: Type _) [Magma G] (h: Equation3758 G) : Equation3915 G := fun x y =>
  let v0 := M x x
  have h1 := h x x
  T (T (T (h x y) (C (R (M y y)) h1)) (S (h v0 y))) (C (T (T h1 (C h1 (R v0))) (S (h x v0))) (R y))

@[equational_result]
theorem Equation3770_implies_Equation3756 (G: Type _) [Magma G] (h: Equation3770 G) : Equation3756 G := fun x y z =>
  let v0 := M z y
  have h1 := h x z y
  T (h x y x) (C (R (M y x)) (T (T (T (h x x z) (C h1 h1)) (S (h v0 v0 (M x y)))) (S (h z z y))))

@[equational_result]
theorem Equation4216_implies_Equation3331 (G: Type _) [Magma G] (h: Equation4216 G) : Equation3331 G := fun x y z =>
  let v0 := M y z
  let v1 := M v0 y
  let v2 := M z v0
  T (T (h x y v0) (C (T (h v1 v0 z) (C (h v2 z y) (R v1))) (R x))) (S (h x v2 v1))

@[equational_result]
theorem Equation4229_implies_Equation3323 (G: Type _) [Magma G] (h: Equation4229 G) : Equation3323 G := fun x y z =>
  let v0 := M z z
  let v1 := M y v0
  T (T (h x y z) (C (T (T (h v0 y v0) (C (S (h y v0 z)) (R v0))) (h v1 v0 z)) (R x))) (S (h x v1 v0))

@[equational_result]
theorem Equation512_implies_Equation2 (G: Type _) [Magma G] (h: Equation512 G) : Equation2 G := fun x y =>
  let v0 := M y x
  have h1 := R x
  T (T (T (h x x (M x (M x v0))) (C h1 (C h1 (C h1 (S (h y x x)))))) (C h1 (C h1 (C h1 (h y y x))))) (S (h y x (M y (M y v0))))

@[equational_result]
theorem Equation830_implies_Equation103 (G: Type _) [Magma G] (h: Equation830 G) : Equation103 G := fun x y z =>
  let v0 := M z z
  T (h x y z) (C (R x) (C (R (M x y)) (T (C (R z) (T (h z z z) (C (h z x x) (R (M v0 v0))))) (S (h z (M (M z x) (M x x)) v0)))))

@[equational_result]
theorem Equation1340_implies_Equation2199 (G: Type _) [Magma G] (h: Equation1340 G) : Equation2199 G := fun x y z =>
  let v0 := M y x
  let v1 := M (M y z) z
  have h2 := h x v1 v0
  T h2 (C (R v1) (T (h (M (M (M v1 v0) v0) x) y z) (C (R y) (S h2))))

@[equational_result]
theorem Equation2335_implies_Equation711 (G: Type _) [Magma G] (h: Equation2335 G) : Equation711 G := fun x y z =>
  let v0 := M x z
  let v1 := M y (M y (M v0 z))
  have h2 := R v1
  T (T (h x v1 z) (C (C h2 (C h2 (h v0 y z))) (R z))) (S (h v1 v1 z))

@[equational_result]
theorem Equation2688_implies_Equation2880 (G: Type _) [Magma G] (h: Equation2688 G) : Equation2880 G := fun x y z =>
  have h0 := R z
  let v1 := M y y
  have h2 := h x z v1
  T h2 (C (T (h (M (M x z) (M v1 v1)) z y) (C (C (S h2) (R v1)) h0)) h0)

@[equational_result]
theorem Equation3132_implies_Equation2 (G: Type _) [Magma G] (h: Equation3132 G) : Equation2 G := fun x y =>
  let v0 := M x y
  have h1 := R x
  T (T (T (h x (M (M v0 x) x) x) (C (C (C (S (h y x x)) h1) h1) h1)) (C (C (C (h y x y) h1) h1) h1)) (S (h y (M (M v0 y) y) x))

@[equational_result]
theorem Equation3370_implies_Equation3334 (G: Type _) [Magma G] (h: Equation3370 G) : Equation3334 G := fun x y z =>
  let v0 := M z (M z y)
  let v1 := M x (M x x)
  T (T (T (T (h x y x) (h y v1 z)) (h v1 v0 x)) (C (R v0) (C (R x) (S (h x x x))))) (S (h x v0 x))

@[equational_result]
theorem Equation3370_implies_Equation3364 (G: Type _) [Magma G] (h: Equation3370 G) : Equation3364 G := fun x y z =>
  have h0 := R y
  let v1 := M x (M x x)
  T (T (T (T (h x y x) (C h0 (C (R x) (h x x x)))) (S (h v1 y x))) (h v1 y z)) (C h0 (C (R z) (S (h x z x))))

@[equational_result]
theorem Equation3404_implies_Equation3323 (G: Type _) [Magma G] (h: Equation3404 G) : Equation3323 G := fun x y z =>
  let v0 := M y (M z z)
  let v1 := M y x
  T (T (h x y y) (C (R y) (T (T (h y v1 z) (C (R z) (C (R v1) (h z y z)))) (S (h v0 v1 z))))) (S (h x v0 y))

@[equational_result]
theorem Equation3560_implies_Equation41 (G: Type _) [Magma G] (h: Equation3560 G) : Equation41 G := fun x y z =>
  let v0 := M x x
  let v1 := M v0 y
  T (T (T (T (h x x y) (h x v1 x)) (S (h z v1 x))) (C (R z) (T (h v0 y x) (S (h (M z z) y x))))) (S (h y z y))

@[equational_result]
theorem Equation3716_implies_Equation4507 (G: Type _) [Magma G] (h: Equation3716 G) : Equation4507 G := fun x y z =>
  let v0 := M x x
  let v1 := M y z
  have h2 := h x x x
  T (T (T (T (h x v1 v0) (C h2 (R (M v1 v0)))) (S (h v0 v1 v0))) (C h2 (R v1))) (S (h v0 y z))

@[equational_result]
theorem Equation3758_implies_Equation3522 (G: Type _) [Magma G] (h: Equation3758 G) : Equation3522 G := fun x y =>
  let v0 := M y y
  have h1 := h y y
  T (T (T (h x y) (C h1 (R (M x x)))) (S (h x v0))) (C (R x) (T (T h1 (C (R v0) h1)) (S (h v0 y))))

@[equational_result]
theorem Equation3804_implies_Equation3820 (G: Type _) [Magma G] (h: Equation3804 G) : Equation3820 G := fun x y z =>
  T (h x y y) (C (T (T (T (h y y z) (h (M z y) (M y z) (M z z))) (C (S (h y z z)) (S (h z y z)))) (S (h z z y))) (R (M x y)))

@[equational_result]
theorem Equation725_implies_Equation1165 (G: Type _) [Magma G] (h: Equation725 G) : Equation1165 G := fun x y z =>
  let v0 := M y x
  let v1 := M y (M (M z v0) z)
  have h2 := R v1
  T (T (h x v1 y) (C h2 (C h2 (C (h v0 y z) (R y))))) (S (h v1 v1 y))

@[equational_result]
theorem Equation1090_implies_Equation26 (G: Type _) [Magma G] (h: Equation1090 G) : Equation26 G := fun x y =>
  let v0 := M x y
  have h1 := S (h y v0 x)
  let v2 := M (M y (M v0 x)) x
  T (h x v0 v2) (C (R v0) (T (C (C (R x) h1) (R v2)) h1))

@[equational_result]
theorem Equation1101_implies_Equation1865 (G: Type _) [Magma G] (h: Equation1101 G) : Equation1865 G := fun x y z =>
  let v0 := M x (M y y)
  let v1 := M v0 (M z z)
  have h2 := R v1
  T (T (h x v1 y) (C h2 (C (h v0 v1 z) h2))) (S (h v1 v1 v1))

@[equational_result]
theorem Equation3404_implies_Equation3906 (G: Type _) [Magma G] (h: Equation3404 G) : Equation3906 G := fun x y z =>
  let v0 := M z z
  have h1 := R z
  T (T (T (h x x z) (C h1 (T (C (R x) (h z x z)) (S (h v0 z x))))) (C h1 (h v0 z y))) (S (h (M y v0) y z))

@[equational_result]
theorem Equation3756_implies_Equation3692 (G: Type _) [Magma G] (h: Equation3756 G) : Equation3692 G := fun x y z =>
  let v0 := M z z
  let v1 := M x x
  have h2 := R v1
  T (T (T (T (h x x x) (C (h x x z) h2)) (S (h v0 v1 x))) (C (h z z y) h2)) (S (h (M y y) v0 x))

@[equational_result]
theorem Equation3791_implies_Equation3804 (G: Type _) [Magma G] (h: Equation3791 G) : Equation3804 G := fun x y z =>
  let v0 := M z x
  let v1 := M y z
  T (T (T (T (h x y z) (h v0 v1 (M x y))) (C (S (h y z x)) (S (h z x y)))) (h v1 v0 (M z z))) (C (S (h z y z)) (S (h x z z)))

@[equational_result]
theorem Equation4176_implies_Equation3500 (G: Type _) [Magma G] (h: Equation4176 G) : Equation3500 G := fun x y z =>
  let v0 := M z z
  have h1 := R z
  T (T (T (h x x z) (C (T (C (h x z z) (R x)) (S (h z v0 x))) h1)) (C (h z v0 y) h1)) (S (h y (M v0 y) z))

@[equational_result]
theorem Equation4182_implies_Equation4146 (G: Type _) [Magma G] (h: Equation4182 G) : Equation4146 G := fun x y z =>
  let v0 := M (M x z) z
  let v1 := M (M y x) x
  T (T (T (T (h x y x) (h v1 x z)) (h v0 v1 y)) (C (C (S (h y y x)) (R y)) (R v0))) (S (h v0 y y))

@[equational_result]
theorem Equation1374_implies_Equation4146 (G: Type _) [Magma G] (h: Equation1374 G) : Equation4146 G := fun x y z =>
  let v0 := M x z
  let v1 := M (M v0 x) v0
  T (C (R x) (T (h y v1 z) (C (R v1) (C (C (S (h v0 z x)) (R z)) (R y))))) (S (h (M (M v0 z) y) x v0))

@[equational_result]
theorem Equation1507_implies_Equation16 (G: Type _) [Magma G] (h: Equation1507 G) : Equation16 G := fun x y =>
  let v0 := M y x
  let v1 := M y v0
  T (T (h x y x) (C (T (C (h y v0 y) (h x y v0)) (S (h (M y v1) (M v0 y) v0))) (R (M x (M x y))))) (S (h v1 y x))

@[equational_result]
theorem Equation2068_implies_Equation2880 (G: Type _) [Magma G] (h: Equation2068 G) : Equation2880 G := fun x y z =>
  let v0 := M y y
  let v1 := M x v0
  let v2 := M (M v1 z) z
  T (T (h x v0 v2) (C (C (h v1 z y) (R v0)) (R (M v2 v2)))) (S (h v2 v0 v2))

@[equational_result]
theorem Equation2552_implies_Equation16 (G: Type _) [Magma G] (h: Equation2552 G) : Equation16 G := fun x y =>
  let v0 := M y x
  have h1 := S (h y x v0)
  let v2 := M x (M (M x v0) y)
  T (h x v2 v0) (C (T (C (R v2) (C h1 (R x))) h1) (R v0))

@[equational_result]
theorem Equation2979_implies_Equation692 (G: Type _) [Magma G] (h: Equation2979 G) : Equation692 G := fun x y z =>
  let v0 := M z y
  let v1 := M x (M v0 z)
  let v2 := M v1 x
  T (h x z v1) (C (T (C (C (h z x v0) (R v2)) (R z)) (S (h y v2 z))) (R v1))

@[equational_result]
theorem Equation3370_implies_Equation3534 (G: Type _) [Magma G] (h: Equation3370 G) : Equation3534 G := fun x y z =>
  let v0 := M z y
  let v1 := M v0 z
  let v2 := M x (M x x)
  T (T (T (T (h x y x) (h y v2 z)) (C (R v2) (h z v0 v0))) (S (h v1 v2 v0))) (S (h x v1 x))

@[equational_result]
theorem Equation3622_implies_Equation41 (G: Type _) [Magma G] (h: Equation3622 G) : Equation41 G := fun x y z =>
  have h0 := h y z x
  have h1 := R x
  T (T (T (h x x x) (C h1 (T (T (h (M x x) x x) (S (h (M y z) x x))) (C h0 h1)))) (S (h x (M (M x z) x) x))) (S h0)

@[equational_result]
theorem Equation3776_implies_Equation3331 (G: Type _) [Magma G] (h: Equation3776 G) : Equation3331 G := fun x y z =>
  let v0 := M y z
  let v1 := M z v0
  T (T (h x y y) (C (T (T (h y y v0) (C (R (M y v0)) (h v0 y z))) (S (h v1 y v0))) (R (M y x)))) (S (h x v1 y))

@[equational_result]
theorem Equation3787_implies_Equation41 (G: Type _) [Magma G] (h: Equation3787 G) : Equation41 G := fun x y z =>
  let v0 := M y x
  have h1 := h x x x
  let v2 := M x x
  T (T (T (T h1 (h v2 v2 x)) (S (h v2 v0 x))) (C (T h1 (S (h x y x))) (R v0))) (S (h y z x))

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
theorem Equation1131_implies_Equation2383 (G: Type _) [Magma G] (h: Equation1131 G) : Equation2383 G := fun x y z =>
  let v0 := M y x
  let v1 := M (M y (M z v0)) z
  have h2 := R v1
  T (T (h x v1 y) (C h2 (C (C h2 (h v0 y z)) (R y)))) (S (h v1 v1 y))

@[equational_result]
theorem Equation1181_implies_Equation2349 (G: Type _) [Magma G] (h: Equation1181 G) : Equation2349 G := fun x y z =>
  let v0 := M z x
  let v1 := M (M y (M y v0)) z
  have h2 := R v1
  T (T (h x v1 z) (C h2 (C (C (R z) (h v0 z y)) h2))) (S (h v1 v1 z))

@[equational_result]
theorem Equation2532_implies_Equation2 (G: Type _) [Magma G] (h: Equation2532 G) : Equation2 G := fun x y =>
  let v0 := M x (M (M x x) x)
  let v1 := M x (M (M x v0) v0)
  T (T (h x x x) (C (T (h v0 x x) (C (R v1) (T (h x x y) (C (h v0 x y) (R y))))) (R x))) (S (h y v1 x))

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
theorem Equation3380_implies_Equation4374 (G: Type _) [Magma G] (h: Equation3380 G) : Equation4374 G := fun x y z w =>
  have h0 := h y z x
  let v1 := M y z
  have h2 := R x
  T (h x v1 w) (C (R w) (T (T (C h2 (C h2 h0)) (S (h x (M y v1) x))) (S h0)))

@[equational_result]
theorem Equation3591_implies_Equation3740 (G: Type _) [Magma G] (h: Equation3591 G) : Equation3740 G := fun x y z =>
  let v0 := M x z
  let v1 := M v0 v0
  T (T (h x y v0) (h v0 (M (M x v0) y) v0)) (C (R v0) (T (C (R v1) (C (h x v0 z) (R y))) (S (h z y v1))))

@[equational_result]
theorem Equation3758_implies_Equation4343 (G: Type _) [Magma G] (h: Equation3758 G) : Equation4343 G := fun x y =>
  let v0 := M x x
  let v1 := M y y
  have h2 := h x x
  T (T (T (T (h x v1) (C (R (M v1 v1)) h2)) (S (h v0 v1))) (C h2 (R v1))) (S (h y v0))

@[equational_result]
theorem Equation3758_implies_Equation4608 (G: Type _) [Magma G] (h: Equation3758 G) : Equation4608 G := fun x y =>
  let v0 := M y y
  have h1 := h y y
  let v2 := M x x
  T (T (T (T (h v2 y) (C h1 (R (M v2 v2)))) (S (h v2 v0))) (C (R v2) h1)) (S (h v0 x))

@[equational_result]
theorem Equation3804_implies_Equation3729 (G: Type _) [Magma G] (h: Equation3804 G) : Equation3729 G := fun x y z =>
  T (h x y x) (C (R (M x y)) (T (T (T (h x x z) (h (M z x) (M x z) (M z z))) (C (S (h x z z)) (S (h z x z)))) (S (h z z x))))

@[equational_result]
theorem Equation3940_implies_Equation3740 (G: Type _) [Magma G] (h: Equation3940 G) : Equation3740 G := fun x y z =>
  let v0 := M z y
  let v1 := M v0 v0
  T (T (h x y v0) (h (M x (M v0 y)) v0 v0)) (C (T (C (C (R x) (h v0 y z)) (R v1)) (S (h x z v1))) (R v0))

@[equational_result]
theorem Equation4176_implies_Equation4226 (G: Type _) [Magma G] (h: Equation4176 G) : Equation4226 G := fun x y z =>
  let v0 := M (M z z) x
  let v1 := M y y
  T (T (h x y y) (C (T (T (h v1 x z) (C (C (h x z z) (R v1)) (R z))) (S (h v1 v0 z))) (R y))) (S (h v0 y y))

@[equational_result]
theorem Equation4182_implies_Equation3997 (G: Type _) [Magma G] (h: Equation4182 G) : Equation3997 G := fun x y z =>
  let v0 := M x z
  let v1 := M z v0
  let v2 := M (M y x) x
  T (T (T (T (h x y x) (h v2 x z)) (C (h v0 z v0) (R v2))) (S (h v2 v1 v0))) (S (h v1 y x))

@[equational_result]
theorem Equation4182_implies_Equation4216 (G: Type _) [Magma G] (h: Equation4182 G) : Equation4216 G := fun x y z =>
  have h0 := R x
  let v1 := M (M y x) x
  T (T (T (T (h x y y) (C (C (h y y x) (R y)) h0)) (S (h x v1 y))) (h x v1 z)) (C (C (S (h z y x)) (R z)) h0)

@[equational_result]
theorem Equation949_implies_Equation546 (G: Type _) [Magma G] (h: Equation949 G) : Equation546 G := fun x y z =>
  let v0 := M z y
  let v1 := M x v0
  have h2 := h x y v1
  T h2 (C (R y) (T (h (M (M v1 x) (M y v1)) z y) (C (R z) (C (S h2) (R v0)))))

@[equational_result]
theorem Equation1165_implies_Equation2399 (G: Type _) [Magma G] (h: Equation1165 G) : Equation2399 G := fun x y z =>
  let v0 := M z x
  let v1 := M (M y (M z v0)) y
  have h2 := R v1
  T (T (h x z v1) (C (R z) (C (C h2 (h v0 z y)) h2))) (S (h v1 z v1))

@[equational_result]
theorem Equation1587_implies_Equation1368 (G: Type _) [Magma G] (h: Equation1587 G) : Equation1368 G := fun x y z =>
  let v0 := M z y
  let v1 := M v0 x
  let v2 := M v1 z
  let v3 := M v2 v0
  T (h x v3 v1) (C (T (C (R v3) (h v1 z y)) (S (h y v2 v0))) (S (h v2 v0 x)))

@[equational_result]
theorem Equation2103_implies_Equation19 (G: Type _) [Magma G] (h: Equation2103 G) : Equation19 G := fun x y z =>
  let v0 := M z x
  let v1 := M y v0
  T (T (T (h x (M x v1) z) (C (S (h v1 x x)) (R v0))) (C (h v1 v1 v1) (h v0 y y))) (S (h v1 (M v1 v1) (M v1 y)))

@[equational_result]
theorem Equation2196_implies_Equation26 (G: Type _) [Magma G] (h: Equation2196 G) : Equation26 G := fun x y =>
  let v0 := M x y
  let v1 := M v0 y
  T (T (h x y x) (C (R (M (M y x) x)) (T (C (h x y v0) (h y v0 y)) (S (h (M v1 y) (M y v0) v0))))) (S (h v1 y x))

@[equational_result]
theorem Equation2279_implies_Equation3334 (G: Type _) [Magma G] (h: Equation2279 G) : Equation3334 G := fun x y z =>
  let v0 := M z y
  let v1 := M v0 (M y v0)
  T (C (T (h x z v1) (C (C (R x) (C (R z) (S (h v0 y z)))) (R v1))) (R y)) (S (h (M x (M z v0)) v0 y))

@[equational_result]
theorem Equation2308_implies_Equation2113 (G: Type _) [Magma G] (h: Equation2308 G) : Equation2113 G := fun x y z =>
  let v0 := M y z
  let v1 := M y x
  have h2 := h x v1 v0
  T h2 (C (T (h (M v1 (M x (M v1 v0))) y z) (C (C (R y) (S h2)) (R z))) (R v0))

@[equational_result]
theorem Equation2370_implies_Equation749 (G: Type _) [Magma G] (h: Equation2370 G) : Equation749 G := fun x y z =>
  let v0 := M x z
  let v1 := M y (M z (M v0 y))
  have h2 := R v1
  T (T (h x z v1) (C (C (R z) (C h2 (h v0 y z))) h2)) (S (h v1 z v1))

@[equational_result]
theorem Equation2519_implies_Equation1304 (G: Type _) [Magma G] (h: Equation2519 G) : Equation1304 G := fun x y z =>
  let v0 := M x z
  let v1 := M y (M (M v0 z) y)
  have h2 := R v1
  T (T (h x v1 z) (C (C h2 (C (h v0 y z) h2)) (R z))) (S (h v1 v1 z))

@[equational_result]
theorem Equation2714_implies_Equation3794 (G: Type _) [Magma G] (h: Equation2714 G) : Equation3794 G := fun x y z =>
  let v0 := M (M z x) (M z y)
  have h1 := S (h v0 x x)
  T (C (T (h x (M (M x v0) (M x x)) x) (C (C h1 h1) (h x z y))) (R y)) (S (h v0 v0 y))

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
theorem Equation1724_implies_Equation4631 (G: Type _) [Magma G] (h: Equation1724 G) : Equation4631 G := fun x y z =>
  let v0 := M (M x z) x
  have h1 := R (M x x)
  let v2 := M (M x y) x
  T (T (T (h v2 x v2) (C h1 (S (h x v2 y)))) (C h1 (h x v0 z))) (S (h v0 x v0))

@[equational_result]
theorem Equation1855_implies_Equation4316 (G: Type _) [Magma G] (h: Equation1855 G) : Equation4316 G := fun x y z =>
  let v0 := M x (M z x)
  have h1 := R (M x x)
  let v2 := M x (M y x)
  T (T (T (h v2 v2 x) (C (S (h x y v2)) h1)) (C (h x z v0) h1)) (S (h v0 v0 x))

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
theorem Equation2888_implies_Equation2076 (G: Type _) [Magma G] (h: Equation2888 G) : Equation2076 G := fun x y z =>
  let v0 := M y z
  let v1 := M x y
  have h2 := h x v1 v0
  T h2 (C (T (h (M (M x (M v1 v0)) v1) y z) (C (C (S h2) (R y)) (R z))) (R v0))

@[equational_result]
theorem Equation3104_implies_Equation2 (G: Type _) [Magma G] (h: Equation3104 G) : Equation2 G := fun x y =>
  have h0 := S (h y (M x y) x)
  have h1 := R x
  have h2 := C (h y x y) h1
  T (T (T (h x (M (M (M y y) y) y) x) (C (T (T (C (T (T (C (S (h y y x)) h1) h2) h0) h1) h2) h0) h1)) h2) h0

@[equational_result]
theorem Equation3823_implies_Equation3692 (G: Type _) [Magma G] (h: Equation3823 G) : Equation3692 G := fun x y z =>
  let v0 := M y y
  let v1 := M x x
  have h2 := R v1
  T (T (T (T (h x x y) (h v0 v1 x)) (C h2 (S (h y y x)))) (C h2 (h y y z))) (S (h v0 (M z z) x))

@[equational_result]
theorem Equation546_implies_Equation962 (G: Type _) [Magma G] (h: Equation546 G) : Equation962 G := fun x y z =>
  let v0 := M x z
  let v1 := M z y
  let v2 := M v1 v0
  T (h x y z) (C (R y) (T (C (R z) (C (R x) (T (h v1 v2 v0) (C (R v2) (S (h v0 v0 v1)))))) (S (h v2 z x))))

@[equational_result]
theorem Equation928_implies_Equation3737 (G: Type _) [Magma G] (h: Equation928 G) : Equation3737 G := fun x y z =>
  let v0 := M (M x z) (M y z)
  have h1 := S (h v0 y x)
  T (C (R x) (T (h y y (M (M y x) (M v0 x))) (C (h y x z) (C h1 h1)))) (S (h v0 x v0))

@[equational_result]
theorem Equation1718_implies_Equation4622 (G: Type _) [Magma G] (h: Equation1718 G) : Equation4622 G := fun x y z =>
  let v0 := M z z
  let v1 := M v0 y
  let v2 := M (M y y) y
  T (C (R (M x x)) (T (h y v1) (C (R (M v1 v1)) (T (h v2 z) (C (R v0) (S (h y v2))))))) (S (h v1 x))

@[equational_result]
theorem Equation2116_implies_Equation2316 (G: Type _) [Magma G] (h: Equation2116 G) : Equation2316 G := fun x y z =>
  let v0 := M z y
  let v1 := M x v0
  let v2 := M y v1
  let v3 := M v0 v2
  T (h x v3 v1) (C (S (h v2 v0 x)) (T (C (h v1 y z) (R v3)) (S (h z v2 v0))))

@[equational_result]
theorem Equation2310_implies_Equation23 (G: Type _) [Magma G] (h: Equation2310 G) : Equation23 G := fun x =>
  have h0 := R x
  let v1 := M x x
  let v2 := M x v1
  let v3 := M x (M v1 v2)
  T (h x v3 (M x v2)) (C (T (C (R v3) (C h0 (S (h x x x)))) (S (h v1 x x))) h0)

@[equational_result]
theorem Equation2805_implies_Equation1587 (G: Type _) [Magma G] (h: Equation2805 G) : Equation1587 G := fun x y z =>
  let v0 := M x y
  let v1 := M z v0
  let v2 := M y z
  let v3 := M v0 v2
  T (h x v1 v3) (C (T (C (R (M v1 v3)) (S (h z x y))) (S (h v2 z v0))) (R v1))

@[equational_result]
theorem Equation3364_implies_Equation4146 (G: Type _) [Magma G] (h: Equation3364 G) : Equation4146 G := fun x y z =>
  let v0 := M x z
  let v1 := M x v0
  let v2 := M v0 z
  T (T (h x y v0) (C (R y) (T (h v0 v1 z) (C (R v1) (T (h z v2 v0) (C (R v2) (S (h x v0 z)))))))) (S (h v2 y v1))

@[equational_result]
theorem Equation3370_implies_Equation3567 (G: Type _) [Magma G] (h: Equation3370 G) : Equation3567 G := fun x y z =>
  let v0 := M z x
  have h1 := R y
  let v2 := M z v0
  T (T (T (T (h x y x) (C h1 (C (R x) (h x x z)))) (S (h v2 y x))) (h v2 y z)) (C h1 (S (h v0 z z)))

@[equational_result]
theorem Equation3417_implies_Equation4007 (G: Type _) [Magma G] (h: Equation3417 G) : Equation4007 G := fun x y z =>
  let v0 := M y x
  have h1 := R v0
  have h2 := h x y v0
  T (T (T h2 (C h1 (h v0 v0 v0))) (C h1 (T (C h1 (S h2)) (C h1 (h x y z))))) (S (h (M z v0) z v0))

@[equational_result]
theorem Equation3758_implies_Equation3545 (G: Type _) [Magma G] (h: Equation3758 G) : Equation3545 G := fun x y =>
  let v0 := M x x
  have h1 := h x x
  T (T (T (T (h x y) (h (M y y) v0)) (C (R (M v0 v0)) (S (h y y)))) (S (h y v0))) (C (R y) (T (T h1 (C (R v0) h1)) (S (h v0 x))))

@[equational_result]
theorem Equation3790_implies_Equation4490 (G: Type _) [Magma G] (h: Equation3790 G) : Equation4490 G := fun x y z =>
  let v0 := M z x
  have h1 := S (h y y y)
  let v2 := M y y
  T (T (T (T (h x v2 z) (C (R v0) h1)) (h v0 v2 x)) (C (R (M x v0)) h1)) (S (h v0 y x))

@[equational_result]
theorem Equation3791_implies_Equation4640 (G: Type _) [Magma G] (h: Equation3791 G) : Equation4640 G := fun x y z =>
  let v0 := M y z
  let v1 := M x y
  T (T (T (h v1 x v0) (h (M v0 v1) (M x v0) (M v1 x))) (C (S (h x v0 v1)) (T (S (h v0 v1 x)) (S (h z x y))))) (S (h v0 z x))

@[equational_result]
theorem Equation4182_implies_Equation4013 (G: Type _) [Magma G] (h: Equation4182 G) : Equation4013 G := fun x y z =>
  have h0 := R x
  let v1 := M y z
  let v2 := M v1 z
  T (T (T (T (h x y y) (C (C (h y y z) (R y)) h0)) (S (h x v2 y))) (h x v2 z)) (C (S (h z v1 z)) h0)

@[equational_result]
theorem Equation4216_implies_Equation3334 (G: Type _) [Magma G] (h: Equation4216 G) : Equation3334 G := fun x y z =>
  let v0 := M z y
  let v1 := M v0 y
  let v2 := M z v0
  T (T (h x y v0) (C (T (h v1 v0 z) (C (T (h v2 z v0) (C (S (h v0 y z)) (R v2))) (R v1))) (R x))) (S (h x v2 v1))

@[equational_result]
theorem Equation556_implies_Equation1355 (G: Type _) [Magma G] (h: Equation556 G) : Equation1355 G := fun x y z =>
  let v0 := M z x
  let v1 := M v0 y
  have h2 := R y
  T (h x y v1) (C h2 (C (R v1) (T (C h2 (C (R x) (T (h v1 y v1) (C h2 (S (h v0 v1 y)))))) (S (h z y x)))))

@[equational_result]
theorem Equation684_implies_Equation16 (G: Type _) [Magma G] (h: Equation684 G) : Equation16 G := fun x y =>
  let v0 := M x (M (M x x) x)
  let v1 := M y x
  have h2 := h x x x
  T (h x y x) (C (R y) (T (C (R x) (C (R v1) (T h2 (C h2 (R v0))))) (S (h v1 x v0))))

@[equational_result]
theorem Equation898_implies_Equation2116 (G: Type _) [Magma G] (h: Equation898 G) : Equation2116 G := fun x y z =>
  let v0 := M y x
  let v1 := M z y
  let v2 := M v0 z
  let v3 := M v1 v0
  T (h x v2 v3) (C (R v2) (T (C (S (h z x y)) (R (M v3 v2))) (S (h v1 z v0))))

@[equational_result]
theorem Equation1080_implies_Equation2 (G: Type _) [Magma G] (h: Equation1080 G) : Equation2 G := fun x y =>
  let v0 := M (M x (M x x)) x
  let v1 := M (M v0 (M v0 x)) x
  T (T (h x x x) (C (R x) (T (h v0 x x) (C (T (h x y x) (C (R y) (h v0 y x))) (R v1))))) (S (h y x v1))

@[equational_result]
theorem Equation1507_implies_Equation4305 (G: Type _) [Magma G] (h: Equation1507 G) : Equation4305 G := fun x y z =>
  let v0 := M y z
  let v1 := M y (M y v0)
  T (T (h (M x (M x y)) v0 y) (C (S (h z y x)) (R v1))) (C (R z) (T (h v1 (M v0 y) v0) (C (S (h y v0 y)) (S (h z y v0)))))

@[equational_result]
theorem Equation1571_implies_Equation3940 (G: Type _) [Magma G] (h: Equation1571 G) : Equation3940 G := fun x y z =>
  let v0 := M x (M z y)
  have h1 := S (h v0 x y)
  let v2 := M x y
  T (T (h v2 v2 (M x (M v0 y))) (C h1 (C (R v2) h1))) (C (R v0) (S (h z x y)))

@[equational_result]
theorem Equation1774_implies_Equation3895 (G: Type _) [Magma G] (h: Equation1774 G) : Equation3895 G := fun x y z =>
  let v0 := M y z
  let v1 := M (M y v0) z
  let v2 := M (M v0 x) v1
  have h3 := h x v0 v1
  T (C (T h3 (C (S (h v0 y z)) (R v2))) h3) (S (h v1 v0 v2))

@[equational_result]
theorem Equation2944_implies_Equation4026 (G: Type _) [Magma G] (h: Equation2944 G) : Equation4026 G := fun x y z =>
  let v0 := M z (M z y)
  let v1 := M v0 x
  let v2 := M v0 v1
  have h3 := R y
  T (C (T (h x v0 y) (C (C (R v2) (h y z v1)) h3)) h3) (S (h v1 v2 y))

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
theorem Equation3804_implies_Equation43 (G: Type _) [Magma G] (h: Equation3804 G) : Equation43 G := fun x y =>
  have h0 := h y x x
  let v1 := M x x
  let v2 := M y x
  have h3 := h x y x
  T (T (T (T (T h3 (C h3 (h x x y))) (S (h v2 v1 (M x y)))) (C h0 (h x x x))) (S (h v1 v2 v1))) (S h0)

@[equational_result]
theorem Equation4210_implies_Equation4656 (G: Type _) [Magma G] (h: Equation4210 G) : Equation4656 G := fun x y z =>
  let v0 := M x z
  let v1 := M x y
  T (T (h v1 y x) (C (T (T (T (C (h x y x) (R v1)) (S (h x x v1))) (h x x v0)) (C (S (h x z x)) (R v0))) (R x))) (S (h v0 z x))

@[equational_result]
theorem Equation711_implies_Equation3553 (G: Type _) [Magma G] (h: Equation711 G) : Equation3553 G := fun x y z =>
  let v0 := M (M x z) z
  let v1 := M y v0
  let v2 := M v1 v0
  have h3 := R x
  T (C h3 (T (h y x v0) (C h3 (C (h x v1 z) (R v2))))) (S (h v1 x v2))

@[equational_result]
theorem Equation778_implies_Equation1590 (G: Type _) [Magma G] (h: Equation778 G) : Equation1590 G := fun x y z =>
  let v0 := M y z
  let v1 := M v0 (M z (M y x))
  have h2 := h x v0 v1
  T h2 (C (R v0) (T (h (M v1 (M (M v1 v0) x)) z y) (C (R z) (C (R y) (S h2)))))

@[equational_result]
theorem Equation1230_implies_Equation8 (G: Type _) [Magma G] (h: Equation1230 G) : Equation8 G := fun x =>
  let v0 := M x x
  let v1 := M v0 x
  let v2 := M (M v1 v0) x
  have h3 := R x
  T (h x (M v1 x) v2) (C h3 (T (C (C (S (h x x x)) h3) (R v2)) (S (h v0 x x))))

@[equational_result]
theorem Equation2079_implies_Equation3331 (G: Type _) [Magma G] (h: Equation2079 G) : Equation3331 G := fun x y z =>
  let v0 := M y z
  let v1 := M x y
  let v2 := M v1 v0
  T (h v1 v0 z) (C (T (T (h (M v2 z) y v0) (C (S (h v2 z y)) (R (M v0 y)))) (S (h x y v0))) (R (M z v0)))

@[equational_result]
theorem Equation2113_implies_Equation3591 (G: Type _) [Magma G] (h: Equation2113 G) : Equation3591 G := fun x y z =>
  let v0 := M (M x z) y
  have h1 := S (h v0 x y)
  let v2 := M x y
  T (T (h v2 (M (M x v0) y) v2) (C (C h1 (R v2)) h1)) (C (S (h z x y)) (R v0))

@[equational_result]
theorem Equation3791_implies_Equation3534 (G: Type _) [Magma G] (h: Equation3791 G) : Equation3534 G := fun x y z =>
  let v0 := M z y
  let v1 := M v0 z
  T (T (h x y v0) (C (R (M v0 x)) (T (T (h y v0 z) (h v0 v1 (M y v0))) (C (S (h v0 z y)) (S (h z y v0)))))) (S (h x v1 v0))

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
theorem Equation2958_implies_Equation26 (G: Type _) [Magma G] (h: Equation2958 G) : Equation26 G := fun x y =>
  let v0 := M (M x (M x x)) x
  let v1 := M x y
  have h2 := h x x x
  T (h x x y) (C (T (C (C (T h2 (C (R v0) h2)) (R v1)) (R x)) (S (h v1 v0 x))) (R y))

@[equational_result]
theorem Equation3758_implies_Equation3964 (G: Type _) [Magma G] (h: Equation3758 G) : Equation3964 G := fun x y =>
  let v0 := M y y
  have h1 := h y y
  T (T (T (T (h x y) (h v0 (M x x))) (C (S (h x x)) (R (M v0 v0)))) (S (h v0 x))) (C (T (T h1 (C h1 (R v0))) (S (h y v0))) (R x))

