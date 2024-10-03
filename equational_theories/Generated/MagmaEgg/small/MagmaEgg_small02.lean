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
theorem Equation3146_implies_Equation2 (G: Type _) [Magma G] (h: Equation3146 G) : Equation2 G := fun x y =>
  let v0 := M y y
  have h1 := R v0
  T (T (T (h x v0 y) (C (S (h v0 y x)) h1)) (C (h v0 y y) h1)) (S (h y v0 y))

@[equational_result]
theorem Equation3363_implies_Equation4374 (G: Type _) [Magma G] (h: Equation3363 G) : Equation4374 G := fun x y z w =>
  let v0 := M y z
  have h1 := R v0
  T (T (T (h x v0 z) (C h1 (S (h y z x)))) (C h1 (h y z w))) (S (h w v0 z))

@[equational_result]
theorem Equation3396_implies_Equation41 (G: Type _) [Magma G] (h: Equation3396 G) : Equation41 G := fun x y z =>
  let v0 := M x x
  let v1 := M z (M y y)
  T (T (T (h x x y) (C (R y) (h x v0 v1))) (S (h v0 v1 y))) (S (h y z v0))

@[equational_result]
theorem Equation3567_implies_Equation3364 (G: Type _) [Magma G] (h: Equation3567 G) : Equation3364 G := fun x y z =>
  let v0 := M x z
  T (h x y v0) (C (R y) (T (T (h (M v0 x) v0 z) (C (R v0) (C (S (h z z x)) (R z)))) (S (h z v0 z))))

@[equational_result]
theorem Equation3617_implies_Equation3820 (G: Type _) [Magma G] (h: Equation3617 G) : Equation3820 G := fun x y z =>
  let v0 := M z z
  T (h x y v0) (C (R v0) (T (T (h (M v0 x) y z) (C (R z) (C (S (h z x z)) (R y)))) (S (h x y z))))

@[equational_result]
theorem Equation4129_implies_Equation4672 (G: Type _) [Magma G] (h: Equation4129 G) : Equation4672 G := fun x y z w =>
  let v0 := M x y
  have h1 := h x y v0
  T (T (T (C h1 (R z)) (S (h v0 x z))) (h v0 x w)) (C (S h1) (R w))

@[equational_result]
theorem Equation4197_implies_Equation4512 (G: Type _) [Magma G] (h: Equation4197 G) : Equation4512 G := fun x y z =>
  let v0 := M y z
  T (h x v0 z) (C (T (C (h z x y) (R v0)) (S (h x y v0))) (R z))

@[equational_result]
theorem Equation684_implies_Equation14 (G: Type _) [Magma G] (h: Equation684 G) : Equation14 G := fun x y =>
  have h0 := S (h y y x)
  let v1 := M y (M (M y x) x)
  T (h x y v1) (C (R y) (C (R x) (T (C h0 (R v1)) h0)))

@[equational_result]
theorem Equation828_implies_Equation49 (G: Type _) [Magma G] (h: Equation828 G) : Equation49 G := fun x y =>
  let v0 := M x x
  T (h x (M v0 v0) y) (C (R x) (C (S (h x x x)) (R (M y x))))

@[equational_result]
theorem Equation1120_implies_Equation2338 (G: Type _) [Magma G] (h: Equation1120 G) : Equation2338 G := fun x y =>
  let v0 := M y x
  have h1 := R y
  T (T (h x y) (C h1 (C (C h1 (h v0 y)) h1))) (S (h (M (M y (M y v0)) y) y))

@[equational_result]
theorem Equation1122_implies_Equation1934 (G: Type _) [Magma G] (h: Equation1122 G) : Equation1934 G := fun x y =>
  let v0 := M y (M y y)
  have h1 := h x v0
  T h1 (C (R v0) (T (h (M (M v0 (M v0 v0)) x) y) (C (R y) (S h1))))

@[equational_result]
theorem Equation1577_implies_Equation968 (G: Type _) [Magma G] (h: Equation1577 G) : Equation968 G := fun x y z =>
  let v0 := M z y
  let v1 := M v0 (M z x)
  T (T (h x v0 z) (C (R (M v0 z)) (h v1 z y))) (S (h (M y v1) v0 z))

@[equational_result]
theorem Equation1590_implies_Equation934 (G: Type _) [Magma G] (h: Equation1590 G) : Equation934 G := fun x y z =>
  let v0 := M y z
  let v1 := M v0 (M z x)
  T (T (h x z v0) (C (R (M z v0)) (h v1 y z))) (S (h (M y v1) z v0))

@[equational_result]
theorem Equation2076_implies_Equation2685 (G: Type _) [Magma G] (h: Equation2076 G) : Equation2685 G := fun x y z =>
  let v0 := M z y
  let v1 := M (M x y) v0
  T (T (h x y v0) (C (h v1 z y) (R (M y v0)))) (S (h (M v1 z) y v0))

@[equational_result]
theorem Equation2196_implies_Equation4640 (G: Type _) [Magma G] (h: Equation2196 G) : Equation4640 G := fun x y z =>
  let v0 := M x y
  T (C (T (C (h x y v0) (h y v0 z)) (S (h (M (M v0 z) z) (M y v0) v0))) (h x y z)) (S (h (M (M y z) z) v0 z))

@[equational_result]
theorem Equation2348_implies_Equation2 (G: Type _) [Magma G] (h: Equation2348 G) : Equation2 G := fun x y =>
  let v0 := M x x
  have h1 := R x
  T (T (h x x x) (C (C h1 (C h1 (h v0 y y))) h1)) (S (h y x (M y (M y (M y v0)))))

@[equational_result]
theorem Equation2364_implies_Equation218 (G: Type _) [Magma G] (h: Equation2364 G) : Equation218 G := fun x y =>
  let v0 := M x x
  T (h x y (M x (M x (M v0 v0)))) (C (C (R y) (S (h v0 x x))) (R x))

@[equational_result]
theorem Equation2964_implies_Equation31 (G: Type _) [Magma G] (h: Equation2964 G) : Equation31 G := fun x y =>
  have h0 := S (h y x x)
  let v1 := M (M x (M x x)) x
  T (h x v1 y) (C (C (T (C (R v1) h0) h0) (R y)) (R x))

@[equational_result]
theorem Equation3128_implies_Equation2538 (G: Type _) [Magma G] (h: Equation3128 G) : Equation2538 G := fun x y z =>
  let v0 := M (M y x) z
  let v1 := M y v0
  T (h x y z) (C (T (C (h v0 y v1) (R y)) (S (h v1 v1 y))) (R z))

@[equational_result]
theorem Equation3350_implies_Equation3943 (G: Type _) [Magma G] (h: Equation3350 G) : Equation3943 G := fun x y z =>
  let v0 := M y y
  let v1 := M x (M z z)
  T (T (h x y y) (C (R y) (T (h x v0 z) (h v0 v1 y)))) (S (h v1 y v0))

@[equational_result]
theorem Equation3370_implies_Equation3997 (G: Type _) [Magma G] (h: Equation3370 G) : Equation3997 G := fun x y z =>
  let v0 := M x z
  T (T (h x y z) (C (R y) (T (T (C (R z) (h z x x)) (S (h v0 z x))) (h v0 z z)))) (S (h (M z v0) y z))

@[equational_result]
theorem Equation3776_implies_Equation3534 (G: Type _) [Magma G] (h: Equation3776 G) : Equation3534 G := fun x y z =>
  let v0 := M z y
  T (T (h x y v0) (C (h y v0 z) (R (M v0 x)))) (S (h x (M v0 z) v0))

@[equational_result]
theorem Equation3914_implies_Equation383 (G: Type _) [Magma G] (h: Equation3914 G) : Equation383 G := fun x y z w =>
  let v0 := M x z
  T (T (T (h x y) (C (T (h x (M x x)) (S (h x z))) (R x))) (h v0 x)) (S (h v0 w))

@[equational_result]
theorem Equation3924_implies_Equation3253 (G: Type _) [Magma G] (h: Equation3924 G) : Equation3253 G := fun x =>
  have h0 := R x
  have h1 := h x x
  T (T h1 (C (C h0 h1) h0)) (S (h x (M x (M x x))))

@[equational_result]
theorem Equation4166_implies_Equation41 (G: Type _) [Magma G] (h: Equation4166 G) : Equation41 G := fun x y z =>
  let v0 := M x x
  let v1 := M (M z z) y
  T (T (T (h x x z) (C (h v0 x v1) (R z))) (S (h v1 v0 z))) (S (h y z v0))

@[equational_result]
theorem Equation4182_implies_Equation3331 (G: Type _) [Magma G] (h: Equation4182 G) : Equation3331 G := fun x y z =>
  let v0 := M y z
  T (T (h x y z) (C (h v0 z v0) (R x))) (S (h x (M z v0) v0))

@[equational_result]
theorem Equation4182_implies_Equation3534 (G: Type _) [Magma G] (h: Equation4182 G) : Equation3534 G := fun x y z =>
  let v0 := M z y
  T (T (h x y z) (C (T (T (C (h y z y) (R z)) (S (h z v0 y))) (h z v0 z)) (R x))) (S (h x (M v0 z) z))

@[equational_result]
theorem Equation4201_implies_Equation41 (G: Type _) [Magma G] (h: Equation4201 G) : Equation41 G := fun x y z =>
  let v0 := M y z
  have h1 := R v0
  T (T (h x x v0) (C (C (T (h v0 x x) (S (h v0 y x))) h1) h1)) (S (h y z v0))

@[equational_result]
theorem Equation647_implies_Equation11 (G: Type _) [Magma G] (h: Equation647 G) : Equation11 G := fun x y =>
  have h0 := S (h y x x)
  let v1 := M x (M (M x x) x)
  T (h x y v1) (C (R x) (C (R y) (T (C h0 (R v1)) h0)))

@[equational_result]
theorem Equation695_implies_Equation1746 (G: Type _) [Magma G] (h: Equation695 G) : Equation1746 G := fun x y z =>
  let v0 := M (M z z) x
  let v1 := M (M y y) v0
  T (T (h x v0 v1) (C (R v0) (S (h (M v1 v1) x z)))) (S (h v1 v0 y))

@[equational_result]
theorem Equation710_implies_Equation2 (G: Type _) [Magma G] (h: Equation710 G) : Equation2 G := fun x y =>
  let v0 := M x x
  have h1 := R x
  T (T (h x x x) (C h1 (C h1 (C (h v0 y x) h1)))) (S (h y x (M y (M (M v0 x) y))))

@[equational_result]
theorem Equation1455_implies_Equation2267 (G: Type _) [Magma G] (h: Equation1455 G) : Equation2267 G := fun x y =>
  let v0 := M y (M y y)
  let v1 := M x v0
  T (T (h x v0) (C (h v1 y) (R (M v0 (M v0 v0))))) (S (h (M v1 y) v0))

@[equational_result]
theorem Equation1590_implies_Equation778 (G: Type _) [Magma G] (h: Equation1590 G) : Equation778 G := fun x y z =>
  let v0 := M z y
  let v1 := M v0 x
  T (T (h x v0 x) (C (R v1) (C (R x) (h v1 z y)))) (S (h (M y (M z v1)) v0 x))

@[equational_result]
theorem Equation1658_implies_Equation2470 (G: Type _) [Magma G] (h: Equation1658 G) : Equation2470 G := fun x y =>
  let v0 := M (M y y) y
  let v1 := M x v0
  T (T (h x v0) (C (h v1 y) (R (M (M v0 v0) v0)))) (S (h (M v1 y) v0))

@[equational_result]
theorem Equation1902_implies_Equation1155 (G: Type _) [Magma G] (h: Equation1902 G) : Equation1155 G := fun x y z =>
  let v0 := M z (M x z)
  let v1 := M y (M v0 y)
  T (T (h x z x) (C (h v0 y v1) (R (M x x)))) (S (h v1 v1 x))

@[equational_result]
theorem Equation1934_implies_Equation1122 (G: Type _) [Magma G] (h: Equation1934 G) : Equation1122 G := fun x y =>
  let v0 := M y (M y y)
  let v1 := M v0 x
  T (T (h x v0) (C (R (M v0 (M v0 v0))) (h v1 y))) (S (h (M y v1) v0))

@[equational_result]
theorem Equation2079_implies_Equation2677 (G: Type _) [Magma G] (h: Equation2079 G) : Equation2677 G := fun x y z =>
  let v0 := M y z
  let v1 := M (M x y) v0
  T (T (h x y v0) (C (h v1 z y) (R (M v0 y)))) (S (h (M v1 z) y v0))

@[equational_result]
theorem Equation2199_implies_Equation1340 (G: Type _) [Magma G] (h: Equation2199 G) : Equation1340 G := fun x y z =>
  let v0 := M (M y z) z
  let v1 := M v0 x
  T (T (h x v0 x) (C (R (M v1 x)) (h v1 y z))) (S (h (M y v1) v0 x))

@[equational_result]
theorem Equation2470_implies_Equation1658 (G: Type _) [Magma G] (h: Equation2470 G) : Equation1658 G := fun x y =>
  let v0 := M (M y y) y
  have h1 := h x v0
  T h1 (C (T (h (M x (M (M v0 v0) v0)) y) (C (S h1) (R y))) (R v0))

@[equational_result]
theorem Equation3330_implies_Equation4360 (G: Type _) [Magma G] (h: Equation3330 G) : Equation4360 G := fun x y z w =>
  let v0 := M z z
  have h1 := R x
  T (T (T (C h1 (h y z v0)) (S (h x v0 y))) (h x v0 w)) (C h1 (S (h w z v0)))

@[equational_result]
theorem Equation3756_implies_Equation3820 (G: Type _) [Magma G] (h: Equation3756 G) : Equation3820 G := fun x y z =>
  let v0 := M x y
  let v1 := M z z
  let v2 := M v1 v0
  T (T (h x y v2) (C (h y x z) (R (M v2 v2)))) (S (h v1 v0 v2))

@[equational_result]
theorem Equation3770_implies_Equation4362 (G: Type _) [Magma G] (h: Equation3770 G) : Equation4362 G := fun x y z =>
  let v0 := M y z
  let v1 := M x z
  T (T (T (h x v0 z) (h (M v0 z) v1 v0)) (C (R (M v1 v0)) (S (h y v0 z)))) (S (h y v1 v0))

@[equational_result]
theorem Equation4133_implies_Equation4672 (G: Type _) [Magma G] (h: Equation4133 G) : Equation4672 G := fun x y z w =>
  let v0 := M x y
  have h1 := R v0
  T (T (T (h v0 z x) (C (S (h x y z)) h1)) (C (h x y w) h1)) (S (h v0 w x))

@[equational_result]
theorem Equation910_implies_Equation504 (G: Type _) [Magma G] (h: Equation910 G) : Equation504 G := fun x y =>
  let v0 := M y y
  have h1 := h x y
  have h2 := R y
  T h1 (C h2 (T (h (M (M y x) v0) y) (C h2 (C (S h1) (R v0)))))

@[equational_result]
theorem Equation1072_implies_Equation19 (G: Type _) [Magma G] (h: Equation1072 G) : Equation19 G := fun x y z =>
  let v0 := M (M x (M x x)) x
  T (h x y) (C (R y) (T (h v0 z) (C (R z) (S (h x (M v0 (M v0 v0)))))))

@[equational_result]
theorem Equation1300_implies_Equation2 (G: Type _) [Magma G] (h: Equation1300 G) : Equation2 G := fun x y =>
  let v0 := M x x
  have h1 := R x
  T (T (h x x x) (C h1 (C (C (h v0 y y) h1) h1))) (S (h y x (M (M (M v0 y) y) y)))

@[equational_result]
theorem Equation1325_implies_Equation2137 (G: Type _) [Magma G] (h: Equation1325 G) : Equation2137 G := fun x y =>
  let v0 := M (M y y) y
  have h1 := h x v0
  T h1 (C (R v0) (T (h (M (M (M v0 v0) v0) x) y) (C (R y) (S h1))))

@[equational_result]
theorem Equation1334_implies_Equation1571 (G: Type _) [Magma G] (h: Equation1334 G) : Equation1571 G := fun x y z =>
  let v0 := M y z
  have h1 := h x v0 z
  T h1 (C (R v0) (T (h (M (M (M v0 z) x) z) y z) (C (R y) (C (S h1) (R z)))))

@[equational_result]
theorem Equation1368_implies_Equation1587 (G: Type _) [Magma G] (h: Equation1368 G) : Equation1587 G := fun x y z =>
  let v0 := M y z
  have h1 := h x v0 z
  T h1 (C (R v0) (T (h (M (M (M z v0) x) z) z y) (C (R z) (C (S h1) (R y)))))

@[equational_result]
theorem Equation1374_implies_Equation2186 (G: Type _) [Magma G] (h: Equation1374 G) : Equation2186 G := fun x y z =>
  let v0 := M (M y z) y
  have h1 := h x v0 y
  T h1 (C (R v0) (T (h (M (M (M y v0) y) x) z y) (C (R z) (S h1))))

@[equational_result]
theorem Equation1458_implies_Equation161 (G: Type _) [Magma G] (h: Equation1458 G) : Equation161 G := fun x y z =>
  let v0 := M y z
  let v1 := M z v0
  T (h x y v1) (C (R (M x y)) (C (R y) (T (C (R v1) (h y z y)) (S (h z v0 z)))))

@[equational_result]
theorem Equation1470_implies_Equation2271 (G: Type _) [Magma G] (h: Equation1470 G) : Equation2271 G := fun x y z =>
  let v0 := M y (M y z)
  let v1 := M x v0
  T (T (h x v0 x) (C (h v1 z y) (R (M x v1)))) (S (h (M v1 z) v0 x))

@[equational_result]
theorem Equation1528_implies_Equation716 (G: Type _) [Magma G] (h: Equation1528 G) : Equation716 G := fun x y =>
  let v0 := M y y
  let v1 := M v0 x
  T (T (h x v0) (C (R (M v0 v0)) (C (R v0) (h v1 y)))) (S (h (M y (M y v1)) v0))

@[equational_result]
theorem Equation1898_implies_Equation1086 (G: Type _) [Magma G] (h: Equation1898 G) : Equation1086 G := fun x y =>
  let v0 := M y y
  let v1 := M x v0
  T (T (h x v0) (C (C (R v0) (h v1 y)) (R (M v0 v0)))) (S (h (M y (M v1 y)) v0))

@[equational_result]
theorem Equation2079_implies_Equation2891 (G: Type _) [Magma G] (h: Equation2079 G) : Equation2891 G := fun x y z =>
  let v0 := M y z
  let v1 := M x v0
  T (T (h x v0 x) (C (C (h v1 z y) (R x)) (R v1))) (S (h (M (M v1 z) y) v0 x))

@[equational_result]
theorem Equation2137_implies_Equation1325 (G: Type _) [Magma G] (h: Equation2137 G) : Equation1325 G := fun x y =>
  let v0 := M (M y y) y
  let v1 := M v0 x
  T (T (h x v0) (C (R (M (M v0 v0) v0)) (h v1 y))) (S (h (M y v1) v0))

@[equational_result]
theorem Equation2167_implies_Equation14 (G: Type _) [Magma G] (h: Equation2167 G) : Equation14 G := fun x y =>
  let v0 := M x x
  have h1 := h x x x
  T (h x x y) (C (T (C (C h1 (R y)) h1) (S (h y (M v0 x) v0))) (R (M x y)))

@[equational_result]
theorem Equation2263_implies_Equation23 (G: Type _) [Magma G] (h: Equation2263 G) : Equation23 G := fun x =>
  have h0 := R x
  have h1 := S (h x x)
  let v2 := M x (M x (M x x))
  T (h x v2) (C (C h0 (T (C (R v2) h1) h1)) h0)

@[equational_result]
theorem Equation2267_implies_Equation1455 (G: Type _) [Magma G] (h: Equation2267 G) : Equation1455 G := fun x y =>
  let v0 := M y (M y y)
  have h1 := h x v0
  T h1 (C (T (h (M x (M v0 (M v0 v0))) y) (C (S h1) (R y))) (R v0))

@[equational_result]
theorem Equation2337_implies_Equation3 (G: Type _) [Magma G] (h: Equation2337 G) : Equation3 G := fun x =>
  have h0 := S (h x x)
  let v1 := M x (M x (M x x))
  have h2 := R v1
  T (h x v1) (C (T (C h2 (T (C h2 h0) h0)) h0) (R x))

@[equational_result]
theorem Equation2936_implies_Equation23 (G: Type _) [Magma G] (h: Equation2936 G) : Equation23 G := fun x =>
  have h0 := R x
  have h1 := S (h x x)
  let v2 := M (M x (M x x)) x
  T (h x v2) (C (C (T (C (R v2) h1) h1) h0) h0)

@[equational_result]
theorem Equation2978_implies_Equation2 (G: Type _) [Magma G] (h: Equation2978 G) : Equation2 G := fun x y =>
  let v0 := M x x
  have h1 := R x
  T (T (h x x x) (C (C (C h1 (h v0 y x)) h1) h1)) (S (h y x (M (M y (M x v0)) y)))

@[equational_result]
theorem Equation3180_implies_Equation2712 (G: Type _) [Magma G] (h: Equation3180 G) : Equation2712 G := fun x y z =>
  have h0 := R x
  let v1 := M y z
  T (h x v1 y) (C (C (C (T (C (h v1 y z) (R y)) (S (h y v1 v1))) h0) (R v1)) h0)

@[equational_result]
theorem Equation3404_implies_Equation3497 (G: Type _) [Magma G] (h: Equation3404 G) : Equation3497 G := fun x y z =>
  let v0 := M z y
  let v1 := M v0 z
  T (T (h x x z) (C (R z) (T (C (R x) (h z x v0)) (S (h v1 v0 x))))) (S (h y v1 z))

@[equational_result]
theorem Equation3609_implies_Equation41 (G: Type _) [Magma G] (h: Equation3609 G) : Equation41 G := fun x y z =>
  let v0 := M x x
  T (T (h x x v0) (C (R v0) (T (h (M x v0) v0 x) (S (h (M z v0) v0 x))))) (S (h y z v0))

@[equational_result]
theorem Equation3758_implies_Equation332 (G: Type _) [Magma G] (h: Equation3758 G) : Equation332 G := fun x y =>
  let v0 := M x x
  T (T (T (h x y) (h (M y y) v0)) (C (R (M v0 v0)) (S (h y y)))) (S (h y v0))

@[equational_result]
theorem Equation3776_implies_Equation3620 (G: Type _) [Magma G] (h: Equation3776 G) : Equation3620 G := fun x y z =>
  let v0 := M z y
  let v1 := M v0 x
  T (T (T (h x y v0) (h (M y v0) v1 v0)) (C (R (M v1 v0)) (S (h v0 z y)))) (S (h z v1 v0))

@[equational_result]
theorem Equation3791_implies_Equation3703 (G: Type _) [Magma G] (h: Equation3791 G) : Equation3703 G := fun x y z =>
  T (T (T (T (h x x z) (h (M z x) (M x z) (M x x))) (C (S (h x z x)) (S (h z x x)))) (S (h z z x))) (h z z y)

@[equational_result]
theorem Equation4013_implies_Equation4216 (G: Type _) [Magma G] (h: Equation4013 G) : Equation4216 G := fun x y z =>
  let v0 := M z y
  T (h x y v0) (C (T (T (h v0 (M y v0) z) (C (C (R z) (S (h z z y))) (R v0))) (S (h v0 z z))) (R x))

@[equational_result]
theorem Equation4024_implies_Equation41 (G: Type _) [Magma G] (h: Equation4024 G) : Equation41 G := fun x y z =>
  let v0 := M z x
  T (T (T (h x x z) (R (M (M z v0) z))) (C (T (h z v0 x) (S (h z (M z y) x))) (R z))) (S (h y z z))

@[equational_result]
theorem Equation4176_implies_Equation3903 (G: Type _) [Magma G] (h: Equation4176 G) : Equation3903 G := fun x y z =>
  let v0 := M z y
  let v1 := M y v0
  T (T (h x x y) (C (T (C (h x y v0) (R x)) (S (h v0 v1 x))) (R y))) (S (h v1 z y))

@[equational_result]
theorem Equation502_implies_Equation2 (G: Type _) [Magma G] (h: Equation502 G) : Equation2 G := fun x y =>
  let v0 := M y (M y x)
  have h1 := R y
  T (T (T (h x y v0) (C h1 (C h1 (S (h y x x))))) (C h1 (C h1 (h y y x)))) (S (h y y v0))

@[equational_result]
theorem Equation543_implies_Equation3737 (G: Type _) [Magma G] (h: Equation543 G) : Equation3737 G := fun x y z =>
  let v0 := M x z
  let v1 := M v0 (M y z)
  T (C (R x) (T (h y z v1) (C (R z) (C (R v1) (S (h v0 y z)))))) (S (h v1 x z))

@[equational_result]
theorem Equation617_implies_Equation8 (G: Type _) [Magma G] (h: Equation617 G) : Equation8 G := fun x =>
  have h0 := S (h x x)
  let v1 := M x (M (M x x) x)
  have h2 := R x
  T (h x v1) (C h2 (C h2 (T (C h0 (R v1)) h0)))

@[equational_result]
theorem Equation862_implies_Equation4 (G: Type _) [Magma G] (h: Equation862 G) : Equation4 G := fun x y =>
  have h0 := S (h y x x)
  let v1 := M x x
  let v2 := M v1 v1
  T (h x y v2) (C (R x) (T (C h0 (S (h v2 x x))) h0))

@[equational_result]
theorem Equation919_implies_Equation716 (G: Type _) [Magma G] (h: Equation919 G) : Equation716 G := fun x y =>
  have h0 := h x y
  let v1 := M y y
  have h2 := R y
  T h0 (C h2 (T (h (M v1 (M y x)) y) (C h2 (C (R v1) (S h0)))))

@[equational_result]
theorem Equation1116_implies_Equation2 (G: Type _) [Magma G] (h: Equation1116 G) : Equation2 G := fun x y =>
  let v0 := M x x
  have h1 := R x
  T (T (h x x x) (C h1 (C (C h1 (h v0 y x)) h1))) (S (h y x (M (M y (M v0 x)) y)))

@[equational_result]
theorem Equation1231_implies_Equation8 (G: Type _) [Magma G] (h: Equation1231 G) : Equation8 G := fun x =>
  have h0 := R x
  have h1 := S (h x x)
  let v2 := M (M (M x x) x) x
  T (h x v2) (C h0 (C (T (C h1 (R v2)) h1) h0))

@[equational_result]
theorem Equation1232_implies_Equation3 (G: Type _) [Magma G] (h: Equation1232 G) : Equation3 G := fun x =>
  have h0 := S (h x x)
  let v1 := M (M (M x x) x) x
  have h2 := R v1
  T (h x v1) (C (R x) (T (C (T (C h0 h2) h0) h2) h0))

@[equational_result]
theorem Equation1275_implies_Equation19 (G: Type _) [Magma G] (h: Equation1275 G) : Equation19 G := fun x y z =>
  let v0 := M (M (M x x) x) x
  T (h x y) (C (R y) (T (h v0 z) (C (R z) (S (h x (M (M v0 v0) v0))))))

@[equational_result]
theorem Equation1387_implies_Equation2152 (G: Type _) [Magma G] (h: Equation1387 G) : Equation2152 G := fun x y z =>
  let v0 := M (M y y) z
  have h1 := h x v0 x
  T h1 (C (R v0) (T (h (M (M (M x x) v0) x) z y) (C (R z) (S h1))))

@[equational_result]
theorem Equation1577_implies_Equation765 (G: Type _) [Magma G] (h: Equation1577 G) : Equation765 G := fun x y z =>
  let v0 := M y z
  let v1 := M v0 x
  T (T (h x x v0) (C (R (M x v0)) (C (R x) (h v1 y z)))) (S (h (M y (M z v1)) x v0))

@[equational_result]
theorem Equation1720_implies_Equation2 (G: Type _) [Magma G] (h: Equation1720 G) : Equation2 G := fun x y =>
  let v0 := M (M x x) x
  have h1 := R (M y y)
  T (T (T (h x y v0) (C h1 (S (h x x x)))) (C h1 (h x y x))) (S (h y y v0))

@[equational_result]
theorem Equation1729_implies_Equation2541 (G: Type _) [Magma G] (h: Equation1729 G) : Equation2541 G := fun x y =>
  let v0 := M y y
  let v1 := M v0 x
  T (T (h x v0) (C (R (M v0 v0)) (C (h v1 y) (R v0)))) (S (h (M (M y v1) y) v0))

@[equational_result]
theorem Equation1774_implies_Equation2552 (G: Type _) [Magma G] (h: Equation1774 G) : Equation2552 G := fun x y z =>
  let v0 := M y z
  let v1 := M v0 x
  T (T (h x v0 x) (C (R v1) (C (h v1 y z) (R x)))) (S (h (M (M y v1) z) v0 x))

@[equational_result]
theorem Equation1790_implies_Equation2586 (G: Type _) [Magma G] (h: Equation1790 G) : Equation2586 G := fun x y z =>
  let v0 := M z y
  let v1 := M v0 x
  T (T (h x x v0) (C (R (M x v0)) (C (h v1 z y) (R x)))) (S (h (M (M y v1) z) x v0))

@[equational_result]
theorem Equation1835_implies_Equation4341 (G: Type _) [Magma G] (h: Equation1835 G) : Equation4341 G := fun x y z =>
  let v0 := M x (M x x)
  have h1 := h x v0
  T (T (T (C h1 (R (M y y))) (S (h v0 y))) (h v0 z)) (C (S h1) (R (M z z)))

@[equational_result]
theorem Equation2271_implies_Equation1470 (G: Type _) [Magma G] (h: Equation2271 G) : Equation1470 G := fun x y z =>
  let v0 := M z (M z y)
  have h1 := h x z v0
  T h1 (C (T (h (M x (M z (M z v0))) z y) (C (S h1) (R y))) (R v0))

@[equational_result]
theorem Equation2327_implies_Equation23 (G: Type _) [Magma G] (h: Equation2327 G) : Equation23 G := fun x =>
  let v0 := M x x
  have h1 := S (h v0 x)
  let v2 := M x (M x (M v0 v0))
  T (h x v2) (C (T (C (R v2) h1) h1) (R x))

@[equational_result]
theorem Equation2474_implies_Equation1673 (G: Type _) [Magma G] (h: Equation2474 G) : Equation1673 G := fun x y z =>
  let v0 := M (M z z) y
  have h1 := h x x v0
  T h1 (C (T (h (M x (M (M x x) v0)) z y) (C (S h1) (R y))) (R v0))

@[equational_result]
theorem Equation2572_implies_Equation2 (G: Type _) [Magma G] (h: Equation2572 G) : Equation2 G := fun x y =>
  let v0 := M x x
  have h1 := R x
  T (T (h x x x) (C (C h1 (C (h v0 y x) h1)) h1)) (S (h y x (M y (M (M x v0) y))))

@[equational_result]
theorem Equation3131_implies_Equation2519 (G: Type _) [Magma G] (h: Equation3131 G) : Equation2519 G := fun x y z =>
  let v0 := M (M x z) y
  have h1 := R v0
  T (h x z v0) (C (C (T (C (C (h z x y) (R x)) h1) (S (h y v0 x))) h1) (R z))

@[equational_result]
theorem Equation3312_implies_Equation4360 (G: Type _) [Magma G] (h: Equation3312 G) : Equation4360 G := fun x y z w =>
  have h0 := R x
  let v1 := M y z
  T (T (h x v1 w) (C h0 (T (h x (M w v1) w) (C h0 (C h0 (S (h w z y))))))) (S (h x (M w z) x))

@[equational_result]
theorem Equation3368_implies_Equation41 (G: Type _) [Magma G] (h: Equation3368 G) : Equation41 G := fun x y z =>
  let v0 := M y (M x y)
  T (T (T (T (h x x y) (h x v0 y)) (S (h z v0 y))) (C (R z) (C (R y) (T (h x y x) (S (h z y x)))))) (S (h y z y))

@[equational_result]
theorem Equation3823_implies_Equation3729 (G: Type _) [Magma G] (h: Equation3823 G) : Equation3729 G := fun x y z =>
  let v0 := M z z
  let v1 := M x y
  let v2 := M v1 v0
  T (T (h x y v2) (C (R (M v2 v2)) (h y x z))) (S (h v1 v0 v2))

@[equational_result]
theorem Equation492_implies_Equation3417 (G: Type _) [Magma G] (h: Equation492 G) : Equation3417 G := fun x y z =>
  let v0 := M y x
  let v1 := M z (M z v0)
  T (C (R x) (T (h y v1 v0) (C (R v1) (C (R y) (S (h v0 v0 z)))))) (S (h v1 x y))

@[equational_result]
theorem Equation627_implies_Equation9 (G: Type _) [Magma G] (h: Equation627 G) : Equation9 G := fun x y =>
  have h0 := S (h y x x)
  let v1 := M y (M (M x x) x)
  have h2 := R x
  T (h x y v1) (C h2 (C h2 (T (C h0 (R v1)) h0)))

@[equational_result]
theorem Equation1093_implies_Equation2 (G: Type _) [Magma G] (h: Equation1093 G) : Equation2 G := fun x y =>
  let v0 := M y (M x y)
  have h1 := R y
  T (T (T (h x y v0) (C h1 (C (S (h y x x)) h1))) (C h1 (C (h y y x) h1))) (S (h y y v0))

@[equational_result]
theorem Equation1226_implies_Equation8 (G: Type _) [Magma G] (h: Equation1226 G) : Equation8 G := fun x =>
  let v0 := M x x
  have h1 := S (h v0 x)
  let v2 := M (M (M v0 v0) x) x
  T (h x v2) (C (R x) (T (C h1 (R v2)) h1))

@[equational_result]
theorem Equation1320_implies_Equation2944 (G: Type _) [Magma G] (h: Equation1320 G) : Equation2944 G := fun x y z =>
  let v0 := M y x
  have h1 := R x
  T (T (h x y x) (C (R y) (C (C (h v0 y z) h1) h1))) (S (h (M (M (M y v0) z) z) y x))

@[equational_result]
theorem Equation1543_implies_Equation731 (G: Type _) [Magma G] (h: Equation1543 G) : Equation731 G := fun x y z =>
  let v0 := M z z
  let v1 := M v0 x
  T (T (h x x v0) (C (R (M x x)) (C (R v0) (h v1 z y)))) (S (h (M y (M y v1)) x v0))

@[equational_result]
theorem Equation1730_implies_Equation2 (G: Type _) [Magma G] (h: Equation1730 G) : Equation2 G := fun x y =>
  let v0 := M (M x y) x
  T (T (h x x (M (M x v0) x)) (C (R (M x x)) (S (h v0 x x)))) (S (h y x x))

@[equational_result]
theorem Equation1910_implies_Equation1090 (G: Type _) [Magma G] (h: Equation1910 G) : Equation1090 G := fun x y z =>
  let v0 := M y z
  let v1 := M x v0
  T (T (h x x v0) (C (C (R x) (h v1 y z)) (R v1))) (S (h (M y (M v1 z)) x v0))

@[equational_result]
theorem Equation2064_implies_Equation2876 (G: Type _) [Magma G] (h: Equation2064 G) : Equation2876 G := fun x y =>
  let v0 := M y y
  let v1 := M x v0
  T (T (h x v0) (C (C (h v1 y) (R v0)) (R (M v0 v0)))) (S (h (M (M v1 y) y) v0))

@[equational_result]
theorem Equation2182_implies_Equation194 (G: Type _) [Magma G] (h: Equation2182 G) : Equation194 G := fun x y z =>
  let v0 := M y z
  let v1 := M v0 y
  T (h x z v1) (C (C (T (C (h z y z) (R v1)) (S (h y v0 y))) (R z)) (R (M z x)))

@[equational_result]
theorem Equation2269_implies_Equation25 (G: Type _) [Magma G] (h: Equation2269 G) : Equation25 G := fun x y =>
  have h0 := R x
  have h1 := S (h y x x)
  let v2 := M y (M x (M x x))
  T (h x v2 y) (C (C h0 (T (C (R v2) h1) h1)) h0)

@[equational_result]
theorem Equation2279_implies_Equation1467 (G: Type _) [Magma G] (h: Equation2279 G) : Equation1467 G := fun x y z =>
  let v0 := M z (M y z)
  have h1 := h x v0 v0
  T h1 (C (T (h (M x (M v0 (M v0 v0))) z y) (C (S h1) (R y))) (R v0))

@[equational_result]
theorem Equation2316_implies_Equation2116 (G: Type _) [Magma G] (h: Equation2316 G) : Equation2116 G := fun x y z =>
  let v0 := M z y
  have h1 := h x y v0
  T h1 (C (T (h (M y (M x (M v0 y))) y z) (C (C (R y) (S h1)) (R z))) (R v0))

@[equational_result]
theorem Equation2333_implies_Equation25 (G: Type _) [Magma G] (h: Equation2333 G) : Equation25 G := fun x y =>
  let v0 := M x y
  have h1 := S (h v0 x x)
  let v2 := M x (M x (M v0 x))
  T (h x v2 y) (C (T (C (R v2) h1) h1) (R x))

@[equational_result]
theorem Equation2663_implies_Equation258 (G: Type _) [Magma G] (h: Equation2663 G) : Equation258 G := fun x y =>
  have h0 := R y
  have h1 := h x y
  have h2 := S h1
  let v3 := M x y
  T h1 (C (T (h (M v3 v3) y) (C (C h2 h2) h0)) h0)

@[equational_result]
theorem Equation2749_implies_Equation5 (G: Type _) [Magma G] (h: Equation2749 G) : Equation5 G := fun x y =>
  have h0 := S (h y x x)
  let v1 := M x x
  let v2 := M v1 v1
  T (h x v2 y) (C (T (C (S (h v2 x x)) h0) h0) (R x))

@[equational_result]
theorem Equation2755_implies_Equation978 (G: Type _) [Magma G] (h: Equation2755 G) : Equation978 G := fun x y z =>
  let v0 := M (M z z) (M x y)
  let v1 := M y y
  T (h x v1 v0) (C (T (C (R (M v1 v1)) (S (h y z x))) (S (h y y y))) (R v0))

@[equational_result]
theorem Equation2956_implies_Equation28 (G: Type _) [Magma G] (h: Equation2956 G) : Equation28 G := fun x y =>
  have h0 := R x
  have h1 := S (h y x x)
  let v2 := M (M x (M x x)) y
  T (h x v2 y) (C (C (T (C (R v2) h1) h1) h0) h0)

@[equational_result]
theorem Equation3289_implies_Equation3301 (G: Type _) [Magma G] (h: Equation3289 G) : Equation3301 G := fun x y z w =>
  let v0 := M x x
  have h1 := R v0
  T (T (T (T (h x v0 x) (C h1 (S (h x x x)))) (C h1 (h x x w))) (S (h w v0 x))) (h w y z)

@[equational_result]
theorem Equation3804_implies_Equation4362 (G: Type _) [Magma G] (h: Equation3804 G) : Equation4362 G := fun x y z =>
  let v0 := M y z
  let v1 := M x z
  T (T (T (h x v0 z) (h (M z v0) v1 v0)) (C (R (M v0 v1)) (S (h y v0 z)))) (S (h y v1 v0))

@[equational_result]
theorem Equation3810_implies_Equation4673 (G: Type _) [Magma G] (h: Equation3810 G) : Equation4673 G := fun x y z =>
  let v0 := M x z
  let v1 := M x y
  T (T (T (h v1 z v0) (C (h v0 z x) (R (M v0 v1)))) (S (h v1 (M x v0) v0))) (S (h v0 y x))

@[equational_result]
theorem Equation4199_implies_Equation41 (G: Type _) [Magma G] (h: Equation4199 G) : Equation41 G := fun x y z =>
  let v0 := M (M z x) z
  T (T (T (T (h x x z) (h v0 x x)) (S (h v0 y x))) (C (C (T (h z x x) (S (h z y x))) (R z)) (R y))) (S (h y z z))

@[equational_result]
theorem Equation4210_implies_Equation4109 (G: Type _) [Magma G] (h: Equation4210 G) : Equation4109 G := fun x y z =>
  let v0 := M x x
  T (T (T (h x x x) (C (T (h v0 x z) (C (T (C (h z x x) (R v0)) (S (h x z v0))) (R z))) (R x))) (S (h z z x))) (h z z y)

@[equational_result]
theorem Equation4643_implies_Equation4680 (G: Type _) [Magma G] (h: Equation4643 G) : Equation4680 G := fun x y z w =>
  T (T (T (T (T (S (h y z x)) (h y z (M y w))) (C (h y w x) (R z))) (S (h w z (M x y)))) (S (h z w w))) (h z w y)

@[equational_result]
theorem Equation909_implies_Equation72 (G: Type _) [Magma G] (h: Equation909 G) : Equation72 G := fun x y =>
  have h0 := h x y
  have h1 := S h0
  have h2 := R y
  let v3 := M y x
  T h0 (C h2 (T (h (M v3 v3) y) (C h2 (C h1 h1))))

@[equational_result]
theorem Equation952_implies_Equation543 (G: Type _) [Magma G] (h: Equation952 G) : Equation543 G := fun x y z =>
  let v0 := M y z
  have h1 := h x y v0
  T h1 (C (R y) (T (h (M (M v0 x) (M v0 y)) z y) (C (R z) (C (S h1) (R v0)))))

@[equational_result]
theorem Equation1304_implies_Equation14 (G: Type _) [Magma G] (h: Equation1304 G) : Equation14 G := fun x y =>
  have h0 := R y
  have h1 := S (h x x x)
  let v2 := M (M (M x x) x) x
  T (h x y v2) (C h0 (C (T (C h1 (R v2)) h1) h0))

@[equational_result]
theorem Equation1577_implies_Equation3997 (G: Type _) [Magma G] (h: Equation1577 G) : Equation3997 G := fun x y z =>
  let v0 := M x z
  let v1 := M v0 x
  T (h (M x y) v1 v0) (C (T (C (R v1) (h v0 x z)) (S (h (M z v0) v0 x))) (S (h y v0 x)))

@[equational_result]
theorem Equation1740_implies_Equation2602 (G: Type _) [Magma G] (h: Equation1740 G) : Equation2602 G := fun x y z =>
  let v0 := M z z
  let v1 := M v0 x
  T (T (h x x v0) (C (R (M x x)) (C (h v1 z y) (R v0)))) (S (h (M (M y v1) y) x v0))

@[equational_result]
theorem Equation1902_implies_Equation1101 (G: Type _) [Magma G] (h: Equation1902 G) : Equation1101 G := fun x y z =>
  let v0 := M z z
  let v1 := M x v0
  T (T (h x v0 x) (C (C (R v0) (h v1 y z)) (R (M x x)))) (S (h (M y (M v1 y)) v0 x))

@[equational_result]
theorem Equation2282_implies_Equation1459 (G: Type _) [Magma G] (h: Equation2282 G) : Equation1459 G := fun x y z =>
  let v0 := M y (M z z)
  have h1 := h x v0 x
  T h1 (C (T (h (M x (M v0 (M x x))) y z) (C (S h1) (R y))) (R v0))

@[equational_result]
theorem Equation2343_implies_Equation5 (G: Type _) [Magma G] (h: Equation2343 G) : Equation5 G := fun x y =>
  have h0 := S (h y x x)
  let v1 := M x (M x (M x x))
  have h2 := R v1
  T (h x v1 y) (C (T (C h2 (T (C h2 h0) h0)) h0) (R x))

@[equational_result]
theorem Equation2511_implies_Equation1301 (G: Type _) [Magma G] (h: Equation2511 G) : Equation1301 G := fun x y z =>
  let v0 := M x z
  have h1 := R x
  T (T (h x z x) (C (C (R z) (C (h v0 y z) h1)) h1)) (S (h (M y (M (M v0 y) z)) z x))

@[equational_result]
theorem Equation2514_implies_Equation2 (G: Type _) [Magma G] (h: Equation2514 G) : Equation2 G := fun x y =>
  let v0 := M (M y x) y
  have h1 := R y
  T (T (T (h x y v0) (C (C h1 (S (h y x x))) h1)) (C (C h1 (h y y x)) h1)) (S (h y y v0))

@[equational_result]
theorem Equation2673_implies_Equation2876 (G: Type _) [Magma G] (h: Equation2673 G) : Equation2876 G := fun x y =>
  have h0 := R y
  let v1 := M y y
  have h2 := h x y
  T h2 (C (T (h (M (M x y) v1) y) (C (C (S h2) (R v1)) h0)) h0)

@[equational_result]
theorem Equation2737_implies_Equation3143 (G: Type _) [Magma G] (h: Equation2737 G) : Equation3143 G := fun x y =>
  have h0 := R y
  have h1 := h x y
  let v2 := M y y
  T h1 (C (T (h (M v2 (M x y)) y) (C (C (R v2) (S h1)) h0)) h0)

@[equational_result]
theorem Equation3182_implies_Equation1761 (G: Type _) [Magma G] (h: Equation3182 G) : Equation1761 G := fun x y z =>
  let v0 := M (M x y) z
  have h1 := R v0
  T (h x z v0) (C (C (T (C (C (h z x y) h1) (R x)) (S (h y v0 x))) (R z)) h1)

@[equational_result]
theorem Equation3182_implies_Equation3794 (G: Type _) [Magma G] (h: Equation3182 G) : Equation3794 G := fun x y z =>
  let v0 := M z y
  let v1 := M (M z x) v0
  T (C (T (h x v1 z) (C (C (S (h v0 z x)) (R v1)) (R z))) (R y)) (S (h v1 z y))

@[equational_result]
theorem Equation3404_implies_Equation3997 (G: Type _) [Magma G] (h: Equation3404 G) : Equation3997 G := fun x y z =>
  let v0 := M x z
  have h1 := R v0
  T (T (h x y v0) (C h1 (C (R y) (T (h v0 x v0) (C h1 (S (h z v0 x))))))) (S (h (M z v0) y v0))

@[equational_result]
theorem Equation3737_implies_Equation3323 (G: Type _) [Magma G] (h: Equation3737 G) : Equation3323 G := fun x y z =>
  let v0 := M z z
  let v1 := M y v0
  T (T (h x y v0) (C (R (M x v0)) (T (h y v0 v0) (C (R v1) (S (h z z z)))))) (S (h x v1 v0))

@[equational_result]
theorem Equation3740_implies_Equation3537 (G: Type _) [Magma G] (h: Equation3740 G) : Equation3537 G := fun x y z =>
  let v0 := M z z
  let v1 := M v0 y
  T (T (h x y v0) (C (R (M x v0)) (T (h v0 y v0) (C (S (h z z z)) (R v1))))) (S (h x v1 v0))

@[equational_result]
theorem Equation3744_implies_Equation4520 (G: Type _) [Magma G] (h: Equation3744 G) : Equation4520 G := fun x y z w =>
  let v0 := M x w
  let v1 := M y z
  T (T (h x v1 v1 (M v0 z)) (C (T (h x v1 w v1) (C (R v0) (S (h y z z y)))) (S (h v0 z z y)))) (S (h v0 z v1 v0))

@[equational_result]
theorem Equation3776_implies_Equation3959 (G: Type _) [Magma G] (h: Equation3776 G) : Equation3959 G := fun x y z =>
  let v0 := M x z
  let v1 := M y v0
  T (T (T (h x y v0) (h v1 (M v0 x) v0)) (C (S (h z v0 x)) (R (M v0 v1)))) (S (h v1 z v0))

@[equational_result]
theorem Equation3794_implies_Equation3537 (G: Type _) [Magma G] (h: Equation3794 G) : Equation3537 G := fun x y z =>
  let v0 := M z z
  let v1 := M v0 y
  T (T (h x y v0) (C (R (M v0 x)) (T (h v0 y v0) (C (S (h z z z)) (R v1))))) (S (h x v1 v0))

@[equational_result]
theorem Equation3804_implies_Equation4673 (G: Type _) [Magma G] (h: Equation3804 G) : Equation4673 G := fun x y z =>
  let v0 := M x z
  let v1 := M x y
  T (T (T (h v1 z v0) (C (h v0 z x) (R (M v1 v0)))) (S (h v1 (M v0 x) v0))) (S (h v0 y x))

@[equational_result]
theorem Equation3810_implies_Equation4369 (G: Type _) [Magma G] (h: Equation3810 G) : Equation4369 G := fun x y z =>
  let v0 := M y x
  let v1 := M y z
  T (T (T (h x v1 v0) (C (R (M v0 v1)) (h v0 x y))) (S (h (M y v0) v1 v0))) (S (h z v0 y))

@[equational_result]
theorem Equation4087_implies_Equation4113 (G: Type _) [Magma G] (h: Equation4087 G) : Equation4113 G := fun x y z w =>
  let v0 := M x x
  have h1 := R v0
  T (T (T (T (h x v0 x) (C (S (h x x x)) h1)) (C (h x x z) h1)) (S (h z v0 x))) (h z y w)

@[equational_result]
theorem Equation4092_implies_Equation4099 (G: Type _) [Magma G] (h: Equation4092 G) : Equation4099 G := fun x y z w =>
  let v0 := M x x
  let v1 := M y y
  T (T (T (h x v1 v0) (C (T (S (h v1 y x)) (h v1 y z)) (R v0))) (S (h z v1 v0))) (h z y w)

@[equational_result]
theorem Equation4618_implies_Equation4680 (G: Type _) [Magma G] (h: Equation4618 G) : Equation4680 G := fun x y z w =>
  T (T (T (T (T (S (h z y x)) (h z y (M w w))) (C (h w y x) (R z))) (S (h z w (M x y)))) (S (h w z z))) (h w z y)

@[equational_result]
theorem Equation546_implies_Equation2586 (G: Type _) [Magma G] (h: Equation546 G) : Equation2586 G := fun x y z =>
  let v0 := M z y
  let v1 := M y (M v0 x)
  T (h x v1 v0) (C (R v1) (T (C (R v0) (T (S (h y x v0)) (h y y z))) (S (h z v0 y))))

@[equational_result]
theorem Equation556_implies_Equation749 (G: Type _) [Magma G] (h: Equation556 G) : Equation749 G := fun x y z =>
  let v0 := M x z
  let v1 := M v0 y
  have h2 := R y
  T (h x y z) (C h2 (C (R z) (T (C h2 (h v0 v1 y)) (S (h v1 y v1)))))

@[equational_result]
theorem Equation887_implies_Equation2725 (G: Type _) [Magma G] (h: Equation887 G) : Equation2725 G := fun x y z =>
  let v0 := M y y
  let v1 := M (M y x) (M z z)
  T (h x v1 v0) (C (R v1) (T (C (S (h y x z)) (R (M v0 v0))) (S (h y y y))))

@[equational_result]
theorem Equation949_implies_Equation1967 (G: Type _) [Magma G] (h: Equation949 G) : Equation1967 G := fun x y z =>
  let v0 := M z x
  let v1 := M (M y v0) (M z y)
  T (T (h x v1 z) (C (R v1) (C (h v0 z y) (R (M v1 z))))) (S (h v1 v1 z))

@[equational_result]
theorem Equation952_implies_Equation1964 (G: Type _) [Magma G] (h: Equation952 G) : Equation1964 G := fun x y z =>
  let v0 := M y z
  let v1 := M z x
  T (T (h x v0 z) (C (R v0) (C (h v1 z y) (R (M z v0))))) (S (h (M (M y v1) v0) v0 z))

@[equational_result]
theorem Equation1266_implies_Equation10 (G: Type _) [Magma G] (h: Equation1266 G) : Equation10 G := fun x y =>
  have h0 := R x
  have h1 := S (h y x x)
  let v2 := M (M (M x x) x) y
  T (h x y v2) (C h0 (C (T (C h1 (R v2)) h1) h0))

@[equational_result]
theorem Equation2076_implies_Equation2888 (G: Type _) [Magma G] (h: Equation2076 G) : Equation2888 G := fun x y z =>
  let v0 := M y z
  let v1 := M x v0
  T (T (h x v0 x) (C (C (h v1 y z) (R x)) (R (M v0 x)))) (S (h (M (M v1 y) z) v0 x))

@[equational_result]
theorem Equation2304_implies_Equation2101 (G: Type _) [Magma G] (h: Equation2304 G) : Equation2101 G := fun x y =>
  let v0 := M y y
  have h1 := R y
  have h2 := h x v0
  T h2 (C (T (h (M v0 (M x (M v0 v0))) y) (C (C h1 (S h2)) h1)) (R v0))

@[equational_result]
theorem Equation2355_implies_Equation31 (G: Type _) [Magma G] (h: Equation2355 G) : Equation31 G := fun x y =>
  let v0 := M y y
  have h1 := S (h v0 y v0)
  let v2 := M y (M y (M v0 v0))
  T (h x v2 y) (C (T (C (R v2) h1) h1) (R x))

@[equational_result]
theorem Equation2522_implies_Equation1293 (G: Type _) [Magma G] (h: Equation2522 G) : Equation1293 G := fun x y z =>
  let v0 := M x y
  have h1 := R x
  T (T (h x x y) (C (C h1 (C (h v0 y z) (R y))) h1)) (S (h (M y (M (M v0 z) z)) x y))

@[equational_result]
theorem Equation3364_implies_Equation3997 (G: Type _) [Magma G] (h: Equation3364 G) : Equation3997 G := fun x y z =>
  let v0 := M x z
  let v1 := M z v0
  T (T (h x y z) (C (R y) (T (h z v0 v1) (C (R v0) (C (R v1) (S (h x z z))))))) (S (h v1 y v0))

@[equational_result]
theorem Equation3388_implies_Equation4362 (G: Type _) [Magma G] (h: Equation3388 G) : Equation4362 G := fun x y z =>
  have h0 := R y
  let v1 := M y z
  T (T (h x v1 y) (C h0 (T (h x (M y v1) y) (C h0 (C (R x) (S (h y z y))))))) (C h0 (S (h x z y)))

@[equational_result]
theorem Equation3740_implies_Equation3943 (G: Type _) [Magma G] (h: Equation3740 G) : Equation3943 G := fun x y z =>
  let v0 := M z z
  let v1 := M x v0
  T (T (h x y v0) (C (T (h x v0 v0) (C (R v1) (S (h z z z)))) (R (M v0 y)))) (S (h v1 y v0))

@[equational_result]
theorem Equation3770_implies_Equation4684 (G: Type _) [Magma G] (h: Equation3770 G) : Equation4684 G := fun x y z =>
  let v0 := M x y
  let v1 := M z y
  T (T (T (h v0 z y) (h v1 (M v0 y) v0)) (C (S (h x v0 y)) (R (M v1 v0)))) (S (h v1 x v0))

@[equational_result]
theorem Equation3794_implies_Equation4226 (G: Type _) [Magma G] (h: Equation3794 G) : Equation4226 G := fun x y z =>
  let v0 := M z z
  let v1 := M v0 x
  T (T (h x y v0) (C (T (h v0 x v0) (C (S (h z z z)) (R v1))) (R (M v0 y)))) (S (h v1 y v0))

@[equational_result]
theorem Equation716_implies_Equation1528 (G: Type _) [Magma G] (h: Equation716 G) : Equation1528 G := fun x y =>
  let v0 := M y y
  have h1 := h x v0
  have h2 := R y
  T h1 (C (R v0) (T (h (M v0 (M (M v0 v0) x)) y) (C h2 (C h2 (S h1)))))

@[equational_result]
theorem Equation1246_implies_Equation10 (G: Type _) [Magma G] (h: Equation1246 G) : Equation10 G := fun x y =>
  let v0 := M y x
  have h1 := S (h v0 x x)
  let v2 := M (M (M x v0) x) x
  T (h x y v2) (C (R x) (T (C h1 (R v2)) h1))

@[equational_result]
theorem Equation1268_implies_Equation4 (G: Type _) [Magma G] (h: Equation1268 G) : Equation4 G := fun x y =>
  have h0 := S (h y x x)
  let v1 := M (M (M x x) x) x
  have h2 := R v1
  T (h x y v1) (C (R x) (T (C (T (C h0 h2) h0) h2) h0))

@[equational_result]
theorem Equation1740_implies_Equation4647 (G: Type _) [Magma G] (h: Equation1740 G) : Equation4647 G := fun x y z =>
  let v0 := M (M z y) z
  let v1 := M (M x y) x
  T (T (h v1 x v1) (C (R (M x x)) (T (S (h y v1 x)) (h y v0 z)))) (S (h v0 x v0))

