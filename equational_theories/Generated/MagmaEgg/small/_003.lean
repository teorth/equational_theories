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
theorem Equation3128_implies_Equation556 (G: Type _) [Magma G] (h: Equation3128 G) : Equation556 G := fun x y z =>
  let v0 := M x z
  let v1 := M y v0
  let v2 := M z v1
  let v3 := M y v2
  have h4 := R y
  T (T (T (h x v1 y) (C (C (T (C (C (T (h v1 v1 y) (C (S (h v0 y v1)) h4)) (R x)) h4) (S (h z x y))) (R v1)) h4)) (C (h v2 y v3) h4)) (S (h v3 v3 y))

@[equational_result]
theorem Equation3567_implies_Equation4216 (G: Type _) [Magma G] (h: Equation3567 G) : Equation4216 G := fun x y z =>
  let v0 := M (M z y) z
  have h1 := R x
  let v2 := M (M y y) y
  let v3 := M (M v0 x) v0
  T (T (T (T (T (T (h x y v0) (h y v3 y)) (h v3 v2 x)) (C (R v2) (C (S (h x x v0)) h1))) (S (h x v2 x))) (C h1 (C (h y y z) (R y)))) (S (h v0 x y))

@[equational_result]
theorem Equation3356_implies_Equation3451 (G: Type _) [Magma G] (h: Equation3356 G) : Equation3451 G := fun x y z w u =>
  let v0 := M u y
  let v1 := M v0 v0
  have h2 := T (h y y) (S (h u y))
  let v3 := M y y
  T (T (T (T (h x y) (C (R y) (T (T (h y v3) (S (h v3 v3))) (C h2 h2)))) (h y v1)) (S (h z v1))) (C (R z) (T (h v0 v0) (S (h w v0))))

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
theorem Equation1064_implies_Equation11 (G: Type _) [Magma G] (h: Equation1064 G) : Equation11 G := fun x y =>
  let v0 := M (M x (M x x)) x
  let v1 := M y y
  have h2 := R y
  have h3 := h v0 x x
  have h4 := R v1
  T (h x v1 v0) (C (R x) (T (T (C (T (C h4 (S h3)) (S (h v1 x x))) h4) (C h4 (C (T (h y x x) (C h2 h3)) h2))) (S (h v1 y v0))))

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
theorem Equation2102_implies_Equation2 (G: Type _) [Magma G] (h: Equation2102 G) : Equation2 G := fun x y =>
  let v0 := M y y
  let v1 := M y x
  let v2 := M v1 y
  have h3 := h x y x
  have h4 := R v2
  have h5 := h x y y
  T (T h5 (C (C (T (C (T (T (h y v1 y) (C (S h3) h4)) (C h5 h4)) h3) (S (h v0 v2 v1))) (R y)) (R v0))) (S (h y y y))

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

@[equational_result]
theorem Equation1913_implies_Equation2776 (G: Type _) [Magma G] (h: Equation1913 G) : Equation2776 G := fun x y z =>
  let v0 := M x y
  let v1 := M y z
  let v2 := M v1 v0
  let v3 := M v2 z
  let v4 := M z v0
  T (T (h x v3 v2) (C (C (R v3) (T (C (T (h x z y) (C (R v4) (h v1 v3 v0))) (h v2 v0 z)) (S (h (M v3 v2) v4 (M v0 v3))))) (R (M v2 v3)))) (S (h v3 v3 v2))

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
theorem Equation2076_implies_Equation2891 (G: Type _) [Magma G] (h: Equation2076 G) : Equation2891 G := fun x y z =>
  let v0 := M y z
  let v1 := M x v0
  let v2 := M (M v1 z) y
  have h3 := h v2 v0 y
  let v4 := M v0 y
  let v5 := M z y
  T (T (h x v0 y) (C (T (C (T (h v1 z y) (C h3 (R v5))) (h y z y)) (S (h (M (M v2 v0) y) v4 v5))) (R v4))) (S h3)

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
theorem Equation1537_implies_Equation14 (G: Type _) [Magma G] (h: Equation1537 G) : Equation14 G := fun x y =>
  let v0 := M x x
  let v1 := M y (M x y)
  have h2 := h x x y
  have h3 := R v1
  have h4 := R v0
  T (T h2 (C h4 (T (h v1 x v1) (C h4 (C h3 (T (T (h (M v1 v1) x v1) (C h4 (T (C h3 (S (h x v1 y))) (C h3 h2)))) (S (h v0 x v1)))))))) (S (h v1 x v0))

@[equational_result]
theorem Equation3718_implies_Equation3935 (G: Type _) [Magma G] (h: Equation3718 G) : Equation3935 G := fun x y z =>
  let v0 := M z x
  let v1 := M x v0
  let v2 := M v1 v1
  let v3 := M x y
  let v4 := M x x
  T (T (T (T (T (h x y x) (R (M v4 v3))) (C (T (T (h x x y) (C (R v4) (h y x z))) (S (h x v0 (M y y)))) (R v3))) (h v1 v3 v2)) (C (R v2) (S (h v1 y x)))) (S (h v1 y v1))

@[equational_result]
theorem Equation3212_implies_Equation2 (G: Type _) [Magma G] (h: Equation3212 G) : Equation2 G := fun x y =>
  let v0 := M (M x y) y
  let v1 := M x x
  let v2 := M v1 x
  have h3 := R x
  have h4 := S (h x v1 x)
  T (T (h x (M v2 x) x) (C (T (T (C h4 h3) (h v1 x y)) (C (C (h v0 x x) (T (C (h x x x) h3) h4)) (R y))) h3)) (S (h y (M v2 v0) x))

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
theorem Equation3810_implies_Equation4297 (G: Type _) [Magma G] (h: Equation3810 G) : Equation4297 G := fun x y z =>
  let v0 := M x y
  let v1 := M x v0
  let v2 := M x z
  have h3 := h z v0 x
  let v4 := M x x
  T (T (T (h x v0 x) (h v1 v4 v0)) (C (T (h v0 v4 v0) (C (S (h x y x)) (T (T (T (h v0 v0 z) (C h3 h3)) (S (h v2 v2 v1))) (S (h z z x))))) (S (h v0 y x)))) (S (h y (M z z) v0))

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
theorem Equation3753_implies_Equation41 (G: Type _) [Magma G] (h: Equation3753 G) : Equation41 G := fun x y z =>
  have h0 := h z y z
  have h1 := S h0
  let v2 := M y z
  have h3 := h x y z
  T (T (T (T (T (T (T (T (T (T (T (h x x x) (C (h x x y) (h x x z))) (S (h (M x y) (M x x) (M x z)))) (S (h y x x))) (h y x y)) (C h3 h3)) (S (h v2 (M y x) v2))) (S (h z y x))) h0) (h v2 v2 v2)) (C h1 h1)) (S (h y z y))

@[equational_result]
theorem Equation556_implies_Equation2538 (G: Type _) [Magma G] (h: Equation556 G) : Equation2538 G := fun x y z =>
  let v0 := M y x
  let v1 := M v0 z
  let v2 := M y v1
  let v3 := M v2 z
  have h4 := R z
  T (T (h x z v1) (C h4 (T (T (C (R v1) (T (T (C h4 (C (R x) (T (h v1 z v1) (C h4 (S (h v0 v1 z)))))) (S (h y z x))) (h y v2 v1))) (S (h v2 v1 v2))) (h v2 v3 z)))) (S (h v3 z v3))

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
theorem Equation2369_implies_Equation2 (G: Type _) [Magma G] (h: Equation2369 G) : Equation2 G := fun x y =>
  have h0 := R x
  have h1 := h x x y
  let v2 := M x x
  let v3 := M x (M y v2)
  T (T (h x x x) (C (C h0 (T (T (h (M x v2) x x) (C (C h0 (C h0 (T (T (T (C (C h0 (C h0 h1)) h0) (S (h v3 x x))) (h v3 x y)) (C (C h0 (C (R y) (S h1))) h0)))) h0)) (S (h (M x (M y x)) x x)))) h0)) (S (h y x x))

@[equational_result]
theorem Equation3810_implies_Equation4007 (G: Type _) [Magma G] (h: Equation3810 G) : Equation4007 G := fun x y z =>
  let v0 := M y x
  let v1 := M z v0
  let v2 := M z z
  have h3 := S (h y x y)
  let v4 := M y y
  T (T (T (T (h x y y) (h v4 v0 v1)) (C (h v1 v0 z) (T (C (h z v0 z) (T (T (T (h y y y) (h v4 v4 v0)) (C h3 h3)) (h v0 v0 z))) (S (h v1 v2 v1))))) (S (h v2 (M z v1) v1))) (S (h v1 z z))

@[equational_result]
theorem Equation1084_implies_Equation2 (G: Type _) [Magma G] (h: Equation1084 G) : Equation2 G := fun x y =>
  have h0 := h x y x
  let v1 := M x (M y x)
  let v2 := M v1 x
  let v3 := M y (M y y)
  let v4 := M (M x (M x x)) x
  T (T h0 (C (R y) (T (T (T (C (R v1) (T (h x x x) (C (h x y y) (R v4)))) (S (h y v1 v4))) (h y v3 v2)) (C (R v3) (T (C (S (h y y y)) (R v2)) (S h0)))))) (S (h y y x))

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
theorem Equation3329_implies_Equation38 (G: Type _) [Magma G] (h: Equation3329 G) : Equation38 G := fun x y =>
  let v0 := M x x
  let v1 := M x y
  have h2 := R x
  have h3 := R v0
  T (T (T (T (h x x v0) (h x (M v0 v0) v1)) (C h2 (C (R v1) (C (T (h v0 v0 y) (C h3 (T (C (R y) (T (C h3 (h x x v1)) (S (h v0 v1 x)))) (S (h y x v0))))) h2)))) (S (h x (M v0 (M y x)) v1))) (S (h x y v0))

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
theorem Equation4161_implies_Equation39 (G: Type _) [Magma G] (h: Equation4161 G) : Equation39 G := fun x y =>
  let v0 := M x x
  let v1 := M y x
  have h2 := R x
  have h3 := R v0
  T (T (T (T (h x x v0) (h (M v0 v0) x v1)) (C (C (C h2 (T (h v0 v0 y) (C (T (C (T (C (h x x v1) h3) (S (h v1 v0 x))) (R y)) (S (h x y v0))) h3))) (R v1)) h2)) (S (h (M (M x y) v0) x v1))) (S (h y x v0))

@[equational_result]
theorem Equation2876_implies_Equation2673 (G: Type _) [Magma G] (h: Equation2876 G) : Equation2673 G := fun x y =>
  let v0 := M y y
  let v1 := M x y
  let v2 := M (M v1 v0) y
  have h3 := h v2 v0
  let v4 := M v0 v0
  have h5 := R y
  have h6 := h x v0
  T (T h6 (C (T (T (h (M (M x v4) v0) y) (C (T (T (C (S h6) h5) (h v1 y)) (C h3 h5)) h5)) (S (h (M (M v2 v4) v0) y))) (R v0))) (S h3)

@[equational_result]
theorem Equation3195_implies_Equation2180 (G: Type _) [Magma G] (h: Equation3195 G) : Equation2180 G := fun x y z =>
  let v0 := M x z
  have h1 := R v0
  have h2 := R y
  let v3 := M y z
  have h4 := R x
  let v5 := M y v0
  T (h x v0 v0) (C (T (T (T (T (C (T (C (C (T (h v0 v5 y) (C (S (h v5 y v0)) h2)) h1) h1) (S (h v0 y v0))) h4) (C (h v0 x z) h4)) (S (h z v0 x))) (h z v3 y)) (C (S (h v3 y z)) h2)) h1)

@[equational_result]
theorem Equation4176_implies_Equation4491 (G: Type _) [Magma G] (h: Equation4176 G) : Equation4491 G := fun x y z =>
  let v0 := M z x
  let v1 := M x v0
  let v2 := M y y
  let v3 := M y v2
  have h4 := R y
  T (T (T (T (h x v2 v3) (C (T (C (T (T (T (h v2 v3 y) (C (S (h y y v2)) h4)) (C (h y y y) h4)) (S (h y v2 y))) (R x)) (h v3 x v0)) (R v3))) (S (h v0 v1 v3))) (h v0 v1 z)) (C (S (h z x v0)) (R z))

@[equational_result]
theorem Equation556_implies_Equation3091 (G: Type _) [Magma G] (h: Equation556 G) : Equation3091 G := fun x y z =>
  let v0 := M x y
  let v1 := M v0 z
  let v2 := M v1 y
  let v3 := M v2 z
  have h4 := R z
  have h5 := R y
  have h6 := R v3
  T (T (h x v3 y) (C h6 (C h5 (C h6 (T (h v0 v3 z) (C h6 (T (C h4 (C h6 (T (h v1 z y) (C h4 (C h5 (T (C h4 (h v2 v3 z)) (S (h v3 z v3)))))))) (S (h y z v3))))))))) (S (h v3 v3 y))

@[equational_result]
theorem Equation1967_implies_Equation562 (G: Type _) [Magma G] (h: Equation1967 G) : Equation562 G := fun x y z =>
  let v0 := M z x
  let v1 := M y v0
  let v2 := M z v1
  have h3 := R v2
  have h4 := S (h v2 v0 v1)
  have h5 := h x v1 z
  let v6 := M v1 v0
  T h5 (C (T (T (T (h v6 v6 (M v0 (M v1 v2))) (C (T (C (R v6) h4) (S h5)) h4)) (C (h x y z) h3)) (S (h y v1 z))) h3)

@[equational_result]
theorem Equation844_implies_Equation11 (G: Type _) [Magma G] (h: Equation844 G) : Equation11 G := fun x y =>
  let v0 := M y y
  have h1 := h v0 y x
  have h2 := R v0
  let v3 := M v0 x
  have h4 := h v0 y v3
  let v5 := M x x
  have h6 := R v5
  T (h x v0 x) (C (R x) (T (C (T (C h2 h1) (S h4)) (T (T (h v5 y v3) (C h6 (S (h v0 x x)))) (C h6 (T h4 (C h2 (S h1)))))) (S (h v0 x v0))))

@[equational_result]
theorem Equation3128_implies_Equation562 (G: Type _) [Magma G] (h: Equation3128 G) : Equation562 G := fun x y z =>
  let v0 := M z x
  let v1 := M y v0
  let v2 := M z v1
  let v3 := M y v2
  have h4 := R y
  T (T (T (h x v1 y) (C (C (T (C (C (T (h v1 v1 y) (C (T (T (S (h v0 y v1)) (h v0 v0 z)) (C (S (h x z v0)) (R z))) h4)) (R x)) h4) (S (h z x y))) (R v1)) h4)) (C (h v2 y v3) h4)) (S (h v3 v3 y))

@[equational_result]
theorem Equation1797_implies_Equation1816 (G: Type _) [Magma G] (h: Equation1797 G) : Equation1816 G := fun x y z w =>
  have h0 := h x z z
  have h1 := S h0
  let v2 := M z z
  let v3 := M v2 x
  have h4 := h v3 y z
  let v5 := M y z
  have h6 := R v5
  T (T (h x y z) (R (M v5 v3))) (C h6 (T (T (T h4 (C h6 h1)) (h (M v5 x) w z)) (C (R (M w z)) (T (C (R v2) (T (C h6 h0) (S h4))) h1))))

@[equational_result]
theorem Equation4545_implies_Equation4365 (G: Type _) [Magma G] (h: Equation4545 G) : Equation4365 G := fun x y z w =>
  have h0 := S (h y z w)
  let v1 := M z w
  let v2 := M y z
  have h3 := h v2 y z
  have h4 := h x y z
  T (T (T (T (T (T (T (T h4 (S (h (M x v2) y z))) (C (T h4 (S h3)) (R v2))) (S (h x v2 v2))) (C (R x) (T h3 (S (h v1 y z))))) (h x v1 v2)) (C (T (h v2 z w) h0) (R v1))) (h (M y v1) z w)) h0

@[equational_result]
theorem Equation556_implies_Equation775 (G: Type _) [Magma G] (h: Equation556 G) : Equation775 G := fun x y z =>
  let v0 := M z x
  let v1 := M z (M v0 y)
  let v2 := M y v1
  have h3 := R v0
  have h4 := R v2
  have h5 := R v1
  T (T (h x v1 z) (C h5 (C (R z) (C h5 (T (T (T (C (R x) (h z v0 x)) (S (h v0 x v0))) (h v0 v2 v0)) (C h4 (T (C h3 (C h4 (C h3 (h v0 z y)))) (S (h z v0 v2))))))))) (S (h v2 v1 z))

@[equational_result]
theorem Equation1710_implies_Equation2146 (G: Type _) [Magma G] (h: Equation1710 G) : Equation2146 G := fun x y z =>
  let v0 := M y y
  let v1 := M x z
  let v2 := M v0 z
  let v3 := M v2 v1
  let v4 := M v0 v3
  T (T (h x v0 z) (C (T (T (h (M v0 x) v1 x) (C (T (T (S (h z x y)) (h z v3 y)) (C (T (C (R v3) (h z z y)) (S (h v1 v2 z))) (R v4))) (R (M (M x x) v1)))) (S (h v4 v1 x))) (R (M (M z z) v0)))) (S (h v3 v0 z))

@[equational_result]
theorem Equation2755_implies_Equation1537 (G: Type _) [Magma G] (h: Equation2755 G) : Equation1537 G := fun x y z =>
  let v0 := M x z
  let v1 := M y y
  let v2 := M v1 (M z v0)
  have h3 := h v0 v0 v0
  let v4 := M v0 v0
  T (T (h x v1 v0) (C (C (R (M v1 v1)) (T (T (T (C h3 (R x)) (S (h z v4 x))) (h z v4 v2)) (C (T (C (R (M v4 v4)) (S (h v0 y z))) (S h3)) (R v2)))) (R v0))) (S (h v2 v1 v0))

@[equational_result]
theorem Equation3193_implies_Equation28 (G: Type _) [Magma G] (h: Equation3193 G) : Equation28 G := fun x y =>
  have h0 := R x
  have h1 := S (h y y x)
  have h2 := R y
  let v3 := M y x
  have h4 := S (h v3 v3 y)
  have h5 := R v3
  have h6 := h v3 y x
  have h7 := C (C (T (C (T (T (C h6 h5) h4) h6) h5) h4) h2) h2
  have h8 := h y v3 v3
  T (h x y y) (C (C (T (C (T (T (T (C (T h8 h7) h2) h1) h8) h7) h2) h1) h0) h0)

@[equational_result]
theorem Equation4210_implies_Equation3794 (G: Type _) [Magma G] (h: Equation4210 G) : Equation3794 G := fun x y z =>
  let v0 := M x y
  let v1 := M z y
  let v2 := M z x
  have h3 := R v0
  have h4 := R v2
  let v5 := M (M v2 y) x
  have h6 := h x y v2
  T (T (T (T h6 (h v5 v2 v0)) (C (T (C (C h6 h4) (R v5)) (S (h v2 v2 v5))) h3)) (C (C (T (h z x v1) (C (S (h x y z)) (R v1))) h4) h3)) (S (h v2 v1 v0))

@[equational_result]
theorem Equation2331_implies_Equation1316 (G: Type _) [Magma G] (h: Equation2331 G) : Equation1316 G := fun x y =>
  let v0 := M y x
  let v1 := M v0 y
  let v2 := M y (M v1 y)
  have h3 := h v2 y
  have h4 := R y
  have h5 := h x y
  T (T h5 (C (T (T (T (h (M y (M y (M x y))) y) (C (C h4 (C h4 (S h5))) h4)) (C (C h4 (T (T (T (h v0 y) (C (C h4 (C h4 (h v1 y))) h4)) (S (h (M y v2) y))) (C h4 h3))) h4)) (S (h (M y (M y (M v2 y))) y))) h4)) (S h3)

@[equational_result]
theorem Equation1430_implies_Equation152 (G: Type _) [Magma G] (h: Equation1430 G) : Equation152 G := fun x y =>
  let v0 := M x x
  have h1 := h x v0 (M x v0)
  have h2 := h x x x
  have h3 := R x
  have h4 := R v0
  let v5 := M x y
  let v6 := M v0 v0
  T (T (T h1 (C h4 (C h3 (S h2)))) (h v6 (M y y) (M y (M v5 v5)))) (C (S (h v0 x x)) (T (C (R v6) (S (h y v5 v5))) (C (T (C h4 (C h3 h2)) (S h1)) (R y))))

@[equational_result]
theorem Equation1577_implies_Equation4677 (G: Type _) [Magma G] (h: Equation1577 G) : Equation4677 G := fun x y z =>
  let v0 := M y x
  let v1 := M v0 z
  let v2 := M x v1
  let v3 := M x y
  let v4 := M v3 z
  let v5 := M x v4
  T (T (h v4 x x) (C (R (M x x)) (T (T (h (M x v5) v0 y) (C (R (M v0 y)) (T (T (T (S (h v5 y x)) (C (h x x y) (C (R v3) (h z x v0)))) (S (h v2 v3 (M x v0)))) (h v2 y x)))) (S (h (M x v2) v0 y))))) (S (h v1 x x))

@[equational_result]
theorem Equation1316_implies_Equation2331 (G: Type _) [Magma G] (h: Equation1316 G) : Equation2331 G := fun x y =>
  let v0 := M x y
  let v1 := M y v0
  let v2 := M (M y v1) y
  have h3 := h v2 y
  have h4 := R y
  have h5 := h x y
  T (T h5 (C h4 (T (T (T (h (M (M (M y x) y) y) y) (C h4 (C (C (S h5) h4) h4))) (C h4 (C (T (T (T (h v0 y) (C h4 (C (C (h v1 y) h4) h4))) (S (h (M v2 y) y))) (C h3 h4)) h4))) (S (h (M (M (M y v2) y) y) y))))) (S h3)

@[equational_result]
theorem Equation2666_implies_Equation2860 (G: Type _) [Magma G] (h: Equation2666 G) : Equation2860 G := fun x y z =>
  let v0 := M x y
  let v1 := M x v0
  let v2 := M v1 z
  let v3 := M v2 z
  have h4 := h v3 v0 v0
  have h5 := R v0
  let v6 := M v3 v0
  have h7 := h v2 z z
  T (T (h x v0 y) (C (T (C (T (T (T (h v1 z z) (C (C h7 h7) (R z))) (S (h (M v3 v3) z z))) (C h4 h4)) h5) (S (h (M v6 v6) v0 v0))) h5)) (S h4)

@[equational_result]
theorem Equation2722_implies_Equation1913 (G: Type _) [Magma G] (h: Equation2722 G) : Equation1913 G := fun x y z =>
  let v0 := M x z
  let v1 := M y v0
  let v2 := M v1 (M z y)
  let v3 := M v1 v2
  have h4 := R y
  T (T (h x v1 v2) (C (C (T (T (T (h (M v1 x) v0 y) (C (S (h z x v1)) h4)) (C (T (h z v2 v1) (C (C (S (h v0 y z)) (R v3)) (R v1))) h4)) (S (h v3 v0 y))) (R (M v2 v1))) (R v2))) (S (h v2 v1 v2))

@[equational_result]
theorem Equation2135_implies_Equation477 (G: Type _) [Magma G] (h: Equation2135 G) : Equation477 G := fun x y =>
  let v0 := M y y
  let v1 := M y v0
  have h2 := h y y
  let v3 := M v0 y
  let v4 := M (M v0 v0) v0
  have h5 := R v3
  let v6 := M (M v1 v1) v1
  T (h x v1) (C (T (T (h v6 y) (C h5 (T (T (T (T (C (R v6) (h y v0)) (S (h v4 v1))) (h v4 y)) (C h5 (T (C (R v4) h2) (S (h v3 v0))))) (S (h v0 y))))) (S h2)) (R (M x v1)))

@[equational_result]
theorem Equation1992_implies_Equation19 (G: Type _) [Magma G] (h: Equation1992 G) : Equation19 G := fun x y z =>
  let v0 := M x x
  let v1 := M x v0
  have h2 := h x v1 x
  have h3 := R v0
  have h4 := h x x x
  have h5 := T h2 (C (S h4) h3)
  T (h x y y) (C (T (C (h y x x) (R (M y y))) (S (h y v1 y))) (T (h v0 z z) (C (T (C (h z x x) (R (M z z))) (S (h z v1 z))) (T (T (T (C (h v0 x x) (C h5 h5)) (S (h v1 v1 v0))) (C h4 h3)) (S h2)))))

@[equational_result]
theorem Equation3159_implies_Equation166 (G: Type _) [Magma G] (h: Equation3159 G) : Equation166 G := fun x y =>
  have h0 := R x
  let v1 := M x x
  have h2 := h x x v1
  have h3 := h x v1 x
  have h4 := S (h y x y)
  have h5 := R y
  have h6 := C (T (C (C (T (C h2 h0) (S h3)) h0) h5) (R (M v1 y))) h5
  have h7 := h y x x
  T (h x y y) (C (C (T (C (T (T (T (C (T h7 h6) h5) h4) h7) h6) h5) h4) h0) (T h3 (C (S h2) h0)))

@[equational_result]
theorem Equation3620_implies_Equation3959 (G: Type _) [Magma G] (h: Equation3620 G) : Equation3959 G := fun x y z =>
  let v0 := M x z
  let v1 := M y v0
  let v2 := M v1 z
  let v3 := M v2 x
  let v4 := M v1 y
  have h5 := R v2
  T (T (T (T (h x y v1) (h v1 (M v4 x) v2)) (C h5 (C (C h5 (T (h v4 x v2) (C h5 (T (h v3 v4 y) (C (R y) (T (C (S (h y v0 y)) (R v3)) (S (h x z v1)))))))) (R v1)))) (S (h v1 (M v2 v1) v2))) (S (h v1 z v1))

@[equational_result]
theorem Equation909_implies_Equation55 (G: Type _) [Magma G] (h: Equation909 G) : Equation55 G := fun x y =>
  let v0 := M y x
  let v1 := M y v0
  have h2 := h v1 x
  let v3 := M x v1
  have h4 := h v0 y
  have h5 := R x
  have h6 := h x x
  have h7 := S h6
  let v8 := M x x
  T h6 (C h5 (T (T (h (M v8 v8) x) (C h5 (T (T (C h7 h7) (C h5 (T (T (T (h x y) (C (R y) (C h4 h4))) (S (h (M v1 v1) y))) (C h2 h2)))) (S (h (M v3 v3) x))))) (S h2)))

@[equational_result]
theorem Equation2062_implies_Equation258 (G: Type _) [Magma G] (h: Equation2062 G) : Equation258 G := fun x y =>
  let v0 := M x x
  let v1 := M v0 y
  have h2 := h v0 y y
  have h3 := R v1
  have h4 := h v0 x y
  let v5 := M v0 x
  let v6 := M v5 x
  have h7 := h x x x
  T (T (h x v1 x) (C (C (T (T (C (T (T h7 (C (T (h v5 x v0) (C (R (M v6 x)) (S h7))) h4)) (S (h v6 x v1))) h3) (S h4)) h2) h3) h2)) (S (h (M v1 y) v1 v1))

@[equational_result]
theorem Equation3772_implies_Equation41 (G: Type _) [Magma G] (h: Equation3772 G) : Equation41 G := fun x y z =>
  let v0 := M x x
  let v1 := M z y
  have h2 := h x z y
  have h3 := h x x x
  have h4 := h x x z
  have h5 := S h4
  have h6 := h v0 (M x z) v0
  have h7 := h z x x
  T (T (T (T (T (T (T h3 (C h4 h4)) (S h6)) (S h7)) (h z x z)) (C (T h2 (C (R v1) (T (T (T h7 h6) (C h5 h5)) (S h3)))) h2)) (S (h (M z x) v1 v0))) (S (h y z x))

@[equational_result]
theorem Equation1260_implies_Equation10 (G: Type _) [Magma G] (h: Equation1260 G) : Equation10 G := fun x y =>
  let v0 := M y x
  let v1 := M x v0
  have h2 := S (h y y x)
  let v3 := M (M v0 y) x
  have h4 := S (h y x v0)
  let v5 := M (M v1 y) v0
  have h6 := R v5
  have h7 := R x
  T (h x y v5) (C h7 (T (T (C (C h4 h7) h6) (C (R v0) (T (h v5 y v3) (C h6 (T (C (T (C h2 h6) h4) (R v3)) h2))))) (S (h v0 v1 y))))
