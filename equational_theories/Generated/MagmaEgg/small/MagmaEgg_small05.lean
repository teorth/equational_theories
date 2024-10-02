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
theorem Equation1932_implies_Equation680 (G: Type _) [Magma G] (h: Equation1932 G) : Equation680 G := fun x y =>
  let v0 := M y y
  let v1 := M v0 y
  let v2 := M v1 (M v1 v1)
  T (h x v1) (C (T (T (h v2 v0) (C (R (M v0 (M v0 v0))) (T (C (R v2) (h v0 y)) (S (h (M y v0) v1))))) (S (h y v0))) (R (M x v1)))

@[equational_result]
theorem Equation2180_implies_Equation2373 (G: Type _) [Magma G] (h: Equation2180 G) : Equation2373 G := fun x y z =>
  let v0 := M x z
  let v1 := M z v0
  let v2 := M y v1
  T (T (T (h x v1 z) (C (S (h z z v0)) (R v0))) (h v1 (M v2 y) v2)) (C (S (h v2 v2 y)) (T (C (h v1 v1 y) (R v2)) (S (h y (M v1 y) v1))))

@[equational_result]
theorem Equation3147_implies_Equation3692 (G: Type _) [Magma G] (h: Equation3147 G) : Equation3692 G := fun x y z =>
  let v0 := M x x
  let v1 := M z z
  let v2 := M (M y y) v1
  have h3 := R v0
  T (T (T (h v0 v0 v0) (C (S (h v0 x v0)) h3)) (C (T (T (h v0 v1 v0) (C (S (h v1 z v0)) h3)) (C (h v1 y v2) h3)) h3)) (S (h v2 v2 v0))

@[equational_result]
theorem Equation3791_implies_Equation3740 (G: Type _) [Magma G] (h: Equation3791 G) : Equation3740 G := fun x y z =>
  let v0 := M z x
  let v1 := M y z
  T (T (T (T (T (T (h x y z) (h v0 v1 (M x y))) (C (S (h y z x)) (S (h z x y)))) (h v1 v0 (M z z))) (C (S (h z y z)) (S (h x z z)))) (h (M z y) (M x z) (M y x))) (C (S (h x z y)) (S (h z y x)))

@[equational_result]
theorem Equation3804_implies_Equation4098 (G: Type _) [Magma G] (h: Equation3804 G) : Equation4098 G := fun x y z =>
  let v0 := M y y
  let v1 := M v0 z
  let v2 := M v0 x
  T (T (T (h x x v0) (h v2 (M x v0) v1)) (C (S (h x z v0)) (T (C (R v2) (T (h v0 z v0) (C (R v1) (S (h y y y))))) (S (h v1 x v0))))) (S (h v1 z x))

@[equational_result]
theorem Equation3810_implies_Equation4647 (G: Type _) [Magma G] (h: Equation3810 G) : Equation4647 G := fun x y z =>
  let v0 := M x y
  let v1 := M z y
  let v2 := M v1 x
  let v3 := M v1 z
  T (T (T (h v0 x v1) (h v2 (M v1 v0) v3)) (C (S (h v0 z v1)) (T (h v3 v2 (M v1 y)) (C (S (h x y v1)) (S (h z y v1)))))) (S (h v1 z v0))

@[equational_result]
theorem Equation492_implies_Equation2573 (G: Type _) [Magma G] (h: Equation492 G) : Equation2573 G := fun x y z =>
  let v0 := M z x
  let v1 := M v0 y
  have h2 := R v1
  T (h x v0 z) (C (T (h v0 y v1) (C (R y) (T (C (R v0) (C h2 (C h2 (T (h y v1 v0) (C h2 (S (h v0 y v0))))))) (S (h v1 v0 v1))))) (S (h z x z)))

@[equational_result]
theorem Equation572_implies_Equation1876 (G: Type _) [Magma G] (h: Equation572 G) : Equation1876 G := fun x y z =>
  let v0 := M y z
  let v1 := M x v0
  let v2 := M v1 (M z y)
  have h3 := R x
  T (T (h x v0 x) (C (R v0) (C h3 (C h3 (T (h v1 v2 y) (C (R v2) (C (R y) (S (h z y v1))))))))) (S (h v2 v0 x))

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
theorem Equation2167_implies_Equation2992 (G: Type _) [Magma G] (h: Equation2167 G) : Equation2992 G := fun x y z =>
  let v0 := M z y
  let v1 := M y v0
  have h2 := S (h z v1 x)
  let v3 := M v1 x
  T (h x y v0) (C (R v3) (T (C (T (h y (M v3 z) v3) (C (C h2 (R y)) h2)) (R v0)) (S (h z z y))))

@[equational_result]
theorem Equation2180_implies_Equation692 (G: Type _) [Magma G] (h: Equation2180 G) : Equation692 G := fun x y z =>
  let v0 := M z y
  let v1 := M v0 z
  let v2 := M x v1
  T (h x (M v1 z) v1) (C (T (T (S (h v1 v1 z)) (C (h v0 v0 z) (T (h z (M y v2) y) (C (S (h y y v2)) (R v0))))) (S (h y v1 v0))) (R v2))

@[equational_result]
theorem Equation3193_implies_Equation3 (G: Type _) [Magma G] (h: Equation3193 G) : Equation3 G := fun x =>
  have h0 := R x
  let v1 := M x x
  have h2 := R v1
  have h3 := C (S (h v1 x x)) h2
  have h4 := h v1 v1 x
  T (h x x x) (C (T (C (C (T (T h4 h3) (C (T h4 h3) h2)) h0) h0) (S (h x v1 v1))) h0)

@[equational_result]
theorem Equation3290_implies_Equation320 (G: Type _) [Magma G] (h: Equation3290 G) : Equation320 G := fun x y z =>
  let v0 := M x x
  let v1 := M y (M z z)
  have h2 := S (h x v0 x)
  T (h x y v0) (C (R y) (T (T (T h2 (h x v1 v0)) (C (R v1) (T (T h2 (h x v0 v0)) (C (R v0) (T (T h2 (h x z v0)) (C (R z) h2)))))) (S (h z v1 v0))))

@[equational_result]
theorem Equation3370_implies_Equation4026 (G: Type _) [Magma G] (h: Equation3370 G) : Equation4026 G := fun x y z =>
  let v0 := M z (M z y)
  let v1 := M v0 (M v0 x)
  T (T (T (T (T (h x y v0) (h y v1 y)) (h v1 (M y (M y y)) x)) (C (C (R y) (h y y z)) (C (R x) (S (h x x v0))))) (S (h x (M y (M y v0)) x))) (S (h v0 x y))

@[equational_result]
theorem Equation3804_implies_Equation3692 (G: Type _) [Magma G] (h: Equation3804 G) : Equation3692 G := fun x y z =>
  let v0 := M z z
  T (T (T (T (T (h x x z) (h (M z x) (M x z) v0)) (C (S (h x z z)) (S (h z x z)))) (S (h z z x))) (h z z z)) (C (T (T (T (h z z y) (h (M y z) (M z y) (M y y))) (C (S (h z y y)) (S (h y z y)))) (S (h y y z))) (R v0))

@[equational_result]
theorem Equation3804_implies_Equation3756 (G: Type _) [Magma G] (h: Equation3804 G) : Equation3756 G := fun x y z =>
  let v0 := M y z
  let v1 := M x z
  let v2 := M z y
  T (T (T (T (h x y y) (C (h y y z) (T (T (h x y z) (h v2 v1 (M z z))) (C (S (h x z z)) (S (h z y z)))))) (S (h v1 v0 v2))) (h v1 v0 (M z x))) (C (S (h y x z)) (S (h z z x)))

@[equational_result]
theorem Equation4085_implies_Equation369 (G: Type _) [Magma G] (h: Equation4085 G) : Equation369 G := fun x y z =>
  let v0 := M x x
  let v1 := M v0 x
  have h2 := R v1
  T (h x x z) (C (T (T (T (T (C (h x x v0) (R x)) (S (h x v0 x))) (h x v1 v1)) (C (C (T (S (h x x x)) (h x x y)) h2) h2)) (S (h y v1 v1))) (R z))

@[equational_result]
theorem Equation4162_implies_Equation3417 (G: Type _) [Magma G] (h: Equation4162 G) : Equation3417 G := fun x y z =>
  let v0 := M y x
  let v1 := M z v0
  let v2 := M z v1
  have h3 := R v2
  have h4 := R z
  T (T (h x y v2) (C (C (T (h y x z) (C (T (C (h x y z) h4) (S (h z v0 z))) h4)) h3) h3)) (S (h z v1 v2))

@[equational_result]
theorem Equation508_implies_Equation4297 (G: Type _) [Magma G] (h: Equation508 G) : Equation4297 G := fun x y z =>
  let v0 := M z z
  have h1 := h v0 y z
  have h2 := R y
  have h3 := h y y v0
  have h4 := R x
  T (T (T (C h4 (C h4 (T (h y y z) (C h2 (C h2 (T (C h2 h1) (S h3))))))) (S (h y x y))) h3) (C h2 (S h1))

@[equational_result]
theorem Equation968_implies_Equation4200 (G: Type _) [Magma G] (h: Equation968 G) : Equation4200 G := fun x y z =>
  let v0 := M z x
  let v1 := M v0 z
  let v2 := M v1 y
  have h3 := h y v0 v2
  T (C (R x) (T h3 (C (R v0) (T (h (M (M v2 v0) (M v2 y)) z v0) (C (R z) (C (R v1) (S h3))))))) (S (h v2 x z))

@[equational_result]
theorem Equation1711_implies_Equation2 (G: Type _) [Magma G] (h: Equation1711 G) : Equation2 G := fun x y =>
  let v0 := M (M x x) x
  let v1 := M y y
  let v2 := M y x
  T (T (T (T (T (h x y y) (C (h v2 y x) (R (M v1 y)))) (S (h v0 (M y v2) y))) (h v0 (M x v1) v0)) (C (S (h v1 x x)) (R (M (M v0 v0) v0)))) (S (h y y v0))

@[equational_result]
theorem Equation2146_implies_Equation1523 (G: Type _) [Magma G] (h: Equation2146 G) : Equation1523 G := fun x y z =>
  let v0 := M z z
  let v1 := M x v0
  let v2 := M y y
  let v3 := M v2 v1
  T (T (h x v3 v3) (C (R (M (M v3 v3) v3)) (T (T (C (h x z v0) (R v3)) (S (h v2 v0 v1))) (h v2 y v1)))) (S (h v3 v3 v3))

@[equational_result]
theorem Equation2666_implies_Equation261 (G: Type _) [Magma G] (h: Equation2666 G) : Equation261 G := fun x y =>
  have h0 := R x
  let v1 := M x y
  have h2 := h v1 x y
  have h3 := h x y y
  T h3 (C (T (h (M v1 v1) x y) (C (T (C (T (C (C h2 h2) h0) (S (h (M (M v1 x) (M v1 y)) x x))) (S h3)) (S h2)) h0)) (R y))

@[equational_result]
theorem Equation3290_implies_Equation4346 (G: Type _) [Magma G] (h: Equation3290 G) : Equation4346 G := fun x y z =>
  let v0 := M z z
  let v1 := M y y
  have h2 := S (h y v1 y)
  T (T (T (C (R x) (T (h y v1 v1) (C (R v1) (T (T h2 (h y z v1)) (C (R z) h2))))) (S (h z x v1))) (h z y v0)) (C (R y) (S (h z v0 z)))

@[equational_result]
theorem Equation3357_implies_Equation41 (G: Type _) [Magma G] (h: Equation3357 G) : Equation41 G := fun x y z =>
  have h0 := R z
  let v1 := M x y
  let v2 := M x v1
  T (T (T (T (T (h x x y) (h x v2 z)) (S (h z v2 z))) (C h0 (T (h x v1 x) (S (h z v1 x))))) (C h0 (T (C h0 (T (h x y x) (S (h z y x)))) (R (M z (M z y)))))) (S (h y z y))

@[equational_result]
theorem Equation3417_implies_Equation4162 (G: Type _) [Magma G] (h: Equation3417 G) : Equation4162 G := fun x y z =>
  let v0 := M y x
  let v1 := M v0 z
  let v2 := M v1 z
  have h3 := R z
  have h4 := R v2
  T (T (h x y v2) (C h4 (C h4 (T (h y x z) (C h3 (T (C h3 (h x y z)) (S (h v0 z z)))))))) (S (h v1 z v2))

@[equational_result]
theorem Equation3553_implies_Equation4023 (G: Type _) [Magma G] (h: Equation3553 G) : Equation4023 G := fun x y z =>
  let v0 := M z x
  let v1 := M z v0
  have h2 := R v1
  let v3 := M v0 x
  T (T (h x y v1) (C (R y) (C (T (h x v1 v3) (C h2 (T (C (S (h z x x)) (R v3)) (S (h z v0 x))))) h2))) (S (h v1 y v1))

@[equational_result]
theorem Equation3607_implies_Equation4135 (G: Type _) [Magma G] (h: Equation3607 G) : Equation4135 G := fun x y z =>
  let v0 := M x y
  let v1 := M v0 z
  have h2 := h x y v1
  let v3 := M (M y v1) x
  T (T (T h2 (h v1 v3 v0)) (C (R v0) (C (T (h v3 v0 z) (C (R z) (S h2))) (R v1)))) (S (h v1 z v0))

@[equational_result]
theorem Equation3776_implies_Equation4369 (G: Type _) [Magma G] (h: Equation3776 G) : Equation4369 G := fun x y z =>
  let v0 := M y x
  let v1 := M z v0
  let v2 := M y z
  let v3 := M v0 y
  T (T (T (h x v2 v1) (C (R (M v2 v1)) (T (T (h v1 x v0) (C (h x v0 y) (R (M v0 v1)))) (S (h v1 v3 v0))))) (S (h v3 v2 v1))) (S (h z v0 y))

@[equational_result]
theorem Equation3790_implies_Equation3533 (G: Type _) [Magma G] (h: Equation3790 G) : Equation3533 G := fun x y z =>
  let v0 := M z y
  have h1 := h y y y
  let v2 := M y y
  T (T (T (h x y y) (C (R (M y x)) h1)) (S (h x v2 y))) (C (R x) (T (T (T (h y y z) (h v0 v2 x)) (C (R (M x v0)) (S h1))) (S (h v0 y x))))

@[equational_result]
theorem Equation3791_implies_Equation3692 (G: Type _) [Magma G] (h: Equation3791 G) : Equation3692 G := fun x y z =>
  let v0 := M z z
  T (T (T (T (h x x v0) (h (M v0 x) (M x v0) (M x x))) (C (S (h x v0 x)) (S (h v0 x x)))) (S (h v0 v0 x))) (C (T (T (T (h z z y) (h (M y z) (M z y) v0)) (C (S (h z y z)) (S (h y z z)))) (S (h y y z))) (R v0))

@[equational_result]
theorem Equation3804_implies_Equation3286 (G: Type _) [Magma G] (h: Equation3804 G) : Equation3286 G := fun x y z =>
  let v0 := M z z
  let v1 := M y v0
  let v2 := M x v0
  T (T (T (h x x v0) (h (M v0 x) v2 v1)) (C (T (C (T (h y v0 v0) (C (S (h z z z)) (R v1))) (R v2)) (S (h x v1 v0))) (S (h y x v0)))) (S (h y v1 x))

@[equational_result]
theorem Equation3804_implies_Equation4026 (G: Type _) [Magma G] (h: Equation3804 G) : Equation4026 G := fun x y z =>
  let v0 := M z y
  let v1 := M z v0
  let v2 := M v0 v1
  T (T (T (T (T (h x y z) (h v0 (M x z) v1)) (C (S (h x v0 z)) (R v2))) (h (M x v0) v2 (M v1 x))) (C (S (h v0 x v1)) (S (h v1 v0 x)))) (S (h v1 x v0))

@[equational_result]
theorem Equation3804_implies_Equation4106 (G: Type _) [Magma G] (h: Equation3804 G) : Equation4106 G := fun x y z =>
  let v0 := M y z
  let v1 := M v0 y
  T (T (T (h x x v1) (C (h v1 x x) (T (T (T (h x v1 v0) (C (S (h v0 z y)) (R (M x v0)))) (S (h x z v0))) (h x z x)))) (S (h (M x z) (M v1 x) (M x x)))) (S (h v1 z x))

@[equational_result]
theorem Equation4176_implies_Equation4200 (G: Type _) [Magma G] (h: Equation4176 G) : Equation4200 G := fun x y z =>
  let v0 := M z x
  let v1 := M v0 z
  have h2 := R v0
  let v3 := M y v0
  T (T (h x y v0) (C (T (T (h v3 x v0) (C (C (T (h x v0 v0) (C (S (h v0 z x)) h2)) (R v3)) h2)) (S (h v3 v1 v0))) h2)) (S (h v1 y v0))

@[equational_result]
theorem Equation489_implies_Equation4458 (G: Type _) [Magma G] (h: Equation489 G) : Equation4458 G := fun x y z =>
  let v0 := M z y
  let v1 := M v0 z
  let v2 := M y x
  T (T (T (C (R x) (h v2 y x)) (S (h y x v2))) (h y v0 z)) (C (R v0) (T (C (R y) (T (T (C (R z) (h v1 v0 z)) (S (h v0 z v1))) (h v0 z y))) (S (h z y v0))))

@[equational_result]
theorem Equation928_implies_Equation2474 (G: Type _) [Magma G] (h: Equation928 G) : Equation2474 G := fun x y z =>
  let v0 := M y y
  let v1 := M v0 z
  let v2 := M x v1
  have h3 := R x
  have h4 := S (h y x x)
  T (T (T (h x x (M (M x x) (M y x))) (C h3 (C h4 h4))) (C h3 (h v0 v2 z))) (S (h (M v2 z) x v1))

@[equational_result]
theorem Equation1964_implies_Equation543 (G: Type _) [Magma G] (h: Equation1964 G) : Equation543 G := fun x y z =>
  let v0 := M y z
  let v1 := M x v0
  let v2 := M z v1
  let v3 := M y v2
  T (T (h x v2 z) (C (T (T (S (h v0 z x)) (h v0 z v3)) (C (C (R z) (S (h v1 y z))) (R (M z v3)))) (R (M v2 z)))) (S (h v3 v2 z))

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
theorem Equation3404_implies_Equation3294 (G: Type _) [Magma G] (h: Equation3404 G) : Equation3294 G := fun x y z =>
  let v0 := M z (M y z)
  let v1 := M y v0
  let v2 := M v1 y
  T (T (T (h x x v0) (C (R v0) (T (C (R x) (h v0 x y)) (S (h v1 y x))))) (h v0 v2 y)) (C (R y) (T (h v2 v1 z) (C (R z) (S (h y z v1)))))

@[equational_result]
theorem Equation3417_implies_Equation3414 (G: Type _) [Magma G] (h: Equation3417 G) : Equation3414 G := fun x y z =>
  have h0 := h y x z
  let v1 := M z (M z (M x y))
  have h2 := h x y v1
  have h3 := R v1
  T (T (T h2 (C h3 (T (T (C h3 h0) (h v1 v1 v1)) (C h3 (T (C h3 (C h3 (S h0))) (S h2)))))) (S (h y x v1))) h0

@[equational_result]
theorem Equation3567_implies_Equation4200 (G: Type _) [Magma G] (h: Equation3567 G) : Equation4200 G := fun x y z =>
  let v0 := M z x
  let v1 := M v0 z
  T (T (h x y v0) (C (R y) (T (R (M (M v0 x) v0)) (C (T (T (h v0 x v1) (C (R x) (T (S (h x (M v1 v0) z)) (S (h z x v0))))) (h x v0 z)) (R v0))))) (S (h v1 y v0))

@[equational_result]
theorem Equation3804_implies_Equation3607 (G: Type _) [Magma G] (h: Equation3804 G) : Equation3607 G := fun x y z =>
  let v0 := M y z
  let v1 := M v0 x
  let v2 := M z x
  T (T (T (T (T (T (h x y z) (C (h z y x) (h x z y))) (S (h v0 v2 (M x y)))) (h v0 v2 v1)) (C (R (M v1 v2)) (h v0 v1 x))) (S (h (M x v1) v2 v1))) (S (h z v1 x))

@[equational_result]
theorem Equation3979_implies_Equation4229 (G: Type _) [Magma G] (h: Equation3979 G) : Equation4229 G := fun x y z =>
  have h0 := R x
  let v1 := M z z
  let v2 := M (M v1 y) x
  let v3 := M y (M v2 v2)
  T (T (T (T (h x y z) (C (T (h y v1 z) (h (M v1 v1) y v2)) h0)) (S (h x v3 v1))) (h x v3 z)) (C (S (h v1 y v2)) h0)

@[equational_result]
theorem Equation4191_implies_Equation41 (G: Type _) [Magma G] (h: Equation4191 G) : Equation41 G := fun x y z =>
  have h0 := R y
  let v1 := M z x
  let v2 := M v1 x
  T (T (T (T (T (h x x z) (h v2 x x)) (S (h v2 y x))) (C (T (h v1 x x) (S (h v1 y x))) h0)) (C (T (C (T (h z x x) (S (h z y x))) h0) (R (M (M z y) y))) h0)) (S (h y z z))

@[equational_result]
theorem Equation522_implies_Equation2519 (G: Type _) [Magma G] (h: Equation522 G) : Equation2519 G := fun x y z =>
  let v0 := M x z
  let v1 := M y (M v0 y)
  let v2 := M v1 z
  have h3 := R v2
  T (T (h x v2 z) (C h3 (C h3 (C (R z) (T (h v0 v2 y) (C h3 (T (C h3 (h v1 v2 z)) (S (h z v2 v2))))))))) (S (h v2 v2 z))

@[equational_result]
theorem Equation522_implies_Equation3364 (G: Type _) [Magma G] (h: Equation522 G) : Equation3364 G := fun x y z =>
  let v0 := M z (M x z)
  let v1 := M y v0
  have h2 := h x v0 z
  have h3 := R v1
  have h4 := R x
  T (C h4 (T (h y x v1) (C h4 (C h4 (T (C h3 (T (S (h x y z)) h2)) (C h3 (S h2))))))) (S (h v1 x x))

@[equational_result]
theorem Equation1060_implies_Equation109 (G: Type _) [Magma G] (h: Equation1060 G) : Equation109 G := fun x y z =>
  let v0 := M y (M x y)
  have h1 := C (h y y x) (R y)
  let v2 := M y y
  let v3 := M v2 (M z v2)
  T (h x v2 z) (C (R x) (T (T (C (R v3) h1) (S (h v3 y v0))) (C (R v2) (T (C (R z) h1) (S (h z y v0))))))

@[equational_result]
theorem Equation1933_implies_Equation2 (G: Type _) [Magma G] (h: Equation1933 G) : Equation2 G := fun x y =>
  let v0 := M x (M x x)
  let v1 := M y y
  let v2 := M x y
  T (T (T (T (T (h x y y) (C (R (M y v1)) (h v2 x x))) (S (h v0 y (M v2 x)))) (h v0 v0 (M v1 y))) (C (R (M v0 (M v0 v0))) (S (h v1 x y)))) (S (h y v0 y))

@[equational_result]
theorem Equation2722_implies_Equation3185 (G: Type _) [Magma G] (h: Equation2722 G) : Equation3185 G := fun x y z =>
  let v0 := M y z
  let v1 := M v0 x
  let v2 := M v1 z
  let v3 := M v2 y
  let v4 := M v0 v3
  T (h x v0 y) (C (C (R v1) (T (C (T (h y v2 v4) (C (C (R v3) (S (h z y v2))) (R v4))) (R v0)) (S (h z v3 v0)))) (R y))

@[equational_result]
theorem Equation2952_implies_Equation5 (G: Type _) [Magma G] (h: Equation2952 G) : Equation5 G := fun x y =>
  let v0 := M y x
  let v1 := M v0 (M v0 v0)
  let v2 := M (M x (M x x)) x
  have h3 := h v2 x x
  T (h x v0 y) (C (T (C (T (h v1 x x) (C (T h3 (C (R v2) h3)) (R v1))) (R y)) (S (h y v2 v1))) (R x))

@[equational_result]
theorem Equation3195_implies_Equation1504 (G: Type _) [Magma G] (h: Equation3195 G) : Equation1504 G := fun x y z =>
  let v0 := M y z
  let v1 := M z v0
  let v2 := M y x
  T (h x v2 y) (C (S (h v2 y x)) (T (h y z v0) (C (T (C (T (T (C (h v1 z v0) (R z)) (S (h v0 v1 z))) (h v0 y z)) (R y)) (S (h z v0 y))) (R v0))))

@[equational_result]
theorem Equation3404_implies_Equation3331 (G: Type _) [Magma G] (h: Equation3404 G) : Equation3331 G := fun x y z =>
  let v0 := M y z
  let v1 := M z v0
  let v2 := M v1 x
  have h3 := R v0
  T (T (h x y v1) (C (R v1) (T (T (h y v2 v0) (C h3 (C (R v2) (T (h v0 y v0) (C h3 (S (h z v0 y))))))) (S (h v1 v2 v0))))) (S (h x v1 v1))

@[equational_result]
theorem Equation3736_implies_Equation3525 (G: Type _) [Magma G] (h: Equation3736 G) : Equation3525 G := fun x y z =>
  let v0 := M y y
  have h1 := h y y y
  let v2 := M x y
  let v3 := M v2 v2
  T (T (T (h x y v3) (C (R (M x v3)) h1)) (S (h x v0 v3))) (C (R x) (T (T h1 (C (h y y z) (R v0))) (S (h (M y z) y v0))))

@[equational_result]
theorem Equation4176_implies_Equation4098 (G: Type _) [Magma G] (h: Equation4176 G) : Equation4098 G := fun x y z =>
  let v0 := M (M y y) z
  have h1 := R v0
  let v2 := M y v0
  T (T (h x x y) (C (T (T (T (T (C (h x y v0) (R x)) (S (h v0 v2 x))) (h v0 v2 v0)) (C (S (h v0 y v0)) h1)) (C (S (h z y y)) h1)) (R y))) (S (h v0 z y))

@[equational_result]
theorem Equation4182_implies_Equation3334 (G: Type _) [Magma G] (h: Equation4182 G) : Equation3334 G := fun x y z =>
  let v0 := M z y
  have h1 := R x
  let v2 := M (M y y) y
  T (T (T (T (T (h x y y) (C (C (h y y y) (R y)) h1)) (S (h x v2 y))) (h x v2 z)) (C (T (C (S (h z y y)) (R z)) (h v0 z v0)) h1)) (S (h x (M z v0) v0))

@[equational_result]
theorem Equation492_implies_Equation1504 (G: Type _) [Magma G] (h: Equation492 G) : Equation1504 G := fun x y z =>
  let v0 := M y z
  have h1 := R v0
  let v2 := M y x
  T (h x v2 y) (C (R v2) (T (T (S (h y x y)) (h y z v0)) (C (R z) (T (C (R y) (C h1 (C h1 (T (h z v0 y) (C h1 (S (h y z y))))))) (S (h v0 y v0))))))

@[equational_result]
theorem Equation1496_implies_Equation1523 (G: Type _) [Magma G] (h: Equation1496 G) : Equation1523 G := fun x y z =>
  let v0 := M y y
  let v1 := M x x
  let v2 := M y v1
  T (h x x z) (C (T (T (h v1 y x) (C (T (T (h v2 v0 x) (C (T (S (h y y x)) (h y y y)) (R (M v0 v1)))) (S (h (M y v0) v0 x))) (R v2))) (S (h v0 y x))) (R (M x (M z z))))

@[equational_result]
theorem Equation2113_implies_Equation3810 (G: Type _) [Magma G] (h: Equation2113 G) : Equation3810 G := fun x y z =>
  let v0 := M z x
  let v1 := M z y
  let v2 := M v1 v0
  have h3 := h y v1 v0
  have h4 := R v2
  T (T (C (T (h x v1 v0) (C (S (h y z x)) h4)) (R y)) (C (C h3 h4) h3)) (S (h v2 (M (M v1 y) v0) v2))

@[equational_result]
theorem Equation2554_implies_Equation246 (G: Type _) [Magma G] (h: Equation2554 G) : Equation246 G := fun x y z =>
  let v0 := M z z
  let v1 := M (M z x) z
  have h2 := C (R z) (h z z x)
  let v3 := M (M v0 y) v0
  T (h x v0 y) (C (T (T (C h2 (R v3)) (S (h v3 z v1))) (C (T (C h2 (R y)) (S (h y z v1))) (R v0))) (R x))

@[equational_result]
theorem Equation3120_implies_Equation1165 (G: Type _) [Magma G] (h: Equation3120 G) : Equation1165 G := fun x y z =>
  let v0 := M y x
  let v1 := M (M z v0) z
  let v2 := M y v1
  have h3 := R v2
  T (T (h x y v2) (C (C (C (T (h v0 z v2) (C (T (C (h v1 y v2) h3) (S (h y v2 v2))) h3)) (R y)) h3) h3)) (S (h v2 y v2))

@[equational_result]
theorem Equation3211_implies_Equation2180 (G: Type _) [Magma G] (h: Equation3211 G) : Equation2180 G := fun x y z =>
  let v0 := M x z
  let v1 := M y z
  have h2 := R v1
  T (h x v0 z) (C (T (T (S (h z x z)) (h z y v1)) (C (T (C (C (C (T (h y v1 z) (C (S (h z y z)) h2)) h2) h2) (R z)) (S (h v1 z v1))) (R y))) (R v0))

@[equational_result]
theorem Equation3417_implies_Equation3601 (G: Type _) [Magma G] (h: Equation3417 G) : Equation3601 G := fun x y z =>
  let v0 := M y x
  have h1 := R z
  have h2 := h x y v0
  have h3 := R v0
  T (T (T (T (T h2 (C h3 (T (h v0 v0 v0) (C h3 (S h2))))) (S (h y x v0))) (h y x z)) (C h1 (C h1 (h x y z)))) (C h1 (S (h v0 z z)))

@[equational_result]
theorem Equation3553_implies_Equation4182 (G: Type _) [Magma G] (h: Equation3553 G) : Equation4182 G := fun x y z =>
  let v0 := M (M y z) z
  have h1 := C (h y v0 z) (R v0)
  let v2 := M (M x x) x
  T (T (T (T (T (T (T (T (h x y x) (h y v2 v0)) (C (R v2) h1)) (S (h v0 v2 v0))) (S (h x v0 x))) (S (h y x z))) (h y x v0)) (C (R x) h1)) (S (h v0 x v0))

@[equational_result]
theorem Equation3566_implies_Equation395 (G: Type _) [Magma G] (h: Equation3566 G) : Equation395 G := fun x y z =>
  have h0 := R y
  have h1 := R x
  let v2 := M z x
  let v3 := M v2 z
  T (T (T (h x y z) (C h0 (C (h z x v2) h0))) (S (h (M v3 x) y x))) (C (T (T (h v3 x z) (C h1 (C (S (h x z z)) h1))) (S (h z x x))) h0)

@[equational_result]
theorem Equation3751_implies_Equation4544 (G: Type _) [Magma G] (h: Equation3751 G) : Equation4544 G := fun x y z =>
  have h0 := h z y
  let v1 := M y z
  have h2 := h x v1
  have h3 := S h2
  let v4 := M v1 x
  T (T (T (T h2 (h v4 v4)) (C h3 h3)) (S (h v1 x))) (C (T (T (T (h y z) (C h0 h0)) (S (h v1 v1))) (S h0)) (R x))

@[equational_result]
theorem Equation3770_implies_Equation4656 (G: Type _) [Magma G] (h: Equation3770 G) : Equation4656 G := fun x y z =>
  let v0 := M x z
  let v1 := M x y
  T (T (T (h v1 y z) (h (M y z) (M v1 z) (M v0 z))) (C (T (T (T (S (h v0 v1 z)) (C (h x z v1) (h x y v1))) (S (h (M y v1) (M z v1) (M x v1)))) (S (h z y v1))) (S (h v0 y z)))) (S (h v0 z y))

@[equational_result]
theorem Equation3804_implies_Equation4143 (G: Type _) [Magma G] (h: Equation3804 G) : Equation4143 G := fun x y z =>
  let v0 := M x z
  let v1 := M v0 y
  let v2 := M x y
  T (T (T (h x y v1) (C (h v1 y x) (T (T (T (h x v1 y) (h (M y v1) v2 v1)) (C (R (M v1 v2)) (S (h v0 v1 y)))) (S (h v0 v2 v1))))) (S (h v0 (M v1 x) v2))) (S (h v1 z x))

@[equational_result]
theorem Equation4026_implies_Equation3526 (G: Type _) [Magma G] (h: Equation4026 G) : Equation3526 G := fun x y z =>
  let v0 := M y z
  let v1 := M v0 z
  have h2 := R v1
  let v3 := M x (M x z)
  T (T (h x y v1) (C (C h2 (T (h v1 y v3) (C (T (C (R v3) (S (h y z x))) (S (h v0 z x))) h2))) (R x))) (S (h x v1 v1))

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
theorem Equation684_implies_Equation26 (G: Type _) [Magma G] (h: Equation684 G) : Equation26 G := fun x y =>
  let v0 := M (M x y) y
  have h1 := S (h v0 v0 x)
  let v2 := M v0 (M (M v0 x) x)
  let v3 := M x v0
  T (T (h x x y) (C (R x) (T (h v3 v0 v2) (C (R v0) (C (R v3) (T (C h1 (R v2)) h1)))))) (S (h v0 x v0))

@[equational_result]
theorem Equation947_implies_Equation65 (G: Type _) [Magma G] (h: Equation947 G) : Equation65 G := fun x y =>
  let v0 := M y x
  have h1 := h v0 x y
  have h2 := R x
  have h3 := h x y y
  T h3 (C (R y) (T (h (M v0 v0) x y) (C h2 (T (C (S h3) (T (C h2 (C h1 h1)) (S (h (M (M y v0) (M x v0)) x x)))) (S h1)))))

@[equational_result]
theorem Equation949_implies_Equation1790 (G: Type _) [Magma G] (h: Equation949 G) : Equation1790 G := fun x y z =>
  let v0 := M y z
  let v1 := M z x
  let v2 := M v0 (M v1 y)
  have h3 := h v2 v2 v0
  T (T (h x v2 z) (C (R v2) (T (C (R v1) (C h3 (h z v1 y))) (S (h (M (M v0 v2) (M v2 v0)) v1 v2))))) (S h3)

@[equational_result]
theorem Equation1301_implies_Equation3091 (G: Type _) [Magma G] (h: Equation1301 G) : Equation3091 G := fun x y z =>
  let v0 := M (M (M x y) z) y
  let v1 := M v0 z
  let v2 := M (M (M v0 x) v1) x
  have h3 := R z
  have h4 := h v0 v1 x
  T (T (h x z y) (C h3 (T h4 (C (C h4 h3) (R v2))))) (S (h v1 z v2))

@[equational_result]
theorem Equation1504_implies_Equation2573 (G: Type _) [Magma G] (h: Equation1504 G) : Equation2573 G := fun x y z =>
  let v0 := M z x
  let v1 := M y (M v0 y)
  have h2 := h z v1 z
  have h3 := h x z (M v1 z)
  T h3 (C (T (C (T (h z v0 y) (C (T (C (R v0) h2) (S h3)) (R v1))) (h x z x)) (S (h v1 x v0))) (S h2))

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
theorem Equation3185_implies_Equation3091 (G: Type _) [Magma G] (h: Equation3185 G) : Equation3091 G := fun x y z =>
  let v0 := M (M x y) z
  let v1 := M v0 y
  let v2 := M v1 z
  have h3 := R y
  T (T (h x v0 y) (C (T (C (S (h z x y)) h3) (C (T (h z v2 v1) (C (S (h v1 v1 z)) (R v2))) h3)) (R v0))) (S (h v2 v0 y))

@[equational_result]
theorem Equation3364_implies_Equation3526 (G: Type _) [Magma G] (h: Equation3364 G) : Equation3526 G := fun x y z =>
  let v0 := M y z
  let v1 := M v0 z
  let v2 := M v0 (M z v0)
  let v3 := M x (M x x)
  T (T (T (T (h x y x) (h y v3 z)) (C (R v3) (T (T (h z v0 v0) (h v0 v2 z)) (C (R v2) (h z v1 v0))))) (S (h v1 v3 v2))) (S (h x v1 x))

@[equational_result]
theorem Equation3791_implies_Equation4364 (G: Type _) [Magma G] (h: Equation3791 G) : Equation4364 G := fun x y z =>
  let v0 := M z x
  let v1 := M y z
  T (T (T (h x v1 v0) (h (M v0 x) (M v1 v0) (M x v1))) (C (T (T (T (S (h v1 v0 x)) (C (h y z x) (h z x y))) (S (h v0 v1 (M x y)))) (S (h x y z))) (S (h v0 x v1)))) (S (h y v0 x))

@[equational_result]
theorem Equation3810_implies_Equation3823 (G: Type _) [Magma G] (h: Equation3810 G) : Equation3823 G := fun x y z =>
  let v0 := M z z
  let v1 := M y x
  let v2 := M v0 z
  have h3 := h z v1 v0
  T (T (h x y y) (h (M y y) v1 v1)) (C (T (T (T (h v1 v1 z) (C h3 h3)) (S (h v2 v2 (M v0 v1)))) (S (h z z v0))) (S (h y x y)))

@[equational_result]
theorem Equation3810_implies_Equation4307 (G: Type _) [Magma G] (h: Equation3810 G) : Equation4307 G := fun x y z =>
  let v0 := M z y
  let v1 := M x y
  T (T (T (h x v1 z) (h (M z v1) (M z x) (M z v0))) (C (S (h x v0 z)) (T (T (T (S (h v1 v0 z)) (C (h x y v1) (h z y v1))) (S (h (M v1 z) (M v1 x) (M v1 y)))) (S (h x z v1))))) (S (h z v0 x))

@[equational_result]
theorem Equation4216_implies_Equation4023 (G: Type _) [Magma G] (h: Equation4216 G) : Equation4023 G := fun x y z =>
  let v0 := M z x
  let v1 := M z v0
  let v2 := M (M v0 z) v0
  let v3 := M (M y y) y
  T (T (T (T (h x y y) (h v3 x z)) (C (T (T (h v0 z v0) (h v2 v0 z)) (C (h v1 z v0) (R v2))) (R v3))) (S (h v3 v1 v2))) (S (h v1 y y))

@[equational_result]
theorem Equation556_implies_Equation1131 (G: Type _) [Magma G] (h: Equation556 G) : Equation1131 G := fun x y z =>
  let v0 := M z x
  let v1 := M y v0
  let v2 := M v1 z
  have h3 := R z
  have h4 := R y
  T (h x y z) (C h4 (T (T (C h3 (C h4 (T (C (R x) (h z v0 x)) (S (h v0 x v0))))) (C h3 (h v1 v2 z))) (S (h v2 z v2))))

@[equational_result]
theorem Equation572_implies_Equation4458 (G: Type _) [Magma G] (h: Equation572 G) : Equation4458 G := fun x y z =>
  let v0 := M z y
  let v1 := M y x
  let v2 := M x v1
  have h3 := R x
  T (T (T (T (h v2 x x) (C h3 (C h3 (C h3 (T (C (R v2) (h x v1 v1)) (S (h v1 v2 v1))))))) (S (h y x x))) (h y v0 y)) (C (R v0) (S (h z y y)))

@[equational_result]
theorem Equation962_implies_Equation546 (G: Type _) [Magma G] (h: Equation962 G) : Equation546 G := fun x y z =>
  let v0 := M z y
  let v1 := M x v0
  let v2 := M z v1
  let v3 := M y v2
  let v4 := M v3 v0
  T (h x y v0) (C (R y) (C (T (C (R v0) (T (h y v4 v2) (C (R v4) (C (S (h z v2 y)) (R v3))))) (S (h z v0 v3))) (R v1)))

@[equational_result]
theorem Equation1131_implies_Equation775 (G: Type _) [Magma G] (h: Equation1131 G) : Equation775 G := fun x y z =>
  let v0 := M z x
  let v1 := M z (M v0 y)
  let v2 := M y v1
  have h3 := R z
  have h4 := R v2
  T (T (h x v2 z) (C h4 (C (C h4 (T (h v0 z v1) (C h3 (C (S (h y z v0)) (R v1))))) h3))) (S (h v2 v2 z))

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
theorem Equation2196_implies_Equation43 (G: Type _) [Magma G] (h: Equation2196 G) : Equation43 G := fun x y =>
  let v0 := M y x
  let v1 := M x y
  let v2 := M (M v1 x) x
  T (T (T (T (C (h x y v1) (h y v1 x)) (S (h v2 (M y v1) v1))) (h v2 x x)) (C (R (M (M x x) x)) (T (C (R v2) (h x y x)) (S (h (M v0 x) v1 x))))) (S (h v0 x x))

@[equational_result]
theorem Equation2511_implies_Equation2928 (G: Type _) [Magma G] (h: Equation2511 G) : Equation2928 G := fun x y z =>
  let v0 := M x z
  let v1 := M (M y v0) z
  let v2 := M v1 y
  have h3 := R v2
  have h4 := R z
  T (T (h x z v2) (C (C h4 (C (T (h v0 v1 z) (C (C (R v1) (S (h y v0 z))) h4)) h3)) h3)) (S (h v2 z v2))

@[equational_result]
theorem Equation3128_implies_Equation1131 (G: Type _) [Magma G] (h: Equation3128 G) : Equation1131 G := fun x y z =>
  let v0 := M z x
  let v1 := M y v0
  let v2 := M v1 z
  let v3 := M y v2
  have h4 := R y
  T (T (T (h x z y) (C (C (T (C (h v0 y v1) h4) (S (h v1 v1 y))) (R z)) h4)) (C (h v2 y v3) h4)) (S (h v3 v3 y))

@[equational_result]
theorem Equation3914_implies_Equation4153 (G: Type _) [Magma G] (h: Equation3914 G) : Equation4153 G := fun x y z w u =>
  let v0 := M x z
  have h1 := h v0 x
  have h2 := h x z
  have h3 := C (T (h x (M x x)) (S h2)) (R x)
  have h4 := h x y
  T (T (T (T h4 h3) h1) (S (h v0 u))) (C (T (T (T (T (T h2 (S h4)) h4) h3) h1) (S (h v0 w))) (R u))

@[equational_result]
theorem Equation522_implies_Equation4458 (G: Type _) [Magma G] (h: Equation522 G) : Equation4458 G := fun x y z =>
  let v0 := M z y
  let v1 := M y x
  let v2 := M x v1
  have h3 := R x
  T (T (T (T (h v2 x x) (C h3 (C h3 (C h3 (T (C (R v2) (h x v2 v1)) (S (h v1 v2 v2))))))) (S (h y x x))) (h y v0 v0)) (C (R v0) (S (h z v0 y)))

@[equational_result]
theorem Equation2167_implies_Equation1358 (G: Type _) [Magma G] (h: Equation2167 G) : Equation1358 G := fun x y z =>
  let v0 := M z x
  let v1 := M v0 z
  let v2 := M v1 y
  let v3 := M y v2
  T (T (h x v3 v0) (C (T (C (T (C (T (C (h y v0 z) (R v2)) (S (h v1 v1 y))) (R v0)) (S (h z z x))) (R x)) (h v0 y v2)) (R (M v3 v0)))) (S (h v3 v3 v0))

@[equational_result]
theorem Equation2170_implies_Equation4358 (G: Type _) [Magma G] (h: Equation2170 G) : Equation4358 G := fun x y z =>
  let v0 := M z y
  let v1 := M x v0
  have h2 := R (M y z)
  let v3 := M v0 v1
  T (T (C (h x z y) h2) (C (T (C (T (h (M v0 x) v1 v0) (C (S (h v0 x v0)) (R v3))) h2) (S (h v3 z y))) h2)) (S (h v1 z y))

@[equational_result]
theorem Equation2180_implies_Equation1152 (G: Type _) [Magma G] (h: Equation2180 G) : Equation1152 G := fun x y z =>
  let v0 := M x y
  let v1 := M (M z v0) z
  have h2 := h x (M y v1) y
  have h3 := h y y v1
  T h2 (C (S h3) (T (C (h x x y) (T (h y z v0) (C (R v1) (T (C h3 (R v0)) (S h2))))) (S (h v1 v0 x))))

@[equational_result]
theorem Equation2383_implies_Equation562 (G: Type _) [Magma G] (h: Equation2383 G) : Equation562 G := fun x y z =>
  let v0 := M z (M y (M z x))
  let v1 := M y v0
  let v2 := M x (M v1 (M x v0))
  have h3 := R y
  have h4 := h v0 x v1
  T (T (h x z y) (C (T h4 (C (R v2) (C h3 h4))) h3)) (S (h v1 v2 y))

@[equational_result]
theorem Equation3211_implies_Equation4458 (G: Type _) [Magma G] (h: Equation3211 G) : Equation4458 G := fun x y z =>
  let v0 := M z y
  have h1 := R v0
  let v2 := M y x
  T (T (T (C (h x y x) (R v2)) (S (h y v2 x))) (h y z v0)) (C (T (C (C (C (T (h z v0 y) (C (S (h y z y)) h1)) h1) h1) (R y)) (S (h v0 y v0))) (R z))

@[equational_result]
theorem Equation3370_implies_Equation4216 (G: Type _) [Magma G] (h: Equation3370 G) : Equation4216 G := fun x y z =>
  let v0 := M z y
  have h1 := R x
  let v2 := M z v0
  let v3 := M z (M z x)
  T (T (T (T (T (T (h x y z) (h y v3 z)) (h v3 v2 x)) (C (R v2) (C h1 (S (h x x z))))) (S (h x v2 x))) (C h1 (h z v0 v0))) (S (h (M v0 z) x v0))

@[equational_result]
theorem Equation3770_implies_Equation3692 (G: Type _) [Magma G] (h: Equation3770 G) : Equation3692 G := fun x y z =>
  have h0 := S (h z x z)
  let v1 := M x z
  have h2 := S (h y x y)
  let v3 := M x y
  T (h x x x) (C (T (T (T (h x x y) (h v3 v3 (M y y))) (C h2 h2)) (S (h y y x))) (T (T (T (h x x z) (h v1 v1 (M z z))) (C h0 h0)) (S (h z z x))))

@[equational_result]
theorem Equation4162_implies_Equation4135 (G: Type _) [Magma G] (h: Equation4162 G) : Equation4135 G := fun x y z =>
  have h0 := h y x z
  let v1 := M (M (M x y) z) z
  have h2 := R v1
  have h3 := h x y v1
  T (T (T h3 (C (T (T (C h0 h2) (h v1 v1 v1)) (C (T (C (C (S h0) h2) h2) (S h3)) h2)) h2)) (S (h y x v1))) h0

@[equational_result]
theorem Equation4216_implies_Equation4200 (G: Type _) [Magma G] (h: Equation4216 G) : Equation4200 G := fun x y z =>
  let v0 := M x y
  let v1 := M (M z x) z
  have h2 := R v1
  let v3 := M (M v0 y) v0
  have h4 := R v3
  T (T (T (T (T (h x y v0) (h v3 x v1)) (C (C (h v1 x z) h2) h4)) (S (h v3 v1 v1))) (C h4 h2)) (S (h v1 y v0))

@[equational_result]
theorem Equation711_implies_Equation2522 (G: Type _) [Magma G] (h: Equation711 G) : Equation2522 G := fun x y z =>
  let v0 := M (M x z) z
  let v1 := M y v0
  have h2 := R v1
  have h3 := S (h x x x)
  let v4 := M x (M (M x x) x)
  T (h x v1 v4) (C h2 (T (T (C h2 (T (C h3 (R v4)) h3)) (C h2 (h x v1 z))) (S (h y v1 v0))))

@[equational_result]
theorem Equation1507_implies_Equation43 (G: Type _) [Magma G] (h: Equation1507 G) : Equation43 G := fun x y =>
  let v0 := M y x
  let v1 := M x (M x v0)
  let v2 := M x y
  T (T (T (T (h v2 x v2) (C (T (h (M x v2) v0 x) (C (S (h x y x)) (R v1))) (R (M v2 (M v2 x))))) (S (h v1 x v2))) (h v1 (M v0 y) v0)) (C (S (h y v0 x)) (S (h x y v0)))

@[equational_result]
theorem Equation1558_implies_Equation2373 (G: Type _) [Magma G] (h: Equation1558 G) : Equation2373 G := fun x y z =>
  let v0 := M x z
  let v1 := M z v0
  let v2 := M y v1
  let v3 := M v2 y
  T (T (h x v0 v3) (C (R (M v0 v3)) (T (C (R x) (T (C (R v0) (T (C (R v2) (h y z v0)) (S (h v1 y v1)))) (S (h z x z)))) (h v0 v2 y)))) (S (h v3 v0 v3))

@[equational_result]
theorem Equation1588_implies_Equation2 (G: Type _) [Magma G] (h: Equation1588 G) : Equation2 G := fun x y =>
  have h0 := S (h y x y)
  let v1 := M y y
  let v2 := M y v1
  have h3 := R v2
  let v4 := M x y
  T (T (h x x y) (C (R v4) (C (R y) (T (h v4 v4 v2) (C h0 (T (T (C h3 h0) (C h3 (h y y y))) (S (h y y v1)))))))) h0

@[equational_result]
theorem Equation1964_implies_Equation952 (G: Type _) [Magma G] (h: Equation1964 G) : Equation952 G := fun x y z =>
  let v0 := M z x
  let v1 := M v0 (M z y)
  let v2 := M y v1
  have h3 := R v2
  T (T (h x v2 z) (C (C h3 (T (h v0 y v1) (C (T (C (h y v0 z) (R (M v1 v0))) (S (h z v1 v0))) h3))) (R (M v2 z)))) (S (h v2 v2 z))

@[equational_result]
theorem Equation2064_implies_Equation2673 (G: Type _) [Magma G] (h: Equation2064 G) : Equation2673 G := fun x y =>
  let v0 := M y y
  let v1 := M x y
  let v2 := M v1 v0
  let v3 := M v2 y
  have h4 := R v0
  T (T (h x y) (C (C (T (T (h v1 v0) (C (C (h v2 y) h4) (R (M v0 v0)))) (S (h (M v3 y) v0))) (R y)) h4)) (S (h v3 y))

@[equational_result]
theorem Equation2714_implies_Equation1117 (G: Type _) [Magma G] (h: Equation2714 G) : Equation1117 G := fun x y z =>
  let v0 := M x z
  let v1 := M y v0
  let v2 := M v1 z
  have h3 := h x x v0
  T (T (h x x z) (C (T (T (C (C h3 h3) (R v0)) (S (h v0 (M (M x x) (M x v0)) v0))) (h v0 y v2)) (R z))) (S (h (M y v2) v1 z))

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
theorem Equation3979_implies_Equation3350 (G: Type _) [Magma G] (h: Equation3979 G) : Equation3350 G := fun x y z =>
  let v0 := M z z
  let v1 := M x v0
  have h2 := T (h x v0 z) (h (M v0 v0) x z)
  let v3 := M y (M y y)
  T (T (T (T (T (T (h x y y) (h v3 x z)) (C h2 (R v3))) (S (h v3 v1 v0))) (S (h v1 y y))) (C h2 (R y))) (S (h y v1 v0))

@[equational_result]
theorem Equation572_implies_Equation2925 (G: Type _) [Magma G] (h: Equation572 G) : Equation2925 G := fun x y z =>
  let v0 := M y (M x z)
  let v1 := M v0 y
  let v2 := M v1 z
  have h3 := R v2
  have h4 := R y
  T (T (h x z y) (C (R z) (C h4 (T (h v0 y v2) (C h4 (C h3 (T (C h3 (h v1 z z)) (S (h z v2 z))))))))) (S (h v2 z y))

@[equational_result]
theorem Equation928_implies_Equation1117 (G: Type _) [Magma G] (h: Equation928 G) : Equation1117 G := fun x y z =>
  let v0 := M x z
  let v1 := M y v0
  let v2 := M v1 z
  have h3 := h x v2 x
  have h4 := R y
  T (h x y x) (C h4 (T (C (T (C h4 (h x v1 z)) (S (h v2 y v0))) (C h3 h3)) (S (h v2 v2 (M (M v2 x) (M x x))))))

@[equational_result]
theorem Equation928_implies_Equation2538 (G: Type _) [Magma G] (h: Equation928 G) : Equation2538 G := fun x y z =>
  let v0 := M y x
  let v1 := M v0 z
  let v2 := M y v1
  have h3 := h x v0 x
  T (T (h x y x) (C (R y) (T (T (C (R v0) (C h3 h3)) (S (h v0 v0 (M (M v0 x) (M x x))))) (h v0 v2 z)))) (S (h (M v2 z) y v1))

@[equational_result]
theorem Equation1504_implies_Equation2992 (G: Type _) [Magma G] (h: Equation1504 G) : Equation2992 G := fun x y z =>
  let v0 := M z y
  let v1 := M y v0
  let v2 := M v1 x
  have h3 := R v2
  T (T (h x v1 (M x v1)) (C h3 (S (h v1 x v1)))) (C h3 (T (C (T (h y z (M v2 z)) (C (R v0) (S (h z v2 z)))) (h v0 y v0)) (S (h z v0 v1))))

@[equational_result]
theorem Equation1561_implies_Equation4358 (G: Type _) [Magma G] (h: Equation1561 G) : Equation4358 G := fun x y z =>
  let v0 := M z y
  let v1 := M x v0
  let v2 := M y z
  let v3 := M v1 v2
  let v4 := M x v2
  T (T (h v4 z y) (C (R v0) (T (C (R v4) (T (h v2 v1 v2) (C (R v3) (C (R v2) (S (h x y z)))))) (S (h v3 x v2))))) (S (h v1 z y))

@[equational_result]
theorem Equation2944_implies_Equation1181 (G: Type _) [Magma G] (h: Equation2944 G) : Equation1181 G := fun x y z =>
  let v0 := M z (M z x)
  let v1 := M v0 y
  have h2 := R v1
  have h3 := S (h x x x)
  let v4 := M (M x (M x x)) x
  T (h x v4 v1) (C (T (T (C (T (C (R v4) h3) h3) h2) (C (h x z v1) h2)) (S (h y v0 v1))) h2)

@[equational_result]
theorem Equation3559_implies_Equation3451 (G: Type _) [Magma G] (h: Equation3559 G) : Equation3451 G := fun x y z w u =>
  let v0 := M u y
  let v1 := M w v0
  have h2 := h w v0
  have h3 := S h2
  T (T (T (T (T (T (T (h x y) (C (R y) (T (h (M y y) y) (S (h u y))))) (h y v0)) h3) h2) (C (R v0) (T (h (M v0 v0) v0) h3))) (h v0 v1)) (S (h z v1))

@[equational_result]
theorem Equation3770_implies_Equation3820 (G: Type _) [Magma G] (h: Equation3770 G) : Equation3820 G := fun x y z =>
  have h0 := h x y z
  have h1 := h (M y z) (M x z) (M z z)
  have h2 := h z y z
  have h3 := h z x z
  let v4 := M z y
  T (T (T (T h0 h1) (C (S h3) (S h2))) (h (M z x) v4 v4)) (C (S (h z z y)) (T (T (C h3 h2) (S h1)) (S h0)))

@[equational_result]
theorem Equation3791_implies_Equation4477 (G: Type _) [Magma G] (h: Equation3791 G) : Equation4477 G := fun x y z =>
  let v0 := M y y
  let v1 := M x z
  let v2 := M v0 x
  T (T (T (T (T (h x v0 v0) (C (R v2) (S (h y y y)))) (h v2 v0 v1)) (C (T (S (h z v0 x)) (h z v0 v1)) (h v0 v1 z))) (S (h (M v0 v1) (M z v0) (M v1 z)))) (S (h v1 z v0))

