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
theorem Equation3364_implies_Equation4026 (G: Type _) [Magma G] (h: Equation3364 G) : Equation4026 G := fun x y z =>
  let v0 := M z y
  let v1 := M z v0
  have h2 := h z v0 y
  have h3 := R v1
  have h4 := C h3 (T (h y v1 v0) (C h3 (S h2)))
  have h5 := R x
  let v6 := M y (M x y)
  T (T (T (T (T (T (T (T (T (h x y y) (h y v6 v1)) (C (R v6) h4)) (S (h v1 v6 v1))) (S (h x v1 y))) (C h5 h2)) (S (h y x v0))) (h y x v1)) (C h5 h4)) (S (h v1 x v1))

@[equational_result]
theorem Equation3607_implies_Equation4369 (G: Type _) [Magma G] (h: Equation3607 G) : Equation4369 G := fun x y z =>
  let v0 := M y z
  let v1 := M x v0
  let v2 := M y x
  have h3 := R z
  let v4 := M z v2
  have h5 := h x v0 v4
  let v6 := M (M v0 v4) x
  T (T h5 (h v4 v6 z)) (C h3 (T (C (T (h v6 z v2) (C (R v2) (S h5))) (T (T (C h3 (h y x v0)) (S (h (M v1 y) y z))) (C (h v1 y x) (R y)))) (S (h y x (M v2 v1)))))

@[equational_result]
theorem Equation3791_implies_Equation3567 (G: Type _) [Magma G] (h: Equation3791 G) : Equation3567 G := fun x y z =>
  let v0 := M z x
  let v1 := M v0 z
  let v2 := M x y
  have h3 := h x y z
  let v4 := M y z
  T (T (T (T (T (T h3 (h v0 v4 v2)) (C (S (h y z x)) (S (h z x y)))) (h v4 v0 v0)) (C (S h3) (R (M v0 v0)))) (C (R v2) (T (T (h v0 v0 v1) (C (T (C (h v0 z x) (h z x v0)) (S (h v0 v1 (M x v0)))) (S (h x v0 z)))) (S (h v1 x v0))))) (S (h y v1 x))

@[equational_result]
theorem Equation3979_implies_Equation3573 (G: Type _) [Magma G] (h: Equation3979 G) : Equation3573 G := fun x y z =>
  let v0 := M z z
  let v1 := M v0 v0
  let v2 := M x v0
  have h3 := h v1 x z
  have h4 := h x v0 z
  let v5 := M y v0
  T (T (T (T (T (T (h x y z) (h v5 x z)) (C (T h4 h3) (R v5))) (S (h v5 v2 v0))) (S (h v2 y z))) (C (T (T (T (T (T h4 h3) (h v2 v1 z)) (C (S (h v0 v0 z)) (R v2))) (h v1 v2 z)) (C (S (h v0 x z)) (R v1))) (R y))) (S (h y (M v0 x) v0))

@[equational_result]
theorem Equation1301_implies_Equation2511 (G: Type _) [Magma G] (h: Equation1301 G) : Equation2511 G := fun x y z =>
  let v0 := M (M x y) z
  let v1 := M y v0
  let v2 := M v1 z
  have h3 := R z
  let v4 := M (M v2 v2) z
  let v5 := M (M v1 v1) v0
  have h6 := R v0
  have h7 := h y v1 v0
  T (T (h x z y) (C h3 (T (T (T (C h6 (T h7 (C (C h7 h6) (R v5)))) (S (h v1 v0 v5))) (h v1 v4 z)) (C (R v4) (C (S (h v1 v2 z)) h3))))) (S (h v2 z v2))

@[equational_result]
theorem Equation1710_implies_Equation2132 (G: Type _) [Magma G] (h: Equation1710 G) : Equation2132 G := fun x y z =>
  let v0 := M z z
  let v1 := M y y
  let v2 := M v1 x
  let v3 := M v2 v0
  have h4 := h v3 v0 z
  let v5 := M v0 v3
  let v6 := M v0 v0
  T (T (h x v3 y) (C (T (T (T (C h4 (T (h x v3 z) (C (T (C (R v3) (h x x y)) (S (h v0 v2 x))) (R v5)))) (S (h v6 v5 z))) (h v6 v5 v3)) (C (S h4) (S (h v3 v3 z)))) (R (M v1 v3)))) (S (h v3 v3 y))

@[equational_result]
theorem Equation1726_implies_Equation3147 (G: Type _) [Magma G] (h: Equation1726 G) : Equation3147 G := fun x y z =>
  let v0 := M y y
  let v1 := M v0 x
  let v2 := M (M v1 z) z
  have h3 := h v2 y v2
  have h4 := h v1 v2 z
  have h5 := R v0
  let v6 := M x x
  have h7 := R v6
  T (T (h x y x) (C h5 (T (C (T (T (h v6 x v1) (C h7 (C (T (T (T (C h7 h4) (S (h v2 x v2))) h3) (C h5 (S h4))) (R v1)))) (S (h v0 x v1))) (R x)) h4))) (S h3)

@[equational_result]
theorem Equation2399_implies_Equation725 (G: Type _) [Magma G] (h: Equation2399 G) : Equation725 G := fun x y z =>
  let v0 := M (M z x) z
  let v1 := M y (M y v0)
  let v2 := M v1 (M x (M x v1))
  have h3 := R y
  have h4 := h v1 v1 x
  have h5 := R z
  have h6 := S (h x x x)
  let v7 := M x (M x (M x x))
  T (T (T (T (h x z v7) (C (C h5 (T (C (R v7) h6) h6)) h5)) (h v0 y y)) (C (C h3 (T h4 (C (R v2) h4))) h3)) (S (h v1 y v2))

@[equational_result]
theorem Equation2685_implies_Equation3331 (G: Type _) [Magma G] (h: Equation2685 G) : Equation3331 G := fun x y z =>
  let v0 := M y z
  let v1 := M z v0
  let v2 := M x v1
  have h3 := h v2 x y
  have h4 := R y
  let v5 := M v2 x
  have h6 := h v2 x v0
  T (C (T (T (h x v1 v2) (C (C h3 (T (h (M v2 v1) z y) (C (T (C (T (C (C h6 (R v1)) (R z)) (S (h (M v5 (M v0 x)) v0 z))) (R v0)) (S h6)) h4))) (R v2))) (S (h (M v5 (M y x)) y v2))) h4) (S h3)

@[equational_result]
theorem Equation2779_implies_Equation1155 (G: Type _) [Magma G] (h: Equation2779 G) : Equation1155 G := fun x y z =>
  let v0 := M x z
  let v1 := M z v0
  let v2 := M v1 y
  have h3 := h y v0 v0
  have h4 := h x v2 v0
  T h4 (C (T (T (T (T (h (M (M v2 v0) (M x v0)) x v2) (C (C (R (M x v2)) (T (S h4) (h x v2 z))) (R x))) (S (h (M (M v2 z) v0) x v2))) (C (T (C (C (R v1) h3) (R z)) (S (h (M (M v0 v0) (M y v0)) z v0))) (R v0))) (S h3)) (R v2))

@[equational_result]
theorem Equation3275_implies_Equation4346 (G: Type _) [Magma G] (h: Equation3275 G) : Equation4346 G := fun x y z =>
  let v0 := M z z
  have h1 := h z v0 y
  have h2 := h y z z
  have h3 := R v0
  let v4 := M y y
  have h5 := R y
  have h6 := R v4
  T (T (T (C (R x) (T (h y v4 x) (C h6 (S (h x y y))))) (S (h v4 x x))) (h v4 y y)) (C h5 (T (T (T (h v4 v0 y) (C h3 (T (C h6 (C h5 (T h1 (C h3 (S h2))))) (S (h y v4 v0))))) (C h3 h2)) (S h1)))

@[equational_result]
theorem Equation3417_implies_Equation4135 (G: Type _) [Magma G] (h: Equation3417 G) : Equation4135 G := fun x y z =>
  let v0 := M x y
  let v1 := M v0 z
  have h2 := S (h v1 z z)
  let v3 := M v1 z
  have h4 := R z
  have h5 := C h4 (T (C h4 (S (h x y v3))) (h z v0 z))
  let v6 := M v3 (M y x)
  have h7 := h v6 v3 z
  T (T (T (T (T (T (h x y z) (C h4 (T (C h4 (h y x z)) (S (h v0 z z))))) (h z v1 v6)) (C (R v6) (T (T h7 h5) h2))) h7) h5) h2

@[equational_result]
theorem Equation3607_implies_Equation4146 (G: Type _) [Magma G] (h: Equation3607 G) : Equation4146 G := fun x y z =>
  let v0 := M x z
  let v1 := M v0 z
  let v2 := M (M y v0) v1
  have h3 := R v0
  have h4 := R v1
  have h5 := h y v0 z
  let v6 := M z (M v1 y)
  T (T (T (T (h x y v0) (C h3 (C h5 (R x)))) (C h3 (T (T (h v6 x z) (C (R z) (T (h v0 v6 v1) (C h4 (C (C (S h5) h4) h3))))) (S (h (M v2 v0) v0 z))))) (S (h v0 v2 v0))) (S (h v1 y v0))

@[equational_result]
theorem Equation4013_implies_Equation4146 (G: Type _) [Magma G] (h: Equation4013 G) : Equation4146 G := fun x y z =>
  let v0 := M x z
  let v1 := M v0 z
  let v2 := M x y
  let v3 := M v2 (M y v2)
  let v4 := M x (M z x)
  let v5 := M z v1
  T (T (T (T (T (h x y v2) (h v3 x z)) (C (T (T (T (T (T (h z v0 z) (h v5 z z)) (C (C (R z) (h z z x)) (R v5))) (S (h v5 v4 z))) (S (h v4 v0 z))) (S (h v0 z x))) (R v3))) (h v1 v3 y)) (C (C (R y) (S (h y y v2))) (R v1))) (S (h v1 y y))

@[equational_result]
theorem Equation4156_implies_Equation41 (G: Type _) [Magma G] (h: Equation4156 G) : Equation41 G := fun x y z =>
  have h0 := R z
  let v1 := M x x
  have h2 := R v1
  have h3 := h y z y
  let v4 := M z y
  let v5 := M y z
  T (T (h x x z) (C (T (T (T (h v1 x v5) (C (T (C (T (h x v1 x) (C (S (h x x x)) (R x))) h2) (S (h x x v1))) (R v5))) (h v1 v5 y)) (C (T (C (T (T (T (C h3 h2) (S (h y v4 v1))) (h y v4 z)) (C (S h3) h0)) h2) (S (h z y v1))) (R y))) h0)) (S (h y z z))

@[equational_result]
theorem Equation492_implies_Equation2196 (G: Type _) [Magma G] (h: Equation492 G) : Equation2196 G := fun x y z =>
  let v0 := M y z
  let v1 := M x y
  let v2 := M v0 z
  let v3 := M v2 v1
  have h4 := R v0
  have h5 := R v1
  T (T (h x y v1) (C (R y) (T (T (T (C (R x) (C h5 (C h5 (T (h y v1 x) (C h5 (S (h x y x))))))) (S (h v1 x v1))) (h v1 v3 v2)) (C (R v3) (T (S (h v2 v1 v2)) (C h4 (T (h z v0 y) (C h4 (S (h y z y)))))))))) (S (h v3 y v0))

@[equational_result]
theorem Equation684_implies_Equation492 (G: Type _) [Magma G] (h: Equation684 G) : Equation492 G := fun x y z =>
  let v0 := M z y
  let v1 := M z v0
  let v2 := M y (M x v1)
  have h3 := S (h v1 v1 v2)
  let v4 := M v1 (M (M v1 v2) v2)
  have h5 := S (h y y x)
  let v6 := M y (M (M y x) x)
  T (h x v1 v4) (C (T (C (R z) (T (h v0 y v6) (C (R y) (C (R v0) (T (C h5 (R v6)) h5))))) (S (h y z y))) (C (R x) (T (C h3 (R v4)) h3)))

@[equational_result]
theorem Equation684_implies_Equation4450 (G: Type _) [Magma G] (h: Equation684 G) : Equation4450 G := fun x y z =>
  let v0 := M (M y z) z
  let v1 := M x (M y x)
  have h2 := S (h v0 v0 x)
  let v3 := M v0 (M (M v0 x) x)
  let v4 := M v1 v0
  have h5 := S (h x x x)
  let v6 := M x (M (M x x) x)
  T (T (h v1 y z) (C (T (h y x v6) (C (R x) (C (R y) (T (C h5 (R v6)) h5)))) (T (h v4 v0 v3) (C (R v0) (C (R v4) (T (C h2 (R v3)) h2)))))) (S (h v0 v1 v0))

@[equational_result]
theorem Equation962_implies_Equation1790 (G: Type _) [Magma G] (h: Equation962 G) : Equation1790 G := fun x y z =>
  let v0 := M z x
  let v1 := M v0 y
  let v2 := M (M y z) v1
  let v3 := M v2 v1
  have h4 := R y
  have h5 := R (M v1 v2)
  have h6 := R v2
  T (T (T (h x v2 v1) (C h6 (C h5 (T (h (M x v1) y v0) (C h4 (S (h z v1 x))))))) (C h6 (C h5 (T (C h4 (T (h z v1 v2) (C (R v1) (C (R v3) (S (h v0 z y)))))) (S (h v3 y v0)))))) (S (h v2 v2 v1))

@[equational_result]
theorem Equation1334_implies_Equation2685 (G: Type _) [Magma G] (h: Equation1334 G) : Equation2685 G := fun x y z =>
  let v0 := M z y
  let v1 := M x y
  let v2 := M v1 v0
  let v3 := M v2 z
  have h4 := h v3 v2 z
  have h5 := R v0
  have h6 := h x v2 v0
  T (T h6 (C (R v2) (T (T (h (M (M (M v2 v0) x) v0) v1 v0) (C (R v1) (T (T (T (C (S h6) h5) (C (R x) (C (h z v1 v0) (R y)))) (S (h (M v3 v0) x y))) (C h4 h5)))) (S (h (M (M v3 v3) z) v1 v0))))) (S h4)

@[equational_result]
theorem Equation2197_implies_Equation2 (G: Type _) [Magma G] (h: Equation2197 G) : Equation2 G := fun x y =>
  let v0 := M y x
  let v1 := M v0 x
  have h2 := S (h v1 x x)
  let v3 := M v1 x
  let v4 := M x x
  let v5 := M v4 x
  let v6 := M v5 x
  have h7 := h v5 x x
  T (T (h x y x) (C (R v1) (T (T (T (T (T (h v4 x x) (C (T h7 (C h7 (R v6))) h7)) (S (h v5 v5 v6))) (h v5 v5 v3)) (C (T (C h2 (R v3)) (S (h v1 y x))) h2)) (S (h v0 y x))))) (S (h y y x))

@[equational_result]
theorem Equation3008_implies_Equation1710 (G: Type _) [Magma G] (h: Equation3008 G) : Equation1710 G := fun x y z =>
  let v0 := M z z
  let v1 := M v0 y
  have h2 := R v0
  let v3 := M v0 v0
  have h4 := h v0 v3 z
  have h5 := R v3
  have h6 := h v0 v0 z
  have h7 := T h4 (C (S h6) h5)
  T (h x v1 z) (C (C (T (C (C (T (T h6 (C (T (C (C h7 h7) h2) (S (h (M v0 v3) v0 v0))) h2)) (C (T (C h6 h5) (S h4)) h2)) (R y)) h2) (S (h y v0 z))) (R x)) (R v1))

@[equational_result]
theorem Equation3131_implies_Equation4450 (G: Type _) [Magma G] (h: Equation3131 G) : Equation4450 G := fun x y z =>
  let v0 := M y z
  let v1 := M v0 z
  have h2 := R v0
  have h3 := R v1
  have h4 := R z
  have h5 := C (S (h z y y)) h2
  have h6 := h y v0 y
  let v7 := M y x
  T (T (T (T (T (C (h x y y) (R v7)) (S (h y v7 y))) h6) h5) (C (T (h z v1 v1) (C (C (C (T (C (C (C (T h6 h5) h4) h4) h4) (S (h v0 z z))) h3) h3) h3)) h2)) (S (h v1 v0 v1))

@[equational_result]
theorem Equation3159_implies_Equation4385 (G: Type _) [Magma G] (h: Equation3159 G) : Equation4385 G := fun x y =>
  have h0 := R x
  have h1 := S (h y x y)
  have h2 := R y
  let v3 := M x x
  have h4 := S (h x v3 x)
  have h5 := C (h x x v3) h0
  have h6 := T h5 h4
  have h7 := C (T (C (C h6 h0) h2) (R (M v3 y))) h2
  have h8 := h y x x
  T (T (T (T (C h0 h6) h5) h4) (h x y y)) (C (C (T (C (T (T (T (C (T h8 h7) h2) h1) h8) h7) h2) h1) h0) h0)

@[equational_result]
theorem Equation3404_implies_Equation3737 (G: Type _) [Magma G] (h: Equation3404 G) : Equation3737 G := fun x y z =>
  have h0 := R y
  let v1 := M x y
  have h2 := R z
  let v3 := M y z
  let v4 := M x z
  T (h x y v4) (C (R v4) (T (T (C h0 (T (T (h v4 x v1) (C (R v1) (T (S (h z v1 x)) (h z v1 y)))) (S (h v3 y v1)))) (C h0 (T (h v3 y z) (C h2 (T (T (C h0 (T (C h2 (h y z x)) (S (h v1 x z)))) (C h0 (T (h v1 x y) (C h0 (S (h y y x)))))) (S (h y y y))))))) (S (h y z y))))

@[equational_result]
theorem Equation3791_implies_Equation3398 (G: Type _) [Magma G] (h: Equation3791 G) : Equation3398 G := fun x y z =>
  let v0 := M x z
  let v1 := M y v0
  let v2 := M z v1
  let v3 := M z v0
  have h4 := h z v1 x
  let v5 := M v1 x
  T (T (T (h x y v0) (h (M v0 x) v1 v2)) (C (T (T (T (C h4 (h v0 x z)) (S (h v5 v3 v0))) (C (T (T (h v1 x z) (h v2 v0 v5)) (C (S (h x z v1)) (S h4))) (R v3))) (S (h v2 z v0))) (R (M v1 v2)))) (S (h z v1 v2))

@[equational_result]
theorem Equation3791_implies_Equation3973 (G: Type _) [Magma G] (h: Equation3791 G) : Equation3973 G := fun x y z =>
  let v0 := M x y
  let v1 := M z x
  let v2 := M y v1
  have h3 := h x y v1
  T (T h3 (C (T (T (h v1 x y) (h v2 v0 (M v1 x))) (C (S h3) (S (h y v1 x)))) (T (T (T (h y v1 v0) (h (M v0 y) (M v1 v0) v2)) (C (T (T (T (S (h v1 v0 y)) (C (h z x y) (h x y z))) (S (h v0 v1 (M y z)))) (S (h y z x))) (S (h v0 y v1)))) (S (h z v0 y))))) (S (h v2 z v0))

@[equational_result]
theorem Equation489_implies_Equation692 (G: Type _) [Magma G] (h: Equation489 G) : Equation692 G := fun x y z =>
  let v0 := M z y
  let v1 := M v0 z
  let v2 := M x v1
  let v3 := M v0 y
  have h4 := R y
  have h5 := R v1
  have h6 := R v0
  T (T (h x v1 v2) (C h5 (S (h v2 x v1)))) (C (T (C h6 (T (T (h z y v0) (C h4 (S (h v0 z y)))) (C h4 (T (h v0 v1 v0) (C h5 (C h6 (T (C h6 (C h5 (T (h v0 y v3) (C h4 (S (h v3 v0 y)))))) (S (h v1 v0 y))))))))) (S (h y v0 v1))) (R v2))

@[equational_result]
theorem Equation546_implies_Equation949 (G: Type _) [Magma G] (h: Equation546 G) : Equation949 G := fun x y z =>
  let v0 := M z x
  let v1 := M y z
  let v2 := M y (M v0 v1)
  have h3 := R v0
  have h4 := R v1
  T (T (h x y v0) (C (R y) (C h3 (T (T (T (C (R x) (T (C h3 (T (h y v1 z) (C h4 (S (h z z y))))) (C h3 (C h4 (T (h z v0 x) (C h3 (S (h x x z)))))))) (S (h v1 x v0))) (h v1 v2 v0)) (C (R v2) (C h3 (S (h y v1 v0)))))))) (S (h v2 y v0))

@[equational_result]
theorem Equation684_implies_Equation1304 (G: Type _) [Magma G] (h: Equation684 G) : Equation1304 G := fun x y z =>
  have h0 := S (h y y x)
  let v1 := M y (M (M y x) x)
  let v2 := M (M x z) z
  have h3 := R v2
  have h4 := S (h v2 v2 x)
  let v5 := M v2 (M (M v2 x) x)
  let v6 := M x v2
  T (T (T (T (h x x z) (C (R x) (T (h v6 v2 v5) (C h3 (C (R v6) (T (C h4 (R v5)) h4)))))) (S (h v2 x v2))) (h v2 y v1)) (C (R y) (C h3 (T (C h0 (R v1)) h0)))

@[equational_result]
theorem Equation1943_implies_Equation711 (G: Type _) [Magma G] (h: Equation1943 G) : Equation711 G := fun x y z =>
  let v0 := M x z
  let v1 := M v0 z
  let v2 := M y (M y v1)
  let v3 := M v2 v0
  have h4 := R (M v2 v3)
  let v5 := M z (M z z)
  let v6 := M x v0
  T (T (T (h x v2 v0) (C h4 (T (T (T (T (h v6 x v0) (C (R (M x v6)) (T (S (h x x z)) (h x z z)))) (S (h v5 x v0))) (h v5 y v1)) (C (R v2) (S (h v0 z z)))))) (C h4 (R v3))) (S (h v2 v2 v0))

@[equational_result]
theorem Equation2196_implies_Equation2519 (G: Type _) [Magma G] (h: Equation2196 G) : Equation2519 G := fun x y z =>
  let v0 := M x z
  let v1 := M v0 y
  let v2 := M y v1
  let v3 := M v2 z
  let v4 := M v3 z
  have h5 := h y v1 v3
  let v6 := M (M v1 v3) v3
  T (T (h x z v3) (C (R (M (M z v3) v3)) (T (T (h v0 y x) (C (R (M (M y x) x)) (T (T (T (C (h v0 y v1) h5) (S (h v6 v2 v1))) (h v6 v2 z)) (C (R v4) (S h5))))) (S (h v4 y x))))) (S (h v3 z v3))

@[equational_result]
theorem Equation3128_implies_Equation2383 (G: Type _) [Magma G] (h: Equation3128 G) : Equation2383 G := fun x y z =>
  let v0 := M y x
  let v1 := M z v0
  let v2 := M (M y v1) z
  have h3 := R v2
  have h4 := R y
  have h5 := h v0 v0 y
  have h6 := h x y v0
  T (T (h x y v2) (C (C (T (C (T h5 (C (S h6) h4)) h3) (C (T (T (T (C h6 h4) (S h5)) (h v0 z v2)) (C (T (C (C (h v1 y z) h3) (R z)) (S (h y v2 z))) h3)) h3)) h4) h3)) (S (h v2 y v2))

@[equational_result]
theorem Equation3791_implies_Equation3526 (G: Type _) [Magma G] (h: Equation3791 G) : Equation3526 G := fun x y z =>
  let v0 := M x y
  let v1 := M y z
  let v2 := M v1 z
  let v3 := M z x
  have h4 := h x y z
  T (T (T (T h4 (h v3 v1 z)) (C (T (T (h z v3 v1) (C (R v2) (S h4))) (h v2 v0 x)) (T (T (T (T (h v1 z x) (h (M x v1) v3 v2)) (C (T (S (h z x v1)) (h z x y)) (S (h x v1 z)))) (S (h v0 x v1))) (h v0 x v2)))) (S (h (M v0 x) (M v2 v0) (M x v2)))) (S (h x v2 v0))

@[equational_result]
theorem Equation3791_implies_Equation4013 (G: Type _) [Magma G] (h: Equation3791 G) : Equation4013 G := fun x y z =>
  let v0 := M y z
  let v1 := M z v0
  let v2 := M x y
  have h3 := h x y z
  let v4 := M z x
  T (T (T (T (T (T h3 (h v4 v0 v2)) (C (S (h y z x)) (S (h z x y)))) (h v0 v4 v0)) (C (R (M v0 v0)) (S h3))) (C (T (T (h v0 v0 v1) (C (S (h v0 y z)) (T (C (h y z v0) (h z v0 y)) (S (h v1 v0 (M v0 y)))))) (S (h y v1 v0))) (R v2))) (S (h v1 x y))

@[equational_result]
theorem Equation3810_implies_Equation3286 (G: Type _) [Magma G] (h: Equation3810 G) : Equation3286 G := fun x y z =>
  let v0 := M z z
  let v1 := M y v0
  let v2 := M v0 y
  let v3 := M v0 v1
  have h4 := h z z z
  have h5 := S h4
  have h6 := h z x z
  T (T (T (T (T (T (h x x z) (C h6 h6)) (S (h v0 v0 (M z x)))) (h v0 v0 v1)) (C (T (C (T (h y v0 v0) (C h5 (R v2))) h4) (S (h v0 v2 v0))) (T (h v1 v0 v0) (C h5 (R v3))))) (S (h v3 v2 v0))) (S (h y v1 v0))

@[equational_result]
theorem Equation489_implies_Equation2180 (G: Type _) [Magma G] (h: Equation489 G) : Equation2180 G := fun x y z =>
  let v0 := M x z
  let v1 := M y z
  let v2 := M v1 y
  let v3 := M v2 v0
  have h4 := R v1
  have h5 := R v3
  T (h x z v0) (C (T (h z v1 v3) (C h4 (T (C (R z) (T (T (C h5 (C h4 (T (h v3 v1 v1) (C h4 (C h5 (T (C h4 (C h4 (T (h v1 y v2) (C (R y) (S (h v2 v1 y)))))) (S (h v1 v1 y)))))))) (S (h v1 v3 v1))) (h v1 y z))) (S (h y z v1))))) (S (h v0 x z)))

@[equational_result]
theorem Equation778_implies_Equation3997 (G: Type _) [Magma G] (h: Equation778 G) : Equation3997 G := fun x y z =>
  let v0 := M x z
  let v1 := M z v0
  let v2 := M v1 y
  have h3 := h v2 v1 v2
  have h4 := R z
  let v5 := M x y
  have h6 := h v5 v1 x
  T (T h6 (C (R v1) (T (T (h (M x (M (M x v1) v5)) v0 z) (C (R v0) (T (T (T (C h4 (S h6)) (C h4 (C (R x) (h y v0 z)))) (S (h (M z v2) z x))) (C h4 h3)))) (S (h (M v2 (M (M v2 v1) v2)) v0 z))))) (S h3)

@[equational_result]
theorem Equation1304_implies_Equation2917 (G: Type _) [Magma G] (h: Equation1304 G) : Equation2917 G := fun x y z =>
  let v0 := M y (M x y)
  let v1 := M (M v0 z) z
  let v2 := M (M (M v1 x) x) v1
  have h3 := R x
  have h4 := h v1 v1 x
  have h5 := R y
  have h6 := S (h x x x)
  let v7 := M (M (M x x) x) x
  T (T (T (T (h x y v7) (C h5 (C (T (C h6 (R v7)) h6) h5))) (h v0 x z)) (C h3 (C (T h4 (C h4 (R v2))) h3))) (S (h v1 x v2))

@[equational_result]
theorem Equation2196_implies_Equation3211 (G: Type _) [Magma G] (h: Equation2196 G) : Equation3211 G := fun x y z =>
  let v0 := M (M y z) z
  let v1 := M v0 x
  let v2 := M v1 y
  let v3 := M v2 v1
  let v4 := M v3 v1
  have h5 := R (M (M v1 x) x)
  let v6 := M x v1
  T (T (h x v1 v2) (C (R (M (M v1 v2) v2)) (T (T (h v6 v1 x) (C h5 (T (T (T (h (M v6 v1) v1 x) (C h5 (S (h v0 x v1)))) (C h5 (T (h v0 v2 v1) (C (R v4) (S (h v1 y z)))))) (S (h v4 v1 x))))) (S (h v3 v1 x))))) (S (h v2 v1 v2))

@[equational_result]
theorem Equation2956_implies_Equation364 (G: Type _) [Magma G] (h: Equation2956 G) : Equation364 G := fun x y =>
  let v0 := M y x
  let v1 := M v0 x
  have h2 := R v1
  have h3 := S (h v0 x x)
  let v4 := M x (M x x)
  let v5 := M v4 v0
  have h6 := R x
  have h7 := S (h y x x)
  let v8 := M v4 y
  have h9 := T (h x v8 y) (C (C (T (C (R v8) h7) h7) h6) h6)
  T (T (T (C h9 h6) (C h2 h9)) (C (T (h v1 v5 v0) (C (C (T (C (R v5) h3) h3) h2) h2)) h2)) (S (h v1 v0 x))

@[equational_result]
theorem Equation3159_implies_Equation832 (G: Type _) [Magma G] (h: Equation3159 G) : Equation832 G := fun x y =>
  have h0 := R x
  let v1 := M x x
  have h2 := h x x v1
  have h3 := S h2
  have h4 := h x v1 x
  have h5 := S (h y x y)
  have h6 := R y
  have h7 := C (T (C (C (T (C h2 h0) (S h4)) h0) h6) (R (M v1 y))) h6
  have h8 := h y x x
  T h4 (C h3 (T (h x y y) (C (C (T (C (T (T (T (C (T h8 h7) h6) h5) h8) h7) h6) h5) h0) (T h4 (C h3 h0)))))

@[equational_result]
theorem Equation3275_implies_Equation3301 (G: Type _) [Magma G] (h: Equation3275 G) : Equation3301 G := fun x y z w =>
  have h0 := h z y w
  let v1 := M y (M z (M w y))
  have h2 := R z
  have h3 := R v1
  have h4 := S h0
  let v5 := M x x
  T (T (T (T (T (T (h x v5 v1) (C (R v5) (T (S (h v1 x x)) (C h3 (T (T h4 (h z v1 x)) (C h3 (T (C h2 (C (R x) h4)) (S (h x z z))))))))) (S (h v1 v5 v1))) (C h3 h4)) (C h3 (T (h z z z) (C h2 (C h2 h0))))) (S (h z v1 z))) h0

@[equational_result]
theorem Equation3791_implies_Equation3417 (G: Type _) [Magma G] (h: Equation3791 G) : Equation3417 G := fun x y z =>
  let v0 := M y x
  let v1 := M z v0
  let v2 := M x y
  have h3 := h x y y
  let v4 := M y y
  have h5 := h y y x
  T (T (T (T h3 (h v0 v4 v1)) (C (h v1 v0 z) (T (T (C (T (T (h y y y) (C h5 (T (T h5 (h v2 v0 v4)) (C (S (h y x y)) (S h3))))) (S (h v0 v0 v2))) (R v1)) (S (h v0 z v0))) (h v0 z v1)))) (S (h (M v0 z) (M v1 v0) (M z v1)))) (S (h z v1 v0))

@[equational_result]
theorem Equation3979_implies_Equation4226 (G: Type _) [Magma G] (h: Equation3979 G) : Equation4226 G := fun x y z =>
  let v0 := M z z
  let v1 := M v0 x
  let v2 := M v1 y
  let v3 := M y (M v2 v2)
  let v4 := M v0 v0
  have h5 := R v4
  let v6 := M x (M x x)
  have h7 := h x v0 z
  T (T (T (T (h x y v2) (h v3 x z)) (C (T (T (T (T (T h7 (h v4 x z)) (C (T h7 (h v4 x x)) h5)) (S (h v4 v6 v0))) (h v4 v6 z)) (C (S (h v0 x x)) h5)) (R v3))) (S (h v3 v1 v0))) (S (h v1 y v2))

@[equational_result]
theorem Equation4176_implies_Equation3906 (G: Type _) [Magma G] (h: Equation4176 G) : Equation3906 G := fun x y z =>
  let v0 := M z z
  let v1 := M y v0
  have h2 := S (h v1 y v0)
  have h3 := R v0
  have h4 := R y
  T (T (T (T (T (h x x y) (C (T (C (h x y v0) (R x)) (S (h v0 v1 x))) h4)) (C (T (h v0 v1 v0) (C (S (h v0 y v0)) h3)) h4)) (S (h v0 v0 y))) (C (T (T (h z z y) (C (T (T (T (C (h z y v0) (R z)) (S (h v0 v1 z))) (h v0 v1 v1)) (C h2 (R v1))) h4)) (S (h v1 v1 y))) h3)) h2

@[equational_result]
theorem Equation4216_implies_Equation3364 (G: Type _) [Magma G] (h: Equation4216 G) : Equation3364 G := fun x y z =>
  let v0 := M x z
  let v1 := M z v0
  let v2 := M v1 z
  have h3 := h v2 z v1
  have h4 := h z v0 z
  let v5 := M (M y y) y
  let v6 := M v0 x
  T (T (T (T (T (T (h x y y) (h v5 x v0)) (C (T (T (T (T (S (h v0 z x)) (C (T (h x z x) (h v6 x v0)) (R z))) (S (h z v0 v6))) h4) h3) (R v5))) (S (h v5 v1 v2))) (S (h v1 y y))) (C (T h4 h3) (R y))) (S (h y v1 v2))

@[equational_result]
theorem Equation572_implies_Equation3131 (G: Type _) [Magma G] (h: Equation572 G) : Equation3131 G := fun x y z =>
  let v0 := M y x
  let v1 := M v0 z
  let v2 := M v1 z
  let v3 := M v2 y
  have h4 := R v2
  have h5 := R z
  T (T (T (h x v2 v2) (C h4 (C h4 (C h4 (T (C (R x) (T (h v2 z z) (C h5 (C h5 (T (C h5 (C h4 (T (h z v2 z) (C h4 (S (h v1 z z)))))) (S (h v0 z v2))))))) (S (h y x z))))))) (C h4 (C h4 (C h4 (T (h y v3 y) (C (R v3) (S (h v2 y y)))))))) (S (h v3 v2 v2))

@[equational_result]
theorem Equation711_implies_Equation1507 (G: Type _) [Magma G] (h: Equation711 G) : Equation1507 G := fun x y z =>
  have h0 := S (h y y x)
  let v1 := M y x
  let v2 := M y (M v1 x)
  have h3 := R z
  have h4 := S (h x x x)
  let v5 := M x (M (M x x) x)
  have h6 := R v1
  have h7 := C h6 (C h6 (T (C h4 (R v5)) h4))
  have h8 := h x v1 v5
  T (T h8 h7) (C h6 (T (T (T (C h6 (T h8 h7)) (S (h y v1 x))) (h y z v2)) (C h3 (C h3 (T (C h0 (R v2)) h0)))))

@[equational_result]
theorem Equation1507_implies_Equation3370 (G: Type _) [Magma G] (h: Equation1507 G) : Equation3370 G := fun x y z =>
  let v0 := M z x
  let v1 := M z v0
  let v2 := M y v1
  have h3 := R (M z (M z y))
  let v4 := M x y
  let v5 := M z (M z v4)
  T (T (T (T (T (C (h x v4 z) (h y x v4)) (S (h v5 (M v4 x) v4))) (h v5 y z)) (C (T (C (h y x z) (R v5)) (S (h v1 v4 z))) h3)) (C (T (C (h z v1 y) (h v0 z v1)) (S (h (M y v2) (M v1 z) v1))) h3)) (S (h v2 y z))

@[equational_result]
theorem Equation2958_implies_Equation4421 (G: Type _) [Magma G] (h: Equation2958 G) : Equation4421 G := fun x y z =>
  have h0 := R y
  have h1 := S (h z y z)
  let v2 := M (M y (M y z)) z
  let v3 := M x (M x y)
  let v4 := M (M x (M x v3)) v3
  let v5 := M v3 y
  have h6 := h v3 x v3
  T (T (T (T (h v3 v3 y) (C (T (C (C (T h6 (C (R v4) h6)) (R v5)) (R v3)) (S (h v5 v4 v3))) h0)) (S (h y x y))) (h y v2 z)) (C (C (T (C (R v2) h1) h1) h0) (R z))

@[equational_result]
theorem Equation3350_implies_Equation4229 (G: Type _) [Magma G] (h: Equation3350 G) : Equation4229 G := fun x y z =>
  let v0 := M z z
  let v1 := M v0 y
  let v2 := M v1 x
  let v3 := M v0 v0
  let v4 := M v1 v3
  let v5 := M v2 v2
  let v6 := M x v0
  T (T (T (T (T (T (h x y z) (h y v6 v0)) (C (R v6) (T (T (T (h y v3 v0) (C (R v3) (S (h v0 y z)))) (h v3 v1 v0)) (C (R v1) (T (S (h v0 v3 z)) (S (h v0 v0 z))))))) (h v6 v4 v5)) (C (R v4) (T (S (h v5 v6 v2)) (S (h x v5 z))))) (S (h x v4 v2))) (S (h v1 x v0))

@[equational_result]
theorem Equation3791_implies_Equation3607 (G: Type _) [Magma G] (h: Equation3791 G) : Equation3607 G := fun x y z =>
  let v0 := M x y
  let v1 := M y z
  let v2 := M v1 x
  have h3 := h x y v1
  T (T h3 (C (T (T (T (h v1 x v0) (h (M v0 v1) (M x v0) v2)) (C (S (h x v0 v1)) (T (T (T (S (h v0 v1 x)) (C (h x y z) (h y z x))) (S (h v1 v0 (M z x)))) (S (h z x y))))) (S (h v0 z x))) (T (T (h y v1 x) (h v0 v2 (M y v1))) (C (S (h v1 x y)) (S h3))))) (S (h z v2 v0))

@[equational_result]
theorem Equation3804_implies_Equation3331 (G: Type _) [Magma G] (h: Equation3804 G) : Equation3331 G := fun x y z =>
  let v0 := M y z
  let v1 := M z v0
  let v2 := M x x
  let v3 := M z v1
  let v4 := M x z
  let v5 := M y v0
  T (T (T (T (h x y x) (h (M x y) v2 v1)) (C (R (M v1 v2)) (T (T (T (C (h x y z) (h z v0 y)) (S (h v5 v4 (M z y)))) (h v5 v4 v3)) (C (S (h x v1 z)) (T (C (h y v0 z) (R v3)) (S (h z v0 v1))))))) (S (h (M x v1) v2 v1))) (S (h x v1 x))

@[equational_result]
theorem Equation3956_implies_Equation41 (G: Type _) [Magma G] (h: Equation3956 G) : Equation41 G := fun x y z =>
  let v0 := M y z
  have h1 := h y z v0
  let v2 := M x x
  let v3 := M z v0
  have h4 := R v2
  have h5 := R v0
  have h6 := h y z (M v0 v3)
  have h7 := h x x v0
  T (T (T (T h7 (h (M x v2) v0 v2)) (C (T (T (T (T (T (C h5 (S h7)) (C h6 h4)) (S (h v0 v3 v2))) (h v0 v3 v0)) (C (S h6) h5)) (C h5 h1)) h4)) (S (h v3 v0 v2))) (S h1)

@[equational_result]
theorem Equation3973_implies_Equation4684 (G: Type _) [Magma G] (h: Equation3973 G) : Equation4684 G := fun x y z =>
  let v0 := M x y
  let v1 := M v0 z
  let v2 := M y v1
  have h3 := R z
  let v4 := M z y
  have h5 := R v4
  let v6 := M v4 x
  let v7 := M v6 v0
  T (T (T (C (T (h x y v4) (C (T (T (T (h y v6 x) (h v7 x z)) (C (T (h x (M z v7) v4) (C (S (h v0 z v6)) h5)) h3)) (S (h y v1 z))) h5)) h3) (S (h y v2 z))) (h y v2 x)) (C (S (h z y v0)) (R x))

@[equational_result]
theorem Equation4101_implies_Equation4113 (G: Type _) [Magma G] (h: Equation4101 G) : Equation4113 G := fun x y z w =>
  have h0 := h w y z
  let v1 := M (M (M y z) w) y
  have h2 := R v1
  have h3 := R w
  have h4 := S h0
  let v5 := M x x
  T (T (T (T (T (T (h x v5 v1) (C (T (S (h v1 x x)) (C (T (T h4 (h w v1 x)) (C (T (C (C h4 (R x)) h3) (S (h x w w))) h2)) h2)) (R v5))) (S (h v1 v5 v1))) (C h4 h2)) (C (T (h w w w) (C (C h0 h3) h3)) h2)) (S (h w v1 w))) h0

@[equational_result]
theorem Equation4176_implies_Equation3794 (G: Type _) [Magma G] (h: Equation4176 G) : Equation3794 G := fun x y z =>
  let v0 := M z y
  have h1 := R x
  have h2 := R z
  let v3 := M x y
  let v4 := M z x
  have h5 := R y
  T (h x y v0) (C (T (C (T (T (T (T (T (T (h y v0 y) (C (S (h y z y)) h5)) (C (h y z x) h5)) (S (h x v4 y))) (h x v4 z)) (C (C (T (C (h z x y) h2) (S (h y v3 z))) h1) h2)) (C (T (C (T (h y v3 x) (C (S (h x x y)) h1)) h1) (S (h x x x))) h2)) h1) (S (h z x x))) (R v0))

@[equational_result]
theorem Equation695_implies_Equation1993 (G: Type _) [Magma G] (h: Equation695 G) : Equation1993 G := fun x y z =>
  let v0 := M z z
  let v1 := M v0 v0
  have h2 := h v0 v1 z
  have h3 := h v0 v0 z
  have h4 := R v1
  have h5 := R v0
  have h6 := T h2 (C h4 (S h3))
  let v7 := M y v0
  T (h x v7 z) (C (R v7) (C (R x) (T (C h5 (C (R y) (T (T h3 (C h5 (T (C h5 (C h6 h6)) (S (h (M v1 v0) v0 v0))))) (C h5 (T (C h4 h3) (S h2)))))) (S (h y v0 z)))))

@[equational_result]
theorem Equation2958_implies_Equation2399 (G: Type _) [Magma G] (h: Equation2958 G) : Equation2399 G := fun x y z =>
  let v0 := M z (M z x)
  have h1 := R v0
  have h2 := S (h y x y)
  let v3 := M (M x (M x y)) y
  let v4 := M v0 v0
  have h5 := S (h v0 x v0)
  let v6 := M (M x (M x v0)) v0
  T (T (T (T (T (h x v0 v0) (C (S (h v4 z x)) h1)) (C (T (h v4 v6 v0) (C (C (T (C (R v6) h5) h5) (R v4)) h1)) h1)) (S (h v0 v0 v0))) (h v0 v3 y)) (C (C (T (C (R v3) h2) h2) h1) (R y))

@[equational_result]
theorem Equation3400_implies_Equation41 (G: Type _) [Magma G] (h: Equation3400 G) : Equation41 G := fun x y z =>
  let v0 := M x x
  have h1 := h y z z
  have h2 := R y
  let v3 := M z y
  have h4 := R v0
  let v5 := M y z
  T (T (h x x y) (C h2 (T (T (T (h x v0 v5) (C (R v5) (T (C h4 (T (h v0 x x) (C (R x) (S (h x x x))))) (S (h x x v0))))) (h v5 v0 z)) (C (R z) (T (C h4 (T (T (T (C h4 h1) (S (h v3 z v0))) (h v3 z y)) (C h2 (S h1)))) (S (h z y v0))))))) (S (h y z y))

@[equational_result]
theorem Equation3804_implies_Equation3500 (G: Type _) [Magma G] (h: Equation3804 G) : Equation3500 G := fun x y z =>
  let v0 := M z z
  let v1 := M v0 y
  let v2 := M z v1
  have h3 := R v1
  T (T (T (T (T (T (T (h x x z) (h (M z x) (M x z) v0)) (C (S (h x z z)) (S (h z x z)))) (S (h z z x))) (h z z y)) (C (h y z z) (T (T (T (h z y v1) (C (T (h v1 y v0) (C h3 (T (C h3 (h z z z)) (S (h v0 y v0))))) (R v2))) (S (h z v1 v1))) (h z v1 z)))) (S (h v2 (M y z) v0))) (S (h y v1 z))

@[equational_result]
theorem Equation3804_implies_Equation4146 (G: Type _) [Magma G] (h: Equation3804 G) : Equation4146 G := fun x y z =>
  let v0 := M x z
  let v1 := M v0 z
  have h2 := h v1 z x
  let v3 := M z v0
  have h4 := h x z z
  let v5 := M z z
  T (T (h x y z) (C (R (M z y)) (T (T (T (T (T (T h4 (h v5 v0 z)) (C (R v3) (T (h v5 z v0) (C (R v1) (S h4))))) (h v3 (M v1 v0) v1)) (C (T (S (h v1 z v0)) h2) (S (h v0 v0 z)))) (S (h v0 (M v1 x) v0))) (S h2)))) (S (h v1 y z))

@[equational_result]
theorem Equation4162_implies_Equation3414 (G: Type _) [Magma G] (h: Equation4162 G) : Equation3414 G := fun x y z =>
  let v0 := M x y
  let v1 := M z v0
  have h2 := S (h z v1 z)
  have h3 := R z
  let v4 := M z v1
  have h5 := C (T (C (S (h x y v4)) h3) (h v0 z z)) h3
  let v6 := M (M y x) v4
  have h7 := h v4 v6 z
  T (T (T (T (T (T (h x y z) (C (T (C (h y x z) h3) (S (h z v0 z))) h3)) (h v1 z v6)) (C (T (T h7 h5) h2) (R v6))) h7) h5) h2

@[equational_result]
theorem Equation3145_implies_Equation1672 (G: Type _) [Magma G] (h: Equation3145 G) : Equation1672 G := fun x y z =>
  let v0 := M z z
  let v1 := M v0 x
  have h2 := S (h v0 v0 v1)
  have h3 := R v0
  have h4 := R v1
  have h5 := C (S (h v0 z v0)) h3
  have h6 := h v0 v0 v0
  have h7 := C (T h6 h5) h3
  T (h x v1 y) (C (C (S (h x z v1)) (R y)) (T (h x z v0) (C (T (C (T (h v1 z v0) (C (T (T (T (T (C (C (T (T h6 h5) h7) h4) h3) h2) h6) h5) h7) h4)) h3) h2) (R x))))

@[equational_result]
theorem Equation3159_implies_Equation1478 (G: Type _) [Magma G] (h: Equation3159 G) : Equation1478 G := fun x y =>
  have h0 := R x
  let v1 := M x x
  have h2 := h x x v1
  have h3 := S h2
  have h4 := h x v1 x
  have h5 := T h4 (C h3 h0)
  have h6 := T (C h2 h0) (S h4)
  have h7 := R y
  have h8 := T (C (T (h y x x) (C (T (C (C h6 h0) h7) (R (M v1 y))) h7)) h7) (S (h y x y))
  T (T (h x y y) (C (C (C h8 h7) h5) h0)) (C (C h8 h6) (T h4 (C h3 h5)))

@[equational_result]
theorem Equation3385_implies_Equation3776 (G: Type _) [Magma G] (h: Equation3385 G) : Equation3776 G := fun x y z =>
  let v0 := M y z
  let v1 := M z x
  have h2 := R v1
  have h3 := C h2 (S (h y z x))
  have h4 := h x y v1
  have h5 := h x y z
  have h6 := R v0
  let v7 := M x y
  T (T (T (T h4 h3) (h v1 v0 v0)) (C h6 (T (T (T (C h2 (C h6 (T (h y z v7) (C (R v7) (S (h z x y)))))) (S (h v0 v7 v1))) (C h6 h5)) (C h6 (T (T (S h5) h4) h3))))) (S (h v0 v1 v0))

@[equational_result]
theorem Equation3573_implies_Equation3323 (G: Type _) [Magma G] (h: Equation3573 G) : Equation3323 G := fun x y z =>
  let v0 := M z z
  let v1 := M y v0
  let v2 := M x v1
  let v3 := M (M v2 v2) x
  let v4 := M v0 v0
  have h5 := R v4
  let v6 := M (M x x) y
  have h7 := h v0 y z
  T (T (T (T (h x y v2) (h y v3 z)) (C (R v3) (T (T (T (T (T h7 (h y v4 z)) (C h5 (T h7 (h y v4 x)))) (S (h v6 v4 v0))) (h v6 v4 z)) (C h5 (S (h y v0 x)))))) (S (h v1 v3 v0))) (S (h x v1 v2))

@[equational_result]
theorem Equation3791_implies_Equation4512 (G: Type _) [Magma G] (h: Equation3791 G) : Equation4512 G := fun x y z =>
  let v0 := M x y
  have h1 := h z x y
  have h2 := S h1
  let v3 := M x v0
  have h4 := R v3
  let v5 := M y z
  let v6 := M v5 v0
  have h7 := h y z x
  T (T (T (T (h x v5 v6) (C (T (h v6 x v0) (C (T (C (R v0) h2) (S h7)) h4)) (T (T (C h7 (R v6)) (S (h (M z x) v5 v0))) (C h1 (R v5))))) (S (h v3 v6 v5))) (C h4 h2)) (S (h v0 z x))

@[equational_result]
theorem Equation3804_implies_Equation3994 (G: Type _) [Magma G] (h: Equation3804 G) : Equation3994 G := fun x y z =>
  let v0 := M x y
  let v1 := M z v0
  let v2 := M v0 v0
  let v3 := M v0 z
  have h4 := h x y y
  let v5 := M y y
  have h6 := h x y x
  T (T (T (T h4 (h v5 v0 z)) (h v1 (M v5 z) v0)) (C (T (T (C (T (T h6 (h v0 (M x x) v0)) (C (S h6) (R v2))) (T (h v5 z v0) (C (R v3) (S h4)))) (S (h v3 v2 v0))) (S (h v0 z v0))) (R (M v1 v0)))) (S (h v1 z v0))

@[equational_result]
theorem Equation3973_implies_Equation3334 (G: Type _) [Magma G] (h: Equation3973 G) : Equation3334 G := fun x y z =>
  let v0 := M z y
  let v1 := M z v0
  let v2 := M v1 (M v0 x)
  have h3 := R v0
  have h4 := R v1
  have h5 := h v0 x z
  let v6 := M (M x v1) z
  T (T (T (T (h x y v0) (C (C (R y) h5) h3)) (C (T (T (h y v6 z) (C (T (h v6 v0 v1) (C (C h3 (C h4 (S h5))) h4)) (R z))) (S (h v0 (M v0 v2) z))) h3)) (S (h v2 v0 v0))) (S (h x v1 v0))

@[equational_result]
theorem Equation4097_implies_Equation4609 (G: Type _) [Magma G] (h: Equation4097 G) : Equation4609 G := fun x y z =>
  let v0 := M x x
  have h1 := h x x x
  have h2 := S h1
  have h3 := h y x x
  have h4 := T h3 h2
  have h5 := S h3
  let v6 := M y y
  let v7 := M v6 z
  T (T (T (C (T (h x x y) (S (h v6 x y))) (R y)) (S (h v7 y v6))) (h v7 z v6)) (C (T (T (T (C (T (h z x x) h2) h4) (C (R v0) (T h1 h5))) (C (T (T h1 h5) (h y x v0)) h4)) (S (h y v0 x))) (R z))

@[equational_result]
theorem Equation489_implies_Equation2992 (G: Type _) [Magma G] (h: Equation489 G) : Equation2992 G := fun x y z =>
  let v0 := M z y
  have h1 := S (h z y v0)
  have h2 := C (R y) (h v0 z y)
  let v3 := M y v0
  let v4 := M v3 x
  have h5 := R v4
  have h6 := R x
  T (h x v4 v4) (C h5 (T (T (T (C h6 (T (T (C h5 (C h5 (T (h v4 x v3) (C h6 (C h5 (T (C (T h2 h1) (R (M x v3))) (S (h x z y)))))))) (S (h v4 v4 x))) (h v4 v3 x))) (S (h v3 x v4))) h2) h1))

@[equational_result]
theorem Equation641_implies_Equation4 (G: Type _) [Magma G] (h: Equation641 G) : Equation4 G := fun x y =>
  let v0 := M x y
  have h1 := h y x (M (M v0 x) x)
  have h2 := h x v0 x
  have h3 := R y
  have h4 := T (C h3 h2) (S h1)
  have h5 := R x
  have h6 := h y v0 y
  have h7 := C h3 (S h2)
  T (T (h x y (M (M y y) y)) (C h5 (T (C (T h1 h7) (C h4 (C (T (C h3 (T (T h1 h7) (C h6 h5))) (C h3 (C (S h6) h5))) h3))) (S (h (M y x) y y))))) (C h5 h4)

@[equational_result]
theorem Equation934_implies_Equation4200 (G: Type _) [Magma G] (h: Equation934 G) : Equation4200 G := fun x y z =>
  let v0 := M z x
  let v1 := M v0 z
  let v2 := M v1 y
  have h3 := h v2 x v1
  let v4 := M (M x v1) (M v1 v2)
  have h5 := R v0
  have h6 := R z
  let v7 := M x y
  have h8 := h y z v7
  T (C (R x) (T (T (T (T h8 (C h6 (T (h (M (M z v7) (M v7 y)) v0 z) (C h5 (C (R v1) (S h8)))))) (C h6 (C h5 h3))) (S (h v4 z x))) (R v4))) (S h3)

@[equational_result]
theorem Equation1493_implies_Equation2 (G: Type _) [Magma G] (h: Equation1493 G) : Equation2 G := fun x y =>
  let v0 := M y x
  let v1 := M y v0
  let v2 := M y y
  let v3 := M y v2
  have h4 := S (h v3 y x)
  let v5 := M y v3
  let v6 := M y v1
  have h7 := h v1 y x
  T (T (h x y x) (C (T (T (T (T (T (h v0 y x) (C h7 (T h7 (C (R v6) h7)))) (S (h v1 v6 v1))) (h v1 v5 v1)) (C h4 (T (C (R v5) h4) (S (h v3 y y))))) (S (h v2 y y))) (R v1))) (S (h y y x))

@[equational_result]
theorem Equation1507_implies_Equation2170 (G: Type _) [Magma G] (h: Equation1507 G) : Equation2170 G := fun x y z =>
  let v0 := M y z
  let v1 := M v0 x
  let v2 := M z y
  have h3 := h z y y
  let v4 := M y (M y y)
  let v5 := M v0 (M v0 v0)
  T (h x v0 v0) (C (R v1) (T (T (h v5 z v1) (C (T (T (T (T (C h3 (R v5)) (S (h v4 v0 v0))) (h v4 v0 x)) (C (T (S h3) (h z y z)) (R (M x (M x v0))))) (S (h (M z v2) v0 x))) (R (M v1 (M v1 z))))) (S (h v2 z v1))))

@[equational_result]
theorem Equation1507_implies_Equation3417 (G: Type _) [Magma G] (h: Equation1507 G) : Equation3417 G := fun x y z =>
  let v0 := M y x
  let v1 := M z v0
  let v2 := M z v1
  let v3 := M v1 (M v1 x)
  have h4 := h x y v2
  let v5 := M v2 (M v2 y)
  let v6 := M x y
  T (T (T (h v6 x v1) (C (T (T (T (T (h (M x v6) v0 x) (C (T (S (h x y x)) h4) (R (M x (M x v0))))) (S (h v5 v0 x))) (h v5 v0 z)) (C (S h4) (R v2))) (R v3))) (R (M (M x v2) v3))) (S (h v2 x v1))

@[equational_result]
theorem Equation2316_implies_Equation898 (G: Type _) [Magma G] (h: Equation2316 G) : Equation898 G := fun x y z =>
  let v0 := M z y
  let v1 := M x z
  let v2 := M v1 v0
  let v3 := M y v2
  have h4 := h v3 v0 v2
  have h5 := R v0
  have h6 := h x v3 v2
  T (T h6 (C (T (T (h (M v3 (M x (M v2 v3))) v0 v1) (C (T (T (T (C h5 (S h6)) (C (C (R z) (h y v0 v1)) (R x))) (S (h (M v0 v3) z x))) (C h5 h4)) (R v1))) (S (h (M v0 (M v3 (M v2 v0))) v0 v1))) (R v2))) (S h4)

@[equational_result]
theorem Equation2738_implies_Equation2 (G: Type _) [Magma G] (h: Equation2738 G) : Equation2 G := fun x y =>
  have h0 := R x
  let v1 := M y y
  have h2 := R v1
  let v3 := M x x
  let v4 := M v1 (M x y)
  have h5 := R v3
  T (T (T (T (T (T (h x x x) (C (C h5 (h v3 x x)) h0)) (S (h (M v3 (M v3 x)) x x))) (C h5 (T (T (T (T (C h5 (h x y x)) (h (M v3 (M v4 x)) x x)) (C (C h5 (T (S (h v4 x x)) (h v4 y x))) h0)) (S (h (M v1 (M v4 y)) x x))) (C h2 (S (h x y y)))))) (h (M v3 (M v1 x)) y x)) (C (C h2 (S (h v1 x y))) h0)) (S (h y y x))

@[equational_result]
theorem Equation3195_implies_Equation14 (G: Type _) [Magma G] (h: Equation3195 G) : Equation14 G := fun x y =>
  let v0 := M x y
  have h1 := R v0
  have h2 := R x
  let v3 := M y v0
  have h4 := R v3
  have h5 := R y
  let v6 := M y v3
  T (h x v0 v0) (C (T (C (T (T (C (C (T (h v0 v3 x) (C (C (T (C (C (C (T (h y y v3) (C (T (C (T (T (C (h v6 y v3) h5) (S (h v3 v6 y))) (h v3 y v0)) h5) (S (h v0 v3 y))) h4)) h1) h2) h4) (S (h x v0 v3))) h1) h2)) h1) h1) (S (h v0 x v0))) (h v0 x y)) h2) (S (h y v0 x))) h1)

@[equational_result]
theorem Equation3195_implies_Equation1152 (G: Type _) [Magma G] (h: Equation3195 G) : Equation1152 G := fun x y z =>
  let v0 := M x y
  let v1 := M z v0
  let v2 := M v1 z
  have h3 := R x
  let v4 := M y v2
  have h5 := R v4
  have h6 := T (C (h v1 z v0) (R z)) (S (h v0 v1 z))
  T (h x v4 v2) (C (T (C (T (T (C (C (T (h v4 v2 x) (C (C (T (C (R (M v2 x)) h6) (S (h x z v0))) h5) h3)) h6) h5) (S (h v0 x v4))) (h v0 x y)) h3) (S (h y v0 x))) (R v2))

@[equational_result]
theorem Equation3567_implies_Equation4146 (G: Type _) [Magma G] (h: Equation3567 G) : Equation4146 G := fun x y z =>
  let v0 := M (M x z) z
  let v1 := M (M y v0) y
  let v2 := M (M y y) y
  have h3 := R v0
  let v4 := M (M v0 y) v0
  let v5 := M (M y x) y
  T (T (T (T (T (T (T (T (T (T (h x y y) (h y v5 v0)) (h v5 v4 z)) (C (R v4) (C (S (h x z y)) (R z)))) (h v4 v0 y)) (C h3 (C (S (h y y v0)) (R y)))) (h v0 v2 v0)) (C (R v2) (C (h v0 v0 y) h3))) (S (h v1 v2 v0))) (S (h y v1 y))) (S (h v0 y y))

@[equational_result]
theorem Equation3791_implies_Equation3979 (G: Type _) [Magma G] (h: Equation3791 G) : Equation3979 G := fun x y z =>
  let v0 := M z z
  let v1 := M y v0
  let v2 := M x y
  have h3 := h x y v0
  let v4 := M v0 x
  T (T (T (T (T h3 (h v4 v1 v1)) (C (T (T (C (h y v0 x) (h v0 x y)) (S (h v4 v1 v2))) (S h3)) (T (T (h v1 v1 v0) (C (T (C (h z z z) (R v1)) (S (h v0 y v0))) (R (M v1 v0)))) (S (h y v1 v0))))) (C (h x y v1) (h y v1 x))) (S (h (M y v1) v2 (M v1 x)))) (S (h v1 x y))

@[equational_result]
theorem Equation3791_implies_Equation4176 (G: Type _) [Magma G] (h: Equation3791 G) : Equation4176 G := fun x y z =>
  let v0 := M x y
  let v1 := M y z
  let v2 := M v1 x
  let v3 := M y v1
  have h4 := h z x y
  let v5 := M z x
  have h6 := T (T (T (C (h y z x) (h v1 x y)) (S (h v5 v3 v0))) (C h4 (R v3))) (S (h v0 y v1))
  T (T (T (h x y z) (h v5 v1 (M v1 v2))) (C (T (T (C h6 h4) (S (h y v1 v0))) (h y v1 x)) (T (C (R v1) h6) (S (h z v0 y))))) (S (h v2 z v0))

@[equational_result]
theorem Equation3804_implies_Equation3823 (G: Type _) [Magma G] (h: Equation3804 G) : Equation3823 G := fun x y z =>
  let v0 := M y x
  let v1 := M y y
  let v2 := M z y
  have h3 := h y x y
  let v4 := M x z
  T (T (T (T (T (T (T (T (T (h x y z) (h v2 v4 (M z z))) (C (S (h x z z)) (S (h z y z)))) (h v4 v2 v0)) (C (S (h z x y)) (S (h y z x)))) (S (h y x z))) h3) (h v0 v1 v1)) (C (S (h y y y)) (S h3))) (C (T (T (T (h y y z) (C (h z y y) (h y z y))) (S (h (M y z) v2 v1))) (S (h z z y))) (R v0))

@[equational_result]
theorem Equation3804_implies_Equation4364 (G: Type _) [Magma G] (h: Equation3804 G) : Equation4364 G := fun x y z =>
  let v0 := M z x
  let v1 := M y v0
  let v2 := M v0 v0
  let v3 := M x x
  let v4 := M x z
  let v5 := M y z
  T (T (T (T (T (T (T (T (T (h x v5 z) (h (M z v5) v4 v5)) (C (R (M v5 v4)) (S (h y v5 z)))) (S (h y v4 v5))) (h y v4 v0)) (C (S (h x x z)) (R v1))) (h v3 v1 v0)) (C (R (M v0 v1)) (T (h v3 v0 v0) (C (R v2) (S (h z x x)))))) (S (h v2 v1 v0))) (S (h y v0 v0))

@[equational_result]
theorem Equation1639_implies_Equation27 (G: Type _) [Magma G] (h: Equation1639 G) : Equation27 G := fun x y z =>
  let v0 := M x x
  let v1 := M v0 x
  let v2 := M x y
  have h3 := h x x v1
  have h4 := h x x x
  have h5 := R v0
  have h6 := T h3 (C h5 (S h4))
  T (h x z v2) (C (T (h v0 y y) (C (T (T (T (C (C h6 h6) (h v0 x x)) (S (h v1 v0 v1))) (C h5 h4)) (S h3)) (T (C (R (M y y)) (h y x x)) (S (h y y v1))))) (T (C (R (M z z)) (h v2 x x)) (S (h z v2 v1))))

@[equational_result]
theorem Equation1929_implies_Equation508 (G: Type _) [Magma G] (h: Equation1929 G) : Equation508 G := fun x y z =>
  let v0 := M z z
  let v1 := M x v0
  let v2 := M y (M y v1)
  have h3 := h v1 y v2
  let v4 := M x x
  have h5 := R v4
  have h6 := R v1
  T (T (h x x v1) (C (T (C (R x) (T (T (h v4 v1 x) (C (T (C h6 (T (C h3 h5) (S (h v2 v2 x)))) (C h6 (T (h v2 v2 z) (C (S h3) (R v0))))) h5)) (S (h v0 v1 x)))) h3) (R (M v1 v1)))) (S (h v2 v2 v1))

@[equational_result]
theorem Equation2891_implies_Equation3534 (G: Type _) [Magma G] (h: Equation2891 G) : Equation3534 G := fun x y z =>
  let v0 := M z y
  let v1 := M v0 z
  let v2 := M x v1
  have h3 := h v2 v1 v1
  let v4 := M v1 v1
  have h5 := R z
  let v6 := M x y
  have h7 := h v6 v1 v1
  T (T h7 (C (T (T (h (M (M v6 v4) v1) v0 z) (C (T (T (T (C (S h7) h5) (C (C (h x v0 z) (R y)) h5)) (S (h (M v2 z) z y))) (C h3 h5)) (R v0))) (S (h (M (M v2 v4) v1) v0 z))) (R v1))) (S h3)

@[equational_result]
theorem Equation3791_implies_Equation3573 (G: Type _) [Magma G] (h: Equation3791 G) : Equation3573 G := fun x y z =>
  let v0 := M z z
  let v1 := M v0 x
  let v2 := M x y
  have h3 := h x y v0
  let v4 := M y v0
  T (T (T (T (T h3 (h v1 v4 v1)) (C (T (T (h v1 v1 v0) (C (R (M v0 v1)) (T (C (R v1) (h z z z)) (S (h x v0 v0))))) (S (h v1 x v0))) (T (T (C (h y v0 x) (h v0 x y)) (S (h v1 v4 v2))) (S h3)))) (C (h v1 x y) (h x y v1))) (S (h v2 (M v1 x) (M y v1)))) (S (h y v1 x))

