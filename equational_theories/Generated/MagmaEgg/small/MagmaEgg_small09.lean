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
theorem Equation1993_implies_Equation1496 (G: Type _) [Magma G] (h: Equation1993 G) : Equation1496 G := fun x y z =>
  let v0 := M z z
  let v1 := M y v0
  let v2 := M y x
  let v3 := M v2 v1
  let v4 := M v3 v0
  T (T (h x v0 y) (C (R (M v0 (M y y))) (T (T (h (M x v0) v2 x) (C (R (M v2 (M x x))) (T (T (S (h y x z)) (h y v3 z)) (C (R v4) (T (C (h y y z) (R v3)) (S (h v2 v1 y))))))) (S (h v4 v2 x))))) (S (h v3 v0 y))

@[equational_result]
theorem Equation2196_implies_Equation3131 (G: Type _) [Magma G] (h: Equation2196 G) : Equation3131 G := fun x y z =>
  let v0 := M y x
  let v1 := M v0 z
  let v2 := M v1 z
  let v3 := M v2 y
  let v4 := M (M v3 y) y
  let v5 := M x v3
  T (T (T (T (h x v3 v1) (C (R (M (M v3 v1) v1)) (T (h v5 v3 y) (C (R v4) (T (h (M v5 v3) v0 z) (C (R v2) (S (h y x v3)))))))) (S (h v4 v3 v1))) (h v4 (M y v3) v3)) (C (S (h v2 y v3)) (S (h y v3 y)))

@[equational_result]
theorem Equation3385_implies_Equation3588 (G: Type _) [Magma G] (h: Equation3385 G) : Equation3588 G := fun x y z =>
  let v0 := M x y
  let v1 := M v0 z
  let v2 := M z v1
  have h3 := R v2
  let v4 := M y z
  T (T (T (h x y z) (h z (M x v4) v2)) (C h3 (C (R z) (C (T (T (T (h x v4 v2) (C h3 (C (R x) (C (T (h y z v0) (C (R v0) (S (h z x y)))) h3)))) (S (h x (M v0 (M z x)) v2))) (S (h v0 z x))) h3)))) (S (h z v1 v2))

@[equational_result]
theorem Equation3567_implies_Equation3334 (G: Type _) [Magma G] (h: Equation3567 G) : Equation3334 G := fun x y z =>
  let v0 := M z y
  let v1 := M z v0
  let v2 := M (M x x) x
  let v3 := M (M x z) x
  let v4 := M v1 z
  T (T (T (T (T (h x y x) (h y v2 z)) (C (R v2) (T (T (T (T (T (h v0 z z) (h z v4 z)) (C (R v4) (C (h z z x) (R z)))) (S (h v3 v4 z))) (S (h v0 v3 z))) (S (h z v0 x))))) (h v2 v1 x)) (C (R v1) (C (S (h x x x)) (R x)))) (S (h x v1 x))

@[equational_result]
theorem Equation546_implies_Equation1790 (G: Type _) [Magma G] (h: Equation546 G) : Equation1790 G := fun x y z =>
  let v0 := M z x
  let v1 := M v0 y
  let v2 := M y z
  have h3 := R v2
  have h4 := R v0
  have h5 := R x
  have h6 := R v1
  T (h x v2 v1) (C h3 (T (C h6 (C h5 (C h6 (T (h v2 x v0) (C h5 (C h4 (T (T (C h3 (T (C h4 (h x x z)) (S (h z v0 x)))) (C h3 (h z z y))) (S (h y v2 z))))))))) (S (h v1 v1 x))))

@[equational_result]
theorem Equation1120_implies_Equation511 (G: Type _) [Magma G] (h: Equation1120 G) : Equation511 G := fun x y =>
  let v0 := M x y
  let v1 := M y v0
  have h2 := h v1 y
  have h3 := R y
  have h4 := h x y
  let v5 := M (M y (M y x)) y
  have h6 := h v5 y
  T (T h4 (C h3 h6)) (C h3 (C h3 (T (T (h (M (M y (M y v5)) y) y) (C h3 (T (T (T (C (T (C h3 (S h6)) (S h4)) h3) (h v0 y)) (C h3 (C (C h3 h2) h3))) (S (h (M (M y (M y v1)) y) y))))) (S h2))))

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
theorem Equation3791_implies_Equation3820 (G: Type _) [Magma G] (h: Equation3791 G) : Equation3820 G := fun x y z =>
  let v0 := M x y
  let v1 := M z z
  let v2 := M y z
  have h3 := h z y z
  let v4 := M z x
  T (T (T (T (T (T (T (h x y z) (h v4 v2 v0)) (C (S (h y z x)) (S (h z x y)))) (h v2 v4 v1)) (C (S h3) (S (h x z z)))) (S (h y x z))) (h y x y)) (C (T (T (T (h y y z) (C h3 (h y z z))) (S (h v2 (M z y) v1))) (S (h z z y))) (R v0))

@[equational_result]
theorem Equation492_implies_Equation16 (G: Type _) [Magma G] (h: Equation492 G) : Equation16 G := fun x y =>
  let v0 := M y x
  let v1 := M y v0
  have h2 := R y
  have h3 := R v1
  have h4 := C h3 (C h2 (S (h x x y)))
  have h5 := h y v1 x
  have h6 := R v0
  T (T (h x v0 y) (C h6 (T (T (T (S (h y x y)) h5) h4) (C h3 (T (h v0 y v1) (C h2 (T (C h6 (C h3 (C h3 (T h5 h4)))) (S (h v1 v0 v1))))))))) (S (h v1 v0 y))

@[equational_result]
theorem Equation684_implies_Equation1983 (G: Type _) [Magma G] (h: Equation684 G) : Equation1983 G := fun x y z =>
  let v0 := M z x
  have h1 := R v0
  have h2 := S (h y y x)
  let v3 := M y (M (M y x) x)
  have h4 := R z
  let v5 := M x (M (M x x) x)
  have h6 := h x x x
  T (T (h x z x) (C h4 (T (C (R x) (C h1 (T h6 (C h6 (R v5))))) (S (h v0 x v5))))) (C (T (h z y v3) (C (R y) (C h4 (T (C h2 (R v3)) h2)))) h1)

@[equational_result]
theorem Equation711_implies_Equation1320 (G: Type _) [Magma G] (h: Equation711 G) : Equation1320 G := fun x y z =>
  let v0 := M y x
  let v1 := M y (M (M v0 z) z)
  let v2 := M v1 (M (M v1 x) x)
  have h3 := h v1 v1 x
  have h4 := R y
  have h5 := S (h x x x)
  let v6 := M x (M (M x x) x)
  T (T (T (h x y v6) (C h4 (C h4 (T (C h5 (R v6)) h5)))) (C h4 (T (h v0 y z) (C h4 (T h3 (C h3 (R v2))))))) (S (h v1 y v2))

@[equational_result]
theorem Equation725_implies_Equation3567 (G: Type _) [Magma G] (h: Equation725 G) : Equation3567 G := fun x y z =>
  let v0 := M (M z x) z
  let v1 := M y v0
  have h2 := h v1 x z
  have h3 := R x
  have h4 := R v1
  have h5 := h y v1 v0
  T (C h3 (T (T h5 (C h4 (T (h (M v1 (M (M v0 y) v0)) v1 v1) (C h4 (T (C h4 (T (C (S h5) h4) (S (h x y z)))) (C h2 h3)))))) (S (h (M x (M (M z v1) z)) v1 x)))) (S h2)

@[equational_result]
theorem Equation1537_implies_Equation3692 (G: Type _) [Magma G] (h: Equation1537 G) : Equation3692 G := fun x y z =>
  let v0 := M y y
  have h1 := R v0
  have h2 := h x x x
  let v3 := M x x
  have h4 := R x
  have h5 := R v3
  T (T (T (T (h v3 x x) (C h5 (T (C h4 (T (C h5 h2) (S (h x x v3)))) (C h4 (T (h x y v3) (C h1 (S h2))))))) (S (h v0 x x))) (h v0 y z)) (C h1 (C (R z) (T (C h1 (h z z z)) (S (h z y (M z z))))))

@[equational_result]
theorem Equation2196_implies_Equation4305 (G: Type _) [Magma G] (h: Equation2196 G) : Equation4305 G := fun x y z =>
  let v0 := M y z
  let v1 := M z v0
  let v2 := M x y
  let v3 := M (M z v2) v2
  T (T (h (M x v2) v0 v1) (C (R (M (M v0 v1) v1)) (T (T (T (T (C (C (h x y z) (R v2)) (h v0 z v2)) (S (h v3 (M v0 z) v2))) (h v3 v0 x)) (C (R (M (M v0 x) x)) (T (S (h y z v2)) (h y z v0)))) (S (h (M v1 v0) v0 x))))) (S (h v1 v0 v1))

@[equational_result]
theorem Equation2306_implies_Equation25 (G: Type _) [Magma G] (h: Equation2306 G) : Equation25 G := fun x y =>
  have h0 := R x
  let v1 := M x y
  let v2 := M v1 x
  let v3 := M v1 (M y v2)
  have h4 := R v3
  have h5 := S (h y x y)
  have h6 := S (h y v1 x)
  let v7 := M x (M y v1)
  T (h x v3 y) (C (T (T (C h4 (C h0 h6)) (C (T (h v3 v7 y) (C (T (C (R v7) (T (C h4 h5) h6)) h5) h4)) (R v1))) (S (h v1 y v2))) h0)

@[equational_result]
theorem Equation2739_implies_Equation323 (G: Type _) [Magma G] (h: Equation2739 G) : Equation323 G := fun x y =>
  let v0 := M x y
  have h1 := R v0
  let v2 := M x v0
  have h3 := h x (M v2 v2) v0
  have h4 := R x
  have h5 := h v2 v2 v2
  let v6 := M x x
  T (T (h v0 v6 x) (C (T (T (T (C (R (M v6 v6)) (T (C (h v0 v0 v0) h4) (S (h x (M v0 v0) y)))) (S (h x x x))) h3) (C (S h5) h4)) h1)) (C (T (C h5 h4) (S h3)) h1)

@[equational_result]
theorem Equation2776_implies_Equation3973 (G: Type _) [Magma G] (h: Equation2776 G) : Equation3973 G := fun x y z =>
  let v0 := M z x
  let v1 := M y v0
  let v2 := M v1 z
  let v3 := M x y
  have h4 := h v3 x z
  let v5 := M (M x z) (M v3 x)
  T h4 (C (T (T (h v5 v3 v2) (C (C (R (M v3 v2)) (T (C (T (h v5 z x) (C (C (R v0) (S h4)) (h x y v0))) (R v3)) (S (h (M v1 v3) v0 v3)))) (R v2))) (S (h v1 v3 v2))) (R z))

@[equational_result]
theorem Equation3131_implies_Equation4640 (G: Type _) [Magma G] (h: Equation3131 G) : Equation4640 G := fun x y z =>
  let v0 := M (M y z) z
  have h1 := R x
  have h2 := R v0
  let v3 := M x y
  have h4 := R z
  let v5 := M v3 x
  T (C (T (h v3 v0 v0) (C (C (C (T (C (C (C (T (T (h y x x) (C (C (C (T (h v3 v5 v3) (C (S (h x v3 v3)) (R v5))) h1) h1) h1)) (S (h v5 x x))) h4) h4) (R v3)) (S (h x v3 z))) h2) h2) h2)) h1) (S (h v0 x v0))

@[equational_result]
theorem Equation3293_implies_Equation4346 (G: Type _) [Magma G] (h: Equation3293 G) : Equation4346 G := fun x y z =>
  let v0 := M y y
  have h1 := h z x x
  have h2 := h y x x
  have h3 := C (R y) (T (C (T h1 (S h2)) (T (T h2 (S h1)) (h z y v0))) (S (h z v0 y)))
  let v4 := M z z
  T (T (T (C (R x) (T (T (h y z x) (S (h v4 z x))) (C (T (h z y v4) h3) (T h1 (S (h x x x)))))) (S (h y x (M y v4)))) (h y y v4)) h3

@[equational_result]
theorem Equation3791_implies_Equation3997 (G: Type _) [Magma G] (h: Equation3791 G) : Equation3997 G := fun x y z =>
  let v0 := M x z
  let v1 := M z v0
  let v2 := M y v0
  have h3 := R v2
  have h4 := h v0 x z
  have h5 := S h4
  T (T (T (T (h x y v0) (R (M (M v0 x) v2))) (C h4 h3)) (C (T (h v1 v0 (M v1 v0)) (C (T (C h5 (R v1)) (S (h x z v0))) (T (C (R v0) h5) (S (h z v0 x))))) h3)) (S (h v1 y v0))

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
theorem Equation2507_implies_Equation3116 (G: Type _) [Magma G] (h: Equation2507 G) : Equation3116 G := fun x y =>
  have h0 := R y
  let v1 := M y x
  let v2 := M v1 y
  have h3 := h v2 y
  have h4 := h x y
  let v5 := M y (M (M x y) y)
  have h6 := h v5 y
  T (T h4 (C h6 h0)) (C (C (T (T (h (M y (M (M v5 y) y)) y) (C (T (T (T (C h0 (T (C (S h6) h0) (S h4))) (h v1 y)) (C (C h0 (C h3 h0)) h0)) (S (h (M y (M (M v2 y) y)) y))) h0)) (S h3)) h0) h0)

@[equational_result]
theorem Equation2958_implies_Equation1670 (G: Type _) [Magma G] (h: Equation2958 G) : Equation1670 G := fun x y z =>
  have h0 := R y
  have h1 := S (h z x z)
  let v2 := M (M x (M x z)) z
  let v3 := M x y
  have h4 := R v3
  let v5 := M (M x (M x x)) x
  have h6 := h x x x
  T (T (h x x y) (C (T (C (C (T h6 (C (R v5) h6)) h4) (R x)) (S (h v3 v5 x))) h0)) (C h4 (T (h y v2 z) (C (C (T (C (R v2) h1) h1) h0) (R z))))

@[equational_result]
theorem Equation2958_implies_Equation1699 (G: Type _) [Magma G] (h: Equation2958 G) : Equation1699 G := fun x y z =>
  let v0 := M (M x (M x y)) y
  let v1 := M y z
  have h2 := h y x y
  let v3 := M (M y x) (M v1 z)
  have h4 := S (h y v3 y)
  let v5 := M (M v3 (M v3 y)) y
  T (h x v5 y) (C (C (T (C (R v5) h4) h4) (R x)) (T (h y y z) (C (T (C (C (T h2 (C (R v0) h2)) (R v1)) (R y)) (S (h v1 v0 y))) (R z))))

@[equational_result]
theorem Equation3804_implies_Equation3334 (G: Type _) [Magma G] (h: Equation3804 G) : Equation3334 G := fun x y z =>
  let v0 := M z y
  let v1 := M z v0
  let v2 := M x v1
  let v3 := M v1 v2
  let v4 := M v0 z
  T (T (T (T (T (T (T (T (T (h x y v0) (C (h v0 y z) (R (M x v0)))) (S (h x v4 v0))) (h x v4 v1)) (C (S (h v0 v0 z)) (R v2))) (h (M v0 v0) v2 v1)) (C (R v3) (S (h z v0 v0)))) (h v3 v1 v2)) (C (R (M v2 v1)) (S (h x v2 v1)))) (S (h x v1 v2))

@[equational_result]
theorem Equation1967_implies_Equation26 (G: Type _) [Magma G] (h: Equation1967 G) : Equation26 G := fun x y =>
  let v0 := M x y
  let v1 := M y v0
  have h2 := h v0 v0 v1
  have h3 := h y y x
  have h4 := R v0
  have h5 := R y
  have h6 := R x
  have h7 := S h3
  T (h x (M x v1) y) (C (S (h v0 x y)) (T (T (C h5 (C h6 (C h5 (T h2 (C (C h4 h7) h7))))) (C h3 (C h6 (C h5 (T (C (C h4 h3) h3) (S h2)))))) (S (h y v1 x))))

@[equational_result]
theorem Equation2677_implies_Equation3534 (G: Type _) [Magma G] (h: Equation2677 G) : Equation3534 G := fun x y z =>
  let v0 := M z y
  let v1 := M v0 z
  have h2 := h x v0 v0
  let v3 := M x y
  have h4 := h v3 z y
  T (T h4 (C (T (T (T (T (h (M (M v3 z) v0) y x) (C (C (S h4) (R (M y x))) (R x))) (S (h x y x))) h2) (C (T (h (M (M x v0) (M v0 v0)) v0 z) (C (C (S h2) (R v1)) (R z))) (R v0))) (R y))) (S (h (M x v1) z y))

@[equational_result]
theorem Equation2958_implies_Equation3211 (G: Type _) [Magma G] (h: Equation2958 G) : Equation3211 G := fun x y z =>
  let v0 := M y z
  have h1 := S (h y x y)
  let v2 := M (M x (M x y)) y
  let v3 := M v0 z
  let v4 := M v3 x
  have h5 := S (h v3 v4 v3)
  let v6 := M (M v4 (M v4 v3)) v3
  T (h x v6 v3) (C (C (T (C (R v6) h5) h5) (R x)) (T (C (T (h v0 v2 y) (C (C (T (C (R v2) h1) h1) (R v0)) (R y))) (R z)) (S (h y y z))))

@[equational_result]
theorem Equation3195_implies_Equation692 (G: Type _) [Magma G] (h: Equation3195 G) : Equation692 G := fun x y z =>
  let v0 := M z y
  let v1 := M v0 z
  let v2 := M x v1
  have h3 := R v2
  have h4 := R x
  let v5 := M x v2
  T (h x v2 v2) (C (T (C (T (T (T (C (C (T (h v2 v5 x) (C (S (h v5 x v2)) h4)) h3) h3) (S (h v2 x v2))) (h v2 x v1)) (C (R (M (M v2 x) v2)) (T (C (h v0 z y) (R z)) (S (h y v0 z))))) h4) (S (h y v2 x))) h3)

@[equational_result]
theorem Equation3298_implies_Equation4346 (G: Type _) [Magma G] (h: Equation3298 G) : Equation4346 G := fun x y z =>
  have h0 := h z x x
  have h1 := S h0
  have h2 := h (M y y) x x
  have h3 := h y x x
  have h4 := S h3
  have h5 := T h0 h4
  let v6 := M z z
  have h7 := T h3 h1
  have h8 := S h2
  T (T (T (C (R x) (T (T h3 h8) (C h7 (T (T h3 h8) (C h7 h7))))) (S (h z x v6))) (h z y v6)) (C (R y) (T (T (C h5 (T (T (C h5 h5) h2) h4)) h2) h1))

@[equational_result]
theorem Equation3404_implies_Equation4200 (G: Type _) [Magma G] (h: Equation3404 G) : Equation4200 G := fun x y z =>
  let v0 := M z x
  let v1 := M v0 z
  let v2 := M v1 y
  have h3 := R v1
  have h4 := R y
  have h5 := h x y v2
  let v6 := M v2 x
  T (T h5 (C (R v2) (T (T (T (h y v6 v1) (C h3 (T (T (h v6 v2 y) (C h4 (T (S h5) (h x y z)))) (S (h v0 z y))))) (h v1 v1 y)) (C h4 (T (C h3 (h y v1 v1)) (S (h v2 v1 v1))))))) (S (h v1 y v2))

@[equational_result]
theorem Equation3959_implies_Equation3620 (G: Type _) [Magma G] (h: Equation3959 G) : Equation3620 G := fun x y z =>
  let v0 := M z y
  let v1 := M v0 x
  let v2 := M z v1
  have h3 := R v2
  let v4 := M y v2
  let v5 := M x v1
  T (T (T (T (h x y v1) (h (M y v5) v1 v2)) (C (C (R v1) (C (T (h y v5 v2) (C (T (h v5 v4 x) (C (T (C (R v4) (S (h v0 x x))) (S (h z y v1))) (R x))) h3)) h3)) h3)) (S (h (M v1 v2) v1 v2))) (S (h z v1 v1))

@[equational_result]
theorem Equation4197_implies_Equation3776 (G: Type _) [Magma G] (h: Equation4197 G) : Equation3776 G := fun x y z =>
  let v0 := M x y
  let v1 := M z x
  let v2 := M y z
  have h3 := R v1
  have h4 := R v2
  have h5 := h x y v2
  have h6 := h z x y
  T (T (T (T h5 (C (S h6) h4)) (h v1 v2 v0)) (C (T (T (C (T (C (h x y z) h3) (S (h y z v1))) h4) (h v2 v2 v1)) (C (C (T (C h6 h4) (S h5)) h4) h3)) (R v0))) (S (h v2 v1 v0))

@[equational_result]
theorem Equation543_implies_Equation3398 (G: Type _) [Magma G] (h: Equation543 G) : Equation3398 G := fun x y z =>
  let v0 := M x z
  let v1 := M z (M y v0)
  have h2 := S (h z y v0)
  have h3 := R v1
  have h4 := R v0
  have h5 := h y v0 v1
  have h6 := R z
  have h7 := R x
  T (C h7 (T h5 (C h4 (C h3 (T (T h2 (h z x v1)) (C h7 (T (T (C h3 (C h6 (S (h y x z)))) (C h3 (C h6 (T h5 (C h4 (C h3 h2)))))) (S (h v0 v1 z))))))))) (S (h v1 x v0))

@[equational_result]
theorem Equation684_implies_Equation1171 (G: Type _) [Magma G] (h: Equation684 G) : Equation1171 G := fun x y z =>
  let v0 := M z (M y z)
  let v1 := M v0 x
  have h2 := R v1
  let v3 := M z (M (M z x) x)
  have h4 := h z z x
  let v5 := M x (M (M x x) x)
  have h6 := h x x x
  T (T (h x v0 x) (C (R v0) (T (C (R x) (C h2 (T h6 (C h6 (R v5))))) (S (h v1 x v5))))) (C (T (C (R z) (C (R y) (T h4 (C h4 (R v3))))) (S (h y z v3))) h2)

@[equational_result]
theorem Equation952_implies_Equation3810 (G: Type _) [Magma G] (h: Equation952 G) : Equation3810 G := fun x y z =>
  let v0 := M x y
  let v1 := M z y
  let v2 := M v1 (M z x)
  have h3 := S (h y y z)
  have h4 := h v0 y z
  have h5 := R v0
  let v6 := M v1 v1
  T (T h4 (C (R y) (T (h (M (M z v0) v1) v6 y) (C (T (h v6 v0 y) (C h5 (T (C h3 (C (h y x z) h5)) (S (h v2 y x))))) (C (S h4) h3))))) (S (h v2 y v0))

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
theorem Equation2335_implies_Equation16 (G: Type _) [Magma G] (h: Equation2335 G) : Equation16 G := fun x y =>
  let v0 := M y (M y x)
  have h1 := h v0 v0 y
  have h2 := R y
  let v3 := M v0 (M v0 (M v0 v0))
  have h4 := R v3
  have h5 := h v0 v0 v0
  have h6 := h x x y
  T (T h6 (C (T (T (T (h (M x (M x (M x y))) y y) (C (C h2 (C h2 (S h6))) h2)) (C (T h5 (C h4 (T h5 (C h4 h1)))) h2)) (S (h (M v0 (M v0 (M v0 y))) v3 y))) h2)) (S h1)

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
theorem Equation492_implies_Equation4458 (G: Type _) [Magma G] (h: Equation492 G) : Equation4458 G := fun x y z =>
  have h0 := h z y z
  let v1 := M z y
  have h2 := R v1
  have h3 := h y v1 z
  let v4 := M y x
  have h5 := S h3
  have h6 := C h2 h0
  have h7 := R v4
  T (T (T (C (R x) (T (h v4 (M v1 z) v4) (C (T h6 h5) (C h7 (C h7 (T (C h7 (T (T h6 h5) (h y x y))) (S (h x v4 y)))))))) (S (h y x v4))) h3) (C h2 (S h0))

@[equational_result]
theorem Equation522_implies_Equation14 (G: Type _) [Magma G] (h: Equation522 G) : Equation14 G := fun x y =>
  let v0 := M x y
  let v1 := M y v0
  have h2 := R v0
  have h3 := h x v1 y
  have h4 := C h2 (T (T (C h2 (S h3)) (C h2 (h x v0 y))) (S (h y v0 v0)))
  have h5 := h v1 v0 v1
  have h6 := R v1
  T (T h3 (C h6 (C h6 (T (T h5 h4) (C h2 (T (h y v1 v1) (C h6 (T (C h6 (C h6 (C (R y) (T h5 h4)))) (S (h v0 v1 y)))))))))) (S (h v1 v1 v0))

@[equational_result]
theorem Equation684_implies_Equation572 (G: Type _) [Magma G] (h: Equation684 G) : Equation572 G := fun x y z =>
  let v0 := M x y
  let v1 := M v0 (M (M v0 x) x)
  let v2 := M z v0
  have h3 := h v0 v0 x
  have h4 := S (h y y x)
  let v5 := M y (M (M y x) x)
  T (h x y v5) (C (R y) (T (T (C (R x) (T (C h4 (R v5)) h4)) (h v0 z v0)) (C (R z) (T (C (R v0) (C (R v2) (T h3 (C h3 (R v1))))) (S (h v2 v0 v1))))))

@[equational_result]
theorem Equation829_implies_Equation3 (G: Type _) [Magma G] (h: Equation829 G) : Equation3 G := fun x =>
  have h0 := h x x x
  have h1 := S h0
  let v2 := M x x
  let v3 := M v2 v2
  have h4 := R v3
  have h5 := h x v3 x
  have h6 := S h5
  have h7 := R x
  have h8 := C h7 (C h0 h0)
  have h9 := R v2
  T (h x v2 v2) (C h7 (T (T (C (C (T h5 (C h7 (C h1 h1))) h9) h4) (C (T (T (C (T h8 h6) h9) h8) h6) h4)) h1))

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
theorem Equation1910_implies_Equation3489 (G: Type _) [Magma G] (h: Equation1910 G) : Equation3489 G := fun x y z =>
  let v0 := M y z
  let v1 := M v0 z
  let v2 := M y v1
  let v3 := M y (M x v1)
  have h4 := h x y v1
  have h5 := S (h v2 v2 v0)
  have h6 := h v0 y z
  have h7 := C (T h6 (C (R v2) h6)) h6
  T (C (T h4 (C (R v3) (T (h v2 v0 v0) (C (T (T (C (R v0) (S h6)) h7) h5) (T h7 h5))))) h4) (S (h v2 v3 v2))

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
theorem Equation2196_implies_Equation4413 (G: Type _) [Magma G] (h: Equation2196 G) : Equation4413 G := fun x y z =>
  let v0 := M y z
  let v1 := M v0 z
  have h2 := h v0 z z
  have h3 := S (h v1 y z)
  let v4 := M v1 y
  let v5 := M (M z z) z
  let v6 := M x y
  T (T (h (M x v6) v0 z) (C (R (M v1 z)) (T (T (T (C (C (h x y z) (R v6)) h2) (S (h v5 v1 v6))) (h v5 v1 v4)) (C (T (C h3 (R v4)) h3) (S h2))))) (S (h v1 v0 z))

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
theorem Equation3791_implies_Equation3331 (G: Type _) [Magma G] (h: Equation3791 G) : Equation3331 G := fun x y z =>
  let v0 := M y z
  let v1 := M z v0
  let v2 := M x v1
  have h3 := h v0 y z
  have h4 := S h3
  T (T (h x y v2) (C (R (M v2 x)) (T (T (h y v2 v0) (C (T (T h3 (h v1 v0 (M v1 v0))) (C (T (C h4 (R v1)) (S (h y z v0))) (T (C (R v0) h4) (S (h z v0 y))))) (R (M v2 v0)))) (S (h v1 v2 v0))))) (S (h x v1 v2))

@[equational_result]
theorem Equation4085_implies_Equation4609 (G: Type _) [Magma G] (h: Equation4085 G) : Equation4609 G := fun x y z =>
  let v0 := M y y
  have h1 := h y v0 y
  have h2 := S h1
  have h3 := R y
  have h4 := h y y v0
  have h5 := C h4 h3
  let v6 := M (M x x) y
  T (T (T (T (C (T (T (h x v0 v6) (C (C (T (T (T (C h4 (R x)) (S (h y v0 x))) h1) (C (S h4) h3)) (R v0)) (R v6))) (S (h y v0 v6))) h3) h5) h2) (h y y z)) (C (T h5 h2) (R z))

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

@[equational_result]
theorem Equation2135_implies_Equation3150 (G: Type _) [Magma G] (h: Equation2135 G) : Equation3150 G := fun x y =>
  let v0 := M (M y y) y
  let v1 := M v0 x
  let v2 := M v1 y
  let v3 := M v2 v2
  let v4 := M v3 v2
  let v5 := M x x
  have h6 := T (T (h (M v5 x) v1) (C (R (M (M v1 v1) v1)) (T (T (S (h v0 x)) (h v0 v2)) (C (R v4) (S (h v1 y)))))) (S (h v4 v1))
  T (T (h x x) (C h6 (T (T (h v5 x) (C h6 h6)) (S (h v3 v2))))) (S (h v2 v2))

@[equational_result]
theorem Equation2196_implies_Equation1467 (G: Type _) [Magma G] (h: Equation2196 G) : Equation1467 G := fun x y z =>
  let v0 := M y z
  let v1 := M z v0
  let v2 := M v0 v1
  let v3 := M x y
  let v4 := M v3 v1
  let v5 := M v3 y
  T (T (T (h x y v4) (C (R (M (M y v4) v4)) (T (C (h x y v3) (h y v3 y)) (S (h (M v5 y) (M y v3) v3))))) (S (h v5 y v4))) (C (R v3) (T (h y v2 v1) (C (S (h z v0 v1)) (T (C (h y z v0) (R v2)) (S (h v0 v1 v0))))))

@[equational_result]
theorem Equation2958_implies_Equation2482 (G: Type _) [Magma G] (h: Equation2958 G) : Equation2482 G := fun x y z =>
  let v0 := M (M x (M x y)) y
  have h1 := h y x y
  let v2 := M (M y z) y
  let v3 := M x v2
  have h4 := R v3
  let v5 := M (M x (M x x)) x
  have h6 := h x x x
  T (T (h x x v2) (C (T (C (C (T h6 (C (R v5) h6)) h4) (R x)) (S (h v3 v5 x))) (R v2))) (C h4 (T (C (C (T h1 (C (R v0) h1)) (R z)) (R y)) (S (h z v0 y))))

@[equational_result]
theorem Equation3182_implies_Equation4210 (G: Type _) [Magma G] (h: Equation3182 G) : Equation4210 G := fun x y z =>
  let v0 := M z y
  let v1 := M (M v0 x) z
  have h2 := R y
  have h3 := R v0
  have h4 := R v1
  have h5 := R z
  have h6 := S (h z v0 x)
  have h7 := h x v1 v0
  T (C (T h7 (C (C (T (T h6 (h z v1 y)) (C (T (T (C (C (S (h x z y)) h5) h4) (C (C (T h7 (C (C h6 h4) h3)) h5) h4)) (S (h v0 z v1))) h2)) h4) h3)) h2) (S (h v1 v0 y))

@[equational_result]
theorem Equation3290_implies_Equation3303 (G: Type _) [Magma G] (h: Equation3290 G) : Equation3303 G := fun x y z w =>
  let v0 := M w w
  have h1 := h w v0 w
  have h2 := R w
  let v3 := M x x
  let v4 := M y (M z v0)
  have h5 := S (h x v3 x)
  T (T (T (T (h x v4 v3) (C (R v4) (T (T h5 (h x v3 v3)) (C (R v3) (T (T h5 (h x w v3)) (C h2 h5)))))) (S (h w v4 v3))) (h w y v0)) (C (R y) (T (T (S h1) (h w z w)) (C (R z) (T (C h2 h1) (S (h w w v0))))))

@[equational_result]
theorem Equation3791_implies_Equation4135 (G: Type _) [Magma G] (h: Equation3791 G) : Equation4135 G := fun x y z =>
  let v0 := M x y
  let v1 := M v0 z
  let v2 := M y v1
  let v3 := M y v0
  have h4 := h x y v0
  T (T (T (T (T (T (T h4 (C (T (T (h v0 x y) (h v3 v0 (M v0 x))) (C (S h4) (S (h y v0 x)))) (R v3))) (S (h v3 y v0))) (h v3 y v1)) (C (S (h z y v0)) (R v2))) (C (h z y v1) (h y v1 z))) (S (h v2 (M z y) (M v1 z)))) (S (h v1 z y))

@[equational_result]
theorem Equation3791_implies_Equation4458 (G: Type _) [Magma G] (h: Equation3791 G) : Equation4458 G := fun x y z =>
  let v0 := M z y
  have h1 := h v0 z y
  let v2 := M y v0
  let v3 := M y x
  T (T (T (T (T (T (T (h x v3 v0) (h (M v0 x) (M v3 v0) (M x v3))) (C (T (S (h v3 v0 x)) (S (h x z y))) (S (h v0 x v3)))) (S (h z v0 x))) (h z v0 v0)) (C (T (T h1 (h v2 v0 (M v0 z))) (C (S (h z y v0)) (S (h y v0 z)))) (R (M v0 v0)))) (S (h v2 v0 v0))) (S h1)

@[equational_result]
theorem Equation4095_implies_Equation369 (G: Type _) [Magma G] (h: Equation4095 G) : Equation369 G := fun x y z =>
  let v0 := M y y
  let v1 := M v0 z
  let v2 := M x x
  have h3 := R (M v2 x)
  have h4 := R v2
  have h5 := h x x x
  have h6 := T (h y x x) (S h5)
  T (h x v2 z) (C (T (T (T (T (C (C (T (T (T h5 (C h3 (R x))) (S (h v0 x x))) (C h6 h6)) h4) h4) (S (h x v2 v2))) (h x x v1)) (C h3 (R v1))) (S (h y x v1))) (R z))

@[equational_result]
theorem Equation4176_implies_Equation3692 (G: Type _) [Magma G] (h: Equation4176 G) : Equation3692 G := fun x y z =>
  let v0 := M z z
  have h1 := R v0
  have h2 := R x
  let v3 := M x x
  have h4 := h x x x
  T (T (T (T h4 (C (T (C h4 h2) (S (h x v3 x))) h2)) (C (T (h x v3 v0) (C (S (h v0 x x)) h1)) h2)) (S (h v0 v0 x))) (C (T (T (T (h z z x) (C (T (C (h z x x) (R z)) (S (h x v3 z))) h2)) (C (T (h x v3 y) (C (S (h y x x)) (R y))) h2)) (S (h y y x))) h1)

@[equational_result]
theorem Equation684_implies_Equation4305 (G: Type _) [Magma G] (h: Equation684 G) : Equation4305 G := fun x y z =>
  let v0 := M z (M y z)
  have h1 := S (h v0 v0 x)
  let v2 := M v0 (M (M v0 x) x)
  let v3 := M x v0
  have h4 := S (h z z x)
  let v5 := M z (M (M z x) x)
  have h6 := R x
  T (C h6 (T (T (C h6 (T (h y z v5) (C (R z) (C (R y) (T (C h4 (R v5)) h4))))) (h v3 v0 v2)) (C (R v0) (C (R v3) (T (C h1 (R v2)) h1))))) (S (h v0 x v0))

@[equational_result]
theorem Equation1492_implies_Equation477 (G: Type _) [Magma G] (h: Equation1492 G) : Equation477 G := fun x y =>
  let v0 := M y (M y y)
  let v1 := M x v0
  let v2 := M y v1
  let v3 := M v2 v2
  let v4 := M v2 v3
  let v5 := M x x
  have h6 := T (T (h (M x v5) v1) (C (T (T (S (h v0 x)) (h v0 v2)) (C (S (h v1 y)) (R v4))) (R (M v1 (M v1 v1))))) (S (h v4 v1))
  T (T (h x x) (C (T (T (h v5 x) (C h6 h6)) (S (h v3 v2))) h6)) (S (h v2 v2))

@[equational_result]
theorem Equation1707_implies_Equation2373 (G: Type _) [Magma G] (h: Equation1707 G) : Equation2373 G := fun x y z =>
  let v0 := M x z
  let v1 := M z v0
  let v2 := M y v1
  let v3 := M v2 y
  have h4 := h v0 z v2
  let v5 := M (M v2 z) v2
  T (T (h x v0 v3) (C (T (T (T (T (h (M v0 x) v1 x) (C (T (S (h v0 z x)) h4) (R (M (M x v1) x)))) (S (h v5 v1 x))) (h v5 v1 y)) (C (S h4) (R v3))) (R (M (M v3 v0) v3)))) (S (h v3 v0 v3))

@[equational_result]
theorem Equation1710_implies_Equation1523 (G: Type _) [Magma G] (h: Equation1710 G) : Equation1523 G := fun x y z =>
  let v0 := M y y
  let v1 := M z z
  let v2 := M x v1
  let v3 := M v0 v2
  let v4 := M v0 v0
  have h5 := h v1 x v0
  let v6 := M v4 x
  T (T (h x v1 v0) (C (T (T (T (T (h (M v1 x) v2 x) (C (T (S (h v1 x z)) h5) (R (M (M x x) v2)))) (S (h v6 v2 x))) (h v6 v2 y)) (C (S h5) (R v3))) (R (M v4 v1)))) (S (h v3 v1 v0))

@[equational_result]
theorem Equation2944_implies_Equation711 (G: Type _) [Magma G] (h: Equation2944 G) : Equation711 G := fun x y z =>
  let v0 := M (M x z) z
  let v1 := M y (M y v0)
  let v2 := M (M x (M x v1)) v1
  have h3 := R x
  have h4 := h v1 x v1
  have h5 := R z
  have h6 := S (h x x x)
  let v7 := M (M x (M x x)) x
  T (T (T (T (h x v7 z) (C (C (T (C (R v7) h6) h6) h5) h5)) (h v0 y x)) (C (C (T h4 (C (R v2) h4)) h3) h3)) (S (h v1 v2 x))

@[equational_result]
theorem Equation3218_implies_Equation5 (G: Type _) [Magma G] (h: Equation3218 G) : Equation5 G := fun x y =>
  let v0 := M y x
  have h1 := R y
  have h2 := S (h v0 v0 v0)
  have h3 := R v0
  have h4 := S (h v0 v0 x)
  have h5 := C (h x y x) h3
  have h6 := C (C (C (T h5 h4) h3) h3) h3
  have h7 := h v0 x v0
  T (h x y y) (C (T (C (C (C (T (h y x v0) (C (T (C (T (T (T (C (T (T (T h5 h4) h7) h6) h3) h2) h7) h6) h3) h2) h1)) h1) h1) h1) (S (h y v0 y))) (R x))

@[equational_result]
theorem Equation3404_implies_Equation4620 (G: Type _) [Magma G] (h: Equation3404 G) : Equation4620 G := fun x y z =>
  let v0 := M z y
  have h1 := h z y z
  let v2 := M y (M z z)
  let v3 := M v0 z
  have h4 := R v0
  T (T (h (M x x) y v0) (C h4 (T (C (R y) (T (T (C h4 (T (T (h x x z) (C (R z) (T (T (C (R x) (h z x v0)) (S (h v3 v0 x))) (C (R v3) h1)))) (S (h v2 v3 z)))) (S (h z v2 v0))) (S h1))) (h y v0 z)))) (S (h v0 z v0))

@[equational_result]
theorem Equation3791_implies_Equation3414 (G: Type _) [Magma G] (h: Equation3791 G) : Equation3414 G := fun x y z =>
  let v0 := M x y
  let v1 := M z v0
  let v2 := M v1 x
  let v3 := M v0 x
  have h4 := h x y v0
  T (T (T (T (T (T (T h4 (C (R v3) (T (T (h y v0 x) (h v0 v3 (M y v0))) (C (S (h v0 x y)) (S h4))))) (S (h x v3 v0))) (h x v3 v1)) (C (R v2) (S (h x z v0)))) (C (h v1 x z) (h x z v1))) (S (h (M x z) v2 (M z v1)))) (S (h z v1 x))

@[equational_result]
theorem Equation3791_implies_Equation4197 (G: Type _) [Magma G] (h: Equation3791 G) : Equation4197 G := fun x y z =>
  let v0 := M z x
  let v1 := M v0 y
  let v2 := M z v0
  let v3 := M y z
  have h4 := R v2
  have h5 := h x y z
  T (T (T (T (T h5 (h v0 v3 z)) (C h4 (T (T (T (h v3 z v0) (C (S h5) h4)) (h (M x y) v2 v3)) (C (S (h z x y)) (S (h v0 y z)))))) (C (h z v0 v1) (h v0 v1 z))) (S (h (M v0 v1) v2 (M v1 z)))) (S (h v1 z v0))

@[equational_result]
theorem Equation4216_implies_Equation3370 (G: Type _) [Magma G] (h: Equation4216 G) : Equation3370 G := fun x y z =>
  let v0 := M z x
  let v1 := M v0 z
  have h2 := R y
  let v3 := M v1 v0
  let v4 := M (M v0 y) v0
  T (T (T (T (T (T (T (h x y v0) (h v4 x v1)) (C (C (h v1 x z) (R v1)) (R v4))) (S (h v4 v1 v1))) (S (h v1 y v0))) (C (T (h v0 z v0) (h v3 v0 v1)) h2)) (S (h y v1 v3))) (C h2 (T (C (T (h z x z) (h v1 z v0)) (R z)) (S (h z v0 v1))))

@[equational_result]
theorem Equation4216_implies_Equation3553 (G: Type _) [Magma G] (h: Equation4216 G) : Equation3553 G := fun x y z =>
  let v0 := M x z
  let v1 := M v0 z
  have h2 := R y
  have h3 := R v1
  have h4 := h v0 z x
  have h5 := C (T (h v1 x v0) (C (S h4) h3)) h3
  let v6 := M (M v0 y) v0
  T (T (T (T (T (T (T (T (T (h x y v0) (h v6 x v1)) (C h5 (R v6))) (S (h v6 v1 v1))) (S (h v1 y v0))) (C h4 h2)) (S (h y x v0))) (h y x v1)) (C h5 h2)) (S (h y v1 v1))

@[equational_result]
theorem Equation508_implies_Equation1996 (G: Type _) [Magma G] (h: Equation508 G) : Equation1996 G := fun x y z =>
  let v0 := M z z
  have h1 := h v0 y z
  have h2 := S h1
  have h3 := R y
  have h4 := h y y v0
  let v5 := M y v0
  T (h x v5 y) (C (R v5) (T (C (T (C h3 h1) (S h4)) (R (M x (M y y)))) (C h3 (T (C (R x) (T (T (C h3 (T (T h4 (C h3 h2)) (C h3 (T (h v0 v0 v0) (C (R v0) (S (h v0 v0 z))))))) h2) (h v0 x z))) (S (h x x v0))))))

@[equational_result]
theorem Equation1507_implies_Equation1165 (G: Type _) [Magma G] (h: Equation1507 G) : Equation1165 G := fun x y z =>
  let v0 := M y x
  let v1 := M z v0
  let v2 := M v1 z
  let v3 := M y v2
  let v4 := M y v3
  have h5 := h z v1 v3
  let v6 := M v3 (M v3 v1)
  T (T (h x y v3) (C (T (T (h v0 z z) (C (T (T (T (C h5 (h v0 z v1)) (S (h v6 v2 v1))) (h v6 v2 y)) (C (S h5) (R v4))) (R (M z (M z z))))) (S (h v4 z z))) (R (M v3 (M v3 y))))) (S (h v3 y v3))

@[equational_result]
theorem Equation2663_implies_Equation263 (G: Type _) [Magma G] (h: Equation2663 G) : Equation263 G := fun x y =>
  have h0 := R x
  let v1 := M x y
  let v2 := M v1 y
  have h3 := h v2 x
  let v4 := M v2 x
  have h5 := h v1 y
  have h6 := h x x
  have h7 := S h6
  let v8 := M x x
  T h6 (C (T (T (h (M v8 v8) x) (C (T (T (C h7 h7) (C (T (T (T (h x y) (C (C h5 h5) (R y))) (S (h (M v2 v2) y))) (C h3 h3)) h0)) (S (h (M v4 v4) x))) h0)) (S h3)) h0)

@[equational_result]
theorem Equation3159_implies_Equation1884 (G: Type _) [Magma G] (h: Equation3159 G) : Equation1884 G := fun x y =>
  have h0 := R x
  let v1 := M x x
  have h2 := h x x v1
  have h3 := h x v1 x
  have h4 := T h3 (C (S h2) h0)
  have h5 := S (h y x y)
  have h6 := R y
  have h7 := C (T (C (C (T (C h2 h0) (S h3)) h0) h6) (R (M v1 y))) h6
  have h8 := h y x x
  T (h x y y) (C (C (T (C (T (T (T (C (T h8 h7) h6) h5) h8) h7) h6) h5) h4) h4)

@[equational_result]
theorem Equation3364_implies_Equation4182 (G: Type _) [Magma G] (h: Equation3364 G) : Equation4182 G := fun x y z =>
  have h0 := R x
  let v1 := M y z
  let v2 := M z v1
  let v3 := M v1 v2
  let v4 := M z (M x z)
  T (T (T (T (T (T (T (h x y z) (h y v4 v2)) (C (R v4) (C (R v2) (h y v2 z)))) (S (h v2 v4 v2))) (S (h x v2 z))) (C h0 (T (h z v1 v1) (h v1 v3 v2)))) (S (h v2 x v3))) (C (T (C (R z) (T (h y z z) (h z v2 v1))) (S (h v1 z v2))) h0)

@[equational_result]
theorem Equation3385_implies_Equation4364 (G: Type _) [Magma G] (h: Equation3385 G) : Equation4364 G := fun x y z =>
  let v0 := M y z
  have h1 := h z x v0
  have h2 := h x y z
  have h3 := R v0
  have h4 := R y
  have h5 := h v0 x y
  let v6 := M y (M z x)
  T (T (T (T (h x v0 v6) (C (R v6) (T (T (C (R x) (C h3 (T (C h4 (T h1 (C h3 (S h2)))) (S h5)))) (S (h v0 v0 x))) (C h3 (h y z x))))) (S (h v0 x v6))) h5) (C h4 (T (C h3 h2) (S h1)))

@[equational_result]
theorem Equation3404_implies_Equation3500 (G: Type _) [Magma G] (h: Equation3404 G) : Equation3500 G := fun x y z =>
  let v0 := M z z
  let v1 := M v0 y
  have h2 := S (h y v1 v0)
  have h3 := R y
  have h4 := R v0
  T (T (T (T (T (h x x y) (C h3 (T (C (R x) (h y x v0)) (S (h v1 v0 x))))) (C h3 (T (h v1 v0 v0) (C h4 (S (h y v0 v0)))))) (S (h v0 v0 y))) (C h4 (T (T (T (h z z y) (C h3 (T (C (R z) (h y z v0)) (S (h v1 v0 z))))) (C h3 (T (h v1 v0 v1) (C (R v1) h2)))) (S (h v1 v1 y))))) h2

@[equational_result]
theorem Equation3404_implies_Equation4210 (G: Type _) [Magma G] (h: Equation3404 G) : Equation4210 G := fun x y z =>
  let v0 := M z y
  let v1 := M v0 x
  have h2 := R x
  have h3 := R v0
  T (T (h x y x) (C h2 (T (h y (M x x) z) (C (R z) (T (T (C (T (T (T (h x x x) (C h2 (T (C h2 (h x x v0)) (S (h v1 v0 x))))) (C h2 (T (h v1 v0 v0) (C h3 (S (h x v0 v0)))))) (S (h v0 v0 x))) h3) (h (M v0 v0) v0 x)) (C h2 (S (h v0 x v0)))))))) (S (h v1 z x))

@[equational_result]
theorem Equation3791_implies_Equation3385 (G: Type _) [Magma G] (h: Equation3791 G) : Equation3385 G := fun x y z =>
  let v0 := M y z
  let v1 := M x v0
  let v2 := M v0 z
  have h3 := R v2
  let v4 := M z x
  have h5 := h x y z
  T (T (T (T (T h5 (h v4 v0 z)) (C (T (T (T (h z v4 v0) (C h3 (S h5))) (h v2 (M x y) v4)) (C (S (h x v0 z)) (S (h y z x)))) h3)) (C (h v1 v0 z) (h v0 z v1))) (S (h v2 (M v1 v0) (M z v1)))) (S (h z v1 v0))

@[equational_result]
theorem Equation3791_implies_Equation4210 (G: Type _) [Magma G] (h: Equation3791 G) : Equation4210 G := fun x y z =>
  let v0 := M z y
  let v1 := M v0 x
  let v2 := M v1 z
  have h3 := h v1 z y
  let v4 := M y v1
  let v5 := M v0 z
  T (T (T (h x y v0) (h v1 (M y v0) v2)) (C (R (M v2 v1)) (T (T (T (C (h y v0 z) h3) (S (h v5 v4 v0))) (C (R v5) (T (T (h y v1 z) (h v0 v2 v4)) (C (S h3) (S (h z y v1)))))) (S (h z v2 v0))))) (S (h v1 z v2))

@[equational_result]
theorem Equation3804_implies_Equation3526 (G: Type _) [Magma G] (h: Equation3804 G) : Equation3526 G := fun x y z =>
  let v0 := M y z
  let v1 := M v0 z
  let v2 := M x z
  let v3 := M v0 v2
  have h4 := R v3
  T (T (T (T (T (T (T (T (h x y z) (h (M z y) v2 v0)) (C h4 (S (h y y z)))) (h v3 (M y y) v0)) (C (S (h y z y)) (T (T (C h4 (h y z z)) (S (h (M z z) v2 v0))) (S (h x z z))))) (h v0 v2 v1)) (C (R (M v1 v2)) (h v0 v1 z))) (S (h (M z v1) v2 v1))) (S (h x v1 z))

@[equational_result]
theorem Equation3804_implies_Equation4200 (G: Type _) [Magma G] (h: Equation3804 G) : Equation4200 G := fun x y z =>
  let v0 := M z x
  let v1 := M v0 z
  let v2 := M y y
  let v3 := M v1 z
  let v4 := M v0 x
  let v5 := M z y
  T (T (T (T (h x y y) (h v2 (M x y) v1)) (C (T (T (T (C (h v0 z x) (h x y z)) (S (h v5 v4 (M x z)))) (h v5 v4 v3)) (C (T (C (R v3) (h v0 x z)) (S (h v0 z v1))) (S (h v1 y z)))) (R (M v2 v1)))) (S (h v2 (M v1 y) v1))) (S (h v1 y y))

@[equational_result]
theorem Equation3810_implies_Equation4620 (G: Type _) [Magma G] (h: Equation3810 G) : Equation4620 G := fun x y z =>
  let v0 := M x x
  let v1 := M z y
  let v2 := M v0 v1
  let v3 := M v0 z
  let v4 := M v0 y
  have h5 := S (h v0 y z)
  let v6 := M z v0
  T (T (T (T (h v0 y v1) (C (h v1 y v0) (T (C (h z y v0) (T (T (T (h x x x) (h v0 v0 z)) (h v6 v6 v1)) (C h5 h5))) (S (h v4 v3 v4))))) (S (h v3 v2 v4))) (R (M v3 v2))) (S (h v1 z v0))

@[equational_result]
theorem Equation492_implies_Equation2170 (G: Type _) [Magma G] (h: Equation492 G) : Equation2170 G := fun x y z =>
  let v0 := M z y
  let v1 := M y z
  let v2 := M v1 x
  have h3 := R v0
  have h4 := R y
  have h5 := R v2
  T (h x v2 v0) (C h5 (T (C (R x) (C h3 (C h3 (T (h v2 v0 y) (C h3 (T (C h5 (T (C h4 (T (C h4 (T (h v0 z v0) (C (R z) (C h3 (C h3 (T (C h3 (h z y z)) (S (h y v0 z)))))))) (S (h z y v0)))) (h v1 x v1))) (S (h x v2 v1)))))))) (S (h v0 x v0))))

@[equational_result]
theorem Equation711_implies_Equation2944 (G: Type _) [Magma G] (h: Equation711 G) : Equation2944 G := fun x y z =>
  let v0 := M y (M y x)
  let v1 := M (M v0 z) z
  let v2 := M v1 (M (M v1 x) x)
  have h3 := h v1 v1 x
  have h4 := R x
  have h5 := S (h x x x)
  let v6 := M x (M (M x x) x)
  have h7 := R y
  T (T (T (T (h x y v6) (C h7 (C h7 (T (C h5 (R v6)) h5)))) (h v0 x z)) (C h4 (C h4 (T h3 (C h3 (R v2)))))) (S (h v1 x v2))

@[equational_result]
theorem Equation857_implies_Equation4 (G: Type _) [Magma G] (h: Equation857 G) : Equation4 G := fun x y =>
  let v0 := M x x
  let v1 := M v0 v0
  have h2 := h v0 x x
  let v3 := M x y
  let v4 := M y y
  let v5 := M y v3
  T (h x y v3) (C (R x) (T (T (T (C (R v5) (T (h v4 y y) (C (h v4 x x) (R (M v4 v4))))) (S (h v5 v4 v1))) (C (R y) (T (h v3 x x) (C (R v3) (T (C (R v0) (T h2 (C h2 (R v1)))) (S (h v0 v0 v1))))))) (S (h y x y))))

@[equational_result]
theorem Equation1993_implies_Equation2132 (G: Type _) [Magma G] (h: Equation1993 G) : Equation2132 G := fun x y z =>
  let v0 := M z z
  let v1 := M y y
  let v2 := M v1 x
  let v3 := M v2 v0
  have h4 := S (h v3 v3 y)
  let v5 := M v1 (M v0 v0)
  T (T (h x x v1) (C (T (h (M x (M v1 v1)) v2 z) (C (R v3) (S (h v1 x v1)))) (T (T (T (C (h x x y) (h x v1 v0)) (S (h v5 (M x v1) x))) (h v5 (M v3 v1) v3)) (C h4 (S (h v3 v1 v0)))))) h4

@[equational_result]
theorem Equation2757_implies_Equation5 (G: Type _) [Magma G] (h: Equation2757 G) : Equation5 G := fun x y =>
  let v0 := M y x
  let v1 := M x x
  let v2 := M v1 v1
  have h3 := h v1 x x
  let v4 := M y y
  let v5 := M v0 y
  T (h x y v0) (C (T (T (T (C (T (h v4 y y) (C (R (M v4 v4)) (h v4 x x))) (R v5)) (S (h v5 v4 v2))) (C (T (h v0 x x) (C (T (C (T h3 (C (R v2) h3)) (R v1)) (S (h v1 v1 v2))) (R v0))) (R y))) (S (h y x y))) (R x))

@[equational_result]
theorem Equation3298_implies_Equation320 (G: Type _) [Magma G] (h: Equation3298 G) : Equation320 G := fun x y z =>
  let v0 := M x x
  let v1 := M z z
  let v2 := M y v1
  have h3 := h x x x
  have h4 := T (h z x x) (S h3)
  have h5 := C h4 h4
  have h6 := S (h v1 x x)
  T (h x y v2) (C (R y) (T (T (R (M v2 (M v2 v2))) (C (R v2) (T (T (T (h v2 x x) h6) h5) (C (R v0) (T (T (T h3 (C (R x) (R (M x v0)))) h6) h5))))) (S (h z v2 v0))))

