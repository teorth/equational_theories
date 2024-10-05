import equational_theories.AllEquations
import equational_theories.Magma

private def congr_op {G: Type _} [Magma G] {a b c d: G} (h1: a = b) (h2: c = d): a ◇ c = b ◇ d := by
  rw [h1, h2]
private abbrev T := @Eq.trans
private abbrev S := @Eq.symm
private abbrev R := @Eq.refl
private abbrev M := @Magma.op
private abbrev C := @congr_op

@[equational_result]
theorem Equation3973_implies_Equation4023 (G: Type _) [Magma G] (h: Equation3973 G) : Equation4023 G := fun x y z =>
  let v0 := M z x
  let v1 := M z v0
  let v2 := M v1 y
  let v3 := M z v1
  have h4 := R v2
  have h5 := R z
  have h6 := h z x v1
  let v7 := M x (M v1 z)
  T (T (T (T (h x y z) (h (M y v0) z v2)) (C (C h5 (C h4 (T (T (h y v0 v2) (C (C (T (T (T h6 (h v7 v1 v0)) (C (C (R v1) (T (h v0 v7 z) (C (S h6) h5))) (R v0))) (S (h z v1 v0))) (R (M v2 y))) h4)) (S (h y v3 v2))))) h4)) (S (h (M y v3) z v2))) (S (h v1 y z))

@[equational_result]
theorem Equation4092_implies_Equation369 (G: Type _) [Magma G] (h: Equation4092 G) : Equation369 G := fun x y z =>
  have h0 := R z
  let v1 := M y y
  let v2 := M v1 z
  let v3 := M x x
  have h4 := R v2
  have h5 := R x
  have h6 := h x v1 v3
  have h7 := R v3
  have h8 := h v1 y x
  have h9 := h v1 y v3
  T (h x v2 z) (C (T (T (T (T (T (C (T (T (S (h z y v2)) (h z x x)) (C (T (T (T (T (C (T (T h6 (C (S h8) h7)) (S h9)) h0) (S (h v1 y z))) h9) (C h8 h7)) (S h6)) h5)) h5) (S (h x x x))) (h x v3 v2)) (C (S (h v3 x x)) h4)) (C (h v3 x y) h4)) (S (h y v3 v2))) h0)

@[equational_result]
theorem Equation1507_implies_Equation2958 (G: Type _) [Magma G] (h: Equation1507 G) : Equation2958 G := fun x y z =>
  let v0 := M y z
  let v1 := M y v0
  let v2 := M v1 x
  let v3 := M z v1
  let v4 := M v2 (M v2 y)
  have h5 := h v1 z y
  have h6 := h v0 y v2
  let v7 := M v0 (M v0 v1)
  let v8 := M v1 (M v1 v1)
  T (h x v1 v1) (C (R v2) (T (T (T (T (h v8 v0 x) (C (T (T (T (C h6 (R v8)) (S (h v4 v1 v1))) (h v4 v1 v0)) (C (S h6) (R v7))) (R (M x (M x v0))))) (S (h v7 v0 x))) (C (R v0) (T (C h6 (T h5 (C (R v3) h5))) (S (h v4 v1 v3))))) (S (h z y v2))))

@[equational_result]
theorem Equation3591_implies_Equation4023 (G: Type _) [Magma G] (h: Equation3591 G) : Equation4023 G := fun x y z =>
  let v0 := M z x
  let v1 := M z v0
  let v2 := M v1 y
  let v3 := M v1 x
  have h4 := R x
  have h5 := h z x v0
  have h6 := S h5
  have h7 := R v3
  let v8 := M x x
  T (T (T (T (h x y x) (h x (M v8 y) v2)) (C (R v2) (C (R (M x v2)) (T (T (h v8 y x) (C h4 (C (C (T (T (h x x v0) (C (R v0) (C (T (C h4 (T (T h5 (h v0 v3 v3)) (C h7 (T (C h6 h7) h6)))) (S (h v1 v0 x))) h4))) (S (h v1 x v0))) h4) (R y)))) (S (h v3 y x)))))) (S (h x (M v3 y) v2))) (S (h v1 y x))

@[equational_result]
theorem Equation3940_implies_Equation3526 (G: Type _) [Magma G] (h: Equation3940 G) : Equation3526 G := fun x y z =>
  let v0 := M y z
  let v1 := M v0 z
  let v2 := M x v1
  let v3 := M v0 v1
  have h4 := R y
  let v5 := M y v1
  have h6 := R v5
  have h7 := h y z v0
  have h8 := S h7
  let v9 := M v0 y
  T (T (T (T (h x y v0) (h (M x v9) v0 v2)) (C (C (T (T (h x v9 y) (C (C (R x) (C h4 (T (C (T (T h7 (h v5 v0 v5)) (C (T (C h6 h8) h8) h6)) h4) (S (h v0 v1 y))))) h4)) (S (h x v3 y))) (R (M v2 v0))) (R v2))) (S (h (M x v3) v0 v2))) (S (h x v1 v0))

@[equational_result]
theorem Equation1314_implies_Equation2 (G: Type _) [Magma G] (h: Equation1314 G) : Equation2 G := fun x y =>
  have h0 := R y
  let v1 := M (M (M x y) y) x
  have h2 := h x x x
  have h3 := S h2
  let v4 := M (M (M x x) x) x
  have h5 := R v4
  have h6 := T (C h3 h5) h3
  have h7 := R x
  have h8 := C h7 (T (C h6 (R v1)) (S (h y x x)))
  have h9 := h v4 x v1
  have h10 := C (T (T (T (T (T h2 (C h7 (T (h v4 x v4) (C h7 (T (C h6 h5) h3))))) (C h7 (C (T h2 (C h2 h5)) h7))) (S (h v4 x x))) h9) h8) h0
  T (T h2 (C h7 (T (T (T h9 h8) h10) (C h10 h0)))) (S (h y x y))

@[equational_result]
theorem Equation1739_implies_Equation2 (G: Type _) [Magma G] (h: Equation1739 G) : Equation2 G := fun x y =>
  let v0 := M y y
  have h1 := R x
  have h2 := R y
  have h3 := h y x y
  have h4 := h v0 y y
  let v5 := M x x
  have h6 := R v5
  let v7 := M y v0
  have h8 := h (M v7 y) x v0
  have h9 := T (T h8 (C h6 (C (S h4) h1))) (S h3)
  T (T (h x y x) (C (R v0) (T (C h6 (T (T (T h3 (C h6 (C (h v0 x y) h1))) (S (h (M v7 x) x v5))) (C (C h2 (T (T h4 (C (C h2 (T (T h3 (C h6 (C h4 h1))) (S h8))) h9)) (C (C h2 h9) h2))) h1))) (S (h (M v0 y) x y))))) (S (h y y y))

@[equational_result]
theorem Equation877_implies_Equation2 (G: Type _) [Magma G] (h: Equation877 G) : Equation2 G := fun x y =>
  let v0 := M y y
  let v1 := M v0 v0
  have h2 := h y v1 y
  let v3 := M x x
  let v4 := M v3 v3
  have h5 := h x v4 x
  have h6 := S h5
  have h7 := R (M (M v4 v4) v0)
  have h8 := R x
  have h9 := h x (M v3 v0) y
  have h10 := S h9
  have h11 := T h6 h9
  T (T (T (T (T (T (h x x x) (C h8 (T (h v4 x v4) (C h5 (T (C h11 h11) (C h10 h10)))))) (S (h v4 x x))) (h v4 x y)) (C h8 h7)) (C h8 (T (T h7 (C h6 (C h2 h2))) (S (h v1 x v1))))) (S (h y x y))

@[equational_result]
theorem Equation3159_implies_Equation3674 (G: Type _) [Magma G] (h: Equation3159 G) : Equation3674 G := fun x y =>
  have h0 := R x
  let v1 := M x x
  have h2 := h x x v1
  have h3 := h x v1 x
  let v4 := M y x
  have h5 := S (h y v4 y)
  have h6 := R y
  have h7 := R v4
  have h8 := S h3
  have h9 := C h2 h0
  have h10 := C (C (C (T (C (T (h v4 x x) (C (T (C (C (T h9 h8) h0) h7) (R (M v1 v4))) h7)) h7) (S (h v4 x v4))) h7) h6) h6
  have h11 := h y v4 v4
  T (T (T h9 h8) (h x y y)) (C (C (T (C (T (T (T (C (T h11 h10) h6) h5) h11) h10) h6) h5) h0) (T h3 (C (S h2) h0)))

@[equational_result]
theorem Equation522_implies_Equation4640 (G: Type _) [Magma G] (h: Equation522 G) : Equation4640 G := fun x y z =>
  let v0 := M y z
  let v1 := M v0 z
  have h2 := h v1 v1 v0
  have h3 := h v0 v1 z
  have h4 := R v1
  have h5 := h z v1 v1
  have h6 := R v0
  have h7 := C h6 (T h5 (C h4 (S h3)))
  have h8 := R z
  let v9 := M x y
  T (T (T (T (T (C (R v9) (h x v9 y)) (S (h y v9 v9))) (h y v1 z)) (C h4 (C h4 (T (C h8 (T (h v0 z z) (C h8 (T (T (T (C h8 (C h8 h7)) (S (h v1 z v0))) h2) (C h4 (C h4 (C h6 (T (C h4 h3) (S h5))))))))) (S (h v1 z v1)))))) (C h4 (C h4 h7))) (S h2)

@[equational_result]
theorem Equation1496_implies_Equation481 (G: Type _) [Magma G] (h: Equation1496 G) : Equation481 G := fun x y z =>
  let v0 := M y (M z z)
  let v1 := M x v0
  let v2 := M y v1
  let v3 := M v2 (M v1 v1)
  let v4 := M x x
  have h5 := R (M v1 v4)
  have h6 := h v0 x v2
  let v7 := M v2 v2
  have h8 := h (M x v7) v1 x
  let v9 := M x v4
  T (T (h x x v2) (C (T (T (h v4 x x) (C (T (T (h v9 v1 x) (C (T (S (h v0 x x)) h6) h5)) (S h8)) (R v9))) (S (h v7 x x))) (T (T h8 (C (T (T (S h6) (h v0 v2 v1)) (C (S (h v1 y z)) (R v3))) h5)) (S (h v3 v1 x))))) (S (h v2 v2 v1))

@[equational_result]
theorem Equation2135_implies_Equation2128 (G: Type _) [Magma G] (h: Equation2135 G) : Equation2128 G := fun x y =>
  let v0 := M y y
  let v1 := M v0 x
  let v2 := M v1 v0
  let v3 := M v2 v2
  let v4 := M v3 v2
  let v5 := M (M v0 v0) v0
  let v6 := M v0 y
  have h7 := R (M (M v1 v1) v1)
  let v8 := M x x
  have h9 := T (T (T (h (M v8 x) v1) (C h7 (S (h v0 x)))) (C h7 (T (h v0 v2) (C (R v4) (T (C (T (T (h v0 y) (C (R v6) (T (h v6 v0) (C (R v5) (S (h y y)))))) (S (h v5 y))) (R v2)) (S (h v1 v0))))))) (S (h v4 v1))
  T (T (h x x) (C h9 (T (T (h v8 x) (C h9 h9)) (S (h v3 v2))))) (S (h v2 v2))

@[equational_result]
theorem Equation909_implies_Equation1434 (G: Type _) [Magma G] (h: Equation909 G) : Equation1434 G := fun x y =>
  let v0 := M y x
  let v1 := M y v0
  have h2 := h v1 x
  let v3 := M x v1
  have h4 := h v0 y
  have h5 := R x
  let v6 := M x x
  have h7 := R v6
  have h8 := S (h x x)
  have h9 := h x v6
  have h10 := S h9
  let v11 := M v6 x
  T (T (T h9 (C h7 (T (h (M v11 v11) v6) (C h7 (C h10 h10))))) (C h7 (T (h (M v6 v6) x) (C h5 (C h8 h8))))) (C h7 (T (C h5 (T (C h5 (T (T (T (h x y) (C (R y) (C h4 h4))) (S (h (M v1 v1) y))) (C h2 h2))) (S (h (M v3 v3) x)))) (S h2)))

@[equational_result]
theorem Equation1504_implies_Equation2180 (G: Type _) [Magma G] (h: Equation1504 G) : Equation2180 G := fun x y z =>
  let v0 := M x z
  let v1 := M y z
  let v2 := M v1 y
  let v3 := M v2 v0
  have h4 := h z y v2
  have h5 := h y v1 y
  have h6 := R v1
  let v7 := M y x
  T (T (h x y y) (C (T (h v7 x x) (C (T (T (h (M x v7) v1 x) (C (T (T (S (h z y x)) h4) (C h6 (S h5))) (R (M x (M v1 x))))) (S (h y v1 x))) (T (T (h (M x (M x x)) v0 x) (C (T (T (S (h z x x)) (h z x v2)) (C (R v0) (C (R v2) (C (R x) (T (C h6 h5) (S h4)))))) (R (M x (M v0 x))))) (S (h v3 v0 x))))) (R (M y (M y y))))) (S (h v3 y y))

@[equational_result]
theorem Equation4524_implies_Equation4365 (G: Type _) [Magma G] (h: Equation4524 G) : Equation4365 G := fun x y z w =>
  let v0 := M z w
  let v1 := M y x
  have h2 := R y
  let v3 := M v1 z
  have h4 := R v1
  have h5 := h y v1 z
  have h6 := h x y z
  T (T (T (T (T (T (T (T (T (T h6 (S (h x y v3))) (C (R x) (T (T (T (T h5 (C (S h6) h4)) (h (M x (M y z)) y x)) (C (T (T (C h2 h6) (h y v1 y)) (S h5)) h2)) (S (h v3 y x))))) (h x v3 v1)) (h (M v3 x) v1 z)) (C (T (h v1 v3 x) (S (h v1 v3 y))) h4)) (S (h (M v3 y) v1 z))) (S (h y v3 v1))) (C h2 (S (h z v1 v0)))) (h y z (M v1 v0))) (S (h y z w))

@[equational_result]
theorem Equation1182_implies_Equation2 (G: Type _) [Magma G] (h: Equation1182 G) : Equation2 G := fun x y =>
  have h0 := R y
  let v1 := M y y
  have h2 := R x
  let v3 := M (M y (M y v1)) y
  let v4 := M (M x (M x y)) x
  let v5 := M (M x (M x v4)) x
  let v6 := M y x
  let v7 := M (M x (M x v6)) x
  T (T (T (T (T (T (T (T (h x x y) (C h2 (C (C h0 (h v6 y x)) h0))) (S (h v7 x y))) (h v7 x x)) (C h2 (C (T (T (T (T (T (C h2 (S (h v6 x x))) (C h2 (C (T (h y x x) (C h2 (h v4 x x))) h2))) (S (h v5 x x))) (h v5 x y)) (C h2 (C (T (C h0 (S (h v4 y x))) (S (h y y x))) h0))) (C h2 (h v1 x y))) h2))) (S (h v3 x x))) (h v3 x y)) (C h2 (C (C h0 (S (h v1 y y))) h0))) (S (h y x y))

@[equational_result]
theorem Equation3804_implies_Equation4197 (G: Type _) [Magma G] (h: Equation3804 G) : Equation4197 G := fun x y z =>
  let v0 := M z x
  let v1 := M v0 y
  let v2 := M x y
  let v3 := M v1 x
  let v4 := M x z
  have h5 := h x y x
  have h6 := h z x x
  have h7 := h v2 v0 (M x x)
  have h8 := h z y x
  T (T (T (T (h x y v1) (C (h v1 y x) (T (T (T (h x v1 v2) (C (R (M v2 v1)) (h x v2 y))) (S (h (M y v2) v1 v2))) (S (h v0 v2 y))))) (C (R (M v2 v3)) (T (T (T (T (T (C h6 h5) (S h7)) (S h8)) (h z y z)) (C (T (T h8 h7) (C (S h6) (S h5))) (h z z x))) (S (h v4 v2 v0))))) (S (h v4 v3 v2))) (S (h v1 z x))

@[equational_result]
theorem Equation4453_implies_Equation4680 (G: Type _) [Magma G] (h: Equation4453 G) : Equation4680 G := fun x y z w =>
  have h0 := h z w y
  let v1 := M w z
  let v2 := M y v1
  have h3 := h v1 z y
  have h4 := R v1
  let v5 := M y z
  have h6 := R z
  T (T (T (T (T (T (T (T (T (T (S (h y z x)) (h y z (M w v1))) (C (S (h v1 y w)) h6)) (S (h v2 z v1))) (S (h v1 (M z v2) y))) (C h4 (T (S (h v2 v1 z)) (h v2 v1 w)))) (h v1 (M w v2) y)) (h v2 w v5)) (C (T (T (T (T (S (h z v2 y)) (C h6 (T (T (S h3) (h v1 z z)) (C h0 h6)))) (h z (M v5 w) w)) (C h4 (S h0))) h3) (R w))) (S (h z w v2))) h0

@[equational_result]
theorem Equation2741_implies_Equation1865 (G: Type _) [Magma G] (h: Equation2741 G) : Equation1865 G := fun x y z =>
  let v0 := M z z
  let v1 := M y y
  let v2 := M x v1
  let v3 := M v2 v0
  have h4 := h v0 x v3
  have h5 := R v3
  let v6 := M x x
  have h7 := h v3 x v3
  let v8 := M v6 (M v3 v3)
  have h9 := h v1 x v3
  T (h x (M v2 v2) v1) (C (S (h v2 v2 v2)) (T (T (T (T (T h9 (C (T (T (h (M v6 (M v1 v3)) y v3) (C (C (R v1) (S h9)) h5)) (C (R (M v1 v1)) h7)) h5)) (S (h v8 v1 v3))) (h v8 v0 v3)) (C (T (T (C (R (M v0 v0)) (S h7)) (C (C (R v0) h4) h5)) (S (h (M v6 (M v0 v3)) z v3))) h5)) (S h4)))

@[equational_result]
theorem Equation3735_implies_Equation3738 (G: Type _) [Magma G] (h: Equation3735 G) : Equation3738 G := fun x y z w =>
  let v0 := M y w
  let v1 := M x z
  let v2 := M v1 v0
  let v3 := M x y
  have h4 := R v2
  let v5 := M y x
  have h6 := S (h y x x)
  have h7 := h x y v2
  let v8 := M x v2
  have h9 := h x y z
  T (T (T (T (T (T h9 (h v1 v5 v0)) (C h4 (T (T (T (T (T (h v5 v1 x) (C (R (M v5 x)) (T (S h9) h7))) (S (h v5 v8 x))) (h v5 v8 v3)) (C h6 (S h7))) h6))) (h v2 v5 x)) (C (R (M v2 x)) (T (T (C (h y x w) h4) (S (h v0 v1 v3))) (h v0 v1 v1)))) (S (h v2 (M v0 v1) x))) (S (h v1 v0 v0))

@[equational_result]
theorem Equation3159_implies_Equation1035 (G: Type _) [Magma G] (h: Equation3159 G) : Equation1035 G := fun x y =>
  have h0 := R x
  let v1 := M x x
  have h2 := h x x v1
  have h3 := S h2
  have h4 := h x v1 x
  have h5 := T h4 (C h3 h0)
  let v6 := M y v1
  have h7 := R y
  have h8 := R v6
  have h9 := T (C h2 h0) (S h4)
  have h10 := T (C (T (h y v6 v6) (C (C (C (T (C (T (h v6 x x) (C (T (C (C h9 h0) h8) (R (M v1 v6))) h8)) h8) (S (h v6 x v6))) h8) h7) h7)) h7) (S (h y v6 y))
  T h4 (C h3 (T (T (T (h x y y) (C (C (C h10 h7) h5) h0)) (C (C (R (M y y)) h9) h0)) (C (C h10 h5) h0)))

@[equational_result]
theorem Equation522_implies_Equation1304 (G: Type _) [Magma G] (h: Equation522 G) : Equation1304 G := fun x y z =>
  let v0 := M x z
  let v1 := M v0 z
  let v2 := M y (M v1 y)
  have h3 := S (h v1 v2 z)
  have h4 := R v1
  have h5 := h z v0 v0
  have h6 := h x v0 z
  have h7 := R v0
  have h8 := R v2
  have h9 := C h8 (C h8 (C (R z) (T (h v0 v1 x) (C h4 (T (T (C h4 (C (R x) (T (C h7 h6) (S h5)))) (C h4 (h v0 v1 z))) (S (h z v1 v1)))))))
  have h10 := h x v2 z
  T (T (T (T h10 h9) h3) (C h7 (T h5 (C h7 (T (T (T (T (S h6) h10) h9) h3) (h v1 v2 y)))))) (S (h v2 v0 v2))

@[equational_result]
theorem Equation1913_implies_Equation3973 (G: Type _) [Magma G] (h: Equation1913 G) : Equation3973 G := fun x y z =>
  let v0 := M z x
  let v1 := M y v0
  let v2 := M x y
  let v3 := M v2 v1
  let v4 := M v0 v2
  let v5 := M v1 z
  have h6 := h y z v1
  have h7 := R v5
  have h8 := R (M y v1)
  have h9 := h z y x
  have h10 := S h9
  have h11 := h x v1 y
  T (T (C (R x) (T h6 (C (T (C h9 h8) (S h11)) h7))) (C (T (h x v0 y) (C (R v4) (T (h v1 v1 v2) (C (C (R v1) h10) (R v3))))) (T (T (C (T h11 (C h10 h8)) h7) (S h6)) (h y v2 v0)))) (S (h v5 v4 v3))

@[equational_result]
theorem Equation895_implies_Equation2982 (G: Type _) [Magma G] (h: Equation895 G) : Equation2982 G := fun x y z =>
  let v0 := M z x
  let v1 := M y v0
  let v2 := M v1 z
  let v3 := M v2 y
  have h4 := S (h y v3 x)
  have h5 := R v3
  have h6 := h x v0 x
  have h7 := R x
  T (T (h x z v2) (C (R z) (C (T (T (T (C h7 (C (R v1) (T (h z x x) (C h7 (T (C (R v0) (C h6 h6)) (S (h v0 v0 (M (M x x) (M v0 x))))))))) (S (h y x v0))) (h y v3 v3)) (C h5 (T (C (T (C (R y) (T (h v3 v3 (M (M y x) (M v3 x))) (C h5 (C h4 h4)))) (S (h v2 y y))) (R (M v3 v3))) (S (h v2 v2 y))))) (R (M z v2))))) (S (h v3 z v2))

@[equational_result]
theorem Equation1506_implies_Equation72 (G: Type _) [Magma G] (h: Equation1506 G) : Equation72 G := fun x y =>
  let v0 := M x x
  let v1 := M y v0
  have h2 := R v1
  have h3 := h v0 y x
  have h4 := S h3
  have h5 := h x x x
  have h6 := S h5
  let v7 := M x v0
  have h8 := h v7 v0 x
  let v9 := M x v7
  have h10 := R (M x v9)
  have h11 := h v9 v1 x
  T (T (T (T (T h5 (C h3 (T h8 (C h6 h10)))) (S h11)) (h v9 x v1)) (C (T (C (R x) (T (T h11 (C h4 (T (C h5 h10) (S h8)))) h6)) (h v0 v0 y)) (T (C h2 h4) (C h2 (h v0 y y))))) (S (h (M y v1) (M v0 v0) v1))

@[equational_result]
theorem Equation2888_implies_Equation2685 (G: Type _) [Magma G] (h: Equation2888 G) : Equation2685 G := fun x y z =>
  let v0 := M z y
  let v1 := M x y
  let v2 := M v1 v0
  let v3 := M v2 z
  have h4 := h v3 v0 z
  have h5 := R z
  have h6 := R v0
  let v7 := M v0 z
  have h8 := R y
  have h9 := h v2 z v0
  have h10 := h v2 v2 v0
  have h11 := h x v0 z
  T (T h11 (C (T (T (T (C (T (T (T (T (h (M x v7) z y) (C (S h11) h8)) (h v1 z y)) (C (C h10 h5) h8)) (S (h (M (M v2 (M v2 v0)) v2) z y))) h6) (S h10)) h9) (C (T (T (T (h (M (M v2 (M z v0)) z) z y) (C (C (S h9) h5) h8)) (C h4 h8)) (S (h (M v3 v7) z y))) h6)) h5)) (S h4)

@[equational_result]
theorem Equation3940_implies_Equation3334 (G: Type _) [Magma G] (h: Equation3940 G) : Equation3334 G := fun x y z =>
  let v0 := M z y
  let v1 := M z v0
  have h2 := R z
  let v3 := M z v1
  let v4 := M v1 v0
  let v5 := M v1 v1
  have h6 := h v1 v0 z
  T (T (T (T (T (T (h x y z) (C (h x v0 v1) h2)) (S (h (M x v4) v0 z))) (C (C (R x) (T (T h6 (h v5 z v3)) (C (T (T (C (T (T (T (C (C h2 (h z y z)) (R v1)) (S (h z z v1))) (h z z v5)) (C (C h2 (S h6)) (R v5))) (S (h z v0 z))) (S (h (M z v4) v1 v1))) (S (h z v0 v1))) (R v3)))) (R v0))) (h (M x (M v1 v3)) v0 z)) (C (S (h x v3 v1)) h2)) (S (h x v1 z))

@[equational_result]
theorem Equation3603_implies_Equation41 (G: Type _) [Magma G] (h: Equation3603 G) : Equation41 G := fun x y z =>
  let v0 := M (M z z) y
  have h1 := h y z v0
  let v2 := M y z
  have h3 := R v2
  let v4 := M x x
  let v5 := M v0 v0
  have h6 := R v5
  have h7 := h x x v4
  let v8 := M v4 x
  have h9 := R v4
  T (T (T (T (T (T (T (T (T (T (T h7 (C h9 (h v4 x v4))) (S (h (M v4 v4) x v4))) (C (T (T (T (C h9 h7) (S (h v8 x v4))) (h v8 x v5)) (C h6 (S h7))) (R x))) (h (M v5 v4) x v5)) (C h6 (S (h v4 v0 v4)))) (S (h v0 x v5))) (h v0 x v2)) (C h3 (S (h y z v4)))) (C h3 (T (h y z v2) (C h1 (R v0))))) (S (h v0 v0 v2))) (S h1)

@[equational_result]
theorem Equation895_implies_Equation2146 (G: Type _) [Magma G] (h: Equation895 G) : Equation2146 G := fun x y z =>
  let v0 := M y y
  let v1 := M (M v0 z) (M x z)
  let v2 := M v1 x
  let v3 := M y x
  have h4 := h y v1 x
  have h5 := R v1
  have h6 := h v1 v0 x
  have h7 := h x x (M v3 (M x x))
  have h8 := h y x x
  have h9 := R x
  have h10 := S h8
  T (T (T (T (T h7 (C h9 (C h10 h10))) (h (M x v0) v1 v1)) (C h5 (T (T (C (C (T (C h9 (C h8 h8)) (S h7)) h5) (R (M v1 v1))) (C (S (h v0 x z)) (C h6 h6))) (S (h v0 v0 (M v2 (M v0 x))))))) (C h5 (C h4 h4))) (S (h v1 v1 (M v3 v2)))

@[equational_result]
theorem Equation1571_implies_Equation1673 (G: Type _) [Magma G] (h: Equation1571 G) : Equation1673 G := fun x y z =>
  let v0 := M z z
  let v1 := M v0 y
  let v2 := M x y
  let v3 := M v2 v1
  have h4 := h z v2 v1
  have h5 := R v3
  let v6 := M v3 z
  have h7 := h x v3 z
  have h8 := h x v2 v1
  have h9 := h v0 x y
  let v10 := M v3 (M z v0)
  have h11 := T (C (T h8 (C h5 (S h9))) (R v10)) (S (h z v3 v0))
  T (T (T (h x x v10) (C h11 (T (T (C (R x) h11) (C h7 (T (h z v3 z) (C (R v6) (T (T (C h5 h9) (S h8)) h7))))) (S (h v6 v6 (M v3 (M x z))))))) (C h4 (C h5 h4))) (S (h v3 v3 (M v2 (M z v1))))

@[equational_result]
theorem Equation2105_implies_Equation4106 (G: Type _) [Magma G] (h: Equation2105 G) : Equation4106 G := fun x y z =>
  let v0 := M x x
  let v1 := M (M y z) y
  let v2 := M z z
  have h3 := R v2
  have h4 := R v0
  have h5 := h v0 x x
  have h6 := R x
  have h7 := h x x x
  have h8 := S h7
  have h9 := h x v0 x
  let v10 := M v1 v1
  T (T (T (T h5 (C (C (T (C h7 h4) (S h9)) h6) h4)) (C (C (T (h x v0 z) (C h8 h3)) h6) h4)) (S (h v2 x x))) (C (T (T (h z y z) (C (T (h v1 v1 x) (C (C (T (T (T (h v10 x x) (C (C (T (C h7 (R v10)) (S (h x v0 v1))) h6) h4)) (C (C (T h9 (C h8 h4)) h6) h4)) (S h5)) (R v1)) h4)) h3)) (S (h v1 v0 z))) (R z))

@[equational_result]
theorem Equation2113_implies_Equation3959 (G: Type _) [Magma G] (h: Equation2113 G) : Equation3959 G := fun x y z =>
  let v0 := M x z
  let v1 := M y v0
  let v2 := M v1 z
  have h3 := h v0 v1 z
  have h4 := S (h v0 x y)
  have h5 := S (h v2 y z)
  let v6 := M y z
  let v7 := M x y
  have h8 := S (h z v0 v7)
  let v9 := M v0 v7
  T (T (T (h v7 (M (M x v0) y) v7) (C (T (T (T (T (C h4 (R v7)) (h v9 (M (M v0 z) v7) v9)) (C (T (C (T h8 (h z x y)) (R v9)) (S (h y v0 v7))) h8)) (h v6 (M (M y v2) z) v6)) (C (T (C h5 (R v6)) (S (h v0 y z))) h5)) h4)) (C (C h3 (R v2)) h3)) (S (h v2 (M (M v1 v0) z) v2))

@[equational_result]
theorem Equation1059_implies_Equation378 (G: Type _) [Magma G] (h: Equation1059 G) : Equation378 G := fun x y =>
  let v0 := M (M x (M y x)) y
  let v1 := M x y
  have h2 := h y y (M x (M v1 x))
  have h3 := R y
  have h4 := h y x v1
  have h5 := T (C h3 (C h4 h3)) (S h2)
  have h6 := h x y v1
  have h7 := R x
  have h8 := h v1 y y
  have h9 := R v1
  have h10 := h y v1 y
  T (T (C (T h6 (C h7 (C (T (C h3 (C (T h8 (C h9 (C h5 h9))) h3)) (S h10)) h7))) h3) (h v0 y y)) (C (C (T (C h7 (C (T h10 (C h3 (C (T (C h9 (C (T h2 (C h3 (C (S h4) h3))) h9)) (S h8)) h3))) h7)) (S h6)) h3) (T (C h5 (R v0)) (S (h y x y))))

@[equational_result]
theorem Equation949_implies_Equation962 (G: Type _) [Magma G] (h: Equation949 G) : Equation962 G := fun x y z =>
  let v0 := M x z
  let v1 := M z y
  let v2 := M v1 v0
  let v3 := M y v2
  have h4 := h v3 v0 v2
  have h5 := h z v1 v2
  have h6 := h z z x
  have h7 := R v0
  have h8 := h x v0 y
  T (T h8 (C h7 (T (T (T (T (T (h (M (M y x) (M v0 y)) z v0) (C (R z) (T (C (S h8) (C h6 h7)) (S (h (M v0 (M z x)) x z))))) (S h6)) h5) (C (R v1) (T (T (h (M (M v2 z) (M v1 v2)) v3 v1) (C (R v3) (T (C (S h5) (R (M v3 v1))) (S (h v2 z y))))) (C h4 (R v2))))) (S (h (M (M v2 v3) (M v0 v2)) v1 v0))))) (S h4)

@[equational_result]
theorem Equation1537_implies_Equation1061 (G: Type _) [Magma G] (h: Equation1537 G) : Equation1061 G := fun x y z =>
  let v0 := M z y
  let v1 := M y v0
  let v2 := M x (M v1 z)
  let v3 := M v2 v2
  have h4 := h z v1 y
  let v5 := M v1 v1
  have h6 := S (h v5 x v1)
  have h7 := R v1
  have h8 := C h7 h4
  let v9 := M x x
  have h10 := R v9
  T (T (h x v0 x) (C (R (M v0 v0)) (T (C (R x) (T (T (T (h v9 x v1) (C h10 (T (C h7 (S (h z x y))) h8))) h6) (C h7 (T (T (h v1 v1 v3) (C (R v5) (T (C (R v3) (C h7 (T (T (h v3 x v1) (C h10 (T (C h7 (S (h z v2 y))) h8))) h6))) (S (h v1 v2 v1))))) (S h4))))) (h v2 v2 v2)))) (S (h v2 v0 v3))

@[equational_result]
theorem Equation1577_implies_Equation3943 (G: Type _) [Magma G] (h: Equation1577 G) : Equation3943 G := fun x y z =>
  let v0 := M z z
  let v1 := M x v0
  let v2 := M v1 y
  let v3 := M v1 v2
  let v4 := M v0 v3
  have h5 := h v1 x v0
  let v6 := M x z
  let v7 := M v0 v1
  have h8 := h z x z
  have h9 := R v1
  have h10 := h y z z
  T (T (h (M x y) v0 v1) (C (R v7) (T (T (T (T (C (R v0) (T (C h9 (C (R x) h10)) (S (h (M z (M z y)) x v0)))) (S h10)) (h y v1 v1)) (C (R (M v1 v1)) (T (h v3 v1 v0) (C (T (C h9 (T (C h8 (T h8 (C (R v6) h5))) (S (h (M x v7) v6 v1)))) (S h5)) (R (M v1 v4)))))) (S (h v4 v1 v1))))) (S (h v2 v0 v1))

@[equational_result]
theorem Equation4122_implies_Equation4153 (G: Type _) [Magma G] (h: Equation4122 G) : Equation4153 G := fun x y z w u =>
  let v0 := M x z
  let v1 := M (M v0 w) u
  let v2 := M x x
  let v3 := M v2 v2
  have h4 := R v1
  have h5 := T (S (h x v2 y)) (h x v2 z)
  have h6 := T (T (T (T (h v2 y v1) (h (M v3 y) v1 v1)) (C (C (C h5 h5) h4) h4)) (S (h (M v3 z) v1 v1))) (S (h v2 z v1))
  let v7 := M v2 y
  let v8 := M v7 v7
  T (T (h x y v1) (h v7 v1 u)) (C (T (h v8 v1 w) (C (T (T (T (C (C (R v8) (T (C h6 h6) (S (h x z (M v2 z))))) h4) (S (h v7 v0 v1))) (C h6 (R v0))) (S (h x z v0))) (R w))) (R u))

@[equational_result]
theorem Equation880_implies_Equation219 (G: Type _) [Magma G] (h: Equation880 G) : Equation219 G := fun x y =>
  let v0 := M x y
  let v1 := M v0 v0
  have h2 := h y v1
  have h3 := h x y
  have h4 := R v1
  let v5 := M x x
  have h6 := R v5
  have h7 := S h3
  have h8 := C (T h2 (C h4 (C h7 h7))) h6
  let v9 := M y v5
  let v10 := M x v9
  let v11 := M v10 v10
  have h12 := S (h v9 v11)
  have h13 := h x v9
  have h14 := C (R v11) (C h13 h13)
  T h13 (C (R v9) (T (T (T (T (h v11 v5) (C h6 (T (C (R (M v11 v5)) (T h14 h12)) (C (T (T h14 h12) h8) h8)))) (S (h (M v1 v5) v5))) (C h4 (C h3 h3))) (S h2)))

@[equational_result]
theorem Equation696_implies_Equation2 (G: Type _) [Magma G] (h: Equation696 G) : Equation2 G := fun x y =>
  let v0 := M (M y y) y
  have h1 := h v0 x y
  have h2 := h (M v0 v0) x y
  have h3 := R x
  have h4 := h x x v0
  let v5 := M x x
  let v6 := M v5 x
  have h7 := h x x v6
  have h8 := S h7
  have h9 := h (M v6 v6) x x
  have h10 := C h3 h9
  have h11 := h v6 x x
  have h12 := T (T h11 h10) h8
  have h13 := R y
  T (T (T (T (T h7 (C h3 (S h9))) (S h11)) (h v6 y y)) (C h13 (T (T (C h12 (T (T h1 (C h3 h2)) (S h4))) (h v5 y x)) (C h13 (T (T (T (T (T (T (C (R v5) h12) h11) h10) h8) h4) (C h3 (S h2))) (S h1)))))) (S (h y y y))

@[equational_result]
theorem Equation1496_implies_Equation2146 (G: Type _) [Magma G] (h: Equation1496 G) : Equation2146 G := fun x y z =>
  let v0 := M y y
  let v1 := M v0 z
  let v2 := M x z
  let v3 := M v1 v2
  let v4 := M v3 (M v1 v1)
  let v5 := M x x
  have h6 := R (M v2 v5)
  have h7 := h z x v3
  let v8 := M v3 v3
  have h9 := h (M x v8) v2 x
  let v10 := M x v5
  T (T (h x x v3) (C (T (T (h v5 x x) (C (T (T (T (h v10 v2 x) (C (S (h z x x)) h6)) (C h7 h6)) (S h9)) (R v10))) (S (h v8 x x))) (T (T h9 (C (T (T (S h7) (h z v3 v1)) (C (T (C (R v3) (h z v0 y)) (S (h v2 v1 v0))) (R v4))) h6)) (S (h v4 v2 x))))) (S (h v3 v3 v1))

@[equational_result]
theorem Equation2707_implies_Equation115 (G: Type _) [Magma G] (h: Equation2707 G) : Equation115 G := fun x y =>
  let v0 := M x x
  let v1 := M v0 y
  let v2 := M y x
  let v3 := M v2 v2
  have h4 := h y v3
  have h5 := R v3
  have h6 := h x y
  have h7 := R v0
  have h8 := S h6
  have h9 := C h7 (T h4 (C (C h8 h8) h5))
  let v10 := M v1 x
  let v11 := M v10 v10
  have h12 := S (h v1 v11)
  have h13 := h x v1
  have h14 := C (C h13 h13) (R v11)
  T h13 (C (T (T (T (T (h v11 v0) (C (T (C (T h14 h12) (R (M v0 v11))) (C h9 (T (T h14 h12) h9))) h7)) (S (h (M v0 v3) v0))) (C (C h6 h6) h5)) (S h4)) (R v1))

@[equational_result]
theorem Equation627_implies_Equation152 (G: Type _) [Magma G] (h: Equation627 G) : Equation152 G := fun x y =>
  let v0 := M x y
  let v1 := M x x
  let v2 := M v1 v0
  have h3 := S (h v0 x x)
  let v4 := M v1 x
  let v5 := M v0 v4
  have h6 := R v1
  have h7 := C h6 (C h6 (T (C h3 (R v5)) h3))
  have h8 := h v1 v0 v5
  let v9 := M x v4
  have h10 := h x x x
  have h11 := R x
  have h12 := S (h y x x)
  let v13 := M y v4
  T (T (h x y v13) (C h11 (C h11 (T (C h12 (R v13)) h12)))) (C (T (h x x v1) (C h11 (T (C h11 (C (T (C h11 (C h11 (T h10 (C h10 (R v9))))) (S (h x x v9))) (T (T h8 h7) (C (T h8 h7) (R v2))))) (S (h x v1 v2))))) (R v0))

@[equational_result]
theorem Equation2948_implies_Equation2 (G: Type _) [Magma G] (h: Equation2948 G) : Equation2 G := fun x y =>
  have h0 := R y
  let v1 := M y (M y y)
  have h2 := h v1 y x
  have h3 := R x
  have h4 := h (M v1 v1) y x
  have h5 := h x v1 x
  let v6 := M x x
  let v7 := M x v6
  have h8 := h x v7 x
  have h9 := S h8
  have h10 := h (M v7 v7) x x
  have h11 := C h10 h3
  have h12 := h v7 x x
  have h13 := T (T h12 h11) h9
  T (T (T (T (T h8 (C (S h10) h3)) (S h12)) (h v7 y y)) (C (T (T (C (T (T h2 (C h4 h3)) (S h5)) h13) (h v6 x y)) (C (T (T (T (T (T (T (C h13 (R v6)) h12) h11) h9) h5) (C (S h4) h3)) (S h2)) h0)) h0)) (S (h y y y))

@[equational_result]
theorem Equation4176_implies_Equation3940 (G: Type _) [Magma G] (h: Equation4176 G) : Equation3940 G := fun x y z =>
  let v0 := M z y
  let v1 := M x v0
  have h2 := R y
  let v3 := M v1 z
  have h4 := R z
  let v5 := M x y
  have h6 := R x
  let v7 := M y v0
  T (T (h x y y) (C (T (T (T (T (T (T (T (C (T (T (h y y v1) (C (T (T (T (C (h y v1 z) h2) (S (h z v3 y))) (h z v3 z)) (C (S (h z v1 z)) h4)) (R v1))) (S (h z z v1))) h6) (C (T (h z z y) (C (T (T (T (C (h z y v0) h4) (S (h v0 v7 z))) (h v0 v7 x)) (C (S (h x y v0)) h6)) h2)) h6)) (S (h y v5 x))) (h y v5 z)) (C (S (h z x y)) h4)) (C (h z x v0) h4)) (R (M (M v3 v0) z))) (S (h v0 v1 z))) h2)) (S (h v1 z y))

@[equational_result]
theorem Equation3298_implies_Equation3303 (G: Type _) [Magma G] (h: Equation3298 G) : Equation3303 G := fun x y z w =>
  have h0 := h w x x
  have h1 := S h0
  let v2 := M x x
  have h3 := C (R x) (R (M x v2))
  let v4 := M w w
  have h5 := h v4 x x
  have h6 := h x x x
  have h7 := T h6 h1
  have h8 := C h7 h7
  have h9 := S h6
  have h10 := R v2
  let v11 := M z v4
  have h12 := T h0 h9
  have h13 := C h12 h12
  have h14 := S h5
  T (h x y v11) (C (R y) (T (T (T (C (R v11) (T (T (T (h v11 x x) h14) h13) (C h10 (T (T (T h6 h3) h14) h13)))) (S (h w v11 v2))) (h w z v2)) (C (R z) (T (T (T (T (C h10 (T (T (T h8 h5) h3) h9)) h8) h5) h3) h1))))

@[equational_result]
theorem Equation4009_implies_Equation41 (G: Type _) [Magma G] (h: Equation4009 G) : Equation41 G := fun x y z =>
  let v0 := M x x
  let v1 := M z z
  let v2 := M x v1
  let v3 := M y z
  let v4 := M y y
  have h5 := R x
  have h6 := R z
  let v7 := M v0 v0
  let v8 := M x (M v1 v1)
  let v9 := M z v7
  T (T (T (T (T (T (T (h x x z) (C (T (T (T (h z v0 x) (C (C h5 (T (h v0 v0 z) (h v9 v0 z))) h6)) (S (h z v9 x))) (C h6 (T (T (h z v7 v8) (C (T (C (R v8) (T (S (h v7 x v0)) (S (h x x v0)))) (S (h v0 v1 x))) h6)) (S (h z z v0))))) h5)) (S (h x z z))) (h x z x)) (h v2 x (M v3 (M v4 v4)))) (C (S (h v0 v4 v3)) (R v2))) (S (h v2 y v0))) (S (h y z x))

@[equational_result]
theorem Equation3973_implies_Equation4307 (G: Type _) [Magma G] (h: Equation3973 G) : Equation4307 G := fun x y z =>
  let v0 := M x y
  let v1 := M z y
  have h2 := h z v1 v0
  let v3 := M v1 (M v0 z)
  have h4 := R y
  let v5 := M z v1
  let v6 := M v0 (M v5 x)
  have h7 := R v1
  let v8 := M x v0
  let v9 := M y (M v8 z)
  let v10 := M v0 (M v1 x)
  have h11 := h x v0 v1
  T (T (T (T (T (T (T (T h11 (h v10 v1 v1)) (C (C h7 (T (C (T (h z y v8) (C (R v9) h11)) (R v10)) (S (h v1 v9 v10)))) h7)) (S (h v9 v1 v1))) (C (C h4 (T (C (h x v0 v5) (R z)) (S (h v1 v6 z)))) h7)) (S (h v6 y v1))) (C (C (R v0) (T (C h2 (R x)) (S (h y v3 x)))) h4)) (S (h v3 v0 y))) (S h2)

@[equational_result]
theorem Equation505_implies_Equation2 (G: Type _) [Magma G] (h: Equation505 G) : Equation2 G := fun x y =>
  let v0 := M y x
  let v1 := M x v0
  have h2 := h y y (M y v1)
  have h3 := S h2
  have h4 := h y y v1
  have h5 := R y
  let v6 := M x x
  have h7 := R v6
  have h8 := h x y x
  have h9 := C h5 (C h5 h8)
  have h10 := C h5 (C h5 (S h8))
  have h11 := R x
  T (T (T (T (h x x (M v0 v6)) (C h11 (C h11 (T (T (T (S (h v0 x x)) (C (T h4 h10) (T (h x x v6) (C h11 (S (h x x x)))))) (C (T (T (T h9 (S h4)) h2) (C h5 h10)) h7)) (C (T (T (T (C h5 h9) h3) (h y y v0)) (C h5 (S (h y y x)))) h7))))) (S (h (M y y) x x))) (C h5 h4)) h3

@[equational_result]
theorem Equation1537_implies_Equation1902 (G: Type _) [Magma G] (h: Equation1537 G) : Equation1902 G := fun x y z =>
  let v0 := M z z
  let v1 := M x y
  let v2 := M y v1
  let v3 := M v2 v0
  have h4 := S (h v0 x v2)
  have h5 := h x z y
  have h6 := R v2
  have h7 := R (M x x)
  have h8 := R v3
  let v9 := M v2 v2
  have h10 := C h6 (T (T (h v9 x v2) (C h7 (C h6 (T (S (h x v2 y)) h5)))) h4)
  have h11 := R v0
  T (T (T (T (T h5 (C h11 (T (h v2 z v2) (C h11 h10)))) (S (h v2 z v0))) (h v2 v1 v2)) (C (R (M v1 v1)) (T (h (M v2 v9) z v3) (C h11 (C h8 (T (T (T (C h10 h8) (h (M v3 v3) x v2)) (C h7 (C h6 (T (S (h x v3 y)) h5)))) h4)))))) (S (h v3 v1 v0))

@[equational_result]
theorem Equation2315_implies_Equation2 (G: Type _) [Magma G] (h: Equation2315 G) : Equation2 G := fun x y =>
  let v0 := M x (M y x)
  let v1 := M x v0
  have h2 := R x
  have h3 := h x x y
  have h4 := R y
  have h5 := h v0 y x
  let v6 := M x x
  let v7 := M x (M y v6)
  let v8 := M y (M v0 (M x y))
  have h9 := h y x x
  let v10 := M x v6
  have h11 := h v10 y y
  let v12 := M y (M v10 (M y y))
  T (T (h x x v1) (C (T (T (T (T (T (C h2 (C h2 (S h3))) h11) (C (T (T (h v12 x v7) (C (C h2 (T (C (R v12) (S h9)) (S h11))) h2)) (S (h x x x))) h4)) (C (T (T h3 (C (C h2 (T h5 (C (R v8) h9))) h2)) (S (h v8 x v7))) h4)) (S h5)) (C h2 (C h4 h3))) h2)) (S (h y x v1))

@[equational_result]
theorem Equation2741_implies_Equation4109 (G: Type _) [Magma G] (h: Equation2741 G) : Equation4109 G := fun x y z =>
  have h0 := R z
  let v1 := M y z
  let v2 := M v1 z
  let v3 := M x x
  have h4 := R v3
  let v5 := M v2 v2
  let v6 := M y y
  let v7 := M v3 v3
  have h8 := h v3 v2 v3
  T (T (T h8 (C (T (T (T (h (M v5 v7) x v3) (C (T (C h4 (S h8)) (C h4 (h v3 x v3))) h4)) (S (h (M v3 v7) x v3))) (C h4 (T (T (h v7 x x) (C (T (C h4 (S (h x x x))) (C h4 (h x y x))) (R x))) (S (h (M v6 v3) x x))))) h4)) (S (h v6 x v3))) (C (T (h y x z) (C (T (T (T (C h4 (T (h v1 v5 z) (C (S (h v2 v2 v2)) h0))) (h (M v3 (M v2 z)) x z)) (C (C h4 (S (h v2 x z))) h0)) (S (h v1 x z))) h0)) (R y))

@[equational_result]
theorem Equation2725_implies_Equation4098 (G: Type _) [Magma G] (h: Equation2725 G) : Equation4098 G := fun x y z =>
  have h0 := R z
  let v1 := M y y
  let v2 := M v1 z
  let v3 := M v2 z
  have h4 := R v2
  let v5 := M x x
  have h6 := h z v5 z
  have h7 := R v5
  let v8 := M z z
  have h9 := R v8
  have h10 := h v5 v2 y
  have h11 := h z v1 x
  have h12 := h z v1 y
  have h13 := h v1 v2 y
  have h14 := h v8 v2 x
  have h15 := C (S h11) h4
  T (T (T (T h10 h15) (C (T h6 (C (C (C (T (T (T h10 h15) (C h12 h4)) (S h13)) h0) h9) h7)) h4)) (S h14)) (C (T (T (h z z v3) (C (C (T h14 (C (T (C (C (C (T (T (T h13 (C (S h12) h4)) (C h11 h4)) (S h10)) h0) h9) h7) (S h6)) h4)) (R (M v3 v3))) h0)) (S (h v2 z v3))) h0)

@[equational_result]
theorem Equation3186_implies_Equation2 (G: Type _) [Magma G] (h: Equation3186 G) : Equation2 G := fun x y =>
  let v0 := M x y
  have h1 := h y v0 y
  have h2 := R y
  have h3 := h y x y
  have h4 := R x
  let v5 := M v0 x
  have h6 := h y (M v5 y) y
  have h7 := h x x y
  have h8 := C (C h7 h2) h2
  let v9 := M x x
  have h10 := R v9
  have h11 := C (C (S h7) h2) h2
  have h12 := h y v5 y
  T (T (T (T (h x (M v9 v0) x) (C (C (T (T (T (S (h v0 x x)) (C (T (h x v9 x) (C (S (h x x x)) h4)) (T h12 h11))) (C h10 (T (T (T h8 (S h12)) h6) (C h11 h2)))) (C h10 (T (T (T (C h8 h2) (S h6)) h1) (C (S h3) h2)))) h4) h4)) (S (h (M y y) x x))) (C h3 h2)) (S h1)

@[equational_result]
theorem Equation2741_implies_Equation3489 (G: Type _) [Magma G] (h: Equation2741 G) : Equation3489 G := fun x y z =>
  let v0 := M y z
  let v1 := M v0 z
  have h2 := R v1
  let v3 := M x x
  have h4 := R v3
  let v5 := M y y
  have h6 := h v1 x v1
  let v7 := M v3 (M v1 v1)
  have h8 := S (h x x x)
  let v9 := M v3 v3
  let v10 := M y v1
  have h11 := h v3 v10 v1
  T (T (T (T h11 (C (T (T (h (M (M v10 v10) (M v3 v1)) x v1) (C (T (T (C h4 (S h11)) (h v9 v3 x)) (C (T (C (R v9) h8) h8) (R x))) h2)) (C h4 h6)) h2)) (S (h v7 x v1))) (h v7 y v1)) (C (T (T (T (C (R v5) (S h6)) (h (M v5 v1) x z)) (C (C h4 (S (h v0 y z))) (R z))) (S (h y x z))) h2)

@[equational_result]
theorem Equation3193_implies_Equation619 (G: Type _) [Magma G] (h: Equation3193 G) : Equation619 G := fun x y =>
  have h0 := R x
  have h1 := S (h y y x)
  have h2 := R y
  let v3 := M y x
  have h4 := S (h v3 v3 y)
  have h5 := R v3
  have h6 := h v3 y x
  have h7 := C (C (T (C (T (T (C h6 h5) h4) h6) h5) h4) h2) h2
  have h8 := h y v3 v3
  let v9 := M v3 x
  let v10 := M x v9
  have h11 := R v10
  have h12 := C (S (h v10 x v9)) h11
  have h13 := h v10 v10 x
  have h14 := T (C (C (T (T h13 h12) (C (T h13 h12) h11)) h0) h0) (S (h x v10 v10))
  have h15 := h x x v9
  T h15 (C h14 (T h15 (C h14 (T (h x y y) (C (C (T (C (T (T (T (C (T h8 h7) h2) h1) h8) h7) h2) h1) h0) h0)))))

@[equational_result]
theorem Equation3754_implies_Equation41 (G: Type _) [Magma G] (h: Equation3754 G) : Equation41 G := fun x y z =>
  let v0 := M x x
  let v1 := M x y
  let v2 := M z y
  have h3 := h x x v0
  let v4 := M v0 x
  have h5 := h x x x
  have h6 := h x x y
  have h7 := S h6
  have h8 := h y x z
  have h9 := S h8
  have h10 := R v0
  have h11 := C h10 h9
  have h12 := h (M v1 v2) v0 v0
  have h13 := h x y x
  have h14 := T h6 (C h10 h8)
  T (T (T (T (T (T (T (T h5 (C h14 h14)) (S h12)) (C h9 h10)) (S h13)) (h x y y)) (C h8 (T h8 (C (T (T (T (T (T h13 (C h8 h10)) h12) (C (T (T (T (T h11 h7) h5) (C h3 h3)) (S (h v4 v0 v0))) (T (T h11 h7) h5))) (S (h v0 v4 v0))) (S h3)) (R v2))))) (S (h v2 v1 v0))) (S (h y z x))

@[equational_result]
theorem Equation3364_implies_Equation4216 (G: Type _) [Magma G] (h: Equation3364 G) : Equation4216 G := fun x y z =>
  have h0 := R x
  let v1 := M z y
  let v2 := M y v1
  let v3 := M x (M v1 x)
  let v4 := M z v1
  let v5 := M v1 z
  let v6 := M v5 (M x v5)
  let v7 := M v5 z
  have h8 := h z v7 v5
  let v9 := M v5 (M z v5)
  T (T (T (T (T (T (T (h x y v5) (h y v6 v1)) (C (R v6) (T (T (T (T (T (S (h z v1 y)) (h z v1 v5)) (h v1 v9 v5)) (C (R v9) (T (h v5 (M v1 v5) z) (C (h v1 v5 z) h8)))) (S (h v7 v9 v9))) (S h8)))) (S (h v5 v6 z))) (S (h x v5 v5))) (C h0 (T (T (h v1 z x) (h z v3 v1)) (C (R v3) (h v1 v4 x))))) (S (h v4 x v3))) (C (T (C (R z) (T (h z y y) (h y v2 v1))) (S (h v1 z v2))) h0)

@[equational_result]
theorem Equation3959_implies_Equation3588 (G: Type _) [Magma G] (h: Equation3959 G) : Equation3588 G := fun x y z =>
  let v0 := M x y
  let v1 := M v0 z
  have h2 := h z v1 x
  let v3 := M v1 (M z x)
  have h4 := h v3 x v0
  have h5 := R v0
  let v6 := M z v1
  have h7 := h v0 v0 z
  have h8 := R z
  have h9 := h v0 z z
  have h10 := R v6
  have h11 := h x y v0
  T (T (T (T (T h11 (h (M y (M x v0)) v0 v0)) (C (T (T (T (T (T (T (T (C h5 (S h11)) h7) (C (T (T (T (h v0 v1 z) (C (C (R v1) h9) h8)) (S (h v6 v1 z))) (C h10 h9)) h8)) (S (h v6 v6 z))) (h v6 v6 v0)) (C (C h10 (T (T (h v6 v0 z) (C (C h5 (S h9)) h8)) (S h7))) h5)) (S (h v0 v6 v0))) (C h5 (T h2 h4))) h5)) (S (h (M x (M v3 v0)) v0 v0))) (S h4)) (S h2)

@[equational_result]
theorem Equation522_implies_Equation4450 (G: Type _) [Magma G] (h: Equation522 G) : Equation4450 G := fun x y z =>
  let v0 := M y z
  let v1 := M v0 z
  have h2 := h v1 v1 v0
  have h3 := h v0 v1 z
  have h4 := R v1
  have h5 := h z v1 v1
  have h6 := R v0
  have h7 := C h6 (T h5 (C h4 (S h3)))
  have h8 := R z
  let v9 := M y x
  let v10 := M x v9
  have h11 := R x
  T (T (T (T (T (T (h v10 x x) (C h11 (C h11 (C h11 (T (C (R v10) (h x v10 v9)) (S (h v9 v10 v10))))))) (S (h y x x))) (h y v1 z)) (C h4 (C h4 (T (C h8 (T (h v0 z z) (C h8 (T (T (T (C h8 (C h8 h7)) (S (h v1 z v0))) h2) (C h4 (C h4 (C h6 (T (C h4 h3) (S h5))))))))) (S (h v1 z v1)))))) (C h4 (C h4 h7))) (S h2)

@[equational_result]
theorem Equation1908_implies_Equation19 (G: Type _) [Magma G] (h: Equation1908 G) : Equation19 G := fun x y z =>
  let v0 := M z x
  let v1 := M y v0
  let v2 := M x (M v1 z)
  let v3 := M v2 x
  let v4 := M z v1
  have h5 := R y
  let v6 := M y (M v0 x)
  let v7 := M v6 y
  have h8 := R z
  let v9 := M x (M x y)
  let v10 := M v9 x
  T (T (T (h x z v10) (C (C h8 (T (C (h x x y) (R v10)) (S (h x v9 x)))) (R v0))) (C (C h8 (T (h x v2 v1) (C (S (h v1 x z)) (R v3)))) (T (T (T (h v0 y v7) (C (C h5 (T (C (h v0 y x) (R v7)) (S (h y v6 v0)))) (R v1))) (C (C h5 (h y z v0)) (T (h v1 z y) (C (T (C (h z y x) (R (M v1 y))) (S (h y v1 z))) (R v4))))) (S (h v4 y (M z y)))))) (S (h v1 z v3))

@[equational_result]
theorem Equation2741_implies_Equation4612 (G: Type _) [Magma G] (h: Equation2741 G) : Equation4612 G := fun x y z =>
  let v0 := M y z
  let v1 := M v0 z
  have h2 := h v1 y y
  have h3 := R y
  let v4 := M y y
  let v5 := M x x
  have h6 := R v5
  let v7 := M v5 v5
  have h8 := S (h v7 v5 x)
  have h9 := R x
  have h10 := h x x x
  have h11 := C (T h10 (C (R v7) h10)) h9
  T (C (T (T (T (T (T h11 h8) (C (T (T h11 h8) (C h6 (T (T (T (T h11 h8) (h v7 x x)) (C (T (C h6 (S h10)) (C h6 (h x y x))) h9)) (S (h (M v4 v5) x x))))) h6)) (S (h v4 x v5))) (C (T (T (T (h y x z) (C (C (T h11 h8) (h v0 x z)) (R z))) (S (h (M v5 v1) v5 z))) (C h6 h2)) h3)) (S (h (M v4 (M v1 y)) x y))) h3) (S h2)

@[equational_result]
theorem Equation627_implies_Equation4395 (G: Type _) [Magma G] (h: Equation627 G) : Equation4395 G := fun x y =>
  have h0 := R x
  let v1 := M x x
  let v2 := M v1 x
  let v3 := M y v2
  have h4 := S (h x y v3)
  have h5 := h y x x
  have h6 := C h0 (C h0 (T h5 (C h5 (R v3))))
  let v7 := M x y
  have h8 := S (h v7 x v2)
  let v9 := M v7 (M (M x v2) v2)
  let v10 := M x v7
  have h11 := S (h v7 v1 v10)
  let v12 := M v7 (M (M v1 v10) v10)
  let v13 := M y (M (M v2 y) y)
  have h14 := h y v2 y
  T (T (T (T (C h0 (C h0 (T h14 (C h14 (R v13))))) (S (h x y v13))) (h x v7 v12)) (C h0 (T (T (C h0 (T (C h11 (R v12)) h11)) h6) h4))) (C (T (h x v7 v9) (C h0 (T (T (C h0 (T (C h8 (R v9)) h8)) h6) h4))) h0)

@[equational_result]
theorem Equation3126_implies_Equation5 (G: Type _) [Magma G] (h: Equation3126 G) : Equation5 G := fun x y =>
  have h0 := R x
  let v1 := M y x
  let v2 := M v1 v1
  have h3 := h y v2 x
  have h4 := R y
  have h5 := R v2
  have h6 := h x y v1
  let v7 := M v1 y
  have h8 := h y v7 x
  have h9 := R v7
  have h10 := h x y y
  let v11 := M v1 x
  have h12 := h y v11 x
  have h13 := R v11
  have h14 := h x y x
  let v15 := M (M (M x y) v1) x
  T (T (T (T (h x y v15) (C (T (T (T (C (C (C (h y x v1) h0) (R v15)) h4) (S (h y v15 x))) h12) (C (C (S h14) h13) h4)) h0)) (C (T (T (T (C (C h14 h13) h4) (S h12)) h8) (C (C (S h10) h9) h4)) h0)) (C (T (T (T (C (C h10 h9) h4) (S h8)) h3) (C (C (S h6) h5) h4)) h0)) (C (T (C (C h6 h5) h4) (S h3)) h0)

@[equational_result]
theorem Equation1507_implies_Equation1320 (G: Type _) [Magma G] (h: Equation1507 G) : Equation1320 G := fun x y z =>
  let v0 := M y x
  let v1 := M v0 z
  let v2 := M v1 z
  let v3 := M y v2
  let v4 := M v2 (M v2 y)
  let v5 := M y v3
  let v6 := M v3 (M v3 v1)
  let v7 := M x (M x v0)
  have h8 := h x y v2
  let v9 := M z v0
  let v10 := M z v9
  T (T h8 (C (T (T (h v0 z z) (C (T (T (T (T (h v9 z v3) (C (T (T (T (T (h v10 x x) (C (T (T (T (C h8 (R v10)) (S (h v4 v0 z))) (h v4 v0 x)) (C (S h8) (R v7))) (R (M x (M x x))))) (S (h v7 x x))) (h v7 v1 v3)) (C (S (h z v0 x)) (R v6))) (R (M v3 (M v3 z))))) (S (h v6 z v3))) (h v6 v2 y)) (C (S (h z v1 v3)) (R v5))) (R (M z (M z z))))) (S (h v5 z z))) (R v4))) (S (h v3 y v2))

@[equational_result]
theorem Equation1537_implies_Equation695 (G: Type _) [Magma G] (h: Equation1537 G) : Equation695 G := fun x y z =>
  let v0 := M z z
  let v1 := M v0 y
  let v2 := M x v1
  let v3 := M y v2
  have h4 := S (h v0 x z)
  have h5 := h z z z
  have h6 := R v0
  have h7 := R z
  have h8 := C h7 (T (h z z v0) (C h6 (S h5)))
  let v9 := M v3 v3
  have h10 := R (M x x)
  let v11 := M y y
  have h12 := R v11
  T (T (h x y v1) (C h12 (T (T (C (T (C h6 (T (h y z y) (C h6 (C (R y) (T (T (h v11 x z) (C h10 (T (C h7 (T (C h12 h5) (S (h z y v0)))) h8))) h4))))) (S (h y z v0))) (R v2)) (h v3 z v3)) (C h6 (C (R v3) (T (T (h v9 x z) (C h10 (T (C h7 (T (C (R v9) h5) (S (h z v3 v0)))) h8))) h4)))))) (S (h v3 y v0))

