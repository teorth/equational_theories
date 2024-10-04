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
theorem Equation4287_implies_Equation4360 (G: Type _) [Magma G] (h: Equation4287 G) : Equation4360 G := fun x y z w =>
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
theorem Equation3139_implies_Equation3659 (G: Type _) [Magma G] (h: Equation3139 G) : Equation3659 G := fun x =>
  let v0 := M x x
  T (h v0 v0) (C (S (h v0 x)) (R v0))

@[equational_result]
theorem Equation1996_implies_Equation1137 (G: Type _) [Magma G] (h: Equation1996 G) : Equation1137 G := fun x y z =>
  let v0 := M y (M z z)
  T (h x v0 y) (C (S (h y y z)) (R (M v0 x)))

@[equational_result]
theorem Equation3715_implies_Equation4470 (G: Type _) [Magma G] (h: Equation3715 G) : Equation4470 G := fun x y =>
  T (T (h x (M y y)) (C (h x x) (S (h y y)))) (S (h (M x x) y))

@[equational_result]
theorem Equation692_implies_Equation1358 (G: Type _) [Magma G] (h: Equation692 G) : Equation1358 G := fun x y z =>
  let v0 := M (M z x) z
  T (h x y v0) (C (R y) (S (h (M v0 y) x z)))

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
theorem Equation1855_implies_Equation4318 (G: Type _) [Magma G] (h: Equation1855 G) : Equation4318 G := fun x y z =>
  let v0 := M x (M y x)
  T (h v0 v0 z) (C (S (h x y v0)) (R (M z z)))

@[equational_result]
theorem Equation1929_implies_Equation4297 (G: Type _) [Magma G] (h: Equation1929 G) : Equation4297 G := fun x y z =>
  let v0 := M x (M x y)
  T (h v0 v0 z) (C (S (h y x v0)) (R (M z z)))

@[equational_result]
theorem Equation2074_implies_Equation3326 (G: Type _) [Magma G] (h: Equation2074 G) : Equation3326 G := fun x y z =>
  let v0 := M x y
  T (h v0 z (M y x)) (C (S (h x y z)) (R (M z v0)))

@[equational_result]
theorem Equation2761_implies_Equation31 (G: Type _) [Magma G] (h: Equation2761 G) : Equation31 G := fun x y =>
  let v0 := M y y
  T (h x v0 y) (C (S (h v0 y y)) (R x))

@[equational_result]
theorem Equation2992_implies_Equation2373 (G: Type _) [Magma G] (h: Equation2992 G) : Equation2373 G := fun x y z =>
  let v0 := M z (M x z)
  T (h x v0 y) (C (S (h (M y v0) z x)) (R y))

@[equational_result]
theorem Equation3159_implies_Equation3 (G: Type _) [Magma G] (h: Equation3159 G) : Equation3 G := fun x =>
  let v0 := M x x
  T (h x v0 x) (C (S (h x x v0)) (R x))

@[equational_result]
theorem Equation3266_implies_Equation310 (G: Type _) [Magma G] (h: Equation3266 G) : Equation310 G := fun x y =>
  let v0 := M y y
  T (h x y v0) (C (R x) (S (h y v0 y)))

@[equational_result]
theorem Equation4096_implies_Equation367 (G: Type _) [Magma G] (h: Equation4096 G) : Equation367 G := fun x y =>
  let v0 := M y y
  T (h x v0 y) (C (S (h y y v0)) (R x))

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
theorem Equation2592_implies_Equation3201 (G: Type _) [Magma G] (h: Equation2592 G) : Equation3201 G := fun x y z =>
  let v0 := M (M y z) y
  T (h x v0 z) (C (C (R v0) (S (h z z y))) (R x))

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
theorem Equation1025_implies_Equation8 (G: Type _) [Magma G] (h: Equation1025 G) : Equation8 G := fun x =>
  have h0 := R x
  T (h x (M x (M x x))) (C h0 (C (S (h x x)) h0))

@[equational_result]
theorem Equation2679_implies_Equation260 (G: Type _) [Magma G] (h: Equation2679 G) : Equation260 G := fun x y =>
  let v0 := M x x
  T (h x y (M v0 v0)) (C (C (R (M x y)) (S (h x x x))) (R x))

@[equational_result]
theorem Equation3727_implies_Equation3726 (G: Type _) [Magma G] (h: Equation3727 G) : Equation3726 G := fun x y z =>
  have h0 := h x y x
  T (T h0 (h (M x y) (M x x) (M y z))) (C (S h0) (S (h y z x)))

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
theorem Equation840_implies_Equation10 (G: Type _) [Magma G] (h: Equation840 G) : Equation10 G := fun x y =>
  let v0 := M y x
  T (h x y (M v0 v0)) (C (R x) (S (h v0 v0 v0)))

@[equational_result]
theorem Equation914_implies_Equation16 (G: Type _) [Magma G] (h: Equation914 G) : Equation16 G := fun x y =>
  let v0 := M y x
  T (h x y (M v0 v0)) (C (R y) (S (h v0 v0 v0)))

@[equational_result]
theorem Equation1101_implies_Equation4325 (G: Type _) [Magma G] (h: Equation1101 G) : Equation4325 G := fun x y z =>
  let v0 := M y (M z z)
  have h1 := R x
  T (C h1 (C (h y v0 z) h1)) (S (h v0 x v0))

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
theorem Equation2152_implies_Equation1387 (G: Type _) [Magma G] (h: Equation2152 G) : Equation1387 G := fun x y z =>
  let v0 := M z z
  let v1 := M v0 y
  T (h x v0 v1) (C (S (h y z v0)) (R (M v1 x)))

@[equational_result]
theorem Equation2446_implies_Equation23 (G: Type _) [Magma G] (h: Equation2446 G) : Equation23 G := fun x =>
  have h0 := R x
  T (h x (M (M x x) x)) (C (C h0 (S (h x x))) h0)

@[equational_result]
theorem Equation2602_implies_Equation4620 (G: Type _) [Magma G] (h: Equation2602 G) : Equation4620 G := fun x y z =>
  have h0 := R z
  let v1 := M (M x x) y
  T (h v1 z v1) (C (C h0 (S (h y v1 x))) h0)

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
theorem Equation3718_implies_Equation329 (G: Type _) [Magma G] (h: Equation3718 G) : Equation329 G := fun x y z =>
  let v0 := M z y
  T (T (h x y v0) (C (R (M x x)) (h v0 y z))) (S (h x v0 (M v0 v0)))

@[equational_result]
theorem Equation3736_implies_Equation381 (G: Type _) [Magma G] (h: Equation3736 G) : Equation381 G := fun x y z =>
  let v0 := M x z
  T (T (h x y v0) (C (h x v0 z) (R (M y y)))) (S (h v0 y (M v0 v0)))

@[equational_result]
theorem Equation3810_implies_Equation3737 (G: Type _) [Magma G] (h: Equation3810 G) : Equation3737 G := fun x y z =>
  T (T (h x y x) (h (M x y) (M x x) (M x z))) (C (S (h x z x)) (S (h y z x)))

@[equational_result]
theorem Equation3990_implies_Equation41 (G: Type _) [Magma G] (h: Equation3990 G) : Equation41 G := fun x y z =>
  T (T (h x x y) (C (T (h y (M x x) x) (S (h y (M y y) x))) (R y))) (S (h y z y))

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
theorem Equation4026_implies_Equation4182 (G: Type _) [Magma G] (h: Equation4026 G) : Equation4182 G := fun x y z =>
  let v0 := M x (M x z)
  T (h x y v0) (C (T (C (R v0) (S (h y z x))) (S (h (M y z) z x))) (R x))

@[equational_result]
theorem Equation4030_implies_Equation41 (G: Type _) [Magma G] (h: Equation4030 G) : Equation41 G := fun x y z =>
  let v0 := M x (M x x)
  T (T (T (h x x x) (h v0 x x)) (S (h v0 y x))) (S (h y z x))

@[equational_result]
theorem Equation634_implies_Equation4 (G: Type _) [Magma G] (h: Equation634 G) : Equation4 G := fun x y =>
  let v0 := M x y
  T (h x y (M (M y v0) x)) (C (R x) (S (h y v0 x)))

@[equational_result]
theorem Equation918_implies_Equation2 (G: Type _) [Magma G] (h: Equation918 G) : Equation2 G := fun x y =>
  let v0 := M x x
  T (T (h x x x) (C (R x) (C (R v0) (h v0 y x)))) (S (h y x (M (M y y) (M v0 x))))

@[equational_result]
theorem Equation1026_implies_Equation411 (G: Type _) [Magma G] (h: Equation1026 G) : Equation411 G := fun x =>
  let v0 := M x (M x x)
  T (h x v0) (C (R x) (C (S (h x x)) (R v0)))

@[equational_result]
theorem Equation1465_implies_Equation4134 (G: Type _) [Magma G] (h: Equation1465 G) : Equation4134 G := fun x y z =>
  let v0 := M x y
  T (h v0 z (M y x)) (C (R (M v0 z)) (S (h y x z)))

@[equational_result]
theorem Equation1673_implies_Equation2474 (G: Type _) [Magma G] (h: Equation1673 G) : Equation2474 G := fun x y z =>
  let v0 := M (M y y) z
  T (h x v0 z) (C (R (M x v0)) (S (h z z y)))

@[equational_result]
theorem Equation1718_implies_Equation1746 (G: Type _) [Magma G] (h: Equation1718 G) : Equation1746 G := fun x y z =>
  let v0 := M (M x x) x
  T (h x y) (C (R (M y y)) (T (h v0 z) (C (R (M z z)) (S (h x v0)))))

@[equational_result]
theorem Equation1764_implies_Equation3185 (G: Type _) [Magma G] (h: Equation1764 G) : Equation3185 G := fun x y z =>
  let v0 := M (M y z) x
  T (h x v0 z) (C (R (M v0 z)) (S (h y x z)))

@[equational_result]
theorem Equation1835_implies_Equation1865 (G: Type _) [Magma G] (h: Equation1835 G) : Equation1865 G := fun x y z =>
  let v0 := M x (M x x)
  T (h x z) (C (T (h v0 y) (C (S (h x v0)) (R (M y y)))) (R (M z z)))

@[equational_result]
theorem Equation1862_implies_Equation1874 (G: Type _) [Magma G] (h: Equation1862 G) : Equation1874 G := fun x y z w =>
  T (h x y w) (C (T (h (M x (M y y)) y z) (C (S (h x y y)) (R (M y z)))) (R (M y w)))

@[equational_result]
theorem Equation1968_implies_Equation2 (G: Type _) [Magma G] (h: Equation1968 G) : Equation2 G := fun x y =>
  let v0 := M x (M y x)
  T (T (h x x y) (C (h v0 x y) (R (M y y)))) (S (h y (M x (M y v0)) y))

@[equational_result]
theorem Equation2253_implies_Equation203 (G: Type _) [Magma G] (h: Equation2253 G) : Equation203 G := fun x =>
  have h0 := R x
  let v1 := M x x
  T (h x (M v1 (M x (M v1 v1)))) (C (C h0 (S (h v1 x))) h0)

@[equational_result]
theorem Equation2891_implies_Equation3331 (G: Type _) [Magma G] (h: Equation2891 G) : Equation3331 G := fun x y z =>
  let v0 := M y z
  T (C (h x z v0) (R y)) (S (h (M x (M z v0)) y z))

@[equational_result]
theorem Equation2981_implies_Equation5 (G: Type _) [Magma G] (h: Equation2981 G) : Equation5 G := fun x y =>
  let v0 := M y x
  T (h x (M x (M v0 y)) y) (C (S (h y x v0)) (R x))

@[equational_result]
theorem Equation3214_implies_Equation2558 (G: Type _) [Magma G] (h: Equation3214 G) : Equation2558 G := fun x y z =>
  let v0 := M (M y z) z
  T (h x v0 y) (C (C (S (h y y z)) (R v0)) (R x))

@[equational_result]
theorem Equation3718_implies_Equation4508 (G: Type _) [Magma G] (h: Equation3718 G) : Equation4508 G := fun x y z =>
  T (T (h x (M y z) (M z z)) (C (h x x x) (S (h z z y)))) (S (h (M x x) z z))

@[equational_result]
theorem Equation1225_implies_Equation99 (G: Type _) [Magma G] (h: Equation1225 G) : Equation99 G := fun x =>
  have h0 := R x
  let v1 := M x x
  T (h x (M (M (M v1 v1) x) v1)) (C h0 (C (S (h v1 x)) h0))

@[equational_result]
theorem Equation1723_implies_Equation2 (G: Type _) [Magma G] (h: Equation1723 G) : Equation2 G := fun x y =>
  let v0 := M (M x y) x
  T (T (h x y x) (C (R (M y y)) (h v0 y x))) (S (h y y (M (M v0 y) x)))

@[equational_result]
theorem Equation2000_implies_Equation16 (G: Type _) [Magma G] (h: Equation2000 G) : Equation16 G := fun x y =>
  let v0 := M y y
  T (h x y y) (C (T (C (h y x y) (R v0)) (S (h y (M x v0) y))) (R (M y x)))

@[equational_result]
theorem Equation3690_implies_Equation3677 (G: Type _) [Magma G] (h: Equation3690 G) : Equation3677 G := fun x y =>
  let v0 := M y x
  let v1 := M v0 v0
  T (T (h x v0 x) (C (R v1) (h x v0 y))) (S (h v0 v0 v1))

@[equational_result]
theorem Equation3827_implies_Equation41 (G: Type _) [Magma G] (h: Equation3827 G) : Equation41 G := fun x y z =>
  T (T (h x x y) (C (R (M y y)) (T (h y x x) (S (h y y x))))) (S (h y z y))

@[equational_result]
theorem Equation714_implies_Equation511 (G: Type _) [Magma G] (h: Equation714 G) : Equation511 G := fun x y =>
  have h0 := R y
  have h1 := h x y
  T h1 (C h0 (T (h (M y (M (M y x) y)) y) (C h0 (C h0 (C (S h1) h0)))))

@[equational_result]
theorem Equation1872_implies_Equation1874 (G: Type _) [Magma G] (h: Equation1872 G) : Equation1874 G := fun x y z w =>
  let v0 := M x (M y z)
  T (T (h x y z) (C (h v0 y w) (R (M y y)))) (S (h (M v0 (M y w)) y y))

@[equational_result]
theorem Equation2273_implies_Equation208 (G: Type _) [Magma G] (h: Equation2273 G) : Equation208 G := fun x y =>
  have h0 := R x
  T (h x y (M x (M x (M x x)))) (C (C h0 (C (R y) (S (h x x x)))) h0)

@[equational_result]
theorem Equation2281_implies_Equation211 (G: Type _) [Magma G] (h: Equation2281 G) : Equation211 G := fun x y =>
  have h0 := R x
  let v1 := M y y
  T (h x (M v1 (M v1 v1)) y) (C (C h0 (S (h v1 v1 y))) h0)

@[equational_result]
theorem Equation2331_implies_Equation2940 (G: Type _) [Magma G] (h: Equation2331 G) : Equation2940 G := fun x y =>
  have h0 := R y
  have h1 := h x y
  T h1 (C (T (h (M y (M y (M x y))) y) (C (C h0 (C h0 (S h1))) h0)) h0)

@[equational_result]
theorem Equation2442_implies_Equation27 (G: Type _) [Magma G] (h: Equation2442 G) : Equation27 G := fun x y z =>
  let v0 := M x (M (M x x) x)
  T (h x z) (C (T (h v0 y) (C (S (h x (M (M v0 v0) v0))) (R y))) (R z))

@[equational_result]
theorem Equation2456_implies_Equation203 (G: Type _) [Magma G] (h: Equation2456 G) : Equation203 G := fun x =>
  have h0 := R x
  T (h x (M x (M (M x x) x))) (C (C h0 (C (S (h x x)) h0)) h0)

@[equational_result]
theorem Equation3310_implies_Equation38 (G: Type _) [Magma G] (h: Equation3310 G) : Equation38 G := fun x y =>
  let v0 := M y x
  T (T (h x x (M v0 x)) (C (R x) (S (h x v0 x)))) (S (h x y x))

@[equational_result]
theorem Equation3672_implies_Equation3665 (G: Type _) [Magma G] (h: Equation3672 G) : Equation3665 G := fun x y =>
  let v0 := M x y
  let v1 := M v0 v0
  T (T (h x x v0) (C (h x y v0) (R v1))) (S (h v0 v1 v0))

@[equational_result]
theorem Equation3682_implies_Equation3709 (G: Type _) [Magma G] (h: Equation3682 G) : Equation3709 G := fun x y z w =>
  let v0 := M x x
  T (T (T (T (h x x x) (C (h x x z) (R v0))) (S (h (M z z) v0 x))) (S (h z z z))) (h z y w)

@[equational_result]
theorem Equation3716_implies_Equation327 (G: Type _) [Magma G] (h: Equation3716 G) : Equation327 G := fun x y z =>
  let v0 := M y z
  T (T (T (h x y z) (h (M x x) v0 z)) (C (S (h x x x)) (R (M v0 z)))) (S (h x v0 z))

@[equational_result]
theorem Equation3790_implies_Equation395 (G: Type _) [Magma G] (h: Equation3790 G) : Equation395 G := fun x y z =>
  let v0 := M z x
  T (T (T (h x y z) (h v0 (M y y) x)) (C (R (M x v0)) (S (h y y y)))) (S (h v0 y x))

@[equational_result]
theorem Equation894_implies_Equation2 (G: Type _) [Magma G] (h: Equation894 G) : Equation2 G := fun x y =>
  let v0 := M x x
  T (T (h x x x) (C (R x) (C (h v0 y x) (R v0)))) (S (h y x (M (M v0 x) (M y y))))

@[equational_result]
theorem Equation898_implies_Equation2316 (G: Type _) [Magma G] (h: Equation898 G) : Equation2316 G := fun x y z =>
  let v0 := M z y
  let v1 := M x v0
  let v2 := M y v1
  T (h x v2 v0) (C (R v2) (S (h z v1 y)))

@[equational_result]
theorem Equation968_implies_Equation765 (G: Type _) [Magma G] (h: Equation968 G) : Equation765 G := fun x y z =>
  have h0 := h x y y
  T h0 (C (R y) (T (h (M (M y y) (M y x)) z y) (C (R z) (C (R (M y z)) (S h0)))))

@[equational_result]
theorem Equation1254_implies_Equation107 (G: Type _) [Magma G] (h: Equation1254 G) : Equation107 G := fun x y =>
  have h0 := R x
  let v1 := M y y
  T (h x y (M (M v1 v1) v1)) (C h0 (C (S (h v1 y v1)) h0))

@[equational_result]
theorem Equation1914_implies_Equation2 (G: Type _) [Magma G] (h: Equation1914 G) : Equation2 G := fun x y =>
  let v0 := M y (M y x)
  T (T (h x (M y (M v0 x)) x) (C (S (h v0 y x)) (R (M x x)))) (S (h y y x))

@[equational_result]
theorem Equation2726_implies_Equation2 (G: Type _) [Magma G] (h: Equation2726 G) : Equation2 G := fun x y =>
  let v0 := M x x
  T (T (h x x x) (C (C (h v0 x y) (R v0)) (R x))) (S (h y (M (M x v0) (M y y)) x))

@[equational_result]
theorem Equation2754_implies_Equation2 (G: Type _) [Magma G] (h: Equation2754 G) : Equation2 G := fun x y =>
  let v0 := M x x
  T (T (h x x x) (C (C (R v0) (h v0 y x)) (R x))) (S (h y x (M (M y y) (M x v0))))

@[equational_result]
theorem Equation2805_implies_Equation1368 (G: Type _) [Magma G] (h: Equation2805 G) : Equation1368 G := fun x y z =>
  let v0 := M z y
  let v1 := M v0 x
  let v2 := M v1 z
  T (h x v2 v0) (C (S (h y v1 z)) (R v2))

@[equational_result]
theorem Equation3559_implies_Equation355 (G: Type _) [Magma G] (h: Equation3559 G) : Equation355 G := fun x y z w =>
  let v0 := M w y
  T (T (T (h x y) (C (R y) (T (h (M y y) y) (S (h w y))))) (h y v0)) (S (h z v0))

@[equational_result]
theorem Equation3778_implies_Equation41 (G: Type _) [Magma G] (h: Equation3778 G) : Equation41 G := fun x y z =>
  have h0 := h x x x
  T (T h0 (C (T h0 (S (h z x x))) (R (M x x)))) (S (h y z x))

@[equational_result]
theorem Equation3812_implies_Equation41 (G: Type _) [Magma G] (h: Equation3812 G) : Equation41 G := fun x y z =>
  let v0 := M x x
  let v1 := M y y
  T (T (T (h x x y) (h (M y x) v1 v0)) (S (h (M y z) v1 v0))) (S (h y z y))

@[equational_result]
theorem Equation1061_implies_Equation452 (G: Type _) [Magma G] (h: Equation1061 G) : Equation452 G := fun x y z =>
  let v0 := M z (M y z)
  T (h x y v0) (C (R x) (C (S (h y z y)) (R v0)))

@[equational_result]
theorem Equation1120_implies_Equation714 (G: Type _) [Magma G] (h: Equation1120 G) : Equation714 G := fun x y =>
  have h0 := R y
  have h1 := h x y
  T h1 (C h0 (T (h (M (M y (M y x)) y) y) (C h0 (C (C h0 (S h1)) h0))))

@[equational_result]
theorem Equation1171_implies_Equation1983 (G: Type _) [Magma G] (h: Equation1171 G) : Equation1983 G := fun x y z =>
  let v0 := M y (M z y)
  T (h x v0 z) (C (R v0) (C (S (h z z y)) (R x)))

@[equational_result]
theorem Equation1243_implies_Equation105 (G: Type _) [Magma G] (h: Equation1243 G) : Equation105 G := fun x y =>
  let v0 := M (M y x) y
  let v1 := M x v0
  T (h x y (M (M v1 x) v1)) (C (R x) (S (h v0 x v1)))

@[equational_result]
theorem Equation1470_implies_Equation3534 (G: Type _) [Magma G] (h: Equation1470 G) : Equation3534 G := fun x y z =>
  let v0 := M z y
  let v1 := M x y
  T (h v1 (M x v1) v0) (C (S (h x y x)) (C (R v0) (S (h z y x))))

@[equational_result]
theorem Equation1742_implies_Equation1816 (G: Type _) [Magma G] (h: Equation1742 G) : Equation1816 G := fun x y z w =>
  let v0 := M (M w z) x
  T (T (h x z w) (C (R (M z z)) (h v0 z y))) (S (h (M (M y z) v0) z z))

@[equational_result]
theorem Equation2372_implies_Equation221 (G: Type _) [Magma G] (h: Equation2372 G) : Equation221 G := fun x y =>
  let v0 := M y (M x y)
  let v1 := M v0 x
  T (h x (M v1 (M x v1)) y) (C (S (h v0 v1 x)) (R x))

@[equational_result]
theorem Equation2482_implies_Equation1670 (G: Type _) [Magma G] (h: Equation2482 G) : Equation1670 G := fun x y z =>
  let v0 := M (M z y) z
  T (h x y v0) (C (C (R x) (S (h y z y))) (R v0))

@[equational_result]
theorem Equation2779_implies_Equation3182 (G: Type _) [Magma G] (h: Equation2779 G) : Equation3182 G := fun x y z =>
  have h0 := h x z z
  T h0 (C (T (h (M (M z z) (M x z)) y z) (C (C (R (M y z)) (S h0)) (R y))) (R z))

@[equational_result]
theorem Equation3686_implies_Equation3693 (G: Type _) [Magma G] (h: Equation3686 G) : Equation3693 G := fun x y z w =>
  let v0 := M x x
  T (T (T (T (h x x x) (C (R v0) (h x z x))) (S (h (M z z) x v0))) (S (h z z z))) (h z y w)

@[equational_result]
theorem Equation3751_implies_Equation43 (G: Type _) [Magma G] (h: Equation3751 G) : Equation43 G := fun x y =>
  have h0 := h x y
  have h1 := S h0
  let v2 := M y x
  T (T (T h0 (h v2 v2)) (C h1 h1)) (S (h y x))

@[equational_result]
theorem Equation3774_implies_Equation41 (G: Type _) [Magma G] (h: Equation3774 G) : Equation41 G := fun x y z =>
  have h0 := S (h z x x)
  let v1 := M x x
  T (T (T (h x x x) (h v1 v1 v1)) (C h0 h0)) (S (h y z x))

@[equational_result]
theorem Equation625_implies_Equation49 (G: Type _) [Magma G] (h: Equation625 G) : Equation49 G := fun x y =>
  have h0 := R x
  T (h x y (M y (M (M x x) y))) (C h0 (C h0 (C (S (h y x x)) h0)))

@[equational_result]
theorem Equation914_implies_Equation1929 (G: Type _) [Magma G] (h: Equation914 G) : Equation1929 G := fun x y z =>
  let v0 := M y x
  T (T (h x y x) (C (R y) (C (h v0 y z) (R (M x x))))) (S (h (M (M y v0) (M z z)) y x))

@[equational_result]
theorem Equation1230_implies_Equation100 (G: Type _) [Magma G] (h: Equation1230 G) : Equation100 G := fun x y =>
  have h0 := R x
  T (h x (M (M (M x x) x) x) y) (C h0 (C (C (S (h x x x)) h0) (R y)))

@[equational_result]
theorem Equation1234_implies_Equation101 (G: Type _) [Magma G] (h: Equation1234 G) : Equation101 G := fun x y =>
  have h0 := R x
  T (h x (M (M (M x x) x) x) y) (C h0 (C (C (S (h x x x)) (R y)) h0))

@[equational_result]
theorem Equation1471_implies_Equation27 (G: Type _) [Magma G] (h: Equation1471 G) : Equation27 G := fun x y z =>
  let v0 := M x (M x x)
  let v1 := M x y
  T (T (h x y x) (C (h v1 z x) (R v0))) (S (h (M v1 z) v0 x))

@[equational_result]
theorem Equation1913_implies_Equation1098 (G: Type _) [Magma G] (h: Equation1913 G) : Equation1098 G := fun x y z =>
  let v0 := M x (M z y)
  T (h x z v0) (C (T (C (h z x y) (R (M x v0))) (S (h y v0 x))) (R (M v0 z)))

@[equational_result]
theorem Equation2277_implies_Equation211 (G: Type _) [Magma G] (h: Equation2277 G) : Equation211 G := fun x y =>
  have h0 := R x
  T (h x y (M y (M x (M x x)))) (C (C h0 (C (R y) (S (h y x x)))) h0)

@[equational_result]
theorem Equation2290_implies_Equation203 (G: Type _) [Magma G] (h: Equation2290 G) : Equation203 G := fun x =>
  let v0 := M x (M x x)
  T (h x (M x (M v0 (M v0 v0)))) (C (S (h v0 x)) (R x))

@[equational_result]
theorem Equation2389_implies_Equation31 (G: Type _) [Magma G] (h: Equation2389 G) : Equation31 G := fun x y =>
  let v0 := M x (M x (M x x))
  T (h x v0 y) (C (T (C (R v0) (C (R y) (S (h y x x)))) (S (h (M y y) x x))) (R x))

@[equational_result]
theorem Equation2507_implies_Equation2913 (G: Type _) [Magma G] (h: Equation2507 G) : Equation2913 G := fun x y =>
  have h0 := R y
  have h1 := h x y
  T h1 (C (T (h (M y (M (M x y) y)) y) (C (C h0 (C (S h1) h0)) h0)) h0)

@[equational_result]
theorem Equation2677_implies_Equation2079 (G: Type _) [Magma G] (h: Equation2677 G) : Equation2079 G := fun x y z =>
  let v0 := M x y
  T (T (h x y x) (C (C (h v0 z y) (R (M y x))) (R x))) (S (h (M (M v0 z) (M z y)) y x))

@[equational_result]
theorem Equation2685_implies_Equation2076 (G: Type _) [Magma G] (h: Equation2685 G) : Equation2076 G := fun x y z =>
  let v0 := M x y
  T (T (h x y x) (C (C (h v0 z y) (R v0)) (R x))) (S (h (M (M v0 z) (M y z)) y x))

@[equational_result]
theorem Equation2688_implies_Equation2068 (G: Type _) [Magma G] (h: Equation2688 G) : Equation2068 G := fun x y z =>
  let v0 := M x y
  T (T (h x y x) (C (C (h v0 y z) (R (M x x))) (R y))) (S (h (M (M v0 y) (M z z)) y x))

@[equational_result]
theorem Equation2913_implies_Equation3116 (G: Type _) [Magma G] (h: Equation2913 G) : Equation3116 G := fun x y =>
  have h0 := R y
  have h1 := h x y
  T h1 (C (T (h (M (M y (M x y)) y) y) (C (C (C h0 (S h1)) h0) h0)) h0)

@[equational_result]
theorem Equation3419_implies_Equation41 (G: Type _) [Magma G] (h: Equation3419 G) : Equation41 G := fun x y z =>
  have h0 := R y
  T (T (h x x y) (C h0 (C h0 (T (h x y x) (S (h z y x)))))) (S (h y z y))

@[equational_result]
theorem Equation3553_implies_Equation3370 (G: Type _) [Magma G] (h: Equation3553 G) : Equation3370 G := fun x y z =>
  let v0 := M z x
  let v1 := M v0 x
  T (h x y v1) (C (R y) (T (C (S (h z x x)) (R v1)) (S (h z v0 x))))

@[equational_result]
theorem Equation3766_implies_Equation41 (G: Type _) [Magma G] (h: Equation3766 G) : Equation41 G := fun x y z =>
  let v0 := M x x
  have h1 := h x x x
  T (T (T h1 (C h1 (R v0))) (S (h (M z z) v0 x))) (S (h y z x))

@[equational_result]
theorem Equation3821_implies_Equation41 (G: Type _) [Magma G] (h: Equation3821 G) : Equation41 G := fun x y z =>
  let v0 := M x x
  T (T (T (h x x v0) (C (R (M v0 v0)) (h x v0 x))) (S (h v0 (M y x) v0))) (S (h y z x))

@[equational_result]
theorem Equation4322_implies_Equation4365 (G: Type _) [Magma G] (h: Equation4322 G) : Equation4365 G := fun x y z w =>
  T (T (T (T (T (S (h y x z)) (h y x x)) (h x y (M z x))) (C (R y) (h x z y))) (S (h z y (M x y)))) (h z y w)

@[equational_result]
theorem Equation4344_implies_Equation4365 (G: Type _) [Magma G] (h: Equation4344 G) : Equation4365 G := fun x y z w =>
  T (T (T (T (T (S (h y x z)) (h y x y)) (h x y (M z z))) (C (R y) (h x z y))) (S (h z y (M x y)))) (h z y w)

@[equational_result]
theorem Equation910_implies_Equation1925 (G: Type _) [Magma G] (h: Equation910 G) : Equation1925 G := fun x y =>
  let v0 := M y y
  let v1 := M y x
  T (T (h x y) (C (R y) (C (h v1 y) (R v0)))) (S (h (M (M y v1) v0) y))

@[equational_result]
theorem Equation1031_implies_Equation101 (G: Type _) [Magma G] (h: Equation1031 G) : Equation101 G := fun x y =>
  have h0 := R x
  T (h x y (M (M y (M x x)) y)) (C h0 (C (C h0 (S (h y x x))) h0))

@[equational_result]
theorem Equation1053_implies_Equation11 (G: Type _) [Magma G] (h: Equation1053 G) : Equation11 G := fun x y =>
  let v0 := M (M x (M x x)) x
  T (h x y v0) (C (R x) (T (C (C (R y) (S (h y x x))) (R v0)) (S (h (M y y) x x))))

@[equational_result]
theorem Equation1674_implies_Equation27 (G: Type _) [Magma G] (h: Equation1674 G) : Equation27 G := fun x y z =>
  let v0 := M (M x x) x
  let v1 := M x y
  T (T (h x y x) (C (h v1 z x) (R v0))) (S (h (M v1 z) v0 x))

@[equational_result]
theorem Equation1937_implies_Equation19 (G: Type _) [Magma G] (h: Equation1937 G) : Equation19 G := fun x y z =>
  let v0 := M x (M x x)
  let v1 := M z x
  T (T (h x x z) (C (R v0) (h v1 x y))) (S (h (M y v1) x v0))

@[equational_result]
theorem Equation2368_implies_Equation221 (G: Type _) [Magma G] (h: Equation2368 G) : Equation221 G := fun x y =>
  let v0 := M x y
  T (h x y (M x (M x (M v0 x)))) (C (C (R y) (S (h v0 x x))) (R x))

@[equational_result]
theorem Equation2741_implies_Equation1726 (G: Type _) [Magma G] (h: Equation2741 G) : Equation1726 G := fun x y z =>
  let v0 := M x z
  T (T (h x x z) (C (C (R (M x x)) (h v0 y z)) (R z))) (S (h (M (M y y) (M v0 z)) x z))

@[equational_result]
theorem Equation3417_implies_Equation3994 (G: Type _) [Magma G] (h: Equation3417 G) : Equation3994 G := fun x y z =>
  let v0 := M x y
  have h1 := R v0
  T (T (h x y v0) (C h1 (C h1 (h y x z)))) (S (h (M z v0) z v0))

@[equational_result]
theorem Equation895_implies_Equation11 (G: Type _) [Magma G] (h: Equation895 G) : Equation11 G := fun x y =>
  have h0 := S (h y x x)
  T (h x x (M (M y x) (M x x))) (C (R x) (C h0 h0))

@[equational_result]
theorem Equation1245_implies_Equation105 (G: Type _) [Magma G] (h: Equation1245 G) : Equation105 G := fun x y =>
  let v0 := M y x
  T (h x y (M (M (M x v0) x) x)) (C (R x) (C (S (h v0 x x)) (R y)))

@[equational_result]
theorem Equation1262_implies_Equation107 (G: Type _) [Magma G] (h: Equation1262 G) : Equation107 G := fun x y =>
  have h0 := R x
  T (h x y (M (M (M x x) x) y)) (C h0 (C (C (S (h y x x)) (R y)) h0))

@[equational_result]
theorem Equation2318_implies_Equation211 (G: Type _) [Magma G] (h: Equation2318 G) : Equation211 G := fun x y =>
  let v0 := M x (M y y)
  T (h x (M x (M v0 (M x x))) y) (C (S (h v0 x x)) (R x))

@[equational_result]
theorem Equation2331_implies_Equation707 (G: Type _) [Magma G] (h: Equation2331 G) : Equation707 G := fun x y =>
  let v0 := M x y
  have h1 := R y
  T (T (h x y) (C (C h1 (C h1 (h v0 y))) h1)) (S (h (M y (M y (M v0 y))) y))

@[equational_result]
theorem Equation2402_implies_Equation31 (G: Type _) [Magma G] (h: Equation2402 G) : Equation31 G := fun x y =>
  have h0 := S (h y x x)
  let v1 := M x (M x (M x x))
  T (h x y v1) (C (C (R y) (T (C (R v1) h0) h0)) (R x))

