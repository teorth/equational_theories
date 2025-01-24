import Mathlib.Tactic
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang
import equational_theories.EquationalResult

/-!
Refutations found by interepeting the magma operation as a linear operation
`x ◇ y = a*x + b*y` and then solving for `a` and `b`.

Discussed on Zulip here:
https://leanprover.zulipchat.com/#narrow/stream/458659-Equational/topic/An.20old.20new.20idea/near/475038501
-/

namespace LinearOps

-- The following tactic can be faster for larger magmas (roughly `Fin n` with `n ≥ 17`, although
-- it of course depends on the number of variables in the equation)
macro "ringFin" : tactic =>
  `(tactic | (constructor; · solve | intro x; revert x; simp only [Magma.op]; ring_nf; simp) )

/--
Found using the Rust program:
```
// x = y ◇ (((x ◇ y) ◇ x) ◇ y)
fn p1286_3(m: u64, a: u64, b: u64) -> bool {
    (a+b) % m != 1 &&
        ((b * b) * (a * a + 1) + a) % m == 0 &&
        (b * (a * a * a * a * a + a * a * a)) % m == (2 * a * a + 1) % m
}
fn main() {
    for m in 2u64 .. 10000 {
        for a in 0u64 .. m {
            for b in 0u64 .. m {
                if p1286_3(m, a, b) {
                    println!("got it! {m}, {a}, {b}")
                }
            }
        }
    }
}
```
-/
@[equational_result]
theorem Equation1286_not_implies_Equation3 : ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [1279, 1286] [3, 8, 23, 47, 99, 151, 203, 255, 326, 359, 375, 411, 614, 817, 1020, 1083, 1426, 1629, 1832, 2035, 2238, 2301, 2441, 2504, 2644, 2847, 3050, 3253, 3319, 3456, 3522, 3659, 3715, 3722, 3862, 3915, 4065, 4118, 4380, 4435, 4470] :=
  ⟨Fin 11, { op := fun x y => 1 * x + 7 * y }, Finite.of_fintype _, by decideFin!⟩

/-- Dual of the above. -/
@[equational_result]
theorem Equation2301_not_implies_Equation3 : ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [2328, 2301] [3, 8, 23, 47, 99, 151, 203, 255, 307, 326, 359, 375, 411, 614, 817, 1020, 1083, 1223, 1426, 1629, 1832, 2035, 2441, 2504, 2644, 2847, 3050, 3253, 3319, 3456, 3522, 3659, 3715, 3722, 3862, 3915, 4065, 4118, 4380, 4435, 4470] :=
  ⟨Fin 11, { op := fun x y => 7 * x + 1 * y }, Finite.of_fintype _, by decideFin!⟩

@[equational_result]
theorem Equation3116_not_implies_Equation513 : ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [3116] [513] :=
  ⟨Fin 11, { op := fun x y => 3 * x + 9 * y }, Finite.of_fintype _, by decideFin!⟩

-- dual of the above
@[equational_result]
theorem Equation511_not_implies_Equation3079 : ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [511] [3079] :=
  ⟨Fin 11, { op := fun x y => 9 * x + 3 * y }, Finite.of_fintype _, by decideFin!⟩

@[equational_result]
theorem LinearInvariance0 : ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [1076] [26, 65, 73, 102, 117, 125, 160, 167, 212, 229, 258, 263, 335, 362, 429, 437, 464, 473, 504, 513, 546, 562, 617, 632, 640, 679, 704, 826, 833, 872, 879, 910, 917, 949, 962, 1029, 1046, 1085, 1110, 1119, 1226, 1231, 1278, 1323, 1455, 1482, 1491, 1518, 1526, 1632, 1654, 1658, 1662, 1682, 1721, 1729, 1790, 1838, 1850, 1861, 1873, 1885, 1897, 1925, 1967, 2044, 2053, 2060, 2100, 2125, 2267, 2300, 2328, 2330, 2449, 2457, 2470, 2485, 2503, 2533, 2541, 2586, 2653, 2663, 2672, 2699, 2744, 2850, 2863, 2875, 2910, 2939, 3053, 3058, 3066, 3075, 3079, 3083, 3094, 3113, 3271, 3279, 3343, 3352, 3459, 3474, 3482, 3518, 3526, 3558, 3607, 3668, 3675, 3761, 3871, 3888, 3924, 3954, 4068, 4073, 4127, 4131, 4135, 4146, 4157, 4290, 4321, 4369, 4383, 4408, 4443, 4585, 4636, 4656] :=
  ⟨Fin 43, { op := fun x y => 17 * x + 27 * y }, Finite.of_fintype _, by ringFin; decideFin!⟩

@[equational_result]
theorem LinearInvariance1 : ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [2531, 3103] [16, 55, 72, 118, 127, 167, 179, 209, 222, 228, 261, 274, 315, 384, 419, 436, 466, 474, 500, 513, 528, 575, 633, 642, 669, 677, 703, 833, 845, 883, 909, 916, 1026, 1039, 1045, 1075, 1086, 1098, 1122, 1184, 1229, 1242, 1279, 1325, 1434, 1444, 1452, 1482, 1525, 1647, 1655, 1682, 1691, 1722, 1731, 1764, 1780, 1840, 1851, 1885, 1898, 1913, 1921, 1934, 1949, 2054, 2061, 2101, 2125, 2137, 2254, 2263, 2304, 2327, 2450, 2467, 2497, 2506, 2540, 2650, 2660, 2699, 2710, 2722, 2737, 2743, 2776, 2865, 2873, 2903, 2912, 2936, 3056, 3068, 3079, 3091, 3115, 3143, 3185, 3261, 3278, 3306, 3334, 3353, 3414, 3475, 3484, 3556, 3675, 3687, 3748, 3868, 3881, 3887, 3951, 3962, 3973, 4023, 4071, 4084, 4130, 4164, 4275, 4307, 4321, 4409, 4443, 4479, 4605, 4636, 4684] :=
  ⟨Fin 25, { op := fun x y => 12 * x + 14 * y }, Finite.of_fintype _, by ringFin; ringFin; decideFin!⟩

@[equational_result]
theorem LinearInvariance2 : ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [2700] [47, 2035, 2847] :=
  ⟨Fin 19, { op := fun x y => 14 * x + 8 * y }, Finite.of_fintype _, by ringFin; decideFin!⟩

@[equational_result]
theorem LinearInvariance3 : ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [2866] [255, 307, 326, 2035, 2644, 3253, 3319, 3456, 3522] :=
  ⟨Fin 23, { op := fun x y => 4 * x + 3 * y }, Finite.of_fintype _, by ringFin; decideFin!⟩

@[equational_result]
theorem LinearInvariance4 : ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [3113] [3079] :=
  ⟨Fin 41, { op := fun x y => 31 * x + 11 * y }, Finite.of_fintype _, by ringFin; decideFin!⟩

@[equational_result]
theorem LinearInvariance5 : ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [882] [3862, 3915] :=
  ⟨Fin 11, { op := fun x y => 6 * x + 7 * y }, Finite.of_fintype _, by decideFin!⟩

@[equational_result]
theorem LinearInvariance6 : ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [2264] [3050] :=
  ⟨Fin 16, { op := fun x y => 5 * x + 6 * y }, Finite.of_fintype _, by decideFin!⟩

@[equational_result]
theorem LinearInvariance7 : ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [706] [47, 359, 375, 817, 1426, 3862, 3915, 4065, 4118] :=
  ⟨Fin 17, { op := fun x y => 10 * x + 11 * y }, Finite.of_fintype _, by ringFin; decideFin!⟩

@[equational_result]
theorem LinearInvariance8 : ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [464] [2457, 3066] :=
  ⟨Fin 19, { op := fun x y => 3 * x + 17 * y }, Finite.of_fintype _, by ringFin; decideFin!⟩

@[equational_result]
theorem LinearInvariance9 : ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [704] [203, 817, 1426, 3050] :=
  ⟨Fin 23, { op := fun x y => 2 * x + 6 * y }, Finite.of_fintype _, by ringFin; decideFin!⟩

@[equational_result]
theorem LinearInvariance10 : ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [2504] [23, 47, 1629, 1832, 3050, 3456, 3522, 4065, 4118] :=
  ⟨Fin 27, { op := fun x y => 20 * x + 13 * y }, Finite.of_fintype _, by ringFin; decideFin!⟩

@[equational_result]
theorem LinearInvariance11 : ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [2531] [16, 55, 72, 118, 127, 167, 179, 209, 222, 228, 261, 274, 315, 384, 419, 436, 466, 474, 500, 513, 528, 575, 633, 642, 669, 677, 703, 833, 845, 883, 909, 916, 1026, 1039, 1045, 1075, 1086, 1098, 1122, 1184, 1229, 1242, 1279, 1325, 1434, 1444, 1452, 1482, 1525, 1647, 1655, 1682, 1691, 1722, 1731, 1764, 1780, 1840, 1851, 1885, 1898, 1913, 1921, 1934, 1949, 2054, 2061, 2101, 2125, 2137, 2254, 2263, 2304, 2327, 2450, 2467, 2497, 2506, 2540, 2650, 2660, 2699, 2710, 2722, 2737, 2743, 2776, 2865, 2873, 2903, 2912, 2936, 3056, 3068, 3079, 3091, 3103, 3115, 3143, 3185, 3261, 3278, 3306, 3334, 3345, 3353, 3414, 3475, 3484, 3548, 3556, 3675, 3687, 3748, 3868, 3881, 3887, 3951, 3962, 3973, 4023, 4071, 4084, 4130, 4164, 4275, 4307, 4321, 4409, 4443, 4479, 4605, 4636, 4684] :=
  ⟨Fin 43, { op := fun x y => 27 * x + 17 * y }, Finite.of_fintype _, by ringFin; decideFin!⟩

@[equational_result]
theorem LinearInvariance12 : ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [2467] [3050, 3079] :=
  ⟨Fin 7, { op := fun x y => 2 * x + 3 * y }, Finite.of_fintype _, by ringFin; decideFin!⟩

@[equational_result]
theorem LinearInvariance13 : ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [412] [48, 413, 414, 415, 615, 818, 1427, 2240, 3254] :=
  ⟨Fin 16, { op := fun x y => 3 * x + 14 * y }, Finite.of_fintype _, by decideFin!⟩

@[equational_result]
theorem LinearInvariance14 : ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [2903] [99, 411, 2035, 2644] :=
  ⟨Fin 13, { op := fun x y => 6 * x + 10 * y }, Finite.of_fintype _, by decideFin!⟩

@[equational_result]
theorem LinearInvariance15 : ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [907] [255, 614, 1426] :=
  ⟨Fin 17, { op := fun x y => 4 * x + 7 * y }, Finite.of_fintype _, by ringFin; decideFin!⟩

-- TODO: Here ringFin fails due to https://github.com/leanprover/lean4/issues/5630
-- we can use it once that's fixed.How?
@[equational_result]
theorem LinearInvariance16 : ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [667] [411, 2847, 3050, 4380] :=
  ⟨Fin 25, { op := fun x y => 17 * x + 2 * y }, Finite.of_fintype _, by decideFin!⟩

@[equational_result]
theorem LinearInvariance17 : ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [511, 714, 1120, 2338] [3079] :=
  ⟨Fin 29, { op := fun x y => 19 * x + 11 * y }, Finite.of_fintype _, by ringFin; ringFin; ringFin; ringFin; decideFin!⟩

@[equational_result]
theorem LinearInvariance18 : ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [1289, 2507, 2913, 3116] [513] :=
  ⟨Fin 27, { op := fun x y => 2 * x + 17 * y }, Finite.of_fintype _, by ringFin; ringFin; ringFin; ringFin; decideFin!⟩

@[equational_result]
theorem LinearInvariance19 : ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [2670, 2866] [255, 307, 326, 3253, 3319, 3456, 3522] :=
  ⟨Fin 27, { op := fun x y => 7 * x + 24 * y }, Finite.of_fintype _, by ringFin; ringFin; decideFin!⟩

@[equational_result]
theorem LinearInvariance20 : ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [474] [513] :=
  ⟨Fin 11, { op := fun x y => 10 * x + 2 * y }, Finite.of_fintype _, by decideFin!⟩

@[equational_result]
theorem LinearInvariance21 : ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [2328] [99, 1426] :=
  ⟨Fin 29, { op := fun x y => 14 * x + 23 * y }, Finite.of_fintype _, by ringFin; decideFin!⟩

@[equational_result]
theorem LinearInvariance22 : ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [670] [817] :=
  ⟨Fin 11, { op := fun x y => 9 * x + 4 * y }, Finite.of_fintype _, by decideFin!⟩

@[equational_result]
theorem LinearInvariance23 : ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [3102] [270, 1238, 2087, 2696, 2899, 3065, 3139, 3176, 4080] :=
  ⟨Fin 16, { op := fun x y => 10 * x + 7 * y }, Finite.of_fintype _, by decideFin!⟩

@[equational_result]
theorem LinearInvariance24 : ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [2937] [2644] :=
  ⟨Fin 11, { op := fun x y => 4 * x + 9 * y }, Finite.of_fintype _, by decideFin!⟩

@[equational_result]
theorem LinearInvariance25 : ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [2301] [3, 8, 23, 47, 99, 151, 203, 255, 307, 326, 359, 375, 411, 614, 817, 1020, 1083, 1223, 1286, 1426, 1629, 1832, 2035, 2441, 2504, 2644, 2847, 3050, 3253, 3319, 3456, 3522, 3659, 3715, 3722, 3862, 3915, 4065, 4118, 4380, 4435, 4470] :=
  ⟨Fin 23, { op := fun x y => 2 * x + 7 * y }, Finite.of_fintype _, by ringFin; decideFin!⟩

@[equational_result]
theorem LinearInvariance26 : ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [1279, 1286, 1288] [3, 8, 23, 47, 99, 151, 203, 255, 307, 326, 359, 375, 411, 614, 817, 1020, 1083, 1426, 1629, 1832, 2035, 2238, 2301, 2441, 2504, 2644, 2847, 3050, 3253, 3319, 3456, 3522, 3659, 3715, 3722, 3862, 3915, 4065, 4118, 4380, 4435, 4470] :=
  ⟨Fin 11, { op := fun x y => 1 * x + 7 * y }, Finite.of_fintype _, by decideFin!⟩
