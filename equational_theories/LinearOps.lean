import Mathlib.Tactic
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang
import equational_theories.EquationalResult

/-!
Refutations found by interepeting the magma operation as a linear operation
`x ◇ y = ax + by` and then solving for `a` and `b`.

Discussed on Zulip here:
https://leanprover.zulipchat.com/#narrow/stream/458659-Equational/topic/An.20old.20new.20idea/near/475038501
-/

namespace LinearOps

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
theorem Equation1286_not_implies_Equation3 : ∃ (G : Type) (_ : Magma G), Facts G [1279, 1286] [3, 8, 23, 47, 99, 151, 203, 255, 326, 359, 375, 411, 614, 817, 1020, 1083, 1426, 1629, 1832, 2035, 2238, 2301, 2441, 2504, 2644, 2847, 3050, 3253, 3319, 3456, 3522, 3659, 3715, 3722, 3862, 3915, 4065, 4118, 4380, 4435, 4470] :=
  ⟨ZMod 11, { op := fun x y => 1 * x + 7 * y }, by decide!⟩

/-- Dual of the above. -/
@[equational_result]
theorem Equation2301_not_implies_Equation3 : ∃ (G : Type) (_ : Magma G), Facts G [2328, 2301] [3, 8, 23, 47, 99, 151, 203, 255, 307, 326, 359, 375, 411, 614, 817, 1020, 1083, 1223, 1426, 1629, 1832, 2035, 2441, 2504, 2644, 2847, 3050, 3253, 3319, 3456, 3522, 3659, 3715, 3722, 3862, 3915, 4065, 4118, 4380, 4435, 4470] :=
  ⟨ZMod 11, { op := fun x y => 7 * x + 1 * y }, by decide!⟩

@[equational_result]
theorem Equation3116_not_implies_Equation513 : ∃ (G : Type) (_ : Magma G), Facts G [3116] [513] :=
  ⟨ZMod 11, { op := fun x y => 3 * x + 9 * y }, by decide!⟩

-- dual of the above
@[equational_result]
theorem Equation511_not_implies_Equation3079 : ∃ (G : Type) (_ : Magma G), Facts G [511] [3079] :=
  ⟨ZMod 11, { op := fun x y => 9 * x + 3 * y }, by decide!⟩
