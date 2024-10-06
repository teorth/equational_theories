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
theorem Equation1286_not_implies_Equation3 : ∃ (G : Type) (_ : Magma G), Facts G [1286] [3] := by
  refine ⟨ZMod 11, { op := fun x y => 1 * x + 7 * y }, ?_, ?_⟩
  · simp only [Equation1286]
    intro x y
    ring_nf
    reduce_mod_char
  · simp only [Equation3, one_mul, self_eq_add_right, not_forall]
    use 1
    ring_nf
    decide

/-- Dual of the above. -/
@[equational_result]
theorem Equation2301_not_implies_Equation3 : ∃ (G : Type) (_ : Magma G), Facts G [2301] [3] := by
  refine ⟨ZMod 11, { op := fun x y => 7 * x + 1 * y }, ?_, ?_⟩
  · simp only [Equation2301]
    intro x y
    ring_nf
    reduce_mod_char
  · simp only [Equation3, one_mul, self_eq_add_right, not_forall]
    use 1
    ring_nf
    decide
