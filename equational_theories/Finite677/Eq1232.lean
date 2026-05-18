import Mathlib.Data.Finite.Prod
import Mathlib.Data.ZMod.Basic
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import Mathlib.Tactic.Module

/-!
The goal of this file is to construct a finite magma satisfying Eq677 and Eq1232, but not Eq4293.
At the moment, the smallest size known is 31^3, which is to large for a representation via a
multiplication table. Instead we construct an extension over the linear model of size 31 that
satisfies Eq1232.
-/

namespace Eq1232

private abbrev B := ZMod 31

/-! matrix with minimal polynomial a^2 - 2*a + 3 -/
private def a : Fin 2 -> Fin 2 -> B
| 0, 0 => 0
| 0, 1 => 28
| 1, 0 => 1
| 1, 1 => 2

/-! poor man's identity matrix -/
private def i : Fin 2 -> Fin 2 -> B
| 0, 0 | 1, 1 => 1
| _, _ => 0

/-! cubic residue class in B-/
def c : B -> Fin 4
| 1 | 2 | 4 | 8 | 15 | 16 | 23 | 27 | 29 | 30 => 1
| 3 | 6 | 7 | 12 | 14 | 17 | 19 | 24 | 25 | 28 => 2
| 5 | 9 | 10 | 11 | 13 | 18 | 20 | 21 | 22 | 26  => 3
| _ => 0 /- this should only be 0, but this way it is easier to prove completeness-/

def cycle : Fin 4 → Fin 4
| 0 => 0
| 1 => 3
| 2 => 1
| 3 => 2

private def f : Fin 4 → Fin 2 -> Fin 2 -> B
| 1  => -15*a + 1*i
| 2 => 3*a + 2*i
| 3  => 12*a - 2*i
| 0  => 5*i

private def g : Fin 4 → Fin 2 -> Fin 2 -> B
| 1  => -12*a + 10*i
| 2 => 13*a + 12*i
| 3  => -5*a + 12*i
| 0  => -4*i

private def baseop (x y : B) : B := 5*x - 4*y

private instance instanceBaseMagma : Magma B where
  op := baseop

private lemma baseop_def (x y : B) : x ◇ y = 5*x - 4*y := rfl

theorem base677 : Equation677 B := fun x y => by
  simp only [baseop_def]
  grind

theorem base264 : Equation264 B := fun x y => by
  simp only [baseop_def]
  grind

lemma base_color1 (x y : B) : c ((x ◇ y) - x) = c (x - y) := by
  have : (x ◇ y) - x = 4 * (x - y) := by grind [baseop_def]
  rw [this]
  generalize (x - y) = t
  fin_cases t <;> grind [c]

lemma base_color2 (x y : B) : c (x - ((y ◇ x) ◇ y)) = cycle (c (y - x)) := by
  have : x - ((y ◇ x) ◇ y) = -21 * (y - x) := by grind [baseop_def]
  rw [this]
  generalize (y - x) = t
  fin_cases t <;> grind [c, cycle]

lemma base_color3 (x y : B) : c (y - (x ◇ ((y ◇ x) ◇ y))) = c (y - x) := by
  have : y - (x ◇ ((y ◇ x) ◇ y)) = 85 * (y - x) := by grind [baseop_def]
  rw [this]
  generalize (y - x) = t
  fin_cases t <;> grind [c, cycle]

lemma base_color4 (x y : B) : c ((x ◇ y) - y) = cycle (c (x - y)) := by
  have : (x ◇ y) - y = 5 * (x - y) := by grind [baseop_def]
  rw [this]
  generalize (x - y) = t
  fin_cases t <;> grind [c, cycle]


private def op : (B × B × B) → (B × B × B) → (B × B × B)
| (x, s0, s1), (y, t0, t1) => (x ◇ y,
  f (c (x - y)) 0 0 * s0 + f (c (x - y)) 0 1 * s1 + g (c (x - y)) 0 0 * t0 + g (c (x - y)) 0 1 * t1,
  f (c (x - y)) 1 0 * s0 + f (c (x - y)) 1 1 * s1 + g (c (x - y)) 1 0 * t0 + g (c (x - y)) 1 1 * t1,
  )

@[reducible]
private instance Magma_677_31_pow_3 : Magma (B × B × B) where
  op := op

@[simp]
lemma Magma_677_31_pow_3_op_def (x y : B) (s0 s1 t0 t1 : B) :
    (x, s0, s1) ◇ (y, t0, t1) = (x ◇ y,
    f (c (x - y)) 0 0 * s0 + f (c (x - y)) 0 1 * s1 + g (c (x - y)) 0 0 * t0 + g (c (x - y)) 0 1 * t1,
    f (c (x - y)) 1 0 * s0 + f (c (x - y)) 1 1 * s1 + g (c (x - y)) 1 0 * t0 + g (c (x - y)) 1 1 * t1) := rfl

lemma Magma_677_31_pow_3_idem : Equation3 (B × B × B) := fun (x, s0, s1) => by
  simp only [Magma_677_31_pow_3_op_def, baseop_def, f, c, sub_self, Fin.isValue, Pi.mul_apply,
    Pi.ofNat_apply, i, mul_one, mul_zero, zero_mul, add_zero, g, Pi.neg_apply, neg_mul, zero_add,
    Prod.mk.injEq]
  grind

lemma Magma_677_31_pow_3_677 : Equation677 (B × B × B) := fun (x, s0, s1) (y, t0, t1) => by
  simp only [Magma_677_31_pow_3_op_def, base_color1, base_color2, base_color3]
  generalize c (y - x) = color
  simp only [← base677 x y, Prod.mk.injEq, true_and]
  fin_cases color <;> simp [f, g, cycle, i, a] <;> grind

lemma Magma_677_31_pow_3_264 : Equation264 (B × B × B) := fun (x, s0, s1) (y, t0, t1) => by
  simp only [Magma_677_31_pow_3_op_def, base_color4]
  generalize c (x - y) = color
  simp only [← base264 x y, Prod.mk.injEq, true_and]
  fin_cases color <;> simp [f, g, cycle, i, a] <;> grind

@[equational_result]
theorem Magma_677_31_pow_3_facts : ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G
    [3, 264, 677, 1232]
    [4293] := by
  refine ⟨B × B × B, Magma_677_31_pow_3, Finite.of_fintype _, Magma_677_31_pow_3_idem,
  Magma_677_31_pow_3_264, Magma_677_31_pow_3_677, fun a b => ?_, fun h => ?_⟩
  · rw [← Magma_677_31_pow_3_264, ← Magma_677_31_pow_3_idem]
  · specialize h (0,1,0) (1,0,1)
    revert h
    decide

end Eq1232
