import equational_theories.ManuallyProved.Equation1729.ExtensionTheorem
import equational_theories.ManuallyProved.Equation1729.SmallMagma
import equational_theories.ManuallyProved.Equation1729.MagmaConstruction
import Mathlib.Algebra.DirectSum.Basic
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.Data.ZMod.Defs
import Mathlib.Data.Countable.Defs

import equational_theories.Equations.All


namespace Eq1729

theorem ExtMagma_shows_1729_not_implies_817 {SM N : Type} [Magma SM]
  (E : ExtOpsWithProps SM N)
  : @Equation1729 (SM ⊕ N) (extMagmaInst E) ∧ ¬@Equation817 (SM ⊕ N) (extMagmaInst E) := by
  constructor
  . apply ExtMagma_sat_eq1729
  · apply ExtMagma_unsat_eq817


theorem not_817 : ∃ (G: Type) (_: Magma G), Equation1729 G ∧ ¬ Equation817 G := by sorry

end Eq1729
