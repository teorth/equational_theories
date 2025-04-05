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



theorem not_817 : ∃ (G: Type) (_: Magma G), Equation1729 G ∧ ¬ Equation817 G := by
  let β := N ⊕ N ⊕ (N × N)
  let task : β → Set PartialSolution := fun s => match s with
    | Sum.inl x => { sol | x ∈ fill sol.Predom_L₀' }
    | Sum.inr (Sum.inl x) => { sol | x ∈ sol.Dom_S' }
    | Sum.inr (Sum.inr (x,y)) => { sol | (x,y) ∈ sol.Dom_op }
  have := exists_greedy_chain task ?_ TrivialPartialSolution
  . obtain ⟨ sols, hchain, hnon, _, h ⟩ := this
    apply use_chain hchain
    . rw [nonempty_subtype]
      use TrivialPartialSolution
    . intro x
      exact h (Sum.inl x)
    . intro x
      exact h (Sum.inr (Sum.inl x))
    intro x y
    exact h (Sum.inr (Sum.inr (x,y)))
  intro sol b
  match b with
  | Sum.inl x =>
      simp only [Set.mem_setOf_eq, task]
      exact enlarge_L₀' sol x
  | Sum.inr (Sum.inl x) =>
      simp only [Set.mem_setOf_eq, task]
      exact enlarge_S' sol x
  | Sum.inr (Sum.inr (x,y)) =>
      simp only [Set.mem_setOf_eq, task]
      exact enlarge_op sol x y

end Eq1729
