import equational_theories.ManuallyProved.Equation1729.ExtensionTheorem


namespace Eq1729

theorem ExtMagma_shows_1729_not_implies_817 {SM N : Type} [Magma SM]
  (E : ExtOpsWithProps SM N)
  : @Equation1729 (SM ⊕ N) (extMagmaInst E) ∧ ¬@Equation817 (SM ⊕ N) (extMagmaInst E) := by
  constructor
  . apply ExtMagma_sat_eq1729
  · apply ExtMagma_unsat_eq817

end Eq1729
