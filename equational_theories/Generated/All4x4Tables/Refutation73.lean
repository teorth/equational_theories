import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[2,2,2,3],[2,3,2,3],[0,1,2,3],[0,1,2,3]]
-/
set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[2,2,2,3],[2,3,2,3],[0,1,2,3],[0,1,2,3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[2,2,2,3],[2,3,2,3],[0,1,2,3],[0,1,2,3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[2,2,2,3],[2,3,2,3],[0,1,2,3],[0,1,2,3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [242,312,1724,2389,2420,2425,2517,2536,2623,2712,3145,3180] [309,3255,3261,3264,3271,3274,3467,3481,3677,4131,4269,4316,4320,4327,4362] :=
    ⟨Fin 4, «FinitePoly [[2,2,2,3],[2,3,2,3],[0,1,2,3],[0,1,2,3]]», by decideFin!⟩
