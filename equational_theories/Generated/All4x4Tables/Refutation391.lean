
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3, 3, 1, 3], [3, 3, 3, 3], [3, 0, 3, 0], [3, 3, 3, 3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[3, 3, 1, 3], [3, 3, 3, 3], [3, 0, 3, 0], [3, 3, 3, 3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[3, 3, 1, 3], [3, 3, 3, 3], [3, 0, 3, 0], [3, 3, 3, 3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[3, 3, 1, 3], [3, 3, 3, 3], [3, 0, 3, 0], [3, 3, 3, 3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [3285, 3710, 4116] [8, 99, 307, 378, 411, 817, 1020, 1223, 1832, 3258, 3259, 3261, 3262, 3268, 3269, 3271, 3272, 3315, 3316, 3318, 3319, 3456, 3721, 3725, 3862, 4131, 4272, 4276, 4343, 4380, 4636] :=
    ⟨Fin 4, «FinitePoly [[3, 3, 1, 3], [3, 3, 3, 3], [3, 0, 3, 0], [3, 3, 3, 3]]», by decideFin!⟩
