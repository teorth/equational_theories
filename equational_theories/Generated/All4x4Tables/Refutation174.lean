
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3, 2, 3, 3], [3, 3, 2, 2], [1, 1, 3, 1], [3, 3, 3, 3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[3, 2, 3, 3], [3, 3, 2, 2], [1, 1, 3, 1], [3, 3, 3, 3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[3, 2, 3, 3], [3, 3, 2, 2], [1, 1, 3, 1], [3, 3, 3, 3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[3, 2, 3, 3], [3, 3, 2, 2], [1, 1, 3, 1], [3, 3, 3, 3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [368, 4113, 4288] [8, 99, 361, 362, 364, 365, 375, 377, 378, 385, 411, 817, 1020, 1223, 1832, 3253, 3667, 3675, 3721, 3725, 3862, 4071, 4083, 4380, 4584, 4588, 4598, 4606, 4636] :=
    ⟨Fin 4, «FinitePoly [[3, 2, 3, 3], [3, 3, 2, 2], [1, 1, 3, 1], [3, 3, 3, 3]]», by decideFin!⟩
