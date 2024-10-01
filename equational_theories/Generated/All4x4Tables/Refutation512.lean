
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3, 2, 3, 3], [3, 3, 3, 3], [0, 3, 1, 3], [3, 3, 3, 3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[3, 2, 3, 3], [3, 3, 3, 3], [0, 3, 1, 3], [3, 3, 3, 3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[3, 2, 3, 3], [3, 3, 3, 3], [0, 3, 1, 3], [3, 3, 3, 3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[3, 2, 3, 3], [3, 3, 3, 3], [0, 3, 1, 3], [3, 3, 3, 3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [4467] [4268, 4275, 4283, 4291, 4293, 4382, 4386, 4398, 4399, 4405, 4406, 4435, 4443, 4539, 4584, 4588, 4629, 4635, 4636] :=
    ⟨Fin 4, «FinitePoly [[3, 2, 3, 3], [3, 3, 3, 3], [0, 3, 1, 3], [3, 3, 3, 3]]», by decideFin!⟩
