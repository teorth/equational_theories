
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3, 2, 2, 3], [3, 3, 3, 3], [0, 3, 3, 3], [0, 1, 2, 3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[3, 2, 2, 3], [3, 3, 3, 3], [0, 3, 3, 3], [0, 1, 2, 3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[3, 2, 2, 3], [3, 3, 3, 3], [0, 3, 3, 3], [0, 1, 2, 3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[3, 2, 2, 3], [3, 3, 3, 3], [0, 3, 3, 3], [0, 1, 2, 3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [1, 25, 31, 224, 242, 246, 319, 323, 1672, 1724, 2376, 2420, 2425, 2430, 2558, 3145, 3197, 3289, 3489, 3529, 3769, 3786, 4098, 4105, 4362, 4611] [2536, 2712, 3078, 3105, 3471, 4155] :=
    ⟨Fin 4, «FinitePoly [[3, 2, 2, 3], [3, 3, 3, 3], [0, 3, 3, 3], [0, 1, 2, 3]]», by decideFin!⟩
