
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0, 0, 3, 1], [1, 1, 1, 1], [1, 2, 1, 2], [0, 3, 3, 1]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0, 0, 3, 1], [1, 1, 1, 1], [1, 2, 1, 2], [0, 3, 3, 1]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[0, 0, 3, 1], [1, 1, 1, 1], [1, 2, 1, 2], [0, 3, 3, 1]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0, 0, 3, 1], [1, 1, 1, 1], [1, 2, 1, 2], [0, 3, 3, 1]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [1, 10, 99, 378, 413, 426, 429, 820, 834, 838, 1031, 1041, 1051, 1055, 1059, 1063, 1225, 1228, 1231, 1238, 1241, 1248, 1251, 1834, 1847, 1850, 3255, 3316, 3661, 3662, 3724, 3725, 3867, 3870, 3925, 3928, 4269] [13, 105, 821, 823, 836, 1023, 1229, 1239, 1242, 1249, 3943] :=
    ⟨Fin 4, «FinitePoly [[0, 0, 3, 1], [1, 1, 1, 1], [1, 2, 1, 2], [0, 3, 3, 1]]», by decideFin!⟩
