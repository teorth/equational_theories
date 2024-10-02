
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0, 0, 2, 1], [3, 1, 0, 3], [2, 2, 3, 0], [1, 3, 1, 2]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0, 0, 2, 1], [3, 1, 0, 3], [2, 2, 3, 0], [1, 3, 1, 2]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[0, 0, 2, 1], [3, 1, 0, 3], [2, 2, 3, 0], [1, 3, 1, 2]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0, 0, 2, 1], [3, 1, 0, 3], [2, 2, 3, 0], [1, 3, 1, 2]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [47, 160, 212, 1223, 3079] [8, 48, 49, 50, 52, 53, 55, 56, 62, 63, 65, 66, 72, 73, 75, 152, 166, 167, 204, 205, 206, 208, 209, 211, 218, 219, 221, 222, 228, 229, 231, 255, 411, 1020, 1226, 1229, 1231, 1252, 1426, 1629, 1832, 2035, 3053, 3058, 3066, 3075, 3253, 3456, 3862, 4065, 4380] :=
    ⟨Fin 4, «FinitePoly [[0, 0, 2, 1], [3, 1, 0, 3], [2, 2, 3, 0], [1, 3, 1, 2]]», by decideFin!⟩
