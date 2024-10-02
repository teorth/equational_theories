
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3, 1, 0, 3], [3, 3, 2, 3], [3, 0, 3, 1], [0, 1, 2, 3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[3, 1, 0, 3], [3, 3, 2, 3], [3, 0, 3, 1], [0, 1, 2, 3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[3, 1, 0, 3], [3, 3, 2, 3], [3, 0, 3, 1], [0, 1, 2, 3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[3, 1, 0, 3], [3, 3, 2, 3], [3, 0, 3, 1], [0, 1, 2, 3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [1, 31, 208, 211, 221, 2530, 2571, 2724, 3500, 4098] [218, 231, 307, 2238, 2449, 2506, 2554, 2672, 3115, 3253, 3722, 4128] :=
    ⟨Fin 4, «FinitePoly [[3, 1, 0, 3], [3, 3, 2, 3], [3, 0, 3, 1], [0, 1, 2, 3]]», by decideFin!⟩
