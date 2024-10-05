
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[1,1,2,1],[3,3,3,3],[1,1,1,1],[0,2,2,2]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[1,1,2,1],[3,3,3,3],[1,1,1,1],[0,2,2,2]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[1,1,2,1],[3,3,3,3],[1,1,1,1],[0,2,2,2]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[1,1,2,1],[3,3,3,3],[1,1,1,1],[0,2,2,2]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [309, 2868, 3460] [263, 2035, 2659, 2662, 2669, 2672, 2852, 2855, 2872, 2875, 3258, 3309, 3316, 3319, 3509, 3512, 3519, 3522, 3659, 3862, 4065, 4268, 4284, 4314, 4380, 4599, 4605, 4608, 4631, 4658] :=
    ⟨Fin 4, «FinitePoly [[1,1,2,1],[3,3,3,3],[1,1,1,1],[0,2,2,2]]», by decideFin!⟩
