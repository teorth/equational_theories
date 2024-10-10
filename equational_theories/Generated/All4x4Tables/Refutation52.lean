
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3,0,1,1],[1,1,1,1],[1,2,0,1],[0,3,1,2]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[3,0,1,1],[1,1,1,1],[1,2,0,1],[0,3,1,2]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[3,0,1,1],[1,1,1,1],[1,2,0,1],[0,3,1,2]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[3,0,1,1],[1,1,1,1],[1,2,0,1],[0,3,1,2]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [1035, 1050] [99, 151, 203, 255, 411, 614, 817, 1023, 1028, 1029, 1036, 1038, 1039, 1045, 1046, 1223, 1426, 1629, 1832, 2035, 2238, 2441, 2644, 2847, 3050, 3253, 3456, 3659, 3862, 4065, 4268, 4269, 4270, 4283, 4284, 4314, 4380, 4583, 4584, 4585, 4598, 4599, 4629] :=
    ⟨Fin 4, «FinitePoly [[3,0,1,1],[1,1,1,1],[1,2,0,1],[0,3,1,2]]», by decideFin!⟩
