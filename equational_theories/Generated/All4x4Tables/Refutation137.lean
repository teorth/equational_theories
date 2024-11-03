
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,0,0],[1,0,0],[2,0,1]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,0,0],[1,0,0],[2,0,1]]» : Magma (Fin 3) where
  op := memoFinOp fun x y => [[0,0,0],[1,0,0],[2,0,1]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,0,0],[1,0,0],[2,0,1]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [832, 833, 836, 1035, 1038, 1048, 1240, 1243, 1244, 1245, 1250, 1254, 1255, 1259, 1262, 1263] [411, 818, 819, 842, 843, 845, 1022, 1023, 1028, 1036, 1039, 1046, 1229, 1832, 3253, 3659, 3862, 4065, 4269, 4270, 4293, 4314, 4583, 4606, 4608, 4622, 4631, 4636, 4647] :=
    ⟨Fin 3, «FinitePoly [[0,0,0],[1,0,0],[2,0,1]]», Finite.of_fintype _, by decideFin!⟩
