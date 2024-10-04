
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3,1,0,1],[2,2,1,2],[2,2,2,2],[2,2,3,2]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[3,1,0,1],[2,2,1,2],[2,2,2,2],[2,2,3,2]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[3,1,0,1],[2,2,1,2],[2,2,2,2],[2,2,3,2]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[3,1,0,1],[2,2,1,2],[2,2,2,2],[2,2,3,2]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [837, 847, 1051, 1052, 1240, 1243, 1245, 1254, 1259, 1263] [411, 819, 820, 823, 832, 833, 842, 843, 1023, 1025, 1028, 1036, 1039, 1226, 1229, 1231, 1832, 3253, 3659, 3862, 4065, 4270, 4583, 4631] :=
    ⟨Fin 4, «FinitePoly [[3,1,0,1],[2,2,1,2],[2,2,2,2],[2,2,3,2]]», by decideFin!⟩
