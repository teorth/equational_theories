
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3,1,3,1],[3,3,3,3],[1,3,3,0],[3,3,3,3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[3,1,3,1],[3,3,3,3],[1,3,3,0],[3,3,3,3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[3,1,3,1],[3,3,3,3],[1,3,3,0],[3,3,3,3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[3,1,3,1],[3,3,3,3],[1,3,3,0],[3,3,3,3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [4103] [3664, 3667, 3668, 3674, 3675, 3678, 3863, 3865, 3868, 3871, 3877, 3880, 3887, 3890, 4629] :=
    ⟨Fin 4, «FinitePoly [[3,1,3,1],[3,3,3,3],[1,3,3,0],[3,3,3,3]]», by decideFin!⟩
