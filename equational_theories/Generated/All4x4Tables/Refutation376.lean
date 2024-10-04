
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3,1,1,3],[3,1,1,3],[1,3,0,1],[3,1,1,3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[3,1,1,3],[3,1,1,3],[1,3,0,1],[3,1,1,3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[3,1,1,3],[3,1,1,3],[1,3,0,1],[3,1,1,3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[3,1,1,3],[3,1,1,3],[1,3,0,1],[3,1,1,3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [4428] [4269, 4272, 4284, 4291, 4435, 4442, 4445, 4470, 4473, 4480] :=
    ⟨Fin 4, «FinitePoly [[3,1,1,3],[3,1,1,3],[1,3,0,1],[3,1,1,3]]», by decideFin!⟩
