import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,3,0,3],[3,1,1,3],[0,1,0,3],[3,3,3,3]]
-/
set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,3,0,3],[3,1,1,3],[0,1,0,3],[3,3,3,3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[0,3,0,3],[3,1,1,3],[0,1,0,3],[3,3,3,3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,3,0,3],[3,1,1,3],[0,1,0,3],[3,3,3,3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [333,335,377,384,3318] [326,375,3319,3352,3522,3558,3715,3721,3748,3759,3761,3915,3951,4118,4164,4290,4369,4408,4470,4479,4605,4684] :=
    ⟨Fin 4, «FinitePoly [[0,3,0,3],[3,1,1,3],[0,1,0,3],[3,3,3,3]]», by decideFin!⟩
