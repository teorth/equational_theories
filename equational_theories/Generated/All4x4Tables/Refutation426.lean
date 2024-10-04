
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3,3,1,3],[3,3,3,3],[3,3,0,3],[3,3,0,3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[3,3,1,3],[3,3,3,3],[3,3,0,3],[3,3,0,3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[3,3,1,3],[3,3,3,3],[3,3,0,3],[3,3,0,3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[3,3,1,3],[3,3,3,3],[3,3,0,3],[3,3,0,3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [3909, 4352] [43, 359, 3253, 3380, 3456, 3588, 3591, 3601, 3607, 3659, 3769, 3776, 3786, 4065, 4096, 4098, 4100, 4104, 4118, 4128, 4131, 4155, 4165, 4175, 4584, 4622] :=
    ⟨Fin 4, «FinitePoly [[3,3,1,3],[3,3,3,3],[3,3,0,3],[3,3,0,3]]», by decideFin!⟩
