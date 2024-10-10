
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3,3,0,3],[3,3,1,3],[2,2,3,3],[3,3,3,3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[3,3,0,3],[3,3,1,3],[2,2,3,3],[3,3,3,3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[3,3,0,3],[3,3,1,3],[2,2,3,3],[3,3,3,3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[3,3,0,3],[3,3,1,3],[2,2,3,3],[3,3,3,3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [3490, 3889, 4417] [3461, 3475, 3868, 3880, 4269, 4273, 4283, 4291, 4321, 4399, 4405, 4433, 4435, 4442, 4443, 4445, 4635, 4656, 4666] :=
    ⟨Fin 4, «FinitePoly [[3,3,0,3],[3,3,1,3],[2,2,3,3],[3,3,3,3]]», by decideFin!⟩
