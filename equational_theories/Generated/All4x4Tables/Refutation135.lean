import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[2,0,1,0],[1,3,1,1],[2,2,3,2],[3,3,3,3]]
-/
set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[2,0,1,0],[1,3,1,1],[2,2,3,2],[3,3,3,3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[2,0,1,0],[1,3,1,1],[2,2,3,2],[3,3,3,3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[2,0,1,0],[1,3,1,1],[2,2,3,2],[3,3,3,3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [843,1039] [8,10,11,99,100,101,104,105,106,107,108,109,110,111,411,414,436,440,444,818,820,823,1036,1832,1861,3253,3319,3659,3862,3915] :=
    ⟨Fin 4, «FinitePoly [[2,0,1,0],[1,3,1,1],[2,2,3,2],[3,3,3,3]]», by decideFin!⟩
