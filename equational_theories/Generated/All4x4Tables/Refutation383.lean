
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3,2,0,1],[3,3,0,2],[1,3,3,2],[0,1,2,3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[3,2,0,1],[3,3,0,2],[1,3,3,2],[0,1,2,3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[3,2,0,1],[3,3,0,2],[1,3,3,2],[0,1,2,3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[3,2,0,1],[3,3,0,2],[1,3,3,2],[0,1,2,3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [2998] [2238, 2449, 2459, 2503, 2530, 2669, 2699, 2855, 2936, 3068, 3075, 3105, 3112, 4320] :=
    ⟨Fin 4, «FinitePoly [[3,2,0,1],[3,3,0,2],[1,3,3,2],[0,1,2,3]]», by decideFin!⟩
