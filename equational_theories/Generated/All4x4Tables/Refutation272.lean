import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[2,1,1,1],[3,0,0,3],[0,0,3,0],[2,2,2,1]]
-/
set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[2,1,1,1],[3,0,0,3],[0,0,3,0],[2,2,2,1]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[2,1,1,1],[3,0,0,3],[0,0,3,0],[2,2,2,1]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[2,1,1,1],[3,0,0,3],[0,0,3,0],[2,2,2,1]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [1630,1631,1633] [151,152,203,205,307,308,326,1426,1427,1428,1429,1430,1832,1833,1837,1838,1839,1850,2238,2240,2243,2246,2249,2443,2446,2449,2452,3253,3254,3255,3256,3257,3318,3319,3320,3457,3458,3459,3460,3511,4120,4127,4131,4598,4673] :=
    ⟨Fin 4, «FinitePoly [[2,1,1,1],[3,0,0,3],[0,0,3,0],[2,2,2,1]]», by decideFin!⟩
