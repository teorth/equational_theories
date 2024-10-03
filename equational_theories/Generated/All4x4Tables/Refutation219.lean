import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3,1,3,3],[2,2,2,1],[0,1,1,1],[0,0,2,0]]
-/
set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[3,1,3,3],[2,2,2,1],[0,1,1,1],[0,0,2,0]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[3,1,3,3],[2,2,2,1],[0,1,1,1],[0,0,2,0]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[3,1,3,3],[2,2,2,1],[0,1,1,1],[0,0,2,0]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [1849] [153,205,308,326,1630,1631,1632,1633,1634,1636,1637,1640,1834,1837,1838,1839,1840,1843,1850,1853,2240,2246,2249,2253,2452,2459,2462,3254,3256,3257,3258,3316,3318,3319,3320,3322,3460,3462,3463,4120,4121,4127,4130,4131,4268,4282,4283,4286,4598,4599,4629,4673] :=
    ⟨Fin 4, «FinitePoly [[3,1,3,3],[2,2,2,1],[0,1,1,1],[0,0,2,0]]», by decideFin!⟩
