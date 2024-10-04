
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3,2,0,1],[2,3,1,0],[0,1,2,3],[0,1,2,3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[3,2,0,1],[2,3,1,0],[0,1,2,3],[0,1,2,3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[3,2,0,1],[2,3,1,0],[0,1,2,3],[0,1,2,3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[3,2,0,1],[2,3,1,0],[0,1,2,3],[0,1,2,3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [2592, 2808, 2964, 2998, 3011, 3201, 3214] [419, 429, 436, 466, 473, 500, 614, 817, 1028, 1038, 1045, 1075, 1082, 1109, 1223, 1426, 1647, 1654, 1684, 1691, 1840, 1850, 1857, 1887, 1894, 1921, 2035, 3253, 3474, 3481, 3549, 3556, 3667, 3677, 3725, 3752, 3862, 4073, 4083, 4131, 4158, 4275, 4380, 4635] :=
    ⟨Fin 4, «FinitePoly [[3,2,0,1],[2,3,1,0],[0,1,2,3],[0,1,2,3]]», by decideFin!⟩
