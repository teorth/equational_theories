
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3,2,0,1],[2,3,1,0],[2,3,1,0],[3,2,0,1]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[3,2,0,1],[2,3,1,0],[2,3,1,0],[3,2,0,1]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[3,2,0,1],[2,3,1,0],[2,3,1,0],[3,2,0,1]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[3,2,0,1],[2,3,1,0],[2,3,1,0],[3,2,0,1]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [528, 575, 1137, 1171, 1184, 1949, 1983, 1996] [8, 23, 614, 817, 1223, 1426, 1543, 1577, 1590, 1629, 2035, 2053, 2060, 2090, 2097, 2124, 2137, 2238, 2441, 2592, 2605, 2644, 2847, 3050, 3075, 3105, 3112, 3139, 3152, 3253, 3456, 3591, 3617, 3659, 3862, 4622] :=
    ⟨Fin 4, «FinitePoly [[3,2,0,1],[2,3,1,0],[2,3,1,0],[3,2,0,1]]», by decideFin!⟩
