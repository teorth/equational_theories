import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[1,2,1,1],[3,3,3,2],[0,1,2,3],[2,0,0,0]]
-/
set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[1,2,1,1],[3,3,3,2],[0,1,2,3],[2,0,0,0]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[1,2,1,1],[3,3,3,2],[0,1,2,3],[2,0,0,0]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[1,2,1,1],[3,3,3,2],[0,1,2,3],[2,0,0,0]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [2044] [255,258,263,307,326,2051,2053,2060,2644,2653,2663,2670,2672,2847,2850,2853,2863,2875,3259,3319,3459,3518,3522,3526,4585,4656] :=
    ⟨Fin 4, «FinitePoly [[1,2,1,1],[3,3,3,2],[0,1,2,3],[2,0,0,0]]», by decideFin!⟩
