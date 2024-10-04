
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,2,1,4,3],[2,3,0,1,4],[1,0,4,3,2],[4,1,3,2,0],[3,4,2,0,1]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,2,1,4,3],[2,3,0,1,4],[1,0,4,3,2],[4,1,3,2,0],[3,4,2,0,1]]» : Magma (Fin 5) where
  op := memoFinOp fun x y => [[0,2,1,4,3],[2,3,0,1,4],[1,0,4,3,2],[4,1,3,2,0],[3,4,2,0,1]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,2,1,4,3],[2,3,0,1,4],[1,0,4,3,2],[4,1,3,2,0],[3,4,2,0,1]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [14, 492, 522, 572, 684, 711, 725, 759, 1165, 1181, 1293, 1304, 1320, 1504, 1507, 1561, 1699, 1943, 2170, 2180, 2196, 2335, 2349, 2399, 2519, 2522, 2917, 2925, 2944, 2958, 3120, 3131, 3211, 3364, 3601, 4007, 4162, 4216] [817, 2644, 3659, 4098] :=
    ⟨Fin 5, «FinitePoly [[0,2,1,4,3],[2,3,0,1,4],[1,0,4,3,2],[4,1,3,2,0],[3,4,2,0,1]]», by decideFin!⟩
