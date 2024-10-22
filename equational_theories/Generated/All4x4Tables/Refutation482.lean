
import Mathlib.Data.Finite.Basic
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[1,2,3,0,4],[2,4,1,3,0],[3,1,0,4,2],[0,3,4,2,1],[4,0,2,1,3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[1,2,3,0,4],[2,4,1,3,0],[3,1,0,4,2],[0,3,4,2,1],[4,0,2,1,3]]» : Magma (Fin 5) where
  op := memoFinOp fun x y => [[1,2,3,0,4],[2,4,1,3,0],[3,1,0,4,2],[0,3,4,2,1],[4,0,2,1,3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[1,2,3,0,4],[2,4,1,3,0],[3,1,0,4,2],[0,3,4,2,1],[4,0,2,1,3]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [467, 679, 1085, 1322, 2247, 2467, 2873, 3140] [47, 99, 151, 203, 255, 413, 416, 417, 426, 440, 476, 503, 619, 620, 633, 642, 670, 704, 817, 1028, 1035, 1038, 1045, 1048, 1075, 1112, 1241, 1251, 1285, 1315, 1426, 1629, 1832, 2035, 2240, 2244, 2246, 2256, 2264, 2443, 2449, 2457, 2459, 2460, 2644, 2852, 2875, 2903, 2909, 2937, 2939, 3058, 3066, 3075, 3253, 3456, 3862, 4065, 4268, 4269, 4272, 4273, 4275, 4284, 4291, 4314, 4320, 4584, 4585, 4587, 4590, 4591, 4598, 4599, 4606] :=
    ⟨Fin 5, «FinitePoly [[1,2,3,0,4],[2,4,1,3,0],[3,1,0,4,2],[0,3,4,2,1],[4,0,2,1,3]]», Finite.of_fintype _, by decideFin!⟩
