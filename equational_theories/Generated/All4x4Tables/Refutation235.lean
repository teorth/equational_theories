
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3, 0, 3, 1], [3, 2, 3, 1], [0, 2, 3, 1], [3, 2, 3, 1]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[3, 0, 3, 1], [3, 2, 3, 1], [0, 2, 3, 1], [3, 2, 3, 1]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[3, 0, 3, 1], [3, 2, 3, 1], [0, 2, 3, 1], [3, 2, 3, 1]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[3, 0, 3, 1], [3, 2, 3, 1], [0, 2, 3, 1], [3, 2, 3, 1]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [1, 52, 361, 619, 635, 639, 3877, 3887, 4073, 4090, 4584] [8, 49, 55, 62, 65, 72, 75, 364, 367, 375, 378, 385, 411, 622, 642, 649, 666, 669, 676, 679, 703, 706, 713, 716, 819, 825, 835, 845, 869, 872, 879, 882, 906, 909, 916, 919, 1020, 1832, 2035, 3253, 3456, 3880, 3890, 3897, 3915, 3918, 3925, 3928, 3952, 3955, 3962, 4118, 4131] :=
    ⟨Fin 4, «FinitePoly [[3, 0, 3, 1], [3, 2, 3, 1], [0, 2, 3, 1], [3, 2, 3, 1]]», by decideFin!⟩
