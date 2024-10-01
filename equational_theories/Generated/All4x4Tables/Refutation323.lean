
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3, 1, 0, 3], [3, 3, 2, 3], [3, 0, 3, 1], [0, 1, 2, 3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[3, 1, 0, 3], [3, 3, 2, 3], [3, 0, 3, 1], [0, 1, 2, 3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[3, 1, 0, 3], [3, 3, 2, 3], [3, 0, 3, 1], [0, 1, 2, 3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[3, 1, 0, 3], [3, 3, 2, 3], [3, 0, 3, 1], [0, 1, 2, 3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [1, 31, 208, 211, 221, 1637, 1718, 1731, 2530, 2543, 2571, 2662, 2724, 2733, 2746, 3058, 3139, 3152, 3500, 3509, 3692, 3700, 4098, 4165, 4341, 4590] [218, 231, 307, 2238, 2449, 2506, 2554, 2672, 3115, 3253, 4128] :=
    ⟨Fin 4, «FinitePoly [[3, 1, 0, 3], [3, 3, 2, 3], [3, 0, 3, 1], [0, 1, 2, 3]]», by decideFin!⟩
