import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3,0,1,3],[3,3,2,3],[0,3,3,3],[0,1,2,3]]
-/
set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[3,0,1,3],[3,3,2,3],[0,3,3,3],[0,1,2,3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[3,0,1,3],[3,3,2,3],[0,3,3,3],[0,1,2,3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[3,0,1,3],[3,3,2,3],[0,3,3,3],[0,1,2,3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [242,246,2310,2351,2355,2364,2389,2425,2430,2554,2623,2791,2836] [2263,2273,2293,2314,2368,2402,2420,2449] :=
    ⟨Fin 4, «FinitePoly [[3,0,1,3],[3,3,2,3],[0,3,3,3],[0,1,2,3]]», by decideFin!⟩
