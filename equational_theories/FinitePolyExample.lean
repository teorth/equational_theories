-- This is an example file, repesenting the generated files, but with shorter lists


import equational_theories.FinitePoly.Common
import equational_theories.FinitePoly.DecideBang
import equational_theories.FinitePoly.FactsSyntax

/-!
This file is generated from the following refutation as produced by
random generation of polynomials:
'(4 * x**2 + 4 * y**2 + 4 * x + 4 * y + 0 * x * y) % 5' (0, 42, 3252, 3318, 3341, 3455, 3521, 3544, 3861, 3914, 3963, 4064, 4117, 4166, 4282, 4357, 4379, 4397, 4404, 4434, 4441, 4481, 4530, 4543, 4634, 4676)

-/

set_option maxRecDepth 100000
set_option synthInstance.maxHeartbeats 20000000

/-! The magma definition -/
def «FinitePoly 4 * x² + 4 * y² + 4 * x + 4 * y» : Magma (Fin 5) where
  op x y := 4 * x*x + 4 * y*y + 4 * x + 4 * y

/-! The facts -/
theorem «Facts from FinitePoly 4 * x² + 4 * y² + 4 * x + 4 * y» :
  ∃ (G : Type) (_ : Magma G), Facts G [1, 43, 3253] [2, 3, 4] := by
    refine ⟨Fin 5, «FinitePoly 4 * x² + 4 * y² + 4 * x + 4 * y», ?_⟩
    decide!
