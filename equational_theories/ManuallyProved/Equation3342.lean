import equational_theories.EquationalResult
import equational_theories.Equations.All
import Mathlib.Algebra.Polynomial.RingDivision

open Polynomial

namespace Eq3342

noncomputable section

open scoped Classical in
def op (a b : ℤ[X]) : ℤ[X] :=
  if a = b ∨ a * X = b then 2 * a /ₘ X ^ a.natTrailingDegree else
  if ∃ m, 2 * a = b * X^m then X * a /ₘ X ^ a.natTrailingDegree else
  if ∃ m, 2 * b = a * X^(m+1) then X * b /ₘ X ^ b.natTrailingDegree else
  0



end
