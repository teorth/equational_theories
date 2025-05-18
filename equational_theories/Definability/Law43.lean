import Batteries.Data.List.Basic
import equational_theories.Definability.Basic
import equational_theories.Equations.All

open FirstOrder.Language
open Law
open Law.MagmaLaw

--TODO: the commutative law is definable from anything of the form f(x,y) ≃ f(y,x).
theorem Equation43_termDefinableFrom_swapped_args {L : NatMagmaLaw}
    (hL2args : ∀ e ∈ L.lhs.elems.1, e ∈ [0,1] := by decide +kernel)
    (hR2args : ∀ e ∈ L.rhs.elems.1, e ∈ [0,1] := by decide +kernel)
    (hSymm : L.lhs ⬝ (fun x ↦ Lf $ Equiv.swap 0 1 x) = L.rhs := by rfl)
    : Law43.TermDefinableFrom L := by
  sorry

/-- The commutative law 43 `x ◇ y = y ◇ x` is TermDefinable from 40 `x ◇ x = y ◇ y`. -/
theorem Equation43_termDefinableFrom_Equation40 : Law43.TermDefinableFrom Law40 :=
  Equation43_termDefinableFrom_swapped_args

/-- The commutative law 43 `x ◇ y = y ◇ x` is TermDefinable from 4343 `x ◇ (y ◇ y) = y ◇ (x ◇ x)`. -/
theorem Equation43_termDefinableFrom_Equation4343 : Law43.TermDefinableFrom Law4343 :=
  Equation43_termDefinableFrom_swapped_args

/-- The commutative law 43 `x ◇ y = y ◇ x` is TermDefinable from 4293 `x ◇ (x ◇ y) = y ◇ (y ◇ x)`. -/
theorem Equation43_termDefinableFrom_Equation4293 : Law43.TermDefinableFrom Law4293 :=
  Equation43_termDefinableFrom_swapped_args

/-- The commutative law 43 `x ◇ y = y ◇ x` is TermDefinable from 4321 `x ◇ (y ◇ x) = y ◇ (x ◇ y)`. -/
theorem Equation43_termDefinableFrom_Equation4321 : Law43.TermDefinableFrom Law4321 :=
  Equation43_termDefinableFrom_swapped_args
