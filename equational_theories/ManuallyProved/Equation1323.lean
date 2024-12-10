import Mathlib.Data.Set.Finite.Basic

import equational_theories.FactsSyntax
import equational_theories.EquationalResult
import equational_theories.Equations.All

/- Refutes the implications from 1323.

When the proof is done, update the blueprint with \lean and \leanok tags as appropriate.
-/


namespace Eq1323

/-- https://leanprover.zulipchat.com/#narrow/channel/458659-Equational/topic/1323/near/481475622 -/
@[equational_result]
conjecture Equation1323_facts : ∃ (G : Type) (_ : Magma G), Facts G [1323] [2744]

end Eq1323
