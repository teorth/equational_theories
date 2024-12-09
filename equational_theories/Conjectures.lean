import equational_theories.FactsSyntax
import equational_theories.EquationalResult
import equational_theories.Equations.All
import Mathlib.Data.Set.Finite.Basic

/- This file is for results currently conjectured from project discussion, but not yet formalized, or assigned to specific files in `ManuallyProven.lean`. -/

namespace Conjectures

/- Some conjectures from https://leanprover.zulipchat.com/#narrow/stream/458659-Equational/topic/1076.20!.3D.3E.203/near/476293108 -/

/-- See https://leanprover.zulipchat.com/user_uploads/3121/ASjTo5huToAvNGcg7pOGOOSy/Equation1692.pdf -/
@[equational_result]
conjecture Equation1692_facts : ∃ (G : Type) (_ : Magma G), Facts G [1692] [47, 1832, 2441, 3050, 3456, 4065]

/-- https://leanprover.zulipchat.com/#narrow/channel/458659-Equational/topic/1323/near/481475622 -/
@[equational_result]
conjecture Equation1323_facts : ∃ (G : Type) (_ : Magma G), Facts G [1323, 1898] [2744, 2710]

/--  https://teorth.github.io/equational_theories/blueprint/1516-chapter.html -/
@[equational_result]
conjecture Equation1516_facts : ∃ (G : Type) (_ : Magma G), Facts G [1516] [255]

/--  https://teorth.github.io/equational_theories/blueprint/1729-chapter.html -/
@[equational_result]
conjecture Equation1729_facts : ∃ (G : Type) (_ : Magma G), Facts G [1729] [817]


/- Finite conjectures follow -/


end Conjectures
