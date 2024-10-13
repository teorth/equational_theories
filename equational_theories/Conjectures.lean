import equational_theories.FactsSyntax
import equational_theories.EquationalResult
import equational_theories.Equations.All

/- This file is for results currently conjectured from project discussion, but not yet formalized.

-/

namespace Conjectures

/-  Some conjectures from https://leanprover.zulipchat.com/#narrow/stream/458659-Equational/topic/1076.20!.3D.3E.203/near/476293108 -/

/-- https://leanprover.zulipchat.com/user_uploads/3121/b-Usk-DH5Y8dALsaMWxIZxPJ/NonImplication-updated.pdf -/
@[equational_result]
conjecture Equation1076_facts : ∃ (G : Type) (_ : Magma G), Facts G [1076] [3]

/-- See https://leanprover.zulipchat.com/user_uploads/3121/zGPTzX7J0AkJcQdPdh_xoCTe/Equation_73-updated.pdf -/
@[equational_result]
conjecture Equation73_facts : ∃ (G : Type) (_ : Magma G), Facts G [73] [99]

/-- See https://leanprover.zulipchat.com/user_uploads/3121/zGPTzX7J0AkJcQdPdh_xoCTe/Equation_73-updated.pdf -/
@[equational_result]
conjecture Equation73_facts' : ∃ (G : Type) (_ : Magma G), Facts G [73] [203]

/-- See https://leanprover.zulipchat.com/user_uploads/3121/zGPTzX7J0AkJcQdPdh_xoCTe/Equation_73-updated.pdf -/
@[equational_result]
conjecture Equation73_facts'' : ∃ (G : Type) (_ : Magma G), Facts G [73] [255]

/-- See https://leanprover.zulipchat.com/user_uploads/3121/zGPTzX7J0AkJcQdPdh_xoCTe/Equation_73-updated.pdf -/
@[equational_result]
conjecture Equation73_facts''' : ∃ (G : Type) (_ : Magma G), Facts G [73] [4380]

/-- See https://leanprover.zulipchat.com/user_uploads/3121/zGPTzX7J0AkJcQdPdh_xoCTe/Equation_73-updated.pdf -/
@[equational_result]
conjecture Equation229_facts : ∃ (G : Type) (_ : Magma G), Facts G [229] [73]




/-- See https://leanprover.zulipchat.com/#narrow/stream/458659-Equational/topic/Oberlix.3A.20joining.20two.20approaches/near/476555119 -/
@[equational_result]
conjecture Equation1491_facts : ∃ (G : Type) (_ : Magma G), Facts G [1491] [65]


end Conjectures
