import equational_theories.FactsSyntax
import equational_theories.EquationalResult
import equational_theories.Equations.All

/- This file is for results currently conjectured from project discussion, but not yet formalized. -/

namespace Conjectures

/- Some conjectures from https://leanprover.zulipchat.com/#narrow/stream/458659-Equational/topic/1076.20!.3D.3E.203/near/476293108 -/

/-- See https://leanprover.zulipchat.com/user_uploads/3121/b-Usk-DH5Y8dALsaMWxIZxPJ/NonImplication-updated.pdf and https://leanprover.zulipchat.com/user_uploads/3121/HjHtBqq50xdgzG5RP6zmLBgh/Equation1076-corrected.pdf -/
@[equational_result]
conjecture Equation1076_facts : ∃ (G : Type) (_ : Magma G), Facts G [1076] [3, 47, 99, 151, 203, 255, 411, 614, 817, 1223, 1426, 1629, 1832, 2035, 2238, 2441, 2644, 2847, 3050, 3253, 3456, 3659, 3862, 4065, 4380]

/-- See https://leanprover.zulipchat.com/user_uploads/3121/zGPTzX7J0AkJcQdPdh_xoCTe/Equation_73-updated.pdf -/
@[equational_result]
conjecture Equation73_facts : ∃ (G : Type) (_ : Magma G), Facts G [73] [99, 203, 255, 4380]

/-- See https://leanprover.zulipchat.com/user_uploads/3121/zGPTzX7J0AkJcQdPdh_xoCTe/Equation_73-updated.pdf -/
@[equational_result]
conjecture Equation229_facts : ∃ (G : Type) (_ : Magma G), Facts G [229] [73]

/-- See https://leanprover.zulipchat.com/#narrow/stream/458659-Equational/topic/Oberlix.3A.20joining.20two.20approaches/near/476555119 -/
@[equational_result]
conjecture Equation1491_facts : ∃ (G : Type) (_ : Magma G), Facts G [1491] [65]

/-- See https://leanprover.zulipchat.com/#narrow/stream/458659-Equational/topic/1076.20!.3D.3E.203/near/477009119 -/
@[equational_result]
conjecture Equation713_facts : ∃ (G : Type) (_ : Magma G), Facts G [713] [359, 817, 1426, 3862, 4065]

/-- See https://leanprover.zulipchat.com/#narrow/stream/458659-Equational/topic/1076.20!.3D.3E.203/near/477009119 -/
@[equational_result]
conjecture Equation1289_facts : ∃ (G : Type) (_ : Magma G), Facts G [1289] [2507, 3116, 4435]

/-- See https://leanprover.zulipchat.com/#narrow/stream/458659-Equational/topic/1076.20!.3D.3E.203/near/477009119 -/
@[equational_result]
conjecture Equation1447_facts : ∃ (G : Type) (_ : Magma G), Facts G [1447] [1431, 4269]

/-- See https://leanprover.zulipchat.com/user_uploads/3121/ASjTo5huToAvNGcg7pOGOOSy/Equation1692.pdf -/
@[equational_result]
conjecture Equation1692_facts : ∃ (G : Type) (_ : Magma G), Facts G [1692] [23, 47, 1832, 2441, 3050, 3456, 4065]

/-- https://leanprover.zulipchat.com/#narrow/channel/458659-Equational/topic/Equation.20879.20!.3D.3E.204065/near/477684558 -/
@[equational_result]
conjecture Equation879_facts : ∃ (G : Type) (_ : Magma G), Facts G [879] [4065]

/-- https://teorth.github.io/equational_theories/blueprint/infinite-magma-constructions-chapter.html#dupont-section -/
@[equational_result]
conjecture Equation63_facts : ∃ (G : Type) (_ : Magma G), Facts G [63] [1692]

/-- https://leanprover.zulipchat.com/#narrow/channel/458659-Equational/topic/Outstanding.20equations.2C.20v1/near/477846456 -/
@[equational_result]
conjecture Equation3308_facts : ∃ (G : Type) (_ : Magma G), Facts G [3308] [3456, 3511]

/-- https://leanprover.zulipchat.com/#narrow/channel/458659-Equational/topic/Outstanding.20equations.2C.20v1/near/477860423 -/
@[equational_result]
conjecture Equation1516_facts : ∃ (G : Type) (_ : Magma G), Facts G [1516] [1489]

/--https://leanprover.zulipchat.com/#narrow/channel/458659-Equational/topic/Outstanding.20equations.2C.20v1/near/477865209 -/
@[equational_result]
conjecture Equation917_facts : ∃ (G : Type) (_ : Magma G), Facts G [917] [1629, 1729, 2441, 2541]

/-- https://teorth.github.io/equational_theories/blueprint/infinite-magma-constructions-chapter.html#adhoc-model -/
@[equational_result]
conjecture Equation3475_facts : ∃ (G : Type) (_ : Magma G), Facts G [3475] [3659]


end Conjectures
