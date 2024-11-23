import equational_theories.FactsSyntax
import equational_theories.EquationalResult
import equational_theories.Equations.All
import Mathlib.Data.Set.Finite.Basic

/- This file is for results currently conjectured from project discussion, but not yet formalized. -/

namespace Conjectures

/- Some conjectures from https://leanprover.zulipchat.com/#narrow/stream/458659-Equational/topic/1076.20!.3D.3E.203/near/476293108 -/

/-- See https://leanprover.zulipchat.com/user_uploads/3121/HjHtBqq50xdgzG5RP6zmLBgh/Equation1076-corrected.pdf -/
@[equational_result]
conjecture Equation1076_facts : ∃ (G : Type) (_ : Magma G), Facts G [1076] [47, 99, 151, 203, 255, 411, 614, 817, 1223, 1426, 1629, 1832, 2035, 2238, 2441, 2644, 2847, 3050, 3253, 3456, 3659, 3862, 4065, 4380]

/-- See https://leanprover.zulipchat.com/user_uploads/3121/zGPTzX7J0AkJcQdPdh_xoCTe/Equation_73-updated.pdf -/
@[equational_result]
conjecture Equation73_facts : ∃ (G : Type) (_ : Magma G), Facts G [73] [99, 203, 255, 4380]

/-- See https://leanprover.zulipchat.com/#narrow/stream/458659-Equational/topic/1076.20!.3D.3E.203/near/477009119 -/
@[equational_result]
conjecture Equation713_facts : ∃ (G : Type) (_ : Magma G), Facts G [713] [817, 1426, 3862, 4065]

/-- See https://leanprover.zulipchat.com/#narrow/stream/458659-Equational/topic/1076.20!.3D.3E.203/near/477009119 -/
@[equational_result]
conjecture Equation1289_facts : ∃ (G : Type) (_ : Magma G), Facts G [1289] [3116, 4435]

/-- See https://leanprover.zulipchat.com/#narrow/stream/458659-Equational/topic/1076.20!.3D.3E.203/near/477009119 -/
@[equational_result]
conjecture Equation1447_facts : ∃ (G : Type) (_ : Magma G), Facts G [1447] [1431, 4269]

/-- See https://leanprover.zulipchat.com/user_uploads/3121/ASjTo5huToAvNGcg7pOGOOSy/Equation1692.pdf -/
@[equational_result]
conjecture Equation1692_facts : ∃ (G : Type) (_ : Magma G), Facts G [1692] [47, 1832, 2441, 3050, 3456, 4065]

/-- https://leanprover.zulipchat.com/#narrow/channel/458659-Equational/topic/Equation.20879.20!.3D.3E.204065/near/477684558 -/
@[equational_result]
conjecture Equation879_facts : ∃ (G : Type) (_ : Magma G), Facts G [879] [4065]

/-- https://teorth.github.io/equational_theories/blueprint/infinite-magma-constructions-chapter.html#dupont-section -/
@[equational_result]
conjecture Equation63_facts : ∃ (G : Type) (_ : Magma G), Facts G [63] [1692]

/-- https://leanprover.zulipchat.com/#narrow/channel/458659-Equational/topic/713.2C.201289.2C.201447/near/482084613.2E01 -/
@[equational_result]
conjecture Equation1722_facts : ∃ (G : Type) (_ : Magma G), Facts G [1722] [2644, 3050, 1832]

/-- https://leanprover.zulipchat.com/#narrow/channel/458659-Equational/topic/1323/near/481475622 -/
@[equational_result]
conjecture Equation1323_facts : ∃ (G : Type) (_ : Magma G), Facts G [1323, 1898] [2744, 2710]

/--  https://teorth.github.io/equational_theories/blueprint/1516-chapter.html -/
@[equational_result]
conjecture Equation1516_facts : ∃ (G : Type) (_ : Magma G), Facts G [1516] [255]


/- Finite conjectures follow -/

/-- https://leanprover.zulipchat.com/#narrow/channel/458659-Equational/topic/Austin.20pairs/near/480601897 -/
@[equational_result]
conjecture Finite.Equation3308_implies_Equation3511 (G : Type) [Magma G] [Finite G] (_ : Equation3308 G) : Equation3511 G
@[equational_result]
conjecture Finite.Equation3549_implies_Equation3955 (G : Type) [Magma G] [Finite G] (_ : Equation3549 G) : Equation3955 G

/-- https://leanprover.zulipchat.com/#narrow/channel/458659-Equational/topic/Austin.20pairs/near/481257624 -/
@[equational_result]
conjecture Finite.Equation467_implies_Equation2847 (G : Type) [Magma G] [Finite G] (_ : Equation467 G) : Equation2847 G
@[equational_result]
conjecture Finite.Equation1133_implies_Equation1167 (G : Type) [Magma G] [Finite G] (_ : Equation1133 G) : Equation1167 G
@[equational_result]
conjecture Finite.Equation1167_implies_Equation1055 (G : Type) [Magma G] [Finite G] (_ : Equation1167 G) : Equation1055 G
@[equational_result]
conjecture Finite.Equation1167_implies_Equation1096 (G : Type) [Magma G] [Finite G] (_ : Equation1167 G) : Equation1096 G
@[equational_result]
conjecture Finite.Equation1167_implies_Equation1112 (G : Type) [Magma G] [Finite G] (_ : Equation1167 G) : Equation1112 G
@[equational_result]
conjecture Finite.Equation1167_implies_Equation1133 (G : Type) [Magma G] [Finite G] (_ : Equation1167 G) : Equation1133 G
@[equational_result]
conjecture Finite.Equation1167_implies_Equation1721 (G : Type) [Magma G] [Finite G] (_ : Equation1167 G) : Equation1721 G
@[equational_result]
conjecture Finite.Equation1167_implies_Equation1897 (G : Type) [Magma G] [Finite G] (_ : Equation1167 G) : Equation1897 G
@[equational_result]
conjecture Finite.Equation1167_implies_Equation1668 (G : Type) [Magma G] [Finite G] (_ : Equation1167 G) : Equation1668 G
@[equational_result]
conjecture Finite.Equation1167_implies_Equation1701 (G : Type) [Magma G] [Finite G] (_ : Equation1167 G) : Equation1701 G
@[equational_result]
conjecture Finite.Equation1167_implies_Equation1958 (G : Type) [Magma G] [Finite G] (_ : Equation1167 G) : Equation1958 G
@[equational_result]
conjecture Finite.Equation1167_implies_Equation4615 (G : Type) [Magma G] [Finite G] (_ : Equation1167 G) : Equation4615 G
@[equational_result]
conjecture Finite.Equation1441_implies_Equation4067 (G : Type) [Magma G] [Finite G] (_ : Equation1441 G) : Equation4067 G
@[equational_result]
conjecture Finite.Equation1443_implies_Equation1630 (G : Type) [Magma G] [Finite G] (_ : Equation1443 G) : Equation1630 G
@[equational_result]
conjecture Finite.Equation1443_implies_Equation3055 (G : Type) [Magma G] [Finite G] (_ : Equation1443 G) : Equation3055 G
@[equational_result]
conjecture Finite.Equation1443_implies_Equation4268 (G : Type) [Magma G] [Finite G] (_ : Equation1443 G) : Equation4268 G
@[equational_result]
conjecture Finite.Equation1447_implies_Equation1431 (G : Type) [Magma G] [Finite G] (_ : Equation1447 G) : Equation1431 G
@[equational_result]
conjecture Finite.Equation1447_implies_Equation4269 (G : Type) [Magma G] [Finite G] (_ : Equation1447 G) : Equation4269 G
@[equational_result]
conjecture Finite.Equation1681_implies_Equation3877 (G : Type) [Magma G] [Finite G] (_ : Equation1681 G) : Equation3877 G
@[equational_result]
conjecture Finite.Equation1701_implies_Equation1035 (G : Type) [Magma G] [Finite G] (_ : Equation1701 G) : Equation1035 G
@[equational_result]
conjecture Finite.Equation1701_implies_Equation1884 (G : Type) [Magma G] [Finite G] (_ : Equation1701 G) : Equation1884 G
@[equational_result]
conjecture Finite.Equation1701_implies_Equation4587 (G : Type) [Magma G] [Finite G] (_ : Equation1701 G) : Equation4587 G

/- The below is also reachable using the method of bijections from above -/
/-- https://leanprover.zulipchat.com/#narrow/channel/458659-Equational/topic/Austin.20pairs/near/482525422 -/
@[equational_result]
conjecture Finite.Equation1516_implies_Equation255 (G : Type) [Magma G] [Finite G] (_ : Equation1516 G) : Equation255 G

/--  https://leanprover.zulipchat.com/#narrow/channel/458659-Equational/topic/Austin.20pairs/near/483160464 -/
@[equational_result]
conjecture Equation503_facts : ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [503] [4065, 3862]
@[equational_result]
conjecture Equation503_facts : ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [476] [359, 4065]

end Conjectures
