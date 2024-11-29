import equational_theories.FactsSyntax
import equational_theories.EquationalResult
import equational_theories.Equations.All
import Mathlib.Data.Set.Finite.Basic

/- This file is for results currently conjectured from project discussion, but not yet formalized. -/

namespace Conjectures

/- Some conjectures from https://leanprover.zulipchat.com/#narrow/stream/458659-Equational/topic/1076.20!.3D.3E.203/near/476293108 -/

/-- See https://leanprover.zulipchat.com/user_uploads/3121/ASjTo5huToAvNGcg7pOGOOSy/Equation1692.pdf -/
@[equational_result]
conjecture Equation1692_facts : ∃ (G : Type) (_ : Magma G), Facts G [1692] [47, 1832, 2441, 3050, 3456, 4065]

/-- https://teorth.github.io/equational_theories/blueprint/infinite-magma-constructions-chapter.html#dupont-section as well as an alternate construction at https://leanprover.zulipchat.com/#narrow/channel/458659-Equational/topic/713.2C.201289.2C.201447/near/482011293.2E01 -/
@[equational_result]
conjecture Equation63_facts : ∃ (G : Type) (_ : Magma G), Facts G [63] [1692]

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
conjecture Finite.Equation1443_implies_Equation3055 (G : Type) [Magma G] [Finite G] (_ : Equation1443 G) : Equation3055 G
@[equational_result]
conjecture Finite.Equation1681_implies_Equation3877 (G : Type) [Magma G] [Finite G] (_ : Equation1681 G) : Equation3877 G
@[equational_result]
conjecture Finite.Equation1701_implies_Equation1035 (G : Type) [Magma G] [Finite G] (_ : Equation1701 G) : Equation1035 G

/- The below is also reachable using the method of bijections from above -/
/-- https://leanprover.zulipchat.com/#narrow/channel/458659-Equational/topic/Austin.20pairs/near/482525422 -/
@[equational_result]
conjecture Finite.Equation1516_implies_Equation255 (G : Type) [Magma G] [Finite G] (_ : Equation1516 G) : Equation255 G

/-- https://teorth.github.io/equational_theories/blueprint/906-chapter.html -/
@[equational_result]
conjecture Finite.Equation906_implies_Equation3862 (G : Type) [Magma G] [Finite G] (_ : Equation906 G) : Equation3862 G


/--  https://leanprover.zulipchat.com/#narrow/channel/458659-Equational/topic/Austin.20pairs/near/483160464 -/
@[equational_result]
conjecture Equation503_facts : ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [503] [4065, 3862]
@[equational_result]
conjecture Equation476_facts : ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [476] [359, 4065]

end Conjectures
