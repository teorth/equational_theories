import equational_theories.Mathlib.Data.List.Defs
import equational_theories.Mathlib.Order.Greedy
import Mathlib.Data.Finset.Order
import Mathlib.Data.List.AList
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Functor
import Mathlib.GroupTheory.FreeGroup.Basic

import equational_theories.FreshGenerator
import equational_theories.Equations.All
import equational_theories.FactsSyntax


/- When the theorems here are fully formalized, update `Conjectures.lean` and `ManuallyProved.lean` accordingly. -/

namespace Eq1441

/- Proof can be found at https://teorth.github.io/equational_theories/blueprint/infinite-model-chapter.html#1441-4067-1443-3055 -/

@[equational_result]
theorem Finite.Equation1441_implies_Equation4067 (G : Type) [Magma G] [Finite G] (_ : Equation1441 G) : Equation4067 G := by sorry



/- Proof can be found at https://teorth.github.io/equational_theories/blueprint/infinite-model-chapter.html#1441-4067-1443-3055 -/

@[equational_result]
theorem Finite.Equation1443_implies_Equation3055 (G : Type) [Magma G] [Finite G] (_ : Equation1443 G) : Equation3055 G := by sorry


/- Proof can be found at https://teorth.github.io/equational_theories/blueprint/infinite-model-chapter.html#1681-3877-1701-1035 -/

@[equational_result]
theorem Finite.Equation1681_implies_Equation3877 (G : Type) [Magma G] [Finite G] (_ : Equation1681 G) : Equation3877 G := by sorry



/- Proof can be found at https://teorth.github.io/equational_theories/blueprint/infinite-model-chapter.html#1681-3877-1701-1035 -/

@[equational_result]
theorem Finite.Equation1701_implies_Equation1035 (G : Type) [Magma G] [Finite G] (_ : Equation1701 G) : Equation1035 G := by sorry


end Eq1441
