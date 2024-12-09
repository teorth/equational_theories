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

namespace Eq1113

/- Proof can be found at https://teorth.github.io/equational_theories/blueprint/infinite-model-chapter.html#1167-1096
 -/

@[equational_result]
theorem Equation1133_implies_Equation1167 (G : Type) [Magma G] [Finite G] (_ : Equation1133 G) : Equation1167 G := by sorry

/- Proof can be found at https://teorth.github.io/equational_theories/blueprint/infinite-model-chapter.html#1167-1096
 -/

@[equational_result]
theorem Finite.Equation1167_implies_Equation1096 (G : Type) [Magma G] [Finite G] (_ : Equation1167 G) : Equation1096 G := by sorry


end Eq1113
