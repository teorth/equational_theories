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



namespace Eq467

/- Proof sketch:
* From 467 the $$L_y$$ are surjective, hence invertible.
* From 467 again one has $$Sy = y (Sy . S^2 y)$$, hence by left cancellability $$y = Sy . S^2 y$$.  Hence squaring is injective, hence invertible, and $$S^{-1} y = y . Sy$$.
* From 467 we have $$Sx = Sx . Cx$$ where $$Cx = Sx.x$$.
* From 467 again we have $$Sx = S^{-1} x . L_{Sx}^2 x = S^{-1} x . Sx = (x . Sx) . Sx$$, hence by invertibility of $$S$$, $$x = (S^{-1} x . x) . x$$, which gives 2847.

When done formalizing, update `Conjectures.lean` and `ManuallyProved.lean` accordingly. -/

@[equational_result]
theorem Equation467_implies_Equation2847 (G : Type) [Magma G] [Finite G] (_ : Equation467 G) : Equation2847 G := by sorry


end Eq467
