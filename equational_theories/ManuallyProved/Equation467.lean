import Mathlib.Data.Set.Finite.Basic

import Mathlib.Data.Fintype.Card
import equational_theories.EquationalResult
import equational_theories.Equations.All


namespace Eq467

/- Proof sketch:
* From 467 the $L_y$ are surjective, hence invertible.
* From 467 again one has $Sy = y (Sy . S^2 y)$, hence by left cancellability $y = Sy . S^2 y$.  Hence squaring is injective, hence invertible, and $S^{-1} y = y . Sy$.
* From 467 we have $Sx = Sx . (Sx . x) = L_{Sx}^2 x$.
* From 467 again we have $Sx = S^{-1} x . L_{Sx}^2 x = S^{-1} x . Sx = (x . Sx) . Sx$, hence by invertibility of $S$, $x = (S^{-1} x . x) . x$, which gives 2847.
 -/

@[equational_result]
theorem Finite.Equation467_implies_Equation2847 (G : Type) [Magma G] [Finite G] (h : Equation467 G) : Equation2847 G := by
  let L (y x: G) := y ◇ x
  let S (x: G) := x ◇ x
  let T (x: G) := x ◇ (S x)
  have L_inj y : Function.Injective (L y) := by
    rw [Finite.injective_iff_surjective]
    intro x
    use (x ◇ (x ◇ (y ◇ y)))
    dsimp [L]
    rw [<-h x y]
  have ST_inv_right : Function.RightInverse S T := by
    intro y
    apply L_inj y
    symm
    dsimp [L, T, S]
    exact h (y ◇ y) y
  have ST_inv_left : Function.LeftInverse S T := Function.leftInverse_of_surjective_of_rightInverse
    (Finite.surjective_of_injective ST_inv_right.injective) ST_inv_right
  intro x
  change x = (T x ◇ x) ◇ x
  rw [<- ST_inv_left x]
  set y := T x
  rw [ST_inv_right y]
  convert h (S y) (T y) using 2
  convert h (S y) (S y) using 3
  change S (T y) = T (S y)
  rw [ST_inv_right y, ST_inv_left y]


end Eq467
