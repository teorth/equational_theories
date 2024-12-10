import Mathlib.Data.Set.Finite.Basic

import Mathlib.Data.Fintype.Card
import equational_theories.EquationalResult
import equational_theories.Equations.All

/- Proves the implications clustered around the equation 1113.

When the proof is done, update the blueprint with \lean and \leanok tags as appropriate.
-/


namespace Eq1113


theorem Function.LeftInverse_eq_RightInverse {α : Type*} {β : Type*} {g g' : β → α} {f : α → β} (h : Function.LeftInverse f g) (h' : Function.RightInverse f g') : g = g' := by
  ext x
  nth_rewrite 2 [<-h x]
  exact (h' (g x)).symm

@[equational_result]
theorem Equation1133_implies_Equation1167 (G : Type) [Magma G] [Finite G] (h : Equation1133 G) : Equation1167 G := by
  let L (y x: G) := y ◇ x
  let R (y x: G) := x ◇ y
  let S (x: G) := x ◇ x
  have Ly_left_inv (y z: G) : Function.LeftInverse (L y) (L (y ◇ (z ◇ y))) := by
    intro x
    exact (h x y z).symm
  have Ly_right_inv (y z: G) : Function.RightInverse (L y) (L (y ◇ (z ◇ y))) := Function.rightInverse_of_injective_of_leftInverse
    (Finite.injective_iff_surjective.mpr (Ly_left_inv y z).surjective) (Ly_left_inv y z)
  have Ly_invol (y : G) : Function.LeftInverse (L y) (L y) := by
    convert Ly_left_inv y (y ◇ S y)
    exact h y y y
  have Ly_invol_right (y : G) : Function.RightInverse (L y) (L y) := by
    convert Ly_right_inv y (y ◇ S y)
    exact h y y y

  have Lzyy_Lzy (y z:G): L ((z ◇ y) ◇ y) = L (z ◇ y) := by
    apply Function.LeftInverse_eq_RightInverse _ (Ly_invol_right (z ◇ y))
    convert Ly_left_inv (z ◇ y) z
    exact (Ly_invol z y).symm

  have S_inj : Function.Injective S := by
    rw [Finite.injective_iff_surjective]
    intro y
    use S y ◇ y
    convert Ly_invol (S y ◇ y) y using 1
    change L (S y ◇ y) (L (y ◇ y) y) = L (S y ◇ y) (L ((y ◇ y) ◇ y) y)
    congr 1
    rw [Lzyy_Lzy y y]

  intro x y z
  change x = (L y) (L (z ◇ S y) x)
  rw [<- Lzyy_Lzy (S y) z]
  convert (Ly_invol y x).symm
  set w := (z ◇ S y) ◇ S y
  apply S_inj
  rw [<-Ly_invol w (S y)]
  change L w w = L w (L ((z ◇ S y) ◇ S y) (S y))
  congr
  rw [Lzyy_Lzy (S y) z]

@[equational_result]
theorem Finite.Equation1167_implies_Equation1096 (G : Type) [Magma G] [Finite G] (h : Equation1167 G) : Equation1096 G := by
  let L (y x: G) := y ◇ x
  let S (x: G) := x ◇ x
  have Ly_left_inv (y z: G) : Function.LeftInverse (L y) (L (z ◇ S y)) := by
    intro x
    exact (h x y z).symm
  have Ly_right_inv (y z: G) : Function.RightInverse (L y) (L (z ◇ S y)) := Function.rightInverse_of_injective_of_leftInverse
    (Finite.injective_iff_surjective.mpr (Ly_left_inv y z).surjective) (Ly_left_inv y z)
  have S_surj : Function.Surjective S := by
    rw [<-Finite.injective_iff_surjective]
    intro x y hxy
    have hxy' : L x x = L y y := hxy
    have := Ly_right_inv x (S x) x
    rw [hxy, hxy', Ly_right_inv y (S y) y] at this
    exact this.symm
  have z_invar (y z z' : G) : L (z ◇ y) = L (z' ◇ y) := by
    obtain ⟨ w, hw ⟩ := S_surj y
    rw [<-hw]
    exact Function.LeftInverse_eq_RightInverse (Ly_left_inv w z) (Ly_right_inv w z')
  have (x y z : G) : L (x ◇ (z ◇ y)) = L y := by
    obtain ⟨ w, hw ⟩ := S_surj z
    obtain ⟨ u, hu ⟩ := S_surj w
    rw [z_invar (z ◇ y) x u]
    ext x
    congr
    convert (h y u w).symm
    rw [<-hw, <-hu]
  intro x y z
  nth_rewrite 1 [h x y y]
  congr 1
  change L (y ◇ (y ◇ y)) x = L (x ◇ (z ◇ y)) x
  rw [this x y z, this y y y]

end Eq1113
