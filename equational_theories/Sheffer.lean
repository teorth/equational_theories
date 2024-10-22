import equational_theories.Generated.VampireProven.Sheffer
import Mathlib.Order.BooleanAlgebra

namespace Sheffer

open Sheffer

/- Sheffer stroke magma on a Boolean algebra -/
instance (B : Type*) [BooleanAlgebra B] : Magma B where
  op a b := (a ⊓ b)ᶜ

lemma Sheffer_Op (B : Type*) [BooleanAlgebra B] (a b : B) : a ◇ b = (a ⊓ b)ᶜ := rfl

/- Sheffer stroke satisfies Equation 345169 -/
theorem Sheffer_Equation345169 (B : Type*) [BooleanAlgebra B] : Equation345169 B := by
  intro _ _ _
  simp only [Sheffer_Op, compl_inf, compl_sup, compl_compl, sup_inf_right, sup_compl_eq_top, le_top, inf_of_le_left, sup_inf_left, compl_sup_eq_top, inf_le_left, sup_of_le_right, inf_le_right, sup_left_comm, inf_of_le_right, le_sup_left, le_inf_iff, and_self]

/- 345169 implies first Sheffer axiom. -/
theorem Equation345169_implies_Axiom1 (G : Type*) [Magma G] (h : Equation345169 G) : ∀ x : G, x = (x ◇ x) ◇ (x ◇ x) := λ x => Equation345169_implies_GeneralAxiom1 G h x x

/- 345169 implies second Sheffer axiom. -/
theorem Equation345169_implies_Axiom2 (G : Type*) [Magma G] (h : Equation345169 G) : ∀ x y : G, x ◇ x = x ◇ (y ◇ (y ◇ y)):= λ x y => Equation345169_implies_Axiom2Auto G h x y

/- Helper equations for third Sheffer axiom -/

theorem Equation345169_implies_Helper11 (G : Type*) [Magma G] (h : Equation345169 G) : ∀ x y z : G, (x ◇ (y ◇ z)) ◇ ((y ◇ x) ◇ x) = (x ◇ (y ◇ z)) ◇ (x ◇ (y ◇ z)) :=  λ x y z => (Equation345169_implies_Helper11Helper G h) (Equation345169_implies_Helper9 G h) (Equation345169_implies_Helper10 G h) x y z

theorem Equation345169_implies_Helper13 (G : Type*) [Magma G] (h : Equation345169 G) : ∀ x y z : G, (x ◇ (y ◇ y)) ◇ (x ◇ (z ◇ y)) = (x ◇ (z ◇ y)) ◇ (x ◇ (z ◇ y)) := by
  intro x y z
  rw [←Equation345169_implies_Helper12 G h y x, Equation345169_implies_Comm G h ((y ◇ x) ◇ x), Equation345169_implies_Comm G h z y]
  exact Equation345169_implies_Helper11 G h x y z

theorem Equation345169_implies_Helper18 (G : Type*) [Magma G] (h : Equation345169 G) : ∀ x y z : G, x ◇ ((y ◇ y) ◇ (z ◇ (x ◇ (x ◇ y)))) = x ◇ ((y ◇ y) ◇ (y ◇ y)) := by
  intro x y z
  have := Equation345169_implies_Helper16 G h x (y ◇ y) z
  rwa [Equation345169_implies_Helper17 G h x y] at this

theorem Equation345169_implies_Helper19 (G : Type*) [Magma G] (h : Equation345169 G) : ∀ x y z : G, x ◇ ((y ◇ y) ◇ (z ◇ (x ◇ (x ◇ y)))) = x ◇ y := by
  intro x y z
  have := Equation345169_implies_Helper18 G h x y z
  rwa [←Equation345169_implies_GeneralAxiom1 G h y y] at this

theorem Equation345169_implies_Helper22 (G : Type*) [Magma G] (h : Equation345169 G) : ∀ x y z : G, (x ◇ ((y ◇ z) ◇ x)) ◇ (y ◇ y) = (y ◇ z)◇ (y ◇ y) := by
  intro x y z
  have := (Equation345169_implies_Helper21 G h y z x).symm
  rwa [Equation345169_implies_Helper1 G h (y ◇ z) (x ◇ ((y ◇ z) ◇ x))] at this

theorem Equation345169_implies_Helper23 (G : Type*) [Magma G] (h : Equation345169 G) : ∀ y x z : G, y = (x ◇ ((y ◇ z) ◇ x)) ◇ (y ◇ y) := λ x y z => (Equation345169_implies_GeneralAxiom1 G h x z).trans (Equation345169_implies_Helper22 G h y x z).symm

theorem Equation345169_implies_Helper24 (G : Type*) [Magma G] (h : Equation345169 G) :  ∀ x y z : G, x ◇ ((y ◇ ((x ◇ z) ◇ y)) ◇ x) = y ◇ ((x ◇ z) ◇ y) := λ x y z => (Equation345169_implies_Helper24Helper G h) (Equation345169_implies_Helper3 G h) (Equation345169_implies_Helper23 G h) x y z

theorem Equation345169_implies_Helper25 (G : Type*) [Magma G] (h : Equation345169 G) : ∀ x y z : G, x ◇ ((y ◇ (y ◇ (z ◇ x))) ◇ x) = y ◇ ((x ◇ (y ◇ (x ◇ z))) ◇ y) := by
  intro x y z
  rw [Equation345169_implies_Helper5 G h, Equation345169_implies_Comm G h z x, Equation345169_implies_Comm G h y (x ◇ z), Equation345169_implies_Helper24 G h]

theorem Equation345169_implies_Helper26 (G : Type*) [Magma G] (h : Equation345169 G) : ∀ x y z : G, x ◇ ((y ◇ (y ◇ (z ◇ x))) ◇ x) = y ◇ (y ◇ (z ◇ x)) := by
  intro _ _ _
  rw [Equation345169_implies_Helper25 G h, Equation345169_implies_Helper5 G h]

theorem Equation345169_implies_Helper27 (G : Type*) [Magma G] (h : Equation345169 G) : ∀ x y z u : G, x ◇ (y ◇ (z ◇ (z ◇ (u ◇ (y ◇ x))))) = x ◇ (y ◇ y) := by
  intro x y z _
  rw [←Equation345169_implies_Helper15 G h x y z, ←Equation345169_implies_Helper26 G h, Equation345169_implies_Helper15 G h, Equation345169_implies_Helper15 G h]

theorem Equation345169_implies_Helper28 (G : Type*) [Magma G] (h : Equation345169 G) : ∀ x y z : G, x ◇ (y ◇ (y ◇ (z ◇ (x ◇ y)))) = x ◇ (y ◇ (x ◇ x)) := by
  intro x y z
  rw [←Equation345169_implies_Helper4 G h x y (x ◇ x), ←Equation345169_implies_Helper27 G h y x y z, Equation345169_implies_Helper4 G h, Equation345169_implies_Helper4 G h]

theorem Equation345169_implies_Helper29 (G : Type*) [Magma G] (h : Equation345169 G) : ∀ x y z : G, x ◇ (y ◇ (y ◇ (z ◇ (x ◇ y)))) = x ◇ x := λ x y z => (Equation345169_implies_Helper28 G h x y z).trans (Equation345169_implies_Helper2 G h x y)

theorem Equation345169_implies_Helper30 (G : Type*) [Magma G] (h : Equation345169 G) : ∀ x y z : G, x ◇ (((y ◇ (z ◇ x)) ◇ (y ◇ (z ◇ x))) ◇ (z ◇ z)) = x ◇ (y ◇ (z ◇ x)) := by
  intro x y z
  have := Equation345169_implies_Helper19 G h x (y ◇ (z ◇ x)) z
  rwa [Equation345169_implies_Helper29 G h z x y] at this

theorem Equation345169_implies_Helper31 (G : Type*) [Magma G] (h : Equation345169 G) : ∀ x y z : G, x ◇ (y ◇ (z ◇ z)) = x ◇ (y ◇ (z ◇ x)) := by
  intro x y z
  have := Equation345169_implies_Helper30 G h x y z
  rwa [Equation345169_implies_Helper14 G h y z x] at this

theorem Equation345169_implies_Helper32 (G : Type*) [Magma G] (h : Equation345169 G) : ∀ x y z : G, x ◇ (y ◇ ((z ◇ z) ◇ x)) = x ◇ (y ◇ z) := by
  intro x y z
  rw [Equation345169_implies_GeneralAxiom1 G h (z ◇ z) x, ←Equation345169_implies_Helper31 G h x y (((z ◇ z) ◇ x) ◇ ((z ◇ z) ◇ (z ◇ z))), ←Equation345169_implies_GeneralAxiom1 G h (z ◇ z) x, ←Equation345169_implies_GeneralAxiom1 G h z z]

theorem Equation345169_implies_Helper33 (G : Type*) [Magma G] (h : Equation345169 G) : ∀ x y z : G, (x ◇ (y ◇ y)) ◇ (x ◇ (z ◇  ((y ◇ y) ◇ x))) = (x ◇ (z ◇ y)) ◇ (x ◇ (z ◇ y)) := by
  intro x y z
  have := Equation345169_implies_Helper13 G h x y z
  rw (config := { occs := .pos [1]}) [←(Equation345169_implies_Helper32 G h x z y)] at this
  exact this

theorem Equation345169_implies_Helper34 (G : Type*) [Magma G] (h : Equation345169 G) : ∀ x y z : G, (x ◇ (y ◇ y)) ◇ (x ◇ (z ◇ (x ◇ (y ◇ y)))) = (x ◇ (z ◇ y)) ◇  (x ◇ (z ◇ y)) := by
  intro x y z
  have := Equation345169_implies_Helper33 G h x y z
  rwa [Equation345169_implies_Helper7 G h y y x] at this

theorem Equation345169_implies_Helper35 (G : Type*) [Magma G] (h : Equation345169 G) : ∀ x y z : G, (x ◇ (y ◇ y)) ◇ (x ◇ (z ◇ z)) = (x ◇ (z ◇ y)) ◇ (x ◇ (z ◇ y)):= λ x y z => (Equation345169_implies_Helper31 G h (x ◇ (y ◇ y)) x z).trans (Equation345169_implies_Helper34 G h x y z)

/- 345169 implies third Sheffer axiom -/
theorem Equation345169_implies_Axiom3 (G : Type*) [Magma G] (h : Equation345169 G) : ∀ x y z : G, (x ◇ (y ◇ z)) ◇ (x ◇ (y ◇ z)) = ((y ◇ y) ◇ x) ◇ ((z ◇ z) ◇ x):= λ x y z => ((Equation345169_implies_Helper35 G h x z y).symm).trans (Equation345169_implies_Helper6 G h x (z ◇ z) x (y ◇ y))

theorem Sheffer_Comm (G : Type*) [Magma G] (ax1 : ∀ x : G, (x ◇ x) ◇ (x ◇ x) = x) (ax2 : ∀ x y : G, x ◇ x = x ◇ (y ◇ (y ◇ y))) (ax3 : ∀ x y z : G, (x ◇ (y ◇ z)) ◇ (x ◇ (y ◇ z)) = ((y ◇ y) ◇ x) ◇ ((z ◇ z) ◇ x)) : ∀ x y : G, x ◇ y = y ◇ x := by
  intro x y
  have h1 : ∀ x y : G, (x ◇ x) ◇ (y ◇ (y ◇ y)) = x := by intro a b; have := (ax2 (a ◇ a) b).symm; rwa [ax1] at this
  have h2 : ∀ x y z : G, ((y ◇ (x ◇ x)) ◇ (y ◇ (x ◇ x))) ◇ (z ◇ (z ◇ z)) = (x ◇ x) ◇ y := by intro a b c; have := h1 ((a ◇ a) ◇ b) c; rwa [←ax3] at this
  have h3 : ∀ x y : G, (x ◇ x) ◇ y = y ◇ (x ◇ x) := by intro a b; have := h1 (b ◇ (a ◇ a)) x; rwa [h2] at this
  have := h3 (x ◇ x) y
  rwa [ax1] at this

/- This would be very convenient for le_trans if possible. Should be true as its just associativity for OR:
   sup (sup(x y) z) = sup((x ◇ x) ◇ (y ◇ y)) z
                    = (((x ◇ x) ◇ (y ◇ y)) ◇ ((x ◇ x) ◇ (y ◇ y))) ◇ (z ◇ z)

   sup (x (sup (y z))) = sup x ((y ◇ y) ◇ (z ◇ z))
                     = (x ◇ x) ◇ (((y ◇ y) ◇ (z ◇ z)) ◇ ((y ◇ y) ◇ (z ◇ z)))
-/ 
theorem Sheffer_Sup_Assoc (G : Type*) [Magma G] (ax1 : ∀ x : G, (x ◇ x) ◇ (x ◇ x) = x) (ax2 : ∀ x y : G, x ◇ x = x ◇ (y ◇ (y ◇ y))) (ax3 : ∀ x y z : G, (x ◇ (y ◇ z)) ◇ (x ◇ (y ◇ z)) = ((y ◇ y) ◇ x) ◇ ((z ◇ z) ◇ x)) : ∀ x y z : G, (((x ◇ x) ◇ (y ◇ y)) ◇ ((x ◇ x) ◇ (y ◇ y))) ◇ (z ◇ z) = (x ◇ x) ◇ (((y ◇ y) ◇ (z ◇ z)) ◇ ((y ◇ y) ◇ (z ◇ z))) := by sorry

/- Boolean algebra induced by magma satisfying the three Sheffer axioms. 
   The operations are defined in terms of Sheffer strokes:
   OR/SUP  = (A | A) | (B | B)
   AND/INF = (A | B) | (A | B)
-/
instance (G : Type*) [Magma G] (ax1 : ∀ x : G, (x ◇ x) ◇ (x ◇ x) = x) (ax2 : ∀ x y : G, x ◇ x = x ◇ (y ◇ (y ◇ y))) (ax3 : ∀ x y z : G, (x ◇ (y ◇ z)) ◇ (x ◇ (y ◇ z)) = ((y ◇ y) ◇ x) ◇ ((z ◇ z) ◇ x)) : BooleanAlgebra G where
  sup x y := (x ◇ x) ◇ (y ◇ y)
  le x y := (x ◇ x) ◇ (y ◇ y) = y
  le_refl x := ax1 x
  le_trans x y z xley ylez := by
    simp at *
    /- have : (x ◇ x) ◇ (((y ◇ y) ◇ (z ◇ z)) ◇ ((y ◇ y) ◇ (z ◇ z))) = z := by rwa [←xley, Sheffer_Sup_Assoc G ax1 ax2 ax3] at ylez
    rwa [ylez] at this -/
    have comm := Sheffer_Comm G ax1 ax2 ax3 x y
    sorry

end Sheffer
