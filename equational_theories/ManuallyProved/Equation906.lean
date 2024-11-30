import equational_theories.EquationalResult
import equational_theories.Equations.All
import equational_theories.FiniteModel
import Mathlib.Data.Fintype.Card
import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic.Linarith

namespace Eq906

-- https://teorth.github.io/equational_theories/blueprint/906-chapter.html

@[equational_result]
theorem Finite.Equation906_implies_Equation3862 (G : Type*) [Magma G] [Finite G] (h : Equation906 G) :
    Equation3862 G := by
  intro x
  let S (x : G) := x ◇ x
  let f (b : G) := x ◇ b
  let inv_f (b : G) := (f b) ◇ (S b)
  have if1 : Function.RightInverse inv_f f := by
    intro a
    symm
    apply h
  have if2 := Function.leftInverse_of_surjective_of_rightInverse
    (Finite.surjective_of_injective if1.injective) if1
  let g (b : G) := (x ◇ (S x)) ◇ b
  let inv_g (b : G) := (g b) ◇ (S b)
  have ig1 : Function.RightInverse inv_g g := by
    intro a
    symm
    apply h
  have ig2 := Function.leftInverse_of_surjective_of_rightInverse
    (Finite.surjective_of_injective ig1.injective) ig1
  have f2_eq_g2 (w : G) (h : f w = g w) : f^[2] w = g^[2] w := by
    have iterated_inv (n : ℕ) : inv_f^[n] w = inv_g^[n] w := by
      induction n generalizing w with
      | zero => simp only [Function.iterate_zero, id_eq]
      | succ n ih =>
        have : inv_f w = inv_g w := by
          change (f w) ◇ (S w) = (g w) ◇ (S w)
          rw [h]
        change inv_f^[n] (inv_f w) = inv_g^[n] (inv_g w)
        rw [this]
        let w := inv_g w
        change inv_f^[n] w = inv_g^[n] w
        have : f w = g w := by
          unfold w
          nth_rewrite 1 [← this]
          rw [if1, ig1]
        exact (ih w) this
    obtain ⟨p, hpgt, hfperiodic, hgperiodic⟩ := FiniteModel.Finite.fn_mutually_eventually_periodic f g
    have inv_periodic {f inv_f : G → G} (inv1 : Function.RightInverse f inv_f)
        (inv2 : Function.RightInverse inv_f f) (hperiodic: f^[p] = f^[2*p]) (k : ℕ) (hk : k < p) :
        inv_f^[k] w = f^[p - k] w := by
      apply Function.Injective.iterate inv1.injective k
      rw [Function.RightInverse.iterate inv2 k]
      symm
      have : k + (p - k) = p := by omega
      rw [← Function.iterate_add_apply, this]
      have cancel : f^[p] w = w := by
        have : f^[2*p] w = f^[p] w := by rw [hperiodic]
        have := Function.iterate_cancel inv1.injective this
        have : p = 2*p-p := by omega
        rwa [this]
      exact cancel
    rcases le_or_lt p 1
    . have : p = 1 := by linarith
      rw [this] at hfperiodic
      rw [this] at hgperiodic
      rw [← hfperiodic, ← hgperiodic, Function.iterate_one, Function.iterate_one, h]
    . have : 2 = (p - (p - 2)) := by omega
      rw [this]
      rw [← inv_periodic if2 if1 hfperiodic (p - 2) (by omega)]
      rw [← inv_periodic ig2 ig1 hgperiodic (p - 2) (by omega)]
      apply iterated_inv
  have cf : x = f (S x ◇ S x) := by apply h
  have cg : x = g (S x ◇ S x) := by
    change x = inv_f (f x)
    symm
    apply if2
  have : f (S x ◇ S x) = g (S x ◇ S x) := by rw [← cf, ← cg]
  change f x = g x
  nth_rewrite 2 [cg]
  nth_rewrite 1 [cf]
  change f^[2] (S x ◇ S x) = g^[2] (S x ◇ S x)
  apply f2_eq_g2 _ this

end Eq906
