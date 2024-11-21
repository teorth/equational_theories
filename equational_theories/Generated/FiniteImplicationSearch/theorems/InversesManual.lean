/-
Currently the tooling only look for inverses of the source not the destination of the
implication, here I add some implications by manually putting auto-generated proofs
together of an implication to the inverse of the destination and then the proof of
implication to the destination.
-/

import equational_theories.Equations.All
import equational_theories.MagmaOp
import equational_theories.Superposition
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.ByContra

set_option linter.unusedVariables false

@[equational_result]
theorem Finite.Equation1443_implies_Equation1630 (G : Type*) [Magma G] [Finite G] (h : Equation1443 G) : Equation1630 G := by
  have eq1443_implies_eq21374 : ∀ X Y : G, X = ((X ◇ (X ◇ Y)) ◇ (X ◇ (X ◇ Y))) := by
    by_contra nh
    simp only [not_forall] at nh
    obtain ⟨sK0, sK1, nh⟩ := nh
    have step7 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
    have step8 : sK0 ≠ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) := mod_symm nh
    subsumption step8 step7
  have eq21374_implies_eq1630 (X Y : G) : ((X ◇ X) ◇ ((X ◇ X) ◇ Y)) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (s ◇ (s ◇ Y))) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (s ◇ s)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (s ◇ s)) (fun s => (s ◇ (s ◇ Y))) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  intro x y
  simp only [eq1443_implies_eq21374, eq21374_implies_eq1630]


@[equational_result]
theorem Finite.Equation1447_implies_Equation1431 (G : Type*) [Magma G] [Finite G] (h : Equation1447 G) : Equation1431 G := by
  have eq1447_implies_eq21413 : ∀ X Y : G, X = ((X ◇ (Y ◇ X)) ◇ (X ◇ (Y ◇ X))) := by
    by_contra nh
    simp only [not_forall] at nh
    obtain ⟨sK0, sK1, nh⟩ := nh
    have step7 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (X2 ◇ X0))) = X0 := mod_symm (h ..)
    have step8 : sK0 ≠ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) := mod_symm nh
    subsumption step8 step7
  have eq21413_implies_eq1431 (X Y : G) : ((X ◇ X) ◇ (Y ◇ (X ◇ X))) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (s ◇ (Y ◇ s))) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (s ◇ s)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (s ◇ s)) (fun s => (s ◇ (Y ◇ s))) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  intro x y
  simp only [eq1447_implies_eq21413, eq21413_implies_eq1431]


@[equational_result]
theorem Finite.Equation1701_implies_Equation1884 (G : Type*) [Magma G] [Finite G] (h : Equation1701 G) : Equation1884 G := by
  have eq1701_implies_eq24202 : ∀ X Y : G, X = (((Y ◇ X) ◇ X) ◇ ((Y ◇ X) ◇ X)) := by
    by_contra nh
    simp only [not_forall] at nh
    obtain ⟨sK0, sK1, nh⟩ := nh
    have step7 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ ((X2 ◇ X0) ◇ X0)) = X0 := mod_symm (h ..)
    have step8 : sK0 ≠ (((sK1 ◇ sK0) ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ sK0)) := mod_symm nh
    subsumption step8 step7
  have eq24202_implies_1884 (X Y : G) : ((Y ◇ (X ◇ X)) ◇ (X ◇ X)) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => ((Y ◇ s) ◇ s)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (s ◇ s)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (s ◇ s)) (fun s => ((Y ◇ s) ◇ s)) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  intro x y
  simp only [eq1701_implies_eq24202, eq24202_implies_1884]


