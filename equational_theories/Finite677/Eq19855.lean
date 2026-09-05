import Mathlib.Data.Set.Finite.Basic
import equational_theories.Equations.All

theorem Finite.Equation677_implies_Equation19855 (G : Type _) [Magma G] [Finite G]
    (h : Equation677 G) : Equation19855 G := fun X Y => by
  symm
  let S : Set G := Set.univ
  have m1 : S.MapsTo (fun s => (s ◇ ((Y ◇ s) ◇ Y))) S := by
    intro
    simp [S]
  have m2 : S.MapsTo (fun s => (Y ◇ s)) S := by
    intro
    simp [S]
  have linv : S.LeftInvOn (fun s => (Y ◇ s)) (fun s => (s ◇ ((Y ◇ s) ◇ Y))) := by
    intro a ha
    simp [S]
    simp [← h]
  have t := linv.surjOn m1
  rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
  have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
  apply rinv _
  simp [S]
