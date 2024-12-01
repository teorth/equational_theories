import equational_theories.Equations.All
import equational_theories.MagmaOp
import equational_theories.Superposition
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.ByContra

set_option linter.unusedVariables false

@[equational_result]
theorem Finite.Equation1076_implies_Equation3 (G : Type*) [Magma G] [Finite G] (h : Equation1076 G) : Equation3 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have step9 (X0 X1 : G) : (X1 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X1)) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ (sK0 ◇ sK0) := mod_symm nh
  have step11 (X Y : G) : ((Y ◇ (X ◇ Y)) ◇ ((Y ◇ (X ◇ Y)) ◇ Y)) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (s ◇ (s ◇ Y))) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (Y ◇ (s ◇ Y))) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (Y ◇ (s ◇ Y))) (fun s => (s ◇ (s ◇ Y))) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step12 (X Y : G) : (((Y ◇ X) ◇ ((Y ◇ X) ◇ Y)) ◇ Y) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => ((s ◇ (s ◇ Y)) ◇ Y)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (Y ◇ s)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (Y ◇ s)) (fun s => ((s ◇ (s ◇ Y)) ◇ Y)) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step13 (X0 X1 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X1) ◇ ((X1 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X1))) = X1 := superpose step9 step9
  have step15 (X0 X1 : G) : ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ X1)) = (X1 ◇ ((((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ X1)) ◇ X0) ◇ X1)) := superpose step12 step9
  have step75 (X0 : G) : ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) = (X0 ◇ (X0 ◇ X0)) := superpose step12 step15
  have step91 (X0 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ X0) = X0 := superpose step75 step12
  have step92 (X0 : G) : (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) = X0 := superpose step75 step13
  have step102 (X0 : G) : (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ X0) = X0 := superpose step11 step92
  have step103 (X0 : G) : (X0 ◇ X0) = X0 := superpose step91 step102
  have step175 : sK0 ≠ sK0 := superpose step103 step10
  subsumption step175 rfl


@[equational_result]
theorem Finite.Equation1086_implies_Equation1832 (G : Type*) [Magma G] [Finite G] (h : Equation1086 G) : Equation1832 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have step10 : sK0 ≠ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have step11 (X Y : G) : ((Y ◇ (X ◇ Y)) ◇ (Y ◇ Y)) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (s ◇ (Y ◇ Y))) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (Y ◇ (s ◇ Y))) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (Y ◇ (s ◇ Y))) (fun s => (s ◇ (Y ◇ Y))) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step15 : sK0 ≠ sK0 := superpose step11 step10
  subsumption step15 rfl


@[equational_result]
theorem Finite.Equation1086_implies_Equation1898 (G : Type*) [Magma G] [Finite G] (h : Equation1086 G) : Equation1898 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step10 : sK0 ≠ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ sK1)) := mod_symm nh
  have step11 (X Y : G) : ((Y ◇ (X ◇ Y)) ◇ (Y ◇ Y)) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (s ◇ (Y ◇ Y))) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (Y ◇ (s ◇ Y))) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (Y ◇ (s ◇ Y))) (fun s => (s ◇ (Y ◇ Y))) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step15 : sK0 ≠ sK0 := superpose step11 step10
  subsumption step15 rfl


@[equational_result]
theorem Finite.Equation1086_implies_Equation2710 (G : Type*) [Magma G] [Finite G] (h : Equation1086 G) : Equation2710 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step10 : sK0 ≠ (((sK1 ◇ sK0) ◇ (sK1 ◇ sK1)) ◇ sK1) := mod_symm nh
  have step12 (X Y : G) : (((Y ◇ X) ◇ (Y ◇ Y)) ◇ Y) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => ((s ◇ (Y ◇ Y)) ◇ Y)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (Y ◇ s)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (Y ◇ s)) (fun s => ((s ◇ (Y ◇ Y)) ◇ Y)) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step17 : sK0 ≠ sK0 := superpose step12 step10
  subsumption step17 rfl


@[equational_result]
theorem Finite.Equation1110_implies_Equation8 (G : Type*) [Magma G] [Finite G] (h : Equation1110 G) : Equation8 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have step11 : sK0 ≠ (sK0 ◇ (sK0 ◇ sK0)) := mod_symm nh
  have step12 (X Y : G) : ((Y ◇ ((Y ◇ X) ◇ Y)) ◇ (Y ◇ ((Y ◇ X) ◇ Y))) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (s ◇ s)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (Y ◇ ((Y ◇ s) ◇ Y))) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (Y ◇ ((Y ◇ s) ◇ Y))) (fun s => (s ◇ s)) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step14 (X Y : G) : ((Y ◇ ((Y ◇ X) ◇ (Y ◇ X))) ◇ Y) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => ((Y ◇ (s ◇ s)) ◇ Y)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (Y ◇ s)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (Y ◇ s)) (fun s => ((Y ◇ (s ◇ s)) ◇ Y)) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step15 (X0 X1 : G) : (((X1 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) ◇ (X0 ◇ X0)) ◇ (X1 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0)))) = X1 := superpose step14 step14
  have step74 (X0 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)))) := superpose step14 step15
  have step160 (X0 : G) : ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0))) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) := superpose step74 step12
  have step167 (X0 : G) : ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0))) = X0 := superpose step12 step160
  have step201 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose step167 step14
  have step244 : sK0 ≠ sK0 := superpose step201 step11
  subsumption step244 rfl


@[equational_result]
theorem Finite.Equation1112_implies_Equation8 (G : Type*) [Magma G] [Finite G] (h : Equation1112 G) : Equation8 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have step8 (X0 X1 : G) : (X1 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X0)) = X0 := mod_symm (h ..)
  have step9 : sK0 ≠ (sK0 ◇ (sK0 ◇ sK0)) := mod_symm nh
  have step10 (X Y : G) : ((Y ◇ ((Y ◇ X) ◇ Y)) ◇ (Y ◇ X)) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => ((Y ◇ (s ◇ Y)) ◇ s)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (Y ◇ s)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (Y ◇ s)) (fun s => ((Y ◇ (s ◇ Y)) ◇ s)) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step13 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ (X0 ◇ X0))) := superpose step8 step10
  have step16 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose step13 step10
  have step18 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose step10 step16
  have step20 : sK0 ≠ sK0 := superpose step18 step9
  subsumption step20 rfl


@[equational_result]
theorem Finite.Equation1113_implies_Equation2534 (G : Type*) [Magma G] [Finite G] (h : Equation1113 G) : Equation2534 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 : sK0 ≠ ((sK1 ◇ ((sK1 ◇ sK0) ◇ sK1)) ◇ sK1) := mod_symm nh
  have step10 (X Y : G) : ((Y ◇ ((Y ◇ X) ◇ Y)) ◇ Y) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (s ◇ Y)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (Y ◇ ((Y ◇ s) ◇ Y))) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (Y ◇ ((Y ◇ s) ◇ Y))) (fun s => (s ◇ Y)) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step13 : sK0 ≠ sK0 := superpose step10 step9
  subsumption step13 rfl


@[equational_result]
theorem Finite.Equation1117_implies_Equation2538 (G : Type*) [Magma G] [Finite G] (h : Equation1117 G) : Equation2538 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have step9 : sK0 ≠ ((sK1 ◇ ((sK1 ◇ sK0) ◇ sK2)) ◇ sK2) := mod_symm nh
  have step10 (X Y Z : G) : ((Y ◇ ((Y ◇ X) ◇ Z)) ◇ Z) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (s ◇ Z)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (Y ◇ ((Y ◇ s) ◇ Z))) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (Y ◇ ((Y ◇ s) ◇ Z))) (fun s => (s ◇ Z)) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step15 : sK0 ≠ sK0 := superpose step10 step9
  subsumption step15 rfl


@[equational_result]
theorem Finite.Equation115_implies_Equation2707 (G : Type*) [Magma G] [Finite G] (h : Equation115 G) : Equation2707 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step10 : sK0 ≠ (((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) ◇ sK1) := mod_symm nh
  have step12 (X Y : G) : (((Y ◇ X) ◇ (Y ◇ X)) ◇ Y) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => ((s ◇ s) ◇ Y)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (Y ◇ s)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (Y ◇ s)) (fun s => ((s ◇ s) ◇ Y)) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step15 : sK0 ≠ sK0 := superpose step12 step10
  subsumption step15 rfl


@[equational_result]
theorem Finite.Equation115_implies_Equation4273 (G : Type*) [Magma G] [Finite G] (h : Equation115 G) : Equation4273 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) : (X1 ◇ ((X0 ◇ X0) ◇ X1)) = X0 := mod_symm (h ..)
  have step10 : (sK0 ◇ (sK0 ◇ sK0)) ≠ (sK1 ◇ (sK0 ◇ sK1)) := mod_symm nh
  have step11 (X Y : G) : ((Y ◇ (X ◇ Y)) ◇ (Y ◇ (X ◇ Y))) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (s ◇ s)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (Y ◇ (s ◇ Y))) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (Y ◇ (s ◇ Y))) (fun s => (s ◇ s)) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step17 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X1)) = (X2 ◇ (X0 ◇ X2)) := superpose step11 step9
  have step49 (X0 : G) : (sK0 ◇ (sK0 ◇ sK0)) ≠ (X0 ◇ (sK0 ◇ X0)) := superpose step17 step10
  subsumption step49 step17


@[equational_result]
theorem Finite.Equation118_implies_Equation222 (G : Type*) [Magma G] [Finite G] (h : Equation118 G) : Equation222 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step10 : sK0 ≠ ((sK1 ◇ (sK0 ◇ sK1)) ◇ sK1) := mod_symm nh
  have step11 (X Y : G) : ((Y ◇ (X ◇ Y)) ◇ Y) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (s ◇ Y)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (Y ◇ (s ◇ Y))) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (Y ◇ (s ◇ Y))) (fun s => (s ◇ Y)) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step16 : sK0 ≠ sK0 := superpose step11 step10
  subsumption step16 rfl


@[equational_result]
theorem Finite.Equation118_implies_Equation274 (G : Type*) [Magma G] [Finite G] (h : Equation118 G) : Equation274 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step10 : sK0 ≠ (((sK1 ◇ sK0) ◇ sK1) ◇ sK1) := mod_symm nh
  have step11 (X Y : G) : ((Y ◇ (X ◇ Y)) ◇ Y) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (s ◇ Y)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (Y ◇ (s ◇ Y))) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (Y ◇ (s ◇ Y))) (fun s => (s ◇ Y)) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step15 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = (X1 ◇ (X0 ◇ X1)) := superpose step11 step11
  have step17 : sK0 ≠ ((sK1 ◇ (sK0 ◇ sK1)) ◇ sK1) := superpose step15 step10
  subsumption step17 step11


@[equational_result]
theorem Finite.Equation118_implies_Equation4435 (G : Type*) [Magma G] [Finite G] (h : Equation118 G) : Equation4435 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step10 : (sK0 ◇ (sK1 ◇ sK0)) ≠ ((sK0 ◇ sK1) ◇ sK0) := mod_symm nh
  have step11 (X Y : G) : ((Y ◇ (X ◇ Y)) ◇ Y) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (s ◇ Y)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (Y ◇ (s ◇ Y))) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (Y ◇ (s ◇ Y))) (fun s => (s ◇ Y)) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step15 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = ((X1 ◇ X0) ◇ X1) := superpose step11 step11
  have step25 : (sK0 ◇ (sK1 ◇ sK0)) ≠ (sK0 ◇ (sK1 ◇ sK0)) := superpose step15 step10
  subsumption step25 rfl


@[equational_result]
theorem Finite.Equation1276_implies_Equation4273 (G : Type*) [Magma G] [Finite G] (h : Equation1276 G) : Equation4273 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) : (X1 ◇ (((X0 ◇ X0) ◇ X0) ◇ X1)) = X0 := mod_symm (h ..)
  have step10 : (sK0 ◇ (sK0 ◇ sK0)) ≠ (sK1 ◇ (sK0 ◇ sK1)) := mod_symm nh
  have step11 (X Y : G) : (((Y ◇ (X ◇ Y)) ◇ (Y ◇ (X ◇ Y))) ◇ (Y ◇ (X ◇ Y))) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => ((s ◇ s) ◇ s)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (Y ◇ (s ◇ Y))) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (Y ◇ (s ◇ Y))) (fun s => ((s ◇ s) ◇ s)) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step17 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X1)) = (X2 ◇ (X0 ◇ X2)) := superpose step11 step9
  have step40 (X0 : G) : (sK0 ◇ (sK0 ◇ sK0)) ≠ (X0 ◇ (sK0 ◇ X0)) := superpose step17 step10
  subsumption step40 step17


@[equational_result]
theorem Finite.Equation1289_implies_Equation2507 (G : Type*) [Magma G] [Finite G] (h : Equation1289 G) : Equation2507 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step11 : sK0 ≠ ((sK1 ◇ ((sK0 ◇ sK1) ◇ sK1)) ◇ sK1) := mod_symm nh
  have step12 (X Y : G) : ((Y ◇ ((X ◇ Y) ◇ Y)) ◇ Y) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (s ◇ Y)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (Y ◇ ((s ◇ Y) ◇ Y))) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (Y ◇ ((s ◇ Y) ◇ Y))) (fun s => (s ◇ Y)) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step18 : sK0 ≠ sK0 := superpose step12 step11
  subsumption step18 rfl


@[equational_result]
theorem Finite.Equation1289_implies_Equation3116 (G : Type*) [Magma G] [Finite G] (h : Equation1289 G) : Equation3116 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step11 : sK0 ≠ ((((sK1 ◇ sK0) ◇ sK1) ◇ sK1) ◇ sK1) := mod_symm nh
  have step14 (X Y : G) : ((((Y ◇ X) ◇ Y) ◇ Y) ◇ Y) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (((s ◇ Y) ◇ Y) ◇ Y)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (Y ◇ s)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (Y ◇ s)) (fun s => (((s ◇ Y) ◇ Y) ◇ Y)) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step21 : sK0 ≠ sK0 := superpose step14 step11
  subsumption step21 rfl


@[equational_result]
theorem Finite.Equation1289_implies_Equation4435 (G : Type*) [Magma G] [Finite G] (h : Equation1289 G) : Equation4435 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step10 (X0 X1 : G) : (X1 ◇ (((X0 ◇ X1) ◇ X1) ◇ X1)) = X0 := mod_symm (h ..)
  have step11 : (sK0 ◇ (sK1 ◇ sK0)) ≠ ((sK0 ◇ sK1) ◇ sK0) := mod_symm nh
  have step14 (X Y : G) : ((((Y ◇ X) ◇ Y) ◇ Y) ◇ Y) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (((s ◇ Y) ◇ Y) ◇ Y)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (Y ◇ s)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (Y ◇ s)) (fun s => (((s ◇ Y) ◇ Y) ◇ Y)) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step21 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = ((X1 ◇ X0) ◇ X1) := superpose step14 step10
  have step33 : (sK0 ◇ (sK1 ◇ sK0)) ≠ (sK0 ◇ (sK1 ◇ sK0)) := superpose step21 step11
  subsumption step33 rfl


@[equational_result]
theorem Finite.Equation1431_implies_Equation1428 (G : Type*) [Magma G] [Finite G] (h : Equation1431 G) : Equation1428 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step8 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0))) = X0 := mod_symm (h ..)
  have step9 : sK0 ≠ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) := mod_symm nh
  have step10 (X Y : G) : ((X ◇ (Y ◇ X)) ◇ (X ◇ (Y ◇ X))) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (s ◇ s)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (s ◇ (Y ◇ s))) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (s ◇ (Y ◇ s))) (fun s => (s ◇ s)) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step14 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = (X0 ◇ (X2 ◇ X0)) := superpose step10 step8
  have step29 (X0 : G) : sK0 ≠ ((sK0 ◇ sK0) ◇ (sK0 ◇ (X0 ◇ sK0))) := superpose step14 step9
  have step41 : sK0 ≠ sK0 := superpose step8 step29
  subsumption step41 rfl


@[equational_result]
theorem Finite.Equation1431_implies_Equation4269 (G : Type*) [Magma G] [Finite G] (h : Equation1431 G) : Equation4269 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step8 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0))) = X0 := mod_symm (h ..)
  have step9 : (sK0 ◇ (sK0 ◇ sK0)) ≠ (sK0 ◇ (sK1 ◇ sK0)) := mod_symm nh
  have step10 (X Y : G) : ((X ◇ (Y ◇ X)) ◇ (X ◇ (Y ◇ X))) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (s ◇ s)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (s ◇ (Y ◇ s))) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (s ◇ (Y ◇ s))) (fun s => (s ◇ s)) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step14 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = (X0 ◇ (X2 ◇ X0)) := superpose step10 step8
  have step33 (X0 : G) : (sK0 ◇ (sK0 ◇ sK0)) ≠ (sK0 ◇ (X0 ◇ sK0)) := superpose step14 step9
  subsumption step33 step14


@[equational_result]
theorem Finite.Equation1491_implies_Equation65 (G : Type*) [Magma G] [Finite G] (h : Equation1491 G) : Equation65 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 : sK0 ≠ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) := mod_symm nh
  have step10 (X Y : G) : (Y ◇ (X ◇ (Y ◇ X))) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (Y ◇ s)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (s ◇ (Y ◇ s))) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (s ◇ (Y ◇ s))) (fun s => (Y ◇ s)) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step12 : sK0 ≠ sK0 := superpose step10 step9
  subsumption step12 rfl


@[equational_result]
theorem Finite.Equation1515_implies_Equation4590 (G : Type*) [Magma G] [Finite G] (h : Equation1515 G) : Equation4590 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step8 (X0 X1 : G) : ((X1 ◇ X1) ◇ (X0 ◇ (X0 ◇ X0))) = X0 := mod_symm (h ..)
  have step9 : ((sK0 ◇ sK0) ◇ sK0) ≠ ((sK1 ◇ sK1) ◇ sK0) := mod_symm nh
  have step10 (X Y : G) : (((Y ◇ Y) ◇ X) ◇ (((Y ◇ Y) ◇ X) ◇ ((Y ◇ Y) ◇ X))) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (s ◇ (s ◇ s))) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => ((Y ◇ Y) ◇ s)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => ((Y ◇ Y) ◇ s)) (fun s => (s ◇ (s ◇ s))) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step12 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ X0) = ((X2 ◇ X2) ◇ X0) := superpose step10 step8
  have step25 (X0 : G) : ((sK0 ◇ sK0) ◇ sK0) ≠ ((X0 ◇ X0) ◇ sK0) := superpose step12 step9
  subsumption step25 step12


@[equational_result]
theorem Finite.Equation1519_implies_Equation2128 (G : Type*) [Magma G] [Finite G] (h : Equation1519 G) : Equation2128 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 : sK0 ≠ (((sK1 ◇ sK1) ◇ sK0) ◇ (sK1 ◇ sK1)) := mod_symm nh
  have step10 (X Y : G) : (((Y ◇ Y) ◇ X) ◇ (Y ◇ Y)) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (s ◇ (Y ◇ Y))) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => ((Y ◇ Y) ◇ s)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => ((Y ◇ Y) ◇ s)) (fun s => (s ◇ (Y ◇ Y))) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step13 : sK0 ≠ sK0 := superpose step10 step9
  subsumption step13 rfl


@[equational_result]
theorem Finite.Equation1523_implies_Equation2132 (G : Type*) [Magma G] [Finite G] (h : Equation1523 G) : Equation2132 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have step9 : sK0 ≠ (((sK1 ◇ sK1) ◇ sK0) ◇ (sK2 ◇ sK2)) := mod_symm nh
  have step10 (X Y Z : G) : (((Y ◇ Y) ◇ X) ◇ (Z ◇ Z)) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (s ◇ (Z ◇ Z))) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => ((Y ◇ Y) ◇ s)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => ((Y ◇ Y) ◇ s)) (fun s => (s ◇ (Z ◇ Z))) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step21 : sK0 ≠ sK0 := superpose step10 step9
  subsumption step21 rfl


@[equational_result]
theorem Finite.Equation1526_implies_Equation1223 (G : Type*) [Magma G] [Finite G] (h : Equation1526 G) : Equation1223 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have step10 : sK0 ≠ (sK0 ◇ (((sK0 ◇ sK0) ◇ sK0) ◇ sK0)) := mod_symm nh
  have step12 (X Y : G) : (Y ◇ (((Y ◇ Y) ◇ X) ◇ Y)) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (Y ◇ (s ◇ Y))) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => ((Y ◇ Y) ◇ s)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => ((Y ◇ Y) ◇ s)) (fun s => (Y ◇ (s ◇ Y))) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step19 : sK0 ≠ sK0 := superpose step12 step10
  subsumption step19 rfl


@[equational_result]
theorem Finite.Equation1526_implies_Equation1323 (G : Type*) [Magma G] [Finite G] (h : Equation1526 G) : Equation1323 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step10 : sK0 ≠ (sK1 ◇ (((sK1 ◇ sK1) ◇ sK0) ◇ sK1)) := mod_symm nh
  have step12 (X Y : G) : (Y ◇ (((Y ◇ Y) ◇ X) ◇ Y)) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (Y ◇ (s ◇ Y))) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => ((Y ◇ Y) ◇ s)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => ((Y ◇ Y) ◇ s)) (fun s => (Y ◇ (s ◇ Y))) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step19 : sK0 ≠ sK0 := superpose step12 step10
  subsumption step19 rfl


@[equational_result]
theorem Finite.Equation1526_implies_Equation2744 (G : Type*) [Magma G] [Finite G] (h : Equation1526 G) : Equation2744 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step10 : sK0 ≠ (((sK1 ◇ sK1) ◇ (sK1 ◇ sK0)) ◇ sK1) := mod_symm nh
  have step11 (X Y : G) : (((Y ◇ Y) ◇ (Y ◇ X)) ◇ Y) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (s ◇ Y)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => ((Y ◇ Y) ◇ (Y ◇ s))) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => ((Y ◇ Y) ◇ (Y ◇ s))) (fun s => (s ◇ Y)) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step17 : sK0 ≠ sK0 := superpose step11 step10
  subsumption step17 rfl


@[equational_result]
theorem Finite.Equation1630_implies_Equation4268 (G : Type*) [Magma G] [Finite G] (h : Equation1630 G) : Equation4268 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step8 (X0 X1 : G) : ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) = X0 := mod_symm (h ..)
  have step9 : (sK0 ◇ (sK0 ◇ sK0)) ≠ (sK0 ◇ (sK0 ◇ sK1)) := mod_symm nh
  have step10 (X Y : G) : ((X ◇ (X ◇ Y)) ◇ (X ◇ (X ◇ Y))) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (s ◇ s)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (s ◇ (s ◇ Y))) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (s ◇ (s ◇ Y))) (fun s => (s ◇ s)) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step17 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ X2)) := superpose step10 step8
  have step34 (X0 : G) : (sK0 ◇ (sK0 ◇ sK0)) ≠ (sK0 ◇ (sK0 ◇ X0)) := superpose step17 step9
  subsumption step34 step17


@[equational_result]
theorem Finite.Equation1648_implies_Equation206 (G : Type*) [Magma G] [Finite G] (h : Equation1648 G) : Equation206 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 : sK0 ≠ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) := mod_symm nh
  have step10 (X Y : G) : ((X ◇ (X ◇ Y)) ◇ Y) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (s ◇ Y)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (s ◇ (s ◇ Y))) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (s ◇ (s ◇ Y))) (fun s => (s ◇ Y)) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step12 : sK0 ≠ sK0 := superpose step10 step9
  subsumption step12 rfl


@[equational_result]
theorem Finite.Equation1692_implies_Equation63 (G : Type*) [Magma G] [Finite G] (h : Equation1692 G) : Equation63 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 : sK0 ≠ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) := mod_symm nh
  have step10 (X Y : G) : (Y ◇ (X ◇ (X ◇ Y))) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (Y ◇ s)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (s ◇ (s ◇ Y))) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (s ◇ (s ◇ Y))) (fun s => (Y ◇ s)) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step13 : sK0 ≠ sK0 := superpose step10 step9
  subsumption step13 rfl


@[equational_result]
theorem Finite.Equation1722_implies_Equation1832 (G : Type*) [Magma G] [Finite G] (h : Equation1722 G) : Equation1832 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have step10 : sK0 ≠ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have step11 (X Y : G) : (((Y ◇ Y) ◇ (X ◇ Y)) ◇ Y) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (s ◇ Y)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => ((Y ◇ Y) ◇ (s ◇ Y))) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => ((Y ◇ Y) ◇ (s ◇ Y))) (fun s => (s ◇ Y)) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step15 (X0 X1 : G) : ((X1 ◇ X1) ◇ (X0 ◇ X1)) = (((X1 ◇ X1) ◇ X0) ◇ X1) := superpose step11 step11
  have step18 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) := superpose step11 step15
  have step47 (X0 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) = X0 := superpose step18 step11
  have step74 : sK0 ≠ sK0 := superpose step47 step10
  subsumption step74 rfl


@[equational_result]
theorem Finite.Equation1722_implies_Equation2644 (G : Type*) [Magma G] [Finite G] (h : Equation1722 G) : Equation2644 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have step10 : sK0 ≠ (((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) ◇ sK0) := mod_symm nh
  have step11 (X Y : G) : (((Y ◇ Y) ◇ (X ◇ Y)) ◇ Y) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (s ◇ Y)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => ((Y ◇ Y) ◇ (s ◇ Y))) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => ((Y ◇ Y) ◇ (s ◇ Y))) (fun s => (s ◇ Y)) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step16 : sK0 ≠ sK0 := superpose step11 step10
  subsumption step16 rfl


@[equational_result]
theorem Finite.Equation1722_implies_Equation2737 (G : Type*) [Magma G] [Finite G] (h : Equation1722 G) : Equation2737 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step10 : sK0 ≠ (((sK1 ◇ sK1) ◇ (sK0 ◇ sK1)) ◇ sK1) := mod_symm nh
  have step11 (X Y : G) : (((Y ◇ Y) ◇ (X ◇ Y)) ◇ Y) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (s ◇ Y)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => ((Y ◇ Y) ◇ (s ◇ Y))) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => ((Y ◇ Y) ◇ (s ◇ Y))) (fun s => (s ◇ Y)) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step16 : sK0 ≠ sK0 := superpose step11 step10
  subsumption step16 rfl


@[equational_result]
theorem Finite.Equation1722_implies_Equation3143 (G : Type*) [Magma G] [Finite G] (h : Equation1722 G) : Equation3143 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step10 : sK0 ≠ ((((sK1 ◇ sK1) ◇ sK0) ◇ sK1) ◇ sK1) := mod_symm nh
  have step11 (X Y : G) : (((Y ◇ Y) ◇ (X ◇ Y)) ◇ Y) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (s ◇ Y)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => ((Y ◇ Y) ◇ (s ◇ Y))) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => ((Y ◇ Y) ◇ (s ◇ Y))) (fun s => (s ◇ Y)) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step15 (X0 X1 : G) : (((X1 ◇ X1) ◇ X0) ◇ X1) = ((X1 ◇ X1) ◇ (X0 ◇ X1)) := superpose step11 step11
  have step16 : sK0 ≠ (((sK1 ◇ sK1) ◇ (sK0 ◇ sK1)) ◇ sK1) := superpose step15 step10
  subsumption step16 step11


@[equational_result]
theorem Finite.Equation1729_implies_Equation917 (G : Type*) [Magma G] [Finite G] (h : Equation1729 G) : Equation917 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step10 : sK0 ≠ (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK0 ◇ sK1))) := mod_symm nh
  have step11 (X Y : G) : (Y ◇ ((Y ◇ Y) ◇ (X ◇ Y))) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (Y ◇ s)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => ((Y ◇ Y) ◇ (s ◇ Y))) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => ((Y ◇ Y) ◇ (s ◇ Y))) (fun s => (Y ◇ s)) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step16 : sK0 ≠ sK0 := superpose step11 step10
  subsumption step16 rfl


@[equational_result]
theorem Finite.Equation476_implies_Equation3862 (G : Type*) [Magma G] [Finite G] (h : Equation476 G) : Equation3862 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have step8 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0)))) = X0 := mod_symm (h ..)
  have step9 : (sK0 ◇ sK0) ≠ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := mod_symm nh
  have step10 (X Y : G) : ((Y ◇ X) ◇ (Y ◇ (Y ◇ (Y ◇ X)))) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (s ◇ (Y ◇ (Y ◇ s)))) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (Y ◇ s)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (Y ◇ s)) (fun s => (s ◇ (Y ◇ (Y ◇ s)))) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step15 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose step8 step10
  have step17 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose step15 step9
  subsumption step17 rfl


@[equational_result]
theorem Finite.Equation477_implies_Equation1492 (G : Type*) [Magma G] [Finite G] (h : Equation477 G) : Equation1492 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 : sK0 ≠ ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK1))) := mod_symm nh
  have step10 (X Y : G) : ((Y ◇ X) ◇ (Y ◇ (Y ◇ Y))) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (s ◇ (Y ◇ (Y ◇ Y)))) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (Y ◇ s)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (Y ◇ s)) (fun s => (s ◇ (Y ◇ (Y ◇ Y)))) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step13 : sK0 ≠ sK0 := superpose step10 step9
  subsumption step13 rfl


@[equational_result]
theorem Finite.Equation477_implies_Equation1519 (G : Type*) [Magma G] [Finite G] (h : Equation477 G) : Equation1519 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step8 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1)))) = X0 := mod_symm (h ..)
  have step9 : sK0 ≠ ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1))) := mod_symm nh
  have step10 (X Y : G) : ((Y ◇ X) ◇ (Y ◇ (Y ◇ Y))) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (s ◇ (Y ◇ (Y ◇ Y)))) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (Y ◇ s)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (Y ◇ s)) (fun s => (s ◇ (Y ◇ (Y ◇ Y)))) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step11 (X0 X1 : G) : (X1 ◇ (X1 ◇ X1)) = (X0 ◇ ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0)))) := superpose step10 step10
  have step17 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) := superpose step10 step11
  have step45 (X0 : G) : ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = (((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))))) := superpose step17 step11
  have step47 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose step10 step45
  have step125 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0))) = X1 := superpose step47 step8
  have step174 : sK0 ≠ sK0 := superpose step125 step9
  subsumption step174 rfl


@[equational_result]
theorem Finite.Equation477_implies_Equation3150 (G : Type*) [Magma G] [Finite G] (h : Equation477 G) : Equation3150 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step8 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1)))) = X0 := mod_symm (h ..)
  have step9 : sK0 ≠ ((((sK1 ◇ sK1) ◇ sK1) ◇ sK0) ◇ sK1) := mod_symm nh
  have step10 (X Y : G) : ((Y ◇ X) ◇ (Y ◇ (Y ◇ Y))) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (s ◇ (Y ◇ (Y ◇ Y)))) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (Y ◇ s)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (Y ◇ s)) (fun s => (s ◇ (Y ◇ (Y ◇ Y)))) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step11 (X0 X1 : G) : (X1 ◇ (X1 ◇ X1)) = (X0 ◇ ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0)))) := superpose step10 step10
  have step15 (X0 X1 : G) : ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) = ((X1 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X0))) := superpose step10 step11
  have step17 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) := superpose step10 step11
  have step45 (X0 : G) : ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = (((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))))) := superpose step17 step11
  have step47 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose step10 step45
  have step67 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X2 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X1 ◇ X1))))) = X2 := superpose step15 step8
  have step126 (X0 X1 : G) : (((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X0)) = X1 := superpose step47 step10
  have step265 (X0 X1 X2 : G) : (((X0 ◇ X0) ◇ X1) ◇ (X2 ◇ ((X0 ◇ X0) ◇ (X1 ◇ (X1 ◇ X1))))) = X2 := superpose step47 step67
  have step773 (X0 X1 : G) : (((X0 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)) = X1 := superpose step10 step265
  have step941 (X0 X1 : G) : ((((X0 ◇ X0) ◇ X0) ◇ X1) ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0))) = X1 := superpose step773 step10
  have step1009 (X0 X1 : G) : ((((X0 ◇ X0) ◇ X0) ◇ X1) ◇ X0) = X1 := superpose step126 step941
  have step1176 : sK0 ≠ sK0 := superpose step1009 step9
  subsumption step1176 rfl


@[equational_result]
theorem Finite.Equation481_implies_Equation1488 (G : Type*) [Magma G] [Finite G] (h : Equation481 G) : Equation1488 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step8 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) = X0 := mod_symm (h ..)
  have step9 : sK0 ≠ ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ sK0))) := mod_symm nh
  have step10 (X Y Z : G) : ((Y ◇ X) ◇ (Y ◇ (Z ◇ Z))) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (s ◇ (Y ◇ (Z ◇ Z)))) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (Y ◇ s)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (Y ◇ s)) (fun s => (s ◇ (Y ◇ (Z ◇ Z)))) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step12 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ X1) := superpose step8 step8
  have step17 (X0 : G) : sK0 ≠ ((sK1 ◇ sK0) ◇ (sK1 ◇ (X0 ◇ X0))) := superpose step12 step9
  subsumption step17 step10


@[equational_result]
theorem Finite.Equation481_implies_Equation1496 (G : Type*) [Magma G] [Finite G] (h : Equation481 G) : Equation1496 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have step8 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) = X0 := mod_symm (h ..)
  have step9 : sK0 ≠ ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK2 ◇ sK2))) := mod_symm nh
  have step10 (X Y Z : G) : ((Y ◇ X) ◇ (Y ◇ (Z ◇ Z))) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (s ◇ (Y ◇ (Z ◇ Z)))) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (Y ◇ s)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (Y ◇ s)) (fun s => (s ◇ (Y ◇ (Z ◇ Z)))) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step12 (X0 X1 : G) : (X1 ◇ X1) = (X0 ◇ X0) := superpose step8 step8
  have step20 (X0 : G) : sK0 ≠ ((sK1 ◇ sK0) ◇ (sK1 ◇ (X0 ◇ X0))) := superpose step12 step9
  subsumption step20 step10


@[equational_result]
theorem Finite.Equation481_implies_Equation2041 (G : Type*) [Magma G] [Finite G] (h : Equation481 G) : Equation2041 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step8 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) = X0 := mod_symm (h ..)
  have step9 : sK0 ≠ (((sK0 ◇ sK0) ◇ sK1) ◇ (sK0 ◇ sK1)) := mod_symm nh
  have step10 (X Y Z : G) : ((Y ◇ X) ◇ (Y ◇ (Z ◇ Z))) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (s ◇ (Y ◇ (Z ◇ Z)))) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (Y ◇ s)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (Y ◇ s)) (fun s => (s ◇ (Y ◇ (Z ◇ Z)))) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step38 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ X0) ◇ (X2 ◇ X0)) = X2 := superpose step10 step8
  have step78 : sK0 ≠ sK0 := superpose step38 step9
  subsumption step78 rfl


@[equational_result]
theorem Finite.Equation481_implies_Equation3161 (G : Type*) [Magma G] [Finite G] (h : Equation481 G) : Equation3161 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have step9 : sK0 ≠ ((((sK1 ◇ sK1) ◇ sK2) ◇ sK0) ◇ sK2) := mod_symm nh
  have step10 (X Y Z : G) : ((Y ◇ X) ◇ (Y ◇ (Z ◇ Z))) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (s ◇ (Y ◇ (Z ◇ Z)))) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (Y ◇ s)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (Y ◇ s)) (fun s => (s ◇ (Y ◇ (Z ◇ Z)))) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step35 (X0 X1 X2 : G) : ((((X1 ◇ X1) ◇ X0) ◇ X2) ◇ X0) = X2 := superpose step10 step10
  have step55 : sK0 ≠ sK0 := superpose step35 step9
  subsumption step55 rfl


@[equational_result]
theorem Finite.Equation504_implies_Equation1629 (G : Type*) [Magma G] [Finite G] (h : Equation504 G) : Equation1629 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have step9 (X0 X1 : G) : (X1 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X1)))) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ sK0)) := mod_symm nh
  have step11 (X Y : G) : ((Y ◇ (Y ◇ X)) ◇ (Y ◇ Y)) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (s ◇ (Y ◇ Y))) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (Y ◇ (Y ◇ s))) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (Y ◇ (Y ◇ s))) (fun s => (s ◇ (Y ◇ Y))) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step13 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X1 ◇ X1))) = ((X1 ◇ X0) ◇ (X1 ◇ X1)) := superpose step9 step11
  have step24 (X0 X1 : G) : ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))))) = X1 := superpose step13 step9
  have step53 (X0 : G) : ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) = X0 := superpose step9 step24
  have step102 : sK0 ≠ sK0 := superpose step53 step10
  subsumption step102 rfl


@[equational_result]
theorem Finite.Equation504_implies_Equation1925 (G : Type*) [Magma G] [Finite G] (h : Equation504 G) : Equation1925 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step10 : sK0 ≠ ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK1)) := mod_symm nh
  have step11 (X Y : G) : ((Y ◇ (Y ◇ X)) ◇ (Y ◇ Y)) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (s ◇ (Y ◇ Y))) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (Y ◇ (Y ◇ s))) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (Y ◇ (Y ◇ s))) (fun s => (s ◇ (Y ◇ Y))) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step15 : sK0 ≠ sK0 := superpose step11 step10
  subsumption step15 rfl


@[equational_result]
theorem Finite.Equation504_implies_Equation817 (G : Type*) [Magma G] [Finite G] (h : Equation504 G) : Equation817 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have step9 (X0 X1 : G) : (X1 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X1)))) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := mod_symm nh
  have step11 (X Y : G) : ((Y ◇ (Y ◇ X)) ◇ (Y ◇ Y)) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (s ◇ (Y ◇ Y))) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (Y ◇ (Y ◇ s))) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (Y ◇ (Y ◇ s))) (fun s => (s ◇ (Y ◇ Y))) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step13 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X1 ◇ X1))) = ((X1 ◇ X0) ◇ (X1 ◇ X1)) := superpose step9 step11
  have step15 : sK0 ≠ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := superpose step13 step10
  subsumption step15 step9


@[equational_result]
theorem Finite.Equation504_implies_Equation910 (G : Type*) [Magma G] [Finite G] (h : Equation504 G) : Equation910 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) : (X1 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X1)))) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ (sK1 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK1))) := mod_symm nh
  have step11 (X Y : G) : ((Y ◇ (Y ◇ X)) ◇ (Y ◇ Y)) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (s ◇ (Y ◇ Y))) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (Y ◇ (Y ◇ s))) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (Y ◇ (Y ◇ s))) (fun s => (s ◇ (Y ◇ Y))) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step13 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X1 ◇ X1))) = ((X1 ◇ X0) ◇ (X1 ◇ X1)) := superpose step9 step11
  have step15 : sK0 ≠ (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := superpose step13 step10
  subsumption step15 step9


@[equational_result]
theorem Finite.Equation511_implies_Equation2338 (G : Type*) [Magma G] [Finite G] (h : Equation511 G) : Equation2338 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step11 : sK0 ≠ ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ sK1) := mod_symm nh
  have step12 (X Y : G) : ((Y ◇ (Y ◇ (Y ◇ X))) ◇ Y) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (s ◇ Y)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (Y ◇ (Y ◇ (Y ◇ s)))) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (Y ◇ (Y ◇ (Y ◇ s)))) (fun s => (s ◇ Y)) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step19 : sK0 ≠ sK0 := superpose step12 step11
  subsumption step19 rfl


@[equational_result]
theorem Finite.Equation511_implies_Equation4435 (G : Type*) [Magma G] [Finite G] (h : Equation511 G) : Equation4435 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step10 (X0 X1 : G) : (X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1)))) = X0 := mod_symm (h ..)
  have step11 : (sK0 ◇ (sK1 ◇ sK0)) ≠ ((sK0 ◇ sK1) ◇ sK0) := mod_symm nh
  have step12 (X Y : G) : ((Y ◇ (Y ◇ (Y ◇ X))) ◇ Y) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (s ◇ Y)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (Y ◇ (Y ◇ (Y ◇ s)))) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (Y ◇ (Y ◇ (Y ◇ s)))) (fun s => (s ◇ Y)) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step18 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = ((X1 ◇ X0) ◇ X1) := superpose step10 step12
  have step25 : (sK0 ◇ (sK1 ◇ sK0)) ≠ (sK0 ◇ (sK1 ◇ sK0)) := superpose step18 step11
  subsumption step25 rfl


@[equational_result]
theorem Finite.Equation511_implies_Equation714 (G : Type*) [Magma G] [Finite G] (h : Equation511 G) : Equation714 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step10 (X0 X1 : G) : (X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1)))) = X0 := mod_symm (h ..)
  have step11 : sK0 ≠ (sK1 ◇ (sK1 ◇ ((sK1 ◇ sK0) ◇ sK1))) := mod_symm nh
  have step12 (X Y : G) : ((Y ◇ (Y ◇ (Y ◇ X))) ◇ Y) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (s ◇ Y)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (Y ◇ (Y ◇ (Y ◇ s)))) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (Y ◇ (Y ◇ (Y ◇ s)))) (fun s => (s ◇ Y)) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step18 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = ((X1 ◇ X0) ◇ X1) := superpose step10 step12
  have step21 : sK0 ≠ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := superpose step18 step11
  subsumption step21 step10


@[equational_result]
theorem Finite.Equation63_implies_Equation1692 (G : Type*) [Magma G] [Finite G] (h : Equation63 G) : Equation1692 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 : sK0 ≠ ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ sK1)) := mod_symm nh
  have step10 (X Y : G) : ((Y ◇ X) ◇ ((Y ◇ X) ◇ Y)) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (s ◇ (s ◇ Y))) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (Y ◇ s)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (Y ◇ s)) (fun s => (s ◇ (s ◇ Y))) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step17 : sK0 ≠ sK0 := superpose step10 step9
  subsumption step17 rfl


@[equational_result]
theorem Finite.Equation65_implies_Equation1426 (G : Type*) [Magma G] [Finite G] (h : Equation65 G) : Equation1426 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have step9 : sK0 ≠ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := mod_symm nh
  have step10 (X Y : G) : ((Y ◇ X) ◇ (Y ◇ (Y ◇ X))) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (s ◇ (Y ◇ s))) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (Y ◇ s)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (Y ◇ s)) (fun s => (s ◇ (Y ◇ s))) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step14 : sK0 ≠ sK0 := superpose step10 step9
  subsumption step14 rfl


@[equational_result]
theorem Finite.Equation65_implies_Equation1491 (G : Type*) [Magma G] [Finite G] (h : Equation65 G) : Equation1491 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 : sK0 ≠ ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK0))) := mod_symm nh
  have step10 (X Y : G) : ((Y ◇ X) ◇ (Y ◇ (Y ◇ X))) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (s ◇ (Y ◇ s))) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (Y ◇ s)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (Y ◇ s)) (fun s => (s ◇ (Y ◇ s))) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step14 : sK0 ≠ sK0 := superpose step10 step9
  subsumption step14 rfl


@[equational_result]
theorem Finite.Equation65_implies_Equation359 (G : Type*) [Magma G] [Finite G] (h : Equation65 G) : Equation359 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have step8 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X1 ◇ X0))) = X0 := mod_symm (h ..)
  have step9 : (sK0 ◇ sK0) ≠ ((sK0 ◇ sK0) ◇ sK0) := mod_symm nh
  have step10 (X Y : G) : ((Y ◇ X) ◇ (Y ◇ (Y ◇ X))) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (s ◇ (Y ◇ s))) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (Y ◇ s)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (Y ◇ s)) (fun s => (s ◇ (Y ◇ s))) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step13 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose step8 step10
  have step16 (X0 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose step13 step8
  have step47 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) := superpose step16 step16
  have step53 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose step13 step47
  have step86 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0)))) := superpose step53 step8
  have step93 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose step10 step86
  have step118 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose step93 step9
  subsumption step118 rfl


@[equational_result]
theorem Finite.Equation65_implies_Equation3862 (G : Type*) [Magma G] [Finite G] (h : Equation65 G) : Equation3862 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have step8 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X1 ◇ X0))) = X0 := mod_symm (h ..)
  have step9 : (sK0 ◇ sK0) ≠ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := mod_symm nh
  have step10 (X Y : G) : ((Y ◇ X) ◇ (Y ◇ (Y ◇ X))) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (s ◇ (Y ◇ s))) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (Y ◇ s)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (Y ◇ s)) (fun s => (s ◇ (Y ◇ s))) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step13 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose step8 step10
  have step15 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose step13 step9
  subsumption step15 rfl


@[equational_result]
theorem Finite.Equation65_implies_Equation614 (G : Type*) [Magma G] [Finite G] (h : Equation65 G) : Equation614 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have step8 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X1 ◇ X0))) = X0 := mod_symm (h ..)
  have step9 : sK0 ≠ (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0))) := mod_symm nh
  have step10 (X Y : G) : ((Y ◇ X) ◇ (Y ◇ (Y ◇ X))) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (s ◇ (Y ◇ s))) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (Y ◇ s)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (Y ◇ s)) (fun s => (s ◇ (Y ◇ s))) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step12 (X0 X1 : G) : (X1 ◇ (X1 ◇ X0)) = (X0 ◇ ((X1 ◇ X0) ◇ X0)) := superpose step10 step10
  have step15 : sK0 ≠ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := superpose step12 step9
  subsumption step15 step8


@[equational_result]
theorem Finite.Equation65_implies_Equation817 (G : Type*) [Magma G] [Finite G] (h : Equation65 G) : Equation817 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have step8 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X1 ◇ X0))) = X0 := mod_symm (h ..)
  have step9 : sK0 ≠ (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := mod_symm nh
  have step10 (X Y : G) : ((Y ◇ X) ◇ (Y ◇ (Y ◇ X))) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (s ◇ (Y ◇ s))) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (Y ◇ s)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (Y ◇ s)) (fun s => (s ◇ (Y ◇ s))) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step13 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose step8 step10
  have step16 (X0 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose step13 step8
  have step47 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) := superpose step16 step16
  have step53 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ X0)) := superpose step13 step47
  have step54 : sK0 ≠ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := superpose step53 step9
  subsumption step54 step8


@[equational_result]
theorem Finite.Equation680_implies_Equation1629 (G : Type*) [Magma G] [Finite G] (h : Equation680 G) : Equation1629 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have step9 : sK0 ≠ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ sK0)) := mod_symm nh
  have step10 (X Y : G) : ((Y ◇ X) ◇ ((Y ◇ Y) ◇ Y)) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (s ◇ ((Y ◇ Y) ◇ Y))) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (Y ◇ s)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (Y ◇ s)) (fun s => (s ◇ ((Y ◇ Y) ◇ Y))) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step13 : sK0 ≠ sK0 := superpose step10 step9
  subsumption step13 rfl


@[equational_result]
theorem Finite.Equation680_implies_Equation1695 (G : Type*) [Magma G] [Finite G] (h : Equation680 G) : Equation1695 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 : sK0 ≠ ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK1) ◇ sK1)) := mod_symm nh
  have step10 (X Y : G) : ((Y ◇ X) ◇ ((Y ◇ Y) ◇ Y)) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (s ◇ ((Y ◇ Y) ◇ Y))) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (Y ◇ s)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (Y ◇ s)) (fun s => (s ◇ ((Y ◇ Y) ◇ Y))) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step13 : sK0 ≠ sK0 := superpose step10 step9
  subsumption step13 rfl


@[equational_result]
theorem Finite.Equation680_implies_Equation1832 (G : Type*) [Magma G] [Finite G] (h : Equation680 G) : Equation1832 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have step8 (X0 X1 : G) : (X1 ◇ (X0 ◇ ((X1 ◇ X1) ◇ X1))) = X0 := mod_symm (h ..)
  have step9 : sK0 ≠ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have step10 (X Y : G) : ((Y ◇ X) ◇ ((Y ◇ Y) ◇ Y)) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (s ◇ ((Y ◇ Y) ◇ Y))) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (Y ◇ s)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (Y ◇ s)) (fun s => (s ◇ ((Y ◇ Y) ◇ Y))) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step12 (X0 X1 : G) : ((X1 ◇ X1) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0))) := superpose step10 step10
  have step16 (X0 X1 : G) : (((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)) = (((X1 ◇ X1) ◇ X1) ◇ ((X0 ◇ X0) ◇ X0)) := superpose step10 step12
  have step32 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (((X0 ◇ X0) ◇ X0) ◇ ((X1 ◇ X1) ◇ X1)))) = X2 := superpose step16 step8
  have step132 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ (X1 ◇ X0)) = X1 := superpose step10 step32
  have step190 : sK0 ≠ sK0 := superpose step132 step9
  subsumption step190 rfl


@[equational_result]
theorem Finite.Equation680_implies_Equation2947 (G : Type*) [Magma G] [Finite G] (h : Equation680 G) : Equation2947 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 : sK0 ≠ (((sK1 ◇ (sK1 ◇ sK1)) ◇ sK0) ◇ sK1) := mod_symm nh
  have step10 (X Y : G) : ((Y ◇ X) ◇ ((Y ◇ Y) ◇ Y)) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (s ◇ ((Y ◇ Y) ◇ Y))) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (Y ◇ s)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (Y ◇ s)) (fun s => (s ◇ ((Y ◇ Y) ◇ Y))) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step12 (X0 X1 : G) : ((X1 ◇ X1) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0))) := superpose step10 step10
  have step16 (X0 X1 : G) : (((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)) = (((X1 ◇ X1) ◇ X1) ◇ ((X0 ◇ X0) ◇ X0)) := superpose step10 step12
  have step31 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X2) ◇ (((X0 ◇ X0) ◇ X0) ◇ ((X1 ◇ X1) ◇ X1))) = X2 := superpose step16 step10
  have step57 (X0 X1 : G) : (((X0 ◇ (X0 ◇ X0)) ◇ X1) ◇ X0) = X1 := superpose step10 step31
  have step106 : sK0 ≠ sK0 := superpose step57 step9
  subsumption step106 rfl


@[equational_result]
theorem Finite.Equation707_implies_Equation1223 (G : Type*) [Magma G] [Finite G] (h : Equation707 G) : Equation1223 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have step11 : sK0 ≠ (sK0 ◇ (((sK0 ◇ sK0) ◇ sK0) ◇ sK0)) := mod_symm nh
  have step14 (X Y : G) : (Y ◇ (((Y ◇ X) ◇ Y) ◇ Y)) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (Y ◇ ((s ◇ Y) ◇ Y))) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (Y ◇ s)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (Y ◇ s)) (fun s => (Y ◇ ((s ◇ Y) ◇ Y))) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step21 : sK0 ≠ sK0 := superpose step14 step11
  subsumption step21 rfl


@[equational_result]
theorem Finite.Equation707_implies_Equation1316 (G : Type*) [Magma G] [Finite G] (h : Equation707 G) : Equation1316 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step11 : sK0 ≠ (sK1 ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK1)) := mod_symm nh
  have step14 (X Y : G) : (Y ◇ (((Y ◇ X) ◇ Y) ◇ Y)) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (Y ◇ ((s ◇ Y) ◇ Y))) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (Y ◇ s)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (Y ◇ s)) (fun s => (Y ◇ ((s ◇ Y) ◇ Y))) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step21 : sK0 ≠ sK0 := superpose step14 step11
  subsumption step21 rfl


@[equational_result]
theorem Finite.Equation707_implies_Equation2238 (G : Type*) [Magma G] [Finite G] (h : Equation707 G) : Equation2238 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have step11 : sK0 ≠ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ sK0) := mod_symm nh
  have step12 (X Y : G) : ((Y ◇ (Y ◇ (X ◇ Y))) ◇ Y) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (s ◇ Y)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (Y ◇ (Y ◇ (s ◇ Y)))) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (Y ◇ (Y ◇ (s ◇ Y)))) (fun s => (s ◇ Y)) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step18 : sK0 ≠ sK0 := superpose step12 step11
  subsumption step18 rfl


@[equational_result]
theorem Finite.Equation707_implies_Equation2940 (G : Type*) [Magma G] [Finite G] (h : Equation707 G) : Equation2940 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step11 : sK0 ≠ (((sK1 ◇ (sK1 ◇ sK0)) ◇ sK1) ◇ sK1) := mod_symm nh
  have step12 (X Y : G) : ((Y ◇ (Y ◇ (X ◇ Y))) ◇ Y) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (s ◇ Y)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (Y ◇ (Y ◇ (s ◇ Y)))) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (Y ◇ (Y ◇ (s ◇ Y)))) (fun s => (s ◇ Y)) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step17 (X0 X1 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X1 ◇ (X1 ◇ (X0 ◇ X1))) := superpose step12 step12
  have step19 : sK0 ≠ ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ sK1) := superpose step17 step11
  subsumption step19 step12


@[equational_result]
theorem Finite.Equation713_implies_Equation1426 (G : Type*) [Magma G] [Finite G] (h : Equation713 G) : Equation1426 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have step9 (X0 X1 : G) : (X1 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X0))) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := mod_symm nh
  have step11 (X Y : G) : ((Y ◇ (Y ◇ (Y ◇ X))) ◇ (Y ◇ (Y ◇ X))) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => ((Y ◇ s) ◇ s)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (Y ◇ (Y ◇ s))) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (Y ◇ (Y ◇ s))) (fun s => ((Y ◇ s) ◇ s)) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step12 (X Y : G) : (Y ◇ ((Y ◇ (Y ◇ X)) ◇ (Y ◇ X))) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (Y ◇ ((Y ◇ s) ◇ s))) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (Y ◇ s)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (Y ◇ s)) (fun s => (Y ◇ ((Y ◇ s) ◇ s))) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step14 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = (X1 ◇ (X0 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X0)))) := superpose step9 step12
  have step15 (X0 X1 : G) : (X1 ◇ ((X1 ◇ X0) ◇ X0)) = ((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)) := superpose step12 step12
  have step21 (X0 X1 : G) : (X1 ◇ (X1 ◇ X0)) = ((X1 ◇ (X1 ◇ (X1 ◇ X0))) ◇ ((X1 ◇ (X1 ◇ (X1 ◇ X0))) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0))))) := superpose step11 step9
  have step26 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose step9 step14
  have step39 (X0 X1 : G) : ((X1 ◇ (X1 ◇ (X1 ◇ X0))) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0)))) = (((X1 ◇ (X1 ◇ (X1 ◇ X0))) ◇ X0) ◇ X0) := superpose step11 step15
  have step54 (X0 X1 : G) : (X1 ◇ (X1 ◇ X0)) = ((X1 ◇ (X1 ◇ (X1 ◇ X0))) ◇ (((X1 ◇ (X1 ◇ (X1 ◇ X0))) ◇ X0) ◇ X0)) := superpose step39 step21
  have step64 (X0 : G) : ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0))) = X0 := superpose step26 step9
  have step67 (X0 : G) : ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = X0 := superpose step26 step64
  have step75 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ ((((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ X0) ◇ X0)) := superpose step26 step54
  have step90 (X0 : G) : (X0 ◇ ((X0 ◇ X0) ◇ X0)) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose step67 step75
  have step91 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose step26 step90
  have step93 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose step91 step67
  have step158 : sK0 ≠ sK0 := superpose step93 step10
  subsumption step158 rfl


@[equational_result]
theorem Finite.Equation713_implies_Equation359 (G : Type*) [Magma G] [Finite G] (h : Equation713 G) : Equation359 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have step9 (X0 X1 : G) : (X1 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X0))) = X0 := mod_symm (h ..)
  have step10 : (sK0 ◇ sK0) ≠ ((sK0 ◇ sK0) ◇ sK0) := mod_symm nh
  have step12 (X Y : G) : (Y ◇ ((Y ◇ (Y ◇ X)) ◇ (Y ◇ X))) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (Y ◇ ((Y ◇ s) ◇ s))) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (Y ◇ s)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (Y ◇ s)) (fun s => (Y ◇ ((Y ◇ s) ◇ s))) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step14 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = (X1 ◇ (X0 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X0)))) := superpose step9 step12
  have step26 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose step9 step14
  have step65 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose step26 step10
  subsumption step65 rfl


@[equational_result]
theorem Finite.Equation713_implies_Equation3862 (G : Type*) [Magma G] [Finite G] (h : Equation713 G) : Equation3862 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have step9 (X0 X1 : G) : (X1 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X0))) = X0 := mod_symm (h ..)
  have step10 : (sK0 ◇ sK0) ≠ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := mod_symm nh
  have step11 (X Y : G) : ((Y ◇ (Y ◇ (Y ◇ X))) ◇ (Y ◇ (Y ◇ X))) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => ((Y ◇ s) ◇ s)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (Y ◇ (Y ◇ s))) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (Y ◇ (Y ◇ s))) (fun s => ((Y ◇ s) ◇ s)) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step12 (X Y : G) : (Y ◇ ((Y ◇ (Y ◇ X)) ◇ (Y ◇ X))) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (Y ◇ ((Y ◇ s) ◇ s))) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (Y ◇ s)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (Y ◇ s)) (fun s => (Y ◇ ((Y ◇ s) ◇ s))) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step14 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = (X1 ◇ (X0 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X0)))) := superpose step9 step12
  have step15 (X0 X1 : G) : (X1 ◇ ((X1 ◇ X0) ◇ X0)) = ((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)) := superpose step12 step12
  have step20 (X0 X1 : G) : (X1 ◇ (X1 ◇ X0)) = (((X1 ◇ (X1 ◇ (X1 ◇ X0))) ◇ ((X1 ◇ (X1 ◇ (X1 ◇ X0))) ◇ X0)) ◇ ((X1 ◇ (X1 ◇ (X1 ◇ X0))) ◇ X0)) := superpose step11 step11
  have step21 (X0 X1 : G) : (X1 ◇ (X1 ◇ X0)) = ((X1 ◇ (X1 ◇ (X1 ◇ X0))) ◇ ((X1 ◇ (X1 ◇ (X1 ◇ X0))) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0))))) := superpose step11 step9
  have step26 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose step9 step14
  have step28 (X0 : G) : (X0 ◇ ((X0 ◇ X0) ◇ X0)) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) := superpose step14 step11
  have step35 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := superpose step26 step28
  have step39 (X0 X1 : G) : ((X1 ◇ (X1 ◇ (X1 ◇ X0))) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0)))) = (((X1 ◇ (X1 ◇ (X1 ◇ X0))) ◇ X0) ◇ X0) := superpose step11 step15
  have step54 (X0 X1 : G) : (X1 ◇ (X1 ◇ X0)) = ((X1 ◇ (X1 ◇ (X1 ◇ X0))) ◇ (((X1 ◇ (X1 ◇ (X1 ◇ X0))) ◇ X0) ◇ X0)) := superpose step39 step21
  have step64 (X0 : G) : ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0))) = X0 := superpose step26 step9
  have step67 (X0 : G) : ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = X0 := superpose step26 step64
  have step75 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ ((((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ X0) ◇ X0)) := superpose step26 step54
  have step77 (X0 : G) : ((X0 ◇ X0) ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) := superpose step14 step54
  have step90 (X0 : G) : (X0 ◇ ((X0 ◇ X0) ◇ X0)) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose step67 step75
  have step91 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose step26 step90
  have step93 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose step91 step67
  have step95 (X0 : G) : ((X0 ◇ X0) ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) := superpose step26 step77
  have step96 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))) := superpose step26 step95
  have step184 (X0 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) = ((((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))) ◇ (X0 ◇ X0))) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))) ◇ (X0 ◇ X0))) := superpose step35 step20
  have step191 (X0 : G) : (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) := superpose step96 step184
  have step192 (X0 : G) : ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) := superpose step35 step191
  have step193 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) = ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) := superpose step91 step192
  have step194 (X0 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose step93 step193
  have step196 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose step194 step96
  have step212 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose step196 step10
  subsumption step212 rfl


@[equational_result]
theorem Finite.Equation713_implies_Equation817 (G : Type*) [Magma G] [Finite G] (h : Equation713 G) : Equation817 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have step9 (X0 X1 : G) : (X1 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X0))) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := mod_symm nh
  have step11 (X Y : G) : ((Y ◇ (Y ◇ (Y ◇ X))) ◇ (Y ◇ (Y ◇ X))) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => ((Y ◇ s) ◇ s)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (Y ◇ (Y ◇ s))) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (Y ◇ (Y ◇ s))) (fun s => ((Y ◇ s) ◇ s)) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step12 (X Y : G) : (Y ◇ ((Y ◇ (Y ◇ X)) ◇ (Y ◇ X))) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (Y ◇ ((Y ◇ s) ◇ s))) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (Y ◇ s)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (Y ◇ s)) (fun s => (Y ◇ ((Y ◇ s) ◇ s))) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step14 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = (X1 ◇ (X0 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X0)))) := superpose step9 step12
  have step15 (X0 X1 : G) : (X1 ◇ ((X1 ◇ X0) ◇ X0)) = ((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)) := superpose step12 step12
  have step21 (X0 X1 : G) : (X1 ◇ (X1 ◇ X0)) = ((X1 ◇ (X1 ◇ (X1 ◇ X0))) ◇ ((X1 ◇ (X1 ◇ (X1 ◇ X0))) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0))))) := superpose step11 step9
  have step26 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose step9 step14
  have step39 (X0 X1 : G) : ((X1 ◇ (X1 ◇ (X1 ◇ X0))) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0)))) = (((X1 ◇ (X1 ◇ (X1 ◇ X0))) ◇ X0) ◇ X0) := superpose step11 step15
  have step54 (X0 X1 : G) : (X1 ◇ (X1 ◇ X0)) = ((X1 ◇ (X1 ◇ (X1 ◇ X0))) ◇ (((X1 ◇ (X1 ◇ (X1 ◇ X0))) ◇ X0) ◇ X0)) := superpose step39 step21
  have step60 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose step26 step9
  have step64 (X0 : G) : ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0))) = X0 := superpose step26 step9
  have step67 (X0 : G) : ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = X0 := superpose step26 step64
  have step75 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ ((((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ X0) ◇ X0)) := superpose step26 step54
  have step90 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose step67 step75
  have step91 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ X0)) := superpose step26 step90
  have step94 : sK0 ≠ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := superpose step91 step10
  subsumption step94 step60


@[equational_result]
theorem Finite.Equation73_implies_Equation125 (G : Type*) [Magma G] [Finite G] (h : Equation73 G) : Equation125 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) : (X1 ◇ (X1 ◇ (X0 ◇ X1))) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ (sK1 ◇ ((sK1 ◇ sK0) ◇ sK1)) := mod_symm nh
  have step11 (X Y : G) : ((Y ◇ (Y ◇ X)) ◇ Y) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (s ◇ Y)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (Y ◇ (Y ◇ s))) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (Y ◇ (Y ◇ s))) (fun s => (s ◇ Y)) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step14 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = ((X1 ◇ X0) ◇ X1) := superpose step9 step11
  have step17 : sK0 ≠ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) := superpose step14 step10
  subsumption step17 step9


@[equational_result]
theorem Finite.Equation73_implies_Equation229 (G : Type*) [Magma G] [Finite G] (h : Equation73 G) : Equation229 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step10 : sK0 ≠ ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK1) := mod_symm nh
  have step11 (X Y : G) : ((Y ◇ (Y ◇ X)) ◇ Y) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (s ◇ Y)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (Y ◇ (Y ◇ s))) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (Y ◇ (Y ◇ s))) (fun s => (s ◇ Y)) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step16 : sK0 ≠ sK0 := superpose step11 step10
  subsumption step16 rfl


@[equational_result]
theorem Finite.Equation73_implies_Equation4435 (G : Type*) [Magma G] [Finite G] (h : Equation73 G) : Equation4435 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) : (X1 ◇ (X1 ◇ (X0 ◇ X1))) = X0 := mod_symm (h ..)
  have step10 : (sK0 ◇ (sK1 ◇ sK0)) ≠ ((sK0 ◇ sK1) ◇ sK0) := mod_symm nh
  have step11 (X Y : G) : ((Y ◇ (Y ◇ X)) ◇ Y) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (s ◇ Y)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (Y ◇ (Y ◇ s))) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (Y ◇ (Y ◇ s))) (fun s => (s ◇ Y)) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step14 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = ((X1 ◇ X0) ◇ X1) := superpose step9 step11
  have step22 : (sK0 ◇ (sK1 ◇ sK0)) ≠ (sK0 ◇ (sK1 ◇ sK0)) := superpose step14 step10
  subsumption step22 rfl


@[equational_result]
theorem Finite.Equation883_implies_Equation2304 (G : Type*) [Magma G] [Finite G] (h : Equation883 G) : Equation2304 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step10 : sK0 ≠ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ sK1) := mod_symm nh
  have step11 (X Y : G) : ((Y ◇ (X ◇ (Y ◇ Y))) ◇ Y) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (s ◇ Y)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (Y ◇ (s ◇ (Y ◇ Y)))) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (Y ◇ (s ◇ (Y ◇ Y)))) (fun s => (s ◇ Y)) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step16 : sK0 ≠ sK0 := superpose step11 step10
  subsumption step16 rfl


@[equational_result]
theorem Finite.Equation917_implies_Equation1629 (G : Type*) [Magma G] [Finite G] (h : Equation917 G) : Equation1629 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have step10 : sK0 ≠ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ sK0)) := mod_symm nh
  have step12 (X Y : G) : ((Y ◇ Y) ◇ ((Y ◇ X) ◇ Y)) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => ((Y ◇ Y) ◇ (s ◇ Y))) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (Y ◇ s)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (Y ◇ s)) (fun s => ((Y ◇ Y) ◇ (s ◇ Y))) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step17 : sK0 ≠ sK0 := superpose step12 step10
  subsumption step17 rfl


@[equational_result]
theorem Finite.Equation917_implies_Equation1729 (G : Type*) [Magma G] [Finite G] (h : Equation917 G) : Equation1729 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step10 : sK0 ≠ ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK0) ◇ sK1)) := mod_symm nh
  have step12 (X Y : G) : ((Y ◇ Y) ◇ ((Y ◇ X) ◇ Y)) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => ((Y ◇ Y) ◇ (s ◇ Y))) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (Y ◇ s)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (Y ◇ s)) (fun s => ((Y ◇ Y) ◇ (s ◇ Y))) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step17 : sK0 ≠ sK0 := superpose step12 step10
  subsumption step17 rfl


@[equational_result]
theorem Finite.Equation917_implies_Equation2541 (G : Type*) [Magma G] [Finite G] (h : Equation917 G) : Equation2541 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step10 : sK0 ≠ ((sK1 ◇ ((sK1 ◇ sK1) ◇ sK0)) ◇ sK1) := mod_symm nh
  have step11 (X Y : G) : ((Y ◇ ((Y ◇ Y) ◇ X)) ◇ Y) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (s ◇ Y)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (Y ◇ ((Y ◇ Y) ◇ s))) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (Y ◇ ((Y ◇ Y) ◇ s))) (fun s => (s ◇ Y)) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step15 : sK0 ≠ sK0 := superpose step11 step10
  subsumption step15 rfl


@[equational_result]
theorem Finite.Equation1875916474_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h : Equation1875916474 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step8 (X0 X1 X2 : G) : ((((X1 ◇ X1) ◇ X1) ◇ X0) ◇ (((X1 ◇ X1) ◇ ((X1 ◇ X1) ◇ X1)) ◇ X2)) = X0 := mod_symm (h ..)
  have step9 : sK0 ≠ sK1 := mod_symm nh
  have step10 (X Y Z : G) : (((Y ◇ Y) ◇ Y) ◇ (X ◇ (((Y ◇ Y) ◇ ((Y ◇ Y) ◇ Y)) ◇ Z))) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (((Y ◇ Y) ◇ Y) ◇ s)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (s ◇ (((Y ◇ Y) ◇ ((Y ◇ Y) ◇ Y)) ◇ Z))) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (s ◇ (((Y ◇ Y) ◇ ((Y ◇ Y) ◇ Y)) ◇ Z))) (fun s => (((Y ◇ Y) ◇ Y) ◇ s)) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step11 (X0 X1 : G) : ((X1 ◇ X1) ◇ X1) = (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0))) := superpose step10 step10
  have step12 (X0 X1 X2 X3 : G) : (X0 ◇ (((X1 ◇ X1) ◇ ((X1 ◇ X1) ◇ X1)) ◇ X2)) = (X0 ◇ (((X1 ◇ X1) ◇ ((X1 ◇ X1) ◇ X1)) ◇ X3)) := superpose step10 step8
  have step15 (X0 X1 : G) : ((X1 ◇ X1) ◇ X1) = ((X0 ◇ X0) ◇ X0) := superpose step11 step11
  have step19 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ ((X1 ◇ X1) ◇ X1)) = (((X0 ◇ X0) ◇ X0) ◇ (((X1 ◇ X1) ◇ ((X1 ◇ X1) ◇ X1)) ◇ X2)) := superpose step11 step8
  have step26 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ X1) = (((X0 ◇ X0) ◇ X0) ◇ ((X2 ◇ X2) ◇ ((X0 ◇ X0) ◇ X0))) := superpose step15 step11
  have step28 (X0 X1 X2 X3 : G) : (((X0 ◇ X0) ◇ X0) ◇ (X2 ◇ (((X1 ◇ X1) ◇ ((X0 ◇ X0) ◇ X0)) ◇ X3))) = X2 := superpose step15 step10
  have step62 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X1) ◇ ((X1 ◇ X1) ◇ X1)) ◇ X3) = ((((X0 ◇ X0) ◇ X0) ◇ (((X1 ◇ X1) ◇ ((X1 ◇ X1) ◇ X1)) ◇ X2)) ◇ (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ X4)) := superpose step12 step8
  have step97 (X0 X1 X3 X4 : G) : (((X1 ◇ X1) ◇ ((X1 ◇ X1) ◇ X1)) ◇ X3) = (((X1 ◇ X1) ◇ ((X1 ◇ X1) ◇ X1)) ◇ (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ X4)) := superpose step19 step62
  have step118 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ X1) = (((X2 ◇ X2) ◇ X2) ◇ ((X0 ◇ X0) ◇ X0)) := superpose step15 step26
  have step141 (X0 X1 X2 X3 X4 : G) : ((X3 ◇ X3) ◇ ((X3 ◇ X3) ◇ X3)) = ((((((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ X1) ◇ (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ X1)) ◇ (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ X2)) ◇ (((X3 ◇ X3) ◇ ((X3 ◇ X3) ◇ X3)) ◇ X4)) := superpose step12 step19
  have step200 (X0 X1 X2 X4 : G) : ((X2 ◇ X2) ◇ ((X2 ◇ X2) ◇ X2)) = ((((X0 ◇ X0) ◇ X0) ◇ ((X1 ◇ X1) ◇ X1)) ◇ (((X2 ◇ X2) ◇ ((X2 ◇ X2) ◇ X2)) ◇ X4)) := superpose step118 step19
  have step274 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ X1) ◇ (X2 ◇ X0)) = X2 := superpose step10 step28
  have step309 (X1 X2 X4 : G) : ((X2 ◇ X2) ◇ ((X2 ◇ X2) ◇ X2)) = ((X1 ◇ X1) ◇ (((X2 ◇ X2) ◇ ((X2 ◇ X2) ◇ X2)) ◇ X4)) := superpose step274 step200
  have step341 (X0 X3 X4 : G) : ((X3 ◇ X3) ◇ ((X3 ◇ X3) ◇ X3)) = (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (((X3 ◇ X3) ◇ ((X3 ◇ X3) ◇ X3)) ◇ X4)) := superpose step309 step141
  have step359 (X0 X1 X2 X3 X4 : G) : ((((X0 ◇ X0) ◇ X0) ◇ (((X0 ◇ X0) ◇ X0) ◇ ((X1 ◇ X1) ◇ X1))) ◇ X2) = ((((X0 ◇ X0) ◇ X0) ◇ (((X0 ◇ X0) ◇ X0) ◇ ((X1 ◇ X1) ◇ X1))) ◇ (((X3 ◇ X3) ◇ ((X3 ◇ X3) ◇ X3)) ◇ X4)) := superpose step118 step97
  have step363 (X0 X1 X2 X3 X4 X5 : G) : (((X2 ◇ X2) ◇ (((X0 ◇ X0) ◇ X0) ◇ ((X1 ◇ X1) ◇ X1))) ◇ X3) = (((X2 ◇ X2) ◇ (((X0 ◇ X0) ◇ X0) ◇ ((X1 ◇ X1) ◇ X1))) ◇ (((X4 ◇ X4) ◇ ((X4 ◇ X4) ◇ X4)) ◇ X5)) := superpose step118 step97
  have step395 (X0 X1 X2 X3 X4 : G) : ((((((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (((X1 ◇ X1) ◇ ((X1 ◇ X1) ◇ X1)) ◇ X2)) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0))) ◇ X3) ◇ (((((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (((X1 ◇ X1) ◇ ((X1 ◇ X1) ◇ X1)) ◇ X2)) ◇ ((((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (((X1 ◇ X1) ◇ ((X1 ◇ X1) ◇ X1)) ◇ X2)) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)))) ◇ X4)) = X3 := superpose step97 step8
  have step428 (X0 X2 X3 X4 : G) : (((X0 ◇ X0) ◇ X0) ◇ X2) = (((X0 ◇ X0) ◇ X0) ◇ (((X3 ◇ X3) ◇ ((X3 ◇ X3) ◇ X3)) ◇ X4)) := superpose step274 step359
  have step431 (X1 X2 X3 X4 X5 : G) : (((X2 ◇ X2) ◇ (X1 ◇ X1)) ◇ X3) = (((X2 ◇ X2) ◇ (X1 ◇ X1)) ◇ (((X4 ◇ X4) ◇ ((X4 ◇ X4) ◇ X4)) ◇ X5)) := superpose step274 step363
  have step444 (X0 X1 X3 X4 : G) : (((((X1 ◇ X1) ◇ ((X1 ◇ X1) ◇ X1)) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0))) ◇ X3) ◇ ((((X1 ◇ X1) ◇ ((X1 ◇ X1) ◇ X1)) ◇ (((X1 ◇ X1) ◇ ((X1 ◇ X1) ◇ X1)) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)))) ◇ X4)) = X3 := superpose step341 step395
  have step445 (X0 X1 X3 X4 : G) : (((((X1 ◇ X1) ◇ ((X1 ◇ X1) ◇ X1)) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0))) ◇ X3) ◇ (((X1 ◇ X1) ◇ ((X1 ◇ X1) ◇ X1)) ◇ X4)) = X3 := superpose step341 step444
  have step467 (X0 X1 X2 : G) : (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X1 ◇ X2)) = X1 := superpose step274 step274
  have step537 (X0 X1 X3 X4 : G) : (((X0 ◇ X0) ◇ X3) ◇ (((X1 ◇ X1) ◇ ((X1 ◇ X1) ◇ X1)) ◇ X4)) = X3 := superpose step467 step445
  have step543 (X0 X2 : G) : (((X0 ◇ X0) ◇ X0) ◇ X2) = X0 := superpose step537 step428
  have step544 (X1 X3 : G) : ((X1 ◇ X1) ◇ X1) = (((X1 ◇ X1) ◇ ((X1 ◇ X1) ◇ X1)) ◇ X3) := superpose step537 step97
  have step546 (X1 X2 X3 : G) : (X1 ◇ X1) = (((X2 ◇ X2) ◇ (X1 ◇ X1)) ◇ X3) := superpose step537 step431
  have step568 (X0 X1 : G) : ((X1 ◇ X1) ◇ ((X1 ◇ X1) ◇ X1)) = (((X0 ◇ X0) ◇ X0) ◇ ((X1 ◇ X1) ◇ X1)) := superpose step544 step19
  have step597 (X0 X1 X3 : G) : (((X0 ◇ X0) ◇ X3) ◇ ((X1 ◇ X1) ◇ X1)) = X3 := superpose step544 step537
  have step600 (X1 : G) : (X1 ◇ X1) = ((X1 ◇ X1) ◇ ((X1 ◇ X1) ◇ X1)) := superpose step274 step568
  have step612 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ (X1 ◇ X2)) = X1 := superpose step600 step467
  have step690 (X1 X3 : G) : (X1 ◇ X1) = (X1 ◇ X3) := superpose step612 step546
  have step763 (X0 X1 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ X1) := superpose step274 step690
  have step784 (X0 : G) : (X0 ◇ X0) = X0 := superpose step543 step763
  have step797 (X0 X2 : G) : ((X0 ◇ X0) ◇ X2) = X0 := superpose step784 step543
  have step798 (X0 X1 X3 : G) : (((X0 ◇ X0) ◇ X3) ◇ (X1 ◇ X1)) = X3 := superpose step784 step597
  have step839 (X0 X2 : G) : (X0 ◇ X2) = X0 := superpose step784 step797
  have step843 (X0 X1 X3 : G) : (((X0 ◇ X0) ◇ X3) ◇ X1) = X3 := superpose step784 step798
  have step844 (X0 X1 X3 : G) : ((X0 ◇ X0) ◇ X1) = X3 := superpose step839 step843
  have step845 (X0 X1 X3 : G) : (X0 ◇ X1) = X3 := superpose step784 step844
  have step852 (X0 X3 : G) : X0 = X3 := superpose step845 step845
  have step858 (X0 : G) : sK0 ≠ X0 := superpose step852 step9
  subsumption step858 step852


