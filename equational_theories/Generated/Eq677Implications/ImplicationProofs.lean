import equational_theories.Equations.All
import equational_theories.MagmaOp
import equational_theories.Superposition
import equational_theories.Finite677.Eq19855
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.ByContra

set_option linter.unusedVariables false

@[equational_result]
theorem Finite.Equation677_and_Equation1035_implies_Equation1020 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation1035 G) : Equation1020 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X0)) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0)) := mod_symm nh
  have step13 : sK0 ≠ sK0 := superpose step9 step10
  subsumption step13 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation1035_implies_Equation1223 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation1035 G) : Equation1223 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X0)) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ (sK0 ◇ (((sK0 ◇ sK0) ◇ sK0) ◇ sK0)) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step17 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose step11 step12
  have step33 (X0 : G) :  (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) = X0 := superpose step17 step9
  have step37 : sK0 ≠ sK0 := superpose step33 step10
  subsumption step37 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation1048_implies_Equation1020 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation1048 G) : Equation1020 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ (X1 ◇ X1)) ◇ X0)) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0)) := mod_symm nh
  have step15 : sK0 ≠ sK0 := superpose step9 step10
  subsumption step15 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation1048_implies_Equation4276 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation1048 G) : Equation4276 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ (X1 ◇ X1)) ◇ X0)) = X0 := mod_symm (h ..)
  have step10 : (sK1 ◇ (sK1 ◇ sK1)) ≠ (sK0 ◇ (sK0 ◇ sK0)) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step14 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X0))) = (((X1 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ X0))) := superpose step9 step9
  have step15 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X1)) ◇ X0) = (X0 ◇ (((X1 ◇ (X1 ◇ X1)) ◇ X0) ◇ (X0 ◇ X0))) := superpose step9 step11
  have step18 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X1)) ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose step9 step12
  have step27 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) = X0 := superpose step18 step12
  have step41 (X0 X1 : G) :  ((X1 ◇ X1) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X1)) = X1 := superpose step18 step27
  have step100 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X1 ◇ X1))) = ((((X1 ◇ (X1 ◇ X1)) ◇ (X1 ◇ (X1 ◇ X1))) ◇ (X1 ◇ (X1 ◇ X1))) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X1 ◇ X1))) ◇ ((((X1 ◇ (X1 ◇ X1)) ◇ (X1 ◇ (X1 ◇ X1))) ◇ (X1 ◇ (X1 ◇ X1))) ◇ (((X1 ◇ (X1 ◇ X1)) ◇ (X1 ◇ (X1 ◇ X1))) ◇ (X1 ◇ (X1 ◇ X1)))))) := superpose step18 step15
  have step118 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X1 ◇ X1))) = (((X1 ◇ (X1 ◇ X1)) ◇ (X1 ◇ (X1 ◇ X1))) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X1 ◇ X1))) ◇ (((X1 ◇ (X1 ◇ X1)) ◇ (X1 ◇ (X1 ◇ X1))) ◇ ((X1 ◇ (X1 ◇ X1)) ◇ (X1 ◇ (X1 ◇ X1)))))) := superpose step14 step100
  have step125 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X1 ◇ X1))) = (((X1 ◇ (X1 ◇ X1)) ◇ (X1 ◇ (X1 ◇ X1))) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X1 ◇ X1))) ◇ (X1 ◇ (X1 ◇ X1)))) := superpose step41 step118
  have step129 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X1 ◇ X1))) = (((X1 ◇ (X1 ◇ X1)) ◇ (X1 ◇ (X1 ◇ X1))) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X1 ◇ X1)))) := superpose step14 step125
  have step132 (X0 X1 : G) :  (X1 ◇ (X1 ◇ X1)) = ((X0 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X1 ◇ X1))) := superpose step41 step129
  have step801 (X0 X1 : G) :  (X0 ◇ (X0 ◇ X0)) = ((X1 ◇ (X1 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X1 ◇ X1))))) := superpose step132 step11
  have step802 (X0 X1 : G) :  (X0 ◇ (X0 ◇ X0)) = ((X1 ◇ (X1 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X1 ◇ X1)))) := superpose step132 step801
  have step837 (X0 X1 : G) :  (X1 ◇ (X1 ◇ X1)) = (X0 ◇ (X0 ◇ X0)) := superpose step9 step802
  have step999 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose step837 step10
  subsumption step999 step837


@[equational_result]
theorem Finite.Equation677_and_Equation1076_implies_Equation3 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation1076 G) : Equation3 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have step11 (X0 X1 : G) :  (X1 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X1)) = X0 := mod_symm (h ..)
  have step12 : sK0 ≠ (sK0 ◇ sK0) := mod_symm nh
  have step13 (X Y : G) : ((Y ◇ (X ◇ Y)) ◇ ((Y ◇ (X ◇ Y)) ◇ Y)) = X := by
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
  have step14 (X Y : G) : (((Y ◇ X) ◇ ((Y ◇ X) ◇ Y)) ◇ Y) = X := by
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
  have step15 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step16 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step20 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) = X0 := superpose step15 step11
  have step22 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ X1)) ◇ X1) = (X0 ◇ ((X1 ◇ X0) ◇ X1)) := superpose step15 step14
  have step27 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step16 step16
  have step35 (X0 X1 : G) :  (((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X0) ◇ (((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X0) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1)))) = X1 := superpose step15 step13
  have step46 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) ◇ (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) := superpose step20 step13
  have step53 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = X0 := superpose step35 step46
  have step59 (X0 : G) :  ((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) = (((X0 ◇ X0) ◇ X0) ◇ (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) := superpose step20 step22
  have step66 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) = X0 := superpose step22 step16
  have step80 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose step53 step66
  have step82 (X0 : G) :  ((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ X0) = ((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) := superpose step27 step59
  have step84 (X0 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose step53 step82
  have step85 (X0 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ X0) = X0 := superpose step80 step84
  have step86 (X0 : G) :  (X0 ◇ ((X0 ◇ X0) ◇ X0)) = X0 := superpose step22 step85
  have step87 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step53 step86
  have step88 : sK0 ≠ sK0 := superpose step87 step12
  subsumption step88 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation1082_implies_Equation3 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation1082 G) : Equation3 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have step10 (X0 X1 : G) :  (X1 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0)) = X0 := mod_symm (h ..)
  have step11 : sK0 ≠ (sK0 ◇ sK0) := mod_symm nh
  have step12 (X Y : G) : (((Y ◇ X) ◇ (Y ◇ (Y ◇ X))) ◇ (Y ◇ X)) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => ((s ◇ (Y ◇ s)) ◇ s)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (Y ◇ s)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (Y ◇ s)) (fun s => ((s ◇ (Y ◇ s)) ◇ s)) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step13 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step14 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step20 (X0 X1 : G) :  ((X0 ◇ (X1 ◇ X0)) ◇ X0) = (X0 ◇ ((X1 ◇ X0) ◇ X1)) := superpose step10 step14
  have step31 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X0) := superpose step14 step12
  have step33 (X0 X1 : G) :  (X1 ◇ X0) = ((X0 ◇ (((X1 ◇ X0) ◇ (X1 ◇ (X1 ◇ X0))) ◇ X0)) ◇ X0) := superpose step12 step12
  have step34 (X0 X1 : G) :  (X1 ◇ (X1 ◇ X0)) = ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X0)) := superpose step12 step13
  have step158 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = X0 := superpose step34 step14
  have step198 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0)) := superpose step158 step31
  have step200 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) := superpose step20 step198
  have step208 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = X0 := superpose step14 step200
  have step336 (X0 : G) :  ((X0 ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0)) ◇ X0) = X0 := superpose step208 step33
  have step354 (X0 : G) :  ((X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ X0) = X0 := superpose step31 step336
  have step364 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step10 step354
  have step388 : sK0 ≠ sK0 := superpose step364 step11
  subsumption step388 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation1083_implies_Equation3 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation1083 G) : Equation3 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have step12 : sK0 ≠ (sK0 ◇ sK0) := mod_symm nh
  have step13 (X Y : G) : ((Y ◇ (X ◇ Y)) ◇ (Y ◇ (Y ◇ (X ◇ Y)))) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (s ◇ (Y ◇ s))) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (Y ◇ (s ◇ Y))) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (Y ◇ (s ◇ Y))) (fun s => (s ◇ (Y ◇ s))) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step14 (X Y : G) : (((Y ◇ X) ◇ (Y ◇ (Y ◇ X))) ◇ Y) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => ((s ◇ (Y ◇ s)) ◇ Y)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (Y ◇ s)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (Y ◇ s)) (fun s => ((s ◇ (Y ◇ s)) ◇ Y)) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step15 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step16 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step22 (X0 X1 : G) :  ((X0 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ ((X1 ◇ X0) ◇ X1)) := superpose step15 step14
  have step28 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step16 step16
  have step30 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose step15 step16
  have step35 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0))) := superpose step22 step30
  have step36 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose step28 step35
  have step37 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose step22 step36
  have step43 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) := superpose step15 step13
  have step50 (X0 : G) :  (X0 ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ X0) := superpose step37 step43
  have step53 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) := superpose step50 step13
  have step59 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = X0 := superpose step13 step53
  have step62 (X0 : G) :  (X0 ◇ ((X0 ◇ X0) ◇ X0)) = X0 := superpose step37 step15
  have step73 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step59 step62
  have step88 : sK0 ≠ sK0 := superpose step73 step12
  subsumption step88 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation1098_implies_Equation466 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation1098 G) : Equation466 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step11 (X0 X1 X2 : G) :  (X1 ◇ ((X0 ◇ (X2 ◇ X1)) ◇ X2)) = X0 := mod_symm (h ..)
  have step12 : sK0 ≠ (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := mod_symm nh
  have step13 (X Y Z : G) : ((Y ◇ (X ◇ Z)) ◇ (Z ◇ Y)) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (s ◇ (Z ◇ Y))) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (Y ◇ (s ◇ Z))) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (Y ◇ (s ◇ Z))) (fun s => (s ◇ (Z ◇ Y))) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step24 (X0 X1 : G) :  (X0 ◇ (X0 ◇ X1)) = X1 := superpose step13 step11
  have step59 : sK0 ≠ (sK1 ◇ (sK1 ◇ sK0)) := superpose step24 step12
  subsumption step59 step24


@[equational_result]
theorem Finite.Equation677_and_Equation1098_implies_Equation4684 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation1098 G) : Equation4684 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have step12 : ((sK0 ◇ sK1) ◇ sK2) ≠ ((sK2 ◇ sK1) ◇ sK0) := mod_symm nh
  have step14 (X Y Z : G) : (((Y ◇ X) ◇ (Z ◇ Y)) ◇ Z) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => ((s ◇ (Z ◇ Y)) ◇ Z)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (Y ◇ s)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (Y ◇ s)) (fun s => ((s ◇ (Z ◇ Y)) ◇ Z)) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step34 (X0 X1 X2 : G) :  (X0 ◇ X2) = ((X2 ◇ (X1 ◇ X0)) ◇ X1) := superpose step14 step14
  have step384 (X0 X1 X2 : G) :  ((X0 ◇ X1) ◇ X2) = ((X2 ◇ X1) ◇ X0) := superpose step34 step14
  have step2721 : ((sK0 ◇ sK1) ◇ sK2) ≠ ((sK0 ◇ sK1) ◇ sK2) := superpose step384 step12
  subsumption step2721 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation1109_implies_Equation124 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation1109 G) : Equation124 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step10 (X0 X1 : G) :  (X1 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X0)) = X0 := mod_symm (h ..)
  have step11 : sK0 ≠ (sK1 ◇ ((sK1 ◇ sK0) ◇ sK0)) := mod_symm nh
  have step12 (X Y : G) : ((Y ◇ ((Y ◇ X) ◇ (Y ◇ X))) ◇ (Y ◇ X)) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => ((Y ◇ (s ◇ s)) ◇ s)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (Y ◇ s)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (Y ◇ s)) (fun s => ((Y ◇ (s ◇ s)) ◇ s)) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step13 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step14 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step17 (X0 X1 : G) :  ((X1 ◇ (X0 ◇ X0)) ◇ X0) = (X0 ◇ ((X1 ◇ X0) ◇ X1)) := superpose step10 step14
  have step19 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose step13 step14
  have step20 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = ((X1 ◇ X0) ◇ (((X1 ◇ (X1 ◇ X0)) ◇ X1) ◇ (X0 ◇ (X1 ◇ X0)))) := superpose step14 step13
  have step22 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (((X1 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) := superpose step14 step12
  have step31 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) = X0 := superpose step17 step14
  have step51 (X0 : G) :  ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) = X0 := superpose step19 step10
  have step62 (X0 X1 : G) :  (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)) = ((X0 ◇ (((X1 ◇ (X1 ◇ X0)) ◇ X1) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1))) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) := superpose step14 step22
  have step64 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) = ((X0 ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) := superpose step31 step22
  have step82 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) := superpose step12 step64
  have step84 (X0 X1 : G) :  (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)) = (((X1 ◇ (X1 ◇ X0)) ◇ X1) ◇ ((X0 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) ◇ X0)) := superpose step17 step62
  have step131 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) = X0 := superpose step82 step10
  have step135 (X0 : G) :  ((((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0)) = ((((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) := superpose step82 step22
  have step136 (X0 : G) :  ((((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0))) := superpose step82 step17
  have step138 (X0 : G) :  (X0 ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ ((((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0))) := superpose step82 step14
  have step141 (X0 : G) :  ((((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) = ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0))) := superpose step136 step135
  have step175 (X0 : G) :  ((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) = X0 := superpose step131 step14
  have step2206 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((((((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose step138 step175
  have step2250 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose step141 step2206
  have step2269 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose step12 step2250
  have step2673 (X0 : G) :  ((X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ X0) = ((((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ (((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0))) := superpose step51 step84
  have step2688 (X0 : G) :  ((X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ X0) = (((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ ((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0))) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0))) := superpose step131 step84
  have step2777 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ X0) := superpose step14 step2688
  have step2789 (X0 : G) :  ((X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ X0) = ((((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) := superpose step2269 step2673
  have step2805 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ X0) := superpose step2269 step2777
  have step2814 (X0 : G) :  ((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ X0) = ((((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) ◇ (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) := superpose step17 step2789
  have step2820 (X0 : G) :  (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose step10 step2805
  have step2824 (X0 : G) :  ((X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) ◇ X0) = ((((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) ◇ (((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))) := superpose step2269 step2814
  have step2831 (X0 : G) :  ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) = ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0)))) ◇ (X0 ◇ (X0 ◇ X0)))) := superpose step2820 step2824
  have step2838 (X0 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ X0) = ((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0))) := superpose step2820 step2831
  have step2845 (X0 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0))) := superpose step82 step2838
  have step2851 (X0 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ X0) = X0 := superpose step14 step2845
  have step2857 (X0 : G) :  (X0 ◇ ((X0 ◇ X0) ◇ X0)) = X0 := superpose step17 step2851
  have step2863 (X0 : G) :  (X0 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose step2269 step2857
  have step2869 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = X0 := superpose step2820 step2863
  have step2899 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose step2869 step14
  have step2907 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) := superpose step2869 step20
  have step2954 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) := superpose step2269 step2907
  have step2992 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose step2820 step2954
  have step3024 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step2899 step2992
  have step3578 (X0 X1 : G) :  (X1 ◇ ((X1 ◇ X0) ◇ X0)) = X0 := superpose step3024 step10
  have step6918 : sK0 ≠ sK0 := superpose step3578 step11
  subsumption step6918 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation1112_implies_Equation3 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation1112 G) : Equation3 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have step11 : sK0 ≠ (sK0 ◇ sK0) := mod_symm nh
  have step12 (X Y : G) : ((Y ◇ ((Y ◇ X) ◇ Y)) ◇ (Y ◇ X)) = X := by
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
  have step13 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step14 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step21 (X0 X1 : G) :  ((X1 ◇ (X0 ◇ X1)) ◇ X0) = (X0 ◇ ((X1 ◇ X0) ◇ X1)) := superpose step13 step12
  have step32 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step14 step14
  have step33 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose step13 step14
  have step40 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = X0 := superpose step12 step33
  have step44 (X0 : G) :  (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0))) = X0 := superpose step40 step14
  have step50 (X0 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ X0) = X0 := superpose step32 step44
  have step52 (X0 : G) :  (X0 ◇ ((X0 ◇ X0) ◇ X0)) = X0 := superpose step21 step50
  have step54 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step40 step52
  have step73 : sK0 ≠ sK0 := superpose step54 step11
  subsumption step73 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation1113_implies_Equation3 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation1113 G) : Equation3 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have step10 (X0 X1 : G) :  (X1 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X1)) = X0 := mod_symm (h ..)
  have step11 : sK0 ≠ (sK0 ◇ sK0) := mod_symm nh
  have step12 (X Y : G) : ((Y ◇ ((Y ◇ X) ◇ Y)) ◇ Y) = X := by
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
  have step13 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step14 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step21 (X0 X1 : G) :  ((X1 ◇ (X0 ◇ X1)) ◇ X1) = (X0 ◇ ((X1 ◇ X0) ◇ X1)) := superpose step13 step12
  have step22 (X0 X1 : G) :  ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X0) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1)))) = X1 := superpose step13 step10
  have step57 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) = X0 := superpose step21 step14
  have step83 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) := superpose step57 step10
  have step94 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step22 step83
  have step142 : sK0 ≠ sK0 := superpose step94 step11
  subsumption step142 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation1117_implies_Equation1109 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation1117 G) : Equation1109 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step10 (X0 X1 X2 : G) :  (X1 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X2)) = X0 := mod_symm (h ..)
  have step11 : sK0 ≠ (sK1 ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ sK0)) := mod_symm nh
  have step16 : sK0 ≠ sK0 := superpose step10 step11
  subsumption step16 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation1119_implies_Equation3 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation1119 G) : Equation3 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have step10 (X0 X1 : G) :  (X1 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X0)) = X0 := mod_symm (h ..)
  have step11 : sK0 ≠ (sK0 ◇ sK0) := mod_symm nh
  have step12 (X Y : G) : ((Y ◇ (Y ◇ (Y ◇ X))) ◇ (Y ◇ X)) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => ((Y ◇ (Y ◇ s)) ◇ s)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (Y ◇ s)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (Y ◇ s)) (fun s => ((Y ◇ (Y ◇ s)) ◇ s)) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step13 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step18 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) := superpose step13 step10
  have step20 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = X0 := superpose step13 step18
  have step22 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X0) = (X0 ◇ ((X1 ◇ X0) ◇ X1)) := superpose step13 step12
  have step27 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = X0 := superpose step20 step13
  have step28 (X0 : G) :  (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) = X0 := superpose step20 step12
  have step32 (X0 : G) :  (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0))) = X0 := superpose step22 step28
  have step33 (X0 : G) :  (X0 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose step20 step32
  have step34 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step27 step33
  have step48 : sK0 ≠ sK0 := superpose step34 step11
  subsumption step48 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation1232_implies_Equation264 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation1232 G) : Equation264 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ (((X0 ◇ X1) ◇ X1) ◇ X1)) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ (((sK0 ◇ sK1) ◇ sK1) ◇ sK1) := mod_symm nh
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step13 (X0 X1 : G) :  (X0 ◇ ((X0 ◇ (((X0 ◇ X1) ◇ X1) ◇ X1)) ◇ (((X0 ◇ X1) ◇ X1) ◇ X1))) = X0 := superpose step9 step9
  have step14 (X0 X1 : G) :  (X0 ◇ (X0 ◇ (((X0 ◇ X1) ◇ X1) ◇ X1))) = X0 := superpose step9 step13
  have step15 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step9 step14
  have step26 (X0 X1 : G) :  (((X0 ◇ X1) ◇ X1) ◇ X1) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose step9 step12
  have step34 (X0 X1 : G) :  (((X0 ◇ X1) ◇ X1) ◇ X1) = (X0 ◇ (X0 ◇ X0)) := superpose step15 step26
  have step37 (X0 X1 : G) :  (((X0 ◇ X1) ◇ X1) ◇ X1) = (X0 ◇ X0) := superpose step15 step34
  have step39 (X0 X1 : G) :  (((X0 ◇ X1) ◇ X1) ◇ X1) = X0 := superpose step15 step37
  have step49 : sK0 ≠ sK0 := superpose step39 step10
  subsumption step49 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation1232_implies_Equation3 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation1232 G) : Equation3 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ (((X0 ◇ X1) ◇ X1) ◇ X1)) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ (sK0 ◇ sK0) := mod_symm nh
  have step13 (X0 X1 : G) :  (X0 ◇ ((X0 ◇ (((X0 ◇ X1) ◇ X1) ◇ X1)) ◇ (((X0 ◇ X1) ◇ X1) ◇ X1))) = X0 := superpose step9 step9
  have step14 (X0 X1 : G) :  (X0 ◇ (X0 ◇ (((X0 ◇ X1) ◇ X1) ◇ X1))) = X0 := superpose step9 step13
  have step15 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step9 step14
  have step16 : sK0 ≠ sK0 := superpose step15 step10
  subsumption step16 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation1238_implies_Equation1223 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation1238 G) : Equation1223 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ X0)) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ (sK0 ◇ (((sK0 ◇ sK0) ◇ sK0) ◇ sK0)) := mod_symm nh
  have step14 : sK0 ≠ sK0 := superpose step9 step10
  subsumption step14 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation124_implies_Equation1109 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation124 G) : Equation1109 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step10 (X0 X1 : G) :  (X1 ◇ ((X1 ◇ X0) ◇ X0)) = X0 := mod_symm (h ..)
  have step11 : sK0 ≠ (sK1 ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ sK0)) := mod_symm nh
  have step13 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step21 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step10 step13
  have step29 : sK0 ≠ (sK1 ◇ ((sK1 ◇ sK0) ◇ sK0)) := superpose step21 step11
  subsumption step29 step10


@[equational_result]
theorem Finite.Equation677_and_Equation124_implies_Equation1113 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation124 G) : Equation1113 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step10 (X0 X1 : G) :  (X1 ◇ ((X1 ◇ X0) ◇ X0)) = X0 := mod_symm (h ..)
  have step11 : sK0 ≠ (sK1 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ sK1)) := mod_symm nh
  have step12 (X Y : G) : ((Y ◇ (Y ◇ X)) ◇ (Y ◇ X)) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => ((Y ◇ s) ◇ s)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (Y ◇ s)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (Y ◇ s)) (fun s => ((Y ◇ s) ◇ s)) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step13 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step14 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step15 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X0) = (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) := superpose step10 step10
  have step17 (X0 X1 : G) :  (X1 ◇ X0) = ((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0))) := superpose step12 step10
  have step23 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X0) = (X0 ◇ ((X1 ◇ X0) ◇ X1)) := superpose step13 step12
  have step39 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (((X1 ◇ X0) ◇ X0) ◇ X0) := superpose step14 step12
  have step66 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ X0) ◇ X0)) = (((X1 ◇ X0) ◇ X0) ◇ (X0 ◇ X1)) := superpose step10 step23
  have step147 (X0 X1 : G) :  (X1 ◇ (X0 ◇ X1)) = (((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) := superpose step17 step12
  have step158 (X0 X1 : G) :  (X1 ◇ (X0 ◇ X1)) = ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X0) := superpose step39 step147
  have step179 (X0 X1 : G) :  ((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ X0) = ((((X0 ◇ X1) ◇ X1) ◇ (X1 ◇ ((X0 ◇ X1) ◇ X1))) ◇ (X1 ◇ ((X0 ◇ X1) ◇ X1))) := superpose step15 step39
  have step180 (X0 X1 : G) :  (((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1))) = (((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1))) ◇ (X1 ◇ (X0 ◇ X1))) := superpose step17 step39
  have step189 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ X1)) ◇ ((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ X0)) = X0 := superpose step39 step10
  have step212 (X0 X1 : G) :  (X1 ◇ (X0 ◇ (X0 ◇ X1))) = (((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1))) ◇ (X1 ◇ (X0 ◇ X1))) := superpose step12 step180
  have step213 (X0 X1 : G) :  (X1 ◇ X0) = ((((X0 ◇ X1) ◇ X1) ◇ (X1 ◇ ((X0 ◇ X1) ◇ X1))) ◇ (X1 ◇ ((X0 ◇ X1) ◇ X1))) := superpose step10 step179
  have step214 (X0 X1 : G) :  (X1 ◇ X0) = (X1 ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X1))) := superpose step212 step213
  have step611 (X0 X1 : G) :  ((X0 ◇ X1) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) = ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ X0)) := superpose step214 step14
  have step625 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ X0)) = X1 := superpose step14 step611
  have step719 (X0 X1 : G) :  (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) = X1 := superpose step10 step625
  have step751 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X1) = (((X0 ◇ X1) ◇ X0) ◇ X0) := superpose step625 step12
  have step1134 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X0) = (X1 ◇ ((X0 ◇ X1) ◇ X1)) := superpose step719 step12
  have step1240 (X0 X1 : G) :  (((((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) ◇ X0) = ((X0 ◇ X1) ◇ ((((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1))) := superpose step625 step66
  have step1319 (X0 X1 : G) :  (((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) ◇ ((X0 ◇ X1) ◇ X1)) = (((((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) ◇ X0) := superpose step1134 step1240
  have step1357 (X0 X1 : G) :  ((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ X0) = (((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) ◇ ((X0 ◇ X1) ◇ X1)) := superpose step751 step1319
  have step1375 (X0 X1 : G) :  ((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ X0) = X1 := superpose step12 step1357
  have step1454 (X0 X1 : G) :  (X0 ◇ (X0 ◇ X1)) = (((X1 ◇ X0) ◇ X0) ◇ X0) := superpose step1375 step625
  have step2199 (X0 X1 : G) :  (((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) ◇ (X0 ◇ (X0 ◇ X1))) = (((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ X0) ◇ X0) := superpose step189 step158
  have step2212 (X0 X1 : G) :  (X1 ◇ X0) = (((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) ◇ (X0 ◇ (X0 ◇ X1))) := superpose step1375 step2199
  have step2273 (X0 X1 : G) :  (X1 ◇ X0) = ((((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X0) ◇ X0) := superpose step39 step2212
  have step2309 (X0 X1 : G) :  (X1 ◇ X0) = (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) := superpose step1454 step2273
  have step3227 (X0 X1 : G) :  (X1 ◇ (X0 ◇ X1)) = ((X1 ◇ X0) ◇ X1) := superpose step2309 step2309
  have step3870 : sK0 ≠ (sK1 ◇ (sK1 ◇ ((sK0 ◇ sK1) ◇ sK1))) := superpose step3227 step11
  subsumption step3870 step719


@[equational_result]
theorem Finite.Equation677_and_Equation1241_implies_Equation1223 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation1241 G) : Equation1223 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ (((X1 ◇ X0) ◇ X1) ◇ X0)) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ (sK0 ◇ (((sK0 ◇ sK0) ◇ sK0) ◇ sK0)) := mod_symm nh
  have step14 : sK0 ≠ sK0 := superpose step9 step10
  subsumption step14 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation124_implies_Equation1479 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation124 G) : Equation1479 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step10 (X0 X1 : G) :  (X1 ◇ ((X1 ◇ X0) ◇ X0)) = X0 := mod_symm (h ..)
  have step11 : sK0 ≠ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK1))) := mod_symm nh
  have step12 (X Y : G) : ((Y ◇ (Y ◇ X)) ◇ (Y ◇ X)) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => ((Y ◇ s) ◇ s)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (Y ◇ s)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (Y ◇ s)) (fun s => ((Y ◇ s) ◇ s)) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step13 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step14 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step15 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X0) = (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) := superpose step10 step10
  have step17 (X0 X1 : G) :  (X1 ◇ X0) = ((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0))) := superpose step12 step10
  have step23 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X0) = (X0 ◇ ((X1 ◇ X0) ◇ X1)) := superpose step13 step12
  have step39 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (((X1 ◇ X0) ◇ X0) ◇ X0) := superpose step14 step12
  have step66 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ X0) ◇ X0)) = (((X1 ◇ X0) ◇ X0) ◇ (X0 ◇ X1)) := superpose step10 step23
  have step179 (X0 X1 : G) :  ((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ X0) = ((((X0 ◇ X1) ◇ X1) ◇ (X1 ◇ ((X0 ◇ X1) ◇ X1))) ◇ (X1 ◇ ((X0 ◇ X1) ◇ X1))) := superpose step15 step39
  have step180 (X0 X1 : G) :  (((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1))) = (((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1))) ◇ (X1 ◇ (X0 ◇ X1))) := superpose step17 step39
  have step212 (X0 X1 : G) :  (X1 ◇ (X0 ◇ (X0 ◇ X1))) = (((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1))) ◇ (X1 ◇ (X0 ◇ X1))) := superpose step12 step180
  have step213 (X0 X1 : G) :  (X1 ◇ X0) = ((((X0 ◇ X1) ◇ X1) ◇ (X1 ◇ ((X0 ◇ X1) ◇ X1))) ◇ (X1 ◇ ((X0 ◇ X1) ◇ X1))) := superpose step10 step179
  have step214 (X0 X1 : G) :  (X1 ◇ X0) = (X1 ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X1))) := superpose step212 step213
  have step611 (X0 X1 : G) :  ((X0 ◇ X1) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) = ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ X0)) := superpose step214 step14
  have step625 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ X0)) = X1 := superpose step14 step611
  have step719 (X0 X1 : G) :  (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) = X1 := superpose step10 step625
  have step751 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X1) = (((X0 ◇ X1) ◇ X0) ◇ X0) := superpose step625 step12
  have step1134 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X0) = (X1 ◇ ((X0 ◇ X1) ◇ X1)) := superpose step719 step12
  have step1240 (X0 X1 : G) :  (((((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) ◇ X0) = ((X0 ◇ X1) ◇ ((((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1))) := superpose step625 step66
  have step1319 (X0 X1 : G) :  (((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) ◇ ((X0 ◇ X1) ◇ X1)) = (((((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) ◇ X0) := superpose step1134 step1240
  have step1357 (X0 X1 : G) :  ((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ X0) = (((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) ◇ ((X0 ◇ X1) ◇ X1)) := superpose step751 step1319
  have step1375 (X0 X1 : G) :  ((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ X0) = X1 := superpose step12 step1357
  have step1412 (X0 X1 : G) :  ((((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ X0) ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) = X0 := superpose step39 step1375
  have step1489 (X0 X1 : G) :  ((X1 ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) = X0 := superpose step1375 step1412
  have step2416 : sK0 ≠ sK0 := superpose step1489 step11
  subsumption step2416 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation124_implies_Equation2670 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation124 G) : Equation2670 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step10 (X0 X1 : G) :  (X1 ◇ ((X1 ◇ X0) ◇ X0)) = X0 := mod_symm (h ..)
  have step11 : sK0 ≠ (((sK0 ◇ sK1) ◇ (sK1 ◇ sK0)) ◇ sK1) := mod_symm nh
  have step12 (X Y : G) : ((Y ◇ (Y ◇ X)) ◇ (Y ◇ X)) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => ((Y ◇ s) ◇ s)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (Y ◇ s)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (Y ◇ s)) (fun s => ((Y ◇ s) ◇ s)) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step13 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step14 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step15 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X0) = (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) := superpose step10 step10
  have step17 (X0 X1 : G) :  (X1 ◇ X0) = ((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0))) := superpose step12 step10
  have step23 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X0) = (X0 ◇ ((X1 ◇ X0) ◇ X1)) := superpose step13 step12
  have step39 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (((X1 ◇ X0) ◇ X0) ◇ X0) := superpose step14 step12
  have step66 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ X0) ◇ X0)) = (((X1 ◇ X0) ◇ X0) ◇ (X0 ◇ X1)) := superpose step10 step23
  have step179 (X0 X1 : G) :  ((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ X0) = ((((X0 ◇ X1) ◇ X1) ◇ (X1 ◇ ((X0 ◇ X1) ◇ X1))) ◇ (X1 ◇ ((X0 ◇ X1) ◇ X1))) := superpose step15 step39
  have step180 (X0 X1 : G) :  (((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1))) = (((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1))) ◇ (X1 ◇ (X0 ◇ X1))) := superpose step17 step39
  have step212 (X0 X1 : G) :  (X1 ◇ (X0 ◇ (X0 ◇ X1))) = (((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1))) ◇ (X1 ◇ (X0 ◇ X1))) := superpose step12 step180
  have step213 (X0 X1 : G) :  (X1 ◇ X0) = ((((X0 ◇ X1) ◇ X1) ◇ (X1 ◇ ((X0 ◇ X1) ◇ X1))) ◇ (X1 ◇ ((X0 ◇ X1) ◇ X1))) := superpose step10 step179
  have step214 (X0 X1 : G) :  (X1 ◇ X0) = (X1 ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X1))) := superpose step212 step213
  have step611 (X0 X1 : G) :  ((X0 ◇ X1) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) = ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ X0)) := superpose step214 step14
  have step625 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ X0)) = X1 := superpose step14 step611
  have step719 (X0 X1 : G) :  (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) = X1 := superpose step10 step625
  have step739 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X0) = X1 := superpose step12 step625
  have step751 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X1) = (((X0 ◇ X1) ◇ X0) ◇ X0) := superpose step625 step12
  have step933 (X0 X1 : G) :  (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X0) = X1 := superpose step739 step12
  have step1134 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X0) = (X1 ◇ ((X0 ◇ X1) ◇ X1)) := superpose step719 step12
  have step1240 (X0 X1 : G) :  (((((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) ◇ X0) = ((X0 ◇ X1) ◇ ((((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1))) := superpose step625 step66
  have step1319 (X0 X1 : G) :  (((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) ◇ ((X0 ◇ X1) ◇ X1)) = (((((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) ◇ X0) := superpose step1134 step1240
  have step1357 (X0 X1 : G) :  ((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ X0) = (((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) ◇ ((X0 ◇ X1) ◇ X1)) := superpose step751 step1319
  have step1375 (X0 X1 : G) :  ((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ X0) = X1 := superpose step12 step1357
  have step1412 (X0 X1 : G) :  ((((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ X0) ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) = X0 := superpose step39 step1375
  have step1489 (X0 X1 : G) :  ((X1 ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) = X0 := superpose step1375 step1412
  have step2447 (X0 X1 : G) :  (X0 ◇ (X0 ◇ X1)) = (((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X1 ◇ X0)) := superpose step1489 step1375
  have step2449 (X0 X1 : G) :  (X0 ◇ (X0 ◇ X1)) = ((((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X0) ◇ X0) ◇ (X1 ◇ X0)) := superpose step751 step2447
  have step2523 (X0 X1 : G) :  ((X0 ◇ X1) ◇ (X1 ◇ X0)) = (X0 ◇ (X0 ◇ X1)) := superpose step933 step2449
  have step33754 : sK0 ≠ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) := superpose step2523 step11
  subsumption step33754 step739


@[equational_result]
theorem Finite.Equation677_and_Equation124_implies_Equation3103 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation124 G) : Equation3103 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step10 (X0 X1 : G) :  (X1 ◇ ((X1 ◇ X0) ◇ X0)) = X0 := mod_symm (h ..)
  have step11 : sK0 ≠ ((((sK1 ◇ sK0) ◇ sK0) ◇ sK0) ◇ sK1) := mod_symm nh
  have step12 (X Y : G) : ((Y ◇ (Y ◇ X)) ◇ (Y ◇ X)) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => ((Y ◇ s) ◇ s)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (Y ◇ s)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (Y ◇ s)) (fun s => ((Y ◇ s) ◇ s)) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step13 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step14 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step15 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X0) = (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) := superpose step10 step10
  have step17 (X0 X1 : G) :  (X1 ◇ X0) = ((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0))) := superpose step12 step10
  have step23 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X0) = (X0 ◇ ((X1 ◇ X0) ◇ X1)) := superpose step13 step12
  have step39 (X0 X1 : G) :  (((X1 ◇ X0) ◇ X0) ◇ X0) = ((X1 ◇ (X1 ◇ X0)) ◇ X1) := superpose step14 step12
  have step66 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ X0) ◇ X0)) = (((X1 ◇ X0) ◇ X0) ◇ (X0 ◇ X1)) := superpose step10 step23
  have step180 (X0 X1 : G) :  ((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ X0) = ((((X0 ◇ X1) ◇ X1) ◇ (X1 ◇ ((X0 ◇ X1) ◇ X1))) ◇ (X1 ◇ ((X0 ◇ X1) ◇ X1))) := superpose step15 step39
  have step181 (X0 X1 : G) :  (((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1))) = (((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1))) ◇ (X1 ◇ (X0 ◇ X1))) := superpose step17 step39
  have step213 (X0 X1 : G) :  (X1 ◇ (X0 ◇ (X0 ◇ X1))) = (((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1))) ◇ (X1 ◇ (X0 ◇ X1))) := superpose step12 step181
  have step214 (X0 X1 : G) :  (X1 ◇ X0) = ((((X0 ◇ X1) ◇ X1) ◇ (X1 ◇ ((X0 ◇ X1) ◇ X1))) ◇ (X1 ◇ ((X0 ◇ X1) ◇ X1))) := superpose step10 step180
  have step215 (X0 X1 : G) :  (X1 ◇ X0) = (X1 ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X1))) := superpose step213 step214
  have step684 (X0 X1 : G) :  ((X0 ◇ X1) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) = ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ X0)) := superpose step215 step14
  have step699 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ X0)) = X1 := superpose step14 step684
  have step864 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X1) = (((X0 ◇ X1) ◇ X0) ◇ X0) := superpose step699 step12
  have step1117 (X0 X1 : G) :  (((((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) ◇ X0) = ((X0 ◇ X1) ◇ ((((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1))) := superpose step699 step66
  have step1184 (X0 X1 : G) :  ((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ X0) = ((X0 ◇ X1) ◇ (((X0 ◇ X1) ◇ X1) ◇ X1)) := superpose step864 step1117
  have step1209 (X0 X1 : G) :  ((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ X0) = X1 := superpose step10 step1184
  have step1521 : sK0 ≠ sK0 := superpose step1209 step11
  subsumption step1521 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation124_implies_Equation4157 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation124 G) : Equation4157 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step10 (X0 X1 : G) :  (X1 ◇ ((X1 ◇ X0) ◇ X0)) = X0 := mod_symm (h ..)
  have step11 : (sK0 ◇ sK1) ≠ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0) := mod_symm nh
  have step12 (X Y : G) : ((Y ◇ (Y ◇ X)) ◇ (Y ◇ X)) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => ((Y ◇ s) ◇ s)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (Y ◇ s)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (Y ◇ s)) (fun s => ((Y ◇ s) ◇ s)) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step13 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step14 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step15 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X0) = (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) := superpose step10 step10
  have step17 (X0 X1 : G) :  (X1 ◇ X0) = ((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0))) := superpose step12 step10
  have step23 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X0) = (X0 ◇ ((X1 ◇ X0) ◇ X1)) := superpose step13 step12
  have step39 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (((X1 ◇ X0) ◇ X0) ◇ X0) := superpose step14 step12
  have step66 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ X0) ◇ X0)) = (((X1 ◇ X0) ◇ X0) ◇ (X0 ◇ X1)) := superpose step10 step23
  have step147 (X0 X1 : G) :  (X1 ◇ (X0 ◇ X1)) = (((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) := superpose step17 step12
  have step158 (X0 X1 : G) :  (X1 ◇ (X0 ◇ X1)) = ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X0) := superpose step39 step147
  have step179 (X0 X1 : G) :  ((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ X0) = ((((X0 ◇ X1) ◇ X1) ◇ (X1 ◇ ((X0 ◇ X1) ◇ X1))) ◇ (X1 ◇ ((X0 ◇ X1) ◇ X1))) := superpose step15 step39
  have step180 (X0 X1 : G) :  (((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1))) = (((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1))) ◇ (X1 ◇ (X0 ◇ X1))) := superpose step17 step39
  have step189 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ X1)) ◇ ((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ X0)) = X0 := superpose step39 step10
  have step212 (X0 X1 : G) :  (X1 ◇ (X0 ◇ (X0 ◇ X1))) = (((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1))) ◇ (X1 ◇ (X0 ◇ X1))) := superpose step12 step180
  have step213 (X0 X1 : G) :  (X1 ◇ X0) = ((((X0 ◇ X1) ◇ X1) ◇ (X1 ◇ ((X0 ◇ X1) ◇ X1))) ◇ (X1 ◇ ((X0 ◇ X1) ◇ X1))) := superpose step10 step179
  have step214 (X0 X1 : G) :  (X1 ◇ X0) = (X1 ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X1))) := superpose step212 step213
  have step611 (X0 X1 : G) :  ((X0 ◇ X1) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) = ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ X0)) := superpose step214 step14
  have step625 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ X0)) = X1 := superpose step14 step611
  have step719 (X0 X1 : G) :  (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) = X1 := superpose step10 step625
  have step751 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X1) = (((X0 ◇ X1) ◇ X0) ◇ X0) := superpose step625 step12
  have step1134 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X0) = (X1 ◇ ((X0 ◇ X1) ◇ X1)) := superpose step719 step12
  have step1240 (X0 X1 : G) :  (((((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) ◇ X0) = ((X0 ◇ X1) ◇ ((((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1))) := superpose step625 step66
  have step1319 (X0 X1 : G) :  (((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) ◇ ((X0 ◇ X1) ◇ X1)) = (((((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) ◇ X0) := superpose step1134 step1240
  have step1357 (X0 X1 : G) :  ((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ X0) = (((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) ◇ ((X0 ◇ X1) ◇ X1)) := superpose step751 step1319
  have step1375 (X0 X1 : G) :  ((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ X0) = X1 := superpose step12 step1357
  have step1418 (X0 X1 : G) :  (X1 ◇ X0) = ((X0 ◇ (X1 ◇ X0)) ◇ X1) := superpose step12 step1375
  have step1454 (X0 X1 : G) :  (X0 ◇ (X0 ◇ X1)) = (((X1 ◇ X0) ◇ X0) ◇ X0) := superpose step1375 step625
  have step2199 (X0 X1 : G) :  (((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) ◇ (X0 ◇ (X0 ◇ X1))) = (((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ X0) ◇ X0) := superpose step189 step158
  have step2212 (X0 X1 : G) :  (X1 ◇ X0) = (((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) ◇ (X0 ◇ (X0 ◇ X1))) := superpose step1375 step2199
  have step2273 (X0 X1 : G) :  (X1 ◇ X0) = ((((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X0) ◇ X0) := superpose step39 step2212
  have step2309 (X0 X1 : G) :  (X1 ◇ X0) = (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) := superpose step1454 step2273
  have step3227 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X1) = (X1 ◇ (X0 ◇ X1)) := superpose step2309 step2309
  have step3870 : (sK0 ◇ sK1) ≠ ((sK1 ◇ (sK0 ◇ sK1)) ◇ sK0) := superpose step3227 step11
  subsumption step3870 step1418


@[equational_result]
theorem Finite.Equation677_and_Equation124_implies_Equation474 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation124 G) : Equation474 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step10 (X0 X1 : G) :  (X1 ◇ ((X1 ◇ X0) ◇ X0)) = X0 := mod_symm (h ..)
  have step11 : sK0 ≠ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := mod_symm nh
  have step12 (X Y : G) : ((Y ◇ (Y ◇ X)) ◇ (Y ◇ X)) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => ((Y ◇ s) ◇ s)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (Y ◇ s)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (Y ◇ s)) (fun s => ((Y ◇ s) ◇ s)) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step13 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step14 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step15 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X0) = (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) := superpose step10 step10
  have step16 (X0 X1 : G) :  (X1 ◇ X0) = (((X1 ◇ (X1 ◇ X0)) ◇ X0) ◇ X0) := superpose step12 step12
  have step17 (X0 X1 : G) :  (X1 ◇ X0) = ((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0))) := superpose step12 step10
  have step23 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X0) = (X0 ◇ ((X1 ◇ X0) ◇ X1)) := superpose step13 step12
  have step39 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (((X1 ◇ X0) ◇ X0) ◇ X0) := superpose step14 step12
  have step57 (X0 X1 : G) :  (((X0 ◇ (X0 ◇ X1)) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) = X1 := superpose step16 step10
  have step66 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ X0) ◇ X0)) = (((X1 ◇ X0) ◇ X0) ◇ (X0 ◇ X1)) := superpose step10 step23
  have step80 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X0) = ((X1 ◇ ((X0 ◇ X1) ◇ X1)) ◇ ((X0 ◇ X1) ◇ X1)) := superpose step23 step12
  have step147 (X0 X1 : G) :  (X1 ◇ (X0 ◇ X1)) = (((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) := superpose step17 step12
  have step158 (X0 X1 : G) :  (X1 ◇ (X0 ◇ X1)) = ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X0) := superpose step39 step147
  have step179 (X0 X1 : G) :  ((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ X0) = ((((X0 ◇ X1) ◇ X1) ◇ (X1 ◇ ((X0 ◇ X1) ◇ X1))) ◇ (X1 ◇ ((X0 ◇ X1) ◇ X1))) := superpose step15 step39
  have step180 (X0 X1 : G) :  (((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1))) = (((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1))) ◇ (X1 ◇ (X0 ◇ X1))) := superpose step17 step39
  have step189 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ X1)) ◇ ((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ X0)) = X0 := superpose step39 step10
  have step212 (X0 X1 : G) :  (X1 ◇ (X0 ◇ (X0 ◇ X1))) = (((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1))) ◇ (X1 ◇ (X0 ◇ X1))) := superpose step12 step180
  have step213 (X0 X1 : G) :  (X1 ◇ X0) = ((((X0 ◇ X1) ◇ X1) ◇ (X1 ◇ ((X0 ◇ X1) ◇ X1))) ◇ (X1 ◇ ((X0 ◇ X1) ◇ X1))) := superpose step10 step179
  have step214 (X0 X1 : G) :  (X1 ◇ X0) = (X1 ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X1))) := superpose step212 step213
  have step611 (X0 X1 : G) :  ((X0 ◇ X1) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) = ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ X0)) := superpose step214 step14
  have step625 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ X0)) = X1 := superpose step14 step611
  have step719 (X0 X1 : G) :  (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) = X1 := superpose step10 step625
  have step739 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X0) = X1 := superpose step12 step625
  have step751 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X1) = (((X0 ◇ X1) ◇ X0) ◇ X0) := superpose step625 step12
  have step1134 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X0) = (X1 ◇ ((X0 ◇ X1) ◇ X1)) := superpose step719 step12
  have step1240 (X0 X1 : G) :  (((((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) ◇ X0) = ((X0 ◇ X1) ◇ ((((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1))) := superpose step625 step66
  have step1319 (X0 X1 : G) :  (((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) ◇ ((X0 ◇ X1) ◇ X1)) = (((((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) ◇ X0) := superpose step1134 step1240
  have step1357 (X0 X1 : G) :  ((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ X0) = (((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) ◇ ((X0 ◇ X1) ◇ X1)) := superpose step751 step1319
  have step1375 (X0 X1 : G) :  ((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ X0) = X1 := superpose step12 step1357
  have step1454 (X0 X1 : G) :  (X0 ◇ (X0 ◇ X1)) = (((X1 ◇ X0) ◇ X0) ◇ X0) := superpose step1375 step625
  have step2199 (X0 X1 : G) :  (((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) ◇ (X0 ◇ (X0 ◇ X1))) = (((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ X0) ◇ X0) := superpose step189 step158
  have step2212 (X0 X1 : G) :  (X1 ◇ X0) = (((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) ◇ (X0 ◇ (X0 ◇ X1))) := superpose step1375 step2199
  have step2273 (X0 X1 : G) :  (X1 ◇ X0) = ((((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X0) ◇ X0) := superpose step39 step2212
  have step2309 (X0 X1 : G) :  (X1 ◇ X0) = (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) := superpose step1454 step2273
  have step3227 (X0 X1 : G) :  (X1 ◇ (X0 ◇ X1)) = ((X1 ◇ X0) ◇ X1) := superpose step2309 step2309
  have step3484 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X1) = (((X1 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X1))) ◇ ((X0 ◇ X1) ◇ X1)) ◇ ((X0 ◇ X1) ◇ X0)) := superpose step80 step57
  have step3560 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X1) = (((X1 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X1))) ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X0 ◇ (X1 ◇ X0))) := superpose step3227 step3484
  have step3615 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X1) = (X1 ◇ (X0 ◇ (X1 ◇ X0))) := superpose step739 step3560
  have step4526 : sK0 ≠ (sK1 ◇ ((sK1 ◇ sK0) ◇ sK0)) := superpose step3615 step11
  subsumption step4526 step10


@[equational_result]
theorem Finite.Equation677_and_Equation124_implies_Equation707 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation124 G) : Equation707 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step10 (X0 X1 : G) :  (X1 ◇ ((X1 ◇ X0) ◇ X0)) = X0 := mod_symm (h ..)
  have step11 : sK0 ≠ (sK1 ◇ (sK1 ◇ ((sK0 ◇ sK1) ◇ sK1))) := mod_symm nh
  have step12 (X Y : G) : ((Y ◇ (Y ◇ X)) ◇ (Y ◇ X)) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => ((Y ◇ s) ◇ s)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (Y ◇ s)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (Y ◇ s)) (fun s => ((Y ◇ s) ◇ s)) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step14 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step15 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X0) = (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) := superpose step10 step10
  have step17 (X0 X1 : G) :  (X1 ◇ X0) = ((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0))) := superpose step12 step10
  have step39 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (((X1 ◇ X0) ◇ X0) ◇ X0) := superpose step14 step12
  have step179 (X0 X1 : G) :  ((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ X0) = ((((X0 ◇ X1) ◇ X1) ◇ (X1 ◇ ((X0 ◇ X1) ◇ X1))) ◇ (X1 ◇ ((X0 ◇ X1) ◇ X1))) := superpose step15 step39
  have step180 (X0 X1 : G) :  (((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1))) = (((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1))) ◇ (X1 ◇ (X0 ◇ X1))) := superpose step17 step39
  have step212 (X0 X1 : G) :  (X1 ◇ (X0 ◇ (X0 ◇ X1))) = (((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1))) ◇ (X1 ◇ (X0 ◇ X1))) := superpose step12 step180
  have step213 (X0 X1 : G) :  (X1 ◇ X0) = ((((X0 ◇ X1) ◇ X1) ◇ (X1 ◇ ((X0 ◇ X1) ◇ X1))) ◇ (X1 ◇ ((X0 ◇ X1) ◇ X1))) := superpose step10 step179
  have step214 (X0 X1 : G) :  (X1 ◇ X0) = (X1 ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X1))) := superpose step212 step213
  have step611 (X0 X1 : G) :  ((X0 ◇ X1) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) = ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ X0)) := superpose step214 step14
  have step625 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ X0)) = X1 := superpose step14 step611
  have step719 (X0 X1 : G) :  (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) = X1 := superpose step10 step625
  have step1120 : sK0 ≠ sK0 := superpose step719 step11
  subsumption step1120 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation1249_implies_Equation1035 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation1249 G) : Equation1035 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ (((X1 ◇ X1) ◇ X0) ◇ X1)) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ (sK0 ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ sK0)) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step17 (X0 X1 : G) :  (((X1 ◇ X1) ◇ X0) ◇ X1) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose step9 step12
  have step18 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step20 (X0 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ X0) = (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ X0)) := superpose step12 step9
  have step22 (X0 X1 X2 : G) :  (((X0 ◇ X0) ◇ X1) ◇ X0) = (((X2 ◇ X2) ◇ X1) ◇ X2) := superpose step17 step17
  have step24 (X0 X1 : G) :  ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((((X1 ◇ X1) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X1 ◇ X1) ◇ X0))) = X1 := superpose step17 step12
  have step27 (X0 X1 : G) :  ((X1 ◇ X1) ◇ X1) = ((((X0 ◇ X0) ◇ X1) ◇ X0) ◇ ((X1 ◇ (((X0 ◇ X0) ◇ X1) ◇ X0)) ◇ X1)) := superpose step17 step12
  have step30 (X0 X1 : G) :  ((X1 ◇ X1) ◇ X1) = ((((X0 ◇ X0) ◇ X1) ◇ X0) ◇ (X1 ◇ X1)) := superpose step9 step27
  have step44 (X0 X1 : G) :  (X0 ◇ X0) = (((X1 ◇ X1) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ X1) := superpose step12 step22
  have step45 (X0 X1 X2 : G) :  ((X0 ◇ X0) ◇ X0) = (((X1 ◇ X1) ◇ (((X2 ◇ X2) ◇ (X0 ◇ X0)) ◇ X2)) ◇ X1) := superpose step9 step22
  have step47 (X0 X1 X2 : G) :  (((X1 ◇ X1) ◇ (X0 ◇ (((X2 ◇ X2) ◇ X0) ◇ (X2 ◇ X2)))) ◇ X1) = (X0 ◇ X2) := superpose step11 step22
  have step80 (X0 X1 : G) :  ((X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) ◇ (((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)))) ◇ (X1 ◇ (X1 ◇ X0)))) = X1 := superpose step18 step12
  have step83 (X0 X1 : G) :  (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) = (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ ((X1 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) ◇ X1)) := superpose step18 step12
  have step90 (X0 : G) :  ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) = ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) := superpose step12 step30
  have step111 (X0 : G) :  (X0 ◇ X0) = (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) := superpose step20 step11
  have step272 (X0 X1 X2 X3 : G) :  (((X3 ◇ X3) ◇ X2) ◇ X3) = ((((X0 ◇ X0) ◇ (((X1 ◇ X1) ◇ (X2 ◇ X2)) ◇ X1)) ◇ X0) ◇ X2) := superpose step45 step22
  have step1213 (X0 : G) :  (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) = ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ ((X0 ◇ X0) ◇ (((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) := superpose step44 step24
  have step1255 (X0 : G) :  (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) = ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) ◇ ((X0 ◇ X0) ◇ (((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))))) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) := superpose step90 step1213
  have step1266 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) := superpose step111 step1255
  have step4082 (X0 : G) :  (X0 ◇ X0) = ((((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) ◇ (X0 ◇ X0))) ◇ ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) ◇ (X0 ◇ X0)))) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) := superpose step1266 step80
  have step4093 (X0 : G) :  (X0 ◇ X0) = ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) := superpose step12 step4082
  have step4121 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose step12 step4093
  have step4282 (X0 : G) :  ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) = (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) := superpose step4121 step83
  have step4284 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose step4121 step12
  have step4286 (X0 X1 : G) :  (X0 ◇ X0) = (((X1 ◇ X1) ◇ (X0 ◇ X0)) ◇ X1) := superpose step4121 step44
  have step4317 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose step12 step4282
  have step4618 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) = ((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) := superpose step4284 step20
  have step4633 (X0 X1 : G) :  (((X1 ◇ X1) ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0))) ◇ X1) = X0 := superpose step4284 step44
  have step4674 (X0 X1 X2 X3 : G) :  ((((X2 ◇ X2) ◇ (((X3 ◇ X3) ◇ (X1 ◇ X1)) ◇ X3)) ◇ X2) ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ X0)) := superpose step4284 step272
  have step4734 (X0 X1 X2 : G) :  ((((X2 ◇ X2) ◇ (X1 ◇ X1)) ◇ X2) ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ X0)) := superpose step4286 step4674
  have step4751 (X0 X1 : G) :  (((X1 ◇ X1) ◇ X0) ◇ X1) = X0 := superpose step4317 step4633
  have step4757 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step4317 step4618
  have step4796 (X0 X1 : G) :  ((X1 ◇ X1) ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ X0)) := superpose step4286 step4734
  have step4827 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X0) = ((X1 ◇ X1) ◇ X1) := superpose step4757 step4796
  have step4850 (X0 X1 : G) :  (X1 ◇ X1) = ((X0 ◇ X1) ◇ X0) := superpose step4757 step4827
  have step4866 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X0) = X1 := superpose step4757 step4850
  have step5314 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ ((((X1 ◇ X1) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X1 ◇ X1) ◇ X0))) = X1 := superpose step4757 step24
  have step5330 (X0 X1 X2 : G) :  (((X1 ◇ X1) ◇ (X2 ◇ ((X0 ◇ X2) ◇ X0))) ◇ X1) = (X2 ◇ X0) := superpose step4757 step47
  have step5580 (X0 X2 : G) :  (X2 ◇ ((X0 ◇ X2) ◇ X0)) = (X2 ◇ X0) := superpose step4751 step5330
  have step5594 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) = X1 := superpose step4866 step5314
  have step5693 (X0 X2 : G) :  (X2 ◇ X2) = (X2 ◇ X0) := superpose step4866 step5580
  have step5704 (X0 X1 : G) :  (X0 ◇ (X0 ◇ X0)) = X1 := superpose step4757 step5594
  have step5765 (X0 X2 : G) :  (X2 ◇ X0) = X2 := superpose step4757 step5693
  have step5772 (X0 X1 : G) :  (X0 ◇ X0) = X1 := superpose step4757 step5704
  have step5791 (X0 X1 : G) :  X0 = X1 := superpose step5765 step5772
  have step6910 (X0 : G) :  (X0 ◇ ((sK1 ◇ (X0 ◇ X0)) ◇ X0)) ≠ X0 := superpose step5791 step10
  subsumption step6910 step5765


@[equational_result]
theorem Finite.Equation677_and_Equation1249_implies_Equation1048 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation1249 G) : Equation1048 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ (((X1 ◇ X1) ◇ X0) ◇ X1)) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ (sK0 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ sK0)) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step17 (X0 X1 : G) :  (((X1 ◇ X1) ◇ X0) ◇ X1) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose step9 step12
  have step18 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step20 (X0 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ X0) = (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ X0)) := superpose step12 step9
  have step22 (X0 X1 X2 : G) :  (((X0 ◇ X0) ◇ X1) ◇ X0) = (((X2 ◇ X2) ◇ X1) ◇ X2) := superpose step17 step17
  have step24 (X0 X1 : G) :  ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((((X1 ◇ X1) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X1 ◇ X1) ◇ X0))) = X1 := superpose step17 step12
  have step27 (X0 X1 : G) :  ((X1 ◇ X1) ◇ X1) = ((((X0 ◇ X0) ◇ X1) ◇ X0) ◇ ((X1 ◇ (((X0 ◇ X0) ◇ X1) ◇ X0)) ◇ X1)) := superpose step17 step12
  have step30 (X0 X1 : G) :  ((X1 ◇ X1) ◇ X1) = ((((X0 ◇ X0) ◇ X1) ◇ X0) ◇ (X1 ◇ X1)) := superpose step9 step27
  have step44 (X0 X1 : G) :  (X0 ◇ X0) = (((X1 ◇ X1) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ X1) := superpose step12 step22
  have step45 (X0 X1 X2 : G) :  ((X0 ◇ X0) ◇ X0) = (((X1 ◇ X1) ◇ (((X2 ◇ X2) ◇ (X0 ◇ X0)) ◇ X2)) ◇ X1) := superpose step9 step22
  have step47 (X0 X1 X2 : G) :  (((X1 ◇ X1) ◇ (X0 ◇ (((X2 ◇ X2) ◇ X0) ◇ (X2 ◇ X2)))) ◇ X1) = (X0 ◇ X2) := superpose step11 step22
  have step80 (X0 X1 : G) :  ((X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) ◇ (((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)))) ◇ (X1 ◇ (X1 ◇ X0)))) = X1 := superpose step18 step12
  have step83 (X0 X1 : G) :  (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) = (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ ((X1 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) ◇ X1)) := superpose step18 step12
  have step90 (X0 : G) :  ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) = ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) := superpose step12 step30
  have step111 (X0 : G) :  (X0 ◇ X0) = (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) := superpose step20 step11
  have step272 (X0 X1 X2 X3 : G) :  (((X3 ◇ X3) ◇ X2) ◇ X3) = ((((X0 ◇ X0) ◇ (((X1 ◇ X1) ◇ (X2 ◇ X2)) ◇ X1)) ◇ X0) ◇ X2) := superpose step45 step22
  have step1213 (X0 : G) :  (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) = ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ ((X0 ◇ X0) ◇ (((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) := superpose step44 step24
  have step1255 (X0 : G) :  (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) = ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) ◇ ((X0 ◇ X0) ◇ (((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))))) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) := superpose step90 step1213
  have step1266 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) := superpose step111 step1255
  have step4082 (X0 : G) :  (X0 ◇ X0) = ((((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) ◇ (X0 ◇ X0))) ◇ ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) ◇ (X0 ◇ X0)))) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) := superpose step1266 step80
  have step4093 (X0 : G) :  (X0 ◇ X0) = ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) := superpose step12 step4082
  have step4121 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose step12 step4093
  have step4282 (X0 : G) :  ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) = (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) := superpose step4121 step83
  have step4284 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose step4121 step12
  have step4286 (X0 X1 : G) :  (X0 ◇ X0) = (((X1 ◇ X1) ◇ (X0 ◇ X0)) ◇ X1) := superpose step4121 step44
  have step4317 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose step12 step4282
  have step4618 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) = ((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) := superpose step4284 step20
  have step4633 (X0 X1 : G) :  (((X1 ◇ X1) ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0))) ◇ X1) = X0 := superpose step4284 step44
  have step4674 (X0 X1 X2 X3 : G) :  ((((X2 ◇ X2) ◇ (((X3 ◇ X3) ◇ (X1 ◇ X1)) ◇ X3)) ◇ X2) ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ X0)) := superpose step4284 step272
  have step4734 (X0 X1 X2 : G) :  ((((X2 ◇ X2) ◇ (X1 ◇ X1)) ◇ X2) ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ X0)) := superpose step4286 step4674
  have step4751 (X0 X1 : G) :  (((X1 ◇ X1) ◇ X0) ◇ X1) = X0 := superpose step4317 step4633
  have step4757 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step4317 step4618
  have step4796 (X0 X1 : G) :  ((X1 ◇ X1) ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ X0)) := superpose step4286 step4734
  have step4827 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X0) = ((X1 ◇ X1) ◇ X1) := superpose step4757 step4796
  have step4850 (X0 X1 : G) :  (X1 ◇ X1) = ((X0 ◇ X1) ◇ X0) := superpose step4757 step4827
  have step4866 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X0) = X1 := superpose step4757 step4850
  have step5314 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ ((((X1 ◇ X1) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X1 ◇ X1) ◇ X0))) = X1 := superpose step4757 step24
  have step5330 (X0 X1 X2 : G) :  (((X1 ◇ X1) ◇ (X2 ◇ ((X0 ◇ X2) ◇ X0))) ◇ X1) = (X2 ◇ X0) := superpose step4757 step47
  have step5581 (X0 X2 : G) :  (X2 ◇ ((X0 ◇ X2) ◇ X0)) = (X2 ◇ X0) := superpose step4751 step5330
  have step5595 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) = X1 := superpose step4866 step5314
  have step5694 (X0 X2 : G) :  (X2 ◇ X2) = (X2 ◇ X0) := superpose step4866 step5581
  have step5705 (X0 X1 : G) :  (X0 ◇ (X0 ◇ X0)) = X1 := superpose step4757 step5595
  have step5766 (X0 X2 : G) :  (X2 ◇ X0) = X2 := superpose step4757 step5694
  have step5773 (X0 X1 : G) :  (X0 ◇ X0) = X1 := superpose step4757 step5705
  have step5789 (X0 X1 : G) :  X0 = X1 := superpose step5766 step5773
  have step6906 (X0 : G) :  (X0 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)) ≠ X0 := superpose step5789 step10
  subsumption step6906 step5766


@[equational_result]
theorem Finite.Equation677_and_Equation1249_implies_Equation1076 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation1249 G) : Equation1076 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ (((X1 ◇ X1) ◇ X0) ◇ X1)) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ (sK1 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step17 (X0 X1 : G) :  (((X1 ◇ X1) ◇ X0) ◇ X1) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose step9 step12
  have step18 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step20 (X0 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ X0) = (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ X0)) := superpose step12 step9
  have step22 (X0 X1 X2 : G) :  (((X0 ◇ X0) ◇ X1) ◇ X0) = (((X2 ◇ X2) ◇ X1) ◇ X2) := superpose step17 step17
  have step24 (X0 X1 : G) :  ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((((X1 ◇ X1) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X1 ◇ X1) ◇ X0))) = X1 := superpose step17 step12
  have step27 (X0 X1 : G) :  ((X1 ◇ X1) ◇ X1) = ((((X0 ◇ X0) ◇ X1) ◇ X0) ◇ ((X1 ◇ (((X0 ◇ X0) ◇ X1) ◇ X0)) ◇ X1)) := superpose step17 step12
  have step30 (X0 X1 : G) :  ((X1 ◇ X1) ◇ X1) = ((((X0 ◇ X0) ◇ X1) ◇ X0) ◇ (X1 ◇ X1)) := superpose step9 step27
  have step44 (X0 X1 : G) :  (X0 ◇ X0) = (((X1 ◇ X1) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ X1) := superpose step12 step22
  have step45 (X0 X1 X2 : G) :  ((X0 ◇ X0) ◇ X0) = (((X1 ◇ X1) ◇ (((X2 ◇ X2) ◇ (X0 ◇ X0)) ◇ X2)) ◇ X1) := superpose step9 step22
  have step47 (X0 X1 X2 : G) :  (((X1 ◇ X1) ◇ (X0 ◇ (((X2 ◇ X2) ◇ X0) ◇ (X2 ◇ X2)))) ◇ X1) = (X0 ◇ X2) := superpose step11 step22
  have step80 (X0 X1 : G) :  ((X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) ◇ (((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)))) ◇ (X1 ◇ (X1 ◇ X0)))) = X1 := superpose step18 step12
  have step83 (X0 X1 : G) :  (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) = (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ ((X1 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) ◇ X1)) := superpose step18 step12
  have step90 (X0 : G) :  ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) = ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) := superpose step12 step30
  have step111 (X0 : G) :  (X0 ◇ X0) = (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) := superpose step20 step11
  have step272 (X0 X1 X2 X3 : G) :  (((X3 ◇ X3) ◇ X2) ◇ X3) = ((((X0 ◇ X0) ◇ (((X1 ◇ X1) ◇ (X2 ◇ X2)) ◇ X1)) ◇ X0) ◇ X2) := superpose step45 step22
  have step1213 (X0 : G) :  (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) = ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ ((X0 ◇ X0) ◇ (((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) := superpose step44 step24
  have step1255 (X0 : G) :  (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) = ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) ◇ ((X0 ◇ X0) ◇ (((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))))) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) := superpose step90 step1213
  have step1266 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) := superpose step111 step1255
  have step4082 (X0 : G) :  (X0 ◇ X0) = ((((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) ◇ (X0 ◇ X0))) ◇ ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) ◇ (X0 ◇ X0)))) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) := superpose step1266 step80
  have step4093 (X0 : G) :  (X0 ◇ X0) = ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) := superpose step12 step4082
  have step4121 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose step12 step4093
  have step4282 (X0 : G) :  ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) = (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) := superpose step4121 step83
  have step4284 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose step4121 step12
  have step4286 (X0 X1 : G) :  (X0 ◇ X0) = (((X1 ◇ X1) ◇ (X0 ◇ X0)) ◇ X1) := superpose step4121 step44
  have step4317 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose step12 step4282
  have step4618 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) = ((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) := superpose step4284 step20
  have step4633 (X0 X1 : G) :  (((X1 ◇ X1) ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0))) ◇ X1) = X0 := superpose step4284 step44
  have step4674 (X0 X1 X2 X3 : G) :  ((((X2 ◇ X2) ◇ (((X3 ◇ X3) ◇ (X1 ◇ X1)) ◇ X3)) ◇ X2) ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ X0)) := superpose step4284 step272
  have step4734 (X0 X1 X2 : G) :  ((((X2 ◇ X2) ◇ (X1 ◇ X1)) ◇ X2) ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ X0)) := superpose step4286 step4674
  have step4751 (X0 X1 : G) :  (((X1 ◇ X1) ◇ X0) ◇ X1) = X0 := superpose step4317 step4633
  have step4757 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step4317 step4618
  have step4796 (X0 X1 : G) :  ((X1 ◇ X1) ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ X0)) := superpose step4286 step4734
  have step4827 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X0) = ((X1 ◇ X1) ◇ X1) := superpose step4757 step4796
  have step4850 (X0 X1 : G) :  (X1 ◇ X1) = ((X0 ◇ X1) ◇ X0) := superpose step4757 step4827
  have step4866 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X0) = X1 := superpose step4757 step4850
  have step5314 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ ((((X1 ◇ X1) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X1 ◇ X1) ◇ X0))) = X1 := superpose step4757 step24
  have step5330 (X0 X1 X2 : G) :  (((X1 ◇ X1) ◇ (X2 ◇ ((X0 ◇ X2) ◇ X0))) ◇ X1) = (X2 ◇ X0) := superpose step4757 step47
  have step5579 (X0 X2 : G) :  (X2 ◇ ((X0 ◇ X2) ◇ X0)) = (X2 ◇ X0) := superpose step4751 step5330
  have step5593 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) = X1 := superpose step4866 step5314
  have step5692 (X0 X2 : G) :  (X2 ◇ X2) = (X2 ◇ X0) := superpose step4866 step5579
  have step5703 (X0 X1 : G) :  (X0 ◇ (X0 ◇ X0)) = X1 := superpose step4757 step5593
  have step5764 (X0 X2 : G) :  (X2 ◇ X0) = X2 := superpose step4757 step5692
  have step5771 (X0 X1 : G) :  (X0 ◇ X0) = X1 := superpose step4757 step5703
  have step5790 (X0 X1 : G) :  X0 = X1 := superpose step5764 step5771
  have step6738 (X0 : G) :  sK0 ≠ (X0 ◇ ((sK0 ◇ (sK0 ◇ X0)) ◇ X0)) := superpose step5790 step10
  subsumption step6738 step5790


@[equational_result]
theorem Finite.Equation677_and_Equation1249_implies_Equation1082 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation1249 G) : Equation1082 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ (((X1 ◇ X1) ◇ X0) ◇ X1)) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0)) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step17 (X0 X1 : G) :  (((X1 ◇ X1) ◇ X0) ◇ X1) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose step9 step12
  have step18 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step20 (X0 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ X0) = (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ X0)) := superpose step12 step9
  have step22 (X0 X1 X2 : G) :  (((X0 ◇ X0) ◇ X1) ◇ X0) = (((X2 ◇ X2) ◇ X1) ◇ X2) := superpose step17 step17
  have step24 (X0 X1 : G) :  ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((((X1 ◇ X1) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X1 ◇ X1) ◇ X0))) = X1 := superpose step17 step12
  have step27 (X0 X1 : G) :  ((X1 ◇ X1) ◇ X1) = ((((X0 ◇ X0) ◇ X1) ◇ X0) ◇ ((X1 ◇ (((X0 ◇ X0) ◇ X1) ◇ X0)) ◇ X1)) := superpose step17 step12
  have step30 (X0 X1 : G) :  ((X1 ◇ X1) ◇ X1) = ((((X0 ◇ X0) ◇ X1) ◇ X0) ◇ (X1 ◇ X1)) := superpose step9 step27
  have step44 (X0 X1 : G) :  (X0 ◇ X0) = (((X1 ◇ X1) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ X1) := superpose step12 step22
  have step45 (X0 X1 X2 : G) :  ((X0 ◇ X0) ◇ X0) = (((X1 ◇ X1) ◇ (((X2 ◇ X2) ◇ (X0 ◇ X0)) ◇ X2)) ◇ X1) := superpose step9 step22
  have step47 (X0 X1 X2 : G) :  (((X1 ◇ X1) ◇ (X0 ◇ (((X2 ◇ X2) ◇ X0) ◇ (X2 ◇ X2)))) ◇ X1) = (X0 ◇ X2) := superpose step11 step22
  have step80 (X0 X1 : G) :  ((X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) ◇ (((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)))) ◇ (X1 ◇ (X1 ◇ X0)))) = X1 := superpose step18 step12
  have step83 (X0 X1 : G) :  (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) = (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ ((X1 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) ◇ X1)) := superpose step18 step12
  have step90 (X0 : G) :  ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) = ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) := superpose step12 step30
  have step111 (X0 : G) :  (X0 ◇ X0) = (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) := superpose step20 step11
  have step272 (X0 X1 X2 X3 : G) :  (((X3 ◇ X3) ◇ X2) ◇ X3) = ((((X0 ◇ X0) ◇ (((X1 ◇ X1) ◇ (X2 ◇ X2)) ◇ X1)) ◇ X0) ◇ X2) := superpose step45 step22
  have step1213 (X0 : G) :  (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) = ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ ((X0 ◇ X0) ◇ (((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) := superpose step44 step24
  have step1255 (X0 : G) :  (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) = ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) ◇ ((X0 ◇ X0) ◇ (((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))))) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) := superpose step90 step1213
  have step1266 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) := superpose step111 step1255
  have step4082 (X0 : G) :  (X0 ◇ X0) = ((((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) ◇ (X0 ◇ X0))) ◇ ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) ◇ (X0 ◇ X0)))) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) := superpose step1266 step80
  have step4093 (X0 : G) :  (X0 ◇ X0) = ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) := superpose step12 step4082
  have step4121 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose step12 step4093
  have step4282 (X0 : G) :  ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) = (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) := superpose step4121 step83
  have step4284 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose step4121 step12
  have step4286 (X0 X1 : G) :  (X0 ◇ X0) = (((X1 ◇ X1) ◇ (X0 ◇ X0)) ◇ X1) := superpose step4121 step44
  have step4317 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose step12 step4282
  have step4618 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) = ((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) := superpose step4284 step20
  have step4633 (X0 X1 : G) :  (((X1 ◇ X1) ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0))) ◇ X1) = X0 := superpose step4284 step44
  have step4674 (X0 X1 X2 X3 : G) :  ((((X2 ◇ X2) ◇ (((X3 ◇ X3) ◇ (X1 ◇ X1)) ◇ X3)) ◇ X2) ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ X0)) := superpose step4284 step272
  have step4734 (X0 X1 X2 : G) :  ((((X2 ◇ X2) ◇ (X1 ◇ X1)) ◇ X2) ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ X0)) := superpose step4286 step4674
  have step4751 (X0 X1 : G) :  (((X1 ◇ X1) ◇ X0) ◇ X1) = X0 := superpose step4317 step4633
  have step4757 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step4317 step4618
  have step4796 (X0 X1 : G) :  ((X1 ◇ X1) ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ X0)) := superpose step4286 step4734
  have step4827 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X0) = ((X1 ◇ X1) ◇ X1) := superpose step4757 step4796
  have step4850 (X0 X1 : G) :  (X1 ◇ X1) = ((X0 ◇ X1) ◇ X0) := superpose step4757 step4827
  have step4866 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X0) = X1 := superpose step4757 step4850
  have step5314 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ ((((X1 ◇ X1) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X1 ◇ X1) ◇ X0))) = X1 := superpose step4757 step24
  have step5330 (X0 X1 X2 : G) :  (((X1 ◇ X1) ◇ (X2 ◇ ((X0 ◇ X2) ◇ X0))) ◇ X1) = (X2 ◇ X0) := superpose step4757 step47
  have step5579 (X0 X2 : G) :  (X2 ◇ ((X0 ◇ X2) ◇ X0)) = (X2 ◇ X0) := superpose step4751 step5330
  have step5593 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) = X1 := superpose step4866 step5314
  have step5692 (X0 X2 : G) :  (X2 ◇ X2) = (X2 ◇ X0) := superpose step4866 step5579
  have step5703 (X0 X1 : G) :  (X0 ◇ (X0 ◇ X0)) = X1 := superpose step4757 step5593
  have step5764 (X0 X2 : G) :  (X2 ◇ X0) = X2 := superpose step4757 step5692
  have step5771 (X0 X1 : G) :  (X0 ◇ X0) = X1 := superpose step4757 step5703
  have step5790 (X0 X1 : G) :  X0 = X1 := superpose step5764 step5771
  have step6738 (X0 : G) :  (sK1 ◇ ((X0 ◇ (sK1 ◇ X0)) ◇ X0)) ≠ X0 := superpose step5790 step10
  subsumption step6738 step5790


@[equational_result]
theorem Finite.Equation677_and_Equation1249_implies_Equation1098 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation1249 G) : Equation1098 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ (((X1 ◇ X1) ◇ X0) ◇ X1)) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ (sK1 ◇ ((sK0 ◇ (sK2 ◇ sK1)) ◇ sK2)) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step17 (X0 X1 : G) :  (((X1 ◇ X1) ◇ X0) ◇ X1) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose step9 step12
  have step18 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step20 (X0 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ X0) = (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ X0)) := superpose step12 step9
  have step22 (X0 X1 X2 : G) :  (((X0 ◇ X0) ◇ X1) ◇ X0) = (((X2 ◇ X2) ◇ X1) ◇ X2) := superpose step17 step17
  have step24 (X0 X1 : G) :  ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((((X1 ◇ X1) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X1 ◇ X1) ◇ X0))) = X1 := superpose step17 step12
  have step27 (X0 X1 : G) :  ((X1 ◇ X1) ◇ X1) = ((((X0 ◇ X0) ◇ X1) ◇ X0) ◇ ((X1 ◇ (((X0 ◇ X0) ◇ X1) ◇ X0)) ◇ X1)) := superpose step17 step12
  have step30 (X0 X1 : G) :  ((X1 ◇ X1) ◇ X1) = ((((X0 ◇ X0) ◇ X1) ◇ X0) ◇ (X1 ◇ X1)) := superpose step9 step27
  have step44 (X0 X1 : G) :  (X0 ◇ X0) = (((X1 ◇ X1) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ X1) := superpose step12 step22
  have step45 (X0 X1 X2 : G) :  ((X0 ◇ X0) ◇ X0) = (((X1 ◇ X1) ◇ (((X2 ◇ X2) ◇ (X0 ◇ X0)) ◇ X2)) ◇ X1) := superpose step9 step22
  have step47 (X0 X1 X2 : G) :  (((X1 ◇ X1) ◇ (X0 ◇ (((X2 ◇ X2) ◇ X0) ◇ (X2 ◇ X2)))) ◇ X1) = (X0 ◇ X2) := superpose step11 step22
  have step80 (X0 X1 : G) :  ((X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) ◇ (((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)))) ◇ (X1 ◇ (X1 ◇ X0)))) = X1 := superpose step18 step12
  have step83 (X0 X1 : G) :  (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) = (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ ((X1 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) ◇ X1)) := superpose step18 step12
  have step90 (X0 : G) :  ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) = ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) := superpose step12 step30
  have step111 (X0 : G) :  (X0 ◇ X0) = (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) := superpose step20 step11
  have step272 (X0 X1 X2 X3 : G) :  (((X3 ◇ X3) ◇ X2) ◇ X3) = ((((X0 ◇ X0) ◇ (((X1 ◇ X1) ◇ (X2 ◇ X2)) ◇ X1)) ◇ X0) ◇ X2) := superpose step45 step22
  have step1213 (X0 : G) :  (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) = ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ ((X0 ◇ X0) ◇ (((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) := superpose step44 step24
  have step1255 (X0 : G) :  (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) = ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) ◇ ((X0 ◇ X0) ◇ (((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))))) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) := superpose step90 step1213
  have step1266 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) := superpose step111 step1255
  have step4082 (X0 : G) :  (X0 ◇ X0) = ((((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) ◇ (X0 ◇ X0))) ◇ ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) ◇ (X0 ◇ X0)))) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) := superpose step1266 step80
  have step4093 (X0 : G) :  (X0 ◇ X0) = ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) := superpose step12 step4082
  have step4121 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose step12 step4093
  have step4282 (X0 : G) :  ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) = (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) := superpose step4121 step83
  have step4284 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose step4121 step12
  have step4286 (X0 X1 : G) :  (X0 ◇ X0) = (((X1 ◇ X1) ◇ (X0 ◇ X0)) ◇ X1) := superpose step4121 step44
  have step4317 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose step12 step4282
  have step4618 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) = ((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) := superpose step4284 step20
  have step4633 (X0 X1 : G) :  (((X1 ◇ X1) ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0))) ◇ X1) = X0 := superpose step4284 step44
  have step4674 (X0 X1 X2 X3 : G) :  ((((X2 ◇ X2) ◇ (((X3 ◇ X3) ◇ (X1 ◇ X1)) ◇ X3)) ◇ X2) ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ X0)) := superpose step4284 step272
  have step4734 (X0 X1 X2 : G) :  ((((X2 ◇ X2) ◇ (X1 ◇ X1)) ◇ X2) ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ X0)) := superpose step4286 step4674
  have step4751 (X0 X1 : G) :  (((X1 ◇ X1) ◇ X0) ◇ X1) = X0 := superpose step4317 step4633
  have step4757 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step4317 step4618
  have step4796 (X0 X1 : G) :  ((X1 ◇ X1) ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ X0)) := superpose step4286 step4734
  have step4827 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X0) = ((X1 ◇ X1) ◇ X1) := superpose step4757 step4796
  have step4850 (X0 X1 : G) :  (X1 ◇ X1) = ((X0 ◇ X1) ◇ X0) := superpose step4757 step4827
  have step4866 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X0) = X1 := superpose step4757 step4850
  have step5314 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ ((((X1 ◇ X1) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X1 ◇ X1) ◇ X0))) = X1 := superpose step4757 step24
  have step5330 (X0 X1 X2 : G) :  (((X1 ◇ X1) ◇ (X2 ◇ ((X0 ◇ X2) ◇ X0))) ◇ X1) = (X2 ◇ X0) := superpose step4757 step47
  have step5579 (X0 X2 : G) :  (X2 ◇ ((X0 ◇ X2) ◇ X0)) = (X2 ◇ X0) := superpose step4751 step5330
  have step5593 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) = X1 := superpose step4866 step5314
  have step5692 (X0 X2 : G) :  (X2 ◇ X2) = (X2 ◇ X0) := superpose step4866 step5579
  have step5703 (X0 X1 : G) :  (X0 ◇ (X0 ◇ X0)) = X1 := superpose step4757 step5593
  have step5764 (X0 X2 : G) :  (X2 ◇ X0) = X2 := superpose step4757 step5692
  have step5771 (X0 X1 : G) :  (X0 ◇ X0) = X1 := superpose step4757 step5703
  have step5790 (X0 X1 : G) :  X0 = X1 := superpose step5764 step5771
  have step6740 (X0 : G) :  sK0 ≠ (sK1 ◇ ((sK0 ◇ (X0 ◇ sK1)) ◇ X0)) := superpose step5790 step10
  subsumption step6740 step5790


@[equational_result]
theorem Finite.Equation677_and_Equation1249_implies_Equation1117 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation1249 G) : Equation1117 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ (((X1 ◇ X1) ◇ X0) ◇ X1)) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ (sK1 ◇ ((sK1 ◇ (sK0 ◇ sK2)) ◇ sK2)) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step17 (X0 X1 : G) :  (((X1 ◇ X1) ◇ X0) ◇ X1) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose step9 step12
  have step18 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step20 (X0 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ X0) = (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ X0)) := superpose step12 step9
  have step22 (X0 X1 X2 : G) :  (((X0 ◇ X0) ◇ X1) ◇ X0) = (((X2 ◇ X2) ◇ X1) ◇ X2) := superpose step17 step17
  have step24 (X0 X1 : G) :  ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((((X1 ◇ X1) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X1 ◇ X1) ◇ X0))) = X1 := superpose step17 step12
  have step27 (X0 X1 : G) :  ((X1 ◇ X1) ◇ X1) = ((((X0 ◇ X0) ◇ X1) ◇ X0) ◇ ((X1 ◇ (((X0 ◇ X0) ◇ X1) ◇ X0)) ◇ X1)) := superpose step17 step12
  have step30 (X0 X1 : G) :  ((X1 ◇ X1) ◇ X1) = ((((X0 ◇ X0) ◇ X1) ◇ X0) ◇ (X1 ◇ X1)) := superpose step9 step27
  have step44 (X0 X1 : G) :  (X0 ◇ X0) = (((X1 ◇ X1) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ X1) := superpose step12 step22
  have step45 (X0 X1 X2 : G) :  ((X0 ◇ X0) ◇ X0) = (((X1 ◇ X1) ◇ (((X2 ◇ X2) ◇ (X0 ◇ X0)) ◇ X2)) ◇ X1) := superpose step9 step22
  have step47 (X0 X1 X2 : G) :  (X0 ◇ X2) = (((X1 ◇ X1) ◇ (X0 ◇ (((X2 ◇ X2) ◇ X0) ◇ (X2 ◇ X2)))) ◇ X1) := superpose step11 step22
  have step80 (X0 X1 : G) :  ((X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) ◇ (((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)))) ◇ (X1 ◇ (X1 ◇ X0)))) = X1 := superpose step18 step12
  have step83 (X0 X1 : G) :  (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) = (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ ((X1 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) ◇ X1)) := superpose step18 step12
  have step90 (X0 : G) :  ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) = ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) := superpose step12 step30
  have step111 (X0 : G) :  (X0 ◇ X0) = (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) := superpose step20 step11
  have step272 (X0 X1 X2 X3 : G) :  (((X3 ◇ X3) ◇ X2) ◇ X3) = ((((X0 ◇ X0) ◇ (((X1 ◇ X1) ◇ (X2 ◇ X2)) ◇ X1)) ◇ X0) ◇ X2) := superpose step45 step22
  have step1213 (X0 : G) :  (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) = ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ ((X0 ◇ X0) ◇ (((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) := superpose step44 step24
  have step1255 (X0 : G) :  (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) = ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) ◇ ((X0 ◇ X0) ◇ (((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))))) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) := superpose step90 step1213
  have step1266 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) := superpose step111 step1255
  have step4082 (X0 : G) :  (X0 ◇ X0) = ((((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) ◇ (X0 ◇ X0))) ◇ ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) ◇ (X0 ◇ X0)))) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) := superpose step1266 step80
  have step4093 (X0 : G) :  (X0 ◇ X0) = ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) := superpose step12 step4082
  have step4121 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose step12 step4093
  have step4282 (X0 : G) :  ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) = (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) := superpose step4121 step83
  have step4284 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose step4121 step12
  have step4286 (X0 X1 : G) :  (X0 ◇ X0) = (((X1 ◇ X1) ◇ (X0 ◇ X0)) ◇ X1) := superpose step4121 step44
  have step4317 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose step12 step4282
  have step4618 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) = ((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) := superpose step4284 step20
  have step4633 (X0 X1 : G) :  (((X1 ◇ X1) ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0))) ◇ X1) = X0 := superpose step4284 step44
  have step4674 (X0 X1 X2 X3 : G) :  ((((X2 ◇ X2) ◇ (((X3 ◇ X3) ◇ (X1 ◇ X1)) ◇ X3)) ◇ X2) ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ X0)) := superpose step4284 step272
  have step4734 (X0 X1 X2 : G) :  ((((X2 ◇ X2) ◇ (X1 ◇ X1)) ◇ X2) ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ X0)) := superpose step4286 step4674
  have step4751 (X0 X1 : G) :  (((X1 ◇ X1) ◇ X0) ◇ X1) = X0 := superpose step4317 step4633
  have step4757 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step4317 step4618
  have step4796 (X0 X1 : G) :  ((X1 ◇ X1) ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ X0)) := superpose step4286 step4734
  have step4827 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X0) = ((X1 ◇ X1) ◇ X1) := superpose step4757 step4796
  have step4850 (X0 X1 : G) :  (X1 ◇ X1) = ((X0 ◇ X1) ◇ X0) := superpose step4757 step4827
  have step4866 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X0) = X1 := superpose step4757 step4850
  have step5314 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ ((((X1 ◇ X1) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X1 ◇ X1) ◇ X0))) = X1 := superpose step4757 step24
  have step5330 (X0 X1 X2 : G) :  (X1 ◇ X0) = (((X2 ◇ X2) ◇ (X1 ◇ ((X0 ◇ X1) ◇ X0))) ◇ X2) := superpose step4757 step47
  have step5579 (X0 X1 : G) :  (X1 ◇ X0) = (X1 ◇ ((X0 ◇ X1) ◇ X0)) := superpose step4751 step5330
  have step5593 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) = X1 := superpose step4866 step5314
  have step5692 (X0 X1 : G) :  (X1 ◇ X1) = (X1 ◇ X0) := superpose step4866 step5579
  have step5703 (X0 X1 : G) :  (X0 ◇ (X0 ◇ X0)) = X1 := superpose step4757 step5593
  have step5764 (X0 X1 : G) :  (X1 ◇ X0) = X1 := superpose step4757 step5692
  have step5771 (X0 X1 : G) :  (X0 ◇ X0) = X1 := superpose step4757 step5703
  have step5790 (X0 X1 : G) :  X0 = X1 := superpose step5764 step5771
  have step6740 (X0 : G) :  sK0 ≠ (sK1 ◇ ((sK1 ◇ (sK0 ◇ X0)) ◇ X0)) := superpose step5790 step10
  subsumption step6740 step5790


@[equational_result]
theorem Finite.Equation677_and_Equation1249_implies_Equation1241 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation1249 G) : Equation1241 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ (((X1 ◇ X1) ◇ X0) ◇ X1)) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ (sK0 ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step17 (X0 X1 : G) :  (((X1 ◇ X1) ◇ X0) ◇ X1) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose step9 step12
  have step18 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step20 (X0 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ X0) = (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ X0)) := superpose step12 step9
  have step22 (X0 X1 X2 : G) :  (((X0 ◇ X0) ◇ X1) ◇ X0) = (((X2 ◇ X2) ◇ X1) ◇ X2) := superpose step17 step17
  have step24 (X0 X1 : G) :  ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((((X1 ◇ X1) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X1 ◇ X1) ◇ X0))) = X1 := superpose step17 step12
  have step27 (X0 X1 : G) :  ((X1 ◇ X1) ◇ X1) = ((((X0 ◇ X0) ◇ X1) ◇ X0) ◇ ((X1 ◇ (((X0 ◇ X0) ◇ X1) ◇ X0)) ◇ X1)) := superpose step17 step12
  have step30 (X0 X1 : G) :  ((X1 ◇ X1) ◇ X1) = ((((X0 ◇ X0) ◇ X1) ◇ X0) ◇ (X1 ◇ X1)) := superpose step9 step27
  have step44 (X0 X1 : G) :  (X0 ◇ X0) = (((X1 ◇ X1) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ X1) := superpose step12 step22
  have step45 (X0 X1 X2 : G) :  ((X0 ◇ X0) ◇ X0) = (((X1 ◇ X1) ◇ (((X2 ◇ X2) ◇ (X0 ◇ X0)) ◇ X2)) ◇ X1) := superpose step9 step22
  have step47 (X0 X1 X2 : G) :  (((X1 ◇ X1) ◇ (X0 ◇ (((X2 ◇ X2) ◇ X0) ◇ (X2 ◇ X2)))) ◇ X1) = (X0 ◇ X2) := superpose step11 step22
  have step80 (X0 X1 : G) :  ((X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) ◇ (((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)))) ◇ (X1 ◇ (X1 ◇ X0)))) = X1 := superpose step18 step12
  have step83 (X0 X1 : G) :  (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) = (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ ((X1 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) ◇ X1)) := superpose step18 step12
  have step90 (X0 : G) :  ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) = ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) := superpose step12 step30
  have step111 (X0 : G) :  (X0 ◇ X0) = (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) := superpose step20 step11
  have step272 (X0 X1 X2 X3 : G) :  (((X3 ◇ X3) ◇ X2) ◇ X3) = ((((X0 ◇ X0) ◇ (((X1 ◇ X1) ◇ (X2 ◇ X2)) ◇ X1)) ◇ X0) ◇ X2) := superpose step45 step22
  have step1213 (X0 : G) :  (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) = ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ ((X0 ◇ X0) ◇ (((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) := superpose step44 step24
  have step1255 (X0 : G) :  (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) = ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) ◇ ((X0 ◇ X0) ◇ (((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))))) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) := superpose step90 step1213
  have step1266 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) := superpose step111 step1255
  have step4082 (X0 : G) :  (X0 ◇ X0) = ((((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) ◇ (X0 ◇ X0))) ◇ ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) ◇ (X0 ◇ X0)))) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) := superpose step1266 step80
  have step4093 (X0 : G) :  (X0 ◇ X0) = ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) := superpose step12 step4082
  have step4121 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose step12 step4093
  have step4282 (X0 : G) :  ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) = (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) := superpose step4121 step83
  have step4284 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose step4121 step12
  have step4286 (X0 X1 : G) :  (X0 ◇ X0) = (((X1 ◇ X1) ◇ (X0 ◇ X0)) ◇ X1) := superpose step4121 step44
  have step4317 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose step12 step4282
  have step4618 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) = ((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) := superpose step4284 step20
  have step4633 (X0 X1 : G) :  (((X1 ◇ X1) ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0))) ◇ X1) = X0 := superpose step4284 step44
  have step4674 (X0 X1 X2 X3 : G) :  ((((X2 ◇ X2) ◇ (((X3 ◇ X3) ◇ (X1 ◇ X1)) ◇ X3)) ◇ X2) ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ X0)) := superpose step4284 step272
  have step4734 (X0 X1 X2 : G) :  ((((X2 ◇ X2) ◇ (X1 ◇ X1)) ◇ X2) ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ X0)) := superpose step4286 step4674
  have step4751 (X0 X1 : G) :  (((X1 ◇ X1) ◇ X0) ◇ X1) = X0 := superpose step4317 step4633
  have step4757 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step4317 step4618
  have step4796 (X0 X1 : G) :  ((X1 ◇ X1) ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ X0)) := superpose step4286 step4734
  have step4827 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X0) = ((X1 ◇ X1) ◇ X1) := superpose step4757 step4796
  have step4850 (X0 X1 : G) :  (X1 ◇ X1) = ((X0 ◇ X1) ◇ X0) := superpose step4757 step4827
  have step4866 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X0) = X1 := superpose step4757 step4850
  have step5314 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ ((((X1 ◇ X1) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X1 ◇ X1) ◇ X0))) = X1 := superpose step4757 step24
  have step5330 (X0 X1 X2 : G) :  (((X1 ◇ X1) ◇ (X2 ◇ ((X0 ◇ X2) ◇ X0))) ◇ X1) = (X2 ◇ X0) := superpose step4757 step47
  have step5579 (X0 X2 : G) :  (X2 ◇ ((X0 ◇ X2) ◇ X0)) = (X2 ◇ X0) := superpose step4751 step5330
  have step5593 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) = X1 := superpose step4866 step5314
  have step5692 (X0 X2 : G) :  (X2 ◇ X2) = (X2 ◇ X0) := superpose step4866 step5579
  have step5703 (X0 X1 : G) :  (X0 ◇ (X0 ◇ X0)) = X1 := superpose step4757 step5593
  have step5764 (X0 X2 : G) :  (X2 ◇ X0) = X2 := superpose step4757 step5692
  have step5771 (X0 X1 : G) :  (X0 ◇ X0) = X1 := superpose step4757 step5703
  have step5790 (X0 X1 : G) :  X0 = X1 := superpose step5764 step5771
  have step6738 (X0 : G) :  (X0 ◇ (((sK1 ◇ X0) ◇ sK1) ◇ X0)) ≠ X0 := superpose step5790 step10
  subsumption step6738 step5764


@[equational_result]
theorem Finite.Equation677_and_Equation1249_implies_Equation1289 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation1249 G) : Equation1289 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ (((X1 ◇ X1) ◇ X0) ◇ X1)) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ (sK1 ◇ (((sK0 ◇ sK1) ◇ sK1) ◇ sK1)) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step17 (X0 X1 : G) :  (((X1 ◇ X1) ◇ X0) ◇ X1) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose step9 step12
  have step18 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step20 (X0 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ X0) = (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ X0)) := superpose step12 step9
  have step22 (X0 X1 X2 : G) :  (((X0 ◇ X0) ◇ X1) ◇ X0) = (((X2 ◇ X2) ◇ X1) ◇ X2) := superpose step17 step17
  have step24 (X0 X1 : G) :  ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((((X1 ◇ X1) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X1 ◇ X1) ◇ X0))) = X1 := superpose step17 step12
  have step28 (X0 X1 : G) :  ((X1 ◇ X1) ◇ X1) = ((((X0 ◇ X0) ◇ X1) ◇ X0) ◇ ((X1 ◇ (((X0 ◇ X0) ◇ X1) ◇ X0)) ◇ X1)) := superpose step17 step12
  have step30 (X0 X1 : G) :  ((X1 ◇ X1) ◇ X1) = ((((X0 ◇ X0) ◇ X1) ◇ X0) ◇ (X1 ◇ X1)) := superpose step9 step28
  have step44 (X0 X1 : G) :  (X0 ◇ X0) = (((X1 ◇ X1) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ X1) := superpose step12 step22
  have step49 (X0 X1 X2 : G) :  (((X2 ◇ X2) ◇ X1) ◇ X2) = ((((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ X0) ◇ (X1 ◇ X1)) := superpose step22 step22
  have step80 (X0 X1 : G) :  ((X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) ◇ (((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)))) ◇ (X1 ◇ (X1 ◇ X0)))) = X1 := superpose step18 step12
  have step86 (X0 X1 : G) :  (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) = (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ ((X1 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) ◇ X1)) := superpose step18 step12
  have step90 (X0 : G) :  ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) = ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) := superpose step12 step30
  have step111 (X0 : G) :  (X0 ◇ X0) = (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) := superpose step20 step11
  have step445 (X0 X1 : G) :  (((X1 ◇ X1) ◇ X0) ◇ X1) = (((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0)) := superpose step17 step49
  have step1213 (X0 : G) :  (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) = ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ ((X0 ◇ X0) ◇ (((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) := superpose step44 step24
  have step1255 (X0 : G) :  (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) = ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) ◇ ((X0 ◇ X0) ◇ (((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))))) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) := superpose step90 step1213
  have step1266 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) := superpose step111 step1255
  have step4082 (X0 : G) :  (X0 ◇ X0) = ((((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) ◇ (X0 ◇ X0))) ◇ ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) ◇ (X0 ◇ X0)))) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) := superpose step1266 step80
  have step4093 (X0 : G) :  (X0 ◇ X0) = ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) := superpose step12 step4082
  have step4121 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose step12 step4093
  have step4282 (X0 : G) :  ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) = (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) := superpose step4121 step86
  have step4284 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose step4121 step12
  have step4317 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose step12 step4282
  have step4593 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) = ((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) := superpose step4284 step20
  have step4596 (X0 X1 : G) :  (X0 ◇ X0) = ((X1 ◇ ((X1 ◇ X1) ◇ X1)) ◇ (((X0 ◇ X1) ◇ (X1 ◇ ((X1 ◇ X1) ◇ X1))) ◇ (X0 ◇ X1))) := superpose step4284 step24
  have step4630 (X0 : G) :  ((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ ((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0))))) = X0 := superpose step4284 step111
  have step4659 (X0 X1 : G) :  (((X1 ◇ X1) ◇ (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ (X1 ◇ X1))) ◇ (X1 ◇ X1)) = ((X0 ◇ X1) ◇ (X0 ◇ X0)) := superpose step4284 step445
  have step4685 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose step4284 step30
  have step4696 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) := superpose step4284 step445
  have step4747 (X0 X1 : G) :  ((X1 ◇ X1) ◇ (X1 ◇ X1)) = ((X0 ◇ X1) ◇ (X0 ◇ X0)) := superpose step4696 step4659
  have step4769 (X0 : G) :  (X0 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose step4317 step4630
  have step4794 (X0 X1 : G) :  (X0 ◇ X0) = ((X1 ◇ (X1 ◇ (X1 ◇ X1))) ◇ (((X0 ◇ X1) ◇ (X1 ◇ (X1 ◇ (X1 ◇ X1)))) ◇ (X0 ◇ X1))) := superpose step4685 step4596
  have step4795 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step4317 step4593
  have step4828 (X0 X1 : G) :  ((X0 ◇ X1) ◇ (X0 ◇ X0)) = X1 := superpose step4284 step4747
  have step4849 (X0 X1 : G) :  (X0 ◇ X0) = (X1 ◇ (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1))) := superpose step4769 step4794
  have step4870 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X0) = X1 := superpose step4795 step4828
  have step4888 (X0 X1 : G) :  (X1 ◇ (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1))) = X0 := superpose step4795 step4849
  have step4915 (X0 X1 : G) :  (X1 ◇ X1) = X0 := superpose step4870 step4888
  have step6493 (X0 : G) :  sK0 ≠ (X0 ◇ X0) := superpose step4915 step10
  subsumption step6493 step4915


@[equational_result]
theorem Finite.Equation677_and_Equation1249_implies_Equation1454 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation1249 G) : Equation1454 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ (((X1 ◇ X1) ◇ X0) ◇ X1)) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK0))) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step17 (X0 X1 : G) :  (((X1 ◇ X1) ◇ X0) ◇ X1) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose step9 step12
  have step18 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step20 (X0 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ X0) = (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ X0)) := superpose step12 step9
  have step22 (X0 X1 X2 : G) :  (((X0 ◇ X0) ◇ X1) ◇ X0) = (((X2 ◇ X2) ◇ X1) ◇ X2) := superpose step17 step17
  have step24 (X0 X1 : G) :  ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((((X1 ◇ X1) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X1 ◇ X1) ◇ X0))) = X1 := superpose step17 step12
  have step27 (X0 X1 : G) :  ((X1 ◇ X1) ◇ X1) = ((((X0 ◇ X0) ◇ X1) ◇ X0) ◇ ((X1 ◇ (((X0 ◇ X0) ◇ X1) ◇ X0)) ◇ X1)) := superpose step17 step12
  have step30 (X0 X1 : G) :  ((X1 ◇ X1) ◇ X1) = ((((X0 ◇ X0) ◇ X1) ◇ X0) ◇ (X1 ◇ X1)) := superpose step9 step27
  have step44 (X0 X1 : G) :  (X0 ◇ X0) = (((X1 ◇ X1) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ X1) := superpose step12 step22
  have step45 (X0 X1 X2 : G) :  ((X0 ◇ X0) ◇ X0) = (((X1 ◇ X1) ◇ (((X2 ◇ X2) ◇ (X0 ◇ X0)) ◇ X2)) ◇ X1) := superpose step9 step22
  have step47 (X0 X1 X2 : G) :  (((X1 ◇ X1) ◇ (X0 ◇ (((X2 ◇ X2) ◇ X0) ◇ (X2 ◇ X2)))) ◇ X1) = (X0 ◇ X2) := superpose step11 step22
  have step80 (X0 X1 : G) :  ((X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) ◇ (((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)))) ◇ (X1 ◇ (X1 ◇ X0)))) = X1 := superpose step18 step12
  have step83 (X0 X1 : G) :  (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) = (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ ((X1 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) ◇ X1)) := superpose step18 step12
  have step90 (X0 : G) :  ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) = ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) := superpose step12 step30
  have step111 (X0 : G) :  (X0 ◇ X0) = (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) := superpose step20 step11
  have step277 (X0 X1 X2 X3 : G) :  (((X3 ◇ X3) ◇ X2) ◇ X3) = (X2 ◇ (((X0 ◇ X0) ◇ (((X1 ◇ X1) ◇ (X2 ◇ X2)) ◇ X1)) ◇ X0)) := superpose step45 step17
  have step1231 (X0 : G) :  (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) = ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ ((X0 ◇ X0) ◇ (((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) := superpose step44 step24
  have step1273 (X0 : G) :  (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) = ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) ◇ ((X0 ◇ X0) ◇ (((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))))) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) := superpose step90 step1231
  have step1284 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) := superpose step111 step1273
  have step4084 (X0 : G) :  (X0 ◇ X0) = ((((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) ◇ (X0 ◇ X0))) ◇ ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) ◇ (X0 ◇ X0)))) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) := superpose step1284 step80
  have step4095 (X0 : G) :  (X0 ◇ X0) = ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) := superpose step12 step4084
  have step4123 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose step12 step4095
  have step4284 (X0 : G) :  ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) = (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) := superpose step4123 step83
  have step4286 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose step4123 step12
  have step4288 (X0 X1 : G) :  (X0 ◇ X0) = (((X1 ◇ X1) ◇ (X0 ◇ X0)) ◇ X1) := superpose step4123 step44
  have step4319 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose step12 step4284
  have step4620 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) = ((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) := superpose step4286 step20
  have step4635 (X0 X1 : G) :  (((X1 ◇ X1) ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0))) ◇ X1) = X0 := superpose step4286 step44
  have step4679 (X0 X1 X2 X3 : G) :  (X1 ◇ (((X2 ◇ X2) ◇ (((X3 ◇ X3) ◇ (X1 ◇ X1)) ◇ X3)) ◇ X2)) = ((X0 ◇ X1) ◇ (X0 ◇ X0)) := superpose step4286 step277
  have step4735 (X0 X1 X2 : G) :  ((X0 ◇ X1) ◇ (X0 ◇ X0)) = (X1 ◇ (((X2 ◇ X2) ◇ (X1 ◇ X1)) ◇ X2)) := superpose step4288 step4679
  have step4753 (X0 X1 : G) :  (((X1 ◇ X1) ◇ X0) ◇ X1) = X0 := superpose step4319 step4635
  have step4759 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step4319 step4620
  have step4798 (X0 X1 : G) :  (X1 ◇ (X1 ◇ X1)) = ((X0 ◇ X1) ◇ (X0 ◇ X0)) := superpose step4288 step4735
  have step4829 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X0) = (X1 ◇ (X1 ◇ X1)) := superpose step4759 step4798
  have step4852 (X0 X1 : G) :  (X1 ◇ X1) = ((X0 ◇ X1) ◇ X0) := superpose step4759 step4829
  have step4868 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X0) = X1 := superpose step4759 step4852
  have step5316 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ ((((X1 ◇ X1) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X1 ◇ X1) ◇ X0))) = X1 := superpose step4759 step24
  have step5332 (X0 X1 X2 : G) :  (((X1 ◇ X1) ◇ (X2 ◇ ((X0 ◇ X2) ◇ X0))) ◇ X1) = (X2 ◇ X0) := superpose step4759 step47
  have step5581 (X0 X2 : G) :  (X2 ◇ ((X0 ◇ X2) ◇ X0)) = (X2 ◇ X0) := superpose step4753 step5332
  have step5595 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) = X1 := superpose step4868 step5316
  have step5694 (X0 X2 : G) :  (X2 ◇ X2) = (X2 ◇ X0) := superpose step4868 step5581
  have step5705 (X0 X1 : G) :  (X0 ◇ (X0 ◇ X0)) = X1 := superpose step4759 step5595
  have step5766 (X0 X2 : G) :  (X2 ◇ X0) = X2 := superpose step4759 step5694
  have step5773 (X0 X1 : G) :  (X0 ◇ X0) = X1 := superpose step4759 step5705
  have step5792 (X0 X1 : G) :  X0 = X1 := superpose step5766 step5773
  have step6740 (X0 : G) :  ((X0 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ X0))) ≠ X0 := superpose step5792 step10
  subsumption step6740 step5792


@[equational_result]
theorem Finite.Equation677_and_Equation1249_implies_Equation159 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation1249 G) : Equation159 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ (((X1 ◇ X1) ◇ X0) ◇ X1)) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ ((sK0 ◇ sK1) ◇ (sK1 ◇ sK0)) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step17 (X0 X1 : G) :  (((X1 ◇ X1) ◇ X0) ◇ X1) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose step9 step12
  have step18 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step20 (X0 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ X0) = (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ X0)) := superpose step12 step9
  have step22 (X0 X1 X2 : G) :  (((X0 ◇ X0) ◇ X1) ◇ X0) = (((X2 ◇ X2) ◇ X1) ◇ X2) := superpose step17 step17
  have step24 (X0 X1 : G) :  ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((((X1 ◇ X1) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X1 ◇ X1) ◇ X0))) = X1 := superpose step17 step12
  have step27 (X0 X1 : G) :  ((X1 ◇ X1) ◇ X1) = ((((X0 ◇ X0) ◇ X1) ◇ X0) ◇ ((X1 ◇ (((X0 ◇ X0) ◇ X1) ◇ X0)) ◇ X1)) := superpose step17 step12
  have step30 (X0 X1 : G) :  ((X1 ◇ X1) ◇ X1) = ((((X0 ◇ X0) ◇ X1) ◇ X0) ◇ (X1 ◇ X1)) := superpose step9 step27
  have step44 (X0 X1 : G) :  (X0 ◇ X0) = (((X1 ◇ X1) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ X1) := superpose step12 step22
  have step45 (X0 X1 X2 : G) :  ((X0 ◇ X0) ◇ X0) = (((X1 ◇ X1) ◇ (((X2 ◇ X2) ◇ (X0 ◇ X0)) ◇ X2)) ◇ X1) := superpose step9 step22
  have step47 (X0 X1 X2 : G) :  (((X1 ◇ X1) ◇ (X0 ◇ (((X2 ◇ X2) ◇ X0) ◇ (X2 ◇ X2)))) ◇ X1) = (X0 ◇ X2) := superpose step11 step22
  have step80 (X0 X1 : G) :  ((X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) ◇ (((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)))) ◇ (X1 ◇ (X1 ◇ X0)))) = X1 := superpose step18 step12
  have step83 (X0 X1 : G) :  (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) = (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ ((X1 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) ◇ X1)) := superpose step18 step12
  have step90 (X0 : G) :  ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) = ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) := superpose step12 step30
  have step111 (X0 : G) :  (X0 ◇ X0) = (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) := superpose step20 step11
  have step277 (X0 X1 X2 X3 : G) :  (((X3 ◇ X3) ◇ X2) ◇ X3) = (X2 ◇ (((X0 ◇ X0) ◇ (((X1 ◇ X1) ◇ (X2 ◇ X2)) ◇ X1)) ◇ X0)) := superpose step45 step17
  have step1231 (X0 : G) :  (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) = ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ ((X0 ◇ X0) ◇ (((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) := superpose step44 step24
  have step1273 (X0 : G) :  (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) = ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) ◇ ((X0 ◇ X0) ◇ (((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))))) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) := superpose step90 step1231
  have step1284 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) := superpose step111 step1273
  have step4084 (X0 : G) :  (X0 ◇ X0) = ((((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) ◇ (X0 ◇ X0))) ◇ ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) ◇ (X0 ◇ X0)))) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) := superpose step1284 step80
  have step4095 (X0 : G) :  (X0 ◇ X0) = ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) := superpose step12 step4084
  have step4123 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose step12 step4095
  have step4284 (X0 : G) :  ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) = (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) := superpose step4123 step83
  have step4286 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose step4123 step12
  have step4288 (X0 X1 : G) :  (X0 ◇ X0) = (((X1 ◇ X1) ◇ (X0 ◇ X0)) ◇ X1) := superpose step4123 step44
  have step4319 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose step12 step4284
  have step4620 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) = ((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) := superpose step4286 step20
  have step4635 (X0 X1 : G) :  (((X1 ◇ X1) ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0))) ◇ X1) = X0 := superpose step4286 step44
  have step4679 (X0 X1 X2 X3 : G) :  (X1 ◇ (((X2 ◇ X2) ◇ (((X3 ◇ X3) ◇ (X1 ◇ X1)) ◇ X3)) ◇ X2)) = ((X0 ◇ X1) ◇ (X0 ◇ X0)) := superpose step4286 step277
  have step4735 (X0 X1 X2 : G) :  ((X0 ◇ X1) ◇ (X0 ◇ X0)) = (X1 ◇ (((X2 ◇ X2) ◇ (X1 ◇ X1)) ◇ X2)) := superpose step4288 step4679
  have step4753 (X0 X1 : G) :  (((X1 ◇ X1) ◇ X0) ◇ X1) = X0 := superpose step4319 step4635
  have step4759 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step4319 step4620
  have step4798 (X0 X1 : G) :  (X1 ◇ (X1 ◇ X1)) = ((X0 ◇ X1) ◇ (X0 ◇ X0)) := superpose step4288 step4735
  have step4829 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X0) = (X1 ◇ (X1 ◇ X1)) := superpose step4759 step4798
  have step4852 (X0 X1 : G) :  (X1 ◇ X1) = ((X0 ◇ X1) ◇ X0) := superpose step4759 step4829
  have step4868 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X0) = X1 := superpose step4759 step4852
  have step5316 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ ((((X1 ◇ X1) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X1 ◇ X1) ◇ X0))) = X1 := superpose step4759 step24
  have step5332 (X0 X1 X2 : G) :  (((X1 ◇ X1) ◇ (X2 ◇ ((X0 ◇ X2) ◇ X0))) ◇ X1) = (X2 ◇ X0) := superpose step4759 step47
  have step5581 (X0 X2 : G) :  (X2 ◇ ((X0 ◇ X2) ◇ X0)) = (X2 ◇ X0) := superpose step4753 step5332
  have step5595 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) = X1 := superpose step4868 step5316
  have step5694 (X0 X2 : G) :  (X2 ◇ X2) = (X2 ◇ X0) := superpose step4868 step5581
  have step5705 (X0 X1 : G) :  (X0 ◇ (X0 ◇ X0)) = X1 := superpose step4759 step5595
  have step5766 (X0 X2 : G) :  (X2 ◇ X0) = X2 := superpose step4759 step5694
  have step5773 (X0 X1 : G) :  (X0 ◇ X0) = X1 := superpose step4759 step5705
  have step5792 (X0 X1 : G) :  X0 = X1 := superpose step5766 step5773
  have step6738 (X0 : G) :  ((X0 ◇ sK1) ◇ (sK1 ◇ X0)) ≠ X0 := superpose step5792 step10
  subsumption step6738 step5792


@[equational_result]
theorem Finite.Equation677_and_Equation1249_implies_Equation1848 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation1249 G) : Equation1848 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ (((X1 ◇ X1) ◇ X0) ◇ X1)) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ sK1)) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step17 (X0 X1 : G) :  (((X1 ◇ X1) ◇ X0) ◇ X1) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose step9 step12
  have step18 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step20 (X0 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ X0) = (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ X0)) := superpose step12 step9
  have step22 (X0 X1 X2 : G) :  (((X0 ◇ X0) ◇ X1) ◇ X0) = (((X2 ◇ X2) ◇ X1) ◇ X2) := superpose step17 step17
  have step24 (X0 X1 : G) :  ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((((X1 ◇ X1) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X1 ◇ X1) ◇ X0))) = X1 := superpose step17 step12
  have step27 (X0 X1 : G) :  ((X1 ◇ X1) ◇ X1) = ((((X0 ◇ X0) ◇ X1) ◇ X0) ◇ ((X1 ◇ (((X0 ◇ X0) ◇ X1) ◇ X0)) ◇ X1)) := superpose step17 step12
  have step30 (X0 X1 : G) :  ((X1 ◇ X1) ◇ X1) = ((((X0 ◇ X0) ◇ X1) ◇ X0) ◇ (X1 ◇ X1)) := superpose step9 step27
  have step44 (X0 X1 : G) :  (X0 ◇ X0) = (((X1 ◇ X1) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ X1) := superpose step12 step22
  have step45 (X0 X1 X2 : G) :  ((X0 ◇ X0) ◇ X0) = (((X1 ◇ X1) ◇ (((X2 ◇ X2) ◇ (X0 ◇ X0)) ◇ X2)) ◇ X1) := superpose step9 step22
  have step47 (X0 X1 X2 : G) :  (((X1 ◇ X1) ◇ (X0 ◇ (((X2 ◇ X2) ◇ X0) ◇ (X2 ◇ X2)))) ◇ X1) = (X0 ◇ X2) := superpose step11 step22
  have step80 (X0 X1 : G) :  ((X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) ◇ (((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)))) ◇ (X1 ◇ (X1 ◇ X0)))) = X1 := superpose step18 step12
  have step83 (X0 X1 : G) :  (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) = (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ ((X1 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) ◇ X1)) := superpose step18 step12
  have step90 (X0 : G) :  ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) = ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) := superpose step12 step30
  have step111 (X0 : G) :  (X0 ◇ X0) = (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) := superpose step20 step11
  have step277 (X0 X1 X2 X3 : G) :  (((X3 ◇ X3) ◇ X2) ◇ X3) = (X2 ◇ (((X0 ◇ X0) ◇ (((X1 ◇ X1) ◇ (X2 ◇ X2)) ◇ X1)) ◇ X0)) := superpose step45 step17
  have step1231 (X0 : G) :  (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) = ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ ((X0 ◇ X0) ◇ (((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) := superpose step44 step24
  have step1273 (X0 : G) :  (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) = ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) ◇ ((X0 ◇ X0) ◇ (((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))))) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) := superpose step90 step1231
  have step1284 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) := superpose step111 step1273
  have step4084 (X0 : G) :  (X0 ◇ X0) = ((((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) ◇ (X0 ◇ X0))) ◇ ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) ◇ (X0 ◇ X0)))) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) := superpose step1284 step80
  have step4095 (X0 : G) :  (X0 ◇ X0) = ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) := superpose step12 step4084
  have step4123 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose step12 step4095
  have step4284 (X0 : G) :  ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) = (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) := superpose step4123 step83
  have step4286 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose step4123 step12
  have step4288 (X0 X1 : G) :  (X0 ◇ X0) = (((X1 ◇ X1) ◇ (X0 ◇ X0)) ◇ X1) := superpose step4123 step44
  have step4319 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose step12 step4284
  have step4620 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) = ((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) := superpose step4286 step20
  have step4635 (X0 X1 : G) :  (((X1 ◇ X1) ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0))) ◇ X1) = X0 := superpose step4286 step44
  have step4679 (X0 X1 X2 X3 : G) :  (X1 ◇ (((X2 ◇ X2) ◇ (((X3 ◇ X3) ◇ (X1 ◇ X1)) ◇ X3)) ◇ X2)) = ((X0 ◇ X1) ◇ (X0 ◇ X0)) := superpose step4286 step277
  have step4735 (X0 X1 X2 : G) :  ((X0 ◇ X1) ◇ (X0 ◇ X0)) = (X1 ◇ (((X2 ◇ X2) ◇ (X1 ◇ X1)) ◇ X2)) := superpose step4288 step4679
  have step4753 (X0 X1 : G) :  (((X1 ◇ X1) ◇ X0) ◇ X1) = X0 := superpose step4319 step4635
  have step4759 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step4319 step4620
  have step4798 (X0 X1 : G) :  (X1 ◇ (X1 ◇ X1)) = ((X0 ◇ X1) ◇ (X0 ◇ X0)) := superpose step4288 step4735
  have step4829 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X0) = (X1 ◇ (X1 ◇ X1)) := superpose step4759 step4798
  have step4852 (X0 X1 : G) :  (X1 ◇ X1) = ((X0 ◇ X1) ◇ X0) := superpose step4759 step4829
  have step4868 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X0) = X1 := superpose step4759 step4852
  have step5316 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ ((((X1 ◇ X1) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X1 ◇ X1) ◇ X0))) = X1 := superpose step4759 step24
  have step5332 (X0 X1 X2 : G) :  (((X1 ◇ X1) ◇ (X2 ◇ ((X0 ◇ X2) ◇ X0))) ◇ X1) = (X2 ◇ X0) := superpose step4759 step47
  have step5581 (X0 X2 : G) :  (X2 ◇ ((X0 ◇ X2) ◇ X0)) = (X2 ◇ X0) := superpose step4753 step5332
  have step5595 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) = X1 := superpose step4868 step5316
  have step5694 (X0 X2 : G) :  (X2 ◇ X2) = (X2 ◇ X0) := superpose step4868 step5581
  have step5705 (X0 X1 : G) :  (X0 ◇ (X0 ◇ X0)) = X1 := superpose step4759 step5595
  have step5766 (X0 X2 : G) :  (X2 ◇ X0) = X2 := superpose step4759 step5694
  have step5773 (X0 X1 : G) :  (X0 ◇ X0) = X1 := superpose step4759 step5705
  have step5792 (X0 X1 : G) :  X0 = X1 := superpose step5766 step5773
  have step6740 (X0 : G) :  sK0 ≠ ((sK0 ◇ (X0 ◇ sK0)) ◇ (sK0 ◇ X0)) := superpose step5792 step10
  subsumption step6740 step5792


@[equational_result]
theorem Finite.Equation677_and_Equation1249_implies_Equation1897 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation1249 G) : Equation1897 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ (((X1 ◇ X1) ◇ X0) ◇ X1)) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ sK0)) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step17 (X0 X1 : G) :  (((X1 ◇ X1) ◇ X0) ◇ X1) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose step9 step12
  have step18 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step20 (X0 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ X0) = (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ X0)) := superpose step12 step9
  have step22 (X0 X1 X2 : G) :  (((X0 ◇ X0) ◇ X1) ◇ X0) = (((X2 ◇ X2) ◇ X1) ◇ X2) := superpose step17 step17
  have step24 (X0 X1 : G) :  ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((((X1 ◇ X1) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X1 ◇ X1) ◇ X0))) = X1 := superpose step17 step12
  have step27 (X0 X1 : G) :  ((X1 ◇ X1) ◇ X1) = ((((X0 ◇ X0) ◇ X1) ◇ X0) ◇ ((X1 ◇ (((X0 ◇ X0) ◇ X1) ◇ X0)) ◇ X1)) := superpose step17 step12
  have step30 (X0 X1 : G) :  ((X1 ◇ X1) ◇ X1) = ((((X0 ◇ X0) ◇ X1) ◇ X0) ◇ (X1 ◇ X1)) := superpose step9 step27
  have step44 (X0 X1 : G) :  (X0 ◇ X0) = (((X1 ◇ X1) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ X1) := superpose step12 step22
  have step45 (X0 X1 X2 : G) :  ((X0 ◇ X0) ◇ X0) = (((X1 ◇ X1) ◇ (((X2 ◇ X2) ◇ (X0 ◇ X0)) ◇ X2)) ◇ X1) := superpose step9 step22
  have step47 (X0 X1 X2 : G) :  (((X1 ◇ X1) ◇ (X0 ◇ (((X2 ◇ X2) ◇ X0) ◇ (X2 ◇ X2)))) ◇ X1) = (X0 ◇ X2) := superpose step11 step22
  have step80 (X0 X1 : G) :  ((X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) ◇ (((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)))) ◇ (X1 ◇ (X1 ◇ X0)))) = X1 := superpose step18 step12
  have step83 (X0 X1 : G) :  (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) = (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ ((X1 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) ◇ X1)) := superpose step18 step12
  have step90 (X0 : G) :  ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) = ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) := superpose step12 step30
  have step111 (X0 : G) :  (X0 ◇ X0) = (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) := superpose step20 step11
  have step277 (X0 X1 X2 X3 : G) :  (((X3 ◇ X3) ◇ X2) ◇ X3) = (X2 ◇ (((X0 ◇ X0) ◇ (((X1 ◇ X1) ◇ (X2 ◇ X2)) ◇ X1)) ◇ X0)) := superpose step45 step17
  have step1231 (X0 : G) :  (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) = ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ ((X0 ◇ X0) ◇ (((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) := superpose step44 step24
  have step1273 (X0 : G) :  (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) = ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) ◇ ((X0 ◇ X0) ◇ (((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))))) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) := superpose step90 step1231
  have step1284 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) := superpose step111 step1273
  have step4084 (X0 : G) :  (X0 ◇ X0) = ((((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) ◇ (X0 ◇ X0))) ◇ ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) ◇ (X0 ◇ X0)))) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) := superpose step1284 step80
  have step4095 (X0 : G) :  (X0 ◇ X0) = ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) := superpose step12 step4084
  have step4123 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose step12 step4095
  have step4284 (X0 : G) :  ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) = (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) := superpose step4123 step83
  have step4286 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose step4123 step12
  have step4288 (X0 X1 : G) :  (X0 ◇ X0) = (((X1 ◇ X1) ◇ (X0 ◇ X0)) ◇ X1) := superpose step4123 step44
  have step4319 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose step12 step4284
  have step4620 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) = ((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) := superpose step4286 step20
  have step4635 (X0 X1 : G) :  (((X1 ◇ X1) ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0))) ◇ X1) = X0 := superpose step4286 step44
  have step4679 (X0 X1 X2 X3 : G) :  (X1 ◇ (((X2 ◇ X2) ◇ (((X3 ◇ X3) ◇ (X1 ◇ X1)) ◇ X3)) ◇ X2)) = ((X0 ◇ X1) ◇ (X0 ◇ X0)) := superpose step4286 step277
  have step4735 (X0 X1 X2 : G) :  ((X0 ◇ X1) ◇ (X0 ◇ X0)) = (X1 ◇ (((X2 ◇ X2) ◇ (X1 ◇ X1)) ◇ X2)) := superpose step4288 step4679
  have step4753 (X0 X1 : G) :  (((X1 ◇ X1) ◇ X0) ◇ X1) = X0 := superpose step4319 step4635
  have step4759 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step4319 step4620
  have step4798 (X0 X1 : G) :  (X1 ◇ (X1 ◇ X1)) = ((X0 ◇ X1) ◇ (X0 ◇ X0)) := superpose step4288 step4735
  have step4829 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X0) = (X1 ◇ (X1 ◇ X1)) := superpose step4759 step4798
  have step4852 (X0 X1 : G) :  (X1 ◇ X1) = ((X0 ◇ X1) ◇ X0) := superpose step4759 step4829
  have step4868 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X0) = X1 := superpose step4759 step4852
  have step5316 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ ((((X1 ◇ X1) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X1 ◇ X1) ◇ X0))) = X1 := superpose step4759 step24
  have step5332 (X0 X1 X2 : G) :  (((X1 ◇ X1) ◇ (X2 ◇ ((X0 ◇ X2) ◇ X0))) ◇ X1) = (X2 ◇ X0) := superpose step4759 step47
  have step5581 (X0 X2 : G) :  (X2 ◇ ((X0 ◇ X2) ◇ X0)) = (X2 ◇ X0) := superpose step4753 step5332
  have step5595 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) = X1 := superpose step4868 step5316
  have step5694 (X0 X2 : G) :  (X2 ◇ X2) = (X2 ◇ X0) := superpose step4868 step5581
  have step5705 (X0 X1 : G) :  (X0 ◇ (X0 ◇ X0)) = X1 := superpose step4759 step5595
  have step5766 (X0 X2 : G) :  (X2 ◇ X0) = X2 := superpose step4759 step5694
  have step5773 (X0 X1 : G) :  (X0 ◇ X0) = X1 := superpose step4759 step5705
  have step5792 (X0 X1 : G) :  X0 = X1 := superpose step5766 step5773
  have step6740 (X0 : G) :  ((sK1 ◇ (X0 ◇ sK1)) ◇ (sK1 ◇ X0)) ≠ X0 := superpose step5792 step10
  subsumption step6740 step5792


@[equational_result]
theorem Finite.Equation677_and_Equation1249_implies_Equation1922 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation1249 G) : Equation1922 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ (((X1 ◇ X1) ◇ X0) ◇ X1)) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ sK1)) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step17 (X0 X1 : G) :  (((X1 ◇ X1) ◇ X0) ◇ X1) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose step9 step12
  have step18 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step20 (X0 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ X0) = (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ X0)) := superpose step12 step9
  have step22 (X0 X1 X2 : G) :  (((X0 ◇ X0) ◇ X1) ◇ X0) = (((X2 ◇ X2) ◇ X1) ◇ X2) := superpose step17 step17
  have step24 (X0 X1 : G) :  ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((((X1 ◇ X1) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X1 ◇ X1) ◇ X0))) = X1 := superpose step17 step12
  have step27 (X0 X1 : G) :  ((X1 ◇ X1) ◇ X1) = ((((X0 ◇ X0) ◇ X1) ◇ X0) ◇ ((X1 ◇ (((X0 ◇ X0) ◇ X1) ◇ X0)) ◇ X1)) := superpose step17 step12
  have step30 (X0 X1 : G) :  ((X1 ◇ X1) ◇ X1) = ((((X0 ◇ X0) ◇ X1) ◇ X0) ◇ (X1 ◇ X1)) := superpose step9 step27
  have step44 (X0 X1 : G) :  (X0 ◇ X0) = (((X1 ◇ X1) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ X1) := superpose step12 step22
  have step45 (X0 X1 X2 : G) :  ((X0 ◇ X0) ◇ X0) = (((X1 ◇ X1) ◇ (((X2 ◇ X2) ◇ (X0 ◇ X0)) ◇ X2)) ◇ X1) := superpose step9 step22
  have step47 (X0 X1 X2 : G) :  (((X1 ◇ X1) ◇ (X0 ◇ (((X2 ◇ X2) ◇ X0) ◇ (X2 ◇ X2)))) ◇ X1) = (X0 ◇ X2) := superpose step11 step22
  have step80 (X0 X1 : G) :  ((X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) ◇ (((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)))) ◇ (X1 ◇ (X1 ◇ X0)))) = X1 := superpose step18 step12
  have step83 (X0 X1 : G) :  (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) = (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ ((X1 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) ◇ X1)) := superpose step18 step12
  have step90 (X0 : G) :  ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) = ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) := superpose step12 step30
  have step111 (X0 : G) :  (X0 ◇ X0) = (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) := superpose step20 step11
  have step277 (X0 X1 X2 X3 : G) :  (((X3 ◇ X3) ◇ X2) ◇ X3) = (X2 ◇ (((X0 ◇ X0) ◇ (((X1 ◇ X1) ◇ (X2 ◇ X2)) ◇ X1)) ◇ X0)) := superpose step45 step17
  have step1231 (X0 : G) :  (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) = ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ ((X0 ◇ X0) ◇ (((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) := superpose step44 step24
  have step1273 (X0 : G) :  (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) = ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) ◇ ((X0 ◇ X0) ◇ (((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))))) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) := superpose step90 step1231
  have step1284 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) := superpose step111 step1273
  have step4084 (X0 : G) :  (X0 ◇ X0) = ((((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) ◇ (X0 ◇ X0))) ◇ ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) ◇ (X0 ◇ X0)))) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) := superpose step1284 step80
  have step4095 (X0 : G) :  (X0 ◇ X0) = ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) := superpose step12 step4084
  have step4123 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose step12 step4095
  have step4284 (X0 : G) :  ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) = (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) := superpose step4123 step83
  have step4286 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose step4123 step12
  have step4288 (X0 X1 : G) :  (X0 ◇ X0) = (((X1 ◇ X1) ◇ (X0 ◇ X0)) ◇ X1) := superpose step4123 step44
  have step4319 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose step12 step4284
  have step4620 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) = ((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) := superpose step4286 step20
  have step4635 (X0 X1 : G) :  (((X1 ◇ X1) ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0))) ◇ X1) = X0 := superpose step4286 step44
  have step4679 (X0 X1 X2 X3 : G) :  (X1 ◇ (((X2 ◇ X2) ◇ (((X3 ◇ X3) ◇ (X1 ◇ X1)) ◇ X3)) ◇ X2)) = ((X0 ◇ X1) ◇ (X0 ◇ X0)) := superpose step4286 step277
  have step4735 (X0 X1 X2 : G) :  ((X0 ◇ X1) ◇ (X0 ◇ X0)) = (X1 ◇ (((X2 ◇ X2) ◇ (X1 ◇ X1)) ◇ X2)) := superpose step4288 step4679
  have step4753 (X0 X1 : G) :  (((X1 ◇ X1) ◇ X0) ◇ X1) = X0 := superpose step4319 step4635
  have step4759 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step4319 step4620
  have step4798 (X0 X1 : G) :  (X1 ◇ (X1 ◇ X1)) = ((X0 ◇ X1) ◇ (X0 ◇ X0)) := superpose step4288 step4735
  have step4829 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X0) = (X1 ◇ (X1 ◇ X1)) := superpose step4759 step4798
  have step4852 (X0 X1 : G) :  (X1 ◇ X1) = ((X0 ◇ X1) ◇ X0) := superpose step4759 step4829
  have step4868 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X0) = X1 := superpose step4759 step4852
  have step5316 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ ((((X1 ◇ X1) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X1 ◇ X1) ◇ X0))) = X1 := superpose step4759 step24
  have step5332 (X0 X1 X2 : G) :  (((X1 ◇ X1) ◇ (X2 ◇ ((X0 ◇ X2) ◇ X0))) ◇ X1) = (X2 ◇ X0) := superpose step4759 step47
  have step5581 (X0 X2 : G) :  (X2 ◇ ((X0 ◇ X2) ◇ X0)) = (X2 ◇ X0) := superpose step4753 step5332
  have step5595 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) = X1 := superpose step4868 step5316
  have step5694 (X0 X2 : G) :  (X2 ◇ X2) = (X2 ◇ X0) := superpose step4868 step5581
  have step5705 (X0 X1 : G) :  (X0 ◇ (X0 ◇ X0)) = X1 := superpose step4759 step5595
  have step5766 (X0 X2 : G) :  (X2 ◇ X0) = X2 := superpose step4759 step5694
  have step5773 (X0 X1 : G) :  (X0 ◇ X0) = X1 := superpose step4759 step5705
  have step5792 (X0 X1 : G) :  X0 = X1 := superpose step5766 step5773
  have step6740 (X0 : G) :  sK0 ≠ ((X0 ◇ (X0 ◇ sK0)) ◇ (sK0 ◇ X0)) := superpose step5792 step10
  subsumption step6740 step5792


@[equational_result]
theorem Finite.Equation677_and_Equation1249_implies_Equation2063 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation1249 G) : Equation2063 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ (((X1 ◇ X1) ◇ X0) ◇ X1)) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ (((sK0 ◇ sK1) ◇ sK1) ◇ (sK1 ◇ sK0)) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step17 (X0 X1 : G) :  (((X1 ◇ X1) ◇ X0) ◇ X1) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose step9 step12
  have step18 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step20 (X0 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ X0) = (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ X0)) := superpose step12 step9
  have step22 (X0 X1 X2 : G) :  (((X0 ◇ X0) ◇ X1) ◇ X0) = (((X2 ◇ X2) ◇ X1) ◇ X2) := superpose step17 step17
  have step24 (X0 X1 : G) :  ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((((X1 ◇ X1) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X1 ◇ X1) ◇ X0))) = X1 := superpose step17 step12
  have step28 (X0 X1 : G) :  ((X1 ◇ X1) ◇ X1) = ((((X0 ◇ X0) ◇ X1) ◇ X0) ◇ ((X1 ◇ (((X0 ◇ X0) ◇ X1) ◇ X0)) ◇ X1)) := superpose step17 step12
  have step30 (X0 X1 : G) :  ((X1 ◇ X1) ◇ X1) = ((((X0 ◇ X0) ◇ X1) ◇ X0) ◇ (X1 ◇ X1)) := superpose step9 step28
  have step44 (X0 X1 : G) :  (X0 ◇ X0) = (((X1 ◇ X1) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ X1) := superpose step12 step22
  have step49 (X0 X1 X2 : G) :  (((X2 ◇ X2) ◇ X1) ◇ X2) = ((((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ X0) ◇ (X1 ◇ X1)) := superpose step22 step22
  have step80 (X0 X1 : G) :  ((X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) ◇ (((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)))) ◇ (X1 ◇ (X1 ◇ X0)))) = X1 := superpose step18 step12
  have step86 (X0 X1 : G) :  (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) = (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ ((X1 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) ◇ X1)) := superpose step18 step12
  have step90 (X0 : G) :  ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) = ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) := superpose step12 step30
  have step111 (X0 : G) :  (X0 ◇ X0) = (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) := superpose step20 step11
  have step445 (X0 X1 : G) :  (((X1 ◇ X1) ◇ X0) ◇ X1) = (((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0)) := superpose step17 step49
  have step1213 (X0 : G) :  (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) = ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ ((X0 ◇ X0) ◇ (((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) := superpose step44 step24
  have step1255 (X0 : G) :  (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) = ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) ◇ ((X0 ◇ X0) ◇ (((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))))) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) := superpose step90 step1213
  have step1266 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) := superpose step111 step1255
  have step4082 (X0 : G) :  (X0 ◇ X0) = ((((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) ◇ (X0 ◇ X0))) ◇ ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) ◇ (X0 ◇ X0)))) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) := superpose step1266 step80
  have step4093 (X0 : G) :  (X0 ◇ X0) = ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) := superpose step12 step4082
  have step4121 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose step12 step4093
  have step4282 (X0 : G) :  ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) = (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) := superpose step4121 step86
  have step4284 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose step4121 step12
  have step4317 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose step12 step4282
  have step4593 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) = ((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) := superpose step4284 step20
  have step4596 (X0 X1 : G) :  (X0 ◇ X0) = ((X1 ◇ ((X1 ◇ X1) ◇ X1)) ◇ (((X0 ◇ X1) ◇ (X1 ◇ ((X1 ◇ X1) ◇ X1))) ◇ (X0 ◇ X1))) := superpose step4284 step24
  have step4630 (X0 : G) :  ((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ ((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0))))) = X0 := superpose step4284 step111
  have step4659 (X0 X1 : G) :  (((X1 ◇ X1) ◇ (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ (X1 ◇ X1))) ◇ (X1 ◇ X1)) = ((X0 ◇ X1) ◇ (X0 ◇ X0)) := superpose step4284 step445
  have step4685 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose step4284 step30
  have step4696 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) := superpose step4284 step445
  have step4747 (X0 X1 : G) :  ((X1 ◇ X1) ◇ (X1 ◇ X1)) = ((X0 ◇ X1) ◇ (X0 ◇ X0)) := superpose step4696 step4659
  have step4769 (X0 : G) :  (X0 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose step4317 step4630
  have step4794 (X0 X1 : G) :  (X0 ◇ X0) = ((X1 ◇ (X1 ◇ (X1 ◇ X1))) ◇ (((X0 ◇ X1) ◇ (X1 ◇ (X1 ◇ (X1 ◇ X1)))) ◇ (X0 ◇ X1))) := superpose step4685 step4596
  have step4795 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step4317 step4593
  have step4828 (X0 X1 : G) :  ((X0 ◇ X1) ◇ (X0 ◇ X0)) = X1 := superpose step4284 step4747
  have step4849 (X0 X1 : G) :  (X0 ◇ X0) = (X1 ◇ (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1))) := superpose step4769 step4794
  have step4870 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X0) = X1 := superpose step4795 step4828
  have step4888 (X0 X1 : G) :  (X1 ◇ (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1))) = X0 := superpose step4795 step4849
  have step4915 (X0 X1 : G) :  (X1 ◇ X1) = X0 := superpose step4870 step4888
  have step6481 (X0 : G) :  sK0 ≠ (X0 ◇ X0) := superpose step4915 step10
  subsumption step6481 step4915


@[equational_result]
theorem Finite.Equation677_and_Equation1249_implies_Equation2088 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation1249 G) : Equation2088 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ (((X1 ◇ X1) ◇ X0) ◇ X1)) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ (((sK1 ◇ sK0) ◇ sK0) ◇ (sK0 ◇ sK1)) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step17 (X0 X1 : G) :  (((X1 ◇ X1) ◇ X0) ◇ X1) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose step9 step12
  have step18 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step20 (X0 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ X0) = (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ X0)) := superpose step12 step9
  have step22 (X0 X1 X2 : G) :  (((X0 ◇ X0) ◇ X1) ◇ X0) = (((X2 ◇ X2) ◇ X1) ◇ X2) := superpose step17 step17
  have step24 (X0 X1 : G) :  ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((((X1 ◇ X1) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X1 ◇ X1) ◇ X0))) = X1 := superpose step17 step12
  have step28 (X0 X1 : G) :  ((X1 ◇ X1) ◇ X1) = ((((X0 ◇ X0) ◇ X1) ◇ X0) ◇ ((X1 ◇ (((X0 ◇ X0) ◇ X1) ◇ X0)) ◇ X1)) := superpose step17 step12
  have step30 (X0 X1 : G) :  ((X1 ◇ X1) ◇ X1) = ((((X0 ◇ X0) ◇ X1) ◇ X0) ◇ (X1 ◇ X1)) := superpose step9 step28
  have step44 (X0 X1 : G) :  (X0 ◇ X0) = (((X1 ◇ X1) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ X1) := superpose step12 step22
  have step49 (X0 X1 X2 : G) :  (((X2 ◇ X2) ◇ X1) ◇ X2) = ((((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ X0) ◇ (X1 ◇ X1)) := superpose step22 step22
  have step80 (X0 X1 : G) :  ((X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) ◇ (((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)))) ◇ (X1 ◇ (X1 ◇ X0)))) = X1 := superpose step18 step12
  have step86 (X0 X1 : G) :  (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) = (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ ((X1 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) ◇ X1)) := superpose step18 step12
  have step90 (X0 : G) :  ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) = ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) := superpose step12 step30
  have step111 (X0 : G) :  (X0 ◇ X0) = (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) := superpose step20 step11
  have step445 (X0 X1 : G) :  (((X1 ◇ X1) ◇ X0) ◇ X1) = (((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0)) := superpose step17 step49
  have step1213 (X0 : G) :  (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) = ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ ((X0 ◇ X0) ◇ (((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) := superpose step44 step24
  have step1255 (X0 : G) :  (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) = ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) ◇ ((X0 ◇ X0) ◇ (((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))))) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) := superpose step90 step1213
  have step1266 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) := superpose step111 step1255
  have step4082 (X0 : G) :  (X0 ◇ X0) = ((((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) ◇ (X0 ◇ X0))) ◇ ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) ◇ (X0 ◇ X0)))) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) := superpose step1266 step80
  have step4093 (X0 : G) :  (X0 ◇ X0) = ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) := superpose step12 step4082
  have step4121 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose step12 step4093
  have step4282 (X0 : G) :  ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) = (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) := superpose step4121 step86
  have step4284 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose step4121 step12
  have step4317 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose step12 step4282
  have step4593 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) = ((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) := superpose step4284 step20
  have step4596 (X0 X1 : G) :  (X0 ◇ X0) = ((X1 ◇ ((X1 ◇ X1) ◇ X1)) ◇ (((X0 ◇ X1) ◇ (X1 ◇ ((X1 ◇ X1) ◇ X1))) ◇ (X0 ◇ X1))) := superpose step4284 step24
  have step4630 (X0 : G) :  ((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ ((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0))))) = X0 := superpose step4284 step111
  have step4659 (X0 X1 : G) :  (((X1 ◇ X1) ◇ (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ (X1 ◇ X1))) ◇ (X1 ◇ X1)) = ((X0 ◇ X1) ◇ (X0 ◇ X0)) := superpose step4284 step445
  have step4685 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose step4284 step30
  have step4696 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) := superpose step4284 step445
  have step4747 (X0 X1 : G) :  ((X1 ◇ X1) ◇ (X1 ◇ X1)) = ((X0 ◇ X1) ◇ (X0 ◇ X0)) := superpose step4696 step4659
  have step4769 (X0 : G) :  (X0 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose step4317 step4630
  have step4794 (X0 X1 : G) :  (X0 ◇ X0) = ((X1 ◇ (X1 ◇ (X1 ◇ X1))) ◇ (((X0 ◇ X1) ◇ (X1 ◇ (X1 ◇ (X1 ◇ X1)))) ◇ (X0 ◇ X1))) := superpose step4685 step4596
  have step4795 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step4317 step4593
  have step4828 (X0 X1 : G) :  ((X0 ◇ X1) ◇ (X0 ◇ X0)) = X1 := superpose step4284 step4747
  have step4849 (X0 X1 : G) :  (X0 ◇ X0) = (X1 ◇ (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1))) := superpose step4769 step4794
  have step4870 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X0) = X1 := superpose step4795 step4828
  have step4888 (X0 X1 : G) :  (X1 ◇ (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1))) = X0 := superpose step4795 step4849
  have step4915 (X0 X1 : G) :  (X1 ◇ X1) = X0 := superpose step4870 step4888
  have step6481 (X0 : G) :  sK0 ≠ (X0 ◇ X0) := superpose step4915 step10
  subsumption step6481 step4915


@[equational_result]
theorem Finite.Equation677_and_Equation1249_implies_Equation2241 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation1249 G) : Equation2241 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ (((X1 ◇ X1) ◇ X0) ◇ X1)) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ sK1) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step17 (X0 X1 : G) :  (((X1 ◇ X1) ◇ X0) ◇ X1) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose step9 step12
  have step18 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step20 (X0 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ X0) = (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ X0)) := superpose step12 step9
  have step22 (X0 X1 X2 : G) :  (((X0 ◇ X0) ◇ X1) ◇ X0) = (((X2 ◇ X2) ◇ X1) ◇ X2) := superpose step17 step17
  have step24 (X0 X1 : G) :  ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((((X1 ◇ X1) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X1 ◇ X1) ◇ X0))) = X1 := superpose step17 step12
  have step28 (X0 X1 : G) :  ((X1 ◇ X1) ◇ X1) = ((((X0 ◇ X0) ◇ X1) ◇ X0) ◇ ((X1 ◇ (((X0 ◇ X0) ◇ X1) ◇ X0)) ◇ X1)) := superpose step17 step12
  have step30 (X0 X1 : G) :  ((X1 ◇ X1) ◇ X1) = ((((X0 ◇ X0) ◇ X1) ◇ X0) ◇ (X1 ◇ X1)) := superpose step9 step28
  have step44 (X0 X1 : G) :  (X0 ◇ X0) = (((X1 ◇ X1) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ X1) := superpose step12 step22
  have step45 (X0 X1 X2 : G) :  ((X0 ◇ X0) ◇ X0) = (((X1 ◇ X1) ◇ (((X2 ◇ X2) ◇ (X0 ◇ X0)) ◇ X2)) ◇ X1) := superpose step9 step22
  have step47 (X0 X1 X2 : G) :  (((X1 ◇ X1) ◇ (X0 ◇ (((X2 ◇ X2) ◇ X0) ◇ (X2 ◇ X2)))) ◇ X1) = (X0 ◇ X2) := superpose step11 step22
  have step80 (X0 X1 : G) :  ((X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) ◇ (((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)))) ◇ (X1 ◇ (X1 ◇ X0)))) = X1 := superpose step18 step12
  have step86 (X0 X1 : G) :  (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) = (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ ((X1 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) ◇ X1)) := superpose step18 step12
  have step90 (X0 : G) :  ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) = ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) := superpose step12 step30
  have step111 (X0 : G) :  (X0 ◇ X0) = (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) := superpose step20 step11
  have step272 (X0 X1 X2 X3 : G) :  (((X3 ◇ X3) ◇ X2) ◇ X3) = ((((X0 ◇ X0) ◇ (((X1 ◇ X1) ◇ (X2 ◇ X2)) ◇ X1)) ◇ X0) ◇ X2) := superpose step45 step22
  have step1213 (X0 : G) :  (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) = ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ ((X0 ◇ X0) ◇ (((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) := superpose step44 step24
  have step1255 (X0 : G) :  (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) = ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) ◇ ((X0 ◇ X0) ◇ (((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))))) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) := superpose step90 step1213
  have step1266 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) := superpose step111 step1255
  have step4082 (X0 : G) :  (X0 ◇ X0) = ((((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) ◇ (X0 ◇ X0))) ◇ ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) ◇ (X0 ◇ X0)))) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) := superpose step1266 step80
  have step4093 (X0 : G) :  (X0 ◇ X0) = ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) := superpose step12 step4082
  have step4121 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose step12 step4093
  have step4282 (X0 : G) :  ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) = (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) := superpose step4121 step86
  have step4284 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose step4121 step12
  have step4286 (X0 X1 : G) :  (X0 ◇ X0) = (((X1 ◇ X1) ◇ (X0 ◇ X0)) ◇ X1) := superpose step4121 step44
  have step4317 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose step12 step4282
  have step4618 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) = ((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) := superpose step4284 step20
  have step4633 (X0 X1 : G) :  (((X1 ◇ X1) ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0))) ◇ X1) = X0 := superpose step4284 step44
  have step4674 (X0 X1 X2 X3 : G) :  ((((X2 ◇ X2) ◇ (((X3 ◇ X3) ◇ (X1 ◇ X1)) ◇ X3)) ◇ X2) ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ X0)) := superpose step4284 step272
  have step4734 (X0 X1 X2 : G) :  ((((X2 ◇ X2) ◇ (X1 ◇ X1)) ◇ X2) ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ X0)) := superpose step4286 step4674
  have step4751 (X0 X1 : G) :  (((X1 ◇ X1) ◇ X0) ◇ X1) = X0 := superpose step4317 step4633
  have step4757 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step4317 step4618
  have step4796 (X0 X1 : G) :  ((X1 ◇ X1) ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ X0)) := superpose step4286 step4734
  have step4827 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X0) = ((X1 ◇ X1) ◇ X1) := superpose step4757 step4796
  have step4850 (X0 X1 : G) :  (X1 ◇ X1) = ((X0 ◇ X1) ◇ X0) := superpose step4757 step4827
  have step4866 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X0) = X1 := superpose step4757 step4850
  have step5365 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ ((((X1 ◇ X1) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X1 ◇ X1) ◇ X0))) = X1 := superpose step4757 step24
  have step5381 (X0 X1 X2 : G) :  (((X1 ◇ X1) ◇ (X2 ◇ ((X0 ◇ X2) ◇ X0))) ◇ X1) = (X2 ◇ X0) := superpose step4757 step47
  have step5534 (X0 X2 : G) :  (X2 ◇ ((X0 ◇ X2) ◇ X0)) = (X2 ◇ X0) := superpose step4751 step5381
  have step5548 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) = X1 := superpose step4866 step5365
  have step5664 (X0 X2 : G) :  (X2 ◇ X2) = (X2 ◇ X0) := superpose step4866 step5534
  have step5675 (X0 X1 : G) :  (X0 ◇ (X0 ◇ X0)) = X1 := superpose step4757 step5548
  have step5751 (X0 X2 : G) :  (X2 ◇ X0) = X2 := superpose step4757 step5664
  have step5758 (X0 X1 : G) :  (X0 ◇ X0) = X1 := superpose step4757 step5675
  have step5784 (X0 X1 : G) :  X0 = X1 := superpose step5751 step5758
  have step6734 (X0 : G) :  sK0 ≠ ((sK0 ◇ (sK0 ◇ (sK0 ◇ X0))) ◇ X0) := superpose step5784 step10
  subsumption step6734 step5784


@[equational_result]
theorem Finite.Equation677_and_Equation1249_implies_Equation2294 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation1249 G) : Equation2294 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ (((X1 ◇ X1) ◇ X0) ◇ X1)) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ sK1) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step17 (X0 X1 : G) :  (((X1 ◇ X1) ◇ X0) ◇ X1) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose step9 step12
  have step18 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step20 (X0 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ X0) = (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ X0)) := superpose step12 step9
  have step22 (X0 X1 X2 : G) :  (((X0 ◇ X0) ◇ X1) ◇ X0) = (((X2 ◇ X2) ◇ X1) ◇ X2) := superpose step17 step17
  have step24 (X0 X1 : G) :  ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((((X1 ◇ X1) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X1 ◇ X1) ◇ X0))) = X1 := superpose step17 step12
  have step27 (X0 X1 : G) :  ((X1 ◇ X1) ◇ X1) = ((((X0 ◇ X0) ◇ X1) ◇ X0) ◇ ((X1 ◇ (((X0 ◇ X0) ◇ X1) ◇ X0)) ◇ X1)) := superpose step17 step12
  have step30 (X0 X1 : G) :  ((X1 ◇ X1) ◇ X1) = ((((X0 ◇ X0) ◇ X1) ◇ X0) ◇ (X1 ◇ X1)) := superpose step9 step27
  have step44 (X0 X1 : G) :  (X0 ◇ X0) = (((X1 ◇ X1) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ X1) := superpose step12 step22
  have step45 (X0 X1 X2 : G) :  ((X0 ◇ X0) ◇ X0) = (((X1 ◇ X1) ◇ (((X2 ◇ X2) ◇ (X0 ◇ X0)) ◇ X2)) ◇ X1) := superpose step9 step22
  have step47 (X0 X1 X2 : G) :  (((X1 ◇ X1) ◇ (X0 ◇ (((X2 ◇ X2) ◇ X0) ◇ (X2 ◇ X2)))) ◇ X1) = (X0 ◇ X2) := superpose step11 step22
  have step80 (X0 X1 : G) :  ((X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) ◇ (((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)))) ◇ (X1 ◇ (X1 ◇ X0)))) = X1 := superpose step18 step12
  have step83 (X0 X1 : G) :  (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) = (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ ((X1 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) ◇ X1)) := superpose step18 step12
  have step90 (X0 : G) :  ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) = ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) := superpose step12 step30
  have step111 (X0 : G) :  (X0 ◇ X0) = (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) := superpose step20 step11
  have step272 (X0 X1 X2 X3 : G) :  (((X3 ◇ X3) ◇ X2) ◇ X3) = ((((X0 ◇ X0) ◇ (((X1 ◇ X1) ◇ (X2 ◇ X2)) ◇ X1)) ◇ X0) ◇ X2) := superpose step45 step22
  have step1213 (X0 : G) :  (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) = ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ ((X0 ◇ X0) ◇ (((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) := superpose step44 step24
  have step1255 (X0 : G) :  (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) = ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) ◇ ((X0 ◇ X0) ◇ (((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))))) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) := superpose step90 step1213
  have step1266 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) := superpose step111 step1255
  have step4082 (X0 : G) :  (X0 ◇ X0) = ((((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) ◇ (X0 ◇ X0))) ◇ ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) ◇ (X0 ◇ X0)))) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) := superpose step1266 step80
  have step4093 (X0 : G) :  (X0 ◇ X0) = ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) := superpose step12 step4082
  have step4121 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose step12 step4093
  have step4282 (X0 : G) :  ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) = (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) := superpose step4121 step83
  have step4284 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose step4121 step12
  have step4286 (X0 X1 : G) :  (X0 ◇ X0) = (((X1 ◇ X1) ◇ (X0 ◇ X0)) ◇ X1) := superpose step4121 step44
  have step4317 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose step12 step4282
  have step4618 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) = ((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) := superpose step4284 step20
  have step4633 (X0 X1 : G) :  (((X1 ◇ X1) ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0))) ◇ X1) = X0 := superpose step4284 step44
  have step4674 (X0 X1 X2 X3 : G) :  ((((X2 ◇ X2) ◇ (((X3 ◇ X3) ◇ (X1 ◇ X1)) ◇ X3)) ◇ X2) ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ X0)) := superpose step4284 step272
  have step4734 (X0 X1 X2 : G) :  ((((X2 ◇ X2) ◇ (X1 ◇ X1)) ◇ X2) ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ X0)) := superpose step4286 step4674
  have step4751 (X0 X1 : G) :  (((X1 ◇ X1) ◇ X0) ◇ X1) = X0 := superpose step4317 step4633
  have step4757 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step4317 step4618
  have step4796 (X0 X1 : G) :  ((X1 ◇ X1) ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ X0)) := superpose step4286 step4734
  have step4827 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X0) = ((X1 ◇ X1) ◇ X1) := superpose step4757 step4796
  have step4850 (X0 X1 : G) :  (X1 ◇ X1) = ((X0 ◇ X1) ◇ X0) := superpose step4757 step4827
  have step4866 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X0) = X1 := superpose step4757 step4850
  have step5314 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ ((((X1 ◇ X1) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X1 ◇ X1) ◇ X0))) = X1 := superpose step4757 step24
  have step5330 (X0 X1 X2 : G) :  (((X1 ◇ X1) ◇ (X2 ◇ ((X0 ◇ X2) ◇ X0))) ◇ X1) = (X2 ◇ X0) := superpose step4757 step47
  have step5579 (X0 X2 : G) :  (X2 ◇ ((X0 ◇ X2) ◇ X0)) = (X2 ◇ X0) := superpose step4751 step5330
  have step5593 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) = X1 := superpose step4866 step5314
  have step5692 (X0 X2 : G) :  (X2 ◇ X2) = (X2 ◇ X0) := superpose step4866 step5579
  have step5703 (X0 X1 : G) :  (X0 ◇ (X0 ◇ X0)) = X1 := superpose step4757 step5593
  have step5764 (X0 X2 : G) :  (X2 ◇ X0) = X2 := superpose step4757 step5692
  have step5771 (X0 X1 : G) :  (X0 ◇ X0) = X1 := superpose step4757 step5703
  have step5790 (X0 X1 : G) :  X0 = X1 := superpose step5764 step5771
  have step6738 (X0 : G) :  sK0 ≠ ((X0 ◇ (sK0 ◇ (sK0 ◇ X0))) ◇ X0) := superpose step5790 step10
  subsumption step6738 step5790


@[equational_result]
theorem Finite.Equation677_and_Equation1249_implies_Equation2301 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation1249 G) : Equation2301 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ (((X1 ◇ X1) ◇ X0) ◇ X1)) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ sK1) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step17 (X0 X1 : G) :  (((X1 ◇ X1) ◇ X0) ◇ X1) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose step9 step12
  have step18 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step20 (X0 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ X0) = (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ X0)) := superpose step12 step9
  have step22 (X0 X1 X2 : G) :  (((X0 ◇ X0) ◇ X1) ◇ X0) = (((X2 ◇ X2) ◇ X1) ◇ X2) := superpose step17 step17
  have step24 (X0 X1 : G) :  ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((((X1 ◇ X1) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X1 ◇ X1) ◇ X0))) = X1 := superpose step17 step12
  have step27 (X0 X1 : G) :  ((X1 ◇ X1) ◇ X1) = ((((X0 ◇ X0) ◇ X1) ◇ X0) ◇ ((X1 ◇ (((X0 ◇ X0) ◇ X1) ◇ X0)) ◇ X1)) := superpose step17 step12
  have step30 (X0 X1 : G) :  ((X1 ◇ X1) ◇ X1) = ((((X0 ◇ X0) ◇ X1) ◇ X0) ◇ (X1 ◇ X1)) := superpose step9 step27
  have step44 (X0 X1 : G) :  (X0 ◇ X0) = (((X1 ◇ X1) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ X1) := superpose step12 step22
  have step45 (X0 X1 X2 : G) :  ((X0 ◇ X0) ◇ X0) = (((X1 ◇ X1) ◇ (((X2 ◇ X2) ◇ (X0 ◇ X0)) ◇ X2)) ◇ X1) := superpose step9 step22
  have step47 (X0 X1 X2 : G) :  (((X1 ◇ X1) ◇ (X0 ◇ (((X2 ◇ X2) ◇ X0) ◇ (X2 ◇ X2)))) ◇ X1) = (X0 ◇ X2) := superpose step11 step22
  have step80 (X0 X1 : G) :  ((X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) ◇ (((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)))) ◇ (X1 ◇ (X1 ◇ X0)))) = X1 := superpose step18 step12
  have step83 (X0 X1 : G) :  (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) = (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ ((X1 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) ◇ X1)) := superpose step18 step12
  have step90 (X0 : G) :  ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) = ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) := superpose step12 step30
  have step111 (X0 : G) :  (X0 ◇ X0) = (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) := superpose step20 step11
  have step272 (X0 X1 X2 X3 : G) :  (((X3 ◇ X3) ◇ X2) ◇ X3) = ((((X0 ◇ X0) ◇ (((X1 ◇ X1) ◇ (X2 ◇ X2)) ◇ X1)) ◇ X0) ◇ X2) := superpose step45 step22
  have step1213 (X0 : G) :  (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) = ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ ((X0 ◇ X0) ◇ (((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) := superpose step44 step24
  have step1255 (X0 : G) :  (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) = ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) ◇ ((X0 ◇ X0) ◇ (((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))))) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) := superpose step90 step1213
  have step1266 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) := superpose step111 step1255
  have step4082 (X0 : G) :  (X0 ◇ X0) = ((((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) ◇ (X0 ◇ X0))) ◇ ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) ◇ (X0 ◇ X0)))) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) := superpose step1266 step80
  have step4093 (X0 : G) :  (X0 ◇ X0) = ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) := superpose step12 step4082
  have step4121 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose step12 step4093
  have step4282 (X0 : G) :  ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) = (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) := superpose step4121 step83
  have step4284 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose step4121 step12
  have step4286 (X0 X1 : G) :  (X0 ◇ X0) = (((X1 ◇ X1) ◇ (X0 ◇ X0)) ◇ X1) := superpose step4121 step44
  have step4317 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose step12 step4282
  have step4618 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) = ((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) := superpose step4284 step20
  have step4633 (X0 X1 : G) :  (((X1 ◇ X1) ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0))) ◇ X1) = X0 := superpose step4284 step44
  have step4674 (X0 X1 X2 X3 : G) :  ((((X2 ◇ X2) ◇ (((X3 ◇ X3) ◇ (X1 ◇ X1)) ◇ X3)) ◇ X2) ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ X0)) := superpose step4284 step272
  have step4734 (X0 X1 X2 : G) :  ((((X2 ◇ X2) ◇ (X1 ◇ X1)) ◇ X2) ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ X0)) := superpose step4286 step4674
  have step4751 (X0 X1 : G) :  (((X1 ◇ X1) ◇ X0) ◇ X1) = X0 := superpose step4317 step4633
  have step4757 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step4317 step4618
  have step4796 (X0 X1 : G) :  ((X1 ◇ X1) ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ X0)) := superpose step4286 step4734
  have step4827 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X0) = ((X1 ◇ X1) ◇ X1) := superpose step4757 step4796
  have step4850 (X0 X1 : G) :  (X1 ◇ X1) = ((X0 ◇ X1) ◇ X0) := superpose step4757 step4827
  have step4866 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X0) = X1 := superpose step4757 step4850
  have step5314 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ ((((X1 ◇ X1) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X1 ◇ X1) ◇ X0))) = X1 := superpose step4757 step24
  have step5330 (X0 X1 X2 : G) :  (((X1 ◇ X1) ◇ (X2 ◇ ((X0 ◇ X2) ◇ X0))) ◇ X1) = (X2 ◇ X0) := superpose step4757 step47
  have step5579 (X0 X2 : G) :  (X2 ◇ ((X0 ◇ X2) ◇ X0)) = (X2 ◇ X0) := superpose step4751 step5330
  have step5593 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) = X1 := superpose step4866 step5314
  have step5692 (X0 X2 : G) :  (X2 ◇ X2) = (X2 ◇ X0) := superpose step4866 step5579
  have step5703 (X0 X1 : G) :  (X0 ◇ (X0 ◇ X0)) = X1 := superpose step4757 step5593
  have step5764 (X0 X2 : G) :  (X2 ◇ X0) = X2 := superpose step4757 step5692
  have step5771 (X0 X1 : G) :  (X0 ◇ X0) = X1 := superpose step4757 step5703
  have step5790 (X0 X1 : G) :  X0 = X1 := superpose step5764 step5771
  have step6738 (X0 : G) :  sK0 ≠ ((X0 ◇ (sK0 ◇ (X0 ◇ sK0))) ◇ X0) := superpose step5790 step10
  subsumption step6738 step5790


@[equational_result]
theorem Finite.Equation677_and_Equation1249_implies_Equation2457 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation1249 G) : Equation2457 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ (((X1 ◇ X1) ◇ X0) ◇ X1)) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ ((sK0 ◇ ((sK1 ◇ sK0) ◇ sK0)) ◇ sK1) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step17 (X0 X1 : G) :  (((X1 ◇ X1) ◇ X0) ◇ X1) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose step9 step12
  have step18 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step20 (X0 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ X0) = (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ X0)) := superpose step12 step9
  have step22 (X0 X1 X2 : G) :  (((X0 ◇ X0) ◇ X1) ◇ X0) = (((X2 ◇ X2) ◇ X1) ◇ X2) := superpose step17 step17
  have step24 (X0 X1 : G) :  ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((((X1 ◇ X1) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X1 ◇ X1) ◇ X0))) = X1 := superpose step17 step12
  have step28 (X0 X1 : G) :  ((X1 ◇ X1) ◇ X1) = ((((X0 ◇ X0) ◇ X1) ◇ X0) ◇ ((X1 ◇ (((X0 ◇ X0) ◇ X1) ◇ X0)) ◇ X1)) := superpose step17 step12
  have step30 (X0 X1 : G) :  ((X1 ◇ X1) ◇ X1) = ((((X0 ◇ X0) ◇ X1) ◇ X0) ◇ (X1 ◇ X1)) := superpose step9 step28
  have step44 (X0 X1 : G) :  (X0 ◇ X0) = (((X1 ◇ X1) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ X1) := superpose step12 step22
  have step49 (X0 X1 X2 : G) :  (((X2 ◇ X2) ◇ X1) ◇ X2) = ((((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ X0) ◇ (X1 ◇ X1)) := superpose step22 step22
  have step80 (X0 X1 : G) :  ((X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) ◇ (((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)))) ◇ (X1 ◇ (X1 ◇ X0)))) = X1 := superpose step18 step12
  have step86 (X0 X1 : G) :  (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) = (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ ((X1 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) ◇ X1)) := superpose step18 step12
  have step90 (X0 : G) :  ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) = ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) := superpose step12 step30
  have step111 (X0 : G) :  (X0 ◇ X0) = (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) := superpose step20 step11
  have step445 (X0 X1 : G) :  (((X1 ◇ X1) ◇ X0) ◇ X1) = (((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0)) := superpose step17 step49
  have step1213 (X0 : G) :  (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) = ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ ((X0 ◇ X0) ◇ (((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) := superpose step44 step24
  have step1255 (X0 : G) :  (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) = ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) ◇ ((X0 ◇ X0) ◇ (((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))))) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) := superpose step90 step1213
  have step1266 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) := superpose step111 step1255
  have step4082 (X0 : G) :  (X0 ◇ X0) = ((((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) ◇ (X0 ◇ X0))) ◇ ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) ◇ (X0 ◇ X0)))) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) := superpose step1266 step80
  have step4093 (X0 : G) :  (X0 ◇ X0) = ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) := superpose step12 step4082
  have step4121 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose step12 step4093
  have step4282 (X0 : G) :  ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) = (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) := superpose step4121 step86
  have step4284 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose step4121 step12
  have step4317 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose step12 step4282
  have step4593 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) = ((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) := superpose step4284 step20
  have step4596 (X0 X1 : G) :  (X0 ◇ X0) = ((X1 ◇ ((X1 ◇ X1) ◇ X1)) ◇ (((X0 ◇ X1) ◇ (X1 ◇ ((X1 ◇ X1) ◇ X1))) ◇ (X0 ◇ X1))) := superpose step4284 step24
  have step4630 (X0 : G) :  ((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ ((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0))))) = X0 := superpose step4284 step111
  have step4659 (X0 X1 : G) :  (((X1 ◇ X1) ◇ (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ (X1 ◇ X1))) ◇ (X1 ◇ X1)) = ((X0 ◇ X1) ◇ (X0 ◇ X0)) := superpose step4284 step445
  have step4685 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose step4284 step30
  have step4696 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) := superpose step4284 step445
  have step4747 (X0 X1 : G) :  ((X1 ◇ X1) ◇ (X1 ◇ X1)) = ((X0 ◇ X1) ◇ (X0 ◇ X0)) := superpose step4696 step4659
  have step4769 (X0 : G) :  (X0 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose step4317 step4630
  have step4794 (X0 X1 : G) :  (X0 ◇ X0) = ((X1 ◇ (X1 ◇ (X1 ◇ X1))) ◇ (((X0 ◇ X1) ◇ (X1 ◇ (X1 ◇ (X1 ◇ X1)))) ◇ (X0 ◇ X1))) := superpose step4685 step4596
  have step4795 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step4317 step4593
  have step4828 (X0 X1 : G) :  ((X0 ◇ X1) ◇ (X0 ◇ X0)) = X1 := superpose step4284 step4747
  have step4849 (X0 X1 : G) :  (X0 ◇ X0) = (X1 ◇ (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1))) := superpose step4769 step4794
  have step4870 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X0) = X1 := superpose step4795 step4828
  have step4888 (X0 X1 : G) :  (X1 ◇ (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1))) = X0 := superpose step4795 step4849
  have step4915 (X0 X1 : G) :  (X1 ◇ X1) = X0 := superpose step4870 step4888
  have step6551 (X0 : G) :  sK0 ≠ (X0 ◇ X0) := superpose step4915 step10
  subsumption step6551 step4915


@[equational_result]
theorem Finite.Equation677_and_Equation1249_implies_Equation2700 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation1249 G) : Equation2700 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ (((X1 ◇ X1) ◇ X0) ◇ X1)) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ (((sK1 ◇ sK0) ◇ (sK0 ◇ sK1)) ◇ sK1) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step17 (X0 X1 : G) :  (((X1 ◇ X1) ◇ X0) ◇ X1) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose step9 step12
  have step18 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step20 (X0 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ X0) = (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ X0)) := superpose step12 step9
  have step22 (X0 X1 X2 : G) :  (((X0 ◇ X0) ◇ X1) ◇ X0) = (((X2 ◇ X2) ◇ X1) ◇ X2) := superpose step17 step17
  have step24 (X0 X1 : G) :  ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((((X1 ◇ X1) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X1 ◇ X1) ◇ X0))) = X1 := superpose step17 step12
  have step27 (X0 X1 : G) :  ((X1 ◇ X1) ◇ X1) = ((((X0 ◇ X0) ◇ X1) ◇ X0) ◇ ((X1 ◇ (((X0 ◇ X0) ◇ X1) ◇ X0)) ◇ X1)) := superpose step17 step12
  have step30 (X0 X1 : G) :  ((X1 ◇ X1) ◇ X1) = ((((X0 ◇ X0) ◇ X1) ◇ X0) ◇ (X1 ◇ X1)) := superpose step9 step27
  have step44 (X0 X1 : G) :  (X0 ◇ X0) = (((X1 ◇ X1) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ X1) := superpose step12 step22
  have step45 (X0 X1 X2 : G) :  ((X0 ◇ X0) ◇ X0) = (((X1 ◇ X1) ◇ (((X2 ◇ X2) ◇ (X0 ◇ X0)) ◇ X2)) ◇ X1) := superpose step9 step22
  have step47 (X0 X1 X2 : G) :  (((X1 ◇ X1) ◇ (X0 ◇ (((X2 ◇ X2) ◇ X0) ◇ (X2 ◇ X2)))) ◇ X1) = (X0 ◇ X2) := superpose step11 step22
  have step80 (X0 X1 : G) :  ((X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) ◇ (((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)))) ◇ (X1 ◇ (X1 ◇ X0)))) = X1 := superpose step18 step12
  have step83 (X0 X1 : G) :  (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) = (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ ((X1 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) ◇ X1)) := superpose step18 step12
  have step90 (X0 : G) :  ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) = ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) := superpose step12 step30
  have step111 (X0 : G) :  (X0 ◇ X0) = (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) := superpose step20 step11
  have step272 (X0 X1 X2 X3 : G) :  (((X3 ◇ X3) ◇ X2) ◇ X3) = ((((X0 ◇ X0) ◇ (((X1 ◇ X1) ◇ (X2 ◇ X2)) ◇ X1)) ◇ X0) ◇ X2) := superpose step45 step22
  have step1213 (X0 : G) :  (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) = ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ ((X0 ◇ X0) ◇ (((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) := superpose step44 step24
  have step1255 (X0 : G) :  (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) = ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) ◇ ((X0 ◇ X0) ◇ (((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))))) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) := superpose step90 step1213
  have step1266 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) := superpose step111 step1255
  have step4082 (X0 : G) :  (X0 ◇ X0) = ((((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) ◇ (X0 ◇ X0))) ◇ ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) ◇ (X0 ◇ X0)))) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) := superpose step1266 step80
  have step4093 (X0 : G) :  (X0 ◇ X0) = ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) := superpose step12 step4082
  have step4121 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose step12 step4093
  have step4282 (X0 : G) :  ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) = (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) := superpose step4121 step83
  have step4284 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose step4121 step12
  have step4286 (X0 X1 : G) :  (X0 ◇ X0) = (((X1 ◇ X1) ◇ (X0 ◇ X0)) ◇ X1) := superpose step4121 step44
  have step4317 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose step12 step4282
  have step4618 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) = ((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) := superpose step4284 step20
  have step4633 (X0 X1 : G) :  (((X1 ◇ X1) ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0))) ◇ X1) = X0 := superpose step4284 step44
  have step4674 (X0 X1 X2 X3 : G) :  ((((X2 ◇ X2) ◇ (((X3 ◇ X3) ◇ (X1 ◇ X1)) ◇ X3)) ◇ X2) ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ X0)) := superpose step4284 step272
  have step4734 (X0 X1 X2 : G) :  ((((X2 ◇ X2) ◇ (X1 ◇ X1)) ◇ X2) ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ X0)) := superpose step4286 step4674
  have step4751 (X0 X1 : G) :  (((X1 ◇ X1) ◇ X0) ◇ X1) = X0 := superpose step4317 step4633
  have step4757 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step4317 step4618
  have step4796 (X0 X1 : G) :  ((X1 ◇ X1) ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ X0)) := superpose step4286 step4734
  have step4827 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X0) = ((X1 ◇ X1) ◇ X1) := superpose step4757 step4796
  have step4850 (X0 X1 : G) :  (X1 ◇ X1) = ((X0 ◇ X1) ◇ X0) := superpose step4757 step4827
  have step4866 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X0) = X1 := superpose step4757 step4850
  have step5314 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ ((((X1 ◇ X1) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X1 ◇ X1) ◇ X0))) = X1 := superpose step4757 step24
  have step5330 (X0 X1 X2 : G) :  (((X1 ◇ X1) ◇ (X2 ◇ ((X0 ◇ X2) ◇ X0))) ◇ X1) = (X2 ◇ X0) := superpose step4757 step47
  have step5579 (X0 X2 : G) :  (X2 ◇ ((X0 ◇ X2) ◇ X0)) = (X2 ◇ X0) := superpose step4751 step5330
  have step5593 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) = X1 := superpose step4866 step5314
  have step5692 (X0 X2 : G) :  (X2 ◇ X2) = (X2 ◇ X0) := superpose step4866 step5579
  have step5703 (X0 X1 : G) :  (X0 ◇ (X0 ◇ X0)) = X1 := superpose step4757 step5593
  have step5764 (X0 X2 : G) :  (X2 ◇ X0) = X2 := superpose step4757 step5692
  have step5771 (X0 X1 : G) :  (X0 ◇ X0) = X1 := superpose step4757 step5703
  have step5790 (X0 X1 : G) :  X0 = X1 := superpose step5764 step5771
  have step6738 (X0 : G) :  sK0 ≠ (((X0 ◇ sK0) ◇ (sK0 ◇ X0)) ◇ X0) := superpose step5790 step10
  subsumption step6738 step5790


@[equational_result]
theorem Finite.Equation677_and_Equation1249_implies_Equation2856 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation1249 G) : Equation2856 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ (((X1 ◇ X1) ◇ X0) ◇ X1)) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ (((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) ◇ sK1) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step17 (X0 X1 : G) :  (((X1 ◇ X1) ◇ X0) ◇ X1) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose step9 step12
  have step18 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step20 (X0 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ X0) = (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ X0)) := superpose step12 step9
  have step22 (X0 X1 X2 : G) :  (((X0 ◇ X0) ◇ X1) ◇ X0) = (((X2 ◇ X2) ◇ X1) ◇ X2) := superpose step17 step17
  have step24 (X0 X1 : G) :  ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((((X1 ◇ X1) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X1 ◇ X1) ◇ X0))) = X1 := superpose step17 step12
  have step28 (X0 X1 : G) :  ((X1 ◇ X1) ◇ X1) = ((((X0 ◇ X0) ◇ X1) ◇ X0) ◇ ((X1 ◇ (((X0 ◇ X0) ◇ X1) ◇ X0)) ◇ X1)) := superpose step17 step12
  have step30 (X0 X1 : G) :  ((X1 ◇ X1) ◇ X1) = ((((X0 ◇ X0) ◇ X1) ◇ X0) ◇ (X1 ◇ X1)) := superpose step9 step28
  have step44 (X0 X1 : G) :  (X0 ◇ X0) = (((X1 ◇ X1) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ X1) := superpose step12 step22
  have step45 (X0 X1 X2 : G) :  ((X0 ◇ X0) ◇ X0) = (((X1 ◇ X1) ◇ (((X2 ◇ X2) ◇ (X0 ◇ X0)) ◇ X2)) ◇ X1) := superpose step9 step22
  have step47 (X0 X1 X2 : G) :  (((X1 ◇ X1) ◇ (X0 ◇ (((X2 ◇ X2) ◇ X0) ◇ (X2 ◇ X2)))) ◇ X1) = (X0 ◇ X2) := superpose step11 step22
  have step80 (X0 X1 : G) :  ((X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) ◇ (((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)))) ◇ (X1 ◇ (X1 ◇ X0)))) = X1 := superpose step18 step12
  have step86 (X0 X1 : G) :  (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) = (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ ((X1 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) ◇ X1)) := superpose step18 step12
  have step90 (X0 : G) :  ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) = ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) := superpose step12 step30
  have step111 (X0 : G) :  (X0 ◇ X0) = (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) := superpose step20 step11
  have step272 (X0 X1 X2 X3 : G) :  (((X3 ◇ X3) ◇ X2) ◇ X3) = ((((X0 ◇ X0) ◇ (((X1 ◇ X1) ◇ (X2 ◇ X2)) ◇ X1)) ◇ X0) ◇ X2) := superpose step45 step22
  have step1213 (X0 : G) :  (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) = ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ ((X0 ◇ X0) ◇ (((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) := superpose step44 step24
  have step1255 (X0 : G) :  (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) = ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) ◇ ((X0 ◇ X0) ◇ (((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))))) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) := superpose step90 step1213
  have step1266 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) := superpose step111 step1255
  have step4082 (X0 : G) :  (X0 ◇ X0) = ((((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) ◇ (X0 ◇ X0))) ◇ ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) ◇ (X0 ◇ X0)))) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) := superpose step1266 step80
  have step4093 (X0 : G) :  (X0 ◇ X0) = ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) := superpose step12 step4082
  have step4121 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose step12 step4093
  have step4282 (X0 : G) :  ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) = (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) := superpose step4121 step86
  have step4284 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose step4121 step12
  have step4286 (X0 X1 : G) :  (X0 ◇ X0) = (((X1 ◇ X1) ◇ (X0 ◇ X0)) ◇ X1) := superpose step4121 step44
  have step4317 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose step12 step4282
  have step4618 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) = ((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) := superpose step4284 step20
  have step4633 (X0 X1 : G) :  (((X1 ◇ X1) ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0))) ◇ X1) = X0 := superpose step4284 step44
  have step4674 (X0 X1 X2 X3 : G) :  ((((X2 ◇ X2) ◇ (((X3 ◇ X3) ◇ (X1 ◇ X1)) ◇ X3)) ◇ X2) ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ X0)) := superpose step4284 step272
  have step4734 (X0 X1 X2 : G) :  ((((X2 ◇ X2) ◇ (X1 ◇ X1)) ◇ X2) ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ X0)) := superpose step4286 step4674
  have step4751 (X0 X1 : G) :  (((X1 ◇ X1) ◇ X0) ◇ X1) = X0 := superpose step4317 step4633
  have step4757 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step4317 step4618
  have step4796 (X0 X1 : G) :  ((X1 ◇ X1) ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ X0)) := superpose step4286 step4734
  have step4827 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X0) = ((X1 ◇ X1) ◇ X1) := superpose step4757 step4796
  have step4850 (X0 X1 : G) :  (X1 ◇ X1) = ((X0 ◇ X1) ◇ X0) := superpose step4757 step4827
  have step4866 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X0) = X1 := superpose step4757 step4850
  have step5365 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ ((((X1 ◇ X1) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X1 ◇ X1) ◇ X0))) = X1 := superpose step4757 step24
  have step5381 (X0 X1 X2 : G) :  (((X1 ◇ X1) ◇ (X2 ◇ ((X0 ◇ X2) ◇ X0))) ◇ X1) = (X2 ◇ X0) := superpose step4757 step47
  have step5534 (X0 X2 : G) :  (X2 ◇ ((X0 ◇ X2) ◇ X0)) = (X2 ◇ X0) := superpose step4751 step5381
  have step5548 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) = X1 := superpose step4866 step5365
  have step5664 (X0 X2 : G) :  (X2 ◇ X2) = (X2 ◇ X0) := superpose step4866 step5534
  have step5675 (X0 X1 : G) :  (X0 ◇ (X0 ◇ X0)) = X1 := superpose step4757 step5548
  have step5751 (X0 X2 : G) :  (X2 ◇ X0) = X2 := superpose step4757 step5664
  have step5758 (X0 X1 : G) :  (X0 ◇ X0) = X1 := superpose step4757 step5675
  have step5784 (X0 X1 : G) :  X0 = X1 := superpose step5751 step5758
  have step6734 (X0 : G) :  sK0 ≠ (((sK0 ◇ (sK0 ◇ X0)) ◇ X0) ◇ X0) := superpose step5784 step10
  subsumption step6734 step5784


@[equational_result]
theorem Finite.Equation677_and_Equation1249_implies_Equation2866 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation1249 G) : Equation2866 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ (((X1 ◇ X1) ◇ X0) ◇ X1)) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ (((sK0 ◇ (sK1 ◇ sK0)) ◇ sK1) ◇ sK1) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step17 (X0 X1 : G) :  (((X1 ◇ X1) ◇ X0) ◇ X1) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose step9 step12
  have step18 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step20 (X0 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ X0) = (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ X0)) := superpose step12 step9
  have step22 (X0 X1 X2 : G) :  (((X0 ◇ X0) ◇ X1) ◇ X0) = (((X2 ◇ X2) ◇ X1) ◇ X2) := superpose step17 step17
  have step24 (X0 X1 : G) :  ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((((X1 ◇ X1) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X1 ◇ X1) ◇ X0))) = X1 := superpose step17 step12
  have step27 (X0 X1 : G) :  ((X1 ◇ X1) ◇ X1) = ((((X0 ◇ X0) ◇ X1) ◇ X0) ◇ ((X1 ◇ (((X0 ◇ X0) ◇ X1) ◇ X0)) ◇ X1)) := superpose step17 step12
  have step30 (X0 X1 : G) :  ((X1 ◇ X1) ◇ X1) = ((((X0 ◇ X0) ◇ X1) ◇ X0) ◇ (X1 ◇ X1)) := superpose step9 step27
  have step44 (X0 X1 : G) :  (X0 ◇ X0) = (((X1 ◇ X1) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ X1) := superpose step12 step22
  have step45 (X0 X1 X2 : G) :  ((X0 ◇ X0) ◇ X0) = (((X1 ◇ X1) ◇ (((X2 ◇ X2) ◇ (X0 ◇ X0)) ◇ X2)) ◇ X1) := superpose step9 step22
  have step47 (X0 X1 X2 : G) :  (((X1 ◇ X1) ◇ (X0 ◇ (((X2 ◇ X2) ◇ X0) ◇ (X2 ◇ X2)))) ◇ X1) = (X0 ◇ X2) := superpose step11 step22
  have step80 (X0 X1 : G) :  ((X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) ◇ (((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)))) ◇ (X1 ◇ (X1 ◇ X0)))) = X1 := superpose step18 step12
  have step83 (X0 X1 : G) :  (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) = (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ ((X1 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) ◇ X1)) := superpose step18 step12
  have step90 (X0 : G) :  ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) = ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) := superpose step12 step30
  have step111 (X0 : G) :  (X0 ◇ X0) = (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) := superpose step20 step11
  have step272 (X0 X1 X2 X3 : G) :  (((X3 ◇ X3) ◇ X2) ◇ X3) = ((((X0 ◇ X0) ◇ (((X1 ◇ X1) ◇ (X2 ◇ X2)) ◇ X1)) ◇ X0) ◇ X2) := superpose step45 step22
  have step1213 (X0 : G) :  (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) = ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ ((X0 ◇ X0) ◇ (((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) := superpose step44 step24
  have step1255 (X0 : G) :  (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) = ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) ◇ ((X0 ◇ X0) ◇ (((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))))) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) := superpose step90 step1213
  have step1266 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) := superpose step111 step1255
  have step4082 (X0 : G) :  (X0 ◇ X0) = ((((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) ◇ (X0 ◇ X0))) ◇ ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) ◇ (X0 ◇ X0)))) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) := superpose step1266 step80
  have step4093 (X0 : G) :  (X0 ◇ X0) = ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) := superpose step12 step4082
  have step4121 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose step12 step4093
  have step4282 (X0 : G) :  ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) = (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) := superpose step4121 step83
  have step4284 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose step4121 step12
  have step4286 (X0 X1 : G) :  (X0 ◇ X0) = (((X1 ◇ X1) ◇ (X0 ◇ X0)) ◇ X1) := superpose step4121 step44
  have step4317 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose step12 step4282
  have step4618 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) = ((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) := superpose step4284 step20
  have step4633 (X0 X1 : G) :  (((X1 ◇ X1) ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0))) ◇ X1) = X0 := superpose step4284 step44
  have step4674 (X0 X1 X2 X3 : G) :  ((((X2 ◇ X2) ◇ (((X3 ◇ X3) ◇ (X1 ◇ X1)) ◇ X3)) ◇ X2) ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ X0)) := superpose step4284 step272
  have step4734 (X0 X1 X2 : G) :  ((((X2 ◇ X2) ◇ (X1 ◇ X1)) ◇ X2) ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ X0)) := superpose step4286 step4674
  have step4751 (X0 X1 : G) :  (((X1 ◇ X1) ◇ X0) ◇ X1) = X0 := superpose step4317 step4633
  have step4757 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step4317 step4618
  have step4796 (X0 X1 : G) :  ((X1 ◇ X1) ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ X0)) := superpose step4286 step4734
  have step4827 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X0) = ((X1 ◇ X1) ◇ X1) := superpose step4757 step4796
  have step4850 (X0 X1 : G) :  (X1 ◇ X1) = ((X0 ◇ X1) ◇ X0) := superpose step4757 step4827
  have step4866 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X0) = X1 := superpose step4757 step4850
  have step5314 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ ((((X1 ◇ X1) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X1 ◇ X1) ◇ X0))) = X1 := superpose step4757 step24
  have step5330 (X0 X1 X2 : G) :  (((X1 ◇ X1) ◇ (X2 ◇ ((X0 ◇ X2) ◇ X0))) ◇ X1) = (X2 ◇ X0) := superpose step4757 step47
  have step5579 (X0 X2 : G) :  (X2 ◇ ((X0 ◇ X2) ◇ X0)) = (X2 ◇ X0) := superpose step4751 step5330
  have step5593 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) = X1 := superpose step4866 step5314
  have step5692 (X0 X2 : G) :  (X2 ◇ X2) = (X2 ◇ X0) := superpose step4866 step5579
  have step5703 (X0 X1 : G) :  (X0 ◇ (X0 ◇ X0)) = X1 := superpose step4757 step5593
  have step5764 (X0 X2 : G) :  (X2 ◇ X0) = X2 := superpose step4757 step5692
  have step5771 (X0 X1 : G) :  (X0 ◇ X0) = X1 := superpose step4757 step5703
  have step5790 (X0 X1 : G) :  X0 = X1 := superpose step5764 step5771
  have step6738 (X0 : G) :  sK0 ≠ (((sK0 ◇ (X0 ◇ sK0)) ◇ X0) ◇ X0) := superpose step5790 step10
  subsumption step6738 step5790


@[equational_result]
theorem Finite.Equation677_and_Equation1249_implies_Equation3106 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation1249 G) : Equation3106 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ (((X1 ◇ X1) ◇ X0) ◇ X1)) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ ((((sK1 ◇ sK0) ◇ sK0) ◇ sK1) ◇ sK1) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step17 (X0 X1 : G) :  (((X1 ◇ X1) ◇ X0) ◇ X1) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose step9 step12
  have step18 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step20 (X0 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ X0) = (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ X0)) := superpose step12 step9
  have step22 (X0 X1 X2 : G) :  (((X0 ◇ X0) ◇ X1) ◇ X0) = (((X2 ◇ X2) ◇ X1) ◇ X2) := superpose step17 step17
  have step24 (X0 X1 : G) :  ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((((X1 ◇ X1) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X1 ◇ X1) ◇ X0))) = X1 := superpose step17 step12
  have step28 (X0 X1 : G) :  ((X1 ◇ X1) ◇ X1) = ((((X0 ◇ X0) ◇ X1) ◇ X0) ◇ ((X1 ◇ (((X0 ◇ X0) ◇ X1) ◇ X0)) ◇ X1)) := superpose step17 step12
  have step30 (X0 X1 : G) :  ((X1 ◇ X1) ◇ X1) = ((((X0 ◇ X0) ◇ X1) ◇ X0) ◇ (X1 ◇ X1)) := superpose step9 step28
  have step44 (X0 X1 : G) :  (X0 ◇ X0) = (((X1 ◇ X1) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ X1) := superpose step12 step22
  have step49 (X0 X1 X2 : G) :  (((X2 ◇ X2) ◇ X1) ◇ X2) = ((((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ X0) ◇ (X1 ◇ X1)) := superpose step22 step22
  have step80 (X0 X1 : G) :  ((X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) ◇ (((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)))) ◇ (X1 ◇ (X1 ◇ X0)))) = X1 := superpose step18 step12
  have step86 (X0 X1 : G) :  (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) = (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ ((X1 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) ◇ X1)) := superpose step18 step12
  have step90 (X0 : G) :  ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) = ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) := superpose step12 step30
  have step111 (X0 : G) :  (X0 ◇ X0) = (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) := superpose step20 step11
  have step445 (X0 X1 : G) :  (((X1 ◇ X1) ◇ X0) ◇ X1) = (((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0)) := superpose step17 step49
  have step1213 (X0 : G) :  (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) = ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ ((X0 ◇ X0) ◇ (((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) := superpose step44 step24
  have step1255 (X0 : G) :  (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) = ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) ◇ ((X0 ◇ X0) ◇ (((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))))) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) := superpose step90 step1213
  have step1266 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) := superpose step111 step1255
  have step4082 (X0 : G) :  (X0 ◇ X0) = ((((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) ◇ (X0 ◇ X0))) ◇ ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) ◇ (X0 ◇ X0)))) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) := superpose step1266 step80
  have step4093 (X0 : G) :  (X0 ◇ X0) = ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) := superpose step12 step4082
  have step4121 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose step12 step4093
  have step4282 (X0 : G) :  ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) = (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) := superpose step4121 step86
  have step4284 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose step4121 step12
  have step4317 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose step12 step4282
  have step4593 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) = ((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) := superpose step4284 step20
  have step4596 (X0 X1 : G) :  (X0 ◇ X0) = ((X1 ◇ ((X1 ◇ X1) ◇ X1)) ◇ (((X0 ◇ X1) ◇ (X1 ◇ ((X1 ◇ X1) ◇ X1))) ◇ (X0 ◇ X1))) := superpose step4284 step24
  have step4630 (X0 : G) :  ((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ ((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0))))) = X0 := superpose step4284 step111
  have step4659 (X0 X1 : G) :  (((X1 ◇ X1) ◇ (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ (X1 ◇ X1))) ◇ (X1 ◇ X1)) = ((X0 ◇ X1) ◇ (X0 ◇ X0)) := superpose step4284 step445
  have step4685 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose step4284 step30
  have step4696 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) := superpose step4284 step445
  have step4747 (X0 X1 : G) :  ((X1 ◇ X1) ◇ (X1 ◇ X1)) = ((X0 ◇ X1) ◇ (X0 ◇ X0)) := superpose step4696 step4659
  have step4769 (X0 : G) :  (X0 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose step4317 step4630
  have step4794 (X0 X1 : G) :  (X0 ◇ X0) = ((X1 ◇ (X1 ◇ (X1 ◇ X1))) ◇ (((X0 ◇ X1) ◇ (X1 ◇ (X1 ◇ (X1 ◇ X1)))) ◇ (X0 ◇ X1))) := superpose step4685 step4596
  have step4795 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step4317 step4593
  have step4828 (X0 X1 : G) :  ((X0 ◇ X1) ◇ (X0 ◇ X0)) = X1 := superpose step4284 step4747
  have step4849 (X0 X1 : G) :  (X0 ◇ X0) = (X1 ◇ (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1))) := superpose step4769 step4794
  have step4870 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X0) = X1 := superpose step4795 step4828
  have step4888 (X0 X1 : G) :  (X1 ◇ (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1))) = X0 := superpose step4795 step4849
  have step4915 (X0 X1 : G) :  (X1 ◇ X1) = X0 := superpose step4870 step4888
  have step6551 (X0 : G) :  sK0 ≠ (X0 ◇ X0) := superpose step4915 step10
  subsumption step6551 step4915


@[equational_result]
theorem Finite.Equation677_and_Equation1249_implies_Equation3355 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation1249 G) : Equation3355 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ (((X1 ◇ X1) ◇ X0) ◇ X1)) = X0 := mod_symm (h ..)
  have step10 : (sK0 ◇ sK1) ≠ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step17 (X0 X1 : G) :  (((X1 ◇ X1) ◇ X0) ◇ X1) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose step9 step12
  have step18 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step20 (X0 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ X0) = (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ X0)) := superpose step12 step9
  have step22 (X0 X1 X2 : G) :  (((X0 ◇ X0) ◇ X1) ◇ X0) = (((X2 ◇ X2) ◇ X1) ◇ X2) := superpose step17 step17
  have step24 (X0 X1 : G) :  ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((((X1 ◇ X1) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X1 ◇ X1) ◇ X0))) = X1 := superpose step17 step12
  have step27 (X0 X1 : G) :  ((X1 ◇ X1) ◇ X1) = ((((X0 ◇ X0) ◇ X1) ◇ X0) ◇ ((X1 ◇ (((X0 ◇ X0) ◇ X1) ◇ X0)) ◇ X1)) := superpose step17 step12
  have step30 (X0 X1 : G) :  ((X1 ◇ X1) ◇ X1) = ((((X0 ◇ X0) ◇ X1) ◇ X0) ◇ (X1 ◇ X1)) := superpose step9 step27
  have step44 (X0 X1 : G) :  (X0 ◇ X0) = (((X1 ◇ X1) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ X1) := superpose step12 step22
  have step45 (X0 X1 X2 : G) :  ((X0 ◇ X0) ◇ X0) = (((X1 ◇ X1) ◇ (((X2 ◇ X2) ◇ (X0 ◇ X0)) ◇ X2)) ◇ X1) := superpose step9 step22
  have step47 (X0 X1 X2 : G) :  (((X1 ◇ X1) ◇ (X0 ◇ (((X2 ◇ X2) ◇ X0) ◇ (X2 ◇ X2)))) ◇ X1) = (X0 ◇ X2) := superpose step11 step22
  have step80 (X0 X1 : G) :  ((X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) ◇ (((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)))) ◇ (X1 ◇ (X1 ◇ X0)))) = X1 := superpose step18 step12
  have step83 (X0 X1 : G) :  (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) = (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ ((X1 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) ◇ X1)) := superpose step18 step12
  have step90 (X0 : G) :  ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) = ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) := superpose step12 step30
  have step111 (X0 : G) :  (X0 ◇ X0) = (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) := superpose step20 step11
  have step275 (X0 X1 X2 X3 : G) :  (((X3 ◇ X3) ◇ X2) ◇ X3) = (X2 ◇ (((X0 ◇ X0) ◇ (((X1 ◇ X1) ◇ (X2 ◇ X2)) ◇ X1)) ◇ X0)) := superpose step45 step17
  have step1229 (X0 : G) :  (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) = ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ ((X0 ◇ X0) ◇ (((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) := superpose step44 step24
  have step1271 (X0 : G) :  (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) = ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) ◇ ((X0 ◇ X0) ◇ (((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))))) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) := superpose step90 step1229
  have step1282 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) := superpose step111 step1271
  have step4081 (X0 : G) :  (X0 ◇ X0) = ((((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) ◇ (X0 ◇ X0))) ◇ ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) ◇ (X0 ◇ X0)))) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) := superpose step1282 step80
  have step4092 (X0 : G) :  (X0 ◇ X0) = ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) := superpose step12 step4081
  have step4120 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose step12 step4092
  have step4281 (X0 : G) :  ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) = (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) := superpose step4120 step83
  have step4283 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose step4120 step12
  have step4285 (X0 X1 : G) :  (X0 ◇ X0) = (((X1 ◇ X1) ◇ (X0 ◇ X0)) ◇ X1) := superpose step4120 step44
  have step4316 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose step12 step4281
  have step4617 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) = ((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) := superpose step4283 step20
  have step4632 (X0 X1 : G) :  (((X1 ◇ X1) ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0))) ◇ X1) = X0 := superpose step4283 step44
  have step4676 (X0 X1 X2 X3 : G) :  (X1 ◇ (((X2 ◇ X2) ◇ (((X3 ◇ X3) ◇ (X1 ◇ X1)) ◇ X3)) ◇ X2)) = ((X0 ◇ X1) ◇ (X0 ◇ X0)) := superpose step4283 step275
  have step4732 (X0 X1 X2 : G) :  ((X0 ◇ X1) ◇ (X0 ◇ X0)) = (X1 ◇ (((X2 ◇ X2) ◇ (X1 ◇ X1)) ◇ X2)) := superpose step4285 step4676
  have step4750 (X0 X1 : G) :  (((X1 ◇ X1) ◇ X0) ◇ X1) = X0 := superpose step4316 step4632
  have step4756 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step4316 step4617
  have step4795 (X0 X1 : G) :  (X1 ◇ (X1 ◇ X1)) = ((X0 ◇ X1) ◇ (X0 ◇ X0)) := superpose step4285 step4732
  have step4826 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X0) = (X1 ◇ (X1 ◇ X1)) := superpose step4756 step4795
  have step4849 (X0 X1 : G) :  (X1 ◇ X1) = ((X0 ◇ X1) ◇ X0) := superpose step4756 step4826
  have step4865 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X0) = X1 := superpose step4756 step4849
  have step5313 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ ((((X1 ◇ X1) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X1 ◇ X1) ◇ X0))) = X1 := superpose step4756 step24
  have step5329 (X0 X1 X2 : G) :  (((X1 ◇ X1) ◇ (X2 ◇ ((X0 ◇ X2) ◇ X0))) ◇ X1) = (X2 ◇ X0) := superpose step4756 step47
  have step5578 (X0 X2 : G) :  (X2 ◇ ((X0 ◇ X2) ◇ X0)) = (X2 ◇ X0) := superpose step4750 step5329
  have step5592 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) = X1 := superpose step4865 step5313
  have step5691 (X0 X2 : G) :  (X2 ◇ X2) = (X2 ◇ X0) := superpose step4865 step5578
  have step5702 (X0 X1 : G) :  (X0 ◇ (X0 ◇ X0)) = X1 := superpose step4756 step5592
  have step5763 (X0 X2 : G) :  (X2 ◇ X0) = X2 := superpose step4756 step5691
  have step5770 (X0 X1 : G) :  (X0 ◇ X0) = X1 := superpose step4756 step5702
  have step5789 (X0 X1 : G) :  X0 = X1 := superpose step5763 step5770
  have step6301 (X0 : G) :  (sK0 ◇ sK1) ≠ X0 := superpose step5789 step10
  subsumption step6301 step5789


@[equational_result]
theorem Finite.Equation677_and_Equation1249_implies_Equation3555 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation1249 G) : Equation3555 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ (((X1 ◇ X1) ◇ X0) ◇ X1)) = X0 := mod_symm (h ..)
  have step10 : (sK0 ◇ sK1) ≠ (sK1 ◇ ((sK1 ◇ sK0) ◇ sK0)) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step17 (X0 X1 : G) :  (((X1 ◇ X1) ◇ X0) ◇ X1) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose step9 step12
  have step18 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step20 (X0 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ X0) = (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ X0)) := superpose step12 step9
  have step22 (X0 X1 X2 : G) :  (((X0 ◇ X0) ◇ X1) ◇ X0) = (((X2 ◇ X2) ◇ X1) ◇ X2) := superpose step17 step17
  have step24 (X0 X1 : G) :  ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((((X1 ◇ X1) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X1 ◇ X1) ◇ X0))) = X1 := superpose step17 step12
  have step28 (X0 X1 : G) :  ((X1 ◇ X1) ◇ X1) = ((((X0 ◇ X0) ◇ X1) ◇ X0) ◇ ((X1 ◇ (((X0 ◇ X0) ◇ X1) ◇ X0)) ◇ X1)) := superpose step17 step12
  have step30 (X0 X1 : G) :  ((X1 ◇ X1) ◇ X1) = ((((X0 ◇ X0) ◇ X1) ◇ X0) ◇ (X1 ◇ X1)) := superpose step9 step28
  have step44 (X0 X1 : G) :  (X0 ◇ X0) = (((X1 ◇ X1) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ X1) := superpose step12 step22
  have step49 (X0 X1 X2 : G) :  (((X2 ◇ X2) ◇ X1) ◇ X2) = ((((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ X0) ◇ (X1 ◇ X1)) := superpose step22 step22
  have step80 (X0 X1 : G) :  ((X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) ◇ (((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)))) ◇ (X1 ◇ (X1 ◇ X0)))) = X1 := superpose step18 step12
  have step86 (X0 X1 : G) :  (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) = (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ ((X1 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) ◇ X1)) := superpose step18 step12
  have step90 (X0 : G) :  ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) = ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) := superpose step12 step30
  have step111 (X0 : G) :  (X0 ◇ X0) = (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) := superpose step20 step11
  have step445 (X0 X1 : G) :  (((X1 ◇ X1) ◇ X0) ◇ X1) = (((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0)) := superpose step17 step49
  have step1213 (X0 : G) :  (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) = ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ ((X0 ◇ X0) ◇ (((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) := superpose step44 step24
  have step1255 (X0 : G) :  (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) = ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) ◇ ((X0 ◇ X0) ◇ (((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))))) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) := superpose step90 step1213
  have step1266 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) := superpose step111 step1255
  have step4082 (X0 : G) :  (X0 ◇ X0) = ((((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) ◇ (X0 ◇ X0))) ◇ ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) ◇ (X0 ◇ X0)))) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) := superpose step1266 step80
  have step4093 (X0 : G) :  (X0 ◇ X0) = ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) := superpose step12 step4082
  have step4121 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose step12 step4093
  have step4282 (X0 : G) :  ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) = (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) := superpose step4121 step86
  have step4284 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose step4121 step12
  have step4317 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose step12 step4282
  have step4593 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) = ((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) := superpose step4284 step20
  have step4596 (X0 X1 : G) :  (X0 ◇ X0) = ((X1 ◇ ((X1 ◇ X1) ◇ X1)) ◇ (((X0 ◇ X1) ◇ (X1 ◇ ((X1 ◇ X1) ◇ X1))) ◇ (X0 ◇ X1))) := superpose step4284 step24
  have step4630 (X0 : G) :  ((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ ((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0))))) = X0 := superpose step4284 step111
  have step4659 (X0 X1 : G) :  (((X1 ◇ X1) ◇ (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ (X1 ◇ X1))) ◇ (X1 ◇ X1)) = ((X0 ◇ X1) ◇ (X0 ◇ X0)) := superpose step4284 step445
  have step4685 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose step4284 step30
  have step4696 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) := superpose step4284 step445
  have step4747 (X0 X1 : G) :  ((X1 ◇ X1) ◇ (X1 ◇ X1)) = ((X0 ◇ X1) ◇ (X0 ◇ X0)) := superpose step4696 step4659
  have step4769 (X0 : G) :  (X0 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose step4317 step4630
  have step4794 (X0 X1 : G) :  (X0 ◇ X0) = ((X1 ◇ (X1 ◇ (X1 ◇ X1))) ◇ (((X0 ◇ X1) ◇ (X1 ◇ (X1 ◇ (X1 ◇ X1)))) ◇ (X0 ◇ X1))) := superpose step4685 step4596
  have step4795 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step4317 step4593
  have step4828 (X0 X1 : G) :  ((X0 ◇ X1) ◇ (X0 ◇ X0)) = X1 := superpose step4284 step4747
  have step4849 (X0 X1 : G) :  (X0 ◇ X0) = (X1 ◇ (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1))) := superpose step4769 step4794
  have step4870 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X0) = X1 := superpose step4795 step4828
  have step4888 (X0 X1 : G) :  (X1 ◇ (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1))) = X0 := superpose step4795 step4849
  have step4915 (X0 X1 : G) :  (X1 ◇ X1) = X0 := superpose step4870 step4888
  have step6448 (X0 : G) :  (sK0 ◇ sK1) ≠ (X0 ◇ X0) := superpose step4915 step10
  subsumption step6448 step4915


@[equational_result]
theorem Finite.Equation677_and_Equation1249_implies_Equation3924 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation1249 G) : Equation3924 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ (((X1 ◇ X1) ◇ X0) ◇ X1)) = X0 := mod_symm (h ..)
  have step10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step17 (X0 X1 : G) :  (((X1 ◇ X1) ◇ X0) ◇ X1) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose step9 step12
  have step18 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step20 (X0 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ X0) = (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ X0)) := superpose step12 step9
  have step22 (X0 X1 X2 : G) :  (((X0 ◇ X0) ◇ X1) ◇ X0) = (((X2 ◇ X2) ◇ X1) ◇ X2) := superpose step17 step17
  have step24 (X0 X1 : G) :  ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((((X1 ◇ X1) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X1 ◇ X1) ◇ X0))) = X1 := superpose step17 step12
  have step27 (X0 X1 : G) :  ((X1 ◇ X1) ◇ X1) = ((((X0 ◇ X0) ◇ X1) ◇ X0) ◇ ((X1 ◇ (((X0 ◇ X0) ◇ X1) ◇ X0)) ◇ X1)) := superpose step17 step12
  have step30 (X0 X1 : G) :  ((X1 ◇ X1) ◇ X1) = ((((X0 ◇ X0) ◇ X1) ◇ X0) ◇ (X1 ◇ X1)) := superpose step9 step27
  have step44 (X0 X1 : G) :  (X0 ◇ X0) = (((X1 ◇ X1) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ X1) := superpose step12 step22
  have step45 (X0 X1 X2 : G) :  ((X0 ◇ X0) ◇ X0) = (((X1 ◇ X1) ◇ (((X2 ◇ X2) ◇ (X0 ◇ X0)) ◇ X2)) ◇ X1) := superpose step9 step22
  have step47 (X0 X1 X2 : G) :  (((X1 ◇ X1) ◇ (X0 ◇ (((X2 ◇ X2) ◇ X0) ◇ (X2 ◇ X2)))) ◇ X1) = (X0 ◇ X2) := superpose step11 step22
  have step80 (X0 X1 : G) :  ((X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) ◇ (((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)))) ◇ (X1 ◇ (X1 ◇ X0)))) = X1 := superpose step18 step12
  have step83 (X0 X1 : G) :  (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) = (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ ((X1 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) ◇ X1)) := superpose step18 step12
  have step90 (X0 : G) :  ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) = ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) := superpose step12 step30
  have step111 (X0 : G) :  (X0 ◇ X0) = (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) := superpose step20 step11
  have step272 (X0 X1 X2 X3 : G) :  (((X3 ◇ X3) ◇ X2) ◇ X3) = ((((X0 ◇ X0) ◇ (((X1 ◇ X1) ◇ (X2 ◇ X2)) ◇ X1)) ◇ X0) ◇ X2) := superpose step45 step22
  have step1213 (X0 : G) :  (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) = ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ ((X0 ◇ X0) ◇ (((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) := superpose step44 step24
  have step1255 (X0 : G) :  (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) = ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) ◇ ((X0 ◇ X0) ◇ (((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))))) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) := superpose step90 step1213
  have step1266 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) := superpose step111 step1255
  have step4082 (X0 : G) :  (X0 ◇ X0) = ((((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) ◇ (X0 ◇ X0))) ◇ ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) ◇ (X0 ◇ X0)))) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) := superpose step1266 step80
  have step4093 (X0 : G) :  (X0 ◇ X0) = ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) := superpose step12 step4082
  have step4121 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose step12 step4093
  have step4282 (X0 : G) :  ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) = (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) := superpose step4121 step83
  have step4284 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose step4121 step12
  have step4286 (X0 X1 : G) :  (X0 ◇ X0) = (((X1 ◇ X1) ◇ (X0 ◇ X0)) ◇ X1) := superpose step4121 step44
  have step4317 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose step12 step4282
  have step4618 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) = ((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) := superpose step4284 step20
  have step4633 (X0 X1 : G) :  (((X1 ◇ X1) ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0))) ◇ X1) = X0 := superpose step4284 step44
  have step4674 (X0 X1 X2 X3 : G) :  ((((X2 ◇ X2) ◇ (((X3 ◇ X3) ◇ (X1 ◇ X1)) ◇ X3)) ◇ X2) ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ X0)) := superpose step4284 step272
  have step4734 (X0 X1 X2 : G) :  ((((X2 ◇ X2) ◇ (X1 ◇ X1)) ◇ X2) ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ X0)) := superpose step4286 step4674
  have step4751 (X0 X1 : G) :  (((X1 ◇ X1) ◇ X0) ◇ X1) = X0 := superpose step4317 step4633
  have step4757 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step4317 step4618
  have step4796 (X0 X1 : G) :  ((X1 ◇ X1) ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ X0)) := superpose step4286 step4734
  have step4827 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X0) = ((X1 ◇ X1) ◇ X1) := superpose step4757 step4796
  have step4850 (X0 X1 : G) :  (X1 ◇ X1) = ((X0 ◇ X1) ◇ X0) := superpose step4757 step4827
  have step4866 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X0) = X1 := superpose step4757 step4850
  have step5314 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ ((((X1 ◇ X1) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X1 ◇ X1) ◇ X0))) = X1 := superpose step4757 step24
  have step5330 (X0 X1 X2 : G) :  (((X1 ◇ X1) ◇ (X2 ◇ ((X0 ◇ X2) ◇ X0))) ◇ X1) = (X2 ◇ X0) := superpose step4757 step47
  have step5579 (X0 X2 : G) :  (X2 ◇ ((X0 ◇ X2) ◇ X0)) = (X2 ◇ X0) := superpose step4751 step5330
  have step5593 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) = X1 := superpose step4866 step5314
  have step5692 (X0 X2 : G) :  (X2 ◇ X2) = (X2 ◇ X0) := superpose step4866 step5579
  have step5703 (X0 X1 : G) :  (X0 ◇ (X0 ◇ X0)) = X1 := superpose step4757 step5593
  have step5764 (X0 X2 : G) :  (X2 ◇ X0) = X2 := superpose step4757 step5692
  have step5771 (X0 X1 : G) :  (X0 ◇ X0) = X1 := superpose step4757 step5703
  have step5790 (X0 X1 : G) :  X0 = X1 := superpose step5764 step5771
  have step6736 (X0 : G) :  (X0 ◇ sK1) ≠ ((X0 ◇ (sK1 ◇ X0)) ◇ X0) := superpose step5790 step10
  subsumption step6736 step5790


@[equational_result]
theorem Finite.Equation677_and_Equation1249_implies_Equation3961 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation1249 G) : Equation3961 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ (((X1 ◇ X1) ◇ X0) ◇ X1)) = X0 := mod_symm (h ..)
  have step10 : (sK0 ◇ sK1) ≠ ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK0) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step17 (X0 X1 : G) :  (((X1 ◇ X1) ◇ X0) ◇ X1) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose step9 step12
  have step18 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step20 (X0 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ X0) = (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ X0)) := superpose step12 step9
  have step22 (X0 X1 X2 : G) :  (((X0 ◇ X0) ◇ X1) ◇ X0) = (((X2 ◇ X2) ◇ X1) ◇ X2) := superpose step17 step17
  have step24 (X0 X1 : G) :  ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((((X1 ◇ X1) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X1 ◇ X1) ◇ X0))) = X1 := superpose step17 step12
  have step28 (X0 X1 : G) :  ((X1 ◇ X1) ◇ X1) = ((((X0 ◇ X0) ◇ X1) ◇ X0) ◇ ((X1 ◇ (((X0 ◇ X0) ◇ X1) ◇ X0)) ◇ X1)) := superpose step17 step12
  have step30 (X0 X1 : G) :  ((X1 ◇ X1) ◇ X1) = ((((X0 ◇ X0) ◇ X1) ◇ X0) ◇ (X1 ◇ X1)) := superpose step9 step28
  have step44 (X0 X1 : G) :  (X0 ◇ X0) = (((X1 ◇ X1) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ X1) := superpose step12 step22
  have step45 (X0 X1 X2 : G) :  ((X0 ◇ X0) ◇ X0) = (((X1 ◇ X1) ◇ (((X2 ◇ X2) ◇ (X0 ◇ X0)) ◇ X2)) ◇ X1) := superpose step9 step22
  have step47 (X0 X1 X2 : G) :  (((X1 ◇ X1) ◇ (X0 ◇ (((X2 ◇ X2) ◇ X0) ◇ (X2 ◇ X2)))) ◇ X1) = (X0 ◇ X2) := superpose step11 step22
  have step80 (X0 X1 : G) :  ((X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) ◇ (((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)))) ◇ (X1 ◇ (X1 ◇ X0)))) = X1 := superpose step18 step12
  have step86 (X0 X1 : G) :  (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) = (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ ((X1 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) ◇ X1)) := superpose step18 step12
  have step90 (X0 : G) :  ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) = ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) := superpose step12 step30
  have step111 (X0 : G) :  (X0 ◇ X0) = (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) := superpose step20 step11
  have step272 (X0 X1 X2 X3 : G) :  (((X3 ◇ X3) ◇ X2) ◇ X3) = ((((X0 ◇ X0) ◇ (((X1 ◇ X1) ◇ (X2 ◇ X2)) ◇ X1)) ◇ X0) ◇ X2) := superpose step45 step22
  have step1213 (X0 : G) :  (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) = ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ ((X0 ◇ X0) ◇ (((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) := superpose step44 step24
  have step1255 (X0 : G) :  (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) = ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) ◇ ((X0 ◇ X0) ◇ (((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))))) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) := superpose step90 step1213
  have step1266 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) := superpose step111 step1255
  have step4082 (X0 : G) :  (X0 ◇ X0) = ((((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) ◇ (X0 ◇ X0))) ◇ ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) ◇ (X0 ◇ X0)))) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) := superpose step1266 step80
  have step4093 (X0 : G) :  (X0 ◇ X0) = ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) := superpose step12 step4082
  have step4121 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose step12 step4093
  have step4282 (X0 : G) :  ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) = (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) := superpose step4121 step86
  have step4284 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose step4121 step12
  have step4286 (X0 X1 : G) :  (X0 ◇ X0) = (((X1 ◇ X1) ◇ (X0 ◇ X0)) ◇ X1) := superpose step4121 step44
  have step4317 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose step12 step4282
  have step4618 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) = ((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) := superpose step4284 step20
  have step4633 (X0 X1 : G) :  (((X1 ◇ X1) ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0))) ◇ X1) = X0 := superpose step4284 step44
  have step4674 (X0 X1 X2 X3 : G) :  ((((X2 ◇ X2) ◇ (((X3 ◇ X3) ◇ (X1 ◇ X1)) ◇ X3)) ◇ X2) ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ X0)) := superpose step4284 step272
  have step4734 (X0 X1 X2 : G) :  ((((X2 ◇ X2) ◇ (X1 ◇ X1)) ◇ X2) ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ X0)) := superpose step4286 step4674
  have step4751 (X0 X1 : G) :  (((X1 ◇ X1) ◇ X0) ◇ X1) = X0 := superpose step4317 step4633
  have step4757 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step4317 step4618
  have step4796 (X0 X1 : G) :  ((X1 ◇ X1) ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ X0)) := superpose step4286 step4734
  have step4827 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X0) = ((X1 ◇ X1) ◇ X1) := superpose step4757 step4796
  have step4850 (X0 X1 : G) :  (X1 ◇ X1) = ((X0 ◇ X1) ◇ X0) := superpose step4757 step4827
  have step4866 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X0) = X1 := superpose step4757 step4850
  have step5365 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ ((((X1 ◇ X1) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X1 ◇ X1) ◇ X0))) = X1 := superpose step4757 step24
  have step5381 (X0 X1 X2 : G) :  (((X1 ◇ X1) ◇ (X2 ◇ ((X0 ◇ X2) ◇ X0))) ◇ X1) = (X2 ◇ X0) := superpose step4757 step47
  have step5534 (X0 X2 : G) :  (X2 ◇ ((X0 ◇ X2) ◇ X0)) = (X2 ◇ X0) := superpose step4751 step5381
  have step5548 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) = X1 := superpose step4866 step5365
  have step5664 (X0 X2 : G) :  (X2 ◇ X2) = (X2 ◇ X0) := superpose step4866 step5534
  have step5675 (X0 X1 : G) :  (X0 ◇ (X0 ◇ X0)) = X1 := superpose step4757 step5548
  have step5751 (X0 X2 : G) :  (X2 ◇ X0) = X2 := superpose step4757 step5664
  have step5758 (X0 X1 : G) :  (X0 ◇ X0) = X1 := superpose step4757 step5675
  have step5784 (X0 X1 : G) :  X0 = X1 := superpose step5751 step5758
  have step6732 (X0 : G) :  (X0 ◇ sK1) ≠ ((sK1 ◇ (sK1 ◇ X0)) ◇ X0) := superpose step5784 step10
  subsumption step6732 step5784


@[equational_result]
theorem Finite.Equation677_and_Equation1249_implies_Equation4093 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation1249 G) : Equation4093 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ (((X1 ◇ X1) ◇ X0) ◇ X1)) = X0 := mod_symm (h ..)
  have step10 : (sK0 ◇ sK0) ≠ (((sK1 ◇ sK1) ◇ sK1) ◇ sK0) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step17 (X0 X1 : G) :  (((X1 ◇ X1) ◇ X0) ◇ X1) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose step9 step12
  have step18 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step20 (X0 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ X0) = (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ X0)) := superpose step12 step9
  have step22 (X0 X1 X2 : G) :  (((X0 ◇ X0) ◇ X1) ◇ X0) = (((X2 ◇ X2) ◇ X1) ◇ X2) := superpose step17 step17
  have step24 (X0 X1 : G) :  ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((((X1 ◇ X1) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X1 ◇ X1) ◇ X0))) = X1 := superpose step17 step12
  have step28 (X0 X1 : G) :  ((X1 ◇ X1) ◇ X1) = ((((X0 ◇ X0) ◇ X1) ◇ X0) ◇ ((X1 ◇ (((X0 ◇ X0) ◇ X1) ◇ X0)) ◇ X1)) := superpose step17 step12
  have step30 (X0 X1 : G) :  ((X1 ◇ X1) ◇ X1) = ((((X0 ◇ X0) ◇ X1) ◇ X0) ◇ (X1 ◇ X1)) := superpose step9 step28
  have step44 (X0 X1 : G) :  (X0 ◇ X0) = (((X1 ◇ X1) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ X1) := superpose step12 step22
  have step49 (X0 X1 X2 : G) :  (((X2 ◇ X2) ◇ X1) ◇ X2) = ((((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ X0) ◇ (X1 ◇ X1)) := superpose step22 step22
  have step80 (X0 X1 : G) :  ((X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) ◇ (((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)))) ◇ (X1 ◇ (X1 ◇ X0)))) = X1 := superpose step18 step12
  have step86 (X0 X1 : G) :  (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) = (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ ((X1 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) ◇ X1)) := superpose step18 step12
  have step90 (X0 : G) :  ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) = ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) := superpose step12 step30
  have step111 (X0 : G) :  (X0 ◇ X0) = (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) := superpose step20 step11
  have step445 (X0 X1 : G) :  (((X1 ◇ X1) ◇ X0) ◇ X1) = (((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0)) := superpose step17 step49
  have step1213 (X0 : G) :  (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) = ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ ((X0 ◇ X0) ◇ (((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) := superpose step44 step24
  have step1255 (X0 : G) :  (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) = ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) ◇ ((X0 ◇ X0) ◇ (((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))))) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) := superpose step90 step1213
  have step1266 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) := superpose step111 step1255
  have step4082 (X0 : G) :  (X0 ◇ X0) = ((((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) ◇ (X0 ◇ X0))) ◇ ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) ◇ (X0 ◇ X0)))) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) := superpose step1266 step80
  have step4093 (X0 : G) :  (X0 ◇ X0) = ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) := superpose step12 step4082
  have step4121 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose step12 step4093
  have step4282 (X0 : G) :  ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) = (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) := superpose step4121 step86
  have step4284 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose step4121 step12
  have step4317 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose step12 step4282
  have step4593 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) = ((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) := superpose step4284 step20
  have step4596 (X0 X1 : G) :  (X0 ◇ X0) = ((X1 ◇ ((X1 ◇ X1) ◇ X1)) ◇ (((X0 ◇ X1) ◇ (X1 ◇ ((X1 ◇ X1) ◇ X1))) ◇ (X0 ◇ X1))) := superpose step4284 step24
  have step4630 (X0 : G) :  ((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ ((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0))))) = X0 := superpose step4284 step111
  have step4659 (X0 X1 : G) :  (((X1 ◇ X1) ◇ (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ (X1 ◇ X1))) ◇ (X1 ◇ X1)) = ((X0 ◇ X1) ◇ (X0 ◇ X0)) := superpose step4284 step445
  have step4685 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose step4284 step30
  have step4696 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) := superpose step4284 step445
  have step4747 (X0 X1 : G) :  ((X1 ◇ X1) ◇ (X1 ◇ X1)) = ((X0 ◇ X1) ◇ (X0 ◇ X0)) := superpose step4696 step4659
  have step4769 (X0 : G) :  (X0 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose step4317 step4630
  have step4794 (X0 X1 : G) :  (X0 ◇ X0) = ((X1 ◇ (X1 ◇ (X1 ◇ X1))) ◇ (((X0 ◇ X1) ◇ (X1 ◇ (X1 ◇ (X1 ◇ X1)))) ◇ (X0 ◇ X1))) := superpose step4685 step4596
  have step4795 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step4317 step4593
  have step4828 (X0 X1 : G) :  ((X0 ◇ X1) ◇ (X0 ◇ X0)) = X1 := superpose step4284 step4747
  have step4849 (X0 X1 : G) :  (X0 ◇ X0) = (X1 ◇ (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1))) := superpose step4769 step4794
  have step4870 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X0) = X1 := superpose step4795 step4828
  have step4888 (X0 X1 : G) :  (X1 ◇ (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1))) = X0 := superpose step4795 step4849
  have step4915 (X0 X1 : G) :  (X1 ◇ X1) = X0 := superpose step4870 step4888
  have step5440 : (sK0 ◇ sK0) ≠ ((sK1 ◇ sK1) ◇ sK0) := superpose step4795 step10
  subsumption step5440 step4915


@[equational_result]
theorem Finite.Equation677_and_Equation1249_implies_Equation4131 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation1249 G) : Equation4131 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ (((X1 ◇ X1) ◇ X0) ◇ X1)) = X0 := mod_symm (h ..)
  have step10 : (sK0 ◇ sK1) ≠ (((sK0 ◇ sK1) ◇ sK1) ◇ sK1) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step17 (X0 X1 : G) :  (((X1 ◇ X1) ◇ X0) ◇ X1) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose step9 step12
  have step18 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step20 (X0 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ X0) = (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ X0)) := superpose step12 step9
  have step22 (X0 X1 X2 : G) :  (((X0 ◇ X0) ◇ X1) ◇ X0) = (((X2 ◇ X2) ◇ X1) ◇ X2) := superpose step17 step17
  have step24 (X0 X1 : G) :  ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((((X1 ◇ X1) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X1 ◇ X1) ◇ X0))) = X1 := superpose step17 step12
  have step28 (X0 X1 : G) :  ((X1 ◇ X1) ◇ X1) = ((((X0 ◇ X0) ◇ X1) ◇ X0) ◇ ((X1 ◇ (((X0 ◇ X0) ◇ X1) ◇ X0)) ◇ X1)) := superpose step17 step12
  have step30 (X0 X1 : G) :  ((X1 ◇ X1) ◇ X1) = ((((X0 ◇ X0) ◇ X1) ◇ X0) ◇ (X1 ◇ X1)) := superpose step9 step28
  have step44 (X0 X1 : G) :  (X0 ◇ X0) = (((X1 ◇ X1) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ X1) := superpose step12 step22
  have step49 (X0 X1 X2 : G) :  (((X2 ◇ X2) ◇ X1) ◇ X2) = ((((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ X0) ◇ (X1 ◇ X1)) := superpose step22 step22
  have step80 (X0 X1 : G) :  ((X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) ◇ (((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)))) ◇ (X1 ◇ (X1 ◇ X0)))) = X1 := superpose step18 step12
  have step86 (X0 X1 : G) :  (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) = (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ ((X1 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) ◇ X1)) := superpose step18 step12
  have step90 (X0 : G) :  ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) = ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) := superpose step12 step30
  have step111 (X0 : G) :  (X0 ◇ X0) = (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) := superpose step20 step11
  have step445 (X0 X1 : G) :  (((X1 ◇ X1) ◇ X0) ◇ X1) = (((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0)) := superpose step17 step49
  have step1213 (X0 : G) :  (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) = ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ ((X0 ◇ X0) ◇ (((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) := superpose step44 step24
  have step1255 (X0 : G) :  (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) = ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) ◇ ((X0 ◇ X0) ◇ (((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))))) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) := superpose step90 step1213
  have step1266 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) := superpose step111 step1255
  have step4082 (X0 : G) :  (X0 ◇ X0) = ((((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) ◇ (X0 ◇ X0))) ◇ ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) ◇ (X0 ◇ X0)))) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) := superpose step1266 step80
  have step4093 (X0 : G) :  (X0 ◇ X0) = ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) := superpose step12 step4082
  have step4121 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose step12 step4093
  have step4282 (X0 : G) :  ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) = (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) := superpose step4121 step86
  have step4284 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose step4121 step12
  have step4317 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose step12 step4282
  have step4593 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) = ((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) := superpose step4284 step20
  have step4596 (X0 X1 : G) :  (X0 ◇ X0) = ((X1 ◇ ((X1 ◇ X1) ◇ X1)) ◇ (((X0 ◇ X1) ◇ (X1 ◇ ((X1 ◇ X1) ◇ X1))) ◇ (X0 ◇ X1))) := superpose step4284 step24
  have step4630 (X0 : G) :  ((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ ((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0))))) = X0 := superpose step4284 step111
  have step4659 (X0 X1 : G) :  (((X1 ◇ X1) ◇ (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ (X1 ◇ X1))) ◇ (X1 ◇ X1)) = ((X0 ◇ X1) ◇ (X0 ◇ X0)) := superpose step4284 step445
  have step4685 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose step4284 step30
  have step4696 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) := superpose step4284 step445
  have step4747 (X0 X1 : G) :  ((X1 ◇ X1) ◇ (X1 ◇ X1)) = ((X0 ◇ X1) ◇ (X0 ◇ X0)) := superpose step4696 step4659
  have step4769 (X0 : G) :  (X0 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose step4317 step4630
  have step4794 (X0 X1 : G) :  (X0 ◇ X0) = ((X1 ◇ (X1 ◇ (X1 ◇ X1))) ◇ (((X0 ◇ X1) ◇ (X1 ◇ (X1 ◇ (X1 ◇ X1)))) ◇ (X0 ◇ X1))) := superpose step4685 step4596
  have step4795 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step4317 step4593
  have step4828 (X0 X1 : G) :  ((X0 ◇ X1) ◇ (X0 ◇ X0)) = X1 := superpose step4284 step4747
  have step4849 (X0 X1 : G) :  (X0 ◇ X0) = (X1 ◇ (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1))) := superpose step4769 step4794
  have step4870 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X0) = X1 := superpose step4795 step4828
  have step4888 (X0 X1 : G) :  (X1 ◇ (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1))) = X0 := superpose step4795 step4849
  have step4915 (X0 X1 : G) :  (X1 ◇ X1) = X0 := superpose step4870 step4888
  have step6550 (X0 : G) :  (sK0 ◇ sK1) ≠ (X0 ◇ X0) := superpose step4915 step10
  subsumption step6550 step4915


@[equational_result]
theorem Finite.Equation677_and_Equation1249_implies_Equation4154 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation1249 G) : Equation4154 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ (((X1 ◇ X1) ◇ X0) ◇ X1)) = X0 := mod_symm (h ..)
  have step10 : (sK0 ◇ sK1) ≠ (((sK1 ◇ sK0) ◇ sK0) ◇ sK0) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step17 (X0 X1 : G) :  (((X1 ◇ X1) ◇ X0) ◇ X1) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose step9 step12
  have step18 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step20 (X0 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ X0) = (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ X0)) := superpose step12 step9
  have step22 (X0 X1 X2 : G) :  (((X0 ◇ X0) ◇ X1) ◇ X0) = (((X2 ◇ X2) ◇ X1) ◇ X2) := superpose step17 step17
  have step24 (X0 X1 : G) :  ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((((X1 ◇ X1) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X1 ◇ X1) ◇ X0))) = X1 := superpose step17 step12
  have step28 (X0 X1 : G) :  ((X1 ◇ X1) ◇ X1) = ((((X0 ◇ X0) ◇ X1) ◇ X0) ◇ ((X1 ◇ (((X0 ◇ X0) ◇ X1) ◇ X0)) ◇ X1)) := superpose step17 step12
  have step30 (X0 X1 : G) :  ((X1 ◇ X1) ◇ X1) = ((((X0 ◇ X0) ◇ X1) ◇ X0) ◇ (X1 ◇ X1)) := superpose step9 step28
  have step44 (X0 X1 : G) :  (X0 ◇ X0) = (((X1 ◇ X1) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ X1) := superpose step12 step22
  have step49 (X0 X1 X2 : G) :  (((X2 ◇ X2) ◇ X1) ◇ X2) = ((((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ X0) ◇ (X1 ◇ X1)) := superpose step22 step22
  have step80 (X0 X1 : G) :  ((X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) ◇ (((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)))) ◇ (X1 ◇ (X1 ◇ X0)))) = X1 := superpose step18 step12
  have step86 (X0 X1 : G) :  (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) = (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ ((X1 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) ◇ X1)) := superpose step18 step12
  have step90 (X0 : G) :  ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) = ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) := superpose step12 step30
  have step111 (X0 : G) :  (X0 ◇ X0) = (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) := superpose step20 step11
  have step445 (X0 X1 : G) :  (((X1 ◇ X1) ◇ X0) ◇ X1) = (((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0)) := superpose step17 step49
  have step1213 (X0 : G) :  (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) = ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ ((X0 ◇ X0) ◇ (((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) := superpose step44 step24
  have step1255 (X0 : G) :  (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) = ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) ◇ ((X0 ◇ X0) ◇ (((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))))) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) := superpose step90 step1213
  have step1266 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) := superpose step111 step1255
  have step4082 (X0 : G) :  (X0 ◇ X0) = ((((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) ◇ (X0 ◇ X0))) ◇ ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) ◇ (X0 ◇ X0)))) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) := superpose step1266 step80
  have step4093 (X0 : G) :  (X0 ◇ X0) = ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) := superpose step12 step4082
  have step4121 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose step12 step4093
  have step4282 (X0 : G) :  ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) = (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) := superpose step4121 step86
  have step4284 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose step4121 step12
  have step4317 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose step12 step4282
  have step4593 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) = ((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) := superpose step4284 step20
  have step4596 (X0 X1 : G) :  (X0 ◇ X0) = ((X1 ◇ ((X1 ◇ X1) ◇ X1)) ◇ (((X0 ◇ X1) ◇ (X1 ◇ ((X1 ◇ X1) ◇ X1))) ◇ (X0 ◇ X1))) := superpose step4284 step24
  have step4630 (X0 : G) :  ((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ ((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0))))) = X0 := superpose step4284 step111
  have step4659 (X0 X1 : G) :  (((X1 ◇ X1) ◇ (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ (X1 ◇ X1))) ◇ (X1 ◇ X1)) = ((X0 ◇ X1) ◇ (X0 ◇ X0)) := superpose step4284 step445
  have step4685 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose step4284 step30
  have step4696 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) := superpose step4284 step445
  have step4747 (X0 X1 : G) :  ((X1 ◇ X1) ◇ (X1 ◇ X1)) = ((X0 ◇ X1) ◇ (X0 ◇ X0)) := superpose step4696 step4659
  have step4769 (X0 : G) :  (X0 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose step4317 step4630
  have step4794 (X0 X1 : G) :  (X0 ◇ X0) = ((X1 ◇ (X1 ◇ (X1 ◇ X1))) ◇ (((X0 ◇ X1) ◇ (X1 ◇ (X1 ◇ (X1 ◇ X1)))) ◇ (X0 ◇ X1))) := superpose step4685 step4596
  have step4795 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step4317 step4593
  have step4828 (X0 X1 : G) :  ((X0 ◇ X1) ◇ (X0 ◇ X0)) = X1 := superpose step4284 step4747
  have step4849 (X0 X1 : G) :  (X0 ◇ X0) = (X1 ◇ (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1))) := superpose step4769 step4794
  have step4870 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X0) = X1 := superpose step4795 step4828
  have step4888 (X0 X1 : G) :  (X1 ◇ (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1))) = X0 := superpose step4795 step4849
  have step4915 (X0 X1 : G) :  (X1 ◇ X1) = X0 := superpose step4870 step4888
  have step6550 (X0 : G) :  (sK0 ◇ sK1) ≠ (X0 ◇ X0) := superpose step4915 step10
  subsumption step6550 step4915


@[equational_result]
theorem Finite.Equation677_and_Equation1249_implies_Equation4362 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation1249 G) : Equation4362 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ (((X1 ◇ X1) ◇ X0) ◇ X1)) = X0 := mod_symm (h ..)
  have step10 : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK1 ◇ (sK0 ◇ sK2)) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step17 (X0 X1 : G) :  (((X1 ◇ X1) ◇ X0) ◇ X1) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose step9 step12
  have step18 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step20 (X0 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ X0) = (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ X0)) := superpose step12 step9
  have step22 (X0 X1 X2 : G) :  (((X0 ◇ X0) ◇ X1) ◇ X0) = (((X2 ◇ X2) ◇ X1) ◇ X2) := superpose step17 step17
  have step24 (X0 X1 : G) :  ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((((X1 ◇ X1) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X1 ◇ X1) ◇ X0))) = X1 := superpose step17 step12
  have step27 (X0 X1 : G) :  ((X1 ◇ X1) ◇ X1) = ((((X0 ◇ X0) ◇ X1) ◇ X0) ◇ ((X1 ◇ (((X0 ◇ X0) ◇ X1) ◇ X0)) ◇ X1)) := superpose step17 step12
  have step30 (X0 X1 : G) :  ((X1 ◇ X1) ◇ X1) = ((((X0 ◇ X0) ◇ X1) ◇ X0) ◇ (X1 ◇ X1)) := superpose step9 step27
  have step44 (X0 X1 : G) :  (X0 ◇ X0) = (((X1 ◇ X1) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ X1) := superpose step12 step22
  have step45 (X0 X1 X2 : G) :  ((X0 ◇ X0) ◇ X0) = (((X1 ◇ X1) ◇ (((X2 ◇ X2) ◇ (X0 ◇ X0)) ◇ X2)) ◇ X1) := superpose step9 step22
  have step47 (X0 X1 X2 : G) :  (X0 ◇ X2) = (((X1 ◇ X1) ◇ (X0 ◇ (((X2 ◇ X2) ◇ X0) ◇ (X2 ◇ X2)))) ◇ X1) := superpose step11 step22
  have step80 (X0 X1 : G) :  ((X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) ◇ (((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)))) ◇ (X1 ◇ (X1 ◇ X0)))) = X1 := superpose step18 step12
  have step83 (X0 X1 : G) :  (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) = (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ ((X1 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) ◇ X1)) := superpose step18 step12
  have step90 (X0 : G) :  ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) = ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) := superpose step12 step30
  have step111 (X0 : G) :  (X0 ◇ X0) = (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) := superpose step20 step11
  have step275 (X0 X1 X2 X3 : G) :  (((X3 ◇ X3) ◇ X2) ◇ X3) = (X2 ◇ (((X0 ◇ X0) ◇ (((X1 ◇ X1) ◇ (X2 ◇ X2)) ◇ X1)) ◇ X0)) := superpose step45 step17
  have step1229 (X0 : G) :  (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) = ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ ((X0 ◇ X0) ◇ (((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) := superpose step44 step24
  have step1271 (X0 : G) :  (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) = ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) ◇ ((X0 ◇ X0) ◇ (((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))))) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) := superpose step90 step1229
  have step1282 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) := superpose step111 step1271
  have step4081 (X0 : G) :  (X0 ◇ X0) = ((((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) ◇ (X0 ◇ X0))) ◇ ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) ◇ (X0 ◇ X0)))) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) := superpose step1282 step80
  have step4092 (X0 : G) :  (X0 ◇ X0) = ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) := superpose step12 step4081
  have step4120 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose step12 step4092
  have step4281 (X0 : G) :  ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) = (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) := superpose step4120 step83
  have step4283 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose step4120 step12
  have step4285 (X0 X1 : G) :  (X0 ◇ X0) = (((X1 ◇ X1) ◇ (X0 ◇ X0)) ◇ X1) := superpose step4120 step44
  have step4316 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose step12 step4281
  have step4617 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) = ((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) := superpose step4283 step20
  have step4632 (X0 X1 : G) :  (((X1 ◇ X1) ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0))) ◇ X1) = X0 := superpose step4283 step44
  have step4676 (X0 X1 X2 X3 : G) :  (X1 ◇ (((X2 ◇ X2) ◇ (((X3 ◇ X3) ◇ (X1 ◇ X1)) ◇ X3)) ◇ X2)) = ((X0 ◇ X1) ◇ (X0 ◇ X0)) := superpose step4283 step275
  have step4732 (X0 X1 X2 : G) :  ((X0 ◇ X1) ◇ (X0 ◇ X0)) = (X1 ◇ (((X2 ◇ X2) ◇ (X1 ◇ X1)) ◇ X2)) := superpose step4285 step4676
  have step4750 (X0 X1 : G) :  (((X1 ◇ X1) ◇ X0) ◇ X1) = X0 := superpose step4316 step4632
  have step4756 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step4316 step4617
  have step4795 (X0 X1 : G) :  (X1 ◇ (X1 ◇ X1)) = ((X0 ◇ X1) ◇ (X0 ◇ X0)) := superpose step4285 step4732
  have step4826 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X0) = (X1 ◇ (X1 ◇ X1)) := superpose step4756 step4795
  have step4849 (X0 X1 : G) :  (X1 ◇ X1) = ((X0 ◇ X1) ◇ X0) := superpose step4756 step4826
  have step4865 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X0) = X1 := superpose step4756 step4849
  have step5313 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ ((((X1 ◇ X1) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X1 ◇ X1) ◇ X0))) = X1 := superpose step4756 step24
  have step5329 (X0 X1 X2 : G) :  (X1 ◇ X0) = (((X2 ◇ X2) ◇ (X1 ◇ ((X0 ◇ X1) ◇ X0))) ◇ X2) := superpose step4756 step47
  have step5578 (X0 X1 : G) :  (X1 ◇ X0) = (X1 ◇ ((X0 ◇ X1) ◇ X0)) := superpose step4750 step5329
  have step5592 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) = X1 := superpose step4865 step5313
  have step5691 (X0 X1 : G) :  (X1 ◇ X1) = (X1 ◇ X0) := superpose step4865 step5578
  have step5702 (X0 X1 : G) :  (X0 ◇ (X0 ◇ X0)) = X1 := superpose step4756 step5592
  have step5763 (X0 X1 : G) :  (X1 ◇ X0) = X1 := superpose step4756 step5691
  have step5770 (X0 X1 : G) :  (X0 ◇ X0) = X1 := superpose step4756 step5702
  have step5789 (X0 X1 : G) :  X0 = X1 := superpose step5763 step5770
  have step6735 (X0 : G) :  (sK0 ◇ (sK1 ◇ X0)) ≠ (sK1 ◇ (sK0 ◇ X0)) := superpose step5789 step10
  subsumption step6735 step5789


@[equational_result]
theorem Finite.Equation677_and_Equation1249_implies_Equation4369 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation1249 G) : Equation4369 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ (((X1 ◇ X1) ◇ X0) ◇ X1)) = X0 := mod_symm (h ..)
  have step10 : (sK0 ◇ (sK1 ◇ sK2)) ≠ (sK2 ◇ (sK1 ◇ sK0)) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step17 (X0 X1 : G) :  (((X1 ◇ X1) ◇ X0) ◇ X1) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose step9 step12
  have step18 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step20 (X0 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ X0) = (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ X0)) := superpose step12 step9
  have step22 (X0 X1 X2 : G) :  (((X0 ◇ X0) ◇ X1) ◇ X0) = (((X2 ◇ X2) ◇ X1) ◇ X2) := superpose step17 step17
  have step24 (X0 X1 : G) :  ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((((X1 ◇ X1) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X1 ◇ X1) ◇ X0))) = X1 := superpose step17 step12
  have step27 (X0 X1 : G) :  ((X1 ◇ X1) ◇ X1) = ((((X0 ◇ X0) ◇ X1) ◇ X0) ◇ ((X1 ◇ (((X0 ◇ X0) ◇ X1) ◇ X0)) ◇ X1)) := superpose step17 step12
  have step30 (X0 X1 : G) :  ((X1 ◇ X1) ◇ X1) = ((((X0 ◇ X0) ◇ X1) ◇ X0) ◇ (X1 ◇ X1)) := superpose step9 step27
  have step44 (X0 X1 : G) :  (X0 ◇ X0) = (((X1 ◇ X1) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ X1) := superpose step12 step22
  have step45 (X0 X1 X2 : G) :  ((X0 ◇ X0) ◇ X0) = (((X1 ◇ X1) ◇ (((X2 ◇ X2) ◇ (X0 ◇ X0)) ◇ X2)) ◇ X1) := superpose step9 step22
  have step47 (X0 X1 X2 : G) :  (((X1 ◇ X1) ◇ (X0 ◇ (((X2 ◇ X2) ◇ X0) ◇ (X2 ◇ X2)))) ◇ X1) = (X0 ◇ X2) := superpose step11 step22
  have step80 (X0 X1 : G) :  ((X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) ◇ (((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)))) ◇ (X1 ◇ (X1 ◇ X0)))) = X1 := superpose step18 step12
  have step83 (X0 X1 : G) :  (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) = (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ ((X1 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) ◇ X1)) := superpose step18 step12
  have step90 (X0 : G) :  ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) = ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) := superpose step12 step30
  have step111 (X0 : G) :  (X0 ◇ X0) = (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) := superpose step20 step11
  have step275 (X0 X1 X2 X3 : G) :  (((X3 ◇ X3) ◇ X2) ◇ X3) = (X2 ◇ (((X0 ◇ X0) ◇ (((X1 ◇ X1) ◇ (X2 ◇ X2)) ◇ X1)) ◇ X0)) := superpose step45 step17
  have step1229 (X0 : G) :  (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) = ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ ((X0 ◇ X0) ◇ (((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) := superpose step44 step24
  have step1271 (X0 : G) :  (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) = ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) ◇ ((X0 ◇ X0) ◇ (((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))))) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) := superpose step90 step1229
  have step1282 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) := superpose step111 step1271
  have step4081 (X0 : G) :  (X0 ◇ X0) = ((((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) ◇ (X0 ◇ X0))) ◇ ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) ◇ (X0 ◇ X0)))) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) := superpose step1282 step80
  have step4092 (X0 : G) :  (X0 ◇ X0) = ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) := superpose step12 step4081
  have step4120 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose step12 step4092
  have step4281 (X0 : G) :  ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) = (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) := superpose step4120 step83
  have step4283 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose step4120 step12
  have step4285 (X0 X1 : G) :  (X0 ◇ X0) = (((X1 ◇ X1) ◇ (X0 ◇ X0)) ◇ X1) := superpose step4120 step44
  have step4316 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose step12 step4281
  have step4617 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) = ((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) := superpose step4283 step20
  have step4632 (X0 X1 : G) :  (((X1 ◇ X1) ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0))) ◇ X1) = X0 := superpose step4283 step44
  have step4676 (X0 X1 X2 X3 : G) :  (X1 ◇ (((X2 ◇ X2) ◇ (((X3 ◇ X3) ◇ (X1 ◇ X1)) ◇ X3)) ◇ X2)) = ((X0 ◇ X1) ◇ (X0 ◇ X0)) := superpose step4283 step275
  have step4732 (X0 X1 X2 : G) :  ((X0 ◇ X1) ◇ (X0 ◇ X0)) = (X1 ◇ (((X2 ◇ X2) ◇ (X1 ◇ X1)) ◇ X2)) := superpose step4285 step4676
  have step4750 (X0 X1 : G) :  (((X1 ◇ X1) ◇ X0) ◇ X1) = X0 := superpose step4316 step4632
  have step4756 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step4316 step4617
  have step4795 (X0 X1 : G) :  (X1 ◇ (X1 ◇ X1)) = ((X0 ◇ X1) ◇ (X0 ◇ X0)) := superpose step4285 step4732
  have step4826 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X0) = (X1 ◇ (X1 ◇ X1)) := superpose step4756 step4795
  have step4849 (X0 X1 : G) :  (X1 ◇ X1) = ((X0 ◇ X1) ◇ X0) := superpose step4756 step4826
  have step4865 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X0) = X1 := superpose step4756 step4849
  have step5313 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ ((((X1 ◇ X1) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X1 ◇ X1) ◇ X0))) = X1 := superpose step4756 step24
  have step5329 (X0 X1 X2 : G) :  (((X1 ◇ X1) ◇ (X2 ◇ ((X0 ◇ X2) ◇ X0))) ◇ X1) = (X2 ◇ X0) := superpose step4756 step47
  have step5578 (X0 X2 : G) :  (X2 ◇ ((X0 ◇ X2) ◇ X0)) = (X2 ◇ X0) := superpose step4750 step5329
  have step5592 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) = X1 := superpose step4865 step5313
  have step5691 (X0 X2 : G) :  (X2 ◇ X2) = (X2 ◇ X0) := superpose step4865 step5578
  have step5702 (X0 X1 : G) :  (X0 ◇ (X0 ◇ X0)) = X1 := superpose step4756 step5592
  have step5763 (X0 X2 : G) :  (X2 ◇ X0) = X2 := superpose step4756 step5691
  have step5770 (X0 X1 : G) :  (X0 ◇ X0) = X1 := superpose step4756 step5702
  have step5789 (X0 X1 : G) :  X0 = X1 := superpose step5763 step5770
  have step6735 (X0 : G) :  (sK0 ◇ (sK1 ◇ X0)) ≠ (X0 ◇ (sK1 ◇ sK0)) := superpose step5789 step10
  subsumption step6735 step5789


@[equational_result]
theorem Finite.Equation677_and_Equation1249_implies_Equation43 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation1249 G) : Equation43 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ (((X1 ◇ X1) ◇ X0) ◇ X1)) = X0 := mod_symm (h ..)
  have step10 : (sK0 ◇ sK1) ≠ (sK1 ◇ sK0) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step17 (X0 X1 : G) :  (((X1 ◇ X1) ◇ X0) ◇ X1) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose step9 step12
  have step18 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step20 (X0 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ X0) = (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ X0)) := superpose step12 step9
  have step22 (X0 X1 X2 : G) :  (((X0 ◇ X0) ◇ X1) ◇ X0) = (((X2 ◇ X2) ◇ X1) ◇ X2) := superpose step17 step17
  have step24 (X0 X1 : G) :  ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((((X1 ◇ X1) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X1 ◇ X1) ◇ X0))) = X1 := superpose step17 step12
  have step27 (X0 X1 : G) :  ((X1 ◇ X1) ◇ X1) = ((((X0 ◇ X0) ◇ X1) ◇ X0) ◇ ((X1 ◇ (((X0 ◇ X0) ◇ X1) ◇ X0)) ◇ X1)) := superpose step17 step12
  have step30 (X0 X1 : G) :  ((X1 ◇ X1) ◇ X1) = ((((X0 ◇ X0) ◇ X1) ◇ X0) ◇ (X1 ◇ X1)) := superpose step9 step27
  have step44 (X0 X1 : G) :  (X0 ◇ X0) = (((X1 ◇ X1) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ X1) := superpose step12 step22
  have step45 (X0 X1 X2 : G) :  ((X0 ◇ X0) ◇ X0) = (((X1 ◇ X1) ◇ (((X2 ◇ X2) ◇ (X0 ◇ X0)) ◇ X2)) ◇ X1) := superpose step9 step22
  have step47 (X0 X1 X2 : G) :  (((X1 ◇ X1) ◇ (X0 ◇ (((X2 ◇ X2) ◇ X0) ◇ (X2 ◇ X2)))) ◇ X1) = (X0 ◇ X2) := superpose step11 step22
  have step80 (X0 X1 : G) :  ((X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) ◇ (((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)))) ◇ (X1 ◇ (X1 ◇ X0)))) = X1 := superpose step18 step12
  have step83 (X0 X1 : G) :  (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) = (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ ((X1 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) ◇ X1)) := superpose step18 step12
  have step90 (X0 : G) :  ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) = ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) := superpose step12 step30
  have step111 (X0 : G) :  (X0 ◇ X0) = (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) := superpose step20 step11
  have step275 (X0 X1 X2 X3 : G) :  (((X3 ◇ X3) ◇ X2) ◇ X3) = (X2 ◇ (((X0 ◇ X0) ◇ (((X1 ◇ X1) ◇ (X2 ◇ X2)) ◇ X1)) ◇ X0)) := superpose step45 step17
  have step1229 (X0 : G) :  (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) = ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ ((X0 ◇ X0) ◇ (((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) := superpose step44 step24
  have step1271 (X0 : G) :  (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) = ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) ◇ ((X0 ◇ X0) ◇ (((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))))) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) := superpose step90 step1229
  have step1282 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) := superpose step111 step1271
  have step4081 (X0 : G) :  (X0 ◇ X0) = ((((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) ◇ (X0 ◇ X0))) ◇ ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) ◇ (X0 ◇ X0)))) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) := superpose step1282 step80
  have step4092 (X0 : G) :  (X0 ◇ X0) = ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) := superpose step12 step4081
  have step4120 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose step12 step4092
  have step4281 (X0 : G) :  ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) = (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) := superpose step4120 step83
  have step4283 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose step4120 step12
  have step4285 (X0 X1 : G) :  (X0 ◇ X0) = (((X1 ◇ X1) ◇ (X0 ◇ X0)) ◇ X1) := superpose step4120 step44
  have step4316 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose step12 step4281
  have step4617 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) = ((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) := superpose step4283 step20
  have step4632 (X0 X1 : G) :  (((X1 ◇ X1) ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0))) ◇ X1) = X0 := superpose step4283 step44
  have step4676 (X0 X1 X2 X3 : G) :  (X1 ◇ (((X2 ◇ X2) ◇ (((X3 ◇ X3) ◇ (X1 ◇ X1)) ◇ X3)) ◇ X2)) = ((X0 ◇ X1) ◇ (X0 ◇ X0)) := superpose step4283 step275
  have step4732 (X0 X1 X2 : G) :  ((X0 ◇ X1) ◇ (X0 ◇ X0)) = (X1 ◇ (((X2 ◇ X2) ◇ (X1 ◇ X1)) ◇ X2)) := superpose step4285 step4676
  have step4750 (X0 X1 : G) :  (((X1 ◇ X1) ◇ X0) ◇ X1) = X0 := superpose step4316 step4632
  have step4756 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step4316 step4617
  have step4795 (X0 X1 : G) :  (X1 ◇ (X1 ◇ X1)) = ((X0 ◇ X1) ◇ (X0 ◇ X0)) := superpose step4285 step4732
  have step4826 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X0) = (X1 ◇ (X1 ◇ X1)) := superpose step4756 step4795
  have step4849 (X0 X1 : G) :  (X1 ◇ X1) = ((X0 ◇ X1) ◇ X0) := superpose step4756 step4826
  have step4865 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X0) = X1 := superpose step4756 step4849
  have step5313 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ ((((X1 ◇ X1) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X1 ◇ X1) ◇ X0))) = X1 := superpose step4756 step24
  have step5329 (X0 X1 X2 : G) :  (((X1 ◇ X1) ◇ (X2 ◇ ((X0 ◇ X2) ◇ X0))) ◇ X1) = (X2 ◇ X0) := superpose step4756 step47
  have step5578 (X0 X2 : G) :  (X2 ◇ ((X0 ◇ X2) ◇ X0)) = (X2 ◇ X0) := superpose step4750 step5329
  have step5592 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) = X1 := superpose step4865 step5313
  have step5691 (X0 X2 : G) :  (X2 ◇ X2) = (X2 ◇ X0) := superpose step4865 step5578
  have step5702 (X0 X1 : G) :  (X0 ◇ (X0 ◇ X0)) = X1 := superpose step4756 step5592
  have step5763 (X0 X2 : G) :  (X2 ◇ X0) = X2 := superpose step4756 step5691
  have step5770 (X0 X1 : G) :  (X0 ◇ X0) = X1 := superpose step4756 step5702
  have step5789 (X0 X1 : G) :  X0 = X1 := superpose step5763 step5770
  have step6297 (X0 : G) :  (sK0 ◇ sK1) ≠ X0 := superpose step5789 step10
  subsumption step6297 step5789


@[equational_result]
theorem Finite.Equation677_and_Equation1249_implies_Equation4436 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation1249 G) : Equation4436 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ (((X1 ◇ X1) ◇ X0) ◇ X1)) = X0 := mod_symm (h ..)
  have step10 : (sK0 ◇ (sK1 ◇ sK0)) ≠ ((sK0 ◇ sK1) ◇ sK1) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step17 (X0 X1 : G) :  (((X1 ◇ X1) ◇ X0) ◇ X1) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose step9 step12
  have step18 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step20 (X0 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ X0) = (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ X0)) := superpose step12 step9
  have step22 (X0 X1 X2 : G) :  (((X0 ◇ X0) ◇ X1) ◇ X0) = (((X2 ◇ X2) ◇ X1) ◇ X2) := superpose step17 step17
  have step24 (X0 X1 : G) :  ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((((X1 ◇ X1) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X1 ◇ X1) ◇ X0))) = X1 := superpose step17 step12
  have step28 (X0 X1 : G) :  ((X1 ◇ X1) ◇ X1) = ((((X0 ◇ X0) ◇ X1) ◇ X0) ◇ ((X1 ◇ (((X0 ◇ X0) ◇ X1) ◇ X0)) ◇ X1)) := superpose step17 step12
  have step30 (X0 X1 : G) :  ((X1 ◇ X1) ◇ X1) = ((((X0 ◇ X0) ◇ X1) ◇ X0) ◇ (X1 ◇ X1)) := superpose step9 step28
  have step44 (X0 X1 : G) :  (X0 ◇ X0) = (((X1 ◇ X1) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ X1) := superpose step12 step22
  have step49 (X0 X1 X2 : G) :  (((X2 ◇ X2) ◇ X1) ◇ X2) = ((((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ X0) ◇ (X1 ◇ X1)) := superpose step22 step22
  have step80 (X0 X1 : G) :  ((X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) ◇ (((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)))) ◇ (X1 ◇ (X1 ◇ X0)))) = X1 := superpose step18 step12
  have step86 (X0 X1 : G) :  (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) = (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ ((X1 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) ◇ X1)) := superpose step18 step12
  have step90 (X0 : G) :  ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) = ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) := superpose step12 step30
  have step111 (X0 : G) :  (X0 ◇ X0) = (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) := superpose step20 step11
  have step445 (X0 X1 : G) :  (((X1 ◇ X1) ◇ X0) ◇ X1) = (((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0)) := superpose step17 step49
  have step1213 (X0 : G) :  (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) = ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ ((X0 ◇ X0) ◇ (((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) := superpose step44 step24
  have step1255 (X0 : G) :  (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) = ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) ◇ ((X0 ◇ X0) ◇ (((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))))) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) := superpose step90 step1213
  have step1266 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) := superpose step111 step1255
  have step4082 (X0 : G) :  (X0 ◇ X0) = ((((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) ◇ (X0 ◇ X0))) ◇ ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) ◇ (X0 ◇ X0)))) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) := superpose step1266 step80
  have step4093 (X0 : G) :  (X0 ◇ X0) = ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) := superpose step12 step4082
  have step4121 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose step12 step4093
  have step4282 (X0 : G) :  ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) = (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) := superpose step4121 step86
  have step4284 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose step4121 step12
  have step4317 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose step12 step4282
  have step4593 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) = ((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) := superpose step4284 step20
  have step4596 (X0 X1 : G) :  (X0 ◇ X0) = ((X1 ◇ ((X1 ◇ X1) ◇ X1)) ◇ (((X0 ◇ X1) ◇ (X1 ◇ ((X1 ◇ X1) ◇ X1))) ◇ (X0 ◇ X1))) := superpose step4284 step24
  have step4630 (X0 : G) :  ((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ ((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0))))) = X0 := superpose step4284 step111
  have step4659 (X0 X1 : G) :  (((X1 ◇ X1) ◇ (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ (X1 ◇ X1))) ◇ (X1 ◇ X1)) = ((X0 ◇ X1) ◇ (X0 ◇ X0)) := superpose step4284 step445
  have step4685 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose step4284 step30
  have step4696 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) := superpose step4284 step445
  have step4747 (X0 X1 : G) :  ((X1 ◇ X1) ◇ (X1 ◇ X1)) = ((X0 ◇ X1) ◇ (X0 ◇ X0)) := superpose step4696 step4659
  have step4769 (X0 : G) :  (X0 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose step4317 step4630
  have step4794 (X0 X1 : G) :  (X0 ◇ X0) = ((X1 ◇ (X1 ◇ (X1 ◇ X1))) ◇ (((X0 ◇ X1) ◇ (X1 ◇ (X1 ◇ (X1 ◇ X1)))) ◇ (X0 ◇ X1))) := superpose step4685 step4596
  have step4795 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step4317 step4593
  have step4828 (X0 X1 : G) :  ((X0 ◇ X1) ◇ (X0 ◇ X0)) = X1 := superpose step4284 step4747
  have step4849 (X0 X1 : G) :  (X0 ◇ X0) = (X1 ◇ (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1))) := superpose step4769 step4794
  have step4870 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X0) = X1 := superpose step4795 step4828
  have step4888 (X0 X1 : G) :  (X1 ◇ (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1))) = X0 := superpose step4795 step4849
  have step4915 (X0 X1 : G) :  (X1 ◇ X1) = X0 := superpose step4870 step4888
  have step6549 (X0 : G) :  (sK0 ◇ (sK1 ◇ sK0)) ≠ (X0 ◇ X0) := superpose step4915 step10
  subsumption step6549 step4915


@[equational_result]
theorem Finite.Equation677_and_Equation1249_implies_Equation4599 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation1249 G) : Equation4599 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ (((X1 ◇ X1) ◇ X0) ◇ X1)) = X0 := mod_symm (h ..)
  have step10 : ((sK0 ◇ sK0) ◇ sK1) ≠ ((sK0 ◇ sK1) ◇ sK1) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step17 (X0 X1 : G) :  (((X1 ◇ X1) ◇ X0) ◇ X1) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose step9 step12
  have step18 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step20 (X0 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ X0) = (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ X0)) := superpose step12 step9
  have step22 (X0 X1 X2 : G) :  (((X0 ◇ X0) ◇ X1) ◇ X0) = (((X2 ◇ X2) ◇ X1) ◇ X2) := superpose step17 step17
  have step24 (X0 X1 : G) :  ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((((X1 ◇ X1) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X1 ◇ X1) ◇ X0))) = X1 := superpose step17 step12
  have step28 (X0 X1 : G) :  ((X1 ◇ X1) ◇ X1) = ((((X0 ◇ X0) ◇ X1) ◇ X0) ◇ ((X1 ◇ (((X0 ◇ X0) ◇ X1) ◇ X0)) ◇ X1)) := superpose step17 step12
  have step30 (X0 X1 : G) :  ((X1 ◇ X1) ◇ X1) = ((((X0 ◇ X0) ◇ X1) ◇ X0) ◇ (X1 ◇ X1)) := superpose step9 step28
  have step44 (X0 X1 : G) :  (X0 ◇ X0) = (((X1 ◇ X1) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ X1) := superpose step12 step22
  have step49 (X0 X1 X2 : G) :  (((X2 ◇ X2) ◇ X1) ◇ X2) = ((((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ X0) ◇ (X1 ◇ X1)) := superpose step22 step22
  have step80 (X0 X1 : G) :  ((X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) ◇ (((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)))) ◇ (X1 ◇ (X1 ◇ X0)))) = X1 := superpose step18 step12
  have step86 (X0 X1 : G) :  (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) = (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ ((X1 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) ◇ X1)) := superpose step18 step12
  have step90 (X0 : G) :  ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) = ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) := superpose step12 step30
  have step111 (X0 : G) :  (X0 ◇ X0) = (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) := superpose step20 step11
  have step445 (X0 X1 : G) :  (((X1 ◇ X1) ◇ X0) ◇ X1) = (((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0)) := superpose step17 step49
  have step1213 (X0 : G) :  (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) = ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ ((X0 ◇ X0) ◇ (((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) := superpose step44 step24
  have step1255 (X0 : G) :  (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) = ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) ◇ ((X0 ◇ X0) ◇ (((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))))) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) := superpose step90 step1213
  have step1266 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) := superpose step111 step1255
  have step4082 (X0 : G) :  (X0 ◇ X0) = ((((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) ◇ (X0 ◇ X0))) ◇ ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) ◇ (X0 ◇ X0)))) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) := superpose step1266 step80
  have step4093 (X0 : G) :  (X0 ◇ X0) = ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) := superpose step12 step4082
  have step4121 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose step12 step4093
  have step4282 (X0 : G) :  ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) = (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) := superpose step4121 step86
  have step4284 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose step4121 step12
  have step4317 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose step12 step4282
  have step4593 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) = ((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) := superpose step4284 step20
  have step4596 (X0 X1 : G) :  (X0 ◇ X0) = ((X1 ◇ ((X1 ◇ X1) ◇ X1)) ◇ (((X0 ◇ X1) ◇ (X1 ◇ ((X1 ◇ X1) ◇ X1))) ◇ (X0 ◇ X1))) := superpose step4284 step24
  have step4630 (X0 : G) :  ((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ ((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0))))) = X0 := superpose step4284 step111
  have step4659 (X0 X1 : G) :  (((X1 ◇ X1) ◇ (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ (X1 ◇ X1))) ◇ (X1 ◇ X1)) = ((X0 ◇ X1) ◇ (X0 ◇ X0)) := superpose step4284 step445
  have step4685 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose step4284 step30
  have step4696 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) := superpose step4284 step445
  have step4747 (X0 X1 : G) :  ((X1 ◇ X1) ◇ (X1 ◇ X1)) = ((X0 ◇ X1) ◇ (X0 ◇ X0)) := superpose step4696 step4659
  have step4769 (X0 : G) :  (X0 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose step4317 step4630
  have step4794 (X0 X1 : G) :  (X0 ◇ X0) = ((X1 ◇ (X1 ◇ (X1 ◇ X1))) ◇ (((X0 ◇ X1) ◇ (X1 ◇ (X1 ◇ (X1 ◇ X1)))) ◇ (X0 ◇ X1))) := superpose step4685 step4596
  have step4795 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step4317 step4593
  have step4828 (X0 X1 : G) :  ((X0 ◇ X1) ◇ (X0 ◇ X0)) = X1 := superpose step4284 step4747
  have step4849 (X0 X1 : G) :  (X0 ◇ X0) = (X1 ◇ (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1))) := superpose step4769 step4794
  have step4870 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X0) = X1 := superpose step4795 step4828
  have step4888 (X0 X1 : G) :  (X1 ◇ (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1))) = X0 := superpose step4795 step4849
  have step4915 (X0 X1 : G) :  (X1 ◇ X1) = X0 := superpose step4870 step4888
  have step6549 (X0 : G) :  (X0 ◇ X0) ≠ ((sK0 ◇ sK0) ◇ sK1) := superpose step4915 step10
  subsumption step6549 step4915


@[equational_result]
theorem Finite.Equation677_and_Equation1249_implies_Equation464 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation1249 G) : Equation464 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ (((X1 ◇ X1) ◇ X0) ◇ X1)) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step17 (X0 X1 : G) :  (((X1 ◇ X1) ◇ X0) ◇ X1) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose step9 step12
  have step18 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step20 (X0 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ X0) = (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ X0)) := superpose step12 step9
  have step22 (X0 X1 X2 : G) :  (((X0 ◇ X0) ◇ X1) ◇ X0) = (((X2 ◇ X2) ◇ X1) ◇ X2) := superpose step17 step17
  have step24 (X0 X1 : G) :  ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((((X1 ◇ X1) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X1 ◇ X1) ◇ X0))) = X1 := superpose step17 step12
  have step27 (X0 X1 : G) :  ((X1 ◇ X1) ◇ X1) = ((((X0 ◇ X0) ◇ X1) ◇ X0) ◇ ((X1 ◇ (((X0 ◇ X0) ◇ X1) ◇ X0)) ◇ X1)) := superpose step17 step12
  have step30 (X0 X1 : G) :  ((X1 ◇ X1) ◇ X1) = ((((X0 ◇ X0) ◇ X1) ◇ X0) ◇ (X1 ◇ X1)) := superpose step9 step27
  have step44 (X0 X1 : G) :  (X0 ◇ X0) = (((X1 ◇ X1) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ X1) := superpose step12 step22
  have step45 (X0 X1 X2 : G) :  ((X0 ◇ X0) ◇ X0) = (((X1 ◇ X1) ◇ (((X2 ◇ X2) ◇ (X0 ◇ X0)) ◇ X2)) ◇ X1) := superpose step9 step22
  have step47 (X0 X1 X2 : G) :  (((X1 ◇ X1) ◇ (X0 ◇ (((X2 ◇ X2) ◇ X0) ◇ (X2 ◇ X2)))) ◇ X1) = (X0 ◇ X2) := superpose step11 step22
  have step80 (X0 X1 : G) :  ((X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) ◇ (((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)))) ◇ (X1 ◇ (X1 ◇ X0)))) = X1 := superpose step18 step12
  have step83 (X0 X1 : G) :  (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) = (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ ((X1 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) ◇ X1)) := superpose step18 step12
  have step90 (X0 : G) :  ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) = ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) := superpose step12 step30
  have step111 (X0 : G) :  (X0 ◇ X0) = (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) := superpose step20 step11
  have step275 (X0 X1 X2 X3 : G) :  (((X3 ◇ X3) ◇ X2) ◇ X3) = (X2 ◇ (((X0 ◇ X0) ◇ (((X1 ◇ X1) ◇ (X2 ◇ X2)) ◇ X1)) ◇ X0)) := superpose step45 step17
  have step1229 (X0 : G) :  (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) = ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ ((X0 ◇ X0) ◇ (((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) := superpose step44 step24
  have step1271 (X0 : G) :  (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) = ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) ◇ ((X0 ◇ X0) ◇ (((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))))) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) := superpose step90 step1229
  have step1282 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) := superpose step111 step1271
  have step4081 (X0 : G) :  (X0 ◇ X0) = ((((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) ◇ (X0 ◇ X0))) ◇ ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) ◇ (X0 ◇ X0)))) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) := superpose step1282 step80
  have step4092 (X0 : G) :  (X0 ◇ X0) = ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) := superpose step12 step4081
  have step4120 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose step12 step4092
  have step4281 (X0 : G) :  ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) = (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) := superpose step4120 step83
  have step4283 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose step4120 step12
  have step4285 (X0 X1 : G) :  (X0 ◇ X0) = (((X1 ◇ X1) ◇ (X0 ◇ X0)) ◇ X1) := superpose step4120 step44
  have step4316 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose step12 step4281
  have step4617 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) = ((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) := superpose step4283 step20
  have step4632 (X0 X1 : G) :  (((X1 ◇ X1) ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0))) ◇ X1) = X0 := superpose step4283 step44
  have step4676 (X0 X1 X2 X3 : G) :  (X1 ◇ (((X2 ◇ X2) ◇ (((X3 ◇ X3) ◇ (X1 ◇ X1)) ◇ X3)) ◇ X2)) = ((X0 ◇ X1) ◇ (X0 ◇ X0)) := superpose step4283 step275
  have step4732 (X0 X1 X2 : G) :  ((X0 ◇ X1) ◇ (X0 ◇ X0)) = (X1 ◇ (((X2 ◇ X2) ◇ (X1 ◇ X1)) ◇ X2)) := superpose step4285 step4676
  have step4750 (X0 X1 : G) :  (((X1 ◇ X1) ◇ X0) ◇ X1) = X0 := superpose step4316 step4632
  have step4756 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step4316 step4617
  have step4795 (X0 X1 : G) :  (X1 ◇ (X1 ◇ X1)) = ((X0 ◇ X1) ◇ (X0 ◇ X0)) := superpose step4285 step4732
  have step4826 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X0) = (X1 ◇ (X1 ◇ X1)) := superpose step4756 step4795
  have step4849 (X0 X1 : G) :  (X1 ◇ X1) = ((X0 ◇ X1) ◇ X0) := superpose step4756 step4826
  have step4865 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X0) = X1 := superpose step4756 step4849
  have step5313 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ ((((X1 ◇ X1) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X1 ◇ X1) ◇ X0))) = X1 := superpose step4756 step24
  have step5329 (X0 X1 X2 : G) :  (((X1 ◇ X1) ◇ (X2 ◇ ((X0 ◇ X2) ◇ X0))) ◇ X1) = (X2 ◇ X0) := superpose step4756 step47
  have step5578 (X0 X2 : G) :  (X2 ◇ ((X0 ◇ X2) ◇ X0)) = (X2 ◇ X0) := superpose step4750 step5329
  have step5592 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) = X1 := superpose step4865 step5313
  have step5691 (X0 X2 : G) :  (X2 ◇ X2) = (X2 ◇ X0) := superpose step4865 step5578
  have step5702 (X0 X1 : G) :  (X0 ◇ (X0 ◇ X0)) = X1 := superpose step4756 step5592
  have step5763 (X0 X2 : G) :  (X2 ◇ X0) = X2 := superpose step4756 step5691
  have step5770 (X0 X1 : G) :  (X0 ◇ X0) = X1 := superpose step4756 step5702
  have step5789 (X0 X1 : G) :  X0 = X1 := superpose step5763 step5770
  have step6737 (X0 : G) :  sK0 ≠ X0 := superpose step5789 step10
  subsumption step6737 step5789


@[equational_result]
theorem Finite.Equation677_and_Equation1249_implies_Equation4658 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation1249 G) : Equation4658 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ (((X1 ◇ X1) ◇ X0) ◇ X1)) = X0 := mod_symm (h ..)
  have step10 : ((sK0 ◇ sK1) ◇ sK1) ≠ ((sK1 ◇ sK0) ◇ sK0) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step17 (X0 X1 : G) :  (((X1 ◇ X1) ◇ X0) ◇ X1) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose step9 step12
  have step18 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step20 (X0 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ X0) = (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ X0)) := superpose step12 step9
  have step22 (X0 X1 X2 : G) :  (((X0 ◇ X0) ◇ X1) ◇ X0) = (((X2 ◇ X2) ◇ X1) ◇ X2) := superpose step17 step17
  have step24 (X0 X1 : G) :  ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((((X1 ◇ X1) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X1 ◇ X1) ◇ X0))) = X1 := superpose step17 step12
  have step28 (X0 X1 : G) :  ((X1 ◇ X1) ◇ X1) = ((((X0 ◇ X0) ◇ X1) ◇ X0) ◇ ((X1 ◇ (((X0 ◇ X0) ◇ X1) ◇ X0)) ◇ X1)) := superpose step17 step12
  have step30 (X0 X1 : G) :  ((X1 ◇ X1) ◇ X1) = ((((X0 ◇ X0) ◇ X1) ◇ X0) ◇ (X1 ◇ X1)) := superpose step9 step28
  have step44 (X0 X1 : G) :  (X0 ◇ X0) = (((X1 ◇ X1) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ X1) := superpose step12 step22
  have step49 (X0 X1 X2 : G) :  (((X2 ◇ X2) ◇ X1) ◇ X2) = ((((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ X0) ◇ (X1 ◇ X1)) := superpose step22 step22
  have step80 (X0 X1 : G) :  ((X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) ◇ (((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)))) ◇ (X1 ◇ (X1 ◇ X0)))) = X1 := superpose step18 step12
  have step86 (X0 X1 : G) :  (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) = (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ ((X1 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) ◇ X1)) := superpose step18 step12
  have step90 (X0 : G) :  ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) = ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) := superpose step12 step30
  have step111 (X0 : G) :  (X0 ◇ X0) = (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) := superpose step20 step11
  have step445 (X0 X1 : G) :  (((X1 ◇ X1) ◇ X0) ◇ X1) = (((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0)) := superpose step17 step49
  have step1213 (X0 : G) :  (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) = ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ ((X0 ◇ X0) ◇ (((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) := superpose step44 step24
  have step1255 (X0 : G) :  (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) = ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) ◇ ((X0 ◇ X0) ◇ (((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))))) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) := superpose step90 step1213
  have step1266 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) := superpose step111 step1255
  have step4082 (X0 : G) :  (X0 ◇ X0) = ((((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) ◇ (X0 ◇ X0))) ◇ ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) ◇ (X0 ◇ X0)))) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) := superpose step1266 step80
  have step4093 (X0 : G) :  (X0 ◇ X0) = ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) := superpose step12 step4082
  have step4121 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose step12 step4093
  have step4282 (X0 : G) :  ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) = (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) := superpose step4121 step86
  have step4284 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose step4121 step12
  have step4317 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose step12 step4282
  have step4593 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) = ((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) := superpose step4284 step20
  have step4596 (X0 X1 : G) :  (X0 ◇ X0) = ((X1 ◇ ((X1 ◇ X1) ◇ X1)) ◇ (((X0 ◇ X1) ◇ (X1 ◇ ((X1 ◇ X1) ◇ X1))) ◇ (X0 ◇ X1))) := superpose step4284 step24
  have step4630 (X0 : G) :  ((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ ((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0))))) = X0 := superpose step4284 step111
  have step4659 (X0 X1 : G) :  (((X1 ◇ X1) ◇ (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ (X1 ◇ X1))) ◇ (X1 ◇ X1)) = ((X0 ◇ X1) ◇ (X0 ◇ X0)) := superpose step4284 step445
  have step4685 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose step4284 step30
  have step4696 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) := superpose step4284 step445
  have step4747 (X0 X1 : G) :  ((X1 ◇ X1) ◇ (X1 ◇ X1)) = ((X0 ◇ X1) ◇ (X0 ◇ X0)) := superpose step4696 step4659
  have step4769 (X0 : G) :  (X0 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose step4317 step4630
  have step4794 (X0 X1 : G) :  (X0 ◇ X0) = ((X1 ◇ (X1 ◇ (X1 ◇ X1))) ◇ (((X0 ◇ X1) ◇ (X1 ◇ (X1 ◇ (X1 ◇ X1)))) ◇ (X0 ◇ X1))) := superpose step4685 step4596
  have step4795 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step4317 step4593
  have step4828 (X0 X1 : G) :  ((X0 ◇ X1) ◇ (X0 ◇ X0)) = X1 := superpose step4284 step4747
  have step4849 (X0 X1 : G) :  (X0 ◇ X0) = (X1 ◇ (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1))) := superpose step4769 step4794
  have step4870 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X0) = X1 := superpose step4795 step4828
  have step4888 (X0 X1 : G) :  (X1 ◇ (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1))) = X0 := superpose step4795 step4849
  have step4915 (X0 X1 : G) :  (X1 ◇ X1) = X0 := superpose step4870 step4888
  have step6549 (X0 : G) :  ((sK0 ◇ sK1) ◇ sK1) ≠ (X0 ◇ X0) := superpose step4915 step10
  subsumption step6549 step4915


@[equational_result]
theorem Finite.Equation677_and_Equation1249_implies_Equation501 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation1249 G) : Equation501 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ (((X1 ◇ X1) ◇ X0) ◇ X1)) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step17 (X0 X1 : G) :  (((X1 ◇ X1) ◇ X0) ◇ X1) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose step9 step12
  have step18 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step20 (X0 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ X0) = (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ X0)) := superpose step12 step9
  have step22 (X0 X1 X2 : G) :  (((X0 ◇ X0) ◇ X1) ◇ X0) = (((X2 ◇ X2) ◇ X1) ◇ X2) := superpose step17 step17
  have step24 (X0 X1 : G) :  ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((((X1 ◇ X1) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X1 ◇ X1) ◇ X0))) = X1 := superpose step17 step12
  have step27 (X0 X1 : G) :  ((X1 ◇ X1) ◇ X1) = ((((X0 ◇ X0) ◇ X1) ◇ X0) ◇ ((X1 ◇ (((X0 ◇ X0) ◇ X1) ◇ X0)) ◇ X1)) := superpose step17 step12
  have step30 (X0 X1 : G) :  ((X1 ◇ X1) ◇ X1) = ((((X0 ◇ X0) ◇ X1) ◇ X0) ◇ (X1 ◇ X1)) := superpose step9 step27
  have step44 (X0 X1 : G) :  (X0 ◇ X0) = (((X1 ◇ X1) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ X1) := superpose step12 step22
  have step45 (X0 X1 X2 : G) :  ((X0 ◇ X0) ◇ X0) = (((X1 ◇ X1) ◇ (((X2 ◇ X2) ◇ (X0 ◇ X0)) ◇ X2)) ◇ X1) := superpose step9 step22
  have step47 (X0 X1 X2 : G) :  (((X1 ◇ X1) ◇ (X0 ◇ (((X2 ◇ X2) ◇ X0) ◇ (X2 ◇ X2)))) ◇ X1) = (X0 ◇ X2) := superpose step11 step22
  have step80 (X0 X1 : G) :  ((X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) ◇ (((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)))) ◇ (X1 ◇ (X1 ◇ X0)))) = X1 := superpose step18 step12
  have step83 (X0 X1 : G) :  (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) = (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ ((X1 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) ◇ X1)) := superpose step18 step12
  have step90 (X0 : G) :  ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) = ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) := superpose step12 step30
  have step111 (X0 : G) :  (X0 ◇ X0) = (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) := superpose step20 step11
  have step275 (X0 X1 X2 X3 : G) :  (((X3 ◇ X3) ◇ X2) ◇ X3) = (X2 ◇ (((X0 ◇ X0) ◇ (((X1 ◇ X1) ◇ (X2 ◇ X2)) ◇ X1)) ◇ X0)) := superpose step45 step17
  have step1229 (X0 : G) :  (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) = ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ ((X0 ◇ X0) ◇ (((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) := superpose step44 step24
  have step1271 (X0 : G) :  (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) = ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) ◇ ((X0 ◇ X0) ◇ (((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))))) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) := superpose step90 step1229
  have step1282 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) := superpose step111 step1271
  have step4081 (X0 : G) :  (X0 ◇ X0) = ((((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) ◇ (X0 ◇ X0))) ◇ ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) ◇ (X0 ◇ X0)))) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) := superpose step1282 step80
  have step4092 (X0 : G) :  (X0 ◇ X0) = ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) := superpose step12 step4081
  have step4120 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose step12 step4092
  have step4281 (X0 : G) :  ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) = (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) := superpose step4120 step83
  have step4283 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose step4120 step12
  have step4285 (X0 X1 : G) :  (X0 ◇ X0) = (((X1 ◇ X1) ◇ (X0 ◇ X0)) ◇ X1) := superpose step4120 step44
  have step4316 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose step12 step4281
  have step4617 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) = ((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) := superpose step4283 step20
  have step4632 (X0 X1 : G) :  (((X1 ◇ X1) ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0))) ◇ X1) = X0 := superpose step4283 step44
  have step4676 (X0 X1 X2 X3 : G) :  (X1 ◇ (((X2 ◇ X2) ◇ (((X3 ◇ X3) ◇ (X1 ◇ X1)) ◇ X3)) ◇ X2)) = ((X0 ◇ X1) ◇ (X0 ◇ X0)) := superpose step4283 step275
  have step4732 (X0 X1 X2 : G) :  ((X0 ◇ X1) ◇ (X0 ◇ X0)) = (X1 ◇ (((X2 ◇ X2) ◇ (X1 ◇ X1)) ◇ X2)) := superpose step4285 step4676
  have step4750 (X0 X1 : G) :  (((X1 ◇ X1) ◇ X0) ◇ X1) = X0 := superpose step4316 step4632
  have step4756 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step4316 step4617
  have step4795 (X0 X1 : G) :  (X1 ◇ (X1 ◇ X1)) = ((X0 ◇ X1) ◇ (X0 ◇ X0)) := superpose step4285 step4732
  have step4826 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X0) = (X1 ◇ (X1 ◇ X1)) := superpose step4756 step4795
  have step4849 (X0 X1 : G) :  (X1 ◇ X1) = ((X0 ◇ X1) ◇ X0) := superpose step4756 step4826
  have step4865 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X0) = X1 := superpose step4756 step4849
  have step5313 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ ((((X1 ◇ X1) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X1 ◇ X1) ◇ X0))) = X1 := superpose step4756 step24
  have step5329 (X0 X1 X2 : G) :  (((X1 ◇ X1) ◇ (X2 ◇ ((X0 ◇ X2) ◇ X0))) ◇ X1) = (X2 ◇ X0) := superpose step4756 step47
  have step5578 (X0 X2 : G) :  (X2 ◇ ((X0 ◇ X2) ◇ X0)) = (X2 ◇ X0) := superpose step4750 step5329
  have step5592 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) = X1 := superpose step4865 step5313
  have step5691 (X0 X2 : G) :  (X2 ◇ X2) = (X2 ◇ X0) := superpose step4865 step5578
  have step5702 (X0 X1 : G) :  (X0 ◇ (X0 ◇ X0)) = X1 := superpose step4756 step5592
  have step5763 (X0 X2 : G) :  (X2 ◇ X0) = X2 := superpose step4756 step5691
  have step5770 (X0 X1 : G) :  (X0 ◇ X0) = X1 := superpose step4756 step5702
  have step5789 (X0 X1 : G) :  X0 = X1 := superpose step5763 step5770
  have step6737 (X0 : G) :  sK0 ≠ X0 := superpose step5789 step10
  subsumption step6737 step5789


@[equational_result]
theorem Finite.Equation677_and_Equation1249_implies_Equation503 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation1249 G) : Equation503 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ (((X1 ◇ X1) ◇ X0) ◇ X1)) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step17 (X0 X1 : G) :  (((X1 ◇ X1) ◇ X0) ◇ X1) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose step9 step12
  have step18 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step20 (X0 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ X0) = (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ X0)) := superpose step12 step9
  have step22 (X0 X1 X2 : G) :  (((X0 ◇ X0) ◇ X1) ◇ X0) = (((X2 ◇ X2) ◇ X1) ◇ X2) := superpose step17 step17
  have step24 (X0 X1 : G) :  ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((((X1 ◇ X1) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X1 ◇ X1) ◇ X0))) = X1 := superpose step17 step12
  have step27 (X0 X1 : G) :  ((X1 ◇ X1) ◇ X1) = ((((X0 ◇ X0) ◇ X1) ◇ X0) ◇ ((X1 ◇ (((X0 ◇ X0) ◇ X1) ◇ X0)) ◇ X1)) := superpose step17 step12
  have step30 (X0 X1 : G) :  ((X1 ◇ X1) ◇ X1) = ((((X0 ◇ X0) ◇ X1) ◇ X0) ◇ (X1 ◇ X1)) := superpose step9 step27
  have step44 (X0 X1 : G) :  (X0 ◇ X0) = (((X1 ◇ X1) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ X1) := superpose step12 step22
  have step45 (X0 X1 X2 : G) :  ((X0 ◇ X0) ◇ X0) = (((X1 ◇ X1) ◇ (((X2 ◇ X2) ◇ (X0 ◇ X0)) ◇ X2)) ◇ X1) := superpose step9 step22
  have step47 (X0 X1 X2 : G) :  (((X1 ◇ X1) ◇ (X0 ◇ (((X2 ◇ X2) ◇ X0) ◇ (X2 ◇ X2)))) ◇ X1) = (X0 ◇ X2) := superpose step11 step22
  have step80 (X0 X1 : G) :  ((X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) ◇ (((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)))) ◇ (X1 ◇ (X1 ◇ X0)))) = X1 := superpose step18 step12
  have step83 (X0 X1 : G) :  (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) = (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ ((X1 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) ◇ X1)) := superpose step18 step12
  have step90 (X0 : G) :  ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) = ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) := superpose step12 step30
  have step111 (X0 : G) :  (X0 ◇ X0) = (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) := superpose step20 step11
  have step275 (X0 X1 X2 X3 : G) :  (((X3 ◇ X3) ◇ X2) ◇ X3) = (X2 ◇ (((X0 ◇ X0) ◇ (((X1 ◇ X1) ◇ (X2 ◇ X2)) ◇ X1)) ◇ X0)) := superpose step45 step17
  have step1229 (X0 : G) :  (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) = ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ ((X0 ◇ X0) ◇ (((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) := superpose step44 step24
  have step1271 (X0 : G) :  (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) = ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) ◇ ((X0 ◇ X0) ◇ (((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))))) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) := superpose step90 step1229
  have step1282 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) := superpose step111 step1271
  have step4081 (X0 : G) :  (X0 ◇ X0) = ((((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) ◇ (X0 ◇ X0))) ◇ ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) ◇ (X0 ◇ X0)))) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) := superpose step1282 step80
  have step4092 (X0 : G) :  (X0 ◇ X0) = ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) := superpose step12 step4081
  have step4120 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose step12 step4092
  have step4281 (X0 : G) :  ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) = (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) := superpose step4120 step83
  have step4283 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose step4120 step12
  have step4285 (X0 X1 : G) :  (X0 ◇ X0) = (((X1 ◇ X1) ◇ (X0 ◇ X0)) ◇ X1) := superpose step4120 step44
  have step4316 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose step12 step4281
  have step4617 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) = ((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) := superpose step4283 step20
  have step4632 (X0 X1 : G) :  (((X1 ◇ X1) ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0))) ◇ X1) = X0 := superpose step4283 step44
  have step4676 (X0 X1 X2 X3 : G) :  (X1 ◇ (((X2 ◇ X2) ◇ (((X3 ◇ X3) ◇ (X1 ◇ X1)) ◇ X3)) ◇ X2)) = ((X0 ◇ X1) ◇ (X0 ◇ X0)) := superpose step4283 step275
  have step4732 (X0 X1 X2 : G) :  ((X0 ◇ X1) ◇ (X0 ◇ X0)) = (X1 ◇ (((X2 ◇ X2) ◇ (X1 ◇ X1)) ◇ X2)) := superpose step4285 step4676
  have step4750 (X0 X1 : G) :  (((X1 ◇ X1) ◇ X0) ◇ X1) = X0 := superpose step4316 step4632
  have step4756 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step4316 step4617
  have step4795 (X0 X1 : G) :  (X1 ◇ (X1 ◇ X1)) = ((X0 ◇ X1) ◇ (X0 ◇ X0)) := superpose step4285 step4732
  have step4826 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X0) = (X1 ◇ (X1 ◇ X1)) := superpose step4756 step4795
  have step4849 (X0 X1 : G) :  (X1 ◇ X1) = ((X0 ◇ X1) ◇ X0) := superpose step4756 step4826
  have step4865 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X0) = X1 := superpose step4756 step4849
  have step5313 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ ((((X1 ◇ X1) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X1 ◇ X1) ◇ X0))) = X1 := superpose step4756 step24
  have step5329 (X0 X1 X2 : G) :  (((X1 ◇ X1) ◇ (X2 ◇ ((X0 ◇ X2) ◇ X0))) ◇ X1) = (X2 ◇ X0) := superpose step4756 step47
  have step5578 (X0 X2 : G) :  (X2 ◇ ((X0 ◇ X2) ◇ X0)) = (X2 ◇ X0) := superpose step4750 step5329
  have step5592 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) = X1 := superpose step4865 step5313
  have step5691 (X0 X2 : G) :  (X2 ◇ X2) = (X2 ◇ X0) := superpose step4865 step5578
  have step5702 (X0 X1 : G) :  (X0 ◇ (X0 ◇ X0)) = X1 := superpose step4756 step5592
  have step5763 (X0 X2 : G) :  (X2 ◇ X0) = X2 := superpose step4756 step5691
  have step5770 (X0 X1 : G) :  (X0 ◇ X0) = X1 := superpose step4756 step5702
  have step5789 (X0 X1 : G) :  X0 = X1 := superpose step5763 step5770
  have step6737 (X0 : G) :  sK0 ≠ X0 := superpose step5789 step10
  subsumption step6737 step5789


@[equational_result]
theorem Finite.Equation677_and_Equation1249_implies_Equation630 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation1249 G) : Equation630 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ (((X1 ◇ X1) ◇ X0) ◇ X1)) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ (sK0 ◇ (sK1 ◇ ((sK0 ◇ sK0) ◇ sK1))) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step17 (X0 X1 : G) :  (((X1 ◇ X1) ◇ X0) ◇ X1) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose step9 step12
  have step18 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step20 (X0 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ X0) = (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ X0)) := superpose step12 step9
  have step22 (X0 X1 X2 : G) :  (((X0 ◇ X0) ◇ X1) ◇ X0) = (((X2 ◇ X2) ◇ X1) ◇ X2) := superpose step17 step17
  have step24 (X0 X1 : G) :  ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((((X1 ◇ X1) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X1 ◇ X1) ◇ X0))) = X1 := superpose step17 step12
  have step27 (X0 X1 : G) :  ((X1 ◇ X1) ◇ X1) = ((((X0 ◇ X0) ◇ X1) ◇ X0) ◇ ((X1 ◇ (((X0 ◇ X0) ◇ X1) ◇ X0)) ◇ X1)) := superpose step17 step12
  have step30 (X0 X1 : G) :  ((X1 ◇ X1) ◇ X1) = ((((X0 ◇ X0) ◇ X1) ◇ X0) ◇ (X1 ◇ X1)) := superpose step9 step27
  have step44 (X0 X1 : G) :  (X0 ◇ X0) = (((X1 ◇ X1) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ X1) := superpose step12 step22
  have step45 (X0 X1 X2 : G) :  ((X0 ◇ X0) ◇ X0) = (((X1 ◇ X1) ◇ (((X2 ◇ X2) ◇ (X0 ◇ X0)) ◇ X2)) ◇ X1) := superpose step9 step22
  have step47 (X0 X1 X2 : G) :  (((X1 ◇ X1) ◇ (X0 ◇ (((X2 ◇ X2) ◇ X0) ◇ (X2 ◇ X2)))) ◇ X1) = (X0 ◇ X2) := superpose step11 step22
  have step80 (X0 X1 : G) :  ((X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) ◇ (((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)))) ◇ (X1 ◇ (X1 ◇ X0)))) = X1 := superpose step18 step12
  have step83 (X0 X1 : G) :  (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) = (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ ((X1 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) ◇ X1)) := superpose step18 step12
  have step90 (X0 : G) :  ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) = ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) := superpose step12 step30
  have step111 (X0 : G) :  (X0 ◇ X0) = (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) := superpose step20 step11
  have step272 (X0 X1 X2 X3 : G) :  (((X3 ◇ X3) ◇ X2) ◇ X3) = ((((X0 ◇ X0) ◇ (((X1 ◇ X1) ◇ (X2 ◇ X2)) ◇ X1)) ◇ X0) ◇ X2) := superpose step45 step22
  have step1213 (X0 : G) :  (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) = ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ ((X0 ◇ X0) ◇ (((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) := superpose step44 step24
  have step1255 (X0 : G) :  (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) = ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) ◇ ((X0 ◇ X0) ◇ (((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))))) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) := superpose step90 step1213
  have step1266 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) := superpose step111 step1255
  have step4082 (X0 : G) :  (X0 ◇ X0) = ((((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) ◇ (X0 ◇ X0))) ◇ ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) ◇ (X0 ◇ X0)))) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) := superpose step1266 step80
  have step4093 (X0 : G) :  (X0 ◇ X0) = ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) := superpose step12 step4082
  have step4121 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose step12 step4093
  have step4282 (X0 : G) :  ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) = (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) := superpose step4121 step83
  have step4284 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose step4121 step12
  have step4286 (X0 X1 : G) :  (X0 ◇ X0) = (((X1 ◇ X1) ◇ (X0 ◇ X0)) ◇ X1) := superpose step4121 step44
  have step4317 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose step12 step4282
  have step4618 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) = ((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) := superpose step4284 step20
  have step4633 (X0 X1 : G) :  (((X1 ◇ X1) ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0))) ◇ X1) = X0 := superpose step4284 step44
  have step4674 (X0 X1 X2 X3 : G) :  ((((X2 ◇ X2) ◇ (((X3 ◇ X3) ◇ (X1 ◇ X1)) ◇ X3)) ◇ X2) ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ X0)) := superpose step4284 step272
  have step4734 (X0 X1 X2 : G) :  ((((X2 ◇ X2) ◇ (X1 ◇ X1)) ◇ X2) ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ X0)) := superpose step4286 step4674
  have step4751 (X0 X1 : G) :  (((X1 ◇ X1) ◇ X0) ◇ X1) = X0 := superpose step4317 step4633
  have step4757 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step4317 step4618
  have step4796 (X0 X1 : G) :  ((X1 ◇ X1) ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ X0)) := superpose step4286 step4734
  have step4827 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X0) = ((X1 ◇ X1) ◇ X1) := superpose step4757 step4796
  have step4850 (X0 X1 : G) :  (X1 ◇ X1) = ((X0 ◇ X1) ◇ X0) := superpose step4757 step4827
  have step4866 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X0) = X1 := superpose step4757 step4850
  have step5314 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ ((((X1 ◇ X1) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X1 ◇ X1) ◇ X0))) = X1 := superpose step4757 step24
  have step5330 (X0 X1 X2 : G) :  (((X1 ◇ X1) ◇ (X2 ◇ ((X0 ◇ X2) ◇ X0))) ◇ X1) = (X2 ◇ X0) := superpose step4757 step47
  have step5580 (X0 X2 : G) :  (X2 ◇ ((X0 ◇ X2) ◇ X0)) = (X2 ◇ X0) := superpose step4751 step5330
  have step5594 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) = X1 := superpose step4866 step5314
  have step5693 (X0 X2 : G) :  (X2 ◇ X2) = (X2 ◇ X0) := superpose step4866 step5580
  have step5704 (X0 X1 : G) :  (X0 ◇ (X0 ◇ X0)) = X1 := superpose step4757 step5594
  have step5765 (X0 X2 : G) :  (X2 ◇ X0) = X2 := superpose step4757 step5693
  have step5772 (X0 X1 : G) :  (X0 ◇ X0) = X1 := superpose step4757 step5704
  have step5791 (X0 X1 : G) :  X0 = X1 := superpose step5765 step5772
  have step6910 (X0 : G) :  sK0 ≠ (sK0 ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ X0))) := superpose step5791 step10
  subsumption step6910 step5791


@[equational_result]
theorem Finite.Equation677_and_Equation1251_implies_Equation1223 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation1251 G) : Equation1223 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ (((X1 ◇ X1) ◇ X1) ◇ X0)) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ (sK0 ◇ (((sK0 ◇ sK0) ◇ sK0) ◇ sK0)) := mod_symm nh
  have step14 : sK0 ≠ sK0 := superpose step9 step10
  subsumption step14 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation1251_implies_Equation623 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation1251 G) : Equation623 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ (((X1 ◇ X1) ◇ X1) ◇ X0)) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ (sK0 ◇ (sK0 ◇ ((sK1 ◇ sK1) ◇ sK1))) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step13 (X0 X1 : G) :  (((X1 ◇ X1) ◇ X1) ◇ ((X0 ◇ X0) ◇ X0)) = ((((X1 ◇ X1) ◇ X1) ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) := superpose step9 step9
  have step17 (X0 X1 : G) :  (((X1 ◇ X1) ◇ X1) ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose step9 step12
  have step23 (X0 X1 X2 : G) :  (((X0 ◇ X0) ◇ X0) ◇ X1) = (((X2 ◇ X2) ◇ X2) ◇ X1) := superpose step17 step17
  have step81 (X0 X1 X2 : G) :  ((X2 ◇ X2) ◇ X2) = (((X0 ◇ X0) ◇ X0) ◇ (((X1 ◇ X1) ◇ X1) ◇ ((X2 ◇ X2) ◇ X2))) := superpose step23 step9
  have step83 (X0 X1 X2 : G) :  (((X2 ◇ X2) ◇ X2) ◇ ((X1 ◇ X1) ◇ X1)) = (((X0 ◇ X0) ◇ X0) ◇ ((((X1 ◇ X1) ◇ X1) ◇ ((X1 ◇ X1) ◇ X1)) ◇ ((X1 ◇ X1) ◇ X1))) := superpose step23 step17
  have step87 (X0 X1 X2 : G) :  (((X2 ◇ X2) ◇ X2) ◇ ((X1 ◇ X1) ◇ X1)) = (((X0 ◇ X0) ◇ X0) ◇ (((X1 ◇ X1) ◇ X1) ◇ ((X1 ◇ X1) ◇ X1))) := superpose step13 step83
  have step105 (X1 X2 : G) :  ((X1 ◇ X1) ◇ X1) = (((X2 ◇ X2) ◇ X2) ◇ ((X1 ◇ X1) ◇ X1)) := superpose step81 step87
  have step545 (X0 X1 : G) :  ((X0 ◇ X0) ◇ X0) = (((X1 ◇ X1) ◇ X1) ◇ (((X0 ◇ X0) ◇ X0) ◇ (((X0 ◇ X0) ◇ X0) ◇ ((X1 ◇ X1) ◇ X1)))) := superpose step105 step11
  have step546 (X0 X1 : G) :  ((X0 ◇ X0) ◇ X0) = (((X1 ◇ X1) ◇ X1) ◇ ((X1 ◇ X1) ◇ X1)) := superpose step81 step545
  have step576 (X0 X1 : G) :  ((X1 ◇ X1) ◇ X1) = ((X0 ◇ X0) ◇ X0) := superpose step105 step546
  have step747 (X0 : G) :  sK0 ≠ (sK0 ◇ (sK0 ◇ ((X0 ◇ X0) ◇ X0))) := superpose step576 step10
  have step853 : sK0 ≠ sK0 := superpose step11 step747
  subsumption step853 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation1285_implies_Equation3 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation1285 G) : Equation3 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have step10 (X0 X1 : G) :  (X1 ◇ (((X0 ◇ X1) ◇ X0) ◇ X0)) = X0 := mod_symm (h ..)
  have step11 : sK0 ≠ (sK0 ◇ sK0) := mod_symm nh
  have step13 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step14 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step15 (X0 X1 : G) :  ((((X0 ◇ X1) ◇ X0) ◇ X0) ◇ ((X0 ◇ X1) ◇ X1)) = X1 := superpose step10 step10
  have step20 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step14 step14
  have step41 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) := superpose step15 step10
  have step49 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = X0 := superpose step13 step41
  have step59 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = X0 := superpose step49 step10
  have step63 (X0 : G) :  (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0))) = X0 := superpose step49 step14
  have step66 (X0 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ X0) = X0 := superpose step20 step63
  have step69 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step59 step66
  have step122 : sK0 ≠ sK0 := superpose step69 step11
  subsumption step122 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation1286_implies_Equation1848 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation1286 G) : Equation1848 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step12 : sK0 ≠ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ sK1)) := mod_symm nh
  have step13 (X Y : G) : (((Y ◇ (X ◇ Y)) ◇ Y) ◇ (Y ◇ (X ◇ Y))) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => ((s ◇ Y) ◇ s)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (Y ◇ (s ◇ Y))) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (Y ◇ (s ◇ Y))) (fun s => ((s ◇ Y) ◇ s)) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step15 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step38 (X0 X1 : G) :  ((X1 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X0)) = X1 := superpose step13 step15
  have step58 : sK0 ≠ sK0 := superpose step38 step12
  subsumption step58 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation1288_implies_Equation3 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation1288 G) : Equation3 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have step10 (X0 X1 : G) :  (X1 ◇ (((X0 ◇ X1) ◇ X1) ◇ X0)) = X0 := mod_symm (h ..)
  have step11 : sK0 ≠ (sK0 ◇ sK0) := mod_symm nh
  have step12 (X Y : G) : ((((Y ◇ X) ◇ Y) ◇ Y) ◇ (Y ◇ X)) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (((s ◇ Y) ◇ Y) ◇ s)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (Y ◇ s)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (Y ◇ s)) (fun s => (((s ◇ Y) ◇ Y) ◇ s)) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step13 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step14 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step17 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ X0) ◇ X1)) = (X1 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X0 ◇ X1))) := superpose step13 step13
  have step19 (X0 X1 : G) :  (((X0 ◇ X1) ◇ X1) ◇ X0) = (X0 ◇ ((X1 ◇ X0) ◇ X1)) := superpose step13 step12
  have step25 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step14 step14
  have step38 (X0 : G) :  (X0 ◇ X0) = (X0 ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0))) := superpose step19 step10
  have step47 (X0 : G) :  (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose step17 step38
  have step50 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = X0 := superpose step47 step13
  have step51 (X0 : G) :  (X0 ◇ ((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0))) = (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) := superpose step47 step19
  have step53 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) := superpose step47 step12
  have step56 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = X0 := superpose step12 step53
  have step58 (X0 : G) :  (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) = (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose step25 step51
  have step59 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) := superpose step56 step58
  have step60 (X0 : G) :  (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose step56 step59
  have step61 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step50 step60
  have step81 : sK0 ≠ sK0 := superpose step61 step11
  subsumption step81 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation1289_implies_Equation474 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation1289 G) : Equation474 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step13 : sK0 ≠ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := mod_symm nh
  have step14 (X Y : G) : ((Y ◇ ((X ◇ Y) ◇ Y)) ◇ Y) = X := by
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
  have step15 (X Y : G) : (((Y ◇ (X ◇ Y)) ◇ Y) ◇ Y) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => ((s ◇ Y) ◇ Y)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (Y ◇ (s ◇ Y))) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (Y ◇ (s ◇ Y))) (fun s => ((s ◇ Y) ◇ Y)) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step17 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step26 (X0 X1 : G) :  (X1 ◇ (X0 ◇ X1)) = ((X1 ◇ X0) ◇ X1) := superpose step15 step14
  have step73 (X0 X1 : G) :  (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0)))) = X1 := superpose step26 step17
  have step151 : sK0 ≠ sK0 := superpose step73 step13
  subsumption step151 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation1312_implies_Equation3 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation1312 G) : Equation3 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have step11 : sK0 ≠ (sK0 ◇ sK0) := mod_symm nh
  have step12 (X Y : G) : (((Y ◇ (Y ◇ X)) ◇ (Y ◇ X)) ◇ (Y ◇ X)) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (((Y ◇ s) ◇ s) ◇ s)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (Y ◇ s)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (Y ◇ s)) (fun s => (((Y ◇ s) ◇ s) ◇ s)) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step13 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step14 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step20 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step14 step14
  have step24 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) := superpose step13 step12
  have step33 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) := superpose step13 step24
  have step34 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = X0 := superpose step13 step33
  have step36 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = X0 := superpose step34 step13
  have step38 (X0 : G) :  (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0))) = X0 := superpose step34 step14
  have step42 (X0 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ X0) = X0 := superpose step20 step38
  have step44 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step36 step42
  have step46 : sK0 ≠ sK0 := superpose step44 step11
  subsumption step46 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation1313_implies_Equation3 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation1313 G) : Equation3 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have step11 (X0 X1 : G) :  (X1 ◇ (((X1 ◇ X0) ◇ X0) ◇ X1)) = X0 := mod_symm (h ..)
  have step12 : sK0 ≠ (sK0 ◇ sK0) := mod_symm nh
  have step14 (X Y : G) : (((Y ◇ (Y ◇ X)) ◇ (Y ◇ X)) ◇ Y) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (((Y ◇ s) ◇ s) ◇ Y)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (Y ◇ s)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (Y ◇ s)) (fun s => (((Y ◇ s) ◇ s) ◇ Y)) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step15 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step16 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step21 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ X0) := superpose step15 step14
  have step26 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose step15 step21
  have step27 (X0 : G) :  (X0 ◇ ((X0 ◇ X0) ◇ X0)) = X0 := superpose step26 step11
  have step34 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = X0 := superpose step26 step27
  have step40 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose step15 step16
  have step45 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := superpose step26 step40
  have step47 (X0 : G) :  (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose step34 step45
  have step48 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step34 step47
  have step49 : sK0 ≠ sK0 := superpose step48 step12
  subsumption step49 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation1315_implies_Equation3 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation1315 G) : Equation3 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have step10 (X0 X1 : G) :  (X1 ◇ (((X1 ◇ X0) ◇ X1) ◇ X0)) = X0 := mod_symm (h ..)
  have step11 : sK0 ≠ (sK0 ◇ sK0) := mod_symm nh
  have step12 (X Y : G) : (((Y ◇ (Y ◇ X)) ◇ Y) ◇ (Y ◇ X)) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (((Y ◇ s) ◇ Y) ◇ s)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (Y ◇ s)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (Y ◇ s)) (fun s => (((Y ◇ s) ◇ Y) ◇ s)) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step13 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step14 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step16 (X0 X1 : G) :  (((X1 ◇ X0) ◇ X1) ◇ X0) = (X1 ◇ ((((X1 ◇ X0) ◇ X1) ◇ X0) ◇ (X0 ◇ X1))) := superpose step10 step13
  have step19 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) := superpose step13 step12
  have step20 (X0 X1 : G) :  (((X1 ◇ X0) ◇ X1) ◇ X0) = (X0 ◇ ((X1 ◇ X0) ◇ X1)) := superpose step13 step12
  have step27 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose step13 step14
  have step48 (X0 : G) :  (X0 ◇ ((X0 ◇ X0) ◇ X0)) = ((((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) := superpose step19 step12
  have step51 (X0 : G) :  (X0 ◇ ((X0 ◇ X0) ◇ X0)) = X0 := superpose step12 step48
  have step57 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ (X0 ◇ X0))) := superpose step27 step10
  have step58 (X0 : G) :  (X0 ◇ X0) = (X0 ◇ ((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ (X0 ◇ X0))) := superpose step51 step57
  have step63 (X0 : G) :  (X0 ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ X0) := superpose step16 step58
  have step67 (X0 : G) :  (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose step20 step63
  have step69 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step51 step67
  have step71 : sK0 ≠ sK0 := superpose step69 step11
  subsumption step71 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation1444_implies_Equation3 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation1444 G) : Equation3 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have step9 (X0 X1 : G) :  ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ X0))) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ (sK0 ◇ sK0) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step15 (X0 : G) :  (X0 ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ X0) := superpose step9 step9
  have step20 (X0 X1 : G) :  (X0 ◇ (X1 ◇ X0)) = (X0 ◇ (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1))) := superpose step9 step12
  have step28 (X0 : G) :  ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose step15 step9
  have step65 (X0 X1 : G) :  (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) = ((X0 ◇ (X1 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X0)) := superpose step20 step12
  have step69 (X0 X1 : G) :  (X1 ◇ X0) = (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) := superpose step12 step65
  have step78 (X0 : G) :  ((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) := superpose step28 step69
  have step96 (X0 : G) :  ((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ X0) = X0 := superpose step9 step78
  have step97 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step11 step96
  have step135 : sK0 ≠ sK0 := superpose step97 step10
  subsumption step135 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation1454_implies_Equation3 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation1454 G) : Equation3 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have step9 (X0 X1 : G) :  ((X0 ◇ X1) ◇ (X1 ◇ (X1 ◇ X0))) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ (sK0 ◇ sK0) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step14 (X0 X1 : G) :  (X1 ◇ (X1 ◇ X0)) = (((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ X0)) := superpose step9 step9
  have step15 (X0 X1 : G) :  (X1 ◇ (X1 ◇ X0)) = ((X0 ◇ X1) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X1)))) := superpose step9 step11
  have step20 (X0 X1 : G) :  (X1 ◇ (X1 ◇ X0)) = (X0 ◇ (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1))) := superpose step9 step12
  have step21 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step88 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose step21 step20
  have step106 (X0 : G) :  (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) = ((X0 ◇ (X0 ◇ X0)) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ X0)))) := superpose step88 step20
  have step107 (X0 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ X0)))) = X0 := superpose step88 step12
  have step111 (X0 : G) :  (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) = X0 := superpose step107 step106
  have step172 (X0 : G) :  (X0 ◇ ((X0 ◇ X0) ◇ X0)) = (X0 ◇ (X0 ◇ (X0 ◇ X0))) := superpose step111 step12
  have step175 (X0 : G) :  (X0 ◇ ((X0 ◇ X0) ◇ X0)) = ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0)) := superpose step111 step20
  have step176 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) ◇ X0)) := superpose step111 step21
  have step177 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose step12 step176
  have step214 (X0 : G) :  ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) = ((((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ X0))) := superpose step88 step14
  have step226 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) = ((((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ X0))) := superpose step177 step214
  have step245 (X0 : G) :  ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose step9 step226
  have step260 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) := superpose step177 step20
  have step268 (X0 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0)))) = X0 := superpose step177 step9
  have step273 (X0 : G) :  (X0 ◇ (X0 ◇ (X0 ◇ X0))) = (((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) := superpose step177 step14
  have step280 (X0 : G) :  (X0 ◇ (X0 ◇ (X0 ◇ X0))) = (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) := superpose step245 step273
  have step284 (X0 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ X0) = X0 := superpose step9 step268
  have step290 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ (X0 ◇ X0))) := superpose step260 step280
  have step304 (X0 : G) :  (X0 ◇ X0) = (((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0)))) := superpose step111 step15
  have step376 (X0 : G) :  (X0 ◇ X0) = (((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) := superpose step175 step304
  have step398 (X0 : G) :  (X0 ◇ X0) = (((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))) := superpose step172 step376
  have step414 (X0 : G) :  (X0 ◇ X0) = (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0)))) := superpose step290 step398
  have step426 (X0 : G) :  (X0 ◇ X0) = (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ X0) := superpose step9 step414
  have step434 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose step88 step426
  have step440 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step284 step434
  have step449 : sK0 ≠ sK0 := superpose step440 step10
  subsumption step449 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation1479_implies_Equation3 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation1479 G) : Equation3 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have step9 (X0 X1 : G) :  ((X1 ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ (sK0 ◇ sK0) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step17 (X0 : G) :  ((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ X0) = X0 := superpose step11 step9
  have step20 (X0 X1 : G) :  (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step9 step12
  have step29 (X0 : G) :  (X0 ◇ (X0 ◇ (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)))) = X0 := superpose step17 step9
  have step46 (X0 : G) :  (X0 ◇ ((X0 ◇ X0) ◇ X0)) = (X0 ◇ (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0))) := superpose step29 step12
  have step54 (X0 : G) :  (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) = (X0 ◇ (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0))) := superpose step17 step20
  have step74 (X0 : G) :  (X0 ◇ ((X0 ◇ X0) ◇ X0)) = (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) := superpose step46 step54
  have step76 (X0 : G) :  (X0 ◇ ((X0 ◇ X0) ◇ X0)) = X0 := superpose step11 step74
  have step78 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step76 step11
  have step123 : sK0 ≠ sK0 := superpose step78 step10
  subsumption step123 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation1482_implies_Equation1426 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation1482 G) : Equation1426 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have step9 (X0 X1 : G) :  ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X1))) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := mod_symm nh
  have step15 : sK0 ≠ sK0 := superpose step9 step10
  subsumption step15 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation1482_implies_Equation255 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation1482 G) : Equation255 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have step9 (X0 X1 : G) :  ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X1))) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ (((sK0 ◇ sK0) ◇ sK0) ◇ sK0) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step13 (X0 X1 : G) :  (X0 ◇ (X1 ◇ X1)) = (X0 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0)))) := superpose step9 step9
  have step15 (X0 X1 : G) :  (X0 ◇ (X1 ◇ X1)) = ((X1 ◇ X0) ◇ ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X0)))) := superpose step9 step11
  have step18 (X0 X1 : G) :  (X0 ◇ (X1 ◇ X1)) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step9 step12
  have step19 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step21 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = ((X1 ◇ X0) ◇ (((X1 ◇ (X1 ◇ X0)) ◇ X1) ◇ (X0 ◇ (X1 ◇ X0)))) := superpose step12 step11
  have step23 (X0 X1 : G) :  ((X0 ◇ (X1 ◇ X1)) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) = ((X0 ◇ (X1 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X1))) ◇ X0)) := superpose step9 step18
  have step28 (X0 X1 : G) :  (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)) = ((X0 ◇ (X1 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X1))) ◇ X0)) := superpose step18 step12
  have step31 (X0 X1 : G) :  (X1 ◇ X1) = (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)) := superpose step12 step28
  have step33 (X0 X1 : G) :  (X1 ◇ X1) = ((X0 ◇ (X1 ◇ X1)) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step23
  have step67 (X0 X1 : G) :  (((X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) ◇ X1) ◇ (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)))) = ((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ (X1 ◇ X0))) := superpose step19 step31
  have step69 (X0 X1 : G) :  ((X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) ◇ (((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)))) ◇ (X1 ◇ (X1 ◇ X0)))) = X1 := superpose step19 step12
  have step70 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ ((X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) ◇ (X1 ◇ (X1 ◇ X0))))) = X1 := superpose step19 step11
  have step73 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ X1)) ◇ X0) = (X1 ◇ (X0 ◇ X0)) := superpose step19 step18
  have step87 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ (X1 ◇ (X1 ◇ X0))))) = X1 := superpose step18 step70
  have step88 (X0 X1 : G) :  ((X0 ◇ (X1 ◇ X1)) ◇ (((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X1))) ◇ (X1 ◇ (X1 ◇ X0)))) = X1 := superpose step18 step69
  have step90 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ (X1 ◇ X0))) = (((X0 ◇ (X1 ◇ X1)) ◇ X1) ◇ (X0 ◇ (X1 ◇ X1))) := superpose step18 step67
  have step157 (X0 X1 : G) :  (((X0 ◇ (X1 ◇ X1)) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) ◇ (X0 ◇ X0)) = (((X0 ◇ (X1 ◇ X1)) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) ◇ (((X0 ◇ (X1 ◇ X1)) ◇ ((X0 ◇ (X1 ◇ X1)) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0)))) ◇ (X0 ◇ (X1 ◇ X1)))) := superpose step13 step18
  have step164 (X0 X1 : G) :  ((X1 ◇ X0) ◇ (X1 ◇ X0)) = (((X0 ◇ (X1 ◇ X1)) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) ◇ (X0 ◇ X0)) := superpose step12 step157
  have step179 (X0 X1 : G) :  ((X1 ◇ X0) ◇ (X1 ◇ X0)) = ((X1 ◇ X1) ◇ (X0 ◇ X0)) := superpose step33 step164
  have step195 (X0 X1 X2 : G) :  (((X0 ◇ X1) ◇ X2) ◇ (X2 ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1)))) = X2 := superpose step179 step9
  have step262 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X0 ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0)) := superpose step9 step15
  have step1623 (X0 X1 X2 : G) :  (X0 ◇ ((X1 ◇ X1) ◇ (X2 ◇ X2))) = (X0 ◇ ((((X1 ◇ X2) ◇ X0) ◇ X0) ◇ ((X1 ◇ X2) ◇ X0))) := superpose step195 step12
  have step1654 (X0 X1 X2 : G) :  (X0 ◇ ((X1 ◇ X1) ◇ (X2 ◇ X2))) = (X0 ◇ ((X1 ◇ X2) ◇ (X1 ◇ X2))) := superpose step18 step1623
  have step1757 (X0 : G) :  (((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ X0))) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))))) := superpose step262 step21
  have step1781 (X0 : G) :  (((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ X0))) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))))) := superpose step90 step1757
  have step1797 (X0 : G) :  (((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ X0))) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))))) := superpose step1654 step1781
  have step1805 (X0 : G) :  (((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ X0))) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ X0)))) := superpose step15 step1797
  have step1809 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ X0)))) := superpose step9 step1805
  have step1811 (X0 : G) :  (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) = X0 := superpose step9 step1809
  have step1814 (X0 : G) :  ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0)) = X0 := superpose step1811 step87
  have step2093 (X0 : G) :  (X0 ◇ (((X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))) ◇ X0) ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))))) = X0 := superpose step1814 step88
  have step2138 (X0 : G) :  (X0 ◇ (((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))))) = X0 := superpose step73 step2093
  have step2161 (X0 : G) :  (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))))) = X0 := superpose step1814 step2138
  have step3115 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))))) ◇ X0)) := superpose step2161 step19
  have step3143 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))) := superpose step12 step3115
  have step6168 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ X0) = ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0)) := superpose step3143 step73
  have step6236 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ X0) = X0 := superpose step1814 step6168
  have step6743 : sK0 ≠ sK0 := superpose step6236 step10
  subsumption step6743 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation1482_implies_Equation817 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation1482 G) : Equation817 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have step9 (X0 X1 : G) :  ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X1))) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step13 (X0 X1 : G) :  (X0 ◇ (X1 ◇ X1)) = (X0 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0)))) := superpose step9 step9
  have step15 (X0 X1 : G) :  (X0 ◇ (X1 ◇ X1)) = ((X1 ◇ X0) ◇ ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X0)))) := superpose step9 step11
  have step18 (X0 X1 : G) :  (X0 ◇ (X1 ◇ X1)) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step9 step12
  have step19 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step20 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose step11 step12
  have step21 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = ((X1 ◇ X0) ◇ (((X1 ◇ (X1 ◇ X0)) ◇ X1) ◇ (X0 ◇ (X1 ◇ X0)))) := superpose step12 step11
  have step23 (X0 X1 : G) :  ((X0 ◇ (X1 ◇ X1)) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) = ((X0 ◇ (X1 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X1))) ◇ X0)) := superpose step9 step18
  have step28 (X0 X1 : G) :  (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)) = ((X0 ◇ (X1 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X1))) ◇ X0)) := superpose step18 step12
  have step31 (X0 X1 : G) :  (X1 ◇ X1) = (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)) := superpose step12 step28
  have step33 (X0 X1 : G) :  (X1 ◇ X1) = ((X0 ◇ (X1 ◇ X1)) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step23
  have step42 (X0 X1 : G) :  (X1 ◇ X1) = ((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) ◇ X0) := superpose step11 step31
  have step45 (X0 : G) :  ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) = ((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) := superpose step20 step31
  have step53 (X0 : G) :  ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) := superpose step31 step45
  have step62 (X0 X1 : G) :  (((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)))) ◇ (X1 ◇ (X1 ◇ X0))) = (X1 ◇ (((X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) ◇ X1) ◇ (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))))) := superpose step19 step19
  have step67 (X0 X1 : G) :  (((X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) ◇ X1) ◇ (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)))) = ((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ (X1 ◇ X0))) := superpose step19 step31
  have step68 (X0 X1 : G) :  (X1 ◇ (((X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) ◇ X1) ◇ (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))))) = (X1 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ (X1 ◇ X0)))) := superpose step19 step18
  have step69 (X0 X1 : G) :  ((X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) ◇ (((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)))) ◇ (X1 ◇ (X1 ◇ X0)))) = X1 := superpose step19 step12
  have step70 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ ((X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) ◇ (X1 ◇ (X1 ◇ X0))))) = X1 := superpose step19 step11
  have step73 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ X1)) ◇ X0) = (X1 ◇ (X0 ◇ X0)) := superpose step19 step18
  have step87 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ (X1 ◇ (X1 ◇ X0))))) = X1 := superpose step18 step70
  have step88 (X0 X1 : G) :  ((X0 ◇ (X1 ◇ X1)) ◇ (((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X1))) ◇ (X1 ◇ (X1 ◇ X0)))) = X1 := superpose step18 step69
  have step89 (X0 X1 : G) :  (X1 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ (X1 ◇ X0)))) = (X1 ◇ (((X0 ◇ (X1 ◇ X1)) ◇ X1) ◇ (X0 ◇ (X1 ◇ X1)))) := superpose step18 step68
  have step90 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ (X1 ◇ X0))) = (((X0 ◇ (X1 ◇ X1)) ◇ X1) ◇ (X0 ◇ (X1 ◇ X1))) := superpose step18 step67
  have step91 (X0 X1 : G) :  (((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X1))) ◇ (X1 ◇ (X1 ◇ X0))) = (X1 ◇ (((X0 ◇ (X1 ◇ X1)) ◇ X1) ◇ (X0 ◇ (X1 ◇ X1)))) := superpose step18 step62
  have step102 (X0 X1 : G) :  (X1 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ (X1 ◇ X0)))) = (((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X1))) ◇ (X1 ◇ (X1 ◇ X0))) := superpose step89 step91
  have step113 (X0 : G) :  ((X0 ◇ X0) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) = (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) := superpose step20 step73
  have step131 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) := superpose step31 step113
  have step136 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0))) := superpose step53 step131
  have step157 (X0 X1 : G) :  (((X0 ◇ (X1 ◇ X1)) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) ◇ (X0 ◇ X0)) = (((X0 ◇ (X1 ◇ X1)) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) ◇ (((X0 ◇ (X1 ◇ X1)) ◇ ((X0 ◇ (X1 ◇ X1)) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0)))) ◇ (X0 ◇ (X1 ◇ X1)))) := superpose step13 step18
  have step164 (X0 X1 : G) :  ((X1 ◇ X0) ◇ (X1 ◇ X0)) = (((X0 ◇ (X1 ◇ X1)) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) ◇ (X0 ◇ X0)) := superpose step12 step157
  have step179 (X0 X1 : G) :  ((X1 ◇ X0) ◇ (X1 ◇ X0)) = ((X1 ◇ X1) ◇ (X0 ◇ X0)) := superpose step33 step164
  have step203 (X0 X1 X2 : G) :  (((X0 ◇ X1) ◇ X2) ◇ (X2 ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1)))) = X2 := superpose step179 step9
  have step262 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X0 ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0)) := superpose step9 step15
  have step304 (X0 X1 : G) :  (((X0 ◇ X1) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) = (((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X1) ◇ X1)))) ◇ (X0 ◇ X1)) := superpose step31 step42
  have step351 (X0 X1 : G) :  (((X0 ◇ X1) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) = (((X0 ◇ X0) ◇ ((X0 ◇ X1) ◇ X1)) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) := superpose step73 step304
  have step1345 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose step136 step12
  have step1386 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) := superpose step351 step1345
  have step1623 (X0 X1 X2 : G) :  (X0 ◇ ((X1 ◇ X1) ◇ (X2 ◇ X2))) = (X0 ◇ ((((X1 ◇ X2) ◇ X0) ◇ X0) ◇ ((X1 ◇ X2) ◇ X0))) := superpose step203 step12
  have step1654 (X0 X1 X2 : G) :  (X0 ◇ ((X1 ◇ X1) ◇ (X2 ◇ X2))) = (X0 ◇ ((X1 ◇ X2) ◇ (X1 ◇ X2))) := superpose step18 step1623
  have step1758 (X0 : G) :  (((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ X0))) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))))) := superpose step262 step21
  have step1781 (X0 : G) :  (((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ X0))) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))))) := superpose step90 step1758
  have step1797 (X0 : G) :  (((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ X0))) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))))) := superpose step1654 step1781
  have step1805 (X0 : G) :  (((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ X0))) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ X0)))) := superpose step15 step1797
  have step1809 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ X0)))) := superpose step9 step1805
  have step1811 (X0 : G) :  (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) = X0 := superpose step9 step1809
  have step1814 (X0 : G) :  ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0)) = X0 := superpose step1811 step87
  have step2094 (X0 : G) :  (X0 ◇ (((X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))) ◇ X0) ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))))) = X0 := superpose step1814 step88
  have step2137 (X0 : G) :  (X0 ◇ (((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))))) = X0 := superpose step73 step2094
  have step2161 (X0 : G) :  (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))))) = X0 := superpose step1814 step2137
  have step3119 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))))) ◇ X0)) := superpose step2161 step19
  have step3146 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))) := superpose step12 step3119
  have step4430 (X0 : G) :  (X0 ◇ ((X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))) ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))))) = (((X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))) ◇ X0) ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))))) := superpose step1814 step102
  have step4632 (X0 : G) :  ((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) = (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0))) := superpose step3146 step4430
  have step4717 (X0 : G) :  (X0 ◇ ((X0 ◇ X0) ◇ X0)) = ((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) := superpose step1386 step4632
  have step4772 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose step31 step4717
  have step5528 : sK0 ≠ (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0))) := superpose step4772 step10
  subsumption step5528 step11


@[equational_result]
theorem Finite.Equation677_and_Equation1489_implies_Equation1426 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation1489 G) : Equation1426 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have step9 (X0 X1 : G) :  ((X1 ◇ X0) ◇ (X1 ◇ (X0 ◇ X1))) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := mod_symm nh
  have step16 : sK0 ≠ sK0 := superpose step9 step10
  subsumption step16 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation1489_implies_Equation255 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation1489 G) : Equation255 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have step9 (X0 X1 : G) :  ((X1 ◇ X0) ◇ (X1 ◇ (X0 ◇ X1))) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ (((sK0 ◇ sK0) ◇ sK0) ◇ sK0) := mod_symm nh
  have step15 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ X0) = X0 := superpose step9 step9
  have step18 : sK0 ≠ sK0 := superpose step15 step10
  subsumption step18 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation1489_implies_Equation817 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation1489 G) : Equation817 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have step9 (X0 X1 : G) :  ((X1 ◇ X0) ◇ (X1 ◇ (X0 ◇ X1))) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step14 (X0 X1 : G) :  (X1 ◇ X0) = (((X1 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X0)) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X0)) := superpose step9 step9
  have step24 (X0 X1 : G) :  (X1 ◇ (X0 ◇ X1)) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step9 step12
  have step25 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step70 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ X1)) ◇ X0) = (X0 ◇ (X1 ◇ X0)) := superpose step25 step24
  have step212 (X0 : G) :  (X0 ◇ X0) = (((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) := superpose step70 step14
  have step383 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose step212 step24
  have step500 : sK0 ≠ (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0))) := superpose step383 step10
  subsumption step500 step11


@[equational_result]
theorem Finite.Equation677_and_Equation1516_implies_Equation1426 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation1516 G) : Equation1426 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have step10 (X0 X1 : G) :  ((X1 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) = X0 := mod_symm (h ..)
  have step11 : sK0 ≠ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := mod_symm nh
  have step17 : sK0 ≠ sK0 := superpose step10 step11
  subsumption step17 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation1516_implies_Equation255 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation1516 G) : Equation255 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have step10 (X0 X1 : G) :  ((X1 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) = X0 := mod_symm (h ..)
  have step11 : sK0 ≠ (((sK0 ◇ sK0) ◇ sK0) ◇ sK0) := mod_symm nh
  have step13 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step19 (X0 : G) :  ((((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) = X0 := superpose step13 step10
  have step42 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) = ((X0 ◇ X0) ◇ ((((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0)) := superpose step19 step10
  have step43 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) := superpose step19 step42
  have step145 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ X0) = X0 := superpose step43 step19
  have step198 : sK0 ≠ sK0 := superpose step145 step11
  subsumption step198 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation1516_implies_Equation817 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation1516 G) : Equation817 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have step10 (X0 X1 : G) :  ((X1 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) = X0 := mod_symm (h ..)
  have step11 : sK0 ≠ (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := mod_symm nh
  have step12 (X Y : G) : (((Y ◇ Y) ◇ X) ◇ (((Y ◇ Y) ◇ X) ◇ Y)) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (s ◇ (s ◇ Y))) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => ((Y ◇ Y) ◇ s)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => ((Y ◇ Y) ◇ s)) (fun s => (s ◇ (s ◇ Y))) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step13 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step14 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step15 (X0 X1 : G) :  (X1 ◇ X1) = (((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X1 ◇ X1) ◇ X0)) := superpose step10 step10
  have step17 (X0 X1 : G) :  (X0 ◇ (X0 ◇ X1)) = ((X1 ◇ X1) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1)))) := superpose step10 step13
  have step19 (X0 : G) :  ((((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) = X0 := superpose step13 step10
  have step21 (X0 X1 : G) :  (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (((X1 ◇ X1) ◇ X0) ◇ (X1 ◇ X1))) := superpose step10 step14
  have step22 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step14 step14
  have step30 (X0 X1 : G) :  ((((X1 ◇ X1) ◇ X0) ◇ X1) ◇ (X0 ◇ ((X1 ◇ X1) ◇ X0))) = X1 := superpose step12 step14
  have step42 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) = ((X0 ◇ X0) ◇ ((((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0)) := superpose step19 step10
  have step43 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) := superpose step19 step42
  have step56 (X0 X1 : G) :  (((X1 ◇ X1) ◇ X0) ◇ (X1 ◇ X1)) = ((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X0)) := superpose step21 step14
  have step59 (X0 X1 : G) :  (X0 ◇ X1) = (((X1 ◇ X1) ◇ X0) ◇ (X1 ◇ X1)) := superpose step14 step56
  have step65 (X0 X1 : G) :  (X0 ◇ (X1 ◇ X1)) = ((X0 ◇ (X0 ◇ X1)) ◇ X1) := superpose step10 step59
  have step145 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ X0) = X0 := superpose step43 step19
  have step221 (X0 X1 : G) :  (((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1))) ◇ (X0 ◇ (X0 ◇ X1))) = (X1 ◇ (((X0 ◇ (X1 ◇ X1)) ◇ X1) ◇ (X0 ◇ (X1 ◇ X1)))) := superpose step65 step22
  have step393 (X0 : G) :  ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0)))) = (((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0)))) ◇ (X0 ◇ (X0 ◇ X0)))) := superpose step17 step17
  have step429 (X0 : G) :  ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0)))) = (((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))))) := superpose step65 step393
  have step452 (X0 : G) :  (((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ X0))) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0)))) := superpose step17 step429
  have step459 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = (((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ X0))) := superpose step10 step452
  have step462 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = (X0 ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0)))) := superpose step221 step459
  have step465 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))) := superpose step65 step462
  have step692 (X0 : G) :  (((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) ◇ X0) ◇ ((((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)))) = X0 := superpose step465 step30
  have step717 (X0 : G) :  (((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = X0 := superpose step15 step692
  have step728 (X0 : G) :  ((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = X0 := superpose step59 step717
  have step734 (X0 : G) :  (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = X0 := superpose step145 step728
  have step820 : sK0 ≠ sK0 := superpose step734 step11
  subsumption step820 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation159_implies_Equation3 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation159 G) : Equation3 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have step9 (X0 X1 : G) :  ((X0 ◇ X1) ◇ (X1 ◇ X0)) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ (sK0 ◇ sK0) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step17 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ X0) ◇ X1)) = (((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X1) ◇ X0) := superpose step11 step9
  have step18 (X0 X1 : G) :  (X0 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X1)) = X1 := superpose step11 step9
  have step19 (X0 X1 : G) :  (X1 ◇ X0) = (X0 ◇ (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1))) := superpose step9 step12
  have step20 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step21 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose step11 step12
  have step44 (X0 X1 : G) :  (((X1 ◇ X0) ◇ X1) ◇ (X1 ◇ X0)) = ((X0 ◇ X1) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X1)) := superpose step19 step12
  have step85 (X0 : G) :  (X0 ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X0 ◇ X0) ◇ X0)) := superpose step21 step9
  have step229 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose step20 step19
  have step257 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose step9 step229
  have step265 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) := superpose step229 step9
  have step273 (X0 : G) :  (X0 ◇ (X0 ◇ (X0 ◇ X0))) = ((X0 ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0))) := superpose step229 step19
  have step279 (X0 : G) :  ((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) = (X0 ◇ (X0 ◇ (X0 ◇ X0))) := superpose step44 step273
  have step286 (X0 : G) :  (X0 ◇ ((X0 ◇ X0) ◇ X0)) = (X0 ◇ (X0 ◇ (X0 ◇ X0))) := superpose step257 step279
  have step397 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) = ((((X0 ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose step257 step17
  have step398 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X0 ◇ X0) ◇ X0))) := superpose step257 step18
  have step406 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose step85 step398
  have step407 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) := superpose step85 step397
  have step416 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = X0 := superpose step9 step406
  have step417 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) := superpose step286 step407
  have step421 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose step265 step417
  have step422 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = X0 := superpose step9 step421
  have step497 (X0 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ X0) = X0 := superpose step416 step9
  have step523 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step422 step497
  have step616 : sK0 ≠ sK0 := superpose step523 step10
  subsumption step616 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation16_implies_Equation1313 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation16 G) : Equation1313 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X1 ◇ (X1 ◇ X0)) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ (sK1 ◇ (((sK1 ◇ sK0) ◇ sK0) ◇ sK1)) := mod_symm nh
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step24 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X0) = ((X1 ◇ (X1 ◇ X0)) ◇ X1) := superpose step12 step9
  have step25 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X0) = (X0 ◇ X1) := superpose step9 step24
  have step83 : sK0 ≠ (sK1 ◇ ((sK0 ◇ sK1) ◇ sK1)) := superpose step25 step10
  have step84 : sK0 ≠ (sK1 ◇ (sK1 ◇ sK0)) := superpose step25 step83
  subsumption step84 step9


@[equational_result]
theorem Finite.Equation677_and_Equation16_implies_Equation1444 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation16 G) : Equation1444 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X1 ◇ (X1 ◇ X0)) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK0))) := mod_symm nh
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step21 (X0 X1 : G) :  ((X1 ◇ X0) ◇ (X0 ◇ X1)) = X0 := superpose step9 step12
  have step24 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = ((X1 ◇ X0) ◇ X0) := superpose step12 step9
  have step25 (X0 X1 : G) :  (X0 ◇ X1) = ((X1 ◇ X0) ◇ X0) := superpose step9 step24
  have step79 (X0 X1 : G) :  ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ X0))) = X0 := superpose step25 step21
  have step749 : sK0 ≠ sK0 := superpose step79 step10
  subsumption step749 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation16_implies_Equation1482 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation16 G) : Equation1482 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X1 ◇ (X1 ◇ X0)) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK1))) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step16 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = X0 := superpose step11 step9
  have step21 (X0 X1 : G) :  ((X1 ◇ X0) ◇ (X0 ◇ X1)) = X0 := superpose step9 step12
  have step50 (X0 : G) :  (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose step21 step16
  have step51 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step9 step50
  have step66 : sK0 ≠ ((sK1 ◇ sK0) ◇ (sK0 ◇ sK1)) := superpose step51 step10
  subsumption step66 step21


@[equational_result]
theorem Finite.Equation677_and_Equation16_implies_Equation1655 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation16 G) : Equation1655 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X1 ◇ (X1 ◇ X0)) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ ((sK0 ◇ sK1) ◇ ((sK1 ◇ sK0) ◇ sK1)) := mod_symm nh
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step21 (X0 X1 : G) :  ((X1 ◇ X0) ◇ (X0 ◇ X1)) = X0 := superpose step9 step12
  have step24 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = ((X1 ◇ X0) ◇ X0) := superpose step12 step9
  have step25 (X0 X1 : G) :  (X0 ◇ X1) = ((X1 ◇ X0) ◇ X0) := superpose step9 step24
  have step68 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X1) = (X0 ◇ (X1 ◇ X0)) := superpose step9 step25
  have step79 (X0 X1 : G) :  ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ X0))) = X0 := superpose step25 step21
  have step186 : sK0 ≠ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK0))) := superpose step68 step10
  subsumption step186 step79


@[equational_result]
theorem Finite.Equation677_and_Equation16_implies_Equation1691 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation16 G) : Equation1691 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X1 ◇ (X1 ◇ X0)) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ sK0)) := mod_symm nh
  have step13 : sK0 ≠ sK0 := superpose step9 step10
  subsumption step13 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation16_implies_Equation1840 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation16 G) : Equation1840 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X1 ◇ (X1 ◇ X0)) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ sK0)) := mod_symm nh
  have step13 : sK0 ≠ (sK1 ◇ (sK1 ◇ sK0)) := superpose step9 step10
  subsumption step13 step9


@[equational_result]
theorem Finite.Equation677_and_Equation16_implies_Equation209 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation16 G) : Equation209 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X1 ◇ (X1 ◇ X0)) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK1) := mod_symm nh
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step24 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = ((X1 ◇ X0) ◇ X0) := superpose step12 step9
  have step25 (X0 X1 : G) :  (X0 ◇ X1) = ((X1 ◇ X0) ◇ X0) := superpose step9 step24
  have step68 (X0 X1 : G) :  (X0 ◇ (X1 ◇ X0)) = ((X1 ◇ X0) ◇ X1) := superpose step9 step25
  have step200 (X0 X1 : G) :  (X1 ◇ (X1 ◇ X0)) = ((X0 ◇ (X1 ◇ X0)) ◇ X1) := superpose step68 step25
  have step203 (X0 X1 : G) :  ((X0 ◇ (X1 ◇ X0)) ◇ X1) = X0 := superpose step9 step200
  have step353 : sK0 ≠ sK0 := superpose step203 step10
  subsumption step353 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation16_implies_Equation2450 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation16 G) : Equation2450 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X1 ◇ (X1 ◇ X0)) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ ((sK0 ◇ ((sK0 ◇ sK1) ◇ sK1)) ◇ sK1) := mod_symm nh
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step24 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = ((X1 ◇ X0) ◇ X0) := superpose step12 step9
  have step25 (X0 X1 : G) :  (X0 ◇ X1) = ((X1 ◇ X0) ◇ X0) := superpose step9 step24
  have step68 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X1) = (X0 ◇ (X1 ◇ X0)) := superpose step9 step25
  have step83 : sK0 ≠ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK1) := superpose step25 step10
  have step252 (X0 X1 : G) :  (X1 ◇ (X1 ◇ X0)) = ((X0 ◇ (X1 ◇ X0)) ◇ X1) := superpose step68 step25
  have step273 (X0 X1 : G) :  ((X0 ◇ (X1 ◇ X0)) ◇ X1) = X0 := superpose step9 step252
  have step551 : sK0 ≠ sK0 := superpose step273 step83
  subsumption step551 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation16_implies_Equation2531 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation16 G) : Equation2531 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X1 ◇ (X1 ◇ X0)) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ ((sK1 ◇ ((sK1 ◇ sK0) ◇ sK0)) ◇ sK1) := mod_symm nh
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step24 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X0) = ((X1 ◇ (X1 ◇ X0)) ◇ X1) := superpose step12 step9
  have step25 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X0) = (X0 ◇ X1) := superpose step9 step24
  have step74 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X0) = (X0 ◇ (X1 ◇ X0)) := superpose step25 step25
  have step83 : sK0 ≠ ((sK1 ◇ (sK0 ◇ sK1)) ◇ sK1) := superpose step25 step10
  have step647 : sK0 ≠ (sK1 ◇ ((sK0 ◇ sK1) ◇ sK1)) := superpose step74 step83
  have step648 : sK0 ≠ (sK1 ◇ (sK1 ◇ sK0)) := superpose step25 step647
  subsumption step648 step9


@[equational_result]
theorem Finite.Equation677_and_Equation16_implies_Equation3079 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation16 G) : Equation3079 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X1 ◇ (X1 ◇ X0)) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ ((((sK0 ◇ sK1) ◇ sK1) ◇ sK1) ◇ sK1) := mod_symm nh
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step24 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = ((X1 ◇ X0) ◇ X0) := superpose step12 step9
  have step25 (X0 X1 : G) :  (X0 ◇ X1) = ((X1 ◇ X0) ◇ X0) := superpose step9 step24
  have step85 : sK0 ≠ (sK1 ◇ ((sK0 ◇ sK1) ◇ sK1)) := superpose step25 step10
  have step86 : sK0 ≠ (sK1 ◇ (sK1 ◇ sK0)) := superpose step25 step85
  subsumption step86 step9


@[equational_result]
theorem Finite.Equation677_and_Equation16_implies_Equation3103 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation16 G) : Equation3103 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X1 ◇ (X1 ◇ X0)) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ ((((sK1 ◇ sK0) ◇ sK0) ◇ sK0) ◇ sK1) := mod_symm nh
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step21 (X0 X1 : G) :  ((X1 ◇ X0) ◇ (X0 ◇ X1)) = X0 := superpose step9 step12
  have step24 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X0) = ((X1 ◇ (X1 ◇ X0)) ◇ X1) := superpose step12 step9
  have step25 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X0) = (X0 ◇ X1) := superpose step9 step24
  have step42 (X0 X1 : G) :  (((X1 ◇ X0) ◇ X1) ◇ X0) = X1 := superpose step9 step21
  have step83 : sK0 ≠ (((sK0 ◇ sK1) ◇ sK0) ◇ sK1) := superpose step25 step10
  subsumption step83 step42


@[equational_result]
theorem Finite.Equation677_and_Equation16_implies_Equation3345 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation16 G) : Equation3345 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X1 ◇ (X1 ◇ X0)) = X0 := mod_symm (h ..)
  have step10 : (sK0 ◇ sK1) ≠ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) := mod_symm nh
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step24 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = ((X1 ◇ X0) ◇ X0) := superpose step12 step9
  have step25 (X0 X1 : G) :  (X0 ◇ X1) = ((X1 ◇ X0) ◇ X0) := superpose step9 step24
  have step68 (X0 X1 : G) :  (X0 ◇ (X1 ◇ X0)) = ((X1 ◇ X0) ◇ X1) := superpose step9 step25
  have step176 (X0 X1 : G) :  (X1 ◇ (X0 ◇ (X1 ◇ X0))) = ((X0 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)) := superpose step68 step68
  have step222 (X0 X1 : G) :  (X1 ◇ (X0 ◇ (X1 ◇ X0))) = ((X1 ◇ X0) ◇ X0) := superpose step25 step176
  have step238 (X0 X1 : G) :  (X0 ◇ X1) = (X1 ◇ (X0 ◇ (X1 ◇ X0))) := superpose step25 step222
  have step1374 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose step238 step10
  subsumption step1374 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation16_implies_Equation3556 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation16 G) : Equation3556 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X1 ◇ (X1 ◇ X0)) = X0 := mod_symm (h ..)
  have step10 : (sK0 ◇ sK1) ≠ (sK1 ◇ ((sK1 ◇ sK0) ◇ sK1)) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step17 (X0 X1 : G) :  (X1 ◇ X0) = (X0 ◇ ((X1 ◇ X0) ◇ X1)) := superpose step11 step9
  have step24 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = ((X1 ◇ X0) ◇ X0) := superpose step12 step9
  have step25 (X0 X1 : G) :  (X0 ◇ X1) = ((X1 ◇ X0) ◇ X0) := superpose step9 step24
  have step68 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X1) = (X0 ◇ (X1 ◇ X0)) := superpose step9 step25
  have step74 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X0) = (X0 ◇ (X1 ◇ X0)) := superpose step25 step25
  have step140 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X0) = (X1 ◇ (((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X1) ◇ X1))) := superpose step17 step11
  have step150 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X0) = (X1 ◇ (((X0 ◇ X1) ◇ X0) ◇ (X1 ◇ X0))) := superpose step25 step140
  have step158 (X0 X1 : G) :  (X0 ◇ (X1 ◇ X0)) = (X1 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0))) := superpose step74 step150
  have step163 (X0 X1 : G) :  (X0 ◇ (X1 ◇ X0)) = (X1 ◇ ((X1 ◇ X0) ◇ X0)) := superpose step25 step158
  have step167 (X0 X1 : G) :  (X0 ◇ (X1 ◇ X0)) = (X1 ◇ (X0 ◇ X1)) := superpose step25 step163
  have step186 : (sK0 ◇ sK1) ≠ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) := superpose step68 step10
  have step217 : (sK0 ◇ sK1) ≠ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) := superpose step167 step186
  subsumption step217 step9


@[equational_result]
theorem Finite.Equation677_and_Equation16_implies_Equation384 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation16 G) : Equation384 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X1 ◇ (X1 ◇ X0)) = X0 := mod_symm (h ..)
  have step10 : (sK0 ◇ sK1) ≠ ((sK1 ◇ sK0) ◇ sK0) := mod_symm nh
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step24 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X0) = ((X1 ◇ (X1 ◇ X0)) ◇ X1) := superpose step12 step9
  have step25 (X0 X1 : G) :  (X0 ◇ X1) = ((X1 ◇ X0) ◇ X0) := superpose step9 step24
  have step83 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose step25 step10
  subsumption step83 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation16_implies_Equation4321 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation16 G) : Equation4321 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X1 ◇ (X1 ◇ X0)) = X0 := mod_symm (h ..)
  have step10 : (sK0 ◇ (sK1 ◇ sK0)) ≠ (sK1 ◇ (sK0 ◇ sK1)) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step17 (X0 X1 : G) :  (X1 ◇ X0) = (X0 ◇ ((X1 ◇ X0) ◇ X1)) := superpose step11 step9
  have step24 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = ((X1 ◇ X0) ◇ X0) := superpose step12 step9
  have step25 (X0 X1 : G) :  (X0 ◇ X1) = ((X1 ◇ X0) ◇ X0) := superpose step9 step24
  have step74 (X0 X1 : G) :  (X0 ◇ (X1 ◇ X0)) = ((X0 ◇ X1) ◇ X0) := superpose step25 step25
  have step139 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X0) = (X1 ◇ (((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X1) ◇ X1))) := superpose step17 step11
  have step150 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X0) = (X1 ◇ (((X0 ◇ X1) ◇ X0) ◇ (X1 ◇ X0))) := superpose step25 step139
  have step158 (X0 X1 : G) :  (X0 ◇ (X1 ◇ X0)) = (X1 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0))) := superpose step74 step150
  have step163 (X0 X1 : G) :  (X0 ◇ (X1 ◇ X0)) = (X1 ◇ ((X1 ◇ X0) ◇ X0)) := superpose step25 step158
  have step167 (X0 X1 : G) :  (X0 ◇ (X1 ◇ X0)) = (X1 ◇ (X0 ◇ X1)) := superpose step25 step163
  have step958 : (sK0 ◇ (sK1 ◇ sK0)) ≠ (sK0 ◇ (sK1 ◇ sK0)) := superpose step167 step10
  subsumption step958 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation16_implies_Equation466 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation16 G) : Equation466 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X1 ◇ (X1 ◇ X0)) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := mod_symm nh
  have step13 : sK0 ≠ (sK1 ◇ (sK1 ◇ sK0)) := superpose step9 step10
  subsumption step13 step9


@[equational_result]
theorem Finite.Equation677_and_Equation16_implies_Equation513 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation16 G) : Equation513 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X1 ◇ (X1 ◇ X0)) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := mod_symm nh
  have step15 : sK0 ≠ (sK1 ◇ (sK1 ◇ sK0)) := superpose step9 step10
  subsumption step15 step9


@[equational_result]
theorem Finite.Equation677_and_Equation1654_implies_Equation3 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation1654 G) : Equation3 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have step9 (X0 X1 : G) :  ((X0 ◇ X1) ◇ ((X1 ◇ X0) ◇ X0)) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ (sK0 ◇ sK0) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step13 (X0 X1 : G) :  (X0 ◇ X1) = (X0 ◇ ((((X1 ◇ X0) ◇ X0) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1))) := superpose step9 step9
  have step15 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X0) = ((X0 ◇ X1) ◇ (((X1 ◇ X0) ◇ X0) ◇ (X0 ◇ (X0 ◇ X1)))) := superpose step9 step11
  have step16 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ X0) ◇ X1)) = (X1 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X0 ◇ X1))) := superpose step11 step11
  have step19 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X0) = (X0 ◇ (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1))) := superpose step9 step12
  have step20 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step21 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose step9 step12
  have step51 (X0 X1 : G) :  (((X1 ◇ X0) ◇ X1) ◇ (X1 ◇ X0)) = (((X0 ◇ X1) ◇ X1) ◇ ((X1 ◇ ((X0 ◇ X1) ◇ X1)) ◇ X1)) := superpose step19 step12
  have step167 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose step20 step19
  have step237 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ X0) = (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0)))) := superpose step167 step19
  have step242 (X0 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))))) = X0 := superpose step167 step11
  have step257 (X0 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) = X0 := superpose step21 step242
  have step259 (X0 : G) :  (X0 ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ X0) := superpose step21 step237
  have step323 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)))) = X0 := superpose step257 step15
  have step348 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose step9 step323
  have step413 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0)) = (X0 ◇ ((((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0)) ◇ (X0 ◇ X0))) := superpose step259 step16
  have step427 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) = (X0 ◇ ((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) := superpose step51 step413
  have step437 (X0 : G) :  (X0 ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) := superpose step13 step427
  have step442 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step348 step437
  have step541 : sK0 ≠ sK0 := superpose step442 step10
  subsumption step541 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation1655_implies_Equation3 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation1655 G) : Equation3 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have step9 (X0 X1 : G) :  ((X0 ◇ X1) ◇ ((X1 ◇ X0) ◇ X1)) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ (sK0 ◇ sK0) := mod_symm nh
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step19 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X1) = (X0 ◇ (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1))) := superpose step9 step12
  have step20 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step21 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose step9 step12
  have step33 (X0 : G) :  (((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) = (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0)) := superpose step21 step19
  have step37 (X0 X1 : G) :  (((X1 ◇ X0) ◇ X1) ◇ (X1 ◇ X0)) = (((X0 ◇ X1) ◇ X0) ◇ ((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1)) := superpose step19 step12
  have step41 (X0 : G) :  (((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) = (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) := superpose step37 step33
  have step67 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose step20 step19
  have step78 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) = (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0)))) := superpose step67 step19
  have step81 (X0 : G) :  (X0 ◇ ((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0))) = (((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) := superpose step67 step20
  have step91 (X0 : G) :  (X0 ◇ ((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0))) = (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) := superpose step41 step81
  have step92 (X0 : G) :  (X0 ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) := superpose step21 step78
  have step94 (X0 : G) :  (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) = (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) := superpose step20 step91
  have step95 (X0 : G) :  (X0 ◇ X0) = (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose step92 step94
  have step96 (X0 : G) :  (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose step9 step95
  have step151 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) := superpose step96 step12
  have step160 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step12 step151
  have step265 : sK0 ≠ sK0 := superpose step160 step10
  subsumption step265 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation16_implies_Equation633 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation16 G) : Equation633 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X1 ◇ (X1 ◇ X0)) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ (sK0 ◇ (sK1 ◇ ((sK0 ◇ sK1) ◇ sK1))) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step16 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = X0 := superpose step11 step9
  have step21 (X0 X1 : G) :  ((X1 ◇ X0) ◇ (X0 ◇ X1)) = X0 := superpose step9 step12
  have step24 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = ((X1 ◇ X0) ◇ X0) := superpose step12 step9
  have step25 (X0 X1 : G) :  (X0 ◇ X1) = ((X1 ◇ X0) ◇ X0) := superpose step9 step24
  have step47 (X0 : G) :  (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose step21 step16
  have step52 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step9 step47
  have step83 : sK0 ≠ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) := superpose step25 step10
  have step84 : sK0 ≠ (sK0 ◇ sK0) := superpose step9 step83
  subsumption step84 step52


@[equational_result]
theorem Finite.Equation677_and_Equation16_implies_Equation642 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation16 G) : Equation642 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X1 ◇ (X1 ◇ X0)) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ (sK0 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ sK0))) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step16 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = X0 := superpose step11 step9
  have step21 (X0 X1 : G) :  ((X1 ◇ X0) ◇ (X0 ◇ X1)) = X0 := superpose step9 step12
  have step50 (X0 : G) :  (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose step21 step16
  have step51 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step9 step50
  have step66 : sK0 ≠ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) := superpose step51 step10
  have step67 : sK0 ≠ (sK0 ◇ sK0) := superpose step9 step66
  subsumption step67 step51


@[equational_result]
theorem Finite.Equation677_and_Equation16_implies_Equation669 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation16 G) : Equation669 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X1 ◇ (X1 ◇ X0)) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ (sK1 ◇ (sK0 ◇ ((sK0 ◇ sK1) ◇ sK0))) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step17 (X0 X1 : G) :  (X1 ◇ X0) = (X0 ◇ ((X1 ◇ X0) ◇ X1)) := superpose step11 step9
  have step24 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = ((X1 ◇ X0) ◇ X0) := superpose step12 step9
  have step25 (X0 X1 : G) :  (X0 ◇ X1) = ((X1 ◇ X0) ◇ X0) := superpose step9 step24
  have step68 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X1) = (X0 ◇ (X1 ◇ X0)) := superpose step9 step25
  have step74 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X0) = (X0 ◇ (X1 ◇ X0)) := superpose step25 step25
  have step139 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X0) = (X1 ◇ (((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X1) ◇ X1))) := superpose step17 step11
  have step150 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X0) = (X1 ◇ (((X0 ◇ X1) ◇ X0) ◇ (X1 ◇ X0))) := superpose step25 step139
  have step158 (X0 X1 : G) :  (X0 ◇ (X1 ◇ X0)) = (X1 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0))) := superpose step74 step150
  have step163 (X0 X1 : G) :  (X0 ◇ (X1 ◇ X0)) = (X1 ◇ ((X1 ◇ X0) ◇ X0)) := superpose step25 step158
  have step167 (X0 X1 : G) :  (X0 ◇ (X1 ◇ X0)) = (X1 ◇ (X0 ◇ X1)) := superpose step25 step163
  have step186 : sK0 ≠ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := superpose step68 step10
  have step217 : sK0 ≠ (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := superpose step167 step186
  have step239 : sK0 ≠ (sK1 ◇ (sK1 ◇ sK0)) := superpose step9 step217
  subsumption step239 step9


@[equational_result]
theorem Finite.Equation677_and_Equation1685_implies_Equation3 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation1685 G) : Equation3 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have step9 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X0 ◇ X1) ◇ X1)) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ (sK0 ◇ sK0) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step13 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X1) = (X0 ◇ ((((X0 ◇ X1) ◇ X1) ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0))) := superpose step9 step9
  have step16 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ X0) ◇ X1)) = (X1 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X0 ◇ X1))) := superpose step11 step11
  have step19 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step9 step12
  have step20 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step21 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose step9 step12
  have step62 (X0 X1 : G) :  ((X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) ◇ (((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)))) ◇ (X1 ◇ (X1 ◇ X0)))) = X1 := superpose step20 step12
  have step66 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ X1)) ◇ X0) = ((X1 ◇ X0) ◇ X0) := superpose step20 step19
  have step76 (X0 X1 : G) :  (((X0 ◇ X1) ◇ X1) ◇ (((X1 ◇ (X1 ◇ X0)) ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X1 ◇ (X1 ◇ X0)))) = X1 := superpose step19 step62
  have step92 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := superpose step9 step66
  have step93 (X0 : G) :  (X0 ◇ X0) = ((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ X0) := superpose step11 step66
  have step250 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = (((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) := superpose step92 step9
  have step257 (X0 : G) :  ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))) = (((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ X0))) := superpose step92 step19
  have step261 (X0 : G) :  ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ X0))) := superpose step20 step257
  have step265 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = (((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ X0))) := superpose step92 step250
  have step268 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ X0))) := superpose step66 step261
  have step270 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = (((X0 ◇ X0) ◇ X0) ◇ X0) := superpose step265 step268
  have step344 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose step270 step93
  have step362 (X0 : G) :  ((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ X0) ◇ X0)) = (X0 ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0)))) := superpose step270 step20
  have step365 (X0 : G) :  ((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ X0) ◇ X0)) = (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0)))) := superpose step66 step362
  have step380 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose step66 step344
  have step382 (X0 : G) :  (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose step21 step365
  have step391 (X0 : G) :  (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose step380 step382
  have step421 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))) = ((X0 ◇ (X0 ◇ X0)) ◇ ((((X0 ◇ X0) ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))) ◇ X0)) := superpose step21 step16
  have step458 (X0 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) = X0 := superpose step76 step421
  have step476 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose step391 step458
  have step513 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) := superpose step476 step19
  have step528 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = X0 := superpose step12 step513
  have step813 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ X0) = ((X0 ◇ X0) ◇ (((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ X0) ◇ X0)) := superpose step528 step13
  have step835 (X0 : G) :  ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) = (((X0 ◇ X0) ◇ X0) ◇ X0) := superpose step93 step813
  have step849 (X0 : G) :  ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) = (X0 ◇ (X0 ◇ X0)) := superpose step270 step835
  have step858 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) := superpose step391 step849
  have step863 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step9 step858
  have step981 : sK0 ≠ sK0 := superpose step863 step10
  subsumption step981 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation1691_implies_Equation3 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation1691 G) : Equation3 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have step9 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ X0)) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ (sK0 ◇ sK0) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step13 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X0) = (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) := superpose step9 step9
  have step19 (X0 X1 : G) :  (((X1 ◇ X0) ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) = X0 := superpose step9 step12
  have step37 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = X0 := superpose step13 step11
  have step44 (X0 : G) :  (X0 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose step37 step19
  have step51 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = X0 := superpose step37 step9
  have step54 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step51 step44
  have step77 : sK0 ≠ sK0 := superpose step54 step10
  subsumption step77 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation1731_implies_Equation16 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation1731 G) : Equation16 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  ((X1 ◇ X1) ◇ ((X1 ◇ X1) ◇ X0)) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ (sK1 ◇ (sK1 ◇ sK0)) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step17 (X0 X1 : G) :  ((X1 ◇ X1) ◇ X0) = (X0 ◇ (((X1 ◇ X1) ◇ X0) ◇ (X1 ◇ X1))) := superpose step11 step9
  have step19 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step20 (X0 X1 : G) :  (((X1 ◇ X1) ◇ X0) ◇ (X0 ◇ (X1 ◇ X1))) = X0 := superpose step9 step12
  have step22 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose step12 step9
  have step129 (X0 X1 : G) :  ((((X1 ◇ X1) ◇ X0) ◇ X0) ◇ ((X1 ◇ X1) ◇ X0)) = ((X0 ◇ (X1 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X1))) ◇ X0)) := superpose step20 step19
  have step135 (X0 X1 : G) :  ((X1 ◇ ((X0 ◇ X0) ◇ X1)) ◇ X1) = ((((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X0)) ◇ ((((X0 ◇ X0) ◇ X1) ◇ (((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X0))) ◇ ((X0 ◇ X0) ◇ X1))) := superpose step17 step19
  have step137 (X0 : G) :  (((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) = (X0 ◇ ((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0))) := superpose step22 step19
  have step144 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ ((X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) ◇ (X1 ◇ (X1 ◇ X0))))) = X1 := superpose step19 step11
  have step148 (X0 X1 : G) :  (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) = (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ ((X1 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) ◇ X1)) := superpose step19 step12
  have step149 (X0 X1 : G) :  (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) = (X1 ◇ ((((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) ◇ (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X1))) := superpose step19 step11
  have step155 (X0 : G) :  (((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) = (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose step19 step137
  have step156 (X0 X1 : G) :  (X0 ◇ X0) = ((X1 ◇ ((X0 ◇ X0) ◇ X1)) ◇ X1) := superpose step12 step135
  have step159 (X0 X1 : G) :  (X1 ◇ X1) = ((((X1 ◇ X1) ◇ X0) ◇ X0) ◇ ((X1 ◇ X1) ◇ X0)) := superpose step12 step129
  have step162 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = (((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) := superpose step9 step155
  have step270 (X0 X1 : G) :  (((X0 ◇ X0) ◇ X1) ◇ (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) ◇ (X0 ◇ X0))) = (((((X0 ◇ X0) ◇ X1) ◇ X1) ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X0) ◇ X1) ◇ X1)) := superpose step159 step19
  have step271 (X0 X1 : G) :  ((X0 ◇ X0) ◇ X1) = ((X0 ◇ X0) ◇ (((((X0 ◇ X0) ◇ X1) ◇ X1) ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X0) ◇ X1) ◇ X1))) := superpose step159 step12
  have step273 (X0 X1 : G) :  (((((X0 ◇ X0) ◇ X1) ◇ X1) ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X0) ◇ X1) ◇ X1)) = X1 := superpose step12 step270
  have step670 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ (X0 ◇ X0)) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)))) := superpose step162 step12
  have step672 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)))) := superpose step162 step670
  have step1181 (X0 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) = ((((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ X0)))) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))))) := superpose step162 step144
  have step1217 (X0 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) = ((X0 ◇ (X0 ◇ X0)) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ X0)))) ◇ (X0 ◇ (X0 ◇ X0))))) := superpose step162 step1181
  have step1251 (X0 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) = ((X0 ◇ (X0 ◇ X0)) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))))) := superpose step156 step1217
  have step1578 (X0 : G) :  (((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ X0))) = (((((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0))) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)))) ◇ (X0 ◇ (X0 ◇ X0)))) := superpose step162 step148
  have step1622 (X0 : G) :  (((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ X0))) = (((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0))) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)))) ◇ (X0 ◇ (X0 ◇ X0)))) := superpose step162 step1578
  have step1650 (X0 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) = (((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ X0))) := superpose step12 step1622
  have step2256 (X0 X1 : G) :  ((X1 ◇ (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1))) ◇ X1) = (((((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) ◇ (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X1)) ◇ (((((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) ◇ ((((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) ◇ (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X1))) ◇ (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)))) := superpose step149 step19
  have step2288 (X0 X1 : G) :  ((X1 ◇ (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1))) ◇ X1) = (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X1) := superpose step12 step2256
  have step3368 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = (((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0))) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)))) ◇ (X0 ◇ (X0 ◇ X0)))) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))))) := superpose step672 step144
  have step3379 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = (((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))))) := superpose step12 step3368
  have step3395 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = (((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0))) := superpose step1251 step3379
  have step3545 (X0 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) = (((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (((((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))))) := superpose step1650 step271
  have step3546 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = (((((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))) := superpose step1650 step273
  have step3575 (X0 : G) :  (((X0 ◇ (X0 ◇ X0)) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)))) ◇ (X0 ◇ (X0 ◇ X0))) = (((((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))) ◇ (X0 ◇ (X0 ◇ X0))) := superpose step1650 step2288
  have step3576 (X0 : G) :  (((X0 ◇ (X0 ◇ X0)) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)))) ◇ (X0 ◇ (X0 ◇ X0))) = (((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))) ◇ (X0 ◇ (X0 ◇ X0))) := superpose step3395 step3575
  have step3597 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = (((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))) ◇ (X0 ◇ (X0 ◇ X0))) := superpose step162 step3546
  have step3598 (X0 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) = (((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))) ◇ (X0 ◇ (X0 ◇ X0)))) := superpose step162 step3545
  have step3610 (X0 : G) :  (((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ X0))) = (((X0 ◇ (X0 ◇ X0)) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)))) ◇ (X0 ◇ (X0 ◇ X0))) := superpose step22 step3576
  have step3624 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = (((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ X0))) := superpose step22 step3597
  have step3625 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) := superpose step12 step3598
  have step3631 (X0 : G) :  (((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ X0))) = (((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)))) ◇ (X0 ◇ (X0 ◇ X0))) := superpose step162 step3610
  have step3641 (X0 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) = (((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ X0))) := superpose step672 step3631
  have step3645 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) := superpose step3624 step3641
  have step3735 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ X0)))) := superpose step3625 step12
  have step3743 (X0 : G) :  (((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) = (((X0 ◇ X0) ◇ X0) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ X0) ◇ X0)))) := superpose step3625 step149
  have step3746 (X0 : G) :  ((((X0 ◇ X0) ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))) ◇ ((X0 ◇ X0) ◇ X0)) = ((((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ X0) ◇ X0)) := superpose step3625 step2288
  have step3747 (X0 : G) :  ((((X0 ◇ X0) ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))) ◇ ((X0 ◇ X0) ◇ X0)) = (((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) := superpose step1650 step3746
  have step3750 (X0 : G) :  (((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) = (((X0 ◇ X0) ◇ X0) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)))) := superpose step1650 step3743
  have step3758 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0))) := superpose step1650 step3735
  have step3769 (X0 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) = ((((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))) ◇ ((X0 ◇ X0) ◇ X0)) := superpose step3625 step3747
  have step3771 (X0 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) = (((X0 ◇ X0) ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)))) := superpose step3625 step3750
  have step3778 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) := superpose step3625 step3758
  have step3783 (X0 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) = ((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ X0) ◇ X0)) := superpose step3645 step3769
  have step3784 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) = ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) := superpose step3395 step3771
  have step3789 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose step3645 step3778
  have step3792 (X0 : G) :  (X0 ◇ ((X0 ◇ X0) ◇ X0)) = ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) := superpose step20 step3783
  have step3793 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) := superpose step3645 step3784
  have step3796 (X0 : G) :  (X0 ◇ ((X0 ◇ X0) ◇ X0)) = (X0 ◇ (X0 ◇ X0)) := superpose step3625 step3792
  have step3797 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = X0 := superpose step20 step3793
  have step3799 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ (X0 ◇ X0))) := superpose step3789 step3796
  have step3801 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step3797 step3799
  have step4271 (X0 X1 : G) :  (X0 ◇ (X0 ◇ X1)) = X1 := superpose step3801 step9
  have step5365 : sK0 ≠ sK0 := superpose step4271 step10
  subsumption step5365 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation1840_implies_Equation3 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation1840 G) : Equation3 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have step9 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X0)) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ (sK0 ◇ sK0) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step15 (X0 X1 : G) :  (X1 ◇ X0) = ((X0 ◇ (X0 ◇ X1)) ◇ ((X1 ◇ X0) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1))))) := superpose step9 step11
  have step19 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X1)) = X1 := superpose step11 step9
  have step20 (X0 X1 : G) :  (X1 ◇ X0) = (X0 ◇ (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X1)))) := superpose step9 step12
  have step23 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = ((X1 ◇ X0) ◇ (((X1 ◇ (X1 ◇ X0)) ◇ X1) ◇ (X0 ◇ (X1 ◇ X0)))) := superpose step12 step11
  have step32 (X0 X1 : G) :  (X1 ◇ X0) = (X0 ◇ ((((X1 ◇ (X1 ◇ X0)) ◇ X1) ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X1 ◇ X0))) := superpose step12 step19
  have step151 (X0 X1 : G) :  (((X1 ◇ (X1 ◇ X0)) ◇ X1) ◇ (X1 ◇ (X1 ◇ X0))) = ((X0 ◇ X1) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X1)) := superpose step20 step12
  have step3322 (X0 : G) :  (X0 ◇ X0) = (X0 ◇ (((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ (X0 ◇ X0))) := superpose step151 step32
  have step3323 (X0 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) := superpose step151 step23
  have step3401 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose step12 step3323
  have step3402 (X0 : G) :  (X0 ◇ X0) = (X0 ◇ (X0 ◇ (X0 ◇ X0))) := superpose step12 step3322
  have step3685 (X0 : G) :  ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) = X0 := superpose step3402 step9
  have step3686 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) := superpose step3402 step12
  have step3713 (X0 : G) :  (X0 ◇ X0) = (((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))))) := superpose step3402 step15
  have step3771 (X0 : G) :  (X0 ◇ X0) = (((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0))))) := superpose step3401 step3713
  have step3814 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)))) := superpose step3686 step3771
  have step3844 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) := superpose step9 step3814
  have step3867 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step3685 step3844
  have step4102 : sK0 ≠ sK0 := superpose step3867 step10
  subsumption step4102 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation1848_implies_Equation1286 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation1848 G) : Equation1286 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X1)) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ (sK1 ◇ (((sK0 ◇ sK1) ◇ sK0) ◇ sK1)) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step13 (X0 X1 : G) :  (X0 ◇ X1) = (((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ X0)))) := superpose step9 step9
  have step18 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ X0) ◇ X1)) = (((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X0) ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X1)) := superpose step11 step9
  have step20 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step110 (X0 X1 : G) :  ((((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ X0)) = (((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ X0))) ◇ (((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ X0)))) ◇ (X0 ◇ X1))) := superpose step13 step20
  have step142 (X0 X1 : G) :  (X0 ◇ (X1 ◇ X0)) = ((((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ X0)) := superpose step12 step110
  have step834 (X0 X1 : G) :  ((((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X0) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X0)) = (((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X1) ◇ (((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X1)) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1)))) := superpose step18 step20
  have step855 (X0 X1 : G) :  ((((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X0) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X0)) = X1 := superpose step12 step834
  have step881 (X0 X1 : G) :  (X0 ◇ (((X1 ◇ X0) ◇ X1) ◇ X0)) = X1 := superpose step142 step855
  have step985 : sK0 ≠ sK0 := superpose step881 step10
  subsumption step985 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation1848_implies_Equation3 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation1848 G) : Equation3 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have step9 (X0 X1 : G) :  ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X1)) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ (sK0 ◇ sK0) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step13 (X0 X1 : G) :  (X0 ◇ X1) = (((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ X0)))) := superpose step9 step9
  have step17 (X0 X1 : G) :  ((X1 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X1)) ◇ X0) = X1 := superpose step11 step9
  have step19 (X0 X1 : G) :  (X0 ◇ X1) = (X0 ◇ (((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X1 ◇ X0)))) := superpose step9 step12
  have step20 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step60 (X0 X1 : G) :  ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ X0))) = ((X0 ◇ X1) ◇ ((((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ X0))) := superpose step13 step12
  have step63 (X0 : G) :  (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) = (X0 ◇ (X0 ◇ (X0 ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0)))) := superpose step17 step19
  have step70 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X0))) = (X1 ◇ (((X1 ◇ X0) ◇ X1) ◇ (X1 ◇ X0))) := superpose step17 step19
  have step84 (X0 : G) :  (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) = (X0 ◇ (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)))) := superpose step70 step63
  have step86 (X0 : G) :  (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) = (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) := superpose step20 step84
  have step88 (X0 : G) :  (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) = X0 := superpose step11 step86
  have step91 (X0 : G) :  (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) = X0 := superpose step88 step9
  have step114 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ X0)) := superpose step88 step20
  have step134 (X0 X1 : G) :  (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) = (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ ((X1 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) ◇ X1)) := superpose step20 step12
  have step140 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) := superpose step134 step114
  have step155 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) ◇ X0)) := superpose step91 step20
  have step156 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose step12 step155
  have step219 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)))) = X0 := superpose step156 step11
  have step233 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose step9 step219
  have step318 (X0 : G) :  ((X0 ◇ X0) ◇ ((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0))) = X0 := superpose step233 step19
  have step322 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0))) := superpose step233 step88
  have step324 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) := superpose step140 step322
  have step327 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose step60 step318
  have step336 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) := superpose step156 step324
  have step341 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step327 step336
  have step399 : sK0 ≠ sK0 := superpose step341 step10
  subsumption step399 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation1850_implies_Equation3 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation1850 G) : Equation3 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have step9 (X0 X1 : G) :  ((X0 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ (sK0 ◇ sK0) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step13 (X0 X1 : G) :  (X1 ◇ X0) = (((X1 ◇ X0) ◇ X0) ◇ X0) := superpose step9 step9
  have step15 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ X0) ◇ X1)) = (X1 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X0 ◇ X1))) := superpose step11 step11
  have step17 (X0 X1 : G) :  (X1 ◇ X0) = (X0 ◇ (((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X1 ◇ X0)))) := superpose step9 step12
  have step18 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step19 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose step11 step12
  have step20 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = ((X1 ◇ X0) ◇ (((X1 ◇ (X1 ◇ X0)) ◇ X1) ◇ (X0 ◇ (X1 ◇ X0)))) := superpose step12 step11
  have step32 (X0 : G) :  (X0 ◇ X0) = (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) := superpose step19 step9
  have step56 (X0 X1 : G) :  (((X1 ◇ (X0 ◇ X1)) ◇ X1) ◇ (X1 ◇ (X0 ◇ X1))) = ((X0 ◇ X1) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X1)) := superpose step17 step12
  have step63 (X0 X1 : G) :  (X1 ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X1))) = (((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X0 ◇ X1)) := superpose step13 step18
  have step572 (X0 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) := superpose step56 step20
  have step600 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose step12 step572
  have step619 (X0 : G) :  ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) = X0 := superpose step600 step12
  have step623 (X0 : G) :  ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) = (X0 ◇ (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0))) := superpose step600 step15
  have step648 (X0 : G) :  ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) = (X0 ◇ (X0 ◇ X0)) := superpose step32 step623
  have step652 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = X0 := superpose step619 step648
  have step658 (X0 : G) :  ((((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0))) = (((X0 ◇ X0) ◇ X0) ◇ (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0))) := superpose step32 step63
  have step729 (X0 : G) :  ((((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0))) = X0 := superpose step12 step658
  have step733 (X0 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ X0) = X0 := superpose step619 step729
  have step736 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step652 step733
  have step737 : sK0 ≠ sK0 := superpose step736 step10
  subsumption step737 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation1850_implies_Equation4131 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation1850 G) : Equation4131 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  ((X0 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)) = X0 := mod_symm (h ..)
  have step10 : (sK0 ◇ sK1) ≠ (((sK0 ◇ sK1) ◇ sK1) ◇ sK1) := mod_symm nh
  have step13 (X0 X1 : G) :  (X1 ◇ X0) = (((X1 ◇ X0) ◇ X0) ◇ X0) := superpose step9 step9
  have step29 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose step13 step10
  subsumption step29 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation1897_implies_Equation3 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation1897 G) : Equation3 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have step9 (X0 X1 : G) :  ((X1 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X0)) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ (sK0 ◇ sK0) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step13 (X0 X1 : G) :  (X1 ◇ (X0 ◇ X1)) = (((X1 ◇ X0) ◇ X0) ◇ ((X1 ◇ X0) ◇ (X1 ◇ (X0 ◇ X1)))) := superpose step9 step9
  have step16 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ X0) ◇ X1)) = (X1 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X0 ◇ X1))) := superpose step11 step11
  have step18 (X0 X1 : G) :  (((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X0) ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X1)) = X1 := superpose step11 step9
  have step19 (X0 X1 : G) :  (X1 ◇ X0) = (X0 ◇ (((X1 ◇ (X0 ◇ X1)) ◇ X0) ◇ (X1 ◇ (X0 ◇ X1)))) := superpose step9 step12
  have step22 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = ((X1 ◇ X0) ◇ (((X1 ◇ (X1 ◇ X0)) ◇ X1) ◇ (X0 ◇ (X1 ◇ X0)))) := superpose step12 step11
  have step24 (X0 X1 : G) :  (X1 ◇ X0) = ((((X1 ◇ (X1 ◇ X0)) ◇ X1) ◇ X0) ◇ (((X1 ◇ (X1 ◇ X0)) ◇ X1) ◇ (X1 ◇ X0))) := superpose step12 step9
  have step37 (X0 X1 : G) :  (((X0 ◇ (X1 ◇ X0)) ◇ X1) ◇ (X0 ◇ (X1 ◇ X0))) = ((X0 ◇ X1) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X1)) := superpose step19 step12
  have step62 (X0 : G) :  (X0 ◇ ((X0 ◇ X0) ◇ X0)) = (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) := superpose step9 step13
  have step439 (X0 : G) :  ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ X0)) = ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) := superpose step62 step12
  have step459 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) := superpose step12 step439
  have step595 (X0 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) := superpose step37 step22
  have step647 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose step12 step595
  have step658 (X0 : G) :  ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) = X0 := superpose step647 step12
  have step664 (X0 : G) :  ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) = (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) := superpose step647 step37
  have step778 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0))) := superpose step658 step24
  have step780 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) := superpose step658 step22
  have step781 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose step658 step12
  have step808 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) := superpose step459 step780
  have step809 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0))) := superpose step647 step778
  have step920 (X0 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) = (((X0 ◇ X0) ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)))) := superpose step781 step16
  have step922 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X0 ◇ X0) ◇ X0))) := superpose step781 step18
  have step937 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0))) := superpose step459 step922
  have step939 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)))) := superpose step459 step920
  have step952 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ X0))) := superpose step808 step937
  have step954 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) := superpose step809 step939
  have step958 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) := superpose step664 step952
  have step960 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose step808 step954
  have step963 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = (X0 ◇ (X0 ◇ (X0 ◇ X0))) := superpose step658 step958
  have step967 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ (X0 ◇ X0))) := superpose step960 step963
  have step1121 (X0 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose step960 step781
  have step1127 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ X0))) := superpose step960 step9
  have step1172 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) := superpose step967 step1127
  have step1208 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step1121 step1172
  have step1451 : sK0 ≠ sK0 := superpose step1208 step10
  subsumption step1451 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation1922_implies_Equation3 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation1922 G) : Equation3 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have step9 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X1)) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ (sK0 ◇ sK0) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step17 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) := superpose step11 step9
  have step21 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step52 (X0 : G) :  ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) = ((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ ((((X0 ◇ X0) ◇ X0) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0))) := superpose step17 step21
  have step71 (X0 : G) :  ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) = X0 := superpose step12 step52
  have step79 (X0 : G) :  (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) = X0 := superpose step71 step9
  have step80 (X0 : G) :  (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) ◇ X0) = X0 := superpose step11 step79
  have step86 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step71 step80
  have step160 : sK0 ≠ sK0 := superpose step86 step10
  subsumption step160 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation2053_implies_Equation3 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation2053 G) : Equation3 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have step9 (X0 X1 : G) :  (((X0 ◇ X1) ◇ X0) ◇ (X1 ◇ X0)) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ (sK0 ◇ sK0) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step14 (X0 : G) :  (X0 ◇ X0) = (X0 ◇ (X0 ◇ (X0 ◇ X0))) := superpose step9 step9
  have step18 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose step9 step11
  have step34 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) := superpose step14 step12
  have step40 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = X0 := superpose step12 step34
  have step41 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose step18 step40
  have step77 (X0 : G) :  (X0 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose step41 step11
  have step91 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step40 step77
  have step121 : sK0 ≠ sK0 := superpose step91 step10
  subsumption step121 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation2063_implies_Equation3 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation2063 G) : Equation3 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have step9 (X0 X1 : G) :  (((X0 ◇ X1) ◇ X1) ◇ (X1 ◇ X0)) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ (sK0 ◇ sK0) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step17 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose step9 step11
  have step20 (X0 X1 : G) :  (X1 ◇ X0) = (X0 ◇ ((((X0 ◇ X1) ◇ X1) ◇ X0) ◇ ((X0 ◇ X1) ◇ X1))) := superpose step9 step12
  have step21 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step29 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose step17 step9
  have step41 (X0 : G) :  ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))) = X0 := superpose step29 step12
  have step45 (X0 : G) :  ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) = X0 := superpose step21 step41
  have step65 (X0 : G) :  (X0 ◇ (((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))) = X0 := superpose step45 step12
  have step69 (X0 : G) :  (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))) = X0 := superpose step45 step65
  have step104 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))) ◇ X0)) := superpose step69 step21
  have step114 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = (X0 ◇ (X0 ◇ (X0 ◇ X0))) := superpose step12 step104
  have step163 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ X0) = X0 := superpose step114 step45
  have step247 (X0 : G) :  (X0 ◇ X0) = (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) := superpose step163 step20
  have step266 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step11 step247
  have step383 : sK0 ≠ sK0 := superpose step266 step10
  subsumption step383 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation2088_implies_Equation3 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation2088 G) : Equation3 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have step9 (X0 X1 : G) :  (((X1 ◇ X0) ◇ X0) ◇ (X0 ◇ X1)) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ (sK0 ◇ sK0) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step17 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose step9 step11
  have step18 (X0 X1 : G) :  ((((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X1) ◇ X1) ◇ X0) = X1 := superpose step11 step9
  have step20 (X0 X1 : G) :  (X0 ◇ X1) = (X0 ◇ ((((X1 ◇ X0) ◇ X0) ◇ X0) ◇ ((X1 ◇ X0) ◇ X0))) := superpose step9 step12
  have step21 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step29 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose step17 step9
  have step50 (X0 : G) :  ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))) = X0 := superpose step29 step12
  have step54 (X0 : G) :  ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) = X0 := superpose step21 step50
  have step69 (X0 : G) :  (X0 ◇ (((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))) = X0 := superpose step54 step12
  have step73 (X0 : G) :  (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))) = X0 := superpose step54 step69
  have step123 (X0 : G) :  (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) = (X0 ◇ (X0 ◇ (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) ◇ X0))) := superpose step18 step20
  have step132 (X0 X1 : G) :  (X1 ◇ (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1))) = (X1 ◇ (((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X0) ◇ X0)) := superpose step18 step20
  have step156 (X0 : G) :  (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) = (X0 ◇ (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)))) := superpose step132 step123
  have step162 (X0 : G) :  (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) = (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) := superpose step21 step156
  have step166 (X0 : G) :  (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) = (X0 ◇ (X0 ◇ X0)) := superpose step29 step162
  have step168 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = X0 := superpose step11 step166
  have step172 (X0 : G) :  (X0 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose step168 step73
  have step186 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step168 step172
  have step244 : sK0 ≠ sK0 := superpose step186 step10
  subsumption step244 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation209_implies_Equation3 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation209 G) : Equation3 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have step10 (X0 X1 : G) :  ((X0 ◇ (X1 ◇ X0)) ◇ X1) = X0 := mod_symm (h ..)
  have step11 : sK0 ≠ (sK0 ◇ sK0) := mod_symm nh
  have step12 (X Y : G) : ((X ◇ Y) ◇ (Y ◇ (X ◇ Y))) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (s ◇ (Y ◇ s))) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (s ◇ Y)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (s ◇ Y)) (fun s => (s ◇ (Y ◇ s))) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step13 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step14 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step22 (X0 : G) :  (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose step10 step13
  have step25 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = X0 := superpose step22 step13
  have step36 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = X0 := superpose step10 step14
  have step46 (X0 : G) :  (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose step36 step12
  have step48 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step25 step46
  have step75 : sK0 ≠ sK0 := superpose step48 step11
  subsumption step75 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation2098_implies_Equation3 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation2098 G) : Equation3 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have step9 (X0 X1 : G) :  (((X1 ◇ X0) ◇ X1) ◇ (X0 ◇ X1)) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ (sK0 ◇ sK0) := mod_symm nh
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step14 (X0 : G) :  (X0 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose step9 step9
  have step17 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) := superpose step14 step9
  have step18 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = X0 := superpose step12 step17
  have step26 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step18 step14
  have step47 : sK0 ≠ sK0 := superpose step26 step10
  subsumption step47 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation2_implies_Equation1083 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation2 G) : Equation1083 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  X0 = X1 := mod_symm (h ..)
  have step10 : sK0 ≠ (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK1)) := mod_symm nh
  have step24 (X0 : G) :  sK0 ≠ (X0 ◇ ((sK0 ◇ (X0 ◇ sK0)) ◇ X0)) := superpose step9 step10
  subsumption step24 step9


@[equational_result]
theorem Finite.Equation677_and_Equation2_implies_Equation1232 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation2 G) : Equation1232 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  X0 = X1 := mod_symm (h ..)
  have step10 : sK0 ≠ (sK0 ◇ (((sK0 ◇ sK1) ◇ sK1) ◇ sK1)) := mod_symm nh
  have step24 (X0 : G) :  sK0 ≠ (sK0 ◇ (((sK0 ◇ X0) ◇ X0) ◇ X0)) := superpose step9 step10
  subsumption step24 step9


@[equational_result]
theorem Finite.Equation677_and_Equation2_implies_Equation1238 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation2 G) : Equation1238 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  X0 = X1 := mod_symm (h ..)
  have step10 : sK0 ≠ (sK0 ◇ (((sK1 ◇ sK0) ◇ sK0) ◇ sK0)) := mod_symm nh
  have step24 (X0 : G) :  (X0 ◇ (((sK1 ◇ X0) ◇ X0) ◇ X0)) ≠ X0 := superpose step9 step10
  subsumption step24 step9


@[equational_result]
theorem Finite.Equation677_and_Equation2_implies_Equation1249 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation2 G) : Equation1249 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  X0 = X1 := mod_symm (h ..)
  have step10 : sK0 ≠ (sK0 ◇ (((sK1 ◇ sK1) ◇ sK0) ◇ sK1)) := mod_symm nh
  have step24 (X0 : G) :  sK0 ≠ (sK0 ◇ (((X0 ◇ X0) ◇ sK0) ◇ X0)) := superpose step9 step10
  subsumption step24 step9


@[equational_result]
theorem Finite.Equation677_and_Equation2_implies_Equation1251 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation2 G) : Equation1251 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  X0 = X1 := mod_symm (h ..)
  have step10 : sK0 ≠ (sK0 ◇ (((sK1 ◇ sK1) ◇ sK1) ◇ sK0)) := mod_symm nh
  have step24 (X0 : G) :  (X0 ◇ (((sK1 ◇ sK1) ◇ sK1) ◇ X0)) ≠ X0 := superpose step9 step10
  subsumption step24 step9


@[equational_result]
theorem Finite.Equation677_and_Equation2_implies_Equation1285 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation2 G) : Equation1285 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  X0 = X1 := mod_symm (h ..)
  have step10 : sK0 ≠ (sK1 ◇ (((sK0 ◇ sK1) ◇ sK0) ◇ sK0)) := mod_symm nh
  have step24 (X0 : G) :  (sK1 ◇ (((X0 ◇ sK1) ◇ X0) ◇ X0)) ≠ X0 := superpose step9 step10
  subsumption step24 step9


@[equational_result]
theorem Finite.Equation677_and_Equation2_implies_Equation2053 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation2 G) : Equation2053 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  X0 = X1 := mod_symm (h ..)
  have step10 : sK0 ≠ (((sK0 ◇ sK1) ◇ sK0) ◇ (sK1 ◇ sK0)) := mod_symm nh
  have step24 (X0 : G) :  (((X0 ◇ sK1) ◇ X0) ◇ (sK1 ◇ X0)) ≠ X0 := superpose step9 step10
  subsumption step24 step9


@[equational_result]
theorem Finite.Equation677_and_Equation2241_implies_Equation3 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation2241 G) : Equation3 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have step10 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X1) = X0 := mod_symm (h ..)
  have step11 : sK0 ≠ (sK0 ◇ sK0) := mod_symm nh
  have step12 (X Y : G) : ((X ◇ Y) ◇ ((X ◇ Y) ◇ ((X ◇ Y) ◇ Y))) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (s ◇ (s ◇ (s ◇ Y)))) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (s ◇ Y)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (s ◇ Y)) (fun s => (s ◇ (s ◇ (s ◇ Y)))) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step13 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step14 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step19 (X0 : G) :  ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) = X0 := superpose step13 step10
  have step22 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step14 step14
  have step39 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = X0 := superpose step19 step12
  have step46 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = X0 := superpose step39 step13
  have step49 (X0 : G) :  (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0))) = X0 := superpose step39 step14
  have step52 (X0 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ X0) = X0 := superpose step22 step49
  have step53 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step46 step52
  have step69 : sK0 ≠ sK0 := superpose step53 step11
  subsumption step69 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation2244_implies_Equation3 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation2244 G) : Equation3 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have step10 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X1) = X0 := mod_symm (h ..)
  have step11 : sK0 ≠ (sK0 ◇ sK0) := mod_symm nh
  have step13 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step14 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step19 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = X0 := superpose step13 step10
  have step23 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step14 step14
  have step28 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = X0 := superpose step19 step10
  have step45 (X0 : G) :  (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0))) = X0 := superpose step28 step14
  have step50 (X0 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ X0) = X0 := superpose step23 step45
  have step51 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step19 step50
  have step82 : sK0 ≠ sK0 := superpose step51 step11
  subsumption step82 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation2257_implies_Equation3 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation2257 G) : Equation3 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have step10 (X0 X1 : G) :  ((X0 ◇ (X1 ◇ (X0 ◇ X1))) ◇ X1) = X0 := mod_symm (h ..)
  have step11 : sK0 ≠ (sK0 ◇ sK0) := mod_symm nh
  have step12 (X Y : G) : ((X ◇ Y) ◇ (Y ◇ ((X ◇ Y) ◇ Y))) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (s ◇ (Y ◇ (s ◇ Y)))) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (s ◇ Y)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (s ◇ Y)) (fun s => (s ◇ (Y ◇ (s ◇ Y)))) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step14 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step28 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose step10 step14
  have step35 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) := superpose step28 step12
  have step38 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = X0 := superpose step12 step35
  have step40 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = X0 := superpose step38 step10
  have step43 (X0 : G) :  (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0)))) = X0 := superpose step38 step12
  have step46 (X0 : G) :  (X0 ◇ ((X0 ◇ X0) ◇ X0)) = X0 := superpose step38 step43
  have step47 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step40 step46
  have step61 : sK0 ≠ sK0 := superpose step47 step11
  subsumption step61 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation2264_implies_Equation3 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation2264 G) : Equation3 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have step11 : sK0 ≠ (sK0 ◇ sK0) := mod_symm nh
  have step12 (X Y : G) : ((X ◇ Y) ◇ (Y ◇ (Y ◇ (X ◇ Y)))) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (s ◇ (Y ◇ (Y ◇ s)))) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (s ◇ Y)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (s ◇ Y)) (fun s => (s ◇ (Y ◇ (Y ◇ s)))) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step13 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step14 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step23 (X0 : G) :  (X0 ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ X0) := superpose step13 step12
  have step26 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) := superpose step23 step12
  have step29 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = X0 := superpose step12 step26
  have step32 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step14 step14
  have step41 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = X0 := superpose step29 step13
  have step42 (X0 : G) :  (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0))) = X0 := superpose step29 step14
  have step47 (X0 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ X0) = X0 := superpose step32 step42
  have step48 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step41 step47
  have step65 : sK0 ≠ sK0 := superpose step48 step11
  subsumption step65 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation2_implies_Equation26 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation2 G) : Equation26 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  X0 = X1 := mod_symm (h ..)
  have step10 : sK0 ≠ ((sK0 ◇ sK1) ◇ sK1) := mod_symm nh
  have step20 (X0 : G) :  sK0 ≠ ((sK0 ◇ X0) ◇ X0) := superpose step9 step10
  subsumption step20 step9


@[equational_result]
theorem Finite.Equation677_and_Equation2_implies_Equation2863 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation2 G) : Equation2863 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  X0 = X1 := mod_symm (h ..)
  have step10 : sK0 ≠ (((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0) ◇ sK1) := mod_symm nh
  have step24 (X0 : G) :  sK0 ≠ (((sK0 ◇ (X0 ◇ sK0)) ◇ sK0) ◇ X0) := superpose step9 step10
  subsumption step24 step9


@[equational_result]
theorem Finite.Equation677_and_Equation2294_implies_Equation3 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation2294 G) : Equation3 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have step11 (X0 X1 : G) :  ((X1 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X1) = X0 := mod_symm (h ..)
  have step12 : sK0 ≠ (sK0 ◇ sK0) := mod_symm nh
  have step13 (X Y : G) : (((Y ◇ X) ◇ Y) ◇ (((Y ◇ X) ◇ Y) ◇ Y)) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (s ◇ (s ◇ Y))) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => ((Y ◇ s) ◇ Y)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => ((Y ◇ s) ◇ Y)) (fun s => (s ◇ (s ◇ Y))) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step14 (X Y : G) : (Y ◇ ((X ◇ Y) ◇ ((X ◇ Y) ◇ Y))) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (Y ◇ (s ◇ (s ◇ Y)))) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (s ◇ Y)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (s ◇ Y)) (fun s => (Y ◇ (s ◇ (s ◇ Y)))) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step15 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step16 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step20 (X0 X1 : G) :  (X0 ◇ (X0 ◇ X1)) = (X1 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) := superpose step11 step15
  have step21 (X0 : G) :  ((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) = X0 := superpose step15 step11
  have step29 (X0 X1 : G) :  ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) = (X0 ◇ ((X1 ◇ X0) ◇ X1)) := superpose step14 step16
  have step31 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose step11 step16
  have step48 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose step31 step16
  have step49 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) := superpose step31 step13
  have step53 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = (X0 ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0))) := superpose step31 step14
  have step56 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = X0 := superpose step14 step53
  have step59 (X0 : G) :  (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose step29 step49
  have step70 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = (X0 ◇ (X0 ◇ (X0 ◇ X0))) := superpose step11 step20
  have step78 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose step56 step70
  have step102 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ X0) = ((((X0 ◇ X0) ◇ X0) ◇ ((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) := superpose step21 step11
  have step103 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = (((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose step78 step102
  have step109 (X0 : G) :  (X0 ◇ X0) = (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose step78 step103
  have step115 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose step29 step109
  have step121 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose step59 step115
  have step125 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step48 step121
  have step128 : sK0 ≠ sK0 := superpose step125 step12
  subsumption step128 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation2301_implies_Equation3 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation2301 G) : Equation3 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have step11 (X0 X1 : G) :  ((X1 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X1) = X0 := mod_symm (h ..)
  have step12 : sK0 ≠ (sK0 ◇ sK0) := mod_symm nh
  have step13 (X Y : G) : (((Y ◇ X) ◇ Y) ◇ (Y ◇ ((Y ◇ X) ◇ Y))) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (s ◇ (Y ◇ s))) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => ((Y ◇ s) ◇ Y)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => ((Y ◇ s) ◇ Y)) (fun s => (s ◇ (Y ◇ s))) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step14 (X Y : G) : (Y ◇ ((X ◇ Y) ◇ (Y ◇ (X ◇ Y)))) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (Y ◇ (s ◇ (Y ◇ s)))) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (s ◇ Y)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (s ◇ Y)) (fun s => (Y ◇ (s ◇ (Y ◇ s)))) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step15 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step16 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step20 (X0 X1 : G) :  (X0 ◇ (X1 ◇ X0)) = (X1 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0)) := superpose step11 step15
  have step30 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose step11 step16
  have step46 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose step30 step16
  have step51 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0)))) := superpose step30 step14
  have step55 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = X0 := superpose step14 step51
  have step69 (X0 : G) :  (X0 ◇ X0) = (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) := superpose step20 step13
  have step79 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose step55 step69
  have step87 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = X0 := superpose step55 step11
  have step145 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) := superpose step87 step20
  have step148 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose step79 step145
  have step153 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step46 step148
  have step186 : sK0 ≠ sK0 := superpose step153 step12
  subsumption step186 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation2_implies_Equation3925 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation2 G) : Equation3925 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  X0 = X1 := mod_symm (h ..)
  have step10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK1) := mod_symm nh
  have step22 (X0 : G) :  (sK0 ◇ X0) ≠ ((sK0 ◇ (X0 ◇ sK0)) ◇ X0) := superpose step9 step10
  subsumption step22 step9


@[equational_result]
theorem Finite.Equation677_and_Equation2_implies_Equation40 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation2 G) : Equation40 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  X0 = X1 := mod_symm (h ..)
  have step10 : (sK0 ◇ sK0) ≠ (sK1 ◇ sK1) := mod_symm nh
  have step16 (X0 : G) :  (sK0 ◇ sK0) ≠ X0 := superpose step9 step10
  subsumption step16 step9


@[equational_result]
theorem Finite.Equation677_and_Equation2_implies_Equation4155 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation2 G) : Equation4155 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  X0 = X1 := mod_symm (h ..)
  have step10 : (sK0 ◇ sK1) ≠ (((sK1 ◇ sK0) ◇ sK0) ◇ sK1) := mod_symm nh
  have step22 (X0 : G) :  (sK0 ◇ X0) ≠ (((X0 ◇ sK0) ◇ sK0) ◇ X0) := superpose step9 step10
  subsumption step22 step9


@[equational_result]
theorem Finite.Equation677_and_Equation2_implies_Equation4158 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation2 G) : Equation4158 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  X0 = X1 := mod_symm (h ..)
  have step10 : (sK0 ◇ sK1) ≠ (((sK1 ◇ sK0) ◇ sK1) ◇ sK1) := mod_symm nh
  have step22 (X0 : G) :  (sK0 ◇ X0) ≠ (((X0 ◇ sK0) ◇ X0) ◇ X0) := superpose step9 step10
  subsumption step22 step9


@[equational_result]
theorem Finite.Equation677_and_Equation2_implies_Equation4399 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation2 G) : Equation4399 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  X0 = X1 := mod_symm (h ..)
  have step10 : (sK0 ◇ (sK0 ◇ sK1)) ≠ ((sK0 ◇ sK1) ◇ sK1) := mod_symm nh
  have step20 (X0 : G) :  (sK0 ◇ (sK0 ◇ X0)) ≠ ((sK0 ◇ X0) ◇ X0) := superpose step9 step10
  subsumption step20 step9


@[equational_result]
theorem Finite.Equation677_and_Equation2447_implies_Equation3 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation2447 G) : Equation3 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have step10 (X0 X1 : G) :  ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1) = X0 := mod_symm (h ..)
  have step11 : sK0 ≠ (sK0 ◇ sK0) := mod_symm nh
  have step12 (X Y : G) : ((X ◇ Y) ◇ (((X ◇ Y) ◇ Y) ◇ (X ◇ Y))) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (s ◇ ((s ◇ Y) ◇ s))) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (s ◇ Y)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (s ◇ Y)) (fun s => (s ◇ ((s ◇ Y) ◇ s))) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step13 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step14 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step16 (X0 : G) :  ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) = X0 := superpose step10 step10
  have step19 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) := superpose step10 step13
  have step20 (X0 X1 : G) :  ((X1 ◇ (X0 ◇ X1)) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X1 := superpose step13 step10
  have step22 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step14 step14
  have step26 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose step16 step14
  have step27 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0))) := superpose step16 step14
  have step30 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose step22 step27
  have step40 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) := superpose step26 step13
  have step42 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose step20 step40
  have step44 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ ((((X0 ◇ X0) ◇ X0) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0))) = X0 := superpose step19 step12
  have step51 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ (((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ X0) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)))) = X0 := superpose step22 step44
  have step53 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))))) = X0 := superpose step42 step51
  have step54 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))))) = X0 := superpose step30 step53
  have step55 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose step26 step54
  have step56 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = X0 := superpose step55 step12
  have step59 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) := superpose step55 step12
  have step64 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose step30 step59
  have step66 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step56 step64
  have step120 : sK0 ≠ sK0 := superpose step66 step11
  subsumption step120 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation2450_implies_Equation3 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation2450 G) : Equation3 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have step10 (X0 X1 : G) :  ((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ X1) = X0 := mod_symm (h ..)
  have step11 : sK0 ≠ (sK0 ◇ sK0) := mod_symm nh
  have step12 (X Y : G) : ((X ◇ Y) ◇ (((X ◇ Y) ◇ Y) ◇ Y)) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (s ◇ ((s ◇ Y) ◇ Y))) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (s ◇ Y)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (s ◇ Y)) (fun s => (s ◇ ((s ◇ Y) ◇ Y))) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step13 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step14 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step16 (X0 X1 : G) :  ((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X1 ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X1))))) = X1 := superpose step10 step13
  have step17 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ X0) ◇ X1)) = (X1 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X0 ◇ X1))) := superpose step13 step13
  have step25 (X0 X1 : G) :  (((X0 ◇ X1) ◇ X1) ◇ X1) = (X0 ◇ (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1))) := superpose step12 step14
  have step26 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step14 step14
  have step27 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose step13 step14
  have step82 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose step26 step25
  have step127 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ X0) ◇ X0)) := superpose step82 step12
  have step134 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose step12 step127
  have step152 (X0 : G) :  ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) = X0 := superpose step13 step16
  have step162 (X0 : G) :  ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0)) = X0 := superpose step134 step152
  have step176 (X0 : G) :  ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) = X0 := superpose step134 step10
  have step179 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0)) := superpose step134 step27
  have step187 (X0 : G) :  (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ X0) = ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))) := superpose step134 step25
  have step190 (X0 : G) :  (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ X0) = ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) := superpose step26 step187
  have step193 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = X0 := superpose step162 step179
  have step196 (X0 : G) :  (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ X0) = X0 := superpose step176 step190
  have step197 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = X0 := superpose step193 step196
  have step204 (X0 : G) :  (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) = ((X0 ◇ X0) ◇ ((X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ X0)))) := superpose step134 step17
  have step254 (X0 : G) :  (X0 ◇ (X0 ◇ (X0 ◇ X0))) = ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0)) := superpose step193 step204
  have step261 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = (X0 ◇ (X0 ◇ (X0 ◇ X0))) := superpose step176 step254
  have step267 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose step193 step261
  have step273 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step197 step267
  have step282 : sK0 ≠ sK0 := superpose step273 step11
  subsumption step282 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation2457_implies_Equation3 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation2457 G) : Equation3 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have step10 (X0 X1 : G) :  ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X1) = X0 := mod_symm (h ..)
  have step11 : sK0 ≠ (sK0 ◇ sK0) := mod_symm nh
  have step12 (X Y : G) : ((X ◇ Y) ◇ ((Y ◇ (X ◇ Y)) ◇ (X ◇ Y))) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (s ◇ ((Y ◇ s) ◇ s))) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (s ◇ Y)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (s ◇ Y)) (fun s => (s ◇ ((Y ◇ s) ◇ s))) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step13 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step14 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step22 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose step13 step14
  have step28 (X0 X1 : G) :  (X0 ◇ (((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X0) ◇ X0)) = X1 := superpose step13 step12
  have step70 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = X0 := superpose step10 step28
  have step89 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose step70 step12
  have step92 (X0 : G) :  (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) = X0 := superpose step70 step12
  have step102 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = X0 := superpose step70 step89
  have step107 (X0 : G) :  (X0 ◇ ((X0 ◇ X0) ◇ X0)) = (((X0 ◇ X0) ◇ X0) ◇ (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0))) := superpose step22 step12
  have step118 (X0 : G) :  (X0 ◇ X0) = (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) := superpose step102 step107
  have step124 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step92 step118
  have step136 : sK0 ≠ sK0 := superpose step124 step11
  subsumption step136 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation2_implies_Equation4673 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation2 G) : Equation4673 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have step9 (X0 X1 : G) :  X0 = X1 := mod_symm (h ..)
  have step10 : ((sK0 ◇ sK1) ◇ sK2) ≠ ((sK0 ◇ sK2) ◇ sK1) := mod_symm nh
  have step22 (X0 : G) :  ((sK0 ◇ sK1) ◇ X0) ≠ ((sK0 ◇ X0) ◇ sK1) := superpose step9 step10
  subsumption step22 step9


@[equational_result]
theorem Finite.Equation677_and_Equation2531_implies_Equation3 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation2531 G) : Equation3 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have step11 (X0 X1 : G) :  ((X1 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X1) = X0 := mod_symm (h ..)
  have step12 : sK0 ≠ (sK0 ◇ sK0) := mod_symm nh
  have step13 (X Y : G) : ((Y ◇ ((Y ◇ X) ◇ Y)) ◇ ((Y ◇ X) ◇ Y)) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => ((Y ◇ s) ◇ s)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => ((Y ◇ s) ◇ Y)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => ((Y ◇ s) ◇ Y)) (fun s => ((Y ◇ s) ◇ s)) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step15 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step20 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X0) = (X1 ◇ (((X1 ◇ X0) ◇ X0) ◇ X0)) := superpose step11 step15
  have step44 (X0 X1 : G) :  (X0 ◇ X1) = ((X1 ◇ ((X1 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X1) ◇ X1)) := superpose step11 step20
  have step159 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step44 step13
  have step273 : sK0 ≠ sK0 := superpose step159 step12
  subsumption step273 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation26_implies_Equation1654 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation26 G) : Equation1654 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X1) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ ((sK0 ◇ sK1) ◇ ((sK1 ◇ sK0) ◇ sK0)) := mod_symm nh
  have step13 : sK0 ≠ ((sK0 ◇ sK1) ◇ sK1) := superpose step9 step10
  subsumption step13 step9


@[equational_result]
theorem Finite.Equation677_and_Equation26_implies_Equation1850 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation26 G) : Equation1850 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X1) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) := mod_symm nh
  have step13 : sK0 ≠ sK0 := superpose step9 step10
  subsumption step13 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation26_implies_Equation2457 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation26 G) : Equation2457 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X1) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ ((sK0 ◇ ((sK1 ◇ sK0) ◇ sK0)) ◇ sK1) := mod_symm nh
  have step13 : sK0 ≠ ((sK0 ◇ sK1) ◇ sK1) := superpose step9 step10
  subsumption step13 step9


@[equational_result]
theorem Finite.Equation677_and_Equation26_implies_Equation3066 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation26 G) : Equation3066 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X1) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ ((((sK0 ◇ sK1) ◇ sK0) ◇ sK0) ◇ sK1) := mod_symm nh
  have step13 : sK0 ≠ ((sK0 ◇ sK1) ◇ sK1) := superpose step9 step10
  subsumption step13 step9


@[equational_result]
theorem Finite.Equation677_and_Equation26_implies_Equation3079 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation26 G) : Equation3079 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X1) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ ((((sK0 ◇ sK1) ◇ sK1) ◇ sK1) ◇ sK1) := mod_symm nh
  have step15 : sK0 ≠ ((sK0 ◇ sK1) ◇ sK1) := superpose step9 step10
  subsumption step15 step9


@[equational_result]
theorem Finite.Equation677_and_Equation26_implies_Equation4073 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation26 G) : Equation4073 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X1) = X0 := mod_symm (h ..)
  have step10 : (sK0 ◇ sK0) ≠ (((sK0 ◇ sK1) ◇ sK1) ◇ sK0) := mod_symm nh
  have step13 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose step9 step10
  subsumption step13 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation264_implies_Equation255 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation264 G) : Equation255 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have step9 (X0 X1 : G) :  (((X0 ◇ X1) ◇ X1) ◇ X1) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ (((sK0 ◇ sK0) ◇ sK0) ◇ sK0) := mod_symm nh
  have step13 : sK0 ≠ sK0 := superpose step9 step10
  subsumption step13 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation2_implies_Equation667 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation2 G) : Equation667 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  X0 = X1 := mod_symm (h ..)
  have step10 : sK0 ≠ (sK1 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK1))) := mod_symm nh
  have step24 (X0 : G) :  sK0 ≠ (X0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ X0))) := superpose step9 step10
  subsumption step24 step9


@[equational_result]
theorem Finite.Equation677_and_Equation2670_implies_Equation3 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation2670 G) : Equation3 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have step10 (X0 X1 : G) :  (((X0 ◇ X1) ◇ (X1 ◇ X0)) ◇ X1) = X0 := mod_symm (h ..)
  have step11 : sK0 ≠ (sK0 ◇ sK0) := mod_symm nh
  have step12 (X Y : G) : (((X ◇ Y) ◇ Y) ◇ (Y ◇ (X ◇ Y))) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => ((s ◇ Y) ◇ (Y ◇ s))) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (s ◇ Y)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (s ◇ Y)) (fun s => ((s ◇ Y) ◇ (Y ◇ s))) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step14 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step15 (X0 X1 : G) :  ((X0 ◇ X1) ◇ (X1 ◇ X0)) = ((X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ (X1 ◇ X0)))) ◇ X1) := superpose step10 step10
  have step26 (X0 X1 : G) :  (X0 ◇ ((((X0 ◇ X1) ◇ (X1 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X1) ◇ (X1 ◇ X0)))) = X1 := superpose step10 step14
  have step28 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step14 step14
  have step341 (X0 : G) :  (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) = X0 := superpose step10 step26
  have step511 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose step341 step15
  have step534 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) ◇ X0)) := superpose step341 step28
  have step535 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose step14 step534
  have step544 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose step511 step535
  have step631 (X0 : G) :  (X0 ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) := superpose step544 step12
  have step670 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step12 step631
  have step838 : sK0 ≠ sK0 := superpose step670 step11
  subsumption step838 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation2700_implies_Equation3 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation2700 G) : Equation3 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have step10 (X0 X1 : G) :  (((X1 ◇ X0) ◇ (X0 ◇ X1)) ◇ X1) = X0 := mod_symm (h ..)
  have step11 : sK0 ≠ (sK0 ◇ sK0) := mod_symm nh
  have step12 (X Y : G) : ((Y ◇ (X ◇ Y)) ◇ ((X ◇ Y) ◇ Y)) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => ((Y ◇ s) ◇ (s ◇ Y))) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (s ◇ Y)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (s ◇ Y)) (fun s => ((Y ◇ s) ◇ (s ◇ Y))) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step13 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step14 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step16 (X0 X1 : G) :  ((X1 ◇ X0) ◇ (X0 ◇ X1)) = (((X1 ◇ ((X1 ◇ X0) ◇ (X0 ◇ X1))) ◇ X0) ◇ X1) := superpose step10 step10
  have step22 (X0 X1 : G) :  (((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X0) ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1)))) = X1 := superpose step13 step12
  have step28 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step14 step14
  have step356 (X0 : G) :  (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) ◇ X0) = X0 := superpose step13 step22
  have step385 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) := superpose step356 step12
  have step400 (X0 : G) :  (X0 ◇ ((X0 ◇ X0) ◇ X0)) = ((((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) ◇ X0) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0)) := superpose step356 step28
  have step401 (X0 : G) :  (X0 ◇ ((X0 ◇ X0) ◇ X0)) = (X0 ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0)) := superpose step356 step400
  have step409 (X0 : G) :  (X0 ◇ ((X0 ◇ X0) ◇ X0)) = (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose step385 step401
  have step521 (X0 : G) :  ((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = (((X0 ◇ ((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ X0) := superpose step385 step16
  have step541 (X0 : G) :  (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = (((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ X0) := superpose step13 step521
  have step556 (X0 : G) :  (X0 ◇ ((X0 ◇ X0) ◇ X0)) = (((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ X0) := superpose step409 step541
  have step562 (X0 : G) :  (X0 ◇ ((X0 ◇ X0) ◇ X0)) = ((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ X0) := superpose step13 step556
  have step564 (X0 : G) :  (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose step13 step562
  have step631 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = X0 := superpose step564 step13
  have step658 (X0 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0))) := superpose step564 step28
  have step659 (X0 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ X0) = X0 := superpose step14 step658
  have step667 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step631 step659
  have step742 : sK0 ≠ sK0 := superpose step667 step11
  subsumption step742 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation2_implies_Equation704 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation2 G) : Equation704 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  X0 = X1 := mod_symm (h ..)
  have step10 : sK0 ≠ (sK1 ◇ (sK1 ◇ ((sK0 ◇ sK0) ◇ sK1))) := mod_symm nh
  have step24 (X0 : G) :  sK0 ≠ (X0 ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ X0))) := superpose step9 step10
  subsumption step24 step9


@[equational_result]
theorem Finite.Equation677_and_Equation271_implies_Equation1312 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation271 G) : Equation1312 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step11 : sK0 ≠ (sK1 ◇ (((sK1 ◇ sK0) ◇ sK0) ◇ sK0)) := mod_symm nh
  have step12 (X Y : G) : ((Y ◇ (X ◇ Y)) ◇ (X ◇ Y)) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => ((Y ◇ s) ◇ s)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (s ◇ Y)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (s ◇ Y)) (fun s => ((Y ◇ s) ◇ s)) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step13 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step14 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step19 (X0 X1 : G) :  (X1 ◇ (X0 ◇ X1)) = (((X0 ◇ X1) ◇ X0) ◇ X0) := superpose step12 step12
  have step87 (X0 X1 : G) :  ((X0 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)) = (((X1 ◇ (X1 ◇ X0)) ◇ X1) ◇ X0) := superpose step14 step19
  have step114 (X0 X1 : G) :  (((X1 ◇ (X1 ◇ X0)) ◇ X1) ◇ X0) = X1 := superpose step12 step87
  have step298 (X0 X1 : G) :  (X1 ◇ X0) = ((X0 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) := superpose step114 step19
  have step301 (X0 X1 : G) :  (X1 ◇ X0) = (X0 ◇ (X0 ◇ X1)) := superpose step12 step298
  have step402 (X0 X1 : G) :  (X1 ◇ (X0 ◇ X1)) = ((X1 ◇ X0) ◇ X1) := superpose step301 step301
  have step569 (X0 X1 : G) :  (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0)))) = X1 := superpose step402 step13
  have step869 (X0 X1 : G) :  (X1 ◇ (X0 ◇ (((X0 ◇ X1) ◇ X0) ◇ X0))) = X0 := superpose step19 step569
  have step911 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0))) = X0 := superpose step402 step869
  have step944 (X0 X1 : G) :  (X1 ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0)))) = X0 := superpose step402 step911
  have step965 (X0 X1 : G) :  (X1 ◇ (((X1 ◇ X0) ◇ X0) ◇ X0)) = X0 := superpose step301 step944
  have step1107 : sK0 ≠ sK0 := superpose step965 step11
  subsumption step1107 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation271_implies_Equation1685 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation271 G) : Equation1685 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step10 (X0 X1 : G) :  (((X1 ◇ X0) ◇ X0) ◇ X1) = X0 := mod_symm (h ..)
  have step11 : sK0 ≠ ((sK1 ◇ sK0) ◇ ((sK0 ◇ sK1) ◇ sK1)) := mod_symm nh
  have step15 (X0 X1 : G) :  ((X0 ◇ X1) ◇ ((X1 ◇ X0) ◇ X0)) = X1 := superpose step10 step10
  have step63 : sK0 ≠ sK0 := superpose step15 step11
  subsumption step63 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation271_implies_Equation2098 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation271 G) : Equation2098 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step11 : sK0 ≠ (((sK1 ◇ sK0) ◇ sK1) ◇ (sK0 ◇ sK1)) := mod_symm nh
  have step12 (X Y : G) : ((Y ◇ (X ◇ Y)) ◇ (X ◇ Y)) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => ((Y ◇ s) ◇ s)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (s ◇ Y)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (s ◇ Y)) (fun s => ((Y ◇ s) ◇ s)) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step14 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step19 (X0 X1 : G) :  (X1 ◇ (X0 ◇ X1)) = (((X0 ◇ X1) ◇ X0) ◇ X0) := superpose step12 step12
  have step87 (X0 X1 : G) :  ((X0 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)) = (((X1 ◇ (X1 ◇ X0)) ◇ X1) ◇ X0) := superpose step14 step19
  have step114 (X0 X1 : G) :  (((X1 ◇ (X1 ◇ X0)) ◇ X1) ◇ X0) = X1 := superpose step12 step87
  have step298 (X0 X1 : G) :  (X1 ◇ X0) = ((X0 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) := superpose step114 step19
  have step301 (X0 X1 : G) :  (X1 ◇ X0) = (X0 ◇ (X0 ◇ X1)) := superpose step12 step298
  have step402 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X1) = (X1 ◇ (X0 ◇ X1)) := superpose step301 step301
  have step579 : sK0 ≠ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1)) := superpose step402 step11
  subsumption step579 step12


@[equational_result]
theorem Finite.Equation677_and_Equation271_implies_Equation2244 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation271 G) : Equation2244 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step10 (X0 X1 : G) :  (((X1 ◇ X0) ◇ X0) ◇ X1) = X0 := mod_symm (h ..)
  have step11 : sK0 ≠ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ sK1) := mod_symm nh
  have step12 (X Y : G) : ((Y ◇ (X ◇ Y)) ◇ (X ◇ Y)) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => ((Y ◇ s) ◇ s)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (s ◇ Y)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (s ◇ Y)) (fun s => ((Y ◇ s) ◇ s)) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step14 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step19 (X0 X1 : G) :  (X1 ◇ (X0 ◇ X1)) = (((X0 ◇ X1) ◇ X0) ◇ X0) := superpose step12 step12
  have step87 (X0 X1 : G) :  ((X0 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)) = (((X1 ◇ (X1 ◇ X0)) ◇ X1) ◇ X0) := superpose step14 step19
  have step114 (X0 X1 : G) :  (((X1 ◇ (X1 ◇ X0)) ◇ X1) ◇ X0) = X1 := superpose step12 step87
  have step298 (X0 X1 : G) :  (X1 ◇ X0) = ((X0 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) := superpose step114 step19
  have step301 (X0 X1 : G) :  (X1 ◇ X0) = (X0 ◇ (X0 ◇ X1)) := superpose step12 step298
  have step430 : sK0 ≠ (((sK1 ◇ sK0) ◇ sK0) ◇ sK1) := superpose step301 step11
  subsumption step430 step10


@[equational_result]
theorem Finite.Equation677_and_Equation271_implies_Equation2447 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation271 G) : Equation2447 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step10 (X0 X1 : G) :  (((X1 ◇ X0) ◇ X0) ◇ X1) = X0 := mod_symm (h ..)
  have step11 : sK0 ≠ ((sK0 ◇ ((sK0 ◇ sK1) ◇ sK0)) ◇ sK1) := mod_symm nh
  have step12 (X Y : G) : ((Y ◇ (X ◇ Y)) ◇ (X ◇ Y)) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => ((Y ◇ s) ◇ s)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (s ◇ Y)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (s ◇ Y)) (fun s => ((Y ◇ s) ◇ s)) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step14 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step19 (X0 X1 : G) :  (X1 ◇ (X0 ◇ X1)) = (((X0 ◇ X1) ◇ X0) ◇ X0) := superpose step12 step12
  have step87 (X0 X1 : G) :  ((X0 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)) = (((X1 ◇ (X1 ◇ X0)) ◇ X1) ◇ X0) := superpose step14 step19
  have step114 (X0 X1 : G) :  (((X1 ◇ (X1 ◇ X0)) ◇ X1) ◇ X0) = X1 := superpose step12 step87
  have step298 (X0 X1 : G) :  (X1 ◇ X0) = ((X0 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) := superpose step114 step19
  have step301 (X0 X1 : G) :  (X1 ◇ X0) = (X0 ◇ (X0 ◇ X1)) := superpose step12 step298
  have step402 (X0 X1 : G) :  (X1 ◇ (X0 ◇ X1)) = ((X1 ◇ X0) ◇ X1) := superpose step301 step301
  have step567 : sK0 ≠ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ sK1) := superpose step402 step11
  have step615 : sK0 ≠ (((sK1 ◇ sK0) ◇ sK0) ◇ sK1) := superpose step301 step567
  subsumption step615 step10


@[equational_result]
theorem Finite.Equation677_and_Equation271_implies_Equation3343 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation271 G) : Equation3343 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step11 : (sK0 ◇ sK1) ≠ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) := mod_symm nh
  have step12 (X Y : G) : ((Y ◇ (X ◇ Y)) ◇ (X ◇ Y)) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => ((Y ◇ s) ◇ s)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (s ◇ Y)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (s ◇ Y)) (fun s => ((Y ◇ s) ◇ s)) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step14 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step19 (X0 X1 : G) :  (X1 ◇ (X0 ◇ X1)) = (((X0 ◇ X1) ◇ X0) ◇ X0) := superpose step12 step12
  have step87 (X0 X1 : G) :  ((X0 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)) = (((X1 ◇ (X1 ◇ X0)) ◇ X1) ◇ X0) := superpose step14 step19
  have step114 (X0 X1 : G) :  (((X1 ◇ (X1 ◇ X0)) ◇ X1) ◇ X0) = X1 := superpose step12 step87
  have step298 (X0 X1 : G) :  (X1 ◇ X0) = ((X0 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) := superpose step114 step19
  have step301 (X0 X1 : G) :  (X1 ◇ X0) = (X0 ◇ (X0 ◇ X1)) := superpose step12 step298
  have step430 : (sK0 ◇ sK1) ≠ (sK1 ◇ (sK1 ◇ sK0)) := superpose step301 step11
  subsumption step430 step301


@[equational_result]
theorem Finite.Equation677_and_Equation271_implies_Equation474 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation271 G) : Equation474 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step11 : sK0 ≠ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := mod_symm nh
  have step12 (X Y : G) : ((Y ◇ (X ◇ Y)) ◇ (X ◇ Y)) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => ((Y ◇ s) ◇ s)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (s ◇ Y)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (s ◇ Y)) (fun s => ((Y ◇ s) ◇ s)) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step13 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step14 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step19 (X0 X1 : G) :  (X1 ◇ (X0 ◇ X1)) = (((X0 ◇ X1) ◇ X0) ◇ X0) := superpose step12 step12
  have step87 (X0 X1 : G) :  ((X0 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)) = (((X1 ◇ (X1 ◇ X0)) ◇ X1) ◇ X0) := superpose step14 step19
  have step114 (X0 X1 : G) :  (((X1 ◇ (X1 ◇ X0)) ◇ X1) ◇ X0) = X1 := superpose step12 step87
  have step298 (X0 X1 : G) :  (X1 ◇ X0) = ((X0 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) := superpose step114 step19
  have step301 (X0 X1 : G) :  (X1 ◇ X0) = (X0 ◇ (X0 ◇ X1)) := superpose step12 step298
  have step402 (X0 X1 : G) :  (X1 ◇ (X0 ◇ X1)) = ((X1 ◇ X0) ◇ X1) := superpose step301 step301
  have step572 (X0 X1 : G) :  (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0)))) = X1 := superpose step402 step13
  have step890 : sK0 ≠ sK0 := superpose step572 step11
  subsumption step890 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation271_implies_Equation713 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation271 G) : Equation713 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step10 (X0 X1 : G) :  (((X1 ◇ X0) ◇ X0) ◇ X1) = X0 := mod_symm (h ..)
  have step11 : sK0 ≠ (sK1 ◇ (sK1 ◇ ((sK1 ◇ sK0) ◇ sK0))) := mod_symm nh
  have step12 (X Y : G) : ((Y ◇ (X ◇ Y)) ◇ (X ◇ Y)) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => ((Y ◇ s) ◇ s)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (s ◇ Y)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (s ◇ Y)) (fun s => ((Y ◇ s) ◇ s)) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step14 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step19 (X0 X1 : G) :  (X1 ◇ (X0 ◇ X1)) = (((X0 ◇ X1) ◇ X0) ◇ X0) := superpose step12 step12
  have step87 (X0 X1 : G) :  ((X0 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)) = (((X1 ◇ (X1 ◇ X0)) ◇ X1) ◇ X0) := superpose step14 step19
  have step114 (X0 X1 : G) :  (((X1 ◇ (X1 ◇ X0)) ◇ X1) ◇ X0) = X1 := superpose step12 step87
  have step298 (X0 X1 : G) :  (X1 ◇ X0) = ((X0 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) := superpose step114 step19
  have step301 (X0 X1 : G) :  (X1 ◇ X0) = (X0 ◇ (X0 ◇ X1)) := superpose step12 step298
  have step410 : sK0 ≠ (((sK1 ◇ sK0) ◇ sK0) ◇ sK1) := superpose step301 step11
  subsumption step410 step10


@[equational_result]
theorem Finite.Equation677_and_Equation271_implies_Equation882 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation271 G) : Equation882 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step10 (X0 X1 : G) :  (((X1 ◇ X0) ◇ X0) ◇ X1) = X0 := mod_symm (h ..)
  have step11 : sK0 ≠ (sK1 ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ sK0))) := mod_symm nh
  have step12 (X Y : G) : ((Y ◇ (X ◇ Y)) ◇ (X ◇ Y)) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => ((Y ◇ s) ◇ s)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (s ◇ Y)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (s ◇ Y)) (fun s => ((Y ◇ s) ◇ s)) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step13 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step14 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step15 (X0 X1 : G) :  ((X0 ◇ X1) ◇ ((X1 ◇ X0) ◇ X0)) = X1 := superpose step10 step10
  have step19 (X0 X1 : G) :  (X1 ◇ (X0 ◇ X1)) = (((X0 ◇ X1) ◇ X0) ◇ X0) := superpose step12 step12
  have step22 (X0 X1 : G) :  (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0)))) = X1 := superpose step10 step13
  have step26 (X0 X1 : G) :  (((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X0) ◇ X0) = X1 := superpose step13 step12
  have step27 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ X0) ◇ X1)) = ((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) ◇ X1) := superpose step13 step10
  have step29 (X0 X1 : G) :  (X0 ◇ X1) = (X0 ◇ (((X1 ◇ (X0 ◇ X1)) ◇ X0) ◇ (X1 ◇ (X0 ◇ X1)))) := superpose step12 step14
  have step35 (X0 X1 : G) :  (X1 ◇ X0) = ((((X1 ◇ (X1 ◇ X0)) ◇ X1) ◇ X0) ◇ X0) := superpose step14 step12
  have step87 (X0 X1 : G) :  ((X0 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)) = (((X1 ◇ (X1 ◇ X0)) ◇ X1) ◇ X0) := superpose step14 step19
  have step105 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X1) = ((X1 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X0 ◇ (X1 ◇ X0))) := superpose step19 step12
  have step114 (X0 X1 : G) :  (((X1 ◇ (X1 ◇ X0)) ◇ X1) ◇ X0) = X1 := superpose step12 step87
  have step298 (X0 X1 : G) :  (X1 ◇ X0) = ((X0 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) := superpose step114 step19
  have step301 (X0 X1 : G) :  (X1 ◇ X0) = (X0 ◇ (X0 ◇ X1)) := superpose step12 step298
  have step391 (X0 X1 : G) :  (((X1 ◇ X0) ◇ X1) ◇ (X0 ◇ (X1 ◇ X0))) = (X1 ◇ ((X1 ◇ X0) ◇ X1)) := superpose step19 step301
  have step394 (X0 X1 : G) :  ((X1 ◇ (X0 ◇ X1)) ◇ X0) = ((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1))) := superpose step12 step301
  have step402 (X0 X1 : G) :  (X1 ◇ (X0 ◇ X1)) = ((X1 ◇ X0) ◇ X1) := superpose step301 step301
  have step439 (X0 X1 : G) :  (X1 ◇ (X1 ◇ (X0 ◇ X1))) = ((X1 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X0))) := superpose step402 step391
  have step444 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X1) = ((X1 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X0))) := superpose step301 step439
  have step465 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) ◇ (X1 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1)))))) = X1 := superpose step13 step22
  have step507 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) ◇ (X1 ◇ (((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) ◇ X0) ◇ X0))) = X1 := superpose step19 step465
  have step522 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) ◇ (X1 ◇ ((X0 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X0)) ◇ X0))) = X1 := superpose step402 step507
  have step532 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) ◇ (X1 ◇ (X0 ◇ (((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X0) ◇ X0)))) = X1 := superpose step402 step522
  have step538 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) ◇ (X1 ◇ (X0 ◇ X1))) = X1 := superpose step26 step532
  have step541 (X0 X1 : G) :  ((((X1 ◇ X0) ◇ X1) ◇ X0) ◇ (X1 ◇ (X0 ◇ X1))) = X1 := superpose step301 step538
  have step544 (X0 X1 : G) :  (((X1 ◇ (X0 ◇ X1)) ◇ X0) ◇ (X1 ◇ (X0 ◇ X1))) = X1 := superpose step402 step541
  have step546 (X0 X1 : G) :  ((X1 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) = X1 := superpose step402 step544
  have step1196 (X0 X1 : G) :  (X1 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ X0) ◇ X1))) = ((X1 ◇ (X1 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ X0) ◇ X1)))) ◇ ((X1 ◇ X0) ◇ X1)) := superpose step19 step27
  have step1245 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ X0) ◇ X1)) = (((((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1)))) ◇ X1) ◇ X1) := superpose step27 step35
  have step1256 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ X0) ◇ X1)) = ((((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))))) ◇ X1) ◇ X1) := superpose step402 step1245
  have step1299 (X0 X1 : G) :  (X1 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X1 ◇ (X0 ◇ X1)))) = ((X1 ◇ (X1 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X1 ◇ (X0 ◇ X1))))) ◇ (X1 ◇ (X0 ◇ X1))) := superpose step402 step1196
  have step1306 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ X0) ◇ X1)) = (((((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1)))) ◇ X0) ◇ X1) ◇ X1) := superpose step394 step1256
  have step1336 (X0 X1 : G) :  (X1 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X1 ◇ (X0 ◇ X1)))) = ((((X0 ◇ (X1 ◇ X0)) ◇ (X1 ◇ (X0 ◇ X1))) ◇ X1) ◇ (X1 ◇ (X0 ◇ X1))) := superpose step301 step1299
  have step1341 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ X0) ◇ X1)) = ((((((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) ◇ X0) ◇ X0) ◇ X0) ◇ X1) ◇ X1) := superpose step19 step1306
  have step1360 (X0 X1 : G) :  (X1 ◇ ((X1 ◇ X0) ◇ X0)) = ((((X1 ◇ X0) ◇ X0) ◇ X1) ◇ (X1 ◇ (X0 ◇ X1))) := superpose step444 step1336
  have step1365 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ X0) ◇ X1)) = (((((X0 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X0)) ◇ X0) ◇ X0) ◇ X1) ◇ X1) := superpose step402 step1341
  have step1377 (X0 X1 : G) :  (X0 ◇ (X1 ◇ (X0 ◇ X1))) = (X1 ◇ ((X1 ◇ X0) ◇ X0)) := superpose step10 step1360
  have step1381 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ X0) ◇ X1)) = ((((X0 ◇ (((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X0) ◇ X0)) ◇ X0) ◇ X1) ◇ X1) := superpose step402 step1365
  have step1389 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ X0) ◇ X1)) = (((X0 ◇ ((((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X0) ◇ X0) ◇ X0)) ◇ X1) ◇ X1) := superpose step402 step1381
  have step1395 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ X0) ◇ X1)) = (((X0 ◇ (X1 ◇ X0)) ◇ X1) ◇ X1) := superpose step26 step1389
  have step1401 (X0 X1 : G) :  (X0 ◇ (X1 ◇ (X0 ◇ X1))) = (((X0 ◇ (X1 ◇ X0)) ◇ X1) ◇ X1) := superpose step402 step1395
  have step1517 (X0 X1 : G) :  (((X1 ◇ (X0 ◇ X1)) ◇ X0) ◇ (X1 ◇ (X0 ◇ X1))) = ((X0 ◇ X1) ◇ (((((X1 ◇ (X0 ◇ X1)) ◇ X0) ◇ (X1 ◇ (X0 ◇ X1))) ◇ X0) ◇ X0)) := superpose step29 step15
  have step1542 (X0 X1 : G) :  ((X1 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) = ((X0 ◇ X1) ◇ ((((X1 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) ◇ X0) ◇ X0)) := superpose step402 step1517
  have step1588 (X0 X1 : G) :  ((X1 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) = ((X0 ◇ X1) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X0)))) := superpose step1401 step1542
  have step1625 (X0 X1 : G) :  ((X1 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) = ((X0 ◇ X1) ◇ (X0 ◇ ((X0 ◇ (X1 ◇ (X0 ◇ X1))) ◇ (X1 ◇ (X0 ◇ X1))))) := superpose step1377 step1588
  have step1654 (X0 X1 : G) :  ((X1 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) = ((X0 ◇ X1) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X0))) := superpose step105 step1625
  have step1675 (X0 X1 : G) :  ((X1 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) = (X0 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1))) := superpose step1377 step1654
  have step1691 (X0 X1 : G) :  ((X1 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) = (X0 ◇ ((X1 ◇ X0) ◇ (X0 ◇ X1))) := superpose step301 step1675
  have step1703 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ X0) ◇ (X0 ◇ X1))) = X1 := superpose step546 step1691
  have step1792 : sK0 ≠ sK0 := superpose step1703 step11
  subsumption step1792 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation2_implies_Equation75 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation2 G) : Equation75 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  X0 = X1 := mod_symm (h ..)
  have step10 : sK0 ≠ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) := mod_symm nh
  have step22 (X0 : G) :  sK0 ≠ X0 := superpose step9 step10
  subsumption step22 step9


@[equational_result]
theorem Finite.Equation677_and_Equation283_implies_Equation1426 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation283 G) : Equation1426 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have step9 (X0 X1 : G) :  (((X1 ◇ X1) ◇ X1) ◇ X0) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step17 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose step9 step11
  have step35 : sK0 ≠ sK0 := superpose step17 step10
  subsumption step35 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation283_implies_Equation255 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation283 G) : Equation255 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have step9 (X0 X1 : G) :  (((X1 ◇ X1) ◇ X1) ◇ X0) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ (((sK0 ◇ sK0) ◇ sK0) ◇ sK0) := mod_symm nh
  have step14 : sK0 ≠ sK0 := superpose step9 step10
  subsumption step14 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation283_implies_Equation623 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation283 G) : Equation623 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (((X1 ◇ X1) ◇ X1) ◇ X0) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ (sK0 ◇ (sK0 ◇ ((sK1 ◇ sK1) ◇ sK1))) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step20 (X0 X1 : G) :  (X0 ◇ ((((X1 ◇ X1) ◇ X1) ◇ X0) ◇ ((X1 ◇ X1) ◇ X1))) = X0 := superpose step11 step9
  have step21 (X0 X1 : G) :  (X0 ◇ (X0 ◇ ((X1 ◇ X1) ◇ X1))) = X0 := superpose step9 step20
  have step43 : sK0 ≠ sK0 := superpose step21 step10
  subsumption step43 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation283_implies_Equation817 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation283 G) : Equation817 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have step9 (X0 X1 : G) :  (((X1 ◇ X1) ◇ X1) ◇ X0) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step16 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ X0) ◇ X1)) = (X1 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X0 ◇ X1))) := superpose step11 step11
  have step17 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose step9 step11
  have step18 (X0 X1 : G) :  ((X1 ◇ X1) ◇ X1) = (X0 ◇ ((X0 ◇ ((X1 ◇ X1) ◇ X1)) ◇ X0)) := superpose step9 step11
  have step20 (X0 X1 : G) :  (X0 ◇ ((((X1 ◇ X1) ◇ X1) ◇ X0) ◇ ((X1 ◇ X1) ◇ X1))) = X0 := superpose step11 step9
  have step21 (X0 X1 : G) :  (X0 ◇ (X0 ◇ ((X1 ◇ X1) ◇ X1))) = X0 := superpose step9 step20
  have step25 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step35 (X0 : G) :  (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0))) = (X0 ◇ (X0 ◇ X0)) := superpose step17 step12
  have step36 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))) := superpose step17 step11
  have step37 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose step25 step35
  have step43 (X0 X1 : G) :  ((X0 ◇ X0) ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ ((X1 ◇ X1) ◇ X1)) := superpose step21 step9
  have step46 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ X1) ◇ X1)) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose step21 step12
  have step49 (X0 X1 : G) :  ((X1 ◇ X1) ◇ X1) = ((X0 ◇ X0) ◇ X0) := superpose step9 step43
  have step69 (X0 X1 : G) :  (((X0 ◇ X0) ◇ X0) ◇ (((X1 ◇ X1) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X1 ◇ X1))) = X1 := superpose step49 step12
  have step74 (X0 X1 : G) :  (((X1 ◇ X1) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X1 ◇ X1)) = X1 := superpose step9 step69
  have step97 (X0 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))))) = X0 := superpose step37 step11
  have step146 (X0 X1 X2 : G) :  (X0 ◇ ((X1 ◇ X1) ◇ X1)) = (X0 ◇ ((X2 ◇ X2) ◇ X2)) := superpose step46 step46
  have step154 (X0 X1 : G) :  ((X0 ◇ X0) ◇ X0) = (X0 ◇ ((X0 ◇ ((X1 ◇ X1) ◇ X1)) ◇ X0)) := superpose step46 step18
  have step243 (X0 X1 : G) :  (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) = (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ ((X1 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) ◇ X1)) := superpose step25 step12
  have step621 (X0 X1 : G) :  ((((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) ◇ (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X1)) = (X1 ◇ (((((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) ◇ (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X1)) ◇ ((((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) ◇ X1))) := superpose step25 step16
  have step985 (X0 X1 : G) :  ((X0 ◇ ((X1 ◇ X1) ◇ X1)) ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0)) := superpose step154 step12
  have step988 (X0 X1 : G) :  ((X0 ◇ ((X1 ◇ X1) ◇ X1)) ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) := superpose step9 step985
  have step5568 (X0 : G) :  (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) = ((((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ X0)))) ◇ X0)) := superpose step37 step243
  have step5644 (X0 : G) :  (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) = ((X0 ◇ (((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ X0)))) ◇ X0) := superpose step9 step5568
  have step5684 (X0 : G) :  (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) := superpose step988 step5644
  have step5708 (X0 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) := superpose step37 step5684
  have step5725 (X0 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0))) = X0 := superpose step5708 step97
  have step5726 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0)) := superpose step5708 step36
  have step5727 (X0 X1 : G) :  ((((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ X1) = X1 := superpose step5708 step9
  have step5787 (X0 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) = X0 := superpose step18 step5725
  have step6131 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ ((X1 ◇ X1) ◇ X1)) = X0 := superpose step5787 step146
  have step7063 (X0 : G) :  ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) := superpose step74 step5726
  have step7265 (X0 X1 : G) :  ((X0 ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) ◇ X1) = X1 := superpose step74 step5727
  have step7616 (X0 X1 : G) :  ((X0 ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0)) ◇ X1) = X1 := superpose step7063 step7265
  have step8238 (X0 X1 : G) :  (X0 ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0)) = ((X0 ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X1 ◇ X1) ◇ X1)) := superpose step7616 step21
  have step8241 (X0 X1 : G) :  ((X1 ◇ X1) ◇ X1) = (X0 ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0)) := superpose step7616 step8238
  have step9021 (X0 X1 : G) :  (((X0 ◇ X0) ◇ X0) ◇ ((X1 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X1)) = (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ X1) := superpose step8241 step12
  have step9042 (X0 X1 : G) :  ((X1 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X1) = (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ X1) := superpose step9 step9021
  have step18367 (X0 : G) :  (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) = ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ X0)) := superpose step7063 step37
  have step18371 (X0 : G) :  (((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0)) = ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0)) := superpose step7063 step5708
  have step18376 (X0 X1 : G) :  (X0 ◇ X0) = ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X1 ◇ X1) ◇ X1)) := superpose step7063 step6131
  have step18426 (X0 : G) :  ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0)) = X0 := superpose step74 step18371
  have step18968 (X0 X1 X2 : G) :  (X0 ◇ X0) = (((X0 ◇ ((X1 ◇ X1) ◇ X1)) ◇ X0) ◇ ((X2 ◇ X2) ◇ X2)) := superpose step9042 step18376
  have step19067 (X0 X1 : G) :  ((((X0 ◇ X0) ◇ ((X1 ◇ X1) ◇ X1)) ◇ (X0 ◇ X0)) ◇ ((((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X1 ◇ X1) ◇ X1))) = (((X1 ◇ X1) ◇ X1) ◇ (((((X0 ◇ X0) ◇ ((X1 ◇ X1) ◇ X1)) ◇ (X0 ◇ X0)) ◇ ((((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X1 ◇ X1) ◇ X1))) ◇ ((((X0 ◇ X0) ◇ ((X1 ◇ X1) ◇ X1)) ◇ (X0 ◇ X0)) ◇ ((X1 ◇ X1) ◇ X1)))) := superpose step18376 step621
  have step19082 (X0 X1 : G) :  ((((X0 ◇ X0) ◇ ((X1 ◇ X1) ◇ X1)) ◇ (X0 ◇ X0)) ◇ ((((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X1 ◇ X1) ◇ X1))) = (((((X0 ◇ X0) ◇ ((X1 ◇ X1) ◇ X1)) ◇ (X0 ◇ X0)) ◇ ((((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X1 ◇ X1) ◇ X1))) ◇ ((((X0 ◇ X0) ◇ ((X1 ◇ X1) ◇ X1)) ◇ (X0 ◇ X0)) ◇ ((X1 ◇ X1) ◇ X1))) := superpose step9 step19067
  have step19184 (X0 X1 : G) :  ((((X0 ◇ X0) ◇ ((X1 ◇ X1) ◇ X1)) ◇ (X0 ◇ X0)) ◇ ((((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X1 ◇ X1) ◇ X1))) = (((((X0 ◇ X0) ◇ ((X1 ◇ X1) ◇ X1)) ◇ (X0 ◇ X0)) ◇ ((((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X1 ◇ X1) ◇ X1))) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose step18968 step19082
  have step19253 (X0 X1 : G) :  ((((X0 ◇ X0) ◇ ((X1 ◇ X1) ◇ X1)) ◇ (X0 ◇ X0)) ◇ (((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X1 ◇ X1) ◇ X1))) = (((((X0 ◇ X0) ◇ ((X1 ◇ X1) ◇ X1)) ◇ (X0 ◇ X0)) ◇ (((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X1 ◇ X1) ◇ X1))) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose step18367 step19184
  have step19292 (X0 X1 : G) :  ((((X0 ◇ X0) ◇ ((X1 ◇ X1) ◇ X1)) ◇ (X0 ◇ X0)) ◇ (X0 ◇ ((X1 ◇ X1) ◇ X1))) = (((((X0 ◇ X0) ◇ ((X1 ◇ X1) ◇ X1)) ◇ (X0 ◇ X0)) ◇ (X0 ◇ ((X1 ◇ X1) ◇ X1))) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose step18426 step19253
  have step19317 (X0 X1 : G) :  (X0 ◇ (X0 ◇ ((X1 ◇ X1) ◇ X1))) = ((X0 ◇ (X0 ◇ ((X1 ◇ X1) ◇ X1))) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose step74 step19292
  have step19331 (X0 : G) :  (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = X0 := superpose step21 step19317
  have step19892 : sK0 ≠ sK0 := superpose step19331 step10
  subsumption step19892 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation2856_implies_Equation3 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation2856 G) : Equation3 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have step11 (X0 X1 : G) :  (((X0 ◇ (X0 ◇ X1)) ◇ X1) ◇ X1) = X0 := mod_symm (h ..)
  have step12 : sK0 ≠ (sK0 ◇ sK0) := mod_symm nh
  have step14 (X Y : G) : (((X ◇ Y) ◇ ((X ◇ Y) ◇ Y)) ◇ Y) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => ((s ◇ (s ◇ Y)) ◇ Y)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (s ◇ Y)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (s ◇ Y)) (fun s => ((s ◇ (s ◇ Y)) ◇ Y)) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step16 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step24 (X0 X1 : G) :  (X0 ◇ (X0 ◇ X1)) = ((((X0 ◇ (X0 ◇ X1)) ◇ X1) ◇ X0) ◇ X1) := superpose step11 step14
  have step91 (X0 : G) :  (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose step11 step24
  have step141 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) := superpose step91 step16
  have step146 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step16 step141
  have step219 : sK0 ≠ sK0 := superpose step146 step12
  subsumption step219 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation2863_implies_Equation3 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation2863 G) : Equation3 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have step10 (X0 X1 : G) :  (((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ X1) = X0 := mod_symm (h ..)
  have step11 : sK0 ≠ (sK0 ◇ sK0) := mod_symm nh
  have step12 (X Y : G) : (((X ◇ Y) ◇ (Y ◇ (X ◇ Y))) ◇ (X ◇ Y)) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => ((s ◇ (Y ◇ s)) ◇ s)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (s ◇ Y)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (s ◇ Y)) (fun s => ((s ◇ (Y ◇ s)) ◇ s)) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step13 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step14 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step15 (X0 X1 : G) :  (((X1 ◇ X0) ◇ X1) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0)) = X1 := superpose step10 step10
  have step24 (X0 X1 : G) :  (X1 ◇ X0) = ((X0 ◇ (((X1 ◇ (X1 ◇ X0)) ◇ X1) ◇ X0)) ◇ X0) := superpose step14 step12
  have step27 (X0 X1 : G) :  (X1 ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X0)) := superpose step12 step13
  have step82 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose step10 step24
  have step109 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = X0 := superpose step27 step14
  have step138 (X0 : G) :  ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0))) = X0 := superpose step109 step15
  have step145 (X0 : G) :  ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = X0 := superpose step82 step138
  have step155 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step109 step145
  have step206 : sK0 ≠ sK0 := superpose step155 step11
  subsumption step206 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation2866_implies_Equation3 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation2866 G) : Equation3 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have step11 (X0 X1 : G) :  (((X0 ◇ (X1 ◇ X0)) ◇ X1) ◇ X1) = X0 := mod_symm (h ..)
  have step12 : sK0 ≠ (sK0 ◇ sK0) := mod_symm nh
  have step14 (X Y : G) : (((X ◇ Y) ◇ (Y ◇ (X ◇ Y))) ◇ Y) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => ((s ◇ (Y ◇ s)) ◇ Y)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (s ◇ Y)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (s ◇ Y)) (fun s => ((s ◇ (Y ◇ s)) ◇ Y)) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step15 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step16 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step21 (X0 X1 : G) :  ((X0 ◇ (X1 ◇ X0)) ◇ X1) = ((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1))) := superpose step14 step14
  have step28 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose step15 step16
  have step66 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose step28 step11
  have step77 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose step66 step15
  have step110 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0)))) := superpose step77 step15
  have step120 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) := superpose step21 step110
  have step124 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step16 step120
  have step166 : sK0 ≠ sK0 := superpose step124 step12
  subsumption step166 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation2910_implies_Equation3 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation2910 G) : Equation3 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have step10 (X0 X1 : G) :  (((X1 ◇ (X0 ◇ X1)) ◇ X0) ◇ X1) = X0 := mod_symm (h ..)
  have step11 : sK0 ≠ (sK0 ◇ sK0) := mod_symm nh
  have step12 (X Y : G) : ((Y ◇ ((X ◇ Y) ◇ Y)) ◇ (X ◇ Y)) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => ((Y ◇ (s ◇ Y)) ◇ s)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (s ◇ Y)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (s ◇ Y)) (fun s => ((Y ◇ (s ◇ Y)) ◇ s)) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step14 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step19 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) := superpose step10 step12
  have step20 (X0 X1 : G) :  (X1 ◇ ((X0 ◇ X1) ◇ X1)) = (((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) ◇ X0) := superpose step12 step12
  have step24 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = X0 := superpose step14 step19
  have step25 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = X0 := superpose step24 step10
  have step26 (X0 : G) :  (((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) = X0 := superpose step24 step12
  have step29 (X0 : G) :  (X0 ◇ ((X0 ◇ X0) ◇ X0)) = X0 := superpose step20 step26
  have step30 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step25 step29
  have step42 : sK0 ≠ sK0 := superpose step30 step11
  subsumption step42 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation2937_implies_Equation3 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation2937 G) : Equation3 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have step11 : sK0 ≠ (sK0 ◇ sK0) := mod_symm nh
  have step12 (X Y : G) : ((Y ◇ (Y ◇ (X ◇ Y))) ◇ (X ◇ Y)) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => ((Y ◇ (Y ◇ s)) ◇ s)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (s ◇ Y)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (s ◇ Y)) (fun s => ((Y ◇ (Y ◇ s)) ◇ s)) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step13 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step20 (X0 : G) :  (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose step13 step12
  have step21 (X0 X1 : G) :  (X1 ◇ (X1 ◇ (X0 ◇ X1))) = (((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X0)) ◇ X0) := superpose step12 step12
  have step25 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = X0 := superpose step20 step13
  have step45 (X0 : G) :  (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) = X0 := superpose step25 step12
  have step50 (X0 : G) :  (X0 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose step21 step45
  have step51 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step25 step50
  have step71 : sK0 ≠ sK0 := superpose step51 step11
  subsumption step71 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation3066_implies_Equation3 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation3066 G) : Equation3 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have step10 (X0 X1 : G) :  ((((X0 ◇ X1) ◇ X0) ◇ X0) ◇ X1) = X0 := mod_symm (h ..)
  have step11 : sK0 ≠ (sK0 ◇ sK0) := mod_symm nh
  have step13 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step14 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step18 (X0 X1 : G) :  (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X1 := superpose step13 step10
  have step20 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step14 step14
  have step37 (X0 : G) :  (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0))) = X0 := superpose step10 step18
  have step49 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = X0 := superpose step13 step37
  have step54 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = X0 := superpose step49 step18
  have step59 (X0 : G) :  (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0))) = X0 := superpose step49 step14
  have step62 (X0 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ X0) = X0 := superpose step20 step59
  have step64 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step54 step62
  have step91 : sK0 ≠ sK0 := superpose step64 step11
  subsumption step91 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation3076_implies_Equation3 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation3076 G) : Equation3 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have step10 (X0 X1 : G) :  ((((X0 ◇ X1) ◇ X1) ◇ X0) ◇ X1) = X0 := mod_symm (h ..)
  have step11 : sK0 ≠ (sK0 ◇ sK0) := mod_symm nh
  have step12 (X Y : G) : ((((X ◇ Y) ◇ Y) ◇ Y) ◇ (X ◇ Y)) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (((s ◇ Y) ◇ Y) ◇ s)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (s ◇ Y)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (s ◇ Y)) (fun s => (((s ◇ Y) ◇ Y) ◇ s)) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step13 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step14 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step21 (X0 : G) :  (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose step10 step12
  have step22 (X0 X1 : G) :  (((X0 ◇ X1) ◇ X1) ◇ X1) = (((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) ◇ X0) := superpose step12 step12
  have step26 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = X0 := superpose step21 step13
  have step34 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) := superpose step21 step14
  have step40 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = X0 := superpose step14 step34
  have step43 (X0 : G) :  (((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) ◇ X0) = X0 := superpose step26 step12
  have step48 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ X0) = X0 := superpose step22 step43
  have step49 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step40 step48
  have step67 : sK0 ≠ sK0 := superpose step49 step11
  subsumption step67 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation3079_implies_Equation3 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation3079 G) : Equation3 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have step9 (X0 X1 : G) :  ((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ X1) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ (sK0 ◇ sK0) := mod_symm nh
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step16 (X0 X1 : G) :  (X0 ◇ (((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ X0) ◇ (((X0 ◇ X1) ◇ X1) ◇ X1))) = X1 := superpose step9 step12
  have step17 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step82 (X0 : G) :  (X0 ◇ (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0))) = X0 := superpose step9 step16
  have step147 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0))) ◇ X0)) := superpose step82 step17
  have step149 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ X0) := superpose step12 step147
  have step207 (X0 : G) :  (X0 ◇ X0) = ((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ X0) := superpose step149 step9
  have step223 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step9 step207
  have step301 : sK0 ≠ sK0 := superpose step223 step10
  subsumption step301 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation3_implies_Equation1020 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation3 G) : Equation1020 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have step9 (X0 : G) :  (X0 ◇ X0) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0)) := mod_symm nh
  have step13 : sK0 ≠ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)) := superpose step9 step10
  have step14 : sK0 ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose step9 step13
  have step15 : sK0 ≠ (sK0 ◇ sK0) := superpose step9 step14
  subsumption step15 step9


@[equational_result]
theorem Finite.Equation677_and_Equation3103_implies_Equation3 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation3103 G) : Equation3 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have step10 (X0 X1 : G) :  ((((X1 ◇ X0) ◇ X0) ◇ X0) ◇ X1) = X0 := mod_symm (h ..)
  have step11 : sK0 ≠ (sK0 ◇ sK0) := mod_symm nh
  have step12 (X Y : G) : (((Y ◇ (X ◇ Y)) ◇ (X ◇ Y)) ◇ (X ◇ Y)) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (((Y ◇ s) ◇ s) ◇ s)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (s ◇ Y)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (s ◇ Y)) (fun s => (((Y ◇ s) ◇ s) ◇ s)) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step14 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step17 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = X0 := superpose step10 step10
  have step32 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose step17 step14
  have step41 (X0 : G) :  (X0 ◇ X0) = (((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := superpose step32 step10
  have step44 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step12 step41
  have step63 : sK0 ≠ sK0 := superpose step44 step11
  subsumption step63 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation3106_implies_Equation3 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation3106 G) : Equation3 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have step11 (X0 X1 : G) :  ((((X1 ◇ X0) ◇ X0) ◇ X1) ◇ X1) = X0 := mod_symm (h ..)
  have step12 : sK0 ≠ (sK0 ◇ sK0) := mod_symm nh
  have step13 (X Y : G) : ((Y ◇ ((X ◇ Y) ◇ Y)) ◇ ((X ◇ Y) ◇ Y)) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => ((Y ◇ s) ◇ s)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => ((s ◇ Y) ◇ Y)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => ((s ◇ Y) ◇ Y)) (fun s => ((Y ◇ s) ◇ s)) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step15 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step16 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step21 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ X0) ◇ X1)) = (((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) ◇ X1) ◇ X1) := superpose step15 step11
  have step28 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step16 step16
  have step244 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose step15 step21
  have step321 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) ◇ X0) := superpose step244 step21
  have step324 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) = X0 := superpose step244 step13
  have step341 (X0 : G) :  ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ ((((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0))) := superpose step244 step28
  have step342 (X0 : G) :  ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) = ((((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) := superpose step244 step341
  have step351 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ X0) := superpose step244 step321
  have step353 (X0 : G) :  (X0 ◇ ((X0 ◇ X0) ◇ X0)) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) := superpose step324 step342
  have step356 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = X0 := superpose step11 step351
  have step357 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ X0) := superpose step244 step353
  have step360 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step356 step357
  have step429 : sK0 ≠ sK0 := superpose step360 step12
  subsumption step429 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation3_implies_Equation1223 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation3 G) : Equation1223 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have step9 (X0 : G) :  (X0 ◇ X0) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ (sK0 ◇ (((sK0 ◇ sK0) ◇ sK0) ◇ sK0)) := mod_symm nh
  have step13 : sK0 ≠ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)) := superpose step9 step10
  have step14 : sK0 ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose step9 step13
  have step15 : sK0 ≠ (sK0 ◇ sK0) := superpose step9 step14
  subsumption step15 step9


@[equational_result]
theorem Finite.Equation677_and_Equation3_implies_Equation1426 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation3 G) : Equation1426 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have step9 (X0 : G) :  (X0 ◇ X0) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := mod_symm nh
  have step13 : sK0 ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose step9 step10
  have step14 : sK0 ≠ (sK0 ◇ sK0) := superpose step9 step13
  subsumption step14 step9


@[equational_result]
theorem Finite.Equation677_and_Equation3_implies_Equation255 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation3 G) : Equation255 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have step9 (X0 : G) :  (X0 ◇ X0) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ (((sK0 ◇ sK0) ◇ sK0) ◇ sK0) := mod_symm nh
  have step13 : sK0 ≠ ((sK0 ◇ sK0) ◇ sK0) := superpose step9 step10
  have step14 : sK0 ≠ (sK0 ◇ sK0) := superpose step9 step13
  subsumption step14 step9


@[equational_result]
theorem Finite.Equation677_and_Equation3343_implies_Equation3 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation3343 G) : Equation3 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ X1) = (X1 ◇ (X0 ◇ (X0 ◇ X1))) := mod_symm (h ..)
  have step10 : sK0 ≠ (sK0 ◇ sK0) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step18 (X0 X1 : G) :  ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X1 ◇ X0)) = X0 := superpose step11 step9
  have step22 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose step11 step12
  have step25 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = X0 := superpose step18 step22
  have step29 (X0 : G) :  (X0 ◇ ((X0 ◇ X0) ◇ X0)) = X0 := superpose step25 step9
  have step30 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step25 step29
  have step48 : sK0 ≠ sK0 := superpose step30 step10
  subsumption step48 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation3345_implies_Equation3 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation3345 G) : Equation3 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ X1) = (X1 ◇ (X0 ◇ (X1 ◇ X0))) := mod_symm (h ..)
  have step10 : sK0 ≠ (sK0 ◇ sK0) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step13 (X0 X1 : G) :  ((X0 ◇ (X1 ◇ X0)) ◇ X1) = (X1 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X1))) := superpose step9 step9
  have step17 (X0 X1 : G) :  (X0 ◇ (X1 ◇ X0)) = ((X0 ◇ X1) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X1)) := superpose step9 step12
  have step20 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose step11 step12
  have step33 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = X0 := superpose step17 step12
  have step45 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose step33 step9
  have step48 (X0 : G) :  ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) = (((X0 ◇ X0) ◇ X0) ◇ (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0))) := superpose step20 step17
  have step55 (X0 : G) :  ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) = X0 := superpose step12 step48
  have step56 (X0 : G) :  ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose step9 step55
  have step57 (X0 : G) :  ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) = X0 := superpose step33 step56
  have step58 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ X0) = X0 := superpose step45 step57
  have step59 (X0 : G) :  (X0 ◇ ((X0 ◇ X0) ◇ X0)) = (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) := superpose step58 step17
  have step66 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) := superpose step45 step59
  have step85 (X0 : G) :  ((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ X0) = (X0 ◇ ((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ X0)) := superpose step58 step13
  have step91 (X0 : G) :  ((((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) = (X0 ◇ ((((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0)) := superpose step45 step85
  have step99 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ X0) = (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) := superpose step66 step91
  have step107 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step58 step99
  have step124 : sK0 ≠ sK0 := superpose step107 step10
  subsumption step124 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation3355_implies_Equation474 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation3355 G) : Equation474 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ X1) = (X1 ◇ (X1 ◇ (X1 ◇ X0))) := mod_symm (h ..)
  have step10 : sK0 ≠ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step14 (X0 X1 : G) :  (X1 ◇ (X0 ◇ X1)) = ((X1 ◇ X0) ◇ X1) := superpose step9 step9
  have step45 (X0 X1 : G) :  (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0)))) = X1 := superpose step14 step11
  have step85 : sK0 ≠ sK0 := superpose step45 step10
  subsumption step85 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation3_implies_Equation3659 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation3 G) : Equation3659 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have step9 (X0 : G) :  (X0 ◇ X0) = X0 := mod_symm (h ..)
  have step10 : (sK0 ◇ sK0) ≠ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have step14 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose step9 step10
  subsumption step14 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation3_implies_Equation4065 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation3 G) : Equation4065 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have step9 (X0 : G) :  (X0 ◇ X0) = X0 := mod_symm (h ..)
  have step10 : (sK0 ◇ sK0) ≠ (((sK0 ◇ sK0) ◇ sK0) ◇ sK0) := mod_symm nh
  have step13 : sK0 ≠ ((sK0 ◇ sK0) ◇ sK0) := superpose step9 step10
  have step14 : sK0 ≠ (sK0 ◇ sK0) := superpose step9 step13
  subsumption step14 step9


@[equational_result]
theorem Finite.Equation677_and_Equation3_implies_Equation411 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation3 G) : Equation411 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have step9 (X0 : G) :  (X0 ◇ X0) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := mod_symm nh
  have step13 : sK0 ≠ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := superpose step9 step10
  have step14 : sK0 ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose step9 step13
  have step15 : sK0 ≠ (sK0 ◇ sK0) := superpose step9 step14
  subsumption step15 step9


@[equational_result]
theorem Finite.Equation677_and_Equation3555_implies_Equation3 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation3555 G) : Equation3 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ X1) = (X1 ◇ ((X1 ◇ X0) ◇ X0)) := mod_symm (h ..)
  have step10 : sK0 ≠ (sK0 ◇ sK0) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step20 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose step11 step12
  have step23 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose step9 step20
  have step31 (X0 : G) :  (X0 ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0))) := superpose step23 step12
  have step38 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step12 step31
  have step42 : sK0 ≠ sK0 := superpose step38 step10
  subsumption step42 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation3556_implies_Equation3 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation3556 G) : Equation3 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ X1) = (X1 ◇ ((X1 ◇ X0) ◇ X1)) := mod_symm (h ..)
  have step10 : sK0 ≠ (sK0 ◇ sK0) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step20 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose step11 step12
  have step23 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose step9 step20
  have step31 (X0 : G) :  (X0 ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0))) := superpose step23 step12
  have step38 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step12 step31
  have step46 : sK0 ≠ sK0 := superpose step38 step10
  subsumption step46 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation3724_implies_Equation255 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation3724 G) : Equation255 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ X1) = ((X0 ◇ X1) ◇ (X1 ◇ X0)) := mod_symm (h ..)
  have step10 : sK0 ≠ (((sK0 ◇ sK0) ◇ sK0) ◇ sK0) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step20 (X0 X1 : G) :  (X0 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X1)) = X0 := superpose step11 step9
  have step21 (X0 X1 : G) :  (X1 ◇ X0) = ((X0 ◇ X1) ◇ (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1))) := superpose step9 step12
  have step32 (X0 X1 : G) :  ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X1) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose step20 step12
  have step151 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) := superpose step32 step21
  have step171 (X0 X1 : G) :  (((X0 ◇ X0) ◇ X0) ◇ X0) = (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) := superpose step21 step151
  have step181 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ X0) = X0 := superpose step11 step171
  have step194 : sK0 ≠ sK0 := superpose step181 step10
  subsumption step194 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation3724_implies_Equation3659 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation3724 G) : Equation3659 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ X1) = ((X0 ◇ X1) ◇ (X1 ◇ X0)) := mod_symm (h ..)
  have step10 : (sK0 ◇ sK0) ≠ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have step15 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose step9 step10
  subsumption step15 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation3_implies_Equation817 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation3 G) : Equation817 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have step9 (X0 : G) :  (X0 ◇ X0) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := mod_symm nh
  have step14 : sK0 ≠ (sK0 ◇ (sK0 ◇ sK0)) := superpose step9 step10
  have step15 : sK0 ≠ (sK0 ◇ sK0) := superpose step9 step14
  subsumption step15 step9


@[equational_result]
theorem Finite.Equation677_and_Equation384_implies_Equation474 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation384 G) : Equation474 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ X1) = ((X1 ◇ X0) ◇ X0) := mod_symm (h ..)
  have step10 : sK0 ≠ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step13 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X0) = (X0 ◇ (X1 ◇ X0)) := superpose step9 step9
  have step51 (X0 X1 : G) :  (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0)))) = X1 := superpose step13 step11
  have step230 : sK0 ≠ sK0 := superpose step51 step10
  subsumption step230 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation3924_implies_Equation3 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation3924 G) : Equation3 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ X1) = ((X0 ◇ (X1 ◇ X0)) ◇ X0) := mod_symm (h ..)
  have step10 : sK0 ≠ (sK0 ◇ sK0) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step13 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ X1)) ◇ X0) = (X0 ◇ (X0 ◇ (X1 ◇ X0))) := superpose step9 step9
  have step20 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose step11 step12
  have step21 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose step9 step12
  have step64 (X0 : G) :  (X0 ◇ X0) = (X0 ◇ (X0 ◇ (X0 ◇ X0))) := superpose step13 step9
  have step78 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) := superpose step64 step13
  have step83 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) := superpose step64 step12
  have step87 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = X0 := superpose step12 step83
  have step91 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = X0 := superpose step11 step78
  have step92 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = (((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) := superpose step21 step20
  have step105 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ X0) = X0 := superpose step87 step92
  have step111 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step91 step105
  have step115 : sK0 ≠ sK0 := superpose step111 step10
  subsumption step115 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation3925_implies_Equation3 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation3925 G) : Equation3 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ X1) = ((X0 ◇ (X1 ◇ X0)) ◇ X1) := mod_symm (h ..)
  have step10 : sK0 ≠ (sK0 ◇ sK0) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step13 (X0 X1 : G) :  (X1 ◇ (X0 ◇ (X1 ◇ X0))) = ((X1 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X0))) := superpose step9 step9
  have step20 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose step11 step12
  have step21 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose step9 step12
  have step24 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ X0) := superpose step9 step20
  have step27 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose step21 step9
  have step28 (X0 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) = X0 := superpose step24 step27
  have step31 (X0 : G) :  (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) = X0 := superpose step24 step11
  have step39 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) = (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) := superpose step28 step9
  have step40 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) = ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) := superpose step24 step39
  have step43 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) = (X0 ◇ (X0 ◇ (X0 ◇ X0))) := superpose step13 step40
  have step65 (X0 : G) :  (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0)))) = ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0)))) := superpose step24 step13
  have step85 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) := superpose step13 step21
  have step95 (X0 : G) :  (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) = ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) := superpose step43 step65
  have step104 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) := superpose step85 step95
  have step110 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = X0 := superpose step31 step104
  have step122 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ X0) := superpose step110 step9
  have step123 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose step24 step122
  have step128 (X0 : G) :  (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose step9 step123
  have step131 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step110 step128
  have step199 : sK0 ≠ sK0 := superpose step131 step10
  subsumption step199 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation3961_implies_Equation3 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation3961 G) : Equation3 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ X1) = ((X1 ◇ (X1 ◇ X0)) ◇ X0) := mod_symm (h ..)
  have step10 : sK0 ≠ (sK0 ◇ sK0) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step17 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose step11 step9
  have step21 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose step11 step12
  have step22 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose step9 step12
  have step27 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose step22 step9
  have step40 (X0 : G) :  ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) = ((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) := superpose step27 step9
  have step41 (X0 : G) :  ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) := superpose step17 step40
  have step44 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) := superpose step21 step41
  have step50 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0))) = X0 := superpose step44 step12
  have step52 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0))) := superpose step44 step12
  have step57 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = X0 := superpose step12 step52
  have step58 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ X0) = X0 := superpose step27 step50
  have step61 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step57 step58
  have step74 : sK0 ≠ sK0 := superpose step61 step10
  subsumption step74 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation40_implies_Equation255 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation40 G) : Equation255 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ X0) = (X1 ◇ X1) := mod_symm (h ..)
  have step10 : sK0 ≠ (((sK0 ◇ sK0) ◇ sK0) ◇ sK0) := mod_symm nh
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step18 (X0 : G) :  sK0 ≠ (((X0 ◇ X0) ◇ sK0) ◇ sK0) := superpose step9 step10
  have step32 (X0 X1 : G) :  ((X0 ◇ X0) ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X1)) = X1 := superpose step9 step12
  have step34 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step63 (X0 X1 : G) :  (X0 ◇ (X1 ◇ X1)) = ((X0 ◇ (X0 ◇ (X1 ◇ X1))) ◇ X0) := superpose step34 step32
  have step878 (X0 X1 : G) :  ((X0 ◇ (X1 ◇ X1)) ◇ (((X0 ◇ (X0 ◇ (X1 ◇ X1))) ◇ (X0 ◇ (X1 ◇ X1))) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1))))) = X0 := superpose step63 step12
  have step884 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1)))) ◇ X0) = X0 := superpose step34 step878
  have step1054 (X0 X1 : G) :  (X0 ◇ (((X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1)))) ◇ X0) ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1)))))) = X0 := superpose step884 step12
  have step1062 (X0 X1 : G) :  (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1)))))) = X0 := superpose step884 step1054
  have step1735 (X0 X1 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1))))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1)))))) ◇ X0)) := superpose step1062 step34
  have step1755 (X0 X1 : G) :  ((X0 ◇ X0) ◇ X0) = (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1)))) := superpose step12 step1735
  have step2762 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ X0) = X0 := superpose step1755 step884
  have step2949 : sK0 ≠ sK0 := superpose step2762 step18
  subsumption step2949 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation40_implies_Equation3659 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation40 G) : Equation3659 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ X0) = (X1 ◇ X1) := mod_symm (h ..)
  have step10 : (sK0 ◇ sK0) ≠ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have step20 (X0 : G) :  (X0 ◇ X0) ≠ (sK0 ◇ sK0) := superpose step9 step10
  subsumption step20 step9


@[equational_result]
theorem Finite.Equation677_and_Equation4073_implies_Equation4065 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation4073 G) : Equation4065 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ X0) = (((X0 ◇ X1) ◇ X1) ◇ X0) := mod_symm (h ..)
  have step10 : (sK0 ◇ sK0) ≠ (((sK0 ◇ sK0) ◇ sK0) ◇ sK0) := mod_symm nh
  have step14 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose step9 step10
  subsumption step14 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation4093_implies_Equation4065 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation4093 G) : Equation4065 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ X0) = (((X1 ◇ X1) ◇ X1) ◇ X0) := mod_symm (h ..)
  have step10 : (sK0 ◇ sK0) ≠ (((sK0 ◇ sK0) ◇ sK0) ◇ sK0) := mod_symm nh
  have step15 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose step9 step10
  subsumption step15 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation4093_implies_Equation623 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation4093 G) : Equation623 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ X0) = (((X1 ◇ X1) ◇ X1) ◇ X0) := mod_symm (h ..)
  have step10 : sK0 ≠ (sK0 ◇ (sK0 ◇ ((sK1 ◇ sK1) ◇ sK1))) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step13 (X0 X1 X2 : G) :  (((X0 ◇ X0) ◇ X0) ◇ X1) = (((X2 ◇ X2) ◇ X2) ◇ X1) := superpose step9 step9
  have step20 (X0 X1 : G) :  ((X0 ◇ X0) ◇ ((((X1 ◇ X1) ◇ X1) ◇ (X0 ◇ X0)) ◇ ((X1 ◇ X1) ◇ X1))) = X0 := superpose step9 step12
  have step21 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step58 (X0 X1 : G) :  (((X0 ◇ X0) ◇ X0) ◇ (((X1 ◇ X1) ◇ ((X1 ◇ X1) ◇ X1)) ◇ (X1 ◇ X1))) = X1 := superpose step13 step12
  have step59 (X0 X1 X2 : G) :  ((X2 ◇ X2) ◇ X2) = (X1 ◇ (((X0 ◇ X0) ◇ X0) ◇ ((X1 ◇ ((X2 ◇ X2) ◇ X2)) ◇ X1))) := superpose step13 step11
  have step562 (X0 X1 : G) :  ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X1 ◇ X1) ◇ X1))) = X0 := superpose step9 step20
  have step1176 (X0 X1 : G) :  (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0))) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X1 ◇ X1) ◇ X1)) := superpose step562 step12
  have step1178 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X1 ◇ X1) ◇ X1)) := superpose step21 step1176
  have step2311 (X0 X1 : G) :  (X0 ◇ X0) = (((X1 ◇ X1) ◇ X1) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) := superpose step1178 step58
  have step2371 (X0 X1 X2 : G) :  ((X1 ◇ X1) ◇ X1) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (((X2 ◇ X2) ◇ X2) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))))) := superpose step1178 step59
  have step2462 (X0 X1 : G) :  ((X1 ◇ X1) ◇ X1) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := superpose step2311 step2371
  have step2499 (X0 X1 : G) :  ((X1 ◇ X1) ◇ X1) = ((X0 ◇ X0) ◇ X0) := superpose step2462 step2462
  have step2950 (X0 : G) :  sK0 ≠ (sK0 ◇ (sK0 ◇ ((X0 ◇ X0) ◇ X0))) := superpose step2499 step10
  have step3503 : sK0 ≠ sK0 := superpose step11 step2950
  subsumption step3503 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation4131_implies_Equation4065 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation4131 G) : Equation4065 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ X1) = (((X0 ◇ X1) ◇ X1) ◇ X1) := mod_symm (h ..)
  have step10 : (sK0 ◇ sK0) ≠ (((sK0 ◇ sK0) ◇ sK0) ◇ sK0) := mod_symm nh
  have step14 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose step9 step10
  subsumption step14 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation4154_implies_Equation474 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation4154 G) : Equation474 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ X1) = (((X1 ◇ X0) ◇ X0) ◇ X0) := mod_symm (h ..)
  have step10 : sK0 ≠ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step14 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X0) = (X0 ◇ (X1 ◇ X0)) := superpose step9 step9
  have step40 (X0 X1 : G) :  (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0)))) = X1 := superpose step14 step11
  have step326 : sK0 ≠ sK0 := superpose step40 step10
  subsumption step326 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation4155_implies_Equation3 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation4155 G) : Equation3 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ X1) = (((X1 ◇ X0) ◇ X0) ◇ X1) := mod_symm (h ..)
  have step10 : sK0 ≠ (sK0 ◇ sK0) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step17 (X0 X1 : G) :  ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X1) = ((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) ◇ X1) := superpose step11 step9
  have step19 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step20 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose step11 step12
  have step28 (X0 : G) :  (X0 ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) := superpose step20 step12
  have step31 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ X0) := superpose step19 step28
  have step32 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) := superpose step17 step31
  have step35 (X0 : G) :  ((X0 ◇ X0) ◇ (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) = X0 := superpose step32 step12
  have step37 (X0 : G) :  (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) = (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) := superpose step32 step9
  have step38 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) = X0 := superpose step11 step37
  have step39 (X0 : G) :  ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) = X0 := superpose step20 step35
  have step41 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = X0 := superpose step38 step39
  have step82 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose step41 step32
  have step91 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step41 step82
  have step149 : sK0 ≠ sK0 := superpose step91 step10
  subsumption step149 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation4157_implies_Equation3 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation4157 G) : Equation3 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ X1) = (((X1 ◇ X0) ◇ X1) ◇ X0) := mod_symm (h ..)
  have step10 : sK0 ≠ (sK0 ◇ sK0) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step13 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ X0) ◇ X1)) = (((X0 ◇ X1) ◇ ((X1 ◇ X0) ◇ X1)) ◇ X0) := superpose step9 step9
  have step16 (X0 X1 : G) :  ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) := superpose step11 step9
  have step17 (X0 X1 : G) :  ((X0 ◇ X1) ◇ ((((X1 ◇ X0) ◇ X1) ◇ (X0 ◇ X1)) ◇ ((X1 ◇ X0) ◇ X1))) = X0 := superpose step9 step12
  have step18 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step19 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose step11 step12
  have step21 (X0 X1 : G) :  (((X1 ◇ (X1 ◇ X0)) ◇ X1) ◇ (X1 ◇ X0)) = ((X0 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) := superpose step12 step9
  have step22 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X1) = ((X0 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) := superpose step9 step21
  have step69 (X0 : G) :  (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) = ((X0 ◇ X0) ◇ ((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0))) := superpose step19 step18
  have step103 (X0 : G) :  (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) = X0 := superpose step17 step69
  have step106 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) = (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) := superpose step19 step22
  have step130 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) = (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) := superpose step103 step106
  have step133 (X0 : G) :  (X0 ◇ ((X0 ◇ X0) ◇ X0)) = (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) := superpose step13 step130
  have step239 (X0 : G) :  (X0 ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ (((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X0 ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))))) := superpose step19 step17
  have step277 (X0 : G) :  (X0 ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) := superpose step133 step239
  have step283 (X0 : G) :  (X0 ◇ X0) = (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) ◇ (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) := superpose step16 step277
  have step284 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step12 step283
  have step285 : sK0 ≠ sK0 := superpose step284 step10
  subsumption step285 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation4158_implies_Equation3 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation4158 G) : Equation3 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ X1) = (((X1 ◇ X0) ◇ X1) ◇ X1) := mod_symm (h ..)
  have step10 : sK0 ≠ (sK0 ◇ sK0) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step16 (X0 X1 : G) :  ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X1) = ((X0 ◇ X1) ◇ X1) := superpose step11 step9
  have step19 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose step11 step12
  have step29 (X0 X1 : G) :  (((X0 ◇ X1) ◇ X1) ◇ (((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1)))) = X1 := superpose step16 step12
  have step37 (X0 : G) :  (X0 ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) := superpose step19 step12
  have step41 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step29 step37
  have step42 : sK0 ≠ sK0 := superpose step41 step10
  subsumption step42 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation4273_implies_Equation255 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation4273 G) : Equation255 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X0 ◇ X1)) := mod_symm (h ..)
  have step10 : sK0 ≠ (((sK0 ◇ sK0) ◇ sK0) ◇ sK0) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step13 (X0 X1 X2 : G) :  (X0 ◇ (X1 ◇ X0)) = (X2 ◇ (X1 ◇ X2)) := superpose step9 step9
  have step23 (X0 X1 : G) :  ((X1 ◇ X1) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X1)) = X1 := superpose step9 step12
  have step24 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose step11 step12
  have step56 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X1) ◇ X0))) = X1 := superpose step13 step11
  have step80 (X0 X1 : G) :  (X0 ◇ (((X1 ◇ (X0 ◇ X1)) ◇ X0) ◇ X0)) = X0 := superpose step23 step56
  have step152 (X0 X1 X2 : G) :  (X2 ◇ (((X1 ◇ (X0 ◇ X1)) ◇ X0) ◇ X2)) = X0 := superpose step80 step13
  have step296 (X0 X1 X2 : G) :  (X0 ◇ ((X1 ◇ X0) ◇ X1)) = (((X2 ◇ (X0 ◇ X2)) ◇ X0) ◇ X1) := superpose step152 step12
  have step1051 (X0 X1 : G) :  ((X1 ◇ X1) ◇ X1) = ((X0 ◇ ((X1 ◇ X1) ◇ X0)) ◇ (X1 ◇ X1)) := superpose step13 step24
  have step37479 (X0 X1 : G) :  (((X0 ◇ ((X1 ◇ X1) ◇ X0)) ◇ (X1 ◇ X1)) ◇ X1) = X1 := superpose step296 step23
  have step37918 (X1 : G) :  (((X1 ◇ X1) ◇ X1) ◇ X1) = X1 := superpose step1051 step37479
  have step39213 : sK0 ≠ sK0 := superpose step37918 step10
  subsumption step39213 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation4273_implies_Equation630 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation4273 G) : Equation630 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X0 ◇ X1)) := mod_symm (h ..)
  have step10 : sK0 ≠ (sK0 ◇ (sK1 ◇ ((sK0 ◇ sK0) ◇ sK1))) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step13 (X0 X1 X2 : G) :  (X0 ◇ (X1 ◇ X0)) = (X2 ◇ (X1 ◇ X2)) := superpose step9 step9
  have step62 (X0 : G) :  sK0 ≠ (sK0 ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ X0))) := superpose step13 step10
  have step92 : sK0 ≠ sK0 := superpose step11 step62
  subsumption step92 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation43_implies_Equation1112 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation43 G) : Equation1112 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ X1) = (X1 ◇ X0) := mod_symm (h ..)
  have step10 : sK0 ≠ (sK1 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ sK0)) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step14 : sK0 ≠ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := superpose step9 step10
  have step16 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X1))) = X0 := superpose step9 step11
  have step21 (X0 X1 : G) :  (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) = X0 := superpose step9 step16
  have step82 : sK0 ≠ sK0 := superpose step21 step14
  subsumption step82 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation43_implies_Equation1119 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation43 G) : Equation1119 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ X1) = (X1 ◇ X0) := mod_symm (h ..)
  have step10 : sK0 ≠ (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK0)) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step16 : sK0 ≠ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := superpose step9 step10
  have step17 : sK0 ≠ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := superpose step9 step16
  have step22 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X1))) = X0 := superpose step9 step11
  have step27 (X0 X1 : G) :  (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) = X0 := superpose step9 step22
  have step88 : sK0 ≠ sK0 := superpose step27 step17
  subsumption step88 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation43_implies_Equation1288 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation43 G) : Equation1288 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ X1) = (X1 ◇ X0) := mod_symm (h ..)
  have step10 : sK0 ≠ (sK1 ◇ (((sK0 ◇ sK1) ◇ sK1) ◇ sK0)) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step16 : sK0 ≠ (sK1 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ sK0)) := superpose step9 step10
  have step17 : sK0 ≠ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := superpose step9 step16
  have step22 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X1))) = X0 := superpose step9 step11
  have step27 (X0 X1 : G) :  (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) = X0 := superpose step9 step22
  have step85 : sK0 ≠ sK0 := superpose step27 step17
  subsumption step85 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation43_implies_Equation1315 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation43 G) : Equation1315 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ X1) = (X1 ◇ X0) := mod_symm (h ..)
  have step10 : sK0 ≠ (sK1 ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK0)) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step18 : sK0 ≠ (sK1 ◇ (sK0 ◇ ((sK1 ◇ sK0) ◇ sK1))) := superpose step9 step10
  subsumption step18 step11


@[equational_result]
theorem Finite.Equation677_and_Equation4320_implies_Equation1426 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation4320 G) : Equation1426 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ (X1 ◇ X0)) = (X1 ◇ (X0 ◇ X0)) := mod_symm (h ..)
  have step10 : sK0 ≠ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step16 : sK0 ≠ (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := superpose step9 step10
  have step17 : sK0 ≠ (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0))) := superpose step9 step16
  subsumption step17 step11


@[equational_result]
theorem Finite.Equation677_and_Equation4320_implies_Equation255 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation4320 G) : Equation255 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ (X1 ◇ X0)) = (X1 ◇ (X0 ◇ X0)) := mod_symm (h ..)
  have step10 : sK0 ≠ (((sK0 ◇ sK0) ◇ sK0) ◇ sK0) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step14 (X0 X1 : G) :  (X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = ((X0 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) := superpose step9 step9
  have step15 (X0 X1 : G) :  ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0))) = (X1 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) := superpose step9 step9
  have step16 (X0 X1 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) = (X1 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) := superpose step9 step14
  have step18 (X0 X1 : G) :  (X0 ◇ X0) = (X1 ◇ ((X0 ◇ X0) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X1))) := superpose step9 step11
  have step24 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step25 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose step11 step12
  have step26 (X0 X1 : G) :  (((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) ◇ X0))) = X1 := superpose step9 step12
  have step29 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = (X0 ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0)) := superpose step9 step25
  have step339 (X0 X1 : G) :  ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0))) = ((X0 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) := superpose step16 step15
  have step593 (X0 X1 : G) :  ((X1 ◇ (X0 ◇ X0)) ◇ X1) = (((X0 ◇ X0) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X1)) ◇ (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X1))) ◇ (X0 ◇ X0))) := superpose step18 step24
  have step644 (X0 X1 : G) :  ((X1 ◇ (X0 ◇ X0)) ◇ X1) = ((X0 ◇ (X1 ◇ X0)) ◇ X1) := superpose step12 step593
  have step722 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ ((X0 ◇ X0) ◇ X1)) ◇ X0)) = (((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ (X0 ◇ X0)) := superpose step644 step9
  have step727 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ ((X0 ◇ X0) ◇ X1)) ◇ X0)) = (X0 ◇ (((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ X0)) := superpose step9 step722
  have step1118 (X0 : G) :  (((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0)) = ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) ◇ (X0 ◇ (((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) ◇ X0))) := superpose step29 step26
  have step1153 (X0 : G) :  (((X0 ◇ X0) ◇ (X0 ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0))) ◇ (X0 ◇ X0)) = ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) ◇ (X0 ◇ (((X0 ◇ X0) ◇ (X0 ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0))) ◇ X0))) := superpose step339 step1118
  have step1172 (X0 : G) :  (((X0 ◇ X0) ◇ (X0 ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0))) ◇ (X0 ◇ X0)) = ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) ◇ (X0 ◇ (((X0 ◇ X0) ◇ (X0 ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0))) ◇ X0))) := superpose step727 step1153
  have step1184 (X0 : G) :  (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) = ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) ◇ (X0 ◇ (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0))) := superpose step29 step1172
  have step1193 (X0 : G) :  (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) = (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) ◇ (X0 ◇ (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0))) := superpose step644 step1184
  have step1197 (X0 : G) :  (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) = ((X0 ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0)) ◇ (X0 ◇ (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0))) := superpose step9 step1193
  have step1200 (X0 : G) :  (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) = (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0))) := superpose step29 step1197
  have step1202 (X0 : G) :  (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) = X0 := superpose step26 step1200
  have step1203 (X0 : G) :  (X0 ◇ (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0)) = X0 := superpose step9 step1202
  have step1214 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ X0) = X0 := superpose step1203 step26
  have step1460 : sK0 ≠ sK0 := superpose step1214 step10
  subsumption step1460 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation4320_implies_Equation817 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation4320 G) : Equation817 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ (X1 ◇ X0)) = (X1 ◇ (X0 ◇ X0)) := mod_symm (h ..)
  have step10 : sK0 ≠ (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step16 : sK0 ≠ (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0))) := superpose step9 step10
  subsumption step16 step11


@[equational_result]
theorem Finite.Equation677_and_Equation43_implies_Equation2257 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation43 G) : Equation2257 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ X1) = (X1 ◇ X0) := mod_symm (h ..)
  have step10 : sK0 ≠ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ sK1) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step14 : sK0 ≠ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := superpose step9 step10
  have step16 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X1))) = X0 := superpose step9 step11
  have step21 (X0 X1 : G) :  (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) = X0 := superpose step9 step16
  have step82 : sK0 ≠ sK0 := superpose step21 step14
  subsumption step82 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation43_implies_Equation2264 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation43 G) : Equation2264 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ X1) = (X1 ◇ X0) := mod_symm (h ..)
  have step10 : sK0 ≠ ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ sK1) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step16 : sK0 ≠ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ sK1) := superpose step9 step10
  have step17 : sK0 ≠ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := superpose step9 step16
  have step22 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X1))) = X0 := superpose step9 step11
  have step27 (X0 X1 : G) :  (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) = X0 := superpose step9 step22
  have step88 : sK0 ≠ sK0 := superpose step27 step17
  subsumption step88 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation43_implies_Equation2450 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation43 G) : Equation2450 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ X1) = (X1 ◇ X0) := mod_symm (h ..)
  have step10 : sK0 ≠ ((sK0 ◇ ((sK0 ◇ sK1) ◇ sK1)) ◇ sK1) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step16 : sK0 ≠ (sK1 ◇ (sK0 ◇ ((sK0 ◇ sK1) ◇ sK1))) := superpose step9 step10
  have step17 : sK0 ≠ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := superpose step9 step16
  have step22 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X1))) = X0 := superpose step9 step11
  have step27 (X0 X1 : G) :  (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) = X0 := superpose step9 step22
  have step83 : sK0 ≠ sK0 := superpose step27 step17
  subsumption step83 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation43_implies_Equation2910 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation43 G) : Equation2910 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ X1) = (X1 ◇ X0) := mod_symm (h ..)
  have step10 : sK0 ≠ (((sK1 ◇ (sK0 ◇ sK1)) ◇ sK0) ◇ sK1) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step16 : sK0 ≠ (sK1 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ sK0)) := superpose step9 step10
  have step17 : sK0 ≠ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := superpose step9 step16
  have step22 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X1))) = X0 := superpose step9 step11
  have step27 (X0 X1 : G) :  (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) = X0 := superpose step9 step22
  have step88 : sK0 ≠ sK0 := superpose step27 step17
  subsumption step88 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation43_implies_Equation2937 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation43 G) : Equation2937 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ X1) = (X1 ◇ X0) := mod_symm (h ..)
  have step10 : sK0 ≠ (((sK1 ◇ (sK1 ◇ sK0)) ◇ sK0) ◇ sK1) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step18 : sK0 ≠ (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK0)) := superpose step9 step10
  have step19 : sK0 ≠ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := superpose step9 step18
  have step25 : sK0 ≠ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := superpose step9 step19
  have step32 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X1))) = X0 := superpose step9 step11
  have step37 (X0 X1 : G) :  (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) = X0 := superpose step9 step32
  have step98 : sK0 ≠ sK0 := superpose step37 step25
  subsumption step98 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation43_implies_Equation3076 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation43 G) : Equation3076 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ X1) = (X1 ◇ X0) := mod_symm (h ..)
  have step10 : sK0 ≠ ((((sK0 ◇ sK1) ◇ sK1) ◇ sK0) ◇ sK1) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step18 : sK0 ≠ ((sK0 ◇ ((sK0 ◇ sK1) ◇ sK1)) ◇ sK1) := superpose step9 step10
  have step19 : sK0 ≠ (sK1 ◇ (sK0 ◇ ((sK0 ◇ sK1) ◇ sK1))) := superpose step9 step18
  have step25 : sK0 ≠ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := superpose step9 step19
  have step32 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X1))) = X0 := superpose step9 step11
  have step37 (X0 X1 : G) :  (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) = X0 := superpose step9 step32
  have step95 : sK0 ≠ sK0 := superpose step37 step25
  subsumption step95 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation43_implies_Equation3724 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation43 G) : Equation3724 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ X1) = (X1 ◇ X0) := mod_symm (h ..)
  have step10 : (sK0 ◇ sK1) ≠ ((sK0 ◇ sK1) ◇ (sK1 ◇ sK0)) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step14 : (sK0 ◇ sK1) ≠ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) := superpose step9 step10
  have step19 (X0 X1 : G) :  (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1)))) = X1 := superpose step9 step11
  have step29 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) := superpose step19 step19
  have step32 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) := superpose step9 step29
  have step36 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = X0 := superpose step19 step32
  have step63 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose step36 step12
  have step100 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose step63 step36
  have step101 (X0 : G) :  (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose step9 step100
  have step106 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step36 step101
  have step168 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose step106 step14
  subsumption step168 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation43_implies_Equation4343 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation43 G) : Equation4343 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ X1) = (X1 ◇ X0) := mod_symm (h ..)
  have step10 : (sK0 ◇ (sK1 ◇ sK1)) ≠ (sK1 ◇ (sK0 ◇ sK0)) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step25 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose step11 step12
  have step27 (X0 X1 : G) :  ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) = X1 := superpose step9 step12
  have step30 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) := superpose step9 step25
  have step34 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) := superpose step9 step30
  have step36 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = X0 := superpose step27 step34
  have step38 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose step36 step12
  have step70 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose step38 step36
  have step71 (X0 : G) :  (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose step9 step70
  have step75 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step36 step71
  have step129 : (sK0 ◇ (sK1 ◇ sK1)) ≠ (sK1 ◇ sK0) := superpose step75 step10
  have step130 : (sK0 ◇ (sK1 ◇ sK1)) ≠ (sK0 ◇ sK1) := superpose step9 step129
  have step135 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose step75 step130
  subsumption step135 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation43_implies_Equation4405 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation43 G) : Equation4405 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ X1) = (X1 ◇ X0) := mod_symm (h ..)
  have step10 : (sK0 ◇ (sK0 ◇ sK1)) ≠ ((sK1 ◇ sK0) ◇ sK0) := mod_symm nh
  have step16 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ (sK1 ◇ sK0)) := superpose step9 step10
  have step17 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ (sK0 ◇ sK1)) := superpose step9 step16
  subsumption step17 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation43_implies_Equation4442 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation43 G) : Equation4442 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ X1) = (X1 ◇ X0) := mod_symm (h ..)
  have step10 : (sK0 ◇ (sK1 ◇ sK0)) ≠ ((sK1 ◇ sK0) ◇ sK0) := mod_symm nh
  have step16 : (sK0 ◇ (sK1 ◇ sK0)) ≠ (sK0 ◇ (sK1 ◇ sK0)) := superpose step9 step10
  subsumption step16 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation43_implies_Equation4608 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation43 G) : Equation4608 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ X1) = (X1 ◇ X0) := mod_symm (h ..)
  have step10 : ((sK0 ◇ sK0) ◇ sK1) ≠ ((sK1 ◇ sK1) ◇ sK0) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step14 : ((sK0 ◇ sK0) ◇ sK1) ≠ (sK0 ◇ (sK1 ◇ sK1)) := superpose step9 step10
  have step15 : (sK0 ◇ (sK1 ◇ sK1)) ≠ (sK1 ◇ (sK0 ◇ sK0)) := superpose step9 step14
  have step21 (X0 X1 : G) :  (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1)))) = X1 := superpose step9 step11
  have step31 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) := superpose step21 step21
  have step34 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) := superpose step9 step31
  have step38 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = X0 := superpose step21 step34
  have step65 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose step38 step12
  have step102 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose step65 step38
  have step103 (X0 : G) :  (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose step9 step102
  have step108 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step38 step103
  have step171 : (sK0 ◇ (sK1 ◇ sK1)) ≠ (sK1 ◇ sK0) := superpose step108 step15
  have step174 : (sK0 ◇ (sK1 ◇ sK1)) ≠ (sK0 ◇ sK1) := superpose step9 step171
  have step181 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose step108 step174
  subsumption step181 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation43_implies_Equation474 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation43 G) : Equation474 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ X1) = (X1 ◇ X0) := mod_symm (h ..)
  have step10 : sK0 ≠ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step14 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X1))) = X0 := superpose step9 step11
  have step19 (X0 X1 : G) :  (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) = X0 := superpose step9 step14
  have step101 : sK0 ≠ sK0 := superpose step19 step10
  subsumption step101 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation4362_implies_Equation1482 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation4362 G) : Equation1482 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 X2 : G) :  (X0 ◇ (X1 ◇ X2)) = (X1 ◇ (X0 ◇ X2)) := mod_symm (h ..)
  have step10 : sK0 ≠ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK1))) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step18 : sK0 ≠ (sK0 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK1))) := superpose step9 step10
  have step19 : sK0 ≠ (sK0 ◇ (sK1 ◇ ((sK1 ◇ sK0) ◇ sK1))) := superpose step9 step18
  have step29 (X0 X1 : G) :  (X0 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := superpose step11 step9
  have step48 : sK0 ≠ sK0 := superpose step29 step19
  subsumption step48 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation4362_implies_Equation1489 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation4362 G) : Equation1489 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 X2 : G) :  (X0 ◇ (X1 ◇ X2)) = (X1 ◇ (X0 ◇ X2)) := mod_symm (h ..)
  have step10 : sK0 ≠ ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ sK1))) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step19 : sK0 ≠ (sK1 ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ sK1))) := superpose step9 step10
  have step22 : sK0 ≠ (sK1 ◇ (sK0 ◇ ((sK1 ◇ sK0) ◇ sK1))) := superpose step9 step19
  subsumption step22 step11


@[equational_result]
theorem Finite.Equation677_and_Equation4362_implies_Equation1516 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation4362 G) : Equation1516 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 X2 : G) :  (X0 ◇ (X1 ◇ X2)) = (X1 ◇ (X0 ◇ X2)) := mod_symm (h ..)
  have step10 : sK0 ≠ ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step16 (X0 X1 X2 X3 : G) :  (X1 ◇ (X3 ◇ (X0 ◇ X2))) = (X3 ◇ (X0 ◇ (X1 ◇ X2))) := superpose step9 step9
  have step18 : sK0 ≠ (sK0 ◇ ((sK1 ◇ sK1) ◇ (sK0 ◇ sK1))) := superpose step9 step10
  have step19 : sK0 ≠ (sK0 ◇ (sK0 ◇ ((sK1 ◇ sK1) ◇ sK1))) := superpose step9 step18
  have step22 (X0 X1 X2 : G) :  (X0 ◇ X2) = (X1 ◇ ((X0 ◇ X2) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X1))) := superpose step9 step11
  have step23 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ X0) ◇ X1)) = (X1 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X0 ◇ X1))) := superpose step11 step11
  have step29 (X0 X1 : G) :  (X0 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := superpose step11 step9
  have step31 (X0 X1 X2 : G) :  (X1 ◇ X0) = (X2 ◇ (X1 ◇ (X0 ◇ ((X2 ◇ X0) ◇ X2)))) := superpose step11 step9
  have step34 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ X0) ◇ X1)) = (X1 ◇ (X0 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X1))) := superpose step9 step23
  have step47 (X0 X1 X2 : G) :  (X1 ◇ X0) = (X0 ◇ (X1 ◇ (X2 ◇ ((X2 ◇ X0) ◇ X2)))) := superpose step29 step9
  have step56 (X0 X1 X2 : G) :  (X0 ◇ X2) = ((X0 ◇ (X1 ◇ X2)) ◇ ((X1 ◇ (X0 ◇ (X1 ◇ X2))) ◇ X1)) := superpose step9 step12
  have step57 (X0 X1 : G) :  (X1 ◇ ((X1 ◇ X0) ◇ X1)) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose step29 step12
  have step58 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step73 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (X1 ◇ (((X1 ◇ X0) ◇ X0) ◇ X0))) := superpose step9 step58
  have step122 (X0 X1 X2 X3 : G) :  (X0 ◇ (X1 ◇ (X2 ◇ X3))) = (X0 ◇ (X2 ◇ (X1 ◇ X3))) := superpose step16 step9
  have step204 (X0 X1 X2 : G) :  (X0 ◇ (X1 ◇ ((X2 ◇ X1) ◇ X2))) = ((X0 ◇ X1) ◇ ((X2 ◇ (X0 ◇ X1)) ◇ X2)) := superpose step31 step12
  have step242 (X0 X1 X2 : G) :  (X2 ◇ X1) = (X1 ◇ (X0 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X0)))) := superpose step16 step47
  have step343 (X0 X1 X2 X3 X4 : G) :  (X3 ◇ (X4 ◇ (X0 ◇ X1))) = (X2 ◇ (X3 ◇ (X4 ◇ ((X0 ◇ X1) ◇ ((X0 ◇ (X2 ◇ X1)) ◇ X2))))) := superpose step22 step16
  have step425 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X1) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X1 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ X1)) := superpose step57 step12
  have step460 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X1) = (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ ((X1 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X1))) := superpose step204 step425
  have step482 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X1) = (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1)))) := superpose step204 step460
  have step499 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X1) = (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ ((X1 ◇ X0) ◇ X1)))) := superpose step16 step482
  have step980 (X0 X1 : G) :  (X1 ◇ X1) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (((X1 ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ (X1 ◇ X0))) := superpose step57 step56
  have step1056 (X0 X1 : G) :  (X1 ◇ X1) = (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ (((X1 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X1 ◇ X0)))) := superpose step204 step980
  have step1100 (X0 X1 : G) :  (X1 ◇ X1) = (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))))) := superpose step204 step1056
  have step1130 (X0 X1 : G) :  (X1 ◇ X1) = (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))))) := superpose step16 step1100
  have step1145 (X0 X1 : G) :  (X1 ◇ X1) = (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)) := superpose step499 step1130
  have step1150 (X0 X1 : G) :  (X1 ◇ X1) = (X1 ◇ (((X1 ◇ X0) ◇ X0) ◇ X0)) := superpose step9 step1145
  have step1196 (X0 X1 : G) :  (((X0 ◇ X1) ◇ X1) ◇ X1) = ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) := superpose step1150 step12
  have step1216 (X0 X1 : G) :  (((X0 ◇ X1) ◇ X1) ◇ X1) = X0 := superpose step12 step1196
  have step1330 (X0 X1 X2 : G) :  ((X2 ◇ (X0 ◇ X1)) ◇ X2) = (((X0 ◇ X1) ◇ ((X0 ◇ (X2 ◇ X1)) ◇ X2)) ◇ (X2 ◇ (((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ ((X0 ◇ (X2 ◇ X1)) ◇ X2))) ◇ ((X0 ◇ X1) ◇ ((X0 ◇ (X2 ◇ X1)) ◇ X2))))) := superpose step22 step73
  have step1347 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ X1)) ◇ X0) = (X1 ◇ (X0 ◇ X0)) := superpose step1150 step73
  have step1365 (X0 X1 X2 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ (X2 ◇ X1)) = (X2 ◇ (X0 ◇ (X1 ◇ (((X1 ◇ X0) ◇ X0) ◇ X0)))) := superpose step73 step9
  have step1476 (X0 X1 X2 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ (X2 ◇ X1)) = (X2 ◇ (X0 ◇ (X1 ◇ X1))) := superpose step1150 step1365
  have step1506 (X0 X1 X2 : G) :  ((X2 ◇ (X0 ◇ X1)) ◇ X2) = (X2 ◇ (((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ ((X0 ◇ (X2 ◇ X1)) ◇ X2))) ◇ (((X0 ◇ X1) ◇ ((X0 ◇ (X2 ◇ X1)) ◇ X2)) ◇ ((X0 ◇ X1) ◇ ((X0 ◇ (X2 ◇ X1)) ◇ X2))))) := superpose step16 step1330
  have step1596 (X0 X1 X2 : G) :  ((X2 ◇ (X0 ◇ X1)) ◇ X2) = (X2 ◇ (((X0 ◇ X1) ◇ ((X0 ◇ (X2 ◇ X1)) ◇ X2)) ◇ (((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ ((X0 ◇ (X2 ◇ X1)) ◇ X2))) ◇ ((X0 ◇ X1) ◇ ((X0 ◇ (X2 ◇ X1)) ◇ X2))))) := superpose step122 step1506
  have step1665 (X0 X1 X2 : G) :  ((X2 ◇ (X0 ◇ X1)) ◇ X2) = (((X0 ◇ X1) ◇ ((X0 ◇ (X2 ◇ X1)) ◇ X2)) ◇ (((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ ((X0 ◇ (X2 ◇ X1)) ◇ X2))) ◇ (X0 ◇ X1))) := superpose step343 step1596
  have step1712 (X0 X1 X2 : G) :  ((X0 ◇ (X2 ◇ X1)) ◇ X2) = ((X2 ◇ (X0 ◇ X1)) ◇ X2) := superpose step12 step1665
  have step1832 (X0 X1 X2 : G) :  (X2 ◇ X0) = (((X0 ◇ X1) ◇ X1) ◇ (X2 ◇ X1)) := superpose step1216 step9
  have step1835 (X0 X1 X2 X3 : G) :  (X2 ◇ (X3 ◇ X0)) = (((X0 ◇ X1) ◇ X1) ◇ (X2 ◇ (X3 ◇ X1))) := superpose step1216 step16
  have step2037 (X0 X1 : G) :  ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ ((X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) ◇ X1)) = (X0 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X1)) := superpose step34 step12
  have step2069 (X0 X1 : G) :  (X0 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X1)) = (X0 ◇ (((X1 ◇ X0) ◇ X1) ◇ ((X1 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X1))) := superpose step204 step2037
  have step2123 (X0 X1 : G) :  (X0 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X1)) = (X0 ◇ ((X1 ◇ X0) ◇ (X1 ◇ ((X1 ◇ X1) ◇ X1)))) := superpose step204 step2069
  have step2156 (X0 X1 : G) :  (X0 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X1)) = (X0 ◇ (X1 ◇ ((X1 ◇ X0) ◇ ((X1 ◇ X1) ◇ X1)))) := superpose step122 step2123
  have step2178 (X0 X1 : G) :  (X0 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X1)) = ((X1 ◇ X1) ◇ X0) := superpose step242 step2156
  have step2854 (X0 X1 : G) :  ((X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) ◇ X1) = ((X0 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X1)) ◇ (X1 ◇ X1)) := superpose step34 step1347
  have step3020 (X0 X1 : G) :  ((X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) ◇ X1) = (X1 ◇ ((X0 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X1)) ◇ X1)) := superpose step9 step2854
  have step3069 (X0 X1 : G) :  ((X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) ◇ X1) = (X1 ◇ (((X1 ◇ X1) ◇ X0) ◇ X1)) := superpose step2178 step3020
  have step3099 (X0 X1 : G) :  (X0 ◇ X1) = (X1 ◇ (((X1 ◇ X1) ◇ X0) ◇ X1)) := superpose step11 step3069
  have step3689 (X0 X1 X2 : G) :  (X1 ◇ X2) = (((X2 ◇ (X0 ◇ (((X0 ◇ X1) ◇ X1) ◇ X1))) ◇ (X0 ◇ (((X0 ◇ X1) ◇ X1) ◇ X1))) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) := superpose step73 step1832
  have step3706 (X0 X1 X2 X3 : G) :  (((X1 ◇ X2) ◇ X2) ◇ X3) = (((X3 ◇ (X0 ◇ X2)) ◇ (X0 ◇ X2)) ◇ (X0 ◇ X1)) := superpose step1832 step1832
  have step3837 (X0 X1 X2 X3 : G) :  (((X1 ◇ X2) ◇ X2) ◇ X3) = (X0 ◇ (((X3 ◇ (X0 ◇ X2)) ◇ (X0 ◇ X2)) ◇ X1)) := superpose step9 step3706
  have step3854 (X0 X1 X2 : G) :  (X1 ◇ X2) = ((X0 ◇ (X0 ◇ X1)) ◇ (((X2 ◇ (X0 ◇ (((X0 ◇ X1) ◇ X1) ◇ X1))) ◇ (X0 ◇ (((X0 ◇ X1) ◇ X1) ◇ X1))) ◇ X0)) := superpose step9 step3689
  have step3922 (X0 X1 X2 X3 : G) :  (((X1 ◇ X2) ◇ X2) ◇ X3) = (X0 ◇ ((X0 ◇ ((X3 ◇ (X0 ◇ X2)) ◇ X2)) ◇ X1)) := superpose step9 step3837
  have step3938 (X0 X1 X2 : G) :  (X1 ◇ X2) = (((X2 ◇ (X0 ◇ (((X0 ◇ X1) ◇ X1) ◇ X1))) ◇ (X0 ◇ (((X0 ◇ X1) ◇ X1) ◇ X1))) ◇ (X1 ◇ (X0 ◇ X0))) := superpose step1476 step3854
  have step3999 (X0 X1 X2 : G) :  (X1 ◇ X2) = (X1 ◇ (X0 ◇ (((X2 ◇ (X0 ◇ (((X0 ◇ X1) ◇ X1) ◇ X1))) ◇ (X0 ◇ (((X0 ◇ X1) ◇ X1) ◇ X1))) ◇ X0))) := superpose step16 step3938
  have step4045 (X0 X1 X2 : G) :  (X1 ◇ X2) = (X1 ◇ (X0 ◇ ((X0 ◇ ((X2 ◇ (X0 ◇ (((X0 ◇ X1) ◇ X1) ◇ X1))) ◇ (((X0 ◇ X1) ◇ X1) ◇ X1))) ◇ X0))) := superpose step1712 step3999
  have step4072 (X0 X1 X2 : G) :  (X1 ◇ X2) = (X1 ◇ (((X0 ◇ (((X0 ◇ X1) ◇ X1) ◇ X1)) ◇ (((X0 ◇ X1) ◇ X1) ◇ X1)) ◇ X2)) := superpose step3922 step4045
  have step4089 (X0 X1 X2 : G) :  (X1 ◇ X2) = (X1 ◇ ((((X0 ◇ X1) ◇ X1) ◇ ((X0 ◇ (((X0 ◇ X1) ◇ X1) ◇ X1)) ◇ X1)) ◇ X2)) := superpose step9 step4072
  have step4098 (X0 X1 X2 : G) :  (X1 ◇ X2) = (X1 ◇ (((X0 ◇ (((X0 ◇ X1) ◇ X1) ◇ X1)) ◇ X0) ◇ X2)) := superpose step1832 step4089
  have step4105 (X0 X1 X2 : G) :  (X1 ◇ X2) = (X1 ◇ (((X0 ◇ X0) ◇ X0) ◇ X2)) := superpose step1150 step4098
  have step6215 (X0 X1 X2 : G) :  (X2 ◇ ((X0 ◇ X1) ◇ X1)) = (((X0 ◇ X1) ◇ X1) ◇ ((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ ((X0 ◇ X1) ◇ X1))) := superpose step1832 step3099
  have step6388 (X0 X1 X2 : G) :  (X2 ◇ ((X0 ◇ X1) ◇ X1)) = ((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ ((X0 ◇ X1) ◇ X0)) := superpose step1835 step6215
  have step6441 (X0 X1 X2 : G) :  (X2 ◇ ((X0 ◇ X1) ◇ X1)) = ((X0 ◇ X1) ◇ ((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ X0)) := superpose step9 step6388
  have step8528 (X0 X1 : G) :  (X0 ◇ ((((X1 ◇ X1) ◇ X1) ◇ X0) ◇ ((X1 ◇ X1) ◇ X1))) = X0 := superpose step4105 step29
  have step8710 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ X1) ◇ ((((X1 ◇ X1) ◇ X1) ◇ X0) ◇ X1))) = X0 := superpose step122 step8528
  have step8852 (X0 X1 : G) :  (X0 ◇ (X0 ◇ ((X1 ◇ X1) ◇ X1))) = X0 := superpose step6441 step8710
  have step10837 : sK0 ≠ sK0 := superpose step8852 step19
  subsumption step10837 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation4362_implies_Equation264 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation4362 G) : Equation264 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 X2 : G) :  (X0 ◇ (X1 ◇ X2)) = (X1 ◇ (X0 ◇ X2)) := mod_symm (h ..)
  have step10 : sK0 ≠ (((sK0 ◇ sK1) ◇ sK1) ◇ sK1) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step16 (X0 X1 X2 X3 : G) :  (X1 ◇ (X3 ◇ (X0 ◇ X2))) = (X3 ◇ (X0 ◇ (X1 ◇ X2))) := superpose step9 step9
  have step25 (X0 X1 : G) :  (X0 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := superpose step11 step9
  have step27 (X0 X1 X2 : G) :  (X1 ◇ X0) = (X2 ◇ (X1 ◇ (X0 ◇ ((X2 ◇ X0) ◇ X2)))) := superpose step11 step9
  have step32 (X0 X1 X2 : G) :  (X0 ◇ X2) = ((X0 ◇ (X1 ◇ X2)) ◇ ((X1 ◇ (X0 ◇ (X1 ◇ X2))) ◇ X1)) := superpose step9 step12
  have step60 (X0 X1 : G) :  (X1 ◇ ((X1 ◇ X0) ◇ X1)) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose step25 step12
  have step197 (X0 X1 X2 : G) :  (X0 ◇ (X1 ◇ ((X2 ◇ X1) ◇ X2))) = ((X0 ◇ X1) ◇ ((X2 ◇ (X0 ◇ X1)) ◇ X2)) := superpose step27 step12
  have step339 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X1) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X1 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ X1)) := superpose step60 step12
  have step369 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X1) = (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ ((X1 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X1))) := superpose step197 step339
  have step391 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X1) = (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1)))) := superpose step197 step369
  have step408 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X1) = (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ ((X1 ◇ X0) ◇ X1)))) := superpose step16 step391
  have step1121 (X0 X1 : G) :  (X1 ◇ X1) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (((X1 ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ (X1 ◇ X0))) := superpose step60 step32
  have step1199 (X0 X1 : G) :  (X1 ◇ X1) = (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ (((X1 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X1 ◇ X0)))) := superpose step197 step1121
  have step1245 (X0 X1 : G) :  (X1 ◇ X1) = (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))))) := superpose step197 step1199
  have step1277 (X0 X1 : G) :  (X1 ◇ X1) = (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))))) := superpose step16 step1245
  have step1294 (X0 X1 : G) :  (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)) = (X1 ◇ X1) := superpose step408 step1277
  have step1300 (X0 X1 : G) :  (X1 ◇ (((X1 ◇ X0) ◇ X0) ◇ X0)) = (X1 ◇ X1) := superpose step9 step1294
  have step1347 (X0 X1 : G) :  (((X0 ◇ X1) ◇ X1) ◇ X1) = ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) := superpose step1300 step12
  have step1367 (X0 X1 : G) :  (((X0 ◇ X1) ◇ X1) ◇ X1) = X0 := superpose step12 step1347
  have step2028 : sK0 ≠ sK0 := superpose step1367 step10
  subsumption step2028 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation4362_implies_Equation4293 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation4362 G) : Equation4293 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 X2 : G) :  (X0 ◇ (X1 ◇ X2)) = (X1 ◇ (X0 ◇ X2)) := mod_symm (h ..)
  have step10 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK1 ◇ (sK1 ◇ sK0)) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step16 (X0 X1 X2 X3 : G) :  (X1 ◇ (X3 ◇ (X0 ◇ X2))) = (X3 ◇ (X0 ◇ (X1 ◇ X2))) := superpose step9 step9
  have step18 (X0 X1 X2 : G) :  (X0 ◇ X2) = (X1 ◇ ((X0 ◇ X2) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X1))) := superpose step9 step11
  have step19 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ X0) ◇ X1)) = (X1 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X0 ◇ X1))) := superpose step11 step11
  have step25 (X0 X1 : G) :  (X0 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := superpose step11 step9
  have step27 (X0 X1 X2 : G) :  (X1 ◇ X0) = (X2 ◇ (X1 ◇ (X0 ◇ ((X2 ◇ X0) ◇ X2)))) := superpose step11 step9
  have step30 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ X0) ◇ X1)) = (X1 ◇ (X0 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X1))) := superpose step9 step19
  have step32 (X0 X1 X2 : G) :  (X0 ◇ X2) = ((X0 ◇ (X1 ◇ X2)) ◇ ((X1 ◇ (X0 ◇ (X1 ◇ X2))) ◇ X1)) := superpose step9 step12
  have step33 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step44 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (X1 ◇ (((X1 ◇ X0) ◇ X0) ◇ X0))) := superpose step9 step33
  have step60 (X0 X1 : G) :  (X1 ◇ ((X1 ◇ X0) ◇ X1)) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose step25 step12
  have step63 (X0 X1 X2 : G) :  (X1 ◇ X0) = (X0 ◇ (X1 ◇ (X2 ◇ ((X2 ◇ X0) ◇ X2)))) := superpose step25 step9
  have step87 (X0 X1 X2 : G) :  (X1 ◇ X0) = (X0 ◇ (X2 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X2)))) := superpose step25 step16
  have step117 (X0 X1 X2 X3 : G) :  (X0 ◇ (X1 ◇ (X2 ◇ X3))) = (X0 ◇ (X2 ◇ (X1 ◇ X3))) := superpose step16 step9
  have step197 (X0 X1 X2 : G) :  (X0 ◇ (X1 ◇ ((X2 ◇ X1) ◇ X2))) = ((X0 ◇ X1) ◇ ((X2 ◇ (X0 ◇ X1)) ◇ X2)) := superpose step27 step12
  have step266 (X0 X1 X2 X3 X4 : G) :  (X3 ◇ (X4 ◇ (X0 ◇ X1))) = (X2 ◇ (X3 ◇ (X4 ◇ ((X0 ◇ X1) ◇ ((X0 ◇ (X2 ◇ X1)) ◇ X2))))) := superpose step18 step16
  have step339 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X1) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X1 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ X1)) := superpose step60 step12
  have step369 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X1) = (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ ((X1 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X1))) := superpose step197 step339
  have step391 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X1) = (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1)))) := superpose step197 step369
  have step408 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X1) = (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ ((X1 ◇ X0) ◇ X1)))) := superpose step16 step391
  have step538 (X0 X1 X2 : G) :  (X2 ◇ X1) = (X1 ◇ (X0 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X0)))) := superpose step16 step63
  have step1121 (X0 X1 : G) :  (X1 ◇ X1) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (((X1 ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ (X1 ◇ X0))) := superpose step60 step32
  have step1199 (X0 X1 : G) :  (X1 ◇ X1) = (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ (((X1 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X1 ◇ X0)))) := superpose step197 step1121
  have step1245 (X0 X1 : G) :  (X1 ◇ X1) = (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))))) := superpose step197 step1199
  have step1277 (X0 X1 : G) :  (X1 ◇ X1) = (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))))) := superpose step16 step1245
  have step1294 (X0 X1 : G) :  (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)) = (X1 ◇ X1) := superpose step408 step1277
  have step1300 (X0 X1 : G) :  (X1 ◇ (((X1 ◇ X0) ◇ X0) ◇ X0)) = (X1 ◇ X1) := superpose step9 step1294
  have step1346 (X0 X1 : G) :  (((X0 ◇ X1) ◇ X1) ◇ X1) = ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) := superpose step1300 step12
  have step1368 (X0 X1 : G) :  (((X0 ◇ X1) ◇ X1) ◇ X1) = X0 := superpose step12 step1346
  have step1486 (X0 X1 X2 : G) :  ((X2 ◇ (X0 ◇ X1)) ◇ X2) = (((X0 ◇ X1) ◇ ((X0 ◇ (X2 ◇ X1)) ◇ X2)) ◇ (X2 ◇ (((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ ((X0 ◇ (X2 ◇ X1)) ◇ X2))) ◇ ((X0 ◇ X1) ◇ ((X0 ◇ (X2 ◇ X1)) ◇ X2))))) := superpose step18 step44
  have step1504 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ X1)) ◇ X0) = (X1 ◇ (X0 ◇ X0)) := superpose step1300 step44
  have step1523 (X0 X1 X2 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ (X2 ◇ X1)) = (X2 ◇ (X0 ◇ (X1 ◇ (((X1 ◇ X0) ◇ X0) ◇ X0)))) := superpose step44 step9
  have step1632 (X0 X1 X2 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ (X2 ◇ X1)) = (X2 ◇ (X0 ◇ (X1 ◇ X1))) := superpose step1300 step1523
  have step1664 (X0 X1 X2 : G) :  ((X2 ◇ (X0 ◇ X1)) ◇ X2) = (X2 ◇ (((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ ((X0 ◇ (X2 ◇ X1)) ◇ X2))) ◇ (((X0 ◇ X1) ◇ ((X0 ◇ (X2 ◇ X1)) ◇ X2)) ◇ ((X0 ◇ X1) ◇ ((X0 ◇ (X2 ◇ X1)) ◇ X2))))) := superpose step16 step1486
  have step1755 (X0 X1 X2 : G) :  ((X2 ◇ (X0 ◇ X1)) ◇ X2) = (X2 ◇ (((X0 ◇ X1) ◇ ((X0 ◇ (X2 ◇ X1)) ◇ X2)) ◇ (((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ ((X0 ◇ (X2 ◇ X1)) ◇ X2))) ◇ ((X0 ◇ X1) ◇ ((X0 ◇ (X2 ◇ X1)) ◇ X2))))) := superpose step117 step1664
  have step1825 (X0 X1 X2 : G) :  ((X2 ◇ (X0 ◇ X1)) ◇ X2) = (((X0 ◇ X1) ◇ ((X0 ◇ (X2 ◇ X1)) ◇ X2)) ◇ (((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ ((X0 ◇ (X2 ◇ X1)) ◇ X2))) ◇ (X0 ◇ X1))) := superpose step266 step1755
  have step1875 (X0 X1 X2 : G) :  ((X0 ◇ (X2 ◇ X1)) ◇ X2) = ((X2 ◇ (X0 ◇ X1)) ◇ X2) := superpose step12 step1825
  have step2001 (X0 X1 X2 : G) :  (X2 ◇ X0) = (((X0 ◇ X1) ◇ X1) ◇ (X2 ◇ X1)) := superpose step1368 step9
  have step2004 (X0 X1 X2 X3 : G) :  (X2 ◇ (X3 ◇ X0)) = (((X0 ◇ X1) ◇ X1) ◇ (X2 ◇ (X3 ◇ X1))) := superpose step1368 step16
  have step2210 (X0 X1 : G) :  ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ ((X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) ◇ X1)) = (X0 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X1)) := superpose step30 step12
  have step2242 (X0 X1 : G) :  (X0 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X1)) = (X0 ◇ (((X1 ◇ X0) ◇ X1) ◇ ((X1 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X1))) := superpose step197 step2210
  have step2297 (X0 X1 : G) :  (X0 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X1)) = (X0 ◇ ((X1 ◇ X0) ◇ (X1 ◇ ((X1 ◇ X1) ◇ X1)))) := superpose step197 step2242
  have step2331 (X0 X1 : G) :  (X0 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X1)) = (X0 ◇ (X1 ◇ ((X1 ◇ X0) ◇ ((X1 ◇ X1) ◇ X1)))) := superpose step117 step2297
  have step2354 (X0 X1 : G) :  (X0 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X1)) = ((X1 ◇ X1) ◇ X0) := superpose step538 step2331
  have step3071 (X0 X1 : G) :  ((X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) ◇ X1) = ((X0 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X1)) ◇ (X1 ◇ X1)) := superpose step30 step1504
  have step3239 (X0 X1 : G) :  ((X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) ◇ X1) = (X1 ◇ ((X0 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X1)) ◇ X1)) := superpose step9 step3071
  have step3288 (X0 X1 : G) :  ((X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) ◇ X1) = (X1 ◇ (((X1 ◇ X1) ◇ X0) ◇ X1)) := superpose step2354 step3239
  have step3319 (X0 X1 : G) :  (X0 ◇ X1) = (X1 ◇ (((X1 ◇ X1) ◇ X0) ◇ X1)) := superpose step11 step3288
  have step3914 (X0 X1 X2 : G) :  (X1 ◇ X2) = (((X2 ◇ (X0 ◇ (((X0 ◇ X1) ◇ X1) ◇ X1))) ◇ (X0 ◇ (((X0 ◇ X1) ◇ X1) ◇ X1))) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) := superpose step44 step2001
  have step3932 (X0 X1 X2 X3 : G) :  (((X1 ◇ X2) ◇ X2) ◇ X3) = (((X3 ◇ (X0 ◇ X2)) ◇ (X0 ◇ X2)) ◇ (X0 ◇ X1)) := superpose step2001 step2001
  have step3933 (X0 X1 X2 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X2) = (((X2 ◇ X1) ◇ X1) ◇ (X0 ◇ (X1 ◇ X1))) := superpose step1504 step2001
  have step3986 (X0 X1 X2 X3 X4 : G) :  (X3 ◇ (X4 ◇ (X0 ◇ X1))) = (((X1 ◇ X2) ◇ X2) ◇ (X3 ◇ (X4 ◇ (X0 ◇ X2)))) := superpose step2001 step16
  have step4064 (X0 X1 X2 : G) :  (X0 ◇ (X1 ◇ X2)) = ((X1 ◇ (X1 ◇ X0)) ◇ X2) := superpose step2004 step3933
  have step4065 (X0 X1 X2 X3 : G) :  (((X1 ◇ X2) ◇ X2) ◇ X3) = (X0 ◇ (((X3 ◇ (X0 ◇ X2)) ◇ (X0 ◇ X2)) ◇ X1)) := superpose step9 step3932
  have step4083 (X0 X1 X2 : G) :  (X1 ◇ X2) = ((X0 ◇ (X0 ◇ X1)) ◇ (((X2 ◇ (X0 ◇ (((X0 ◇ X1) ◇ X1) ◇ X1))) ◇ (X0 ◇ (((X0 ◇ X1) ◇ X1) ◇ X1))) ◇ X0)) := superpose step9 step3914
  have step4153 (X0 X1 X2 X3 : G) :  (((X1 ◇ X2) ◇ X2) ◇ X3) = (X0 ◇ ((X0 ◇ ((X3 ◇ (X0 ◇ X2)) ◇ X2)) ◇ X1)) := superpose step9 step4065
  have step4170 (X0 X1 X2 : G) :  (X1 ◇ X2) = (((X2 ◇ (X0 ◇ (((X0 ◇ X1) ◇ X1) ◇ X1))) ◇ (X0 ◇ (((X0 ◇ X1) ◇ X1) ◇ X1))) ◇ (X1 ◇ (X0 ◇ X0))) := superpose step1632 step4083
  have step4233 (X0 X1 X2 : G) :  (X1 ◇ X2) = (X1 ◇ (X0 ◇ (((X2 ◇ (X0 ◇ (((X0 ◇ X1) ◇ X1) ◇ X1))) ◇ (X0 ◇ (((X0 ◇ X1) ◇ X1) ◇ X1))) ◇ X0))) := superpose step16 step4170
  have step4281 (X0 X1 X2 : G) :  (X1 ◇ X2) = (X1 ◇ (X0 ◇ ((X0 ◇ ((X2 ◇ (X0 ◇ (((X0 ◇ X1) ◇ X1) ◇ X1))) ◇ (((X0 ◇ X1) ◇ X1) ◇ X1))) ◇ X0))) := superpose step1875 step4233
  have step4311 (X0 X1 X2 : G) :  (X1 ◇ X2) = (X1 ◇ (((X0 ◇ (((X0 ◇ X1) ◇ X1) ◇ X1)) ◇ (((X0 ◇ X1) ◇ X1) ◇ X1)) ◇ X2)) := superpose step4153 step4281
  have step4328 (X0 X1 X2 : G) :  (X1 ◇ X2) = (X1 ◇ ((((X0 ◇ X1) ◇ X1) ◇ ((X0 ◇ (((X0 ◇ X1) ◇ X1) ◇ X1)) ◇ X1)) ◇ X2)) := superpose step9 step4311
  have step4336 (X0 X1 X2 : G) :  (X1 ◇ X2) = (X1 ◇ (((X0 ◇ (((X0 ◇ X1) ◇ X1) ◇ X1)) ◇ X0) ◇ X2)) := superpose step2001 step4328
  have step4342 (X0 X1 X2 : G) :  (X1 ◇ X2) = (X1 ◇ (((X0 ◇ X0) ◇ X0) ◇ X2)) := superpose step1300 step4336
  have step4467 (X0 X1 X2 X3 X4 : G) :  (X4 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3)))) = (X4 ◇ (X0 ◇ (X2 ◇ (X1 ◇ X3)))) := superpose step16 step117
  have step6624 (X0 X1 X2 : G) :  (X2 ◇ ((X0 ◇ X1) ◇ X1)) = (((X0 ◇ X1) ◇ X1) ◇ ((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ ((X0 ◇ X1) ◇ X1))) := superpose step2001 step3319
  have step6799 (X0 X1 X2 : G) :  (X2 ◇ ((X0 ◇ X1) ◇ X1)) = ((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ ((X0 ◇ X1) ◇ X0)) := superpose step2004 step6624
  have step6853 (X0 X1 X2 : G) :  (X2 ◇ ((X0 ◇ X1) ◇ X1)) = ((X0 ◇ X1) ◇ ((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ X0)) := superpose step9 step6799
  have step9052 (X0 X1 X2 : G) :  (X1 ◇ X0) = (X0 ◇ (X1 ◇ ((((X2 ◇ X2) ◇ X2) ◇ X0) ◇ ((X2 ◇ X2) ◇ X2)))) := superpose step4342 step87
  have step9137 (X0 X1 X2 : G) :  (((X0 ◇ X1) ◇ X1) ◇ X1) = (((X2 ◇ X2) ◇ X2) ◇ X0) := superpose step4342 step2001
  have step9154 (X0 X2 : G) :  (((X2 ◇ X2) ◇ X2) ◇ X0) = X0 := superpose step1368 step9137
  have step9230 (X0 X1 X2 : G) :  (X1 ◇ X0) = (X0 ◇ (X1 ◇ ((X2 ◇ X2) ◇ ((((X2 ◇ X2) ◇ X2) ◇ X0) ◇ X2)))) := superpose step4467 step9052
  have step9380 (X0 X1 X2 : G) :  (X1 ◇ X0) = (X0 ◇ (X1 ◇ (X0 ◇ ((X2 ◇ X2) ◇ X2)))) := superpose step6853 step9230
  have step10292 (X0 X1 : G) :  (((X1 ◇ X1) ◇ X1) ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X1) ◇ X1)))) = X0 := superpose step9154 step11
  have step10476 (X0 X1 : G) :  (X0 ◇ (X0 ◇ ((X1 ◇ X1) ◇ X1))) = X0 := superpose step3986 step10292
  have step12947 (X0 X1 X2 : G) :  (X0 ◇ (X0 ◇ X1)) = (X1 ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ ((X2 ◇ X2) ◇ X2)))) := superpose step10476 step4064
  have step12953 (X0 X1 X2 : G) :  (X0 ◇ (X0 ◇ X1)) = (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ ((X2 ◇ X2) ◇ X2))))) := superpose step4064 step12947
  have step13050 (X0 X1 : G) :  (X0 ◇ (X0 ◇ X1)) = (X1 ◇ (X1 ◇ X0)) := superpose step9380 step12953
  have step16790 : (sK0 ◇ (sK0 ◇ sK1)) ≠ (sK0 ◇ (sK0 ◇ sK1)) := superpose step13050 step10
  subsumption step16790 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation4362_implies_Equation4320 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation4362 G) : Equation4320 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 X2 : G) :  (X0 ◇ (X1 ◇ X2)) = (X1 ◇ (X0 ◇ X2)) := mod_symm (h ..)
  have step10 : (sK0 ◇ (sK1 ◇ sK0)) ≠ (sK1 ◇ (sK0 ◇ sK0)) := mod_symm nh
  have step18 : (sK0 ◇ (sK1 ◇ sK0)) ≠ (sK0 ◇ (sK1 ◇ sK0)) := superpose step9 step10
  subsumption step18 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation4362_implies_Equation640 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation4362 G) : Equation640 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 X2 : G) :  (X0 ◇ (X1 ◇ X2)) = (X1 ◇ (X0 ◇ X2)) := mod_symm (h ..)
  have step10 : sK0 ≠ (sK0 ◇ (sK1 ◇ ((sK1 ◇ sK0) ◇ sK1))) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step25 (X0 X1 : G) :  (X0 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := superpose step11 step9
  have step64 : sK0 ≠ sK0 := superpose step25 step10
  subsumption step64 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation4362_implies_Equation716 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation4362 G) : Equation716 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 X2 : G) :  (X0 ◇ (X1 ◇ X2)) = (X1 ◇ (X0 ◇ X2)) := mod_symm (h ..)
  have step10 : sK0 ≠ (sK1 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ sK0))) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step16 (X0 X1 X2 X3 : G) :  (X1 ◇ (X3 ◇ (X0 ◇ X2))) = (X3 ◇ (X0 ◇ (X1 ◇ X2))) := superpose step9 step9
  have step18 (X0 X1 X2 : G) :  (X0 ◇ X2) = (X1 ◇ ((X0 ◇ X2) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X1))) := superpose step9 step11
  have step25 (X0 X1 : G) :  (X0 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := superpose step11 step9
  have step27 (X0 X1 X2 : G) :  (X1 ◇ X0) = (X2 ◇ (X1 ◇ (X0 ◇ ((X2 ◇ X0) ◇ X2)))) := superpose step11 step9
  have step32 (X0 X1 X2 : G) :  (X0 ◇ X2) = ((X0 ◇ (X1 ◇ X2)) ◇ ((X1 ◇ (X0 ◇ (X1 ◇ X2))) ◇ X1)) := superpose step9 step12
  have step33 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step36 (X0 X1 X2 : G) :  (((X0 ◇ X1) ◇ X2) ◇ (X0 ◇ (((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X2)) ◇ X1))) = X2 := superpose step9 step12
  have step39 (X0 X1 X2 : G) :  (X1 ◇ X0) = ((X2 ◇ X0) ◇ (X1 ◇ ((X2 ◇ (X2 ◇ X0)) ◇ X2))) := superpose step12 step9
  have step41 (X0 X1 X2 : G) :  (X0 ◇ (((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X2)) ◇ (((X0 ◇ X1) ◇ X2) ◇ X1))) = X2 := superpose step16 step36
  have step44 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (X1 ◇ (((X1 ◇ X0) ◇ X0) ◇ X0))) := superpose step9 step33
  have step46 (X0 X1 X2 : G) :  (X0 ◇ (((X0 ◇ X1) ◇ X2) ◇ (((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X2)) ◇ X1))) = X2 := superpose step9 step41
  have step60 (X0 X1 : G) :  (X1 ◇ ((X1 ◇ X0) ◇ X1)) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose step25 step12
  have step90 (X0 X1 X2 : G) :  (X1 ◇ X0) = ((X2 ◇ X0) ◇ ((X2 ◇ (X2 ◇ X0)) ◇ (X1 ◇ X2))) := superpose step12 step16
  have step102 (X0 X1 X2 X3 : G) :  (X2 ◇ (X3 ◇ X0)) = ((X1 ◇ X0) ◇ (X2 ◇ (X3 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)))) := superpose step12 step16
  have step120 (X0 X1 X2 X3 : G) :  (X0 ◇ (X1 ◇ (X2 ◇ X3))) = (X0 ◇ (X2 ◇ (X1 ◇ X3))) := superpose step16 step9
  have step198 (X0 X1 X2 : G) :  (X0 ◇ (X1 ◇ ((X2 ◇ X1) ◇ X2))) = ((X0 ◇ X1) ◇ ((X2 ◇ (X0 ◇ X1)) ◇ X2)) := superpose step27 step12
  have step267 (X0 X1 X2 X3 X4 : G) :  (X3 ◇ (X4 ◇ (X0 ◇ X1))) = (X2 ◇ (X3 ◇ (X4 ◇ ((X0 ◇ X1) ◇ ((X0 ◇ (X2 ◇ X1)) ◇ X2))))) := superpose step18 step16
  have step340 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X1) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X1 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ X1)) := superpose step60 step12
  have step370 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X1) = (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ ((X1 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X1))) := superpose step198 step340
  have step392 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X1) = (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1)))) := superpose step198 step370
  have step409 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X1) = (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ ((X1 ◇ X0) ◇ X1)))) := superpose step16 step392
  have step640 (X0 X1 X2 X3 : G) :  (X3 ◇ X2) = (((X0 ◇ X1) ◇ X2) ◇ (((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X2)) ◇ (X0 ◇ (X3 ◇ X1)))) := superpose step16 step39
  have step690 (X0 X1 X2 X3 : G) :  (X3 ◇ X2) = (X0 ◇ (((X0 ◇ X1) ◇ X2) ◇ (((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X2)) ◇ (X3 ◇ X1)))) := superpose step16 step640
  have step1122 (X0 X1 : G) :  (X1 ◇ X1) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (((X1 ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ (X1 ◇ X0))) := superpose step60 step32
  have step1200 (X0 X1 : G) :  (X1 ◇ X1) = (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ (((X1 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X1 ◇ X0)))) := superpose step198 step1122
  have step1246 (X0 X1 : G) :  (X1 ◇ X1) = (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))))) := superpose step198 step1200
  have step1278 (X0 X1 : G) :  (X1 ◇ X1) = (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))))) := superpose step16 step1246
  have step1295 (X0 X1 : G) :  (X1 ◇ X1) = (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)) := superpose step409 step1278
  have step1301 (X0 X1 : G) :  (X1 ◇ X1) = (X1 ◇ (((X1 ◇ X0) ◇ X0) ◇ X0)) := superpose step9 step1295
  have step1349 (X0 X1 : G) :  (((X0 ◇ X1) ◇ X1) ◇ X1) = ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) := superpose step1301 step12
  have step1367 (X0 X1 : G) :  (((X0 ◇ X1) ◇ X1) ◇ X1) = X0 := superpose step12 step1349
  have step1488 (X0 X1 X2 : G) :  ((X2 ◇ (X0 ◇ X1)) ◇ X2) = (((X0 ◇ X1) ◇ ((X0 ◇ (X2 ◇ X1)) ◇ X2)) ◇ (X2 ◇ (((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ ((X0 ◇ (X2 ◇ X1)) ◇ X2))) ◇ ((X0 ◇ X1) ◇ ((X0 ◇ (X2 ◇ X1)) ◇ X2))))) := superpose step18 step44
  have step1506 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ X1)) ◇ X0) = (X1 ◇ (X0 ◇ X0)) := superpose step1301 step44
  have step1525 (X0 X1 X2 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ (X2 ◇ X1)) = (X2 ◇ (X0 ◇ (X1 ◇ (((X1 ◇ X0) ◇ X0) ◇ X0)))) := superpose step44 step9
  have step1634 (X0 X1 X2 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ (X2 ◇ X1)) = (X2 ◇ (X0 ◇ (X1 ◇ X1))) := superpose step1301 step1525
  have step1666 (X0 X1 X2 : G) :  ((X2 ◇ (X0 ◇ X1)) ◇ X2) = (X2 ◇ (((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ ((X0 ◇ (X2 ◇ X1)) ◇ X2))) ◇ (((X0 ◇ X1) ◇ ((X0 ◇ (X2 ◇ X1)) ◇ X2)) ◇ ((X0 ◇ X1) ◇ ((X0 ◇ (X2 ◇ X1)) ◇ X2))))) := superpose step16 step1488
  have step1757 (X0 X1 X2 : G) :  ((X2 ◇ (X0 ◇ X1)) ◇ X2) = (X2 ◇ (((X0 ◇ X1) ◇ ((X0 ◇ (X2 ◇ X1)) ◇ X2)) ◇ (((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ ((X0 ◇ (X2 ◇ X1)) ◇ X2))) ◇ ((X0 ◇ X1) ◇ ((X0 ◇ (X2 ◇ X1)) ◇ X2))))) := superpose step120 step1666
  have step1827 (X0 X1 X2 : G) :  ((X2 ◇ (X0 ◇ X1)) ◇ X2) = (((X0 ◇ X1) ◇ ((X0 ◇ (X2 ◇ X1)) ◇ X2)) ◇ (((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ ((X0 ◇ (X2 ◇ X1)) ◇ X2))) ◇ (X0 ◇ X1))) := superpose step267 step1757
  have step1877 (X0 X1 X2 : G) :  ((X0 ◇ (X2 ◇ X1)) ◇ X2) = ((X2 ◇ (X0 ◇ X1)) ◇ X2) := superpose step12 step1827
  have step2003 (X0 X1 X2 : G) :  (X2 ◇ X0) = (((X0 ◇ X1) ◇ X1) ◇ (X2 ◇ X1)) := superpose step1367 step9
  have step2006 (X0 X1 X2 X3 : G) :  (X2 ◇ (X3 ◇ X0)) = (((X0 ◇ X1) ◇ X1) ◇ (X2 ◇ (X3 ◇ X1))) := superpose step1367 step16
  have step3919 (X0 X1 X2 : G) :  (X1 ◇ X2) = (((X2 ◇ (X0 ◇ (((X0 ◇ X1) ◇ X1) ◇ X1))) ◇ (X0 ◇ (((X0 ◇ X1) ◇ X1) ◇ X1))) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) := superpose step44 step2003
  have step3937 (X0 X1 X2 X3 : G) :  (((X1 ◇ X2) ◇ X2) ◇ X3) = (((X3 ◇ (X0 ◇ X2)) ◇ (X0 ◇ X2)) ◇ (X0 ◇ X1)) := superpose step2003 step2003
  have step3938 (X0 X1 X2 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X2) = (((X2 ◇ X1) ◇ X1) ◇ (X0 ◇ (X1 ◇ X1))) := superpose step1506 step2003
  have step3974 (X0 X1 X2 : G) :  (((X2 ◇ X0) ◇ X0) ◇ X1) = ((X0 ◇ X1) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) := superpose step2003 step39
  have step4069 (X0 X1 X2 : G) :  (X0 ◇ (X1 ◇ X2)) = ((X1 ◇ (X1 ◇ X0)) ◇ X2) := superpose step2006 step3938
  have step4070 (X0 X1 X2 X3 : G) :  (((X1 ◇ X2) ◇ X2) ◇ X3) = (X0 ◇ (((X3 ◇ (X0 ◇ X2)) ◇ (X0 ◇ X2)) ◇ X1)) := superpose step9 step3937
  have step4088 (X0 X1 X2 : G) :  (X1 ◇ X2) = ((X0 ◇ (X0 ◇ X1)) ◇ (((X2 ◇ (X0 ◇ (((X0 ◇ X1) ◇ X1) ◇ X1))) ◇ (X0 ◇ (((X0 ◇ X1) ◇ X1) ◇ X1))) ◇ X0)) := superpose step9 step3919
  have step4158 (X0 X1 X2 X3 : G) :  (((X1 ◇ X2) ◇ X2) ◇ X3) = (X0 ◇ ((X0 ◇ ((X3 ◇ (X0 ◇ X2)) ◇ X2)) ◇ X1)) := superpose step9 step4070
  have step4175 (X0 X1 X2 : G) :  (X1 ◇ X2) = (((X2 ◇ (X0 ◇ (((X0 ◇ X1) ◇ X1) ◇ X1))) ◇ (X0 ◇ (((X0 ◇ X1) ◇ X1) ◇ X1))) ◇ (X1 ◇ (X0 ◇ X0))) := superpose step1634 step4088
  have step4238 (X0 X1 X2 : G) :  (X1 ◇ X2) = (X1 ◇ (X0 ◇ (((X2 ◇ (X0 ◇ (((X0 ◇ X1) ◇ X1) ◇ X1))) ◇ (X0 ◇ (((X0 ◇ X1) ◇ X1) ◇ X1))) ◇ X0))) := superpose step16 step4175
  have step4286 (X0 X1 X2 : G) :  (X1 ◇ X2) = (X1 ◇ (X0 ◇ ((X0 ◇ ((X2 ◇ (X0 ◇ (((X0 ◇ X1) ◇ X1) ◇ X1))) ◇ (((X0 ◇ X1) ◇ X1) ◇ X1))) ◇ X0))) := superpose step1877 step4238
  have step4316 (X0 X1 X2 : G) :  (X1 ◇ X2) = (X1 ◇ (((X0 ◇ (((X0 ◇ X1) ◇ X1) ◇ X1)) ◇ (((X0 ◇ X1) ◇ X1) ◇ X1)) ◇ X2)) := superpose step4158 step4286
  have step4333 (X0 X1 X2 : G) :  (X1 ◇ X2) = (X1 ◇ ((((X0 ◇ X1) ◇ X1) ◇ ((X0 ◇ (((X0 ◇ X1) ◇ X1) ◇ X1)) ◇ X1)) ◇ X2)) := superpose step9 step4316
  have step4341 (X0 X1 X2 : G) :  (X1 ◇ X2) = (X1 ◇ (((X0 ◇ (((X0 ◇ X1) ◇ X1) ◇ X1)) ◇ X0) ◇ X2)) := superpose step2003 step4333
  have step4347 (X0 X1 X2 : G) :  (X1 ◇ X2) = (X1 ◇ (((X0 ◇ X0) ◇ X0) ◇ X2)) := superpose step1301 step4341
  have step9127 (X0 X1 X2 X3 : G) :  (X0 ◇ (((X0 ◇ X1) ◇ X3) ◇ (((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X3)) ◇ (((X2 ◇ X2) ◇ X2) ◇ X1)))) = X3 := superpose step4347 step46
  have step9174 (X2 X3 : G) :  (((X2 ◇ X2) ◇ X2) ◇ X3) = X3 := superpose step690 step9127
  have step61645 (X0 X1 X2 : G) :  ((X0 ◇ X2) ◇ ((X0 ◇ (X0 ◇ X2)) ◇ X1)) = ((X0 ◇ X1) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) := superpose step90 step102
  have step61936 (X0 X1 X2 : G) :  ((X0 ◇ X2) ◇ ((X0 ◇ (X0 ◇ X2)) ◇ X1)) = (((X2 ◇ X0) ◇ X0) ◇ X1) := superpose step3974 step61645
  have step61992 (X0 X1 X2 : G) :  (((X2 ◇ X0) ◇ X0) ◇ X1) = ((X0 ◇ X2) ◇ (X2 ◇ (X0 ◇ X1))) := superpose step4069 step61936
  have step62030 (X0 X1 X2 : G) :  (((X2 ◇ X0) ◇ X0) ◇ X1) = (X2 ◇ (X0 ◇ ((X0 ◇ X2) ◇ X1))) := superpose step16 step61992
  have step190352 : sK0 ≠ (((sK1 ◇ sK1) ◇ sK1) ◇ sK0) := superpose step62030 step10
  subsumption step190352 step9174


@[equational_result]
theorem Finite.Equation677_and_Equation4362_implies_Equation836 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation4362 G) : Equation836 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 X2 : G) :  (X0 ◇ (X1 ◇ X2)) = (X1 ◇ (X0 ◇ X2)) := mod_symm (h ..)
  have step10 : sK0 ≠ (sK0 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK1))) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step18 : sK0 ≠ (sK0 ◇ (sK1 ◇ ((sK1 ◇ sK0) ◇ sK1))) := superpose step9 step10
  have step27 (X0 X1 : G) :  (X0 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := superpose step11 step9
  have step46 : sK0 ≠ sK0 := superpose step27 step18
  subsumption step46 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation4362_implies_Equation843 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation4362 G) : Equation843 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 X2 : G) :  (X0 ◇ (X1 ◇ X2)) = (X1 ◇ (X0 ◇ X2)) := mod_symm (h ..)
  have step10 : sK0 ≠ (sK0 ◇ ((sK1 ◇ sK1) ◇ (sK0 ◇ sK1))) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step16 (X0 X1 X2 X3 : G) :  (X1 ◇ (X3 ◇ (X0 ◇ X2))) = (X3 ◇ (X0 ◇ (X1 ◇ X2))) := superpose step9 step9
  have step18 : sK0 ≠ (sK0 ◇ (sK0 ◇ ((sK1 ◇ sK1) ◇ sK1))) := superpose step9 step10
  have step20 (X0 X1 X2 : G) :  (X0 ◇ X2) = (X1 ◇ ((X0 ◇ X2) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X1))) := superpose step9 step11
  have step21 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ X0) ◇ X1)) = (X1 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X0 ◇ X1))) := superpose step11 step11
  have step27 (X0 X1 : G) :  (X0 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := superpose step11 step9
  have step29 (X0 X1 X2 : G) :  (X1 ◇ X0) = (X2 ◇ (X1 ◇ (X0 ◇ ((X2 ◇ X0) ◇ X2)))) := superpose step11 step9
  have step32 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ X0) ◇ X1)) = (X1 ◇ (X0 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X1))) := superpose step9 step21
  have step45 (X0 X1 X2 : G) :  (X1 ◇ X0) = (X0 ◇ (X1 ◇ (X2 ◇ ((X2 ◇ X0) ◇ X2)))) := superpose step27 step9
  have step54 (X0 X1 X2 : G) :  (X0 ◇ X2) = ((X0 ◇ (X1 ◇ X2)) ◇ ((X1 ◇ (X0 ◇ (X1 ◇ X2))) ◇ X1)) := superpose step9 step12
  have step55 (X0 X1 : G) :  (X1 ◇ ((X1 ◇ X0) ◇ X1)) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose step27 step12
  have step56 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step71 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (X1 ◇ (((X1 ◇ X0) ◇ X0) ◇ X0))) := superpose step9 step56
  have step119 (X0 X1 X2 X3 : G) :  (X0 ◇ (X1 ◇ (X2 ◇ X3))) = (X0 ◇ (X2 ◇ (X1 ◇ X3))) := superpose step16 step9
  have step200 (X0 X1 X2 : G) :  (X0 ◇ (X1 ◇ ((X2 ◇ X1) ◇ X2))) = ((X0 ◇ X1) ◇ ((X2 ◇ (X0 ◇ X1)) ◇ X2)) := superpose step29 step12
  have step238 (X0 X1 X2 : G) :  (X2 ◇ X1) = (X1 ◇ (X0 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X0)))) := superpose step16 step45
  have step339 (X0 X1 X2 X3 X4 : G) :  (X3 ◇ (X4 ◇ (X0 ◇ X1))) = (X2 ◇ (X3 ◇ (X4 ◇ ((X0 ◇ X1) ◇ ((X0 ◇ (X2 ◇ X1)) ◇ X2))))) := superpose step20 step16
  have step421 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X1) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X1 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ X1)) := superpose step55 step12
  have step456 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X1) = (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ ((X1 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X1))) := superpose step200 step421
  have step478 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X1) = (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1)))) := superpose step200 step456
  have step495 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X1) = (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ ((X1 ◇ X0) ◇ X1)))) := superpose step16 step478
  have step976 (X0 X1 : G) :  (X1 ◇ X1) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (((X1 ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ (X1 ◇ X0))) := superpose step55 step54
  have step1052 (X0 X1 : G) :  (X1 ◇ X1) = (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ (((X1 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X1 ◇ X0)))) := superpose step200 step976
  have step1096 (X0 X1 : G) :  (X1 ◇ X1) = (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))))) := superpose step200 step1052
  have step1126 (X0 X1 : G) :  (X1 ◇ X1) = (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))))) := superpose step16 step1096
  have step1141 (X0 X1 : G) :  (X1 ◇ X1) = (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)) := superpose step495 step1126
  have step1146 (X0 X1 : G) :  (X1 ◇ X1) = (X1 ◇ (((X1 ◇ X0) ◇ X0) ◇ X0)) := superpose step9 step1141
  have step1192 (X0 X1 : G) :  (((X0 ◇ X1) ◇ X1) ◇ X1) = ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) := superpose step1146 step12
  have step1212 (X0 X1 : G) :  (((X0 ◇ X1) ◇ X1) ◇ X1) = X0 := superpose step12 step1192
  have step1326 (X0 X1 X2 : G) :  ((X2 ◇ (X0 ◇ X1)) ◇ X2) = (((X0 ◇ X1) ◇ ((X0 ◇ (X2 ◇ X1)) ◇ X2)) ◇ (X2 ◇ (((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ ((X0 ◇ (X2 ◇ X1)) ◇ X2))) ◇ ((X0 ◇ X1) ◇ ((X0 ◇ (X2 ◇ X1)) ◇ X2))))) := superpose step20 step71
  have step1343 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ X1)) ◇ X0) = (X1 ◇ (X0 ◇ X0)) := superpose step1146 step71
  have step1361 (X0 X1 X2 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ (X2 ◇ X1)) = (X2 ◇ (X0 ◇ (X1 ◇ (((X1 ◇ X0) ◇ X0) ◇ X0)))) := superpose step71 step9
  have step1472 (X0 X1 X2 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ (X2 ◇ X1)) = (X2 ◇ (X0 ◇ (X1 ◇ X1))) := superpose step1146 step1361
  have step1502 (X0 X1 X2 : G) :  ((X2 ◇ (X0 ◇ X1)) ◇ X2) = (X2 ◇ (((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ ((X0 ◇ (X2 ◇ X1)) ◇ X2))) ◇ (((X0 ◇ X1) ◇ ((X0 ◇ (X2 ◇ X1)) ◇ X2)) ◇ ((X0 ◇ X1) ◇ ((X0 ◇ (X2 ◇ X1)) ◇ X2))))) := superpose step16 step1326
  have step1592 (X0 X1 X2 : G) :  ((X2 ◇ (X0 ◇ X1)) ◇ X2) = (X2 ◇ (((X0 ◇ X1) ◇ ((X0 ◇ (X2 ◇ X1)) ◇ X2)) ◇ (((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ ((X0 ◇ (X2 ◇ X1)) ◇ X2))) ◇ ((X0 ◇ X1) ◇ ((X0 ◇ (X2 ◇ X1)) ◇ X2))))) := superpose step119 step1502
  have step1661 (X0 X1 X2 : G) :  ((X2 ◇ (X0 ◇ X1)) ◇ X2) = (((X0 ◇ X1) ◇ ((X0 ◇ (X2 ◇ X1)) ◇ X2)) ◇ (((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ ((X0 ◇ (X2 ◇ X1)) ◇ X2))) ◇ (X0 ◇ X1))) := superpose step339 step1592
  have step1708 (X0 X1 X2 : G) :  ((X0 ◇ (X2 ◇ X1)) ◇ X2) = ((X2 ◇ (X0 ◇ X1)) ◇ X2) := superpose step12 step1661
  have step1828 (X0 X1 X2 : G) :  (X2 ◇ X0) = (((X0 ◇ X1) ◇ X1) ◇ (X2 ◇ X1)) := superpose step1212 step9
  have step1831 (X0 X1 X2 X3 : G) :  (X2 ◇ (X3 ◇ X0)) = (((X0 ◇ X1) ◇ X1) ◇ (X2 ◇ (X3 ◇ X1))) := superpose step1212 step16
  have step2033 (X0 X1 : G) :  ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ ((X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) ◇ X1)) = (X0 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X1)) := superpose step32 step12
  have step2065 (X0 X1 : G) :  (X0 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X1)) = (X0 ◇ (((X1 ◇ X0) ◇ X1) ◇ ((X1 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X1))) := superpose step200 step2033
  have step2119 (X0 X1 : G) :  (X0 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X1)) = (X0 ◇ ((X1 ◇ X0) ◇ (X1 ◇ ((X1 ◇ X1) ◇ X1)))) := superpose step200 step2065
  have step2152 (X0 X1 : G) :  (X0 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X1)) = (X0 ◇ (X1 ◇ ((X1 ◇ X0) ◇ ((X1 ◇ X1) ◇ X1)))) := superpose step119 step2119
  have step2174 (X0 X1 : G) :  (X0 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X1)) = ((X1 ◇ X1) ◇ X0) := superpose step238 step2152
  have step2850 (X0 X1 : G) :  ((X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) ◇ X1) = ((X0 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X1)) ◇ (X1 ◇ X1)) := superpose step32 step1343
  have step3016 (X0 X1 : G) :  ((X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) ◇ X1) = (X1 ◇ ((X0 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X1)) ◇ X1)) := superpose step9 step2850
  have step3065 (X0 X1 : G) :  ((X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) ◇ X1) = (X1 ◇ (((X1 ◇ X1) ◇ X0) ◇ X1)) := superpose step2174 step3016
  have step3095 (X0 X1 : G) :  (X0 ◇ X1) = (X1 ◇ (((X1 ◇ X1) ◇ X0) ◇ X1)) := superpose step11 step3065
  have step3685 (X0 X1 X2 : G) :  (X1 ◇ X2) = (((X2 ◇ (X0 ◇ (((X0 ◇ X1) ◇ X1) ◇ X1))) ◇ (X0 ◇ (((X0 ◇ X1) ◇ X1) ◇ X1))) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) := superpose step71 step1828
  have step3702 (X0 X1 X2 X3 : G) :  (((X1 ◇ X2) ◇ X2) ◇ X3) = (((X3 ◇ (X0 ◇ X2)) ◇ (X0 ◇ X2)) ◇ (X0 ◇ X1)) := superpose step1828 step1828
  have step3833 (X0 X1 X2 X3 : G) :  (((X1 ◇ X2) ◇ X2) ◇ X3) = (X0 ◇ (((X3 ◇ (X0 ◇ X2)) ◇ (X0 ◇ X2)) ◇ X1)) := superpose step9 step3702
  have step3850 (X0 X1 X2 : G) :  (X1 ◇ X2) = ((X0 ◇ (X0 ◇ X1)) ◇ (((X2 ◇ (X0 ◇ (((X0 ◇ X1) ◇ X1) ◇ X1))) ◇ (X0 ◇ (((X0 ◇ X1) ◇ X1) ◇ X1))) ◇ X0)) := superpose step9 step3685
  have step3918 (X0 X1 X2 X3 : G) :  (((X1 ◇ X2) ◇ X2) ◇ X3) = (X0 ◇ ((X0 ◇ ((X3 ◇ (X0 ◇ X2)) ◇ X2)) ◇ X1)) := superpose step9 step3833
  have step3934 (X0 X1 X2 : G) :  (X1 ◇ X2) = (((X2 ◇ (X0 ◇ (((X0 ◇ X1) ◇ X1) ◇ X1))) ◇ (X0 ◇ (((X0 ◇ X1) ◇ X1) ◇ X1))) ◇ (X1 ◇ (X0 ◇ X0))) := superpose step1472 step3850
  have step3995 (X0 X1 X2 : G) :  (X1 ◇ X2) = (X1 ◇ (X0 ◇ (((X2 ◇ (X0 ◇ (((X0 ◇ X1) ◇ X1) ◇ X1))) ◇ (X0 ◇ (((X0 ◇ X1) ◇ X1) ◇ X1))) ◇ X0))) := superpose step16 step3934
  have step4041 (X0 X1 X2 : G) :  (X1 ◇ X2) = (X1 ◇ (X0 ◇ ((X0 ◇ ((X2 ◇ (X0 ◇ (((X0 ◇ X1) ◇ X1) ◇ X1))) ◇ (((X0 ◇ X1) ◇ X1) ◇ X1))) ◇ X0))) := superpose step1708 step3995
  have step4067 (X0 X1 X2 : G) :  (X1 ◇ X2) = (X1 ◇ (((X0 ◇ (((X0 ◇ X1) ◇ X1) ◇ X1)) ◇ (((X0 ◇ X1) ◇ X1) ◇ X1)) ◇ X2)) := superpose step3918 step4041
  have step4083 (X0 X1 X2 : G) :  (X1 ◇ X2) = (X1 ◇ ((((X0 ◇ X1) ◇ X1) ◇ ((X0 ◇ (((X0 ◇ X1) ◇ X1) ◇ X1)) ◇ X1)) ◇ X2)) := superpose step9 step4067
  have step4091 (X0 X1 X2 : G) :  (X1 ◇ X2) = (X1 ◇ (((X0 ◇ (((X0 ◇ X1) ◇ X1) ◇ X1)) ◇ X0) ◇ X2)) := superpose step1828 step4083
  have step4097 (X0 X1 X2 : G) :  (X1 ◇ X2) = (X1 ◇ (((X0 ◇ X0) ◇ X0) ◇ X2)) := superpose step1146 step4091
  have step6205 (X0 X1 X2 : G) :  (X2 ◇ ((X0 ◇ X1) ◇ X1)) = (((X0 ◇ X1) ◇ X1) ◇ ((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ ((X0 ◇ X1) ◇ X1))) := superpose step1828 step3095
  have step6378 (X0 X1 X2 : G) :  (X2 ◇ ((X0 ◇ X1) ◇ X1)) = ((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ ((X0 ◇ X1) ◇ X0)) := superpose step1831 step6205
  have step6431 (X0 X1 X2 : G) :  (X2 ◇ ((X0 ◇ X1) ◇ X1)) = ((X0 ◇ X1) ◇ ((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ X0)) := superpose step9 step6378
  have step8515 (X0 X1 : G) :  (X0 ◇ ((((X1 ◇ X1) ◇ X1) ◇ X0) ◇ ((X1 ◇ X1) ◇ X1))) = X0 := superpose step4097 step27
  have step8703 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ X1) ◇ ((((X1 ◇ X1) ◇ X1) ◇ X0) ◇ X1))) = X0 := superpose step119 step8515
  have step8847 (X0 X1 : G) :  (X0 ◇ (X0 ◇ ((X1 ◇ X1) ◇ X1))) = X0 := superpose step6431 step8703
  have step10799 : sK0 ≠ sK0 := superpose step8847 step18
  subsumption step10799 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation4362_implies_Equation907 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation4362 G) : Equation907 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 X2 : G) :  (X0 ◇ (X1 ◇ X2)) = (X1 ◇ (X0 ◇ X2)) := mod_symm (h ..)
  have step10 : sK0 ≠ (sK1 ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ sK1))) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step18 : sK0 ≠ (sK1 ◇ (sK0 ◇ ((sK1 ◇ sK0) ◇ sK1))) := superpose step9 step10
  subsumption step18 step11


@[equational_result]
theorem Finite.Equation677_and_Equation43_implies_Equation670 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation43 G) : Equation670 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ X1) = (X1 ◇ X0) := mod_symm (h ..)
  have step10 : sK0 ≠ (sK1 ◇ (sK0 ◇ ((sK0 ◇ sK1) ◇ sK1))) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step14 : sK0 ≠ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := superpose step9 step10
  have step16 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X1))) = X0 := superpose step9 step11
  have step21 (X0 X1 : G) :  (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) = X0 := superpose step9 step16
  have step79 : sK0 ≠ sK0 := superpose step21 step14
  subsumption step79 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation4369_implies_Equation271 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation4369 G) : Equation271 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 X2 : G) :  (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X1 ◇ X0)) := mod_symm (h ..)
  have step10 : sK0 ≠ (((sK1 ◇ sK0) ◇ sK0) ◇ sK1) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step16 (X0 X1 X2 X3 : G) :  ((X1 ◇ X0) ◇ (X2 ◇ X3)) = (X3 ◇ (X0 ◇ (X1 ◇ X2))) := superpose step9 step9
  have step23 (X0 X1 : G) :  (X0 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X1))) = X1 := superpose step9 step11
  have step32 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X1)) = X0 := superpose step9 step12
  have step51 (X0 X1 : G) :  (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X1))))) = X0 := superpose step16 step32
  have step92 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose step51 step51
  have step93 (X0 : G) :  (X0 ◇ (X0 ◇ (X0 ◇ X0))) = ((X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) ◇ (X0 ◇ X0)) := superpose step51 step12
  have step101 (X0 : G) :  (X0 ◇ (X0 ◇ (X0 ◇ X0))) = (X0 ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0))) := superpose step16 step93
  have step102 (X0 : G) :  (X0 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose step16 step92
  have step104 (X0 : G) :  (X0 ◇ (X0 ◇ (X0 ◇ X0))) = (X0 ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)))) := superpose step16 step101
  have step106 (X0 : G) :  (X0 ◇ X0) = (X0 ◇ (X0 ◇ (X0 ◇ X0))) := superpose step23 step104
  have step108 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step102 step106
  have step117 (X0 X1 : G) :  (X1 ◇ X0) = (X0 ◇ (X0 ◇ X1)) := superpose step108 step9
  have step521 (X0 X1 : G) :  (((X0 ◇ X1) ◇ X1) ◇ X0) = X1 := superpose step117 step23
  have step919 : sK0 ≠ sK0 := superpose step521 step10
  subsumption step919 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation4399_implies_Equation1076 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation4399 G) : Equation1076 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ X1) := mod_symm (h ..)
  have step10 : sK0 ≠ (sK1 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step13 (X0 X1 : G) :  (X0 ◇ ((X0 ◇ X1) ◇ X1)) = (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) := superpose step9 step9
  have step14 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ X1)) ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) := superpose step9 step9
  have step19 (X0 X1 : G) :  (X1 ◇ X0) = (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) := superpose step11 step9
  have step23 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step24 (X0 X1 : G) :  ((X0 ◇ X1) ◇ (((X0 ◇ X1) ◇ X1) ◇ X0)) = X1 := superpose step9 step12
  have step29 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X0))) := superpose step13 step23
  have step38 (X0 X1 : G) :  (X0 ◇ X1) = ((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ ((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ ((X0 ◇ X1) ◇ X1))) := superpose step19 step19
  have step46 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X0) = ((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ ((X0 ◇ X1) ◇ X1)) := superpose step19 step12
  have step53 (X0 X1 : G) :  (X0 ◇ X1) = (((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ ((X0 ◇ X1) ◇ X1)) ◇ ((X0 ◇ X1) ◇ X1)) := superpose step9 step38
  have step55 (X0 X1 : G) :  (X0 ◇ X1) = (((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X1) ◇ X1)) := superpose step46 step53
  have step207 (X0 X1 : G) :  ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1)))) = X0 := superpose step11 step55
  have step242 (X0 X1 : G) :  ((X0 ◇ X1) ◇ (X1 ◇ X0)) = X0 := superpose step19 step207
  have step263 (X0 X1 : G) :  (((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X0 ◇ X1)) = (((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X1))) := superpose step55 step13
  have step282 (X0 X1 : G) :  ((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) = (((X0 ◇ X1) ◇ X0) ◇ (((X0 ◇ X1) ◇ X1) ◇ X1)) := superpose step9 step263
  have step326 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X0) = (X0 ◇ (X1 ◇ X0)) := superpose step242 step9
  have step939 (X0 X1 : G) :  ((((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ X0)) = (((X0 ◇ X1) ◇ X1) ◇ (((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)))) := superpose step55 step29
  have step1040 (X0 X1 : G) :  ((((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ X0)) = (((X0 ◇ X1) ◇ X1) ◇ (((X0 ◇ X1) ◇ X0) ◇ (((X0 ◇ X1) ◇ X1) ◇ X1))) := superpose step9 step939
  have step1094 (X0 X1 : G) :  (((X0 ◇ X1) ◇ X1) ◇ ((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ (X0 ◇ X1))) = ((((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ X0)) := superpose step282 step1040
  have step1135 (X0 X1 : G) :  (((X0 ◇ X1) ◇ X1) ◇ ((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ (X0 ◇ X1))) = (((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X0))) := superpose step326 step1094
  have step1163 (X0 X1 : G) :  (((X0 ◇ X1) ◇ X1) ◇ ((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ (X0 ◇ X1))) = (((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X0)) ◇ X0) := superpose step14 step1135
  have step1177 (X0 X1 : G) :  (((X0 ◇ X1) ◇ X1) ◇ ((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ (X0 ◇ X1))) = ((((X0 ◇ X1) ◇ X0) ◇ X0) ◇ X0) := superpose step9 step1163
  have step1186 (X0 X1 : G) :  (((X0 ◇ X1) ◇ X1) ◇ ((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ (X0 ◇ X1))) = (((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ X0) := superpose step326 step1177
  have step1190 (X0 X1 : G) :  (((X0 ◇ X1) ◇ X1) ◇ ((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ (X0 ◇ X1))) = ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X0) := superpose step326 step1186
  have step1192 (X0 X1 : G) :  (((X0 ◇ X1) ◇ X1) ◇ ((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ (X0 ◇ X1))) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ X0)) := superpose step326 step1190
  have step1193 (X0 X1 : G) :  (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ X0)) = X1 := superpose step24 step1192
  have step1216 (X0 X1 : G) :  (X1 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X1)) = X0 := superpose step9 step1193
  have step1578 : sK0 ≠ sK0 := superpose step1216 step10
  subsumption step1578 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation4399_implies_Equation1289 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation4399 G) : Equation1289 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ X1) := mod_symm (h ..)
  have step10 : sK0 ≠ (sK1 ◇ (((sK0 ◇ sK1) ◇ sK1) ◇ sK1)) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step13 (X0 X1 : G) :  (X0 ◇ ((X0 ◇ X1) ◇ X1)) = (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) := superpose step9 step9
  have step14 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ X1)) ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) := superpose step9 step9
  have step20 (X0 X1 : G) :  (X1 ◇ X0) = (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) := superpose step11 step9
  have step28 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step29 (X0 X1 : G) :  ((X0 ◇ X1) ◇ (((X0 ◇ X1) ◇ X1) ◇ X0)) = X1 := superpose step9 step12
  have step36 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X0))) := superpose step13 step28
  have step56 (X0 X1 : G) :  (X0 ◇ X1) = ((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ ((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ ((X0 ◇ X1) ◇ X1))) := superpose step20 step20
  have step65 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X0) = ((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ ((X0 ◇ X1) ◇ X1)) := superpose step20 step12
  have step73 (X0 X1 : G) :  (X0 ◇ X1) = (((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ ((X0 ◇ X1) ◇ X1)) ◇ ((X0 ◇ X1) ◇ X1)) := superpose step9 step56
  have step76 (X0 X1 : G) :  (X0 ◇ X1) = (((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X1) ◇ X1)) := superpose step65 step73
  have step257 (X0 X1 : G) :  ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1)))) = X0 := superpose step11 step76
  have step273 (X0 X1 : G) :  (((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X0 ◇ X1)) = (((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X1))) := superpose step76 step13
  have step282 (X0 X1 : G) :  ((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) = (((X0 ◇ X1) ◇ X0) ◇ (((X0 ◇ X1) ◇ X1) ◇ X1)) := superpose step9 step273
  have step296 (X0 X1 : G) :  ((X0 ◇ X1) ◇ (X1 ◇ X0)) = X0 := superpose step20 step257
  have step387 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X0) = (X0 ◇ (X1 ◇ X0)) := superpose step296 step9
  have step610 (X0 X1 : G) :  ((((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ X0)) = (((X0 ◇ X1) ◇ X1) ◇ (((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)))) := superpose step76 step36
  have step697 (X0 X1 : G) :  ((((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ X0)) = (((X0 ◇ X1) ◇ X1) ◇ (((X0 ◇ X1) ◇ X0) ◇ (((X0 ◇ X1) ◇ X1) ◇ X1))) := superpose step9 step610
  have step742 (X0 X1 : G) :  (((X0 ◇ X1) ◇ X1) ◇ ((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ (X0 ◇ X1))) = ((((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ X0)) := superpose step282 step697
  have step774 (X0 X1 : G) :  (((X0 ◇ X1) ◇ X1) ◇ ((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ (X0 ◇ X1))) = (((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X0))) := superpose step387 step742
  have step791 (X0 X1 : G) :  (((X0 ◇ X1) ◇ X1) ◇ ((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ (X0 ◇ X1))) = (((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X0)) ◇ X0) := superpose step14 step774
  have step799 (X0 X1 : G) :  (((X0 ◇ X1) ◇ X1) ◇ ((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ (X0 ◇ X1))) = ((((X0 ◇ X1) ◇ X0) ◇ X0) ◇ X0) := superpose step9 step791
  have step803 (X0 X1 : G) :  (((X0 ◇ X1) ◇ X1) ◇ ((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ (X0 ◇ X1))) = (((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ X0) := superpose step387 step799
  have step806 (X0 X1 : G) :  (((X0 ◇ X1) ◇ X1) ◇ ((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ (X0 ◇ X1))) = ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X0) := superpose step387 step803
  have step809 (X0 X1 : G) :  (((X0 ◇ X1) ◇ X1) ◇ ((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ (X0 ◇ X1))) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ X0)) := superpose step387 step806
  have step810 (X0 X1 : G) :  (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ X0)) = X1 := superpose step29 step809
  have step832 : sK0 ≠ sK0 := superpose step810 step10
  subsumption step832 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation4399_implies_Equation159 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation4399 G) : Equation159 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ X1) := mod_symm (h ..)
  have step10 : sK0 ≠ ((sK0 ◇ sK1) ◇ (sK1 ◇ sK0)) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step19 (X0 X1 : G) :  (X1 ◇ X0) = (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) := superpose step11 step9
  have step38 (X0 X1 : G) :  (X0 ◇ X1) = ((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ ((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ ((X0 ◇ X1) ◇ X1))) := superpose step19 step19
  have step46 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X0) = ((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ ((X0 ◇ X1) ◇ X1)) := superpose step19 step12
  have step53 (X0 X1 : G) :  (X0 ◇ X1) = (((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ ((X0 ◇ X1) ◇ X1)) ◇ ((X0 ◇ X1) ◇ X1)) := superpose step9 step38
  have step55 (X0 X1 : G) :  (X0 ◇ X1) = (((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X1) ◇ X1)) := superpose step46 step53
  have step207 (X0 X1 : G) :  ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1)))) = X0 := superpose step11 step55
  have step242 (X0 X1 : G) :  ((X0 ◇ X1) ◇ (X1 ◇ X0)) = X0 := superpose step19 step207
  have step326 : sK0 ≠ sK0 := superpose step242 step10
  subsumption step326 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation4399_implies_Equation2294 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation4399 G) : Equation2294 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ X1) := mod_symm (h ..)
  have step10 : sK0 ≠ ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ sK1) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step13 (X0 X1 : G) :  (X0 ◇ ((X0 ◇ X1) ◇ X1)) = (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) := superpose step9 step9
  have step14 (X0 X1 : G) :  ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) = ((X0 ◇ (X0 ◇ X1)) ◇ X1) := superpose step9 step9
  have step19 (X0 X1 : G) :  (X1 ◇ X0) = (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) := superpose step11 step9
  have step23 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step24 (X0 X1 : G) :  ((X0 ◇ X1) ◇ (((X0 ◇ X1) ◇ X1) ◇ X0)) = X1 := superpose step9 step12
  have step29 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X0))) := superpose step13 step23
  have step38 (X0 X1 : G) :  (X0 ◇ X1) = ((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ ((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ ((X0 ◇ X1) ◇ X1))) := superpose step19 step19
  have step46 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X0) = ((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ ((X0 ◇ X1) ◇ X1)) := superpose step19 step12
  have step53 (X0 X1 : G) :  (X0 ◇ X1) = (((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ ((X0 ◇ X1) ◇ X1)) ◇ ((X0 ◇ X1) ◇ X1)) := superpose step9 step38
  have step55 (X0 X1 : G) :  (X0 ◇ X1) = (((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X1) ◇ X1)) := superpose step46 step53
  have step207 (X0 X1 : G) :  ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1)))) = X0 := superpose step11 step55
  have step242 (X0 X1 : G) :  ((X0 ◇ X1) ◇ (X1 ◇ X0)) = X0 := superpose step19 step207
  have step263 (X0 X1 : G) :  (((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X0 ◇ X1)) = (((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X1))) := superpose step55 step13
  have step282 (X0 X1 : G) :  ((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) = (((X0 ◇ X1) ◇ X0) ◇ (((X0 ◇ X1) ◇ X1) ◇ X1)) := superpose step9 step263
  have step326 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X0) = (X0 ◇ (X1 ◇ X0)) := superpose step242 step9
  have step463 : sK0 ≠ (sK1 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)) := superpose step326 step10
  have step809 (X0 X1 : G) :  ((((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ X0)) = (((X0 ◇ X1) ◇ X1) ◇ (((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)))) := superpose step55 step29
  have step904 (X0 X1 : G) :  ((((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ X0)) = (((X0 ◇ X1) ◇ X1) ◇ (((X0 ◇ X1) ◇ X0) ◇ (((X0 ◇ X1) ◇ X1) ◇ X1))) := superpose step9 step809
  have step955 (X0 X1 : G) :  (((X0 ◇ X1) ◇ X1) ◇ ((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ (X0 ◇ X1))) = ((((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ X0)) := superpose step282 step904
  have step993 (X0 X1 : G) :  (((X0 ◇ X1) ◇ X1) ◇ ((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ (X0 ◇ X1))) = (((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X0))) := superpose step326 step955
  have step1019 (X0 X1 : G) :  (((X0 ◇ X1) ◇ X1) ◇ ((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ (X0 ◇ X1))) = (((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X0)) ◇ X0) := superpose step14 step993
  have step1031 (X0 X1 : G) :  (((X0 ◇ X1) ◇ X1) ◇ ((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ (X0 ◇ X1))) = ((((X0 ◇ X1) ◇ X0) ◇ X0) ◇ X0) := superpose step9 step1019
  have step1039 (X0 X1 : G) :  (((X0 ◇ X1) ◇ X1) ◇ ((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ (X0 ◇ X1))) = (((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ X0) := superpose step326 step1031
  have step1043 (X0 X1 : G) :  (((X0 ◇ X1) ◇ X1) ◇ ((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ (X0 ◇ X1))) = ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X0) := superpose step326 step1039
  have step1046 (X0 X1 : G) :  (((X0 ◇ X1) ◇ X1) ◇ ((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ (X0 ◇ X1))) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ X0)) := superpose step326 step1043
  have step1048 (X0 X1 : G) :  (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ X0)) = X1 := superpose step24 step1046
  have step1070 (X0 X1 : G) :  (X1 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X1)) = X0 := superpose step9 step1048
  have step1416 : sK0 ≠ sK0 := superpose step1070 step463
  subsumption step1416 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation4405_implies_Equation3 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation4405 G) : Equation3 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ (X0 ◇ X1)) = ((X1 ◇ X0) ◇ X0) := mod_symm (h ..)
  have step10 : sK0 ≠ (sK0 ◇ sK0) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step13 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ X1)) ◇ X0) = (X0 ◇ (X0 ◇ (X1 ◇ X0))) := superpose step9 step9
  have step16 (X0 : G) :  (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) = X0 := superpose step9 step11
  have step42 (X0 X1 : G) :  ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) = X1 := superpose step13 step12
  have step65 (X0 : G) :  (((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0))) = X0 := superpose step16 step42
  have step74 (X0 : G) :  ((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))))) = X0 := superpose step13 step65
  have step79 (X0 : G) :  (X0 ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0)) = X0 := superpose step11 step74
  have step81 (X0 : G) :  (X0 ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) = X0 := superpose step13 step79
  have step82 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step11 step81
  have step129 : sK0 ≠ sK0 := superpose step82 step10
  subsumption step129 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation4436_implies_Equation3 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation4436 G) : Equation3 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ (X1 ◇ X0)) = ((X0 ◇ X1) ◇ X1) := mod_symm (h ..)
  have step10 : sK0 ≠ (sK0 ◇ sK0) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step14 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ X0) ◇ X0)) = (((X0 ◇ X1) ◇ X1) ◇ (X1 ◇ X0)) := superpose step9 step9
  have step112 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) = X0 := superpose step14 step11
  have step119 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = X0 := superpose step11 step112
  have step136 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = X0 := superpose step9 step119
  have step147 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose step136 step9
  have step159 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ (X0 ◇ X0))) := superpose step9 step147
  have step164 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step136 step159
  have step246 : sK0 ≠ sK0 := superpose step164 step10
  subsumption step246 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation4442_implies_Equation3 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation4442 G) : Equation3 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ (X1 ◇ X0)) = ((X1 ◇ X0) ◇ X0) := mod_symm (h ..)
  have step10 : sK0 ≠ (sK0 ◇ sK0) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step16 (X0 : G) :  (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) = X0 := superpose step9 step11
  have step31 (X0 : G) :  (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) = ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) := superpose step16 step9
  have step32 (X0 : G) :  ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) = X0 := superpose step16 step31
  have step51 (X0 : G) :  (X0 ◇ (((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))) = X0 := superpose step32 step12
  have step54 (X0 : G) :  (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))) = X0 := superpose step32 step51
  have step57 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step16 step54
  have step77 : sK0 ≠ sK0 := superpose step57 step10
  subsumption step77 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation4599_implies_Equation1020 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation4599 G) : Equation1020 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have step9 (X0 X1 : G) :  ((X0 ◇ X0) ◇ X1) = ((X0 ◇ X1) ◇ X1) := mod_symm (h ..)
  have step10 : sK0 ≠ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0)) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step17 (X0 X1 : G) :  ((X1 ◇ X1) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) := superpose step11 step9
  have step20 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step341 (X0 X1 : G) :  (((X1 ◇ X1) ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1)))) ◇ (X1 ◇ X1)) = ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))))) := superpose step17 step20
  have step370 (X0 X1 : G) :  (((X1 ◇ X1) ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1)))) ◇ (X1 ◇ X1)) = ((X0 ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1)))) ◇ X0) := superpose step20 step341
  have step9900 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) := superpose step11 step370
  have step10143 (X0 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose step9900 step20
  have step10585 : sK0 ≠ (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0))) := superpose step10143 step10
  subsumption step10585 step11


@[equational_result]
theorem Finite.Equation677_and_Equation4608_implies_Equation255 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation4608 G) : Equation255 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have step9 (X0 X1 : G) :  ((X0 ◇ X0) ◇ X1) = ((X1 ◇ X1) ◇ X0) := mod_symm (h ..)
  have step10 : sK0 ≠ (((sK0 ◇ sK0) ◇ sK0) ◇ sK0) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step14 (X0 X1 : G) :  ((X1 ◇ X1) ◇ (X0 ◇ (((X0 ◇ X0) ◇ X1) ◇ (X1 ◇ X1)))) = X0 := superpose step9 step11
  have step17 (X0 X1 : G) :  (((X0 ◇ X0) ◇ X1) ◇ (((X1 ◇ X1) ◇ ((X0 ◇ X0) ◇ X1)) ◇ (X1 ◇ X1))) = X0 := superpose step9 step12
  have step18 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step27 (X0 X1 : G) :  (X0 ◇ (((X1 ◇ X1) ◇ X0) ◇ (X1 ◇ X1))) = (X0 ◇ (((X0 ◇ X0) ◇ X1) ◇ (X1 ◇ X1))) := superpose step14 step12
  have step97 (X0 : G) :  (X0 ◇ (((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) = X0 := superpose step12 step17
  have step118 (X0 : G) :  (X0 ◇ (((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) = X0 := superpose step27 step97
  have step120 (X0 : G) :  (X0 ◇ (X0 ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) = X0 := superpose step12 step118
  have step126 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) ◇ X0)) := superpose step120 step18
  have step129 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) := superpose step12 step126
  have step179 (X0 X1 : G) :  ((X1 ◇ X1) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) = (((X0 ◇ X0) ◇ X0) ◇ X1) := superpose step129 step9
  have step225 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ X0) = X0 := superpose step179 step12
  have step323 : sK0 ≠ sK0 := superpose step225 step10
  subsumption step323 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation464_implies_Equation3 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation464 G) : Equation3 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have step10 (X0 X1 : G) :  (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) = X0 := mod_symm (h ..)
  have step11 : sK0 ≠ (sK0 ◇ sK0) := mod_symm nh
  have step13 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step14 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step17 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = X0 := superpose step10 step10
  have step23 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = X0 := superpose step17 step13
  have step34 (X0 : G) :  (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0))) = X0 := superpose step17 step14
  have step35 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step14 step14
  have step43 (X0 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ X0) = X0 := superpose step35 step34
  have step44 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step23 step43
  have step45 : sK0 ≠ sK0 := superpose step44 step11
  subsumption step45 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation4658_implies_Equation3 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation4658 G) : Equation3 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have step9 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X1) = ((X1 ◇ X0) ◇ X0) := mod_symm (h ..)
  have step10 : sK0 ≠ (sK0 ◇ sK0) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step14 (X0 X1 : G) :  ((X1 ◇ X0) ◇ (X0 ◇ (((X0 ◇ X1) ◇ X1) ◇ (X1 ◇ X0)))) = X0 := superpose step9 step11
  have step17 (X0 X1 : G) :  (((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X1) ◇ X1) = (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) := superpose step11 step9
  have step20 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step57 (X0 X1 : G) :  (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)) = ((X0 ◇ (((X0 ◇ X1) ◇ X1) ◇ (X1 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (((X0 ◇ X1) ◇ X1) ◇ (X1 ◇ X0)))) ◇ X0)) := superpose step14 step20
  have step78 (X0 X1 : G) :  (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)) = (((X0 ◇ X1) ◇ X1) ◇ (X1 ◇ X0)) := superpose step12 step57
  have step186 (X0 X1 : G) :  ((((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X1) ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1)))) ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X1)) = (X1 ◇ (((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) ◇ X1) ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))))) := superpose step17 step20
  have step216 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X1)) = ((((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X1) ◇ X1) ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X1)) := superpose step11 step78
  have step30281 (X0 : G) :  (X0 ◇ ((X0 ◇ X0) ◇ X0)) = ((((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) ◇ X0) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0)) := superpose step11 step186
  have step30501 (X0 : G) :  (X0 ◇ ((X0 ◇ X0) ◇ X0)) = ((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0)) := superpose step216 step30281
  have step30506 (X0 : G) :  (X0 ◇ ((X0 ◇ X0) ◇ X0)) = (X0 ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0)) := superpose step11 step30501
  have step30530 (X0 : G) :  ((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ X0) = (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) ◇ (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) := superpose step30506 step20
  have step30616 (X0 : G) :  ((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ X0) = X0 := superpose step12 step30530
  have step30674 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step11 step30616
  have step31077 : sK0 ≠ sK0 := superpose step30674 step10
  subsumption step31077 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation466_implies_Equation1731 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation466 G) : Equation1731 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step10 (X0 X1 : G) :  (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) = X0 := mod_symm (h ..)
  have step11 : sK0 ≠ ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ sK0)) := mod_symm nh
  have step12 (X Y : G) : ((Y ◇ X) ◇ ((Y ◇ X) ◇ (Y ◇ (Y ◇ X)))) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (s ◇ (s ◇ (Y ◇ s)))) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (Y ◇ s)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (Y ◇ s)) (fun s => (s ◇ (s ◇ (Y ◇ s)))) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step13 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step14 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step15 (X0 X1 : G) :  (X0 ◇ (X0 ◇ (X1 ◇ X0))) = (X1 ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X0))) := superpose step10 step10
  have step16 (X0 X1 : G) :  (X0 ◇ (X0 ◇ (X1 ◇ X0))) = (X1 ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X0 ◇ X1))) := superpose step10 step13
  have step19 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ X0) ◇ X1)) = (X1 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X0))) := superpose step13 step10
  have step20 (X0 X1 : G) :  (X0 ◇ (X0 ◇ (X1 ◇ X0))) = (X0 ◇ ((X1 ◇ X0) ◇ X1)) := superpose step10 step14
  have step21 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step14 step14
  have step33 (X0 X1 : G) :  ((X1 ◇ X0) ◇ (X1 ◇ (X1 ◇ X0))) = (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) := superpose step12 step12
  have step34 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) := superpose step14 step12
  have step38 (X0 X1 : G) :  (X1 ◇ (X1 ◇ X0)) = (((X1 ◇ X0) ◇ (X1 ◇ (X1 ◇ X0))) ◇ (((X1 ◇ X0) ◇ (X1 ◇ (X1 ◇ X0))) ◇ X0)) := superpose step12 step12
  have step39 (X0 X1 : G) :  (X1 ◇ (X1 ◇ X0)) = (((X1 ◇ X0) ◇ (X1 ◇ (X1 ◇ X0))) ◇ (X0 ◇ (X1 ◇ X0))) := superpose step12 step14
  have step98 (X0 X1 : G) :  (((X1 ◇ X0) ◇ X1) ◇ (((X1 ◇ X0) ◇ X1) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0))))) = (((X1 ◇ X0) ◇ X1) ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X0)) := superpose step20 step20
  have step112 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X1) = ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) ◇ X0)) := superpose step20 step14
  have step115 (X0 X1 : G) :  (X0 ◇ (X1 ◇ X0)) = ((X1 ◇ X0) ◇ X1) := superpose step14 step112
  have step241 (X0 X1 : G) :  (X0 ◇ X1) = ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X0) := superpose step10 step115
  have step242 (X0 X1 : G) :  (X0 ◇ X1) = ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X0) := superpose step13 step115
  have step247 (X0 X1 : G) :  (X0 ◇ (X1 ◇ X0)) = (((X1 ◇ (X1 ◇ X0)) ◇ X1) ◇ X0) := superpose step14 step115
  have step251 (X0 X1 : G) :  ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X0)) = (((X0 ◇ X1) ◇ X0) ◇ X1) := superpose step115 step115
  have step478 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0)))) = ((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ (X1 ◇ X0)) := superpose step33 step115
  have step552 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X1) = (((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) := superpose step10 step241
  have step567 (X0 X1 : G) :  (((X1 ◇ X0) ◇ X1) ◇ X0) = ((((X1 ◇ X0) ◇ X1) ◇ (((X1 ◇ X0) ◇ X1) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0))))) ◇ ((X1 ◇ X0) ◇ X1)) := superpose step20 step241
  have step571 (X0 X1 : G) :  (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) = ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X0) := superpose step241 step241
  have step584 (X0 X1 : G) :  (X1 ◇ X0) = ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X1)) := superpose step241 step14
  have step586 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) = X0 := superpose step241 step10
  have step592 (X0 X1 : G) :  ((X0 ◇ X1) ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X0 ◇ X1))) = (X0 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X0))) := superpose step241 step33
  have step594 (X0 X1 : G) :  (X0 ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) := superpose step241 step115
  have step609 (X0 X1 : G) :  (((X1 ◇ X0) ◇ X1) ◇ X0) = ((((X1 ◇ X0) ◇ X1) ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X0)) ◇ ((X1 ◇ X0) ◇ X1)) := superpose step98 step567
  have step624 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X1) = (X0 ◇ ((((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X0) ◇ X0) ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X0))) := superpose step21 step552
  have step630 (X0 X1 : G) :  (((X1 ◇ X0) ◇ X1) ◇ X0) = ((((X1 ◇ X0) ◇ X1) ◇ (X0 ◇ X1)) ◇ ((X1 ◇ X0) ◇ X1)) := superpose step241 step609
  have step641 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X1) = (X0 ◇ (X0 ◇ (((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X0) ◇ X0))) := superpose step20 step624
  have step643 (X0 X1 : G) :  (((X1 ◇ X0) ◇ X1) ◇ X0) = ((X0 ◇ X1) ◇ (((X1 ◇ X0) ◇ X1) ◇ (X0 ◇ X1))) := superpose step115 step630
  have step651 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X1) = (X0 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X0))) := superpose step241 step641
  have step719 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X0 ◇ X1)) = (X1 ◇ (((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X0 ◇ X1)) ◇ (((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))))) := superpose step16 step10
  have step736 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X0 ◇ X1)) = (X1 ◇ ((((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) ◇ (X0 ◇ X1))) := superpose step251 step719
  have step778 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X0 ◇ X1)) = (X1 ◇ (((X0 ◇ X1) ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X0 ◇ X1))) ◇ (X0 ◇ X1))) := superpose step115 step736
  have step805 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X0 ◇ X1)) = (X1 ◇ ((X0 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X0))) ◇ (X0 ◇ X1))) := superpose step592 step778
  have step823 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X0 ◇ X1)) = (X1 ◇ (X0 ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)))) := superpose step651 step805
  have step844 (X0 X1 : G) :  (((X1 ◇ X0) ◇ (X1 ◇ (X1 ◇ X0))) ◇ (X1 ◇ X0)) = ((((X1 ◇ X0) ◇ (X1 ◇ (X1 ◇ X0))) ◇ (X0 ◇ (X1 ◇ X0))) ◇ ((X1 ◇ X0) ◇ (X1 ◇ (X1 ◇ X0)))) := superpose step12 step242
  have step864 (X0 X1 : G) :  ((X0 ◇ (X1 ◇ X0)) ◇ X0) = (((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X0))) := superpose step241 step242
  have step890 (X0 X1 : G) :  ((X0 ◇ (X1 ◇ X0)) ◇ X0) = ((X0 ◇ X1) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X1))) := superpose step115 step864
  have step907 (X0 X1 : G) :  (((X1 ◇ X0) ◇ (X1 ◇ (X1 ◇ X0))) ◇ (X1 ◇ X0)) = ((X0 ◇ (X1 ◇ X0)) ◇ (((X1 ◇ X0) ◇ (X1 ◇ (X1 ◇ X0))) ◇ (X0 ◇ (X1 ◇ X0)))) := superpose step115 step844
  have step917 (X0 X1 : G) :  ((X0 ◇ (X1 ◇ X0)) ◇ X0) = ((X0 ◇ X1) ◇ (X1 ◇ X0)) := superpose step584 step890
  have step927 (X0 X1 : G) :  (((X1 ◇ X0) ◇ (X1 ◇ (X1 ◇ X0))) ◇ (X1 ◇ X0)) = ((X0 ◇ (X1 ◇ X0)) ◇ (X1 ◇ (X1 ◇ X0))) := superpose step39 step907
  have step935 (X0 X1 : G) :  ((X0 ◇ (X1 ◇ X0)) ◇ (X1 ◇ (X1 ◇ X0))) = (((X1 ◇ X0) ◇ X1) ◇ (X1 ◇ (X1 ◇ X0))) := superpose step917 step927
  have step1133 (X0 X1 : G) :  (((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X0) ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X1)) = X0 := superpose step10 step584
  have step1141 (X0 X1 : G) :  ((((X1 ◇ X0) ◇ (X1 ◇ (X1 ◇ X0))) ◇ X0) ◇ (((X1 ◇ X0) ◇ (X1 ◇ (X1 ◇ X0))) ◇ (X1 ◇ X0))) = X0 := superpose step12 step584
  have step1248 (X0 X1 : G) :  ((((X1 ◇ X0) ◇ (X1 ◇ (X1 ◇ X0))) ◇ X0) ◇ (((X1 ◇ X0) ◇ X1) ◇ (X1 ◇ (X1 ◇ X0)))) = X0 := superpose step917 step1141
  have step1256 (X0 X1 : G) :  ((X0 ◇ X1) ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X1)) = X0 := superpose step241 step1133
  have step1276 (X0 X1 : G) :  ((((X1 ◇ (X1 ◇ X0)) ◇ X1) ◇ X0) ◇ (((X1 ◇ X0) ◇ X1) ◇ (X1 ◇ (X1 ◇ X0)))) = X0 := superpose step115 step1248
  have step1289 (X0 X1 : G) :  ((X0 ◇ (X1 ◇ X0)) ◇ (((X1 ◇ X0) ◇ X1) ◇ (X1 ◇ (X1 ◇ X0)))) = X0 := superpose step247 step1276
  have step1302 (X0 X1 : G) :  (X0 ◇ (X0 ◇ X1)) = (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ (X1 ◇ (X0 ◇ X1))) := superpose step115 step39
  have step1346 (X0 X1 : G) :  ((X1 ◇ (X0 ◇ X1)) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1)))) = ((X1 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))))) := superpose step39 step20
  have step1363 (X0 X1 : G) :  ((X1 ◇ (X0 ◇ X1)) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1)))) = ((X1 ◇ (X0 ◇ X1)) ◇ (((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X0 ◇ X1))) := superpose step115 step1346
  have step1415 (X0 X1 : G) :  ((X1 ◇ (X0 ◇ X1)) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1)))) = ((X1 ◇ (X0 ◇ X1)) ◇ (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ (X0 ◇ X1)))) := superpose step917 step1363
  have step1450 (X0 X1 : G) :  ((X1 ◇ (X0 ◇ X1)) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1)))) = X1 := superpose step1289 step1415
  have step1942 (X0 X1 : G) :  (X0 ◇ (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0))) = ((X0 ◇ (X1 ◇ X0)) ◇ (((X1 ◇ (X1 ◇ X0)) ◇ X1) ◇ (X0 ◇ (X1 ◇ X0)))) := superpose step247 step33
  have step1958 (X0 X1 : G) :  (X0 ◇ (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0))) = ((X0 ◇ (X1 ◇ X0)) ◇ (X1 ◇ (X1 ◇ X0))) := superpose step1302 step1942
  have step2095 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))))) = ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X0)) := superpose step15 step12
  have step2136 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))))) = (((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) := superpose step251 step2095
  have step2192 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))))) = ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ X0))) := superpose step241 step2136
  have step2239 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ ((X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) ◇ X1)) = ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ X0))) := superpose step20 step2192
  have step2274 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ X0))) := superpose step10 step2239
  have step2779 (X0 X1 : G) :  (((X0 ◇ X1) ◇ X0) ◇ X1) = ((X1 ◇ X0) ◇ (X0 ◇ X1)) := superpose step115 step917
  have step2802 (X0 X1 : G) :  (((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X0) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) = (((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X1) ◇ X0) := superpose step10 step917
  have step2957 (X0 X1 : G) :  (X0 ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X0)) = (((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X1) ◇ X0) := superpose step115 step2802
  have step3011 (X0 X1 : G) :  (X0 ◇ (X0 ◇ X1)) = (((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X1) ◇ X0) := superpose step241 step2957
  have step3059 (X0 X1 : G) :  (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) = (((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0))))) ◇ (((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0))))) ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X0 ◇ X1)))) := superpose step16 step38
  have step3108 (X0 X1 : G) :  (((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) ◇ X1) = ((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ (((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X0 ◇ (X0 ◇ X1))))) := superpose step38 step12
  have step3159 (X0 X1 : G) :  (((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) ◇ X1) = (((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1)))) ◇ (X0 ◇ X1)) := superpose step34 step3108
  have step3207 (X0 X1 : G) :  (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) = (((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0))))) ◇ (((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0))))) ◇ ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ X0))))) := superpose step2274 step3059
  have step3237 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X0) = (((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) ◇ X1) := superpose step241 step3159
  have step3280 (X0 X1 : G) :  (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) = (((X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) ◇ X1) ◇ (((X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ X0))))) := superpose step115 step3207
  have step3309 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X0) = (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X1) := superpose step115 step3237
  have step3338 (X0 X1 : G) :  ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ X0))))) = X0 := superpose step10 step3280
  have step3466 (X0 X1 : G) :  (X1 ◇ (X1 ◇ (((X0 ◇ X1) ◇ X0) ◇ X1))) = (((X0 ◇ X1) ◇ X0) ◇ (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ ((X0 ◇ X1) ◇ X0))) := superpose step3309 step33
  have step3486 (X0 X1 : G) :  (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ (X0 ◇ X1)) = (X1 ◇ (X1 ◇ (((X0 ◇ X1) ◇ X0) ◇ X1))) := superpose step643 step3466
  have step3546 (X0 X1 : G) :  (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ (X0 ◇ X1)) = (X1 ◇ (X1 ◇ ((X1 ◇ X0) ◇ (X0 ◇ X1)))) := superpose step2779 step3486
  have step3589 (X0 X1 : G) :  (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) = (X1 ◇ (X1 ◇ ((X1 ◇ X0) ◇ (X0 ◇ X1)))) := superpose step2779 step3546
  have step5302 (X0 X1 : G) :  (((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X1) ◇ (((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X1) ◇ X0)) = ((X0 ◇ X1) ◇ ((((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X1) ◇ (((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X1) ◇ X0)) ◇ ((((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X1) ◇ (((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X1) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X1)))) := superpose step1256 step15
  have step5352 (X0 X1 : G) :  (((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X1) ◇ (((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X1) ◇ X0)) = ((X0 ◇ X1) ◇ (((((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X1) ◇ (((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X1) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X1)) ◇ (((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X1) ◇ X0))) := superpose step251 step5302
  have step5446 (X0 X1 : G) :  (((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X1) ◇ (((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X1) ◇ X0)) = ((X0 ◇ X1) ◇ (((((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X1) ◇ X0) ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X1)) ◇ (((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X1) ◇ (((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X1) ◇ X0)))) := superpose step2779 step5352
  have step5513 (X0 X1 : G) :  (((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X1) ◇ (((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X1) ◇ X0)) = ((X0 ◇ X1) ◇ ((X0 ◇ (((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X1) ◇ X0)) ◇ (((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X1) ◇ (((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X1) ◇ X0)))) := superpose step935 step5446
  have step5547 (X0 X1 : G) :  (((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X1) ◇ (((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X1) ◇ X0)) = ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ ((X0 ◇ (((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X1) ◇ X0)) ◇ X0)))) := superpose step1958 step5513
  have step5566 (X0 X1 : G) :  ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X0)))) = (((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) := superpose step3011 step5547
  have step5577 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X0))) ◇ (X0 ◇ (X0 ◇ X1))) = (((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) := superpose step823 step5566
  have step5584 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X0))) = (((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) := superpose step2274 step5577
  have step6131 (X0 X1 : G) :  ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ X0))) = (((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) := superpose step241 step2779
  have step8239 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X0 ◇ X1)) = ((((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) ◇ ((((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))))) := superpose step16 step1450
  have step8250 (X0 X1 : G) :  (X1 ◇ (X1 ◇ X0)) = (((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0)))) ◇ (((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0)))) ◇ ((X1 ◇ X0) ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0)))))) := superpose step33 step1450
  have step8476 (X0 X1 : G) :  (X1 ◇ (X1 ◇ X0)) = (((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0)))) ◇ (((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0)))) ◇ X0)) := superpose step10 step8250
  have step8487 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X0 ◇ X1)) = ((((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) ◇ ((((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) ◇ X0)) := superpose step10 step8239
  have step8565 (X0 X1 : G) :  (X1 ◇ (X1 ◇ X0)) = (((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ (X1 ◇ X0)) ◇ (((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ (X1 ◇ X0)) ◇ X0)) := superpose step478 step8476
  have step8575 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X0 ◇ X1)) = (((X0 ◇ X1) ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X0 ◇ X1))) ◇ (((X0 ◇ X1) ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X0 ◇ X1))) ◇ X0)) := superpose step115 step8487
  have step8618 (X0 X1 : G) :  (X1 ◇ (X1 ◇ X0)) = (((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) := superpose step3011 step8565
  have step8626 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X0 ◇ X1)) = ((X0 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X0))) ◇ X0)) := superpose step592 step8575
  have step8651 (X0 X1 : G) :  (X1 ◇ (X1 ◇ X0)) = ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0))) := superpose step5584 step8618
  have step8658 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X0 ◇ X1)) = (((X0 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X0))) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X0))) := superpose step251 step8626
  have step8670 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X0 ◇ X1)) = (((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X0) ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X0)))) := superpose step2779 step8658
  have step8678 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X0 ◇ X1)) = ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X0))) := superpose step6131 step8670
  have step8682 (X0 X1 : G) :  ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ X0))) = ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X0))) := superpose step2274 step8678
  have step11853 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X0)) = ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X0)) ◇ (((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))))) := superpose step586 step15
  have step11859 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0))))) = ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X0)) := superpose step586 step20
  have step11948 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0))))) = (((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) := superpose step251 step11859
  have step11952 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X0)) = ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ ((((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X0))) := superpose step251 step11853
  have step12097 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0))))) = (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) := superpose step2779 step11948
  have step12100 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X0)) = ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ ((((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X0) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X0)))) := superpose step2779 step11952
  have step12216 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X0)) = ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ ((X0 ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X0)))) := superpose step935 step12100
  have step12299 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X0)) = ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X0 ◇ (X0 ◇ ((X0 ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X0)) ◇ X0)))) := superpose step1958 step12216
  have step12347 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0))))) = ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X0 ◇ (X0 ◇ ((X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0))))) ◇ X0)))) := superpose step571 step12299
  have step12375 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X0))) ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0))))) = ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0))))) := superpose step823 step12347
  have step12389 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X0))) ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0))))) = (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) := superpose step12097 step12375
  have step12398 (X0 X1 : G) :  (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) = ((X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) ◇ (X0 ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X0))) := superpose step2274 step12389
  have step12402 (X0 X1 : G) :  (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) = ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0))) := superpose step8682 step12398
  have step12405 (X0 X1 : G) :  (X1 ◇ (X1 ◇ X0)) = (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) := superpose step8651 step12402
  have step13085 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X0) = (X0 ◇ ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ (((X1 ◇ (X1 ◇ X0)) ◇ X1) ◇ (X1 ◇ X0))))) := superpose step14 step594
  have step13391 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X0) = (X0 ◇ ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ (((X1 ◇ X0) ◇ X1) ◇ (X1 ◇ (X1 ◇ X0)))))) := superpose step2779 step13085
  have step13520 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X0) = (X0 ◇ (((X1 ◇ (X1 ◇ X0)) ◇ X1) ◇ (X1 ◇ (X1 ◇ (X1 ◇ X0))))) := superpose step3589 step13391
  have step13606 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X0) = (X0 ◇ (X0 ◇ (X0 ◇ X1))) := superpose step12405 step13520
  have step14305 (X0 X1 : G) :  (X1 ◇ (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1)))) = ((((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X0)) ◇ X1) ◇ X1) := superpose step19 step13606
  have step14329 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ X0)) = ((((X1 ◇ (X1 ◇ X0)) ◇ X1) ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)) := superpose step14 step13606
  have step14378 (X0 X1 : G) :  (((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) = X0 := superpose step13606 step3338
  have step14529 (X0 X1 : G) :  ((X1 ◇ X0) ◇ (X0 ◇ X1)) = X0 := superpose step584 step14378
  have step14571 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ X0)) = ((((X1 ◇ X0) ◇ X1) ◇ (X1 ◇ (X1 ◇ X0))) ◇ (X1 ◇ X0)) := superpose step2779 step14329
  have step14594 (X0 X1 : G) :  (X1 ◇ (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1)))) = (((((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X0) ◇ ((X1 ◇ X0) ◇ X1)) ◇ X1) ◇ X1) := superpose step251 step14305
  have step14667 (X0 X1 : G) :  (X1 ◇ (X1 ◇ X0)) = ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ X0)) := superpose step14529 step14571
  have step14682 (X0 X1 : G) :  (X1 ◇ (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1)))) = ((((((X1 ◇ X0) ◇ X1) ◇ X0) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) ◇ X1) ◇ X1) := superpose step2779 step14594
  have step14724 (X0 X1 : G) :  (X1 ◇ (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1)))) = ((X0 ◇ X1) ◇ X1) := superpose step14529 step14682
  have step14750 (X0 X1 : G) :  (X1 ◇ X0) = ((X0 ◇ X1) ◇ X1) := superpose step13 step14724
  have step15840 (X0 X1 : G) :  (((X0 ◇ X1) ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)) = ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ X0)) := superpose step14529 step13606
  have step15850 (X0 X1 : G) :  (X1 ◇ (X1 ◇ X0)) = (((X0 ◇ X1) ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)) := superpose step14667 step15840
  have step16026 (X0 X1 : G) :  (X1 ◇ (X1 ◇ X0)) = ((X1 ◇ X0) ◇ (X0 ◇ X1)) := superpose step14750 step15850
  have step16168 (X0 X1 : G) :  (X1 ◇ (X1 ◇ X0)) = X0 := superpose step14529 step16026
  have step17359 : sK0 ≠ sK0 := superpose step16168 step11
  subsumption step17359 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation4673_implies_Equation264 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation4673 G) : Equation264 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 X2 : G) :  ((X0 ◇ X1) ◇ X2) = ((X0 ◇ X2) ◇ X1) := mod_symm (h ..)
  have step10 : sK0 ≠ (((sK0 ◇ sK1) ◇ sK1) ◇ sK1) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step16 (X0 X1 X2 X3 : G) :  (((X0 ◇ X2) ◇ X3) ◇ X1) = (((X0 ◇ X1) ◇ X2) ◇ X3) := superpose step9 step9
  have step18 (X0 X1 X2 : G) :  ((X0 ◇ X2) ◇ (X1 ◇ (((X0 ◇ X1) ◇ X2) ◇ (X0 ◇ X2)))) = X1 := superpose step9 step11
  have step19 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ X0) ◇ X1)) = (X1 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X0 ◇ X1))) := superpose step11 step11
  have step21 (X0 X1 : G) :  (X0 ◇ (X1 ◇ ((X0 ◇ X0) ◇ X1))) = X1 := superpose step9 step11
  have step24 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ X0) ◇ X1)) = (X1 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ ((X1 ◇ X0) ◇ X1))) := superpose step9 step19
  have step27 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step33 (X0 X1 X2 : G) :  (X0 ◇ X2) = (((X1 ◇ X0) ◇ X2) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) := superpose step12 step9
  have step34 (X0 X1 X2 : G) :  (X0 ◇ X2) = (((X1 ◇ X0) ◇ X2) ◇ ((X1 ◇ X1) ◇ (X1 ◇ X0))) := superpose step9 step33
  have step38 (X0 X1 : G) :  (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) = ((X1 ◇ X1) ◇ (X1 ◇ X0)) := superpose step9 step27
  have step50 (X0 X1 X2 : G) :  (X0 ◇ X2) = ((X1 ◇ X2) ◇ (X0 ◇ ((X1 ◇ X1) ◇ X0))) := superpose step21 step9
  have step133 (X0 X1 X2 X3 : G) :  (((X0 ◇ X1) ◇ X2) ◇ X3) = (((X0 ◇ X3) ◇ X2) ◇ X1) := superpose step16 step9
  have step462 (X0 X1 : G) :  (((X0 ◇ X0) ◇ X0) ◇ X1) = (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X1) ◇ (X0 ◇ X0)) := superpose step50 step34
  have step507 (X0 X1 : G) :  (((X0 ◇ X0) ◇ X0) ◇ X1) = (((X0 ◇ X1) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) := superpose step16 step462
  have step1309 (X0 : G) :  (X0 ◇ ((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0))) = (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ ((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)))) := superpose step21 step24
  have step1395 (X0 : G) :  (X0 ◇ ((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0))) = X0 := superpose step18 step1309
  have step1419 (X0 : G) :  (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) = X0 := superpose step38 step1395
  have step1437 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ X0) = X0 := superpose step507 step1419
  have step1499 (X0 X1 : G) :  (X0 ◇ X1) = ((((X0 ◇ X0) ◇ X1) ◇ X0) ◇ X0) := superpose step1437 step133
  have step2096 (X0 X1 : G) :  (((X0 ◇ X1) ◇ X1) ◇ X1) = (X1 ◇ (X0 ◇ ((X1 ◇ X1) ◇ X0))) := superpose step50 step1499
  have step2195 (X0 X1 : G) :  (((X0 ◇ X1) ◇ X1) ◇ X1) = X0 := superpose step21 step2096
  have step2464 : sK0 ≠ sK0 := superpose step2195 step10
  subsumption step2464 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation4673_implies_Equation643 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation4673 G) : Equation643 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 X2 : G) :  ((X0 ◇ X1) ◇ X2) = ((X0 ◇ X2) ◇ X1) := mod_symm (h ..)
  have step10 : sK0 ≠ (sK0 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ sK1))) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step16 (X0 X1 X2 X3 : G) :  (((X0 ◇ X2) ◇ X3) ◇ X1) = (((X0 ◇ X1) ◇ X2) ◇ X3) := superpose step9 step9
  have step19 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ X0) ◇ X1)) = (X1 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X0 ◇ X1))) := superpose step11 step11
  have step21 (X0 X1 : G) :  (X0 ◇ (X1 ◇ ((X0 ◇ X0) ◇ X1))) = X1 := superpose step9 step11
  have step23 (X0 X1 X2 : G) :  (X0 ◇ X2) = ((X1 ◇ X2) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) := superpose step11 step9
  have step24 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ X0) ◇ X1)) = (X1 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ ((X1 ◇ X0) ◇ X1))) := superpose step9 step19
  have step26 (X0 X1 X2 : G) :  (((X0 ◇ X1) ◇ X2) ◇ (((X0 ◇ X2) ◇ ((X0 ◇ X1) ◇ X2)) ◇ (X0 ◇ X2))) = X1 := superpose step9 step12
  have step30 (X0 X1 : G) :  ((X0 ◇ X1) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X1))) = X1 := superpose step9 step12
  have step39 (X0 X1 X2 : G) :  (((X0 ◇ X1) ◇ X2) ◇ (((X0 ◇ X2) ◇ (X0 ◇ X2)) ◇ ((X0 ◇ X1) ◇ X2))) = X1 := superpose step9 step26
  have step47 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ X0) ◇ X1)) = (X0 ◇ ((X1 ◇ X1) ◇ X0)) := superpose step21 step12
  have step50 (X0 X1 X2 : G) :  (X0 ◇ X2) = ((X1 ◇ X2) ◇ (X0 ◇ ((X1 ◇ X1) ◇ X0))) := superpose step21 step9
  have step155 (X0 X1 X2 X3 : G) :  (X2 ◇ (X0 ◇ ((X3 ◇ X0) ◇ X3))) = ((X0 ◇ X1) ◇ (X2 ◇ (((X3 ◇ X1) ◇ X2) ◇ (X3 ◇ X1)))) := superpose step23 step23
  have step222 (X0 X1 X2 : G) :  (X1 ◇ (((X0 ◇ X2) ◇ X1) ◇ (X0 ◇ X2))) = (X1 ◇ (((X0 ◇ X1) ◇ X2) ◇ (X0 ◇ X2))) := superpose step16 step47
  have step1591 (X0 X1 : G) :  (X0 ◇ (((X1 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X0))) ◇ (X1 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X0)))) ◇ X0)) = X0 := superpose step30 step39
  have step1682 (X0 X1 : G) :  (X0 ◇ (((X1 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X0))) ◇ X0) ◇ (X1 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X0))))) = X0 := superpose step47 step1591
  have step1735 (X0 X1 : G) :  (X0 ◇ (((X1 ◇ X0) ◇ ((X1 ◇ X1) ◇ (X1 ◇ X0))) ◇ (X1 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X0))))) = X0 := superpose step222 step1682
  have step1765 (X0 X1 : G) :  (X0 ◇ (X0 ◇ (X1 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X0))))) = X0 := superpose step30 step1735
  have step2275 (X0 X1 : G) :  (X0 ◇ (((X1 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X0))) ◇ X0) ◇ (X1 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X0))))) = ((X1 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X0))) ◇ (X0 ◇ (((X1 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X0))) ◇ X0) ◇ (X1 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X0)))))) := superpose step1765 step24
  have step2296 (X0 X1 X2 : G) :  (X0 ◇ (X1 ◇ ((X0 ◇ X0) ◇ X1))) = (X1 ◇ (X0 ◇ (X2 ◇ ((X2 ◇ X2) ◇ (X2 ◇ X0))))) := superpose step1765 step50
  have step2324 (X0 X1 X2 : G) :  (X1 ◇ (X0 ◇ (X2 ◇ ((X2 ◇ X2) ◇ (X2 ◇ X0))))) = X1 := superpose step21 step2296
  have step2333 (X0 X1 : G) :  (X0 ◇ (X1 ◇ ((X1 ◇ X1) ◇ X1))) = (X0 ◇ (((X1 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X0))) ◇ X0) ◇ (X1 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X0))))) := superpose step155 step2275
  have step2355 (X0 X1 : G) :  (X0 ◇ (X1 ◇ ((X1 ◇ X1) ◇ X1))) = (X0 ◇ (((X1 ◇ X0) ◇ ((X1 ◇ X1) ◇ (X1 ◇ X0))) ◇ (X1 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X0))))) := superpose step222 step2333
  have step2366 (X0 X1 : G) :  (X0 ◇ (X1 ◇ ((X1 ◇ X1) ◇ X1))) = (X0 ◇ (X0 ◇ (X1 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X0))))) := superpose step30 step2355
  have step2373 (X0 X1 : G) :  (X0 ◇ (X1 ◇ ((X1 ◇ X1) ◇ X1))) = X0 := superpose step2324 step2366
  have step2641 : sK0 ≠ sK0 := superpose step2373 step10
  subsumption step2641 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation4673_implies_Equation679 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation4673 G) : Equation679 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 X2 : G) :  ((X0 ◇ X1) ◇ X2) = ((X0 ◇ X2) ◇ X1) := mod_symm (h ..)
  have step10 : sK0 ≠ (sK1 ◇ (sK0 ◇ ((sK1 ◇ sK1) ◇ sK0))) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step18 : sK0 ≠ (sK1 ◇ (sK0 ◇ ((sK1 ◇ sK0) ◇ sK1))) := superpose step9 step10
  subsumption step18 step11


@[equational_result]
theorem Finite.Equation677_and_Equation4684_implies_Equation384 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation4684 G) : Equation384 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 X2 : G) :  ((X0 ◇ X1) ◇ X2) = ((X2 ◇ X1) ◇ X0) := mod_symm (h ..)
  have step10 : (sK0 ◇ sK1) ≠ ((sK1 ◇ sK0) ◇ sK0) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step16 (X0 X1 X2 X3 : G) :  ((X3 ◇ X0) ◇ (X2 ◇ X1)) = (((X0 ◇ X1) ◇ X2) ◇ X3) := superpose step9 step9
  have step18 : (sK0 ◇ sK1) ≠ ((sK0 ◇ sK0) ◇ sK1) := superpose step9 step10
  have step26 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step27 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose step11 step12
  have step40 (X0 X1 X2 X3 : G) :  (X0 ◇ (X2 ◇ X3)) = ((((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X3) ◇ X2) ◇ X1) := superpose step11 step16
  have step55 (X0 X1 X2 X3 : G) :  ((X0 ◇ X3) ◇ X1) = ((X1 ◇ X2) ◇ (X3 ◇ (X0 ◇ ((X2 ◇ X0) ◇ X2)))) := superpose step11 step16
  have step79 (X0 X1 X2 X3 : G) :  ((X0 ◇ X1) ◇ (X2 ◇ X3)) = ((X0 ◇ X2) ◇ (X1 ◇ X3)) := superpose step16 step9
  have step86 (X0 X1 X2 X3 : G) :  (X0 ◇ (X2 ◇ X3)) = ((X1 ◇ X2) ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X3)) := superpose step9 step40
  have step365 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))))) := superpose step27 step11
  have step387 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X0) ◇ X0) ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))))) := superpose step79 step365
  have step402 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0))) := superpose step55 step387
  have step412 (X0 : G) :  (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose step86 step402
  have step438 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) := superpose step412 step12
  have step456 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose step12 step438
  have step595 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = (((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) := superpose step456 step27
  have step622 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0)) := superpose step9 step595
  have step626 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) := superpose step79 step622
  have step628 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = X0 := superpose step12 step626
  have step828 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) := superpose step628 step26
  have step838 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = X0 := superpose step12 step828
  have step1175 (X0 : G) :  (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose step456 step838
  have step1219 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step628 step1175
  have step1761 : (sK0 ◇ sK1) ≠ (sK0 ◇ sK1) := superpose step1219 step18
  subsumption step1761 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation474_implies_Equation3 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation474 G) : Equation3 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have step10 (X0 X1 : G) :  (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) = X0 := mod_symm (h ..)
  have step11 : sK0 ≠ (sK0 ◇ sK0) := mod_symm nh
  have step12 (X Y : G) : ((Y ◇ X) ◇ (Y ◇ ((Y ◇ X) ◇ Y))) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (s ◇ (Y ◇ (s ◇ Y)))) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (Y ◇ s)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (Y ◇ s)) (fun s => (s ◇ (Y ◇ (s ◇ Y)))) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step13 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step14 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step19 (X0 X1 : G) :  (X0 ◇ (X1 ◇ (X0 ◇ X1))) = (X0 ◇ ((X1 ◇ X0) ◇ X1)) := superpose step13 step12
  have step20 (X0 X1 : G) :  (X1 ◇ ((X1 ◇ X0) ◇ X1)) = (X0 ◇ ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0)))) := superpose step12 step12
  have step26 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0)) := superpose step10 step14
  have step27 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose step13 step14
  have step31 (X0 : G) :  ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ X0) := superpose step19 step27
  have step34 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ X0) := superpose step26 step31
  have step35 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) = X0 := superpose step34 step12
  have step61 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X1) = ((X0 ◇ (X1 ◇ (X0 ◇ X1))) ◇ (X0 ◇ ((X0 ◇ (X1 ◇ (X0 ◇ X1))) ◇ X0))) := superpose step19 step12
  have step65 (X0 X1 : G) :  (X1 ◇ (X0 ◇ X1)) = ((X1 ◇ X0) ◇ X1) := superpose step12 step61
  have step74 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0))) := superpose step35 step65
  have step79 (X0 X1 : G) :  ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) = X1 := superpose step65 step12
  have step90 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) := superpose step26 step74
  have step135 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose step13 step79
  have step143 (X0 : G) :  (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose step65 step135
  have step158 (X0 : G) :  (X0 ◇ X0) = (X0 ◇ (X0 ◇ (X0 ◇ X0))) := superpose step19 step143
  have step184 (X0 : G) :  ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0))) = (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))) := superpose step19 step20
  have step221 (X0 : G) :  ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0))) = (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0))) := superpose step158 step184
  have step238 (X0 : G) :  ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0))) = (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0)))) := superpose step19 step221
  have step243 (X0 : G) :  (X0 ◇ ((X0 ◇ X0) ◇ X0)) = ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0))) := superpose step20 step238
  have step246 (X0 : G) :  (X0 ◇ ((X0 ◇ X0) ◇ X0)) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0)))) := superpose step65 step243
  have step248 (X0 : G) :  (X0 ◇ ((X0 ◇ X0) ◇ X0)) = ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) := superpose step90 step246
  have step249 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose step90 step248
  have step250 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ (X0 ◇ X0))) := superpose step19 step249
  have step251 (X0 : G) :  (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose step158 step250
  have step261 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) := superpose step251 step14
  have step272 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step14 step261
  have step415 : sK0 ≠ sK0 := superpose step272 step11
  subsumption step415 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation501_implies_Equation3 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation501 G) : Equation3 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1)))) = X0 := mod_symm (h ..)
  have step12 : sK0 ≠ (sK0 ◇ sK0) := mod_symm nh
  have step14 (X Y : G) : (Y ◇ ((Y ◇ X) ◇ ((Y ◇ X) ◇ Y))) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (Y ◇ (s ◇ (s ◇ Y)))) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (Y ◇ s)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (Y ◇ s)) (fun s => (Y ◇ (s ◇ (s ◇ Y)))) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step15 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step16 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step21 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) = X0 := superpose step15 step11
  have step23 (X0 X1 : G) :  (X1 ◇ (X0 ◇ (X0 ◇ X1))) = (X0 ◇ ((X1 ◇ X0) ◇ X1)) := superpose step15 step14
  have step24 (X0 X1 : G) :  (X1 ◇ (X0 ◇ (X0 ◇ X1))) = ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ X1)) := superpose step14 step14
  have step29 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step16 step16
  have step30 (X0 X1 : G) :  (X0 ◇ (X0 ◇ X1)) = ((X1 ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X0 ◇ X1)) := superpose step11 step16
  have step31 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose step15 step16
  have step36 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0)) := superpose step23 step31
  have step37 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose step30 step36
  have step54 (X0 : G) :  (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0)))) = X0 := superpose step37 step14
  have step68 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ X0) = (X0 ◇ ((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0))) := superpose step21 step16
  have step75 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ X0) = (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose step29 step68
  have step80 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ X0) = ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0)) := superpose step24 step75
  have step83 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose step30 step80
  have step85 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose step37 step83
  have step154 (X0 : G) :  (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0)))) := superpose step85 step15
  have step162 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step54 step154
  have step212 : sK0 ≠ sK0 := superpose step162 step12
  subsumption step212 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation503_implies_Equation3 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation503 G) : Equation3 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0)))) = X0 := mod_symm (h ..)
  have step12 : sK0 ≠ (sK0 ◇ sK0) := mod_symm nh
  have step14 (X Y : G) : (Y ◇ ((Y ◇ X) ◇ (Y ◇ (Y ◇ X)))) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (Y ◇ (s ◇ (Y ◇ s)))) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (Y ◇ s)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (Y ◇ s)) (fun s => (Y ◇ (s ◇ (Y ◇ s)))) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step15 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step16 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step21 (X0 X1 : G) :  (X1 ◇ (X0 ◇ (X1 ◇ X0))) = (X0 ◇ ((X1 ◇ X0) ◇ X1)) := superpose step15 step14
  have step22 (X0 X1 : G) :  (X1 ◇ (X0 ◇ (X1 ◇ X0))) = ((X1 ◇ X0) ◇ (X1 ◇ (X1 ◇ X0))) := superpose step14 step14
  have step29 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step16 step16
  have step30 (X0 X1 : G) :  (X0 ◇ (X1 ◇ X0)) = ((X1 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X0 ◇ X1)) := superpose step11 step16
  have step31 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose step15 step16
  have step36 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0)) := superpose step21 step31
  have step37 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose step30 step36
  have step56 (X0 : G) :  ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))))) = X0 := superpose step37 step14
  have step59 (X0 : G) :  ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))) = X0 := superpose step22 step56
  have step62 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))))) = X0 := superpose step22 step59
  have step65 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = X0 := superpose step14 step62
  have step85 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = X0 := superpose step65 step37
  have step87 (X0 : G) :  (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0))) = X0 := superpose step65 step16
  have step92 (X0 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ X0) = X0 := superpose step29 step87
  have step95 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step85 step92
  have step147 : sK0 ≠ sK0 := superpose step95 step12
  subsumption step147 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation513_implies_Equation411 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation513 G) : Equation411 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X1 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X0)))) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := mod_symm nh
  have step13 : sK0 ≠ sK0 := superpose step9 step10
  subsumption step13 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation630_implies_Equation4273 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation630 G) : Equation4273 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ (X1 ◇ ((X0 ◇ X0) ◇ X1))) = X0 := mod_symm (h ..)
  have step10 : (sK0 ◇ (sK0 ◇ sK0)) ≠ (sK1 ◇ (sK0 ◇ sK1)) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step17 (X0 X1 : G) :  (X1 ◇ ((X0 ◇ X0) ◇ X1)) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose step9 step12
  have step18 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step20 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose step11 step12
  have step21 (X0 : G) :  (X0 ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ X0)) = X0 := superpose step12 step9
  have step23 (X0 : G) :  (X0 ◇ ((X0 ◇ X0) ◇ X0)) = (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ X0) := superpose step21 step12
  have step32 (X0 X1 : G) :  (X1 ◇ ((X1 ◇ X1) ◇ X1)) = (((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) := superpose step17 step17
  have step34 (X0 X1 X2 : G) :  (X0 ◇ ((X1 ◇ X1) ◇ X0)) = (X2 ◇ ((X1 ◇ X1) ◇ X2)) := superpose step17 step17
  have step36 (X0 : G) :  (X0 ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0))) := superpose step17 step12
  have step48 (X0 : G) :  (X0 ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) := superpose step20 step36
  have step174 (X0 : G) :  (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) := superpose step17 step23
  have step179 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) := superpose step20 step174
  have step487 (X0 X1 : G) :  (X1 ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X1)) = (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) := superpose step48 step34
  have step492 (X0 : G) :  ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = (((X0 ◇ X0) ◇ X0) ◇ (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0))) := superpose step48 step18
  have step496 (X0 : G) :  ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = X0 := superpose step12 step492
  have step3270 (X0 : G) :  (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) = ((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)))) := superpose step487 step32
  have step3333 (X0 : G) :  (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) = ((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0))) := superpose step179 step3270
  have step3370 (X0 : G) :  ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = ((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0))) := superpose step179 step3333
  have step3378 (X0 : G) :  ((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0))) = X0 := superpose step496 step3370
  have step23840 (X0 X1 X2 : G) :  (X1 ◇ (X0 ◇ X1)) = (X2 ◇ (X0 ◇ X2)) := superpose step3378 step34
  have step25637 (X0 : G) :  (sK0 ◇ (sK0 ◇ sK0)) ≠ (X0 ◇ (sK0 ◇ X0)) := superpose step23840 step10
  subsumption step25637 step23840


@[equational_result]
theorem Finite.Equation677_and_Equation633_implies_Equation255 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation633 G) : Equation255 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X1))) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ (((sK0 ◇ sK0) ◇ sK0) ◇ sK0) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step13 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X1))))) = X0 := superpose step9 step9
  have step14 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ ((X0 ◇ X1) ◇ X1)) ◇ X0)) = X0 := superpose step9 step13
  have step15 (X0 X1 : G) :  (X1 ◇ ((X0 ◇ X1) ◇ X1)) = (X0 ◇ ((X1 ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X0 ◇ X0))) := superpose step9 step11
  have step18 (X0 X1 : G) :  (X1 ◇ ((X0 ◇ X1) ◇ X1)) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose step9 step12
  have step19 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step21 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose step11 step12
  have step28 (X0 X1 : G) :  ((X1 ◇ ((X0 ◇ X1) ◇ X1)) ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose step14 step12
  have step30 (X0 X1 : G) :  (X0 ◇ (((X1 ◇ ((X0 ◇ X1) ◇ X1)) ◇ X0) ◇ (X0 ◇ ((X1 ◇ ((X0 ◇ X1) ◇ X1)) ◇ X0)))) = X0 := superpose step14 step9
  have step31 (X0 X1 : G) :  (X0 ◇ (((X1 ◇ ((X0 ◇ X1) ◇ X1)) ◇ X0) ◇ X0)) = X0 := superpose step14 step30
  have step40 (X0 X1 X2 : G) :  (X0 ◇ ((X1 ◇ X0) ◇ X0)) = (X2 ◇ ((X1 ◇ X2) ◇ X2)) := superpose step18 step18
  have step45 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X1) = (X1 ◇ (((X0 ◇ X1) ◇ X1) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X1))) := superpose step18 step11
  have step51 (X0 X1 : G) :  ((X1 ◇ X1) ◇ X1) = ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ ((X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ X1)) := superpose step18 step12
  have step54 (X0 X1 : G) :  ((X1 ◇ X1) ◇ X1) = ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X1 ◇ X1)) := superpose step9 step51
  have step68 (X0 X1 : G) :  (X1 ◇ ((X0 ◇ X1) ◇ X1)) = ((X1 ◇ ((X0 ◇ X1) ◇ X1)) ◇ X0) := superpose step31 step9
  have step120 (X0 X1 : G) :  ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0))) = (X1 ◇ (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X1) ◇ X1)) := superpose step21 step40
  have step147 (X0 X1 X2 : G) :  (X0 ◇ (((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X0) ◇ X0)) = X2 := superpose step40 step31
  have step158 (X0 : G) :  ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0))) = X0 := superpose step147 step120
  have step189 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ ((X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) ◇ (X1 ◇ (X1 ◇ X0))))) = X1 := superpose step19 step11
  have step257 (X0 X1 X2 : G) :  (X0 ◇ ((X1 ◇ X0) ◇ X1)) = (((X2 ◇ ((X0 ◇ X2) ◇ X2)) ◇ X1) ◇ X1) := superpose step147 step12
  have step343 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) = (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0))) := superpose step158 step12
  have step360 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose step19 step343
  have step438 (X0 : G) :  (((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)))) ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) := superpose step158 step28
  have step543 (X0 : G) :  ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) = (((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ (X0 ◇ X0)) := superpose step19 step438
  have step558 (X0 : G) :  ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) = ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ (X0 ◇ X0)) := superpose step360 step543
  have step1052 (X0 : G) :  ((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)))) = (((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)))) ◇ (X0 ◇ X0)) := superpose step158 step68
  have step1134 (X0 : G) :  ((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) = (((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ (X0 ◇ X0)) := superpose step19 step1052
  have step1148 (X0 : G) :  (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) = ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ (X0 ◇ X0)) := superpose step360 step1134
  have step1155 (X0 : G) :  ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) = (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) := superpose step558 step1148
  have step1894 (X0 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ X0) = (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) := superpose step360 step19
  have step2234 (X0 X1 : G) :  ((X1 ◇ ((X0 ◇ X1) ◇ X1)) ◇ X1) = ((((X0 ◇ X1) ◇ X1) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X1)) ◇ ((((X0 ◇ X1) ◇ X1) ◇ (((X0 ◇ X1) ◇ X1) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X1))) ◇ ((X0 ◇ X1) ◇ X1))) := superpose step45 step19
  have step2253 (X0 X1 : G) :  ((X1 ◇ ((X0 ◇ X1) ◇ X1)) ◇ X1) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X1) := superpose step12 step2234
  have step2323 (X0 : G) :  ((X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ X0) = (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) := superpose step1894 step19
  have step2359 (X0 : G) :  ((X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ X0) = (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) := superpose step1155 step2323
  have step2369 (X0 : G) :  (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ X0) = (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) := superpose step1894 step2359
  have step3244 (X0 X1 X2 : G) :  ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X2) = ((X1 ◇ ((X1 ◇ X1) ◇ X1)) ◇ X2) := superpose step40 step2253
  have step3830 (X0 X1 X2 : G) :  (((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X2 ◇ X1)) ◇ (X2 ◇ X1)) = ((X2 ◇ (X2 ◇ X1)) ◇ X2) := superpose step257 step19
  have step3833 (X0 X1 X2 : G) :  (((X0 ◇ (((X1 ◇ X2) ◇ X0) ◇ X0)) ◇ X1) ◇ X1) = X2 := superpose step257 step12
  have step4606 (X0 X1 X2 : G) :  ((X1 ◇ (((X2 ◇ X0) ◇ X1) ◇ X1)) ◇ X2) = (((X1 ◇ (((X2 ◇ X0) ◇ X1) ◇ X1)) ◇ X2) ◇ (X2 ◇ (X0 ◇ X2))) := superpose step3833 step9
  have step4622 (X0 X1 X2 X3 : G) :  (X1 ◇ ((((X2 ◇ (((X3 ◇ X0) ◇ X2) ◇ X2)) ◇ X3) ◇ X1) ◇ X1)) = (X3 ◇ (X0 ◇ X3)) := superpose step3833 step40
  have step4629 (X0 X1 X2 : G) :  (X1 ◇ (X0 ◇ X1)) = ((X1 ◇ (X0 ◇ X1)) ◇ ((X2 ◇ (((X1 ◇ X0) ◇ X2) ◇ X2)) ◇ X1)) := superpose step3833 step68
  have step4982 (X0 X1 X2 : G) :  ((((X1 ◇ (X1 ◇ X0)) ◇ X1) ◇ (X0 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1))) ◇ X2) = (((X1 ◇ X0) ◇ (((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0))) ◇ X2) := superpose step12 step3244
  have step5061 (X0 X1 X2 X3 : G) :  ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X2) = ((X3 ◇ ((X1 ◇ X3) ◇ X3)) ◇ X2) := superpose step3244 step3244
  have step11537 (X0 X1 : G) :  ((X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ X0) = (((X1 ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ X1) ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) := superpose step1894 step3830
  have step11783 (X0 X1 : G) :  ((X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ X0) = ((X1 ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ X1) ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) := superpose step68 step11537
  have step11899 (X0 X1 : G) :  ((X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ X0) = (X1 ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ X1) ◇ X1)) := superpose step68 step11783
  have step11929 (X0 X1 : G) :  (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ X0) = (X1 ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ X1) ◇ X1)) := superpose step1894 step11899
  have step12010 (X0 : G) :  ((X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ (X0 ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))))) = X0 := superpose step1894 step189
  have step12145 (X0 : G) :  (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) = X0 := superpose step1894 step12010
  have step12200 (X0 : G) :  (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))))) = X0 := superpose step28 step12145
  have step12223 (X0 : G) :  (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ X0))) = X0 := superpose step11929 step12200
  have step12252 (X0 X1 : G) :  (((X1 ◇ (X1 ◇ X1)) ◇ X1) ◇ (X0 ◇ (((X1 ◇ (X1 ◇ X1)) ◇ X0) ◇ X0))) = X1 := superpose step40 step12223
  have step14424 (X0 X1 : G) :  (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (((X1 ◇ (((X0 ◇ X0) ◇ X1) ◇ X1)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ ((X1 ◇ (((X0 ◇ X0) ◇ X1) ◇ X1)) ◇ X0)))) = X0 := superpose step4629 step12252
  have step14481 (X0 X1 X2 : G) :  (((X2 ◇ (((X0 ◇ (X1 ◇ X0)) ◇ X2) ◇ X2)) ◇ X0) ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ ((X2 ◇ (((X0 ◇ (X1 ◇ X0)) ◇ X2) ◇ X2)) ◇ X0))) = X1 := superpose step4629 step147
  have step14488 (X0 X1 X2 X3 : G) :  (X0 ◇ ((X1 ◇ X0) ◇ X0)) = ((X2 ◇ ((X1 ◇ X2) ◇ X2)) ◇ ((X3 ◇ (((X0 ◇ (X1 ◇ X0)) ◇ X3) ◇ X3)) ◇ X0)) := superpose step4629 step5061
  have step14495 (X0 X1 X2 : G) :  (((X2 ◇ (((X0 ◇ (X1 ◇ X0)) ◇ X2) ◇ X2)) ◇ X0) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) = X1 := superpose step14488 step14481
  have step14545 (X0 X1 : G) :  (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (((X1 ◇ (((X0 ◇ X0) ◇ X1) ◇ X1)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0)))) = X0 := superpose step4629 step14424
  have step14705 (X0 X1 X2 : G) :  ((X2 ◇ (((X0 ◇ (X1 ◇ X0)) ◇ X2) ◇ X2)) ◇ X0) = X1 := superpose step4606 step14495
  have step14740 (X0 X1 : G) :  (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X1 ◇ (((X0 ◇ X0) ◇ X1) ◇ X1)) ◇ X0)) = X0 := superpose step4606 step14545
  have step15145 (X0 X1 : G) :  (X0 ◇ (X0 ◇ X0)) = ((X1 ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ X1) ◇ X1)) ◇ X0) := superpose step1894 step14705
  have step15732 (X0 X1 : G) :  (((X1 ◇ (((X0 ◇ X0) ◇ X1) ◇ X1)) ◇ X0) ◇ (X0 ◇ ((X1 ◇ (((X0 ◇ X0) ◇ X1) ◇ X1)) ◇ X0))) = (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((((X1 ◇ (((X0 ◇ X0) ◇ X1) ◇ X1)) ◇ X0) ◇ (X0 ◇ ((X1 ◇ (((X0 ◇ X0) ◇ X1) ◇ X1)) ◇ X0))) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) := superpose step14740 step15
  have step15757 (X0 X1 : G) :  ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) = ((((X1 ◇ (((X0 ◇ X0) ◇ X1) ◇ X1)) ◇ X0) ◇ (X0 ◇ ((X1 ◇ (((X0 ◇ X0) ◇ X1) ◇ X1)) ◇ X0))) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) := superpose step14740 step54
  have step15800 (X0 X1 : G) :  (((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) = ((((X1 ◇ (((X0 ◇ X0) ◇ X1) ◇ X1)) ◇ X0) ◇ (X0 ◇ ((X1 ◇ (((X0 ◇ X0) ◇ X1) ◇ X1)) ◇ X0))) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)))) := superpose step1155 step15757
  have step15817 (X0 X1 : G) :  (((X1 ◇ (((X0 ◇ X0) ◇ X1) ◇ X1)) ◇ X0) ◇ (X0 ◇ ((X1 ◇ (((X0 ◇ X0) ◇ X1) ◇ X1)) ◇ X0))) = (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((((X1 ◇ (((X0 ◇ X0) ◇ X1) ◇ X1)) ◇ X0) ◇ (X0 ◇ ((X1 ◇ (((X0 ◇ X0) ◇ X1) ◇ X1)) ◇ X0))) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))))) := superpose step1155 step15732
  have step15877 (X0 X1 : G) :  (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) = (((X1 ◇ (((X0 ◇ X0) ◇ X1) ◇ X1)) ◇ X0) ◇ (X0 ◇ ((X1 ◇ (((X0 ◇ X0) ◇ X1) ◇ X1)) ◇ X0))) := superpose step15800 step15817
  have step15901 (X0 X1 : G) :  (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ X0) = (((X1 ◇ (((X0 ◇ X0) ◇ X1) ◇ X1)) ◇ X0) ◇ (X0 ◇ ((X1 ◇ (((X0 ◇ X0) ◇ X1) ◇ X1)) ◇ X0))) := superpose step2369 step15877
  have step16381 (X0 X1 : G) :  (X0 ◇ (X0 ◇ X0)) = ((((X1 ◇ (((X0 ◇ X0) ◇ X1) ◇ X1)) ◇ X0) ◇ (X0 ◇ ((X1 ◇ (((X0 ◇ X0) ◇ X1) ◇ X1)) ◇ X0))) ◇ X0) := superpose step14740 step15145
  have step16565 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ X0) ◇ X0) := superpose step15901 step16381
  have step17208 (X0 : G) :  (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) = ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ ((X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) := superpose step16565 step4629
  have step17209 (X0 X1 : G) :  (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) = (X1 ◇ ((((X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ X1) ◇ X1)) := superpose step16565 step4622
  have step17213 (X0 X1 : G) :  (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) = (X1 ◇ (((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ X1) ◇ X1)) := superpose step1894 step17209
  have step17214 (X0 : G) :  (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) = (((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) ◇ ((X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) := superpose step4982 step17208
  have step17268 (X0 X1 : G) :  ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) = (X1 ◇ ((((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) ◇ X1) ◇ X1)) := superpose step1155 step17213
  have step17269 (X0 : G) :  (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) = (((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) := superpose step1894 step17214
  have step17292 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) := superpose step147 step17268
  have step17293 (X0 : G) :  ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) = (((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)))) := superpose step1155 step17269
  have step17298 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose step17292 step17293
  have step17693 (X0 : G) :  ((((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ X0) ◇ X0) = X0 := superpose step17298 step3833
  have step17694 (X0 : G) :  ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) ◇ X0) = X0 := superpose step17298 step17693
  have step17781 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ X0) = X0 := superpose step17298 step17694
  have step18638 : sK0 ≠ sK0 := superpose step17781 step10
  subsumption step18638 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation633_implies_Equation3659 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation633 G) : Equation3659 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X1))) = X0 := mod_symm (h ..)
  have step10 : (sK0 ◇ sK0) ≠ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step13 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X1))))) = X0 := superpose step9 step9
  have step14 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ ((X0 ◇ X1) ◇ X1)) ◇ X0)) = X0 := superpose step9 step13
  have step15 (X0 X1 : G) :  (X1 ◇ ((X0 ◇ X1) ◇ X1)) = (X0 ◇ ((X1 ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X0 ◇ X0))) := superpose step9 step11
  have step18 (X0 X1 : G) :  (X1 ◇ ((X0 ◇ X1) ◇ X1)) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose step9 step12
  have step19 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step21 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose step11 step12
  have step28 (X0 X1 : G) :  ((X1 ◇ ((X0 ◇ X1) ◇ X1)) ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose step14 step12
  have step30 (X0 X1 : G) :  (X0 ◇ (((X1 ◇ ((X0 ◇ X1) ◇ X1)) ◇ X0) ◇ (X0 ◇ ((X1 ◇ ((X0 ◇ X1) ◇ X1)) ◇ X0)))) = X0 := superpose step14 step9
  have step31 (X0 X1 : G) :  (X0 ◇ (((X1 ◇ ((X0 ◇ X1) ◇ X1)) ◇ X0) ◇ X0)) = X0 := superpose step14 step30
  have step40 (X0 X1 X2 : G) :  (X0 ◇ ((X1 ◇ X0) ◇ X0)) = (X2 ◇ ((X1 ◇ X2) ◇ X2)) := superpose step18 step18
  have step45 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X1) = (X1 ◇ (((X0 ◇ X1) ◇ X1) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X1))) := superpose step18 step11
  have step51 (X0 X1 : G) :  ((X1 ◇ X1) ◇ X1) = ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ ((X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ X1)) := superpose step18 step12
  have step54 (X0 X1 : G) :  ((X1 ◇ X1) ◇ X1) = ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X1 ◇ X1)) := superpose step9 step51
  have step68 (X0 X1 : G) :  (X1 ◇ ((X0 ◇ X1) ◇ X1)) = ((X1 ◇ ((X0 ◇ X1) ◇ X1)) ◇ X0) := superpose step31 step9
  have step120 (X0 X1 : G) :  ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0))) = (X1 ◇ (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X1) ◇ X1)) := superpose step21 step40
  have step147 (X0 X1 X2 : G) :  (X0 ◇ (((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X0) ◇ X0)) = X2 := superpose step40 step31
  have step158 (X0 : G) :  ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0))) = X0 := superpose step147 step120
  have step189 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ ((X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) ◇ (X1 ◇ (X1 ◇ X0))))) = X1 := superpose step19 step11
  have step257 (X0 X1 X2 : G) :  (X0 ◇ ((X1 ◇ X0) ◇ X1)) = (((X2 ◇ ((X0 ◇ X2) ◇ X2)) ◇ X1) ◇ X1) := superpose step147 step12
  have step343 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) = (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0))) := superpose step158 step12
  have step360 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose step19 step343
  have step438 (X0 : G) :  (((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)))) ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) := superpose step158 step28
  have step543 (X0 : G) :  ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) = (((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ (X0 ◇ X0)) := superpose step19 step438
  have step558 (X0 : G) :  ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) = ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ (X0 ◇ X0)) := superpose step360 step543
  have step1052 (X0 : G) :  ((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)))) = (((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)))) ◇ (X0 ◇ X0)) := superpose step158 step68
  have step1134 (X0 : G) :  ((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) = (((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ (X0 ◇ X0)) := superpose step19 step1052
  have step1148 (X0 : G) :  (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) = ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ (X0 ◇ X0)) := superpose step360 step1134
  have step1155 (X0 : G) :  ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) = (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) := superpose step558 step1148
  have step1893 (X0 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ X0) = (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) := superpose step360 step19
  have step2235 (X0 X1 : G) :  ((X1 ◇ ((X0 ◇ X1) ◇ X1)) ◇ X1) = ((((X0 ◇ X1) ◇ X1) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X1)) ◇ ((((X0 ◇ X1) ◇ X1) ◇ (((X0 ◇ X1) ◇ X1) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X1))) ◇ ((X0 ◇ X1) ◇ X1))) := superpose step45 step19
  have step2253 (X0 X1 : G) :  ((X1 ◇ ((X0 ◇ X1) ◇ X1)) ◇ X1) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X1) := superpose step12 step2235
  have step2325 (X0 : G) :  ((X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ X0) = (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) := superpose step1893 step19
  have step2357 (X0 : G) :  ((X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ X0) = (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) := superpose step1155 step2325
  have step2369 (X0 : G) :  (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ X0) = (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) := superpose step1893 step2357
  have step3244 (X0 X1 X2 : G) :  ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X2) = ((X1 ◇ ((X1 ◇ X1) ◇ X1)) ◇ X2) := superpose step40 step2253
  have step3800 (X0 X1 X2 : G) :  (((X0 ◇ (((X1 ◇ X2) ◇ X0) ◇ X0)) ◇ X1) ◇ X1) = X2 := superpose step257 step12
  have step3835 (X0 X1 X2 : G) :  (((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X2 ◇ X1)) ◇ (X2 ◇ X1)) = ((X2 ◇ (X2 ◇ X1)) ◇ X2) := superpose step257 step19
  have step4607 (X0 X1 X2 : G) :  ((X1 ◇ (((X2 ◇ X0) ◇ X1) ◇ X1)) ◇ X2) = (((X1 ◇ (((X2 ◇ X0) ◇ X1) ◇ X1)) ◇ X2) ◇ (X2 ◇ (X0 ◇ X2))) := superpose step3800 step9
  have step4623 (X0 X1 X2 X3 : G) :  (X1 ◇ ((((X2 ◇ (((X3 ◇ X0) ◇ X2) ◇ X2)) ◇ X3) ◇ X1) ◇ X1)) = (X3 ◇ (X0 ◇ X3)) := superpose step3800 step40
  have step4630 (X0 X1 X2 : G) :  (X1 ◇ (X0 ◇ X1)) = ((X1 ◇ (X0 ◇ X1)) ◇ ((X2 ◇ (((X1 ◇ X0) ◇ X2) ◇ X2)) ◇ X1)) := superpose step3800 step68
  have step4983 (X0 X1 X2 : G) :  ((((X1 ◇ (X1 ◇ X0)) ◇ X1) ◇ (X0 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1))) ◇ X2) = (((X1 ◇ X0) ◇ (((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0))) ◇ X2) := superpose step12 step3244
  have step5062 (X0 X1 X2 X3 : G) :  ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X2) = ((X3 ◇ ((X1 ◇ X3) ◇ X3)) ◇ X2) := superpose step3244 step3244
  have step11544 (X0 X1 : G) :  ((X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ X0) = (((X1 ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ X1) ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) := superpose step1893 step3835
  have step11791 (X0 X1 : G) :  ((X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ X0) = ((X1 ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ X1) ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) := superpose step68 step11544
  have step11907 (X0 X1 : G) :  ((X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ X0) = (X1 ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ X1) ◇ X1)) := superpose step68 step11791
  have step11937 (X0 X1 : G) :  (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ X0) = (X1 ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ X1) ◇ X1)) := superpose step1893 step11907
  have step12018 (X0 : G) :  ((X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ (X0 ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))))) = X0 := superpose step1893 step189
  have step12153 (X0 : G) :  (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) = X0 := superpose step1893 step12018
  have step12208 (X0 : G) :  (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))))) = X0 := superpose step28 step12153
  have step12231 (X0 : G) :  (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ X0))) = X0 := superpose step11937 step12208
  have step12260 (X0 X1 : G) :  (((X1 ◇ (X1 ◇ X1)) ◇ X1) ◇ (X0 ◇ (((X1 ◇ (X1 ◇ X1)) ◇ X0) ◇ X0))) = X1 := superpose step40 step12231
  have step14434 (X0 X1 : G) :  (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (((X1 ◇ (((X0 ◇ X0) ◇ X1) ◇ X1)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ ((X1 ◇ (((X0 ◇ X0) ◇ X1) ◇ X1)) ◇ X0)))) = X0 := superpose step4630 step12260
  have step14435 (X0 X1 X2 : G) :  (((X2 ◇ (((X0 ◇ (X1 ◇ X0)) ◇ X2) ◇ X2)) ◇ X0) ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ ((X2 ◇ (((X0 ◇ (X1 ◇ X0)) ◇ X2) ◇ X2)) ◇ X0))) = X1 := superpose step4630 step147
  have step14442 (X0 X1 X2 X3 : G) :  (X0 ◇ ((X1 ◇ X0) ◇ X0)) = ((X2 ◇ ((X1 ◇ X2) ◇ X2)) ◇ ((X3 ◇ (((X0 ◇ (X1 ◇ X0)) ◇ X3) ◇ X3)) ◇ X0)) := superpose step4630 step5062
  have step14554 (X0 X1 X2 : G) :  (((X2 ◇ (((X0 ◇ (X1 ◇ X0)) ◇ X2) ◇ X2)) ◇ X0) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) = X1 := superpose step14442 step14435
  have step14555 (X0 X1 : G) :  (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (((X1 ◇ (((X0 ◇ X0) ◇ X1) ◇ X1)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0)))) = X0 := superpose step4630 step14434
  have step14749 (X0 X1 X2 : G) :  ((X2 ◇ (((X0 ◇ (X1 ◇ X0)) ◇ X2) ◇ X2)) ◇ X0) = X1 := superpose step4607 step14554
  have step14750 (X0 X1 : G) :  (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X1 ◇ (((X0 ◇ X0) ◇ X1) ◇ X1)) ◇ X0)) = X0 := superpose step4607 step14555
  have step15156 (X0 X1 : G) :  (X0 ◇ (X0 ◇ X0)) = ((X1 ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ X1) ◇ X1)) ◇ X0) := superpose step1893 step14749
  have step15746 (X0 X1 : G) :  (((X1 ◇ (((X0 ◇ X0) ◇ X1) ◇ X1)) ◇ X0) ◇ (X0 ◇ ((X1 ◇ (((X0 ◇ X0) ◇ X1) ◇ X1)) ◇ X0))) = (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((((X1 ◇ (((X0 ◇ X0) ◇ X1) ◇ X1)) ◇ X0) ◇ (X0 ◇ ((X1 ◇ (((X0 ◇ X0) ◇ X1) ◇ X1)) ◇ X0))) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) := superpose step14750 step15
  have step15771 (X0 X1 : G) :  ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) = ((((X1 ◇ (((X0 ◇ X0) ◇ X1) ◇ X1)) ◇ X0) ◇ (X0 ◇ ((X1 ◇ (((X0 ◇ X0) ◇ X1) ◇ X1)) ◇ X0))) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) := superpose step14750 step54
  have step15811 (X0 X1 : G) :  (((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) = ((((X1 ◇ (((X0 ◇ X0) ◇ X1) ◇ X1)) ◇ X0) ◇ (X0 ◇ ((X1 ◇ (((X0 ◇ X0) ◇ X1) ◇ X1)) ◇ X0))) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)))) := superpose step1155 step15771
  have step15828 (X0 X1 : G) :  (((X1 ◇ (((X0 ◇ X0) ◇ X1) ◇ X1)) ◇ X0) ◇ (X0 ◇ ((X1 ◇ (((X0 ◇ X0) ◇ X1) ◇ X1)) ◇ X0))) = (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((((X1 ◇ (((X0 ◇ X0) ◇ X1) ◇ X1)) ◇ X0) ◇ (X0 ◇ ((X1 ◇ (((X0 ◇ X0) ◇ X1) ◇ X1)) ◇ X0))) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))))) := superpose step1155 step15746
  have step15888 (X0 X1 : G) :  (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) = (((X1 ◇ (((X0 ◇ X0) ◇ X1) ◇ X1)) ◇ X0) ◇ (X0 ◇ ((X1 ◇ (((X0 ◇ X0) ◇ X1) ◇ X1)) ◇ X0))) := superpose step15811 step15828
  have step15912 (X0 X1 : G) :  (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ X0) = (((X1 ◇ (((X0 ◇ X0) ◇ X1) ◇ X1)) ◇ X0) ◇ (X0 ◇ ((X1 ◇ (((X0 ◇ X0) ◇ X1) ◇ X1)) ◇ X0))) := superpose step2369 step15888
  have step16392 (X0 X1 : G) :  (X0 ◇ (X0 ◇ X0)) = ((((X1 ◇ (((X0 ◇ X0) ◇ X1) ◇ X1)) ◇ X0) ◇ (X0 ◇ ((X1 ◇ (((X0 ◇ X0) ◇ X1) ◇ X1)) ◇ X0))) ◇ X0) := superpose step14750 step15156
  have step16576 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ X0) ◇ X0) := superpose step15912 step16392
  have step17164 (X0 : G) :  (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) = ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ ((X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) := superpose step16576 step4630
  have step17165 (X0 X1 : G) :  (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) = (X1 ◇ ((((X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ X1) ◇ X1)) := superpose step16576 step4623
  have step17258 (X0 X1 : G) :  (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) = (X1 ◇ (((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ X1) ◇ X1)) := superpose step1893 step17165
  have step17259 (X0 : G) :  (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) = (((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) ◇ ((X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) := superpose step4983 step17164
  have step17292 (X0 X1 : G) :  ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) = (X1 ◇ ((((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) ◇ X1) ◇ X1)) := superpose step1155 step17258
  have step17293 (X0 : G) :  (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) = (((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) := superpose step1893 step17259
  have step17307 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) := superpose step147 step17292
  have step17308 (X0 : G) :  ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) = (((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)))) := superpose step1155 step17293
  have step17310 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose step17307 step17308
  have step17609 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose step17310 step10
  subsumption step17609 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation640_implies_Equation1426 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation640 G) : Equation1426 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step17 (X0 X1 : G) :  (X1 ◇ ((X1 ◇ X0) ◇ X1)) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose step9 step12
  have step18 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step23 (X0 X1 X2 : G) :  (X0 ◇ ((X0 ◇ X1) ◇ X0)) = (X2 ◇ ((X2 ◇ X1) ◇ X2)) := superpose step17 step17
  have step26 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X1) = (X1 ◇ (((X1 ◇ X0) ◇ X1) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X1))) := superpose step17 step11
  have step27 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X1) = (((X1 ◇ X0) ◇ X1) ◇ (X1 ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X1))) := superpose step17 step9
  have step52 (X0 X1 X2 : G) :  (X0 ◇ (X0 ◇ X0)) = (X1 ◇ ((X1 ◇ (X2 ◇ ((X2 ◇ X0) ◇ X2))) ◇ X1)) := superpose step9 step23
  have step53 (X0 X1 X2 : G) :  (X1 ◇ ((X1 ◇ (X0 ◇ ((X2 ◇ X0) ◇ X2))) ◇ X1)) = (X2 ◇ (X0 ◇ X2)) := superpose step11 step23
  have step77 (X0 X1 X2 : G) :  ((X2 ◇ X1) ◇ X2) = ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ ((X2 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X0))) ◇ X2)) := superpose step23 step12
  have step92 (X0 X1 X2 : G) :  (X2 ◇ ((X2 ◇ (X1 ◇ X0)) ◇ X2)) = (X1 ◇ (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)))) := superpose step18 step23
  have step334 (X0 X1 X2 : G) :  ((X2 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X0))) ◇ X2) = ((X0 ◇ (X1 ◇ X0)) ◇ ((X2 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X2)) := superpose step53 step12
  have step802 (X0 X1 : G) :  ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X0) = ((((X0 ◇ X1) ◇ X0) ◇ ((X1 ◇ ((X1 ◇ X1) ◇ X1)) ◇ X0)) ◇ ((((X0 ◇ X1) ◇ X0) ◇ (((X0 ◇ X1) ◇ X0) ◇ ((X1 ◇ ((X1 ◇ X1) ◇ X1)) ◇ X0))) ◇ ((X0 ◇ X1) ◇ X0))) := superpose step26 step18
  have step813 (X0 X1 : G) :  ((X1 ◇ ((X1 ◇ X1) ◇ X1)) ◇ X0) = ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X0) := superpose step12 step802
  have step877 (X0 X1 X2 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ X2) = (((X1 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (((X1 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X1 ◇ ((X1 ◇ X0) ◇ X1))) ◇ (X1 ◇ ((X1 ◇ X0) ◇ X1)))) ◇ X2) := superpose step52 step813
  have step960 (X0 X1 X2 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ X2) = ((((X1 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X0) ◇ (X1 ◇ ((X1 ◇ X0) ◇ X1))) ◇ X2) := superpose step77 step877
  have step1024 (X0 X1 X2 : G) :  (((X2 ◇ ((X2 ◇ X2) ◇ X2)) ◇ X2) ◇ (X2 ◇ ((X2 ◇ X2) ◇ X2))) = ((((X2 ◇ ((X2 ◇ X2) ◇ X2)) ◇ X2) ◇ (X2 ◇ ((X2 ◇ X2) ◇ X2))) ◇ (X0 ◇ ((X0 ◇ (X1 ◇ ((X1 ◇ (X2 ◇ ((X2 ◇ X2) ◇ X2))) ◇ X1))) ◇ X0))) := superpose step52 step27
  have step1052 (X0 X1 X2 : G) :  (((X2 ◇ ((X2 ◇ X2) ◇ X2)) ◇ X2) ◇ (X2 ◇ ((X2 ◇ X2) ◇ X2))) = ((X2 ◇ (X2 ◇ X2)) ◇ (X0 ◇ ((X0 ◇ (X1 ◇ ((X1 ◇ (X2 ◇ ((X2 ◇ X2) ◇ X2))) ◇ X1))) ◇ X0))) := superpose step960 step1024
  have step1086 (X0 X2 : G) :  (((X2 ◇ ((X2 ◇ X2) ◇ X2)) ◇ X2) ◇ (X2 ◇ ((X2 ◇ X2) ◇ X2))) = ((X2 ◇ (X2 ◇ X2)) ◇ (X0 ◇ ((X0 ◇ (X2 ◇ (X2 ◇ X2))) ◇ X0))) := superpose step53 step1052
  have step1103 (X2 : G) :  (X2 ◇ (X2 ◇ X2)) = (((X2 ◇ ((X2 ◇ X2) ◇ X2)) ◇ X2) ◇ (X2 ◇ ((X2 ◇ X2) ◇ X2))) := superpose step9 step1086
  have step8996 (X0 : G) :  (X0 ◇ ((X0 ◇ X0) ◇ X0)) = ((X0 ◇ (X0 ◇ X0)) ◇ ((((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0))) := superpose step1103 step12
  have step9090 (X0 : G) :  (X0 ◇ ((X0 ◇ X0) ◇ X0)) = ((((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0)) := superpose step334 step8996
  have step9155 (X0 : G) :  (X0 ◇ ((X0 ◇ X0) ◇ X0)) = ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0)) := superpose step960 step9090
  have step15597 (X0 X1 : G) :  (X1 ◇ ((X1 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ X1)) = ((X0 ◇ (X0 ◇ X0)) ◇ (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) ◇ (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))))) := superpose step9155 step92
  have step15664 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ X0) = (X1 ◇ ((X1 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ X1)) := superpose step12 step15597
  have step15735 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose step53 step15664
  have step16304 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose step15735 step12
  have step17079 : sK0 ≠ sK0 := superpose step16304 step10
  subsumption step17079 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation640_implies_Equation255 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation640 G) : Equation255 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ (((sK0 ◇ sK0) ◇ sK0) ◇ sK0) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step13 (X0 X1 : G) :  (X1 ◇ ((X1 ◇ X0) ◇ X1)) = ((X1 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X0 ◇ (X0 ◇ X0))) := superpose step9 step9
  have step15 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ X0) ◇ X1)) = (X1 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X0 ◇ X1))) := superpose step11 step11
  have step17 (X0 X1 : G) :  (X1 ◇ ((X1 ◇ X0) ◇ X1)) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose step9 step12
  have step18 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step20 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose step11 step12
  have step23 (X0 X1 X2 : G) :  (X0 ◇ ((X0 ◇ X1) ◇ X0)) = (X2 ◇ ((X2 ◇ X1) ◇ X2)) := superpose step17 step17
  have step25 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X1) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X1 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ X1)) := superpose step17 step12
  have step26 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X1) = (X1 ◇ (((X1 ◇ X0) ◇ X1) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X1))) := superpose step17 step11
  have step27 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X1) = (((X1 ◇ X0) ◇ X1) ◇ (X1 ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X1))) := superpose step17 step9
  have step30 (X0 X1 : G) :  ((X1 ◇ X1) ◇ X1) = ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ ((X1 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X0))) ◇ X1)) := superpose step17 step12
  have step33 (X0 X1 : G) :  ((X1 ◇ X1) ◇ X1) = ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ (X1 ◇ X1)) := superpose step9 step30
  have step52 (X0 X1 X2 : G) :  (X0 ◇ (X0 ◇ X0)) = (X1 ◇ ((X1 ◇ (X2 ◇ ((X2 ◇ X0) ◇ X2))) ◇ X1)) := superpose step9 step23
  have step53 (X0 X1 X2 : G) :  (X1 ◇ ((X1 ◇ (X0 ◇ ((X2 ◇ X0) ◇ X2))) ◇ X1)) = (X2 ◇ (X0 ◇ X2)) := superpose step11 step23
  have step54 (X0 X1 X2 : G) :  (X1 ◇ ((X1 ◇ ((X2 ◇ (X2 ◇ X0)) ◇ X2)) ◇ X1)) = ((X2 ◇ X0) ◇ (X0 ◇ (X2 ◇ X0))) := superpose step12 step23
  have step56 (X0 X1 X2 X3 : G) :  (X2 ◇ ((X2 ◇ ((X3 ◇ X1) ◇ X3)) ◇ X2)) = (X3 ◇ ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X3)) := superpose step23 step23
  have step57 (X0 X1 X2 : G) :  (X1 ◇ ((X1 ◇ ((X2 ◇ X0) ◇ X2)) ◇ X1)) = (X2 ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X2)) := superpose step17 step23
  have step77 (X0 X1 X2 : G) :  ((X2 ◇ X1) ◇ X2) = ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ ((X2 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X0))) ◇ X2)) := superpose step23 step12
  have step88 (X0 : G) :  (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) = ((X0 ◇ X0) ◇ ((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0))) := superpose step20 step18
  have step92 (X0 X1 X2 : G) :  (X2 ◇ ((X2 ◇ (X1 ◇ X0)) ◇ X2)) = (X1 ◇ (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)))) := superpose step18 step23
  have step94 (X0 X1 : G) :  (X1 ◇ X0) = ((X1 ◇ X0) ◇ (X1 ◇ (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))))) := superpose step18 step9
  have step97 (X0 X1 : G) :  ((X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) ◇ (((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)))) ◇ (X1 ◇ (X1 ◇ X0)))) = X1 := superpose step18 step12
  have step104 (X0 X1 : G) :  (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) = (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ ((X1 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) ◇ X1)) := superpose step18 step12
  have step128 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ ((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0))) := superpose step33 step11
  have step157 (X0 : G) :  (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) = ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0)))))) := superpose step13 step9
  have step158 (X0 : G) :  (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) = ((X0 ◇ (X0 ◇ X0)) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0)))))) := superpose step13 step11
  have step161 (X0 : G) :  (((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0)))) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0)))) = (((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))))) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))))) := superpose step13 step33
  have step171 (X0 : G) :  (((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0)))) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0)))) = (((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))))) := superpose step17 step161
  have step174 (X0 : G) :  (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) = ((X0 ◇ (X0 ◇ X0)) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) := superpose step17 step158
  have step175 (X0 : G) :  (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) = ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) := superpose step17 step157
  have step230 (X0 X1 X2 X3 : G) :  (X1 ◇ ((X1 ◇ ((X2 ◇ (X3 ◇ ((X3 ◇ X0) ◇ X3))) ◇ X2)) ◇ X1)) = (X2 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X2)) := superpose step52 step23
  have step334 (X0 X1 X2 : G) :  ((X2 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X0))) ◇ X2) = ((X0 ◇ (X1 ◇ X0)) ◇ ((X2 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X2)) := superpose step53 step12
  have step391 (X0 X1 : G) :  ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X0 ◇ X1)) = (((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X0 ◇ X1)) ◇ (X1 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X1))) := superpose step15 step9
  have step802 (X0 X1 : G) :  ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X0) = ((((X0 ◇ X1) ◇ X0) ◇ ((X1 ◇ ((X1 ◇ X1) ◇ X1)) ◇ X0)) ◇ ((((X0 ◇ X1) ◇ X0) ◇ (((X0 ◇ X1) ◇ X0) ◇ ((X1 ◇ ((X1 ◇ X1) ◇ X1)) ◇ X0))) ◇ ((X0 ◇ X1) ◇ X0))) := superpose step26 step18
  have step813 (X0 X1 : G) :  ((X1 ◇ ((X1 ◇ X1) ◇ X1)) ◇ X0) = ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X0) := superpose step12 step802
  have step864 (X0 X1 X2 : G) :  ((X2 ◇ ((X2 ◇ X1) ◇ X2)) ◇ X2) = ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X2) := superpose step17 step813
  have step865 (X0 X1 X2 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ X2) = ((X2 ◇ ((X2 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X1))) ◇ X2)) ◇ X2) := superpose step52 step813
  have step876 (X0 X1 X2 : G) :  ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X2) = ((X1 ◇ ((X1 ◇ X1) ◇ X1)) ◇ X2) := superpose step23 step813
  have step877 (X0 X1 X2 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ X2) = (((X1 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (((X1 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X1 ◇ ((X1 ◇ X0) ◇ X1))) ◇ (X1 ◇ ((X1 ◇ X0) ◇ X1)))) ◇ X2) := superpose step52 step813
  have step960 (X0 X1 X2 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ X2) = ((((X1 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X0) ◇ (X1 ◇ ((X1 ◇ X0) ◇ X1))) ◇ X2) := superpose step77 step877
  have step1024 (X0 X1 X2 : G) :  (((X2 ◇ ((X2 ◇ X2) ◇ X2)) ◇ X2) ◇ (X2 ◇ ((X2 ◇ X2) ◇ X2))) = ((((X2 ◇ ((X2 ◇ X2) ◇ X2)) ◇ X2) ◇ (X2 ◇ ((X2 ◇ X2) ◇ X2))) ◇ (X0 ◇ ((X0 ◇ (X1 ◇ ((X1 ◇ (X2 ◇ ((X2 ◇ X2) ◇ X2))) ◇ X1))) ◇ X0))) := superpose step52 step27
  have step1052 (X0 X1 X2 : G) :  (((X2 ◇ ((X2 ◇ X2) ◇ X2)) ◇ X2) ◇ (X2 ◇ ((X2 ◇ X2) ◇ X2))) = ((X2 ◇ (X2 ◇ X2)) ◇ (X0 ◇ ((X0 ◇ (X1 ◇ ((X1 ◇ (X2 ◇ ((X2 ◇ X2) ◇ X2))) ◇ X1))) ◇ X0))) := superpose step960 step1024
  have step1086 (X0 X2 : G) :  (((X2 ◇ ((X2 ◇ X2) ◇ X2)) ◇ X2) ◇ (X2 ◇ ((X2 ◇ X2) ◇ X2))) = ((X2 ◇ (X2 ◇ X2)) ◇ (X0 ◇ ((X0 ◇ (X2 ◇ (X2 ◇ X2))) ◇ X0))) := superpose step53 step1052
  have step1103 (X2 : G) :  (X2 ◇ (X2 ◇ X2)) = (((X2 ◇ ((X2 ◇ X2) ◇ X2)) ◇ X2) ◇ (X2 ◇ ((X2 ◇ X2) ◇ X2))) := superpose step9 step1086
  have step1146 (X0 X1 X2 X3 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ X1) = ((X3 ◇ ((X3 ◇ (X2 ◇ ((X2 ◇ X0) ◇ X2))) ◇ X3)) ◇ X1) := superpose step52 step864
  have step1148 (X0 X1 X2 X3 : G) :  ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X2) = ((X3 ◇ ((X3 ◇ X1) ◇ X3)) ◇ X2) := superpose step864 step864
  have step1180 (X0 X1 X2 : G) :  ((X2 ◇ ((X2 ◇ (X1 ◇ X0)) ◇ X2)) ◇ X2) = ((X1 ◇ (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)))) ◇ X2) := superpose step18 step864
  have step1236 (X0 X1 : G) :  ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ (X1 ◇ (X1 ◇ X1))) = ((X1 ◇ (X1 ◇ X1)) ◇ (((X1 ◇ (X1 ◇ X1)) ◇ X1) ◇ (X1 ◇ (X1 ◇ X1)))) := superpose step864 step13
  have step1279 (X0 X1 : G) :  ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ (X1 ◇ (X1 ◇ X1))) = (X1 ◇ ((X1 ◇ X1) ◇ X1)) := superpose step17 step1236
  have step1391 (X0 X1 X2 : G) :  (((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X0)))) ◇ X2) = (((X1 ◇ (X1 ◇ X1)) ◇ (((X1 ◇ (X1 ◇ X1)) ◇ (X1 ◇ (X1 ◇ X1))) ◇ (X1 ◇ (X1 ◇ X1)))) ◇ X2) := superpose step13 step876
  have step1763 (X0 X1 X2 : G) :  (((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X0)))) ◇ X2) = ((((X1 ◇ (X1 ◇ X1)) ◇ (X1 ◇ ((X1 ◇ X1) ◇ X1))) ◇ (X1 ◇ (X1 ◇ X1))) ◇ X2) := superpose step334 step1391
  have step3828 (X0 X1 X2 : G) :  (X1 ◇ (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X1)) = ((X0 ◇ X1) ◇ ((X2 ◇ ((X2 ◇ X1) ◇ X2)) ◇ (X0 ◇ X1))) := superpose step18 step56
  have step4459 (X0 : G) :  ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) = ((X0 ◇ X0) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0))) := superpose step33 step57
  have step4742 (X0 : G) :  ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) = (X0 ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ X0)) := superpose step3828 step4459
  have step6929 (X0 X1 X2 X3 : G) :  (X1 ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (((X1 ◇ (X2 ◇ ((X2 ◇ X0) ◇ X2))) ◇ (X2 ◇ ((X2 ◇ X0) ◇ X2))) ◇ (X1 ◇ (X2 ◇ ((X2 ◇ X0) ◇ X2)))))) = (X3 ◇ ((X3 ◇ (X1 ◇ (X2 ◇ ((X2 ◇ X0) ◇ X2)))) ◇ X3)) := superpose step876 step92
  have step8957 (X0 : G) :  ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) = X0 := superpose step1103 step11
  have step9008 (X0 : G) :  (X0 ◇ ((X0 ◇ X0) ◇ X0)) = ((X0 ◇ (X0 ◇ X0)) ◇ ((((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0))) := superpose step1103 step12
  have step9102 (X0 : G) :  (X0 ◇ ((X0 ◇ X0) ◇ X0)) = ((((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0)) := superpose step334 step9008
  have step9167 (X0 : G) :  (X0 ◇ ((X0 ◇ X0) ◇ X0)) = ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0)) := superpose step960 step9102
  have step9644 (X0 X1 : G) :  ((X1 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) = X0 := superpose step8957 step1148
  have step14050 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (((X0 ◇ X0) ◇ ((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)))) := superpose step88 step53
  have step14161 (X0 X1 X2 : G) :  (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) ◇ X1) = ((X2 ◇ ((X2 ◇ (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (((X0 ◇ X0) ◇ ((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0))))) ◇ X2)) ◇ X1) := superpose step88 step1146
  have step14180 (X0 X1 X2 : G) :  (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) ◇ X1) = ((X2 ◇ ((X2 ◇ (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0))))) ◇ X2)) ◇ X1) := superpose step128 step14161
  have step14291 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)))) := superpose step128 step14050
  have step14341 (X0 X1 X2 : G) :  ((((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ (X0 ◇ (X0 ◇ X0))) ◇ X1) = ((X2 ◇ ((X2 ◇ (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0))))) ◇ X2)) ◇ X1) := superpose step1763 step14180
  have step14411 (X0 X1 X2 : G) :  ((((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ (X0 ◇ (X0 ◇ X0))) ◇ X1) = ((X2 ◇ ((X2 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X2)) ◇ X1) := superpose step14291 step14341
  have step15547 (X0 X1 X2 : G) :  ((X2 ◇ (X2 ◇ X2)) ◇ (((X2 ◇ (X2 ◇ X2)) ◇ (X2 ◇ (X2 ◇ X2))) ◇ (X2 ◇ (X2 ◇ X2)))) = (((X0 ◇ ((X0 ◇ (X1 ◇ ((X1 ◇ X2) ◇ X1))) ◇ X0)) ◇ ((X2 ◇ (X2 ◇ X2)) ◇ (X2 ◇ (X2 ◇ X2)))) ◇ (((X2 ◇ (X2 ◇ X2)) ◇ (((X2 ◇ (X2 ◇ X2)) ◇ (X2 ◇ (X2 ◇ X2))) ◇ (X2 ◇ (X2 ◇ X2)))) ◇ (X2 ◇ (X2 ◇ X2)))) := superpose step1146 step9167
  have step15586 (X0 X1 X2 : G) :  (X0 ◇ ((X0 ◇ X0) ◇ X0)) = ((X1 ◇ ((X1 ◇ (X2 ◇ ((X2 ◇ X0) ◇ X2))) ◇ X1)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0)) := superpose step9167 step1146
  have step15588 (X0 : G) :  ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))))) := superpose step9167 step11
  have step15589 (X0 : G) :  ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ (X0 ◇ (X0 ◇ X0)))) := superpose step9167 step12
  have step15596 (X0 : G) :  (((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ (X0 ◇ (X0 ◇ X0))) = (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) ◇ (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) := superpose step9167 step18
  have step15605 (X0 : G) :  ((((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0)) = (((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))) ◇ (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0))) := superpose step9167 step33
  have step15608 (X0 X1 : G) :  ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) = (X1 ◇ ((X1 ◇ (((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ (X0 ◇ (X0 ◇ X0)))) ◇ X1)) := superpose step9167 step54
  have step15618 (X0 X1 : G) :  (X1 ◇ ((X1 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ X1)) = ((X0 ◇ (X0 ◇ X0)) ◇ (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) ◇ (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))))) := superpose step9167 step92
  have step15635 (X0 : G) :  ((((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))) ◇ (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0)))) = (((((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))) ◇ (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0)))) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ ((((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))) ◇ (X0 ◇ (X0 ◇ X0))))) := superpose step9167 step391
  have step15668 (X0 : G) :  ((((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0)))) = (((((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0)))) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ ((((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ (X0 ◇ (X0 ◇ X0))))) := superpose step13 step15635
  have step15685 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ X0) = (X1 ◇ ((X1 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ X1)) := superpose step12 step15618
  have step15695 (X0 : G) :  ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) = ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))) := superpose step230 step15608
  have step15698 (X0 : G) :  ((((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0)) = (((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0))) := superpose step13 step15605
  have step15707 (X0 : G) :  (((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose step12 step15596
  have step15714 (X0 : G) :  (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) := superpose step77 step15589
  have step15715 (X0 : G) :  ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) := superpose step13 step15588
  have step15737 (X0 X1 X2 : G) :  ((X2 ◇ (X2 ◇ X2)) ◇ (((X2 ◇ (X2 ◇ X2)) ◇ (X2 ◇ (X2 ◇ X2))) ◇ (X2 ◇ (X2 ◇ X2)))) = (((X0 ◇ ((X0 ◇ (X1 ◇ ((X1 ◇ X2) ◇ X1))) ◇ X0)) ◇ ((X2 ◇ (X2 ◇ X2)) ◇ (X2 ◇ (X2 ◇ X2)))) ◇ ((((X2 ◇ (X2 ◇ X2)) ◇ (X2 ◇ ((X2 ◇ X2) ◇ X2))) ◇ (X2 ◇ (X2 ◇ X2))) ◇ (X2 ◇ (X2 ◇ X2)))) := superpose step14411 step15547
  have step15748 (X0 : G) :  ((((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0)))) = (((((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0)))) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))))) := superpose step960 step15668
  have step15756 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose step53 step15685
  have step15760 (X0 : G) :  (X0 ◇ ((X0 ◇ X0) ◇ X0)) = ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))) := superpose step17 step15695
  have step15769 (X0 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) := superpose step1103 step15715
  have step15787 (X0 X1 X2 : G) :  ((X2 ◇ (X2 ◇ X2)) ◇ (((X2 ◇ (X2 ◇ X2)) ◇ (X2 ◇ (X2 ◇ X2))) ◇ (X2 ◇ (X2 ◇ X2)))) = (((X0 ◇ ((X0 ◇ (X1 ◇ ((X1 ◇ X2) ◇ X1))) ◇ X0)) ◇ ((X2 ◇ (X2 ◇ X2)) ◇ (X2 ◇ (X2 ◇ X2)))) ◇ (X2 ◇ (X2 ◇ (X2 ◇ X2)))) := superpose step15707 step15737
  have step15797 (X0 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0)))) = (((X0 ◇ (X0 ◇ X0)) ◇ (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0)))) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))))) := superpose step960 step15748
  have step15818 (X0 X1 X2 : G) :  ((X2 ◇ (X2 ◇ X2)) ◇ (((X2 ◇ ((X2 ◇ X2) ◇ X2)) ◇ X2) ◇ (X2 ◇ (X2 ◇ X2)))) = (((X0 ◇ ((X0 ◇ (X1 ◇ ((X1 ◇ X2) ◇ X1))) ◇ X0)) ◇ ((X2 ◇ ((X2 ◇ X2) ◇ X2)) ◇ X2)) ◇ (X2 ◇ (X2 ◇ (X2 ◇ X2)))) := superpose step15769 step15787
  have step15825 (X0 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0)))) = (((X0 ◇ (X0 ◇ X0)) ◇ (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0)))) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) := superpose step15760 step15797
  have step15836 (X2 : G) :  ((X2 ◇ ((X2 ◇ X2) ◇ X2)) ◇ (X2 ◇ (X2 ◇ (X2 ◇ X2)))) = ((X2 ◇ (X2 ◇ X2)) ◇ (((X2 ◇ ((X2 ◇ X2) ◇ X2)) ◇ X2) ◇ (X2 ◇ (X2 ◇ X2)))) := superpose step15586 step15818
  have step15847 (X2 : G) :  ((X2 ◇ (X2 ◇ X2)) ◇ (((X2 ◇ ((X2 ◇ X2) ◇ X2)) ◇ X2) ◇ (X2 ◇ (X2 ◇ X2)))) = X2 := superpose step9644 step15836
  have step16325 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose step15756 step12
  have step16333 (X0 : G) :  ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) = (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) := superpose step15756 step4742
  have step16341 (X0 X1 : G) :  (X1 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X1)) = (X0 ◇ (X0 ◇ (X0 ◇ X0))) := superpose step15756 step23
  have step16373 (X0 X1 X2 : G) :  ((X1 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X1)) ◇ X2) = ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X2) := superpose step15756 step1148
  have step16547 (X0 : G) :  ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) = (X0 ◇ (X0 ◇ (X0 ◇ X0))) := superpose step16341 step16333
  have step16634 (X0 : G) :  ((((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))))) = (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) ◇ (((((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))))) ◇ (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))))) := superpose step25 step174
  have step16703 (X0 : G) :  (((X0 ◇ (X0 ◇ X0)) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ X0)))) ◇ (((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ (((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))))) = (((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))))) := superpose step174 step1279
  have step16714 (X0 : G) :  (((X0 ◇ (X0 ◇ X0)) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ X0)))) ◇ (((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ (((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))))) = ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))))) := superpose step6929 step16703
  have step16775 (X0 : G) :  ((((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))))) = ((((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (((((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))))) ◇ (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))))) := superpose step1763 step16634
  have step16804 (X0 : G) :  (((X0 ◇ (X0 ◇ X0)) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ X0)))) ◇ (((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ (((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))))) = ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ X0) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))))) := superpose step77 step16714
  have step16862 (X0 : G) :  ((((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))))) = ((((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (((((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))))) ◇ (X0 ◇ (X0 ◇ X0)))) := superpose step1103 step16775
  have step16888 (X0 : G) :  (((X0 ◇ (X0 ◇ X0)) ◇ (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0)))) ◇ ((((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))))) = (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) ◇ (((((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ X0) ◇ (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))))) := superpose step15714 step16804
  have step16941 (X0 : G) :  (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) = ((((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ (X0 ◇ (X0 ◇ X0)))) := superpose step15714 step16862
  have step16958 (X0 : G) :  (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0)))) = (((X0 ◇ (X0 ◇ X0)) ◇ (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0)))) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))))) := superpose step1103 step16888
  have step16992 (X0 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) = ((((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ (X0 ◇ (X0 ◇ X0)))) := superpose step865 step16941
  have step17000 (X0 : G) :  (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0)))) = (((X0 ◇ (X0 ◇ X0)) ◇ (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0)))) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) := superpose step15760 step16958
  have step17027 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) := superpose step15707 step16992
  have step17031 (X0 : G) :  (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0)))) = ((X0 ◇ (X0 ◇ X0)) ◇ (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0)))) := superpose step15825 step17000
  have step17051 (X0 : G) :  (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0)))) = X0 := superpose step15847 step17031
  have step17064 (X0 : G) :  (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0)) = X0 := superpose step15714 step17051
  have step17147 (X0 : G) :  (X0 ◇ ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0)))) = X0 := superpose step16325 step94
  have step17214 (X0 : G) :  (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = X0 := superpose step12 step17147
  have step17316 (X0 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) = (((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) := superpose step15756 step175
  have step17395 (X0 : G) :  (((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0)))) = ((((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0)))) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0)))) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ (((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0)))) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))))) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))))) := superpose step175 step104
  have step17448 (X0 : G) :  (((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0)) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0)))) = ((((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0)))) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0)))) ◇ (((X0 ◇ X0) ◇ (((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0)))) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))))) ◇ (X0 ◇ X0))) := superpose step17027 step17395
  have step17505 (X0 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) = (((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0)) := superpose step17027 step17316
  have step17528 (X0 : G) :  (((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0)) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0)))) = ((((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))))) ◇ (((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0)))))) ◇ (X0 ◇ X0))) := superpose step171 step17448
  have step17580 (X0 : G) :  ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) = (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) ◇ (X0 ◇ X0)) := superpose step15769 step17505
  have step17602 (X0 : G) :  ((((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0)) = ((((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0))) ◇ (((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0)))) ◇ (X0 ◇ X0))) := superpose step15714 step17528
  have step17658 (X0 : G) :  ((((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0)) = (((((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0)) ◇ (((X0 ◇ X0) ◇ ((((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0))) ◇ (X0 ◇ X0))) := superpose step15698 step17602
  have step17689 (X0 : G) :  ((((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0)) = ((X0 ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0)) ◇ (((X0 ◇ X0) ◇ (X0 ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0))) ◇ (X0 ◇ X0))) := superpose step17064 step17658
  have step17707 (X0 : G) :  (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) = ((((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0)) := superpose step77 step17689
  have step17718 (X0 : G) :  (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) = (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0)) := superpose step17580 step17707
  have step17726 (X0 : G) :  (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) = X0 := superpose step17064 step17718
  have step17732 (X0 : G) :  ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0)) = X0 := superpose step16547 step17726
  have step17762 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ X0)) := superpose step17214 step18
  have step17788 (X0 : G) :  ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ X0)) ◇ (((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ X0))) ◇ (X0 ◇ X0))) = X0 := superpose step17214 step97
  have step17851 (X0 : G) :  ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0))) = X0 := superpose step17214 step17788
  have step17864 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := superpose step17214 step17762
  have step17880 (X0 : G) :  ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)))) ◇ (X0 ◇ X0))) = X0 := superpose step1180 step17851
  have step17898 (X0 : G) :  ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ (X0 ◇ X0))) = X0 := superpose step18 step17880
  have step17913 (X0 : G) :  ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0))) = X0 := superpose step16373 step17898
  have step17924 (X0 : G) :  ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) ◇ X0) = X0 := superpose step17732 step17913
  have step17933 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ X0) = X0 := superpose step17864 step17924
  have step18649 : sK0 ≠ sK0 := superpose step17933 step10
  subsumption step18649 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation640_implies_Equation817 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation640 G) : Equation817 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step17 (X0 X1 : G) :  (X1 ◇ ((X1 ◇ X0) ◇ X1)) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose step9 step12
  have step18 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step23 (X0 X1 X2 : G) :  (X0 ◇ ((X0 ◇ X1) ◇ X0)) = (X2 ◇ ((X2 ◇ X1) ◇ X2)) := superpose step17 step17
  have step26 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X1) = (X1 ◇ (((X1 ◇ X0) ◇ X1) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X1))) := superpose step17 step11
  have step27 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X1) = (((X1 ◇ X0) ◇ X1) ◇ (X1 ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X1))) := superpose step17 step9
  have step52 (X0 X1 X2 : G) :  (X0 ◇ (X0 ◇ X0)) = (X1 ◇ ((X1 ◇ (X2 ◇ ((X2 ◇ X0) ◇ X2))) ◇ X1)) := superpose step9 step23
  have step53 (X0 X1 X2 : G) :  (X1 ◇ ((X1 ◇ (X0 ◇ ((X2 ◇ X0) ◇ X2))) ◇ X1)) = (X2 ◇ (X0 ◇ X2)) := superpose step11 step23
  have step77 (X0 X1 X2 : G) :  ((X2 ◇ X1) ◇ X2) = ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ ((X2 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X0))) ◇ X2)) := superpose step23 step12
  have step92 (X0 X1 X2 : G) :  (X2 ◇ ((X2 ◇ (X1 ◇ X0)) ◇ X2)) = (X1 ◇ (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)))) := superpose step18 step23
  have step94 (X0 X1 : G) :  (X1 ◇ X0) = ((X1 ◇ X0) ◇ (X1 ◇ (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))))) := superpose step18 step9
  have step334 (X0 X1 X2 : G) :  ((X2 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X0))) ◇ X2) = ((X0 ◇ (X1 ◇ X0)) ◇ ((X2 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X2)) := superpose step53 step12
  have step802 (X0 X1 : G) :  ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X0) = ((((X0 ◇ X1) ◇ X0) ◇ ((X1 ◇ ((X1 ◇ X1) ◇ X1)) ◇ X0)) ◇ ((((X0 ◇ X1) ◇ X0) ◇ (((X0 ◇ X1) ◇ X0) ◇ ((X1 ◇ ((X1 ◇ X1) ◇ X1)) ◇ X0))) ◇ ((X0 ◇ X1) ◇ X0))) := superpose step26 step18
  have step813 (X0 X1 : G) :  ((X1 ◇ ((X1 ◇ X1) ◇ X1)) ◇ X0) = ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X0) := superpose step12 step802
  have step877 (X0 X1 X2 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ X2) = (((X1 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (((X1 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X1 ◇ ((X1 ◇ X0) ◇ X1))) ◇ (X1 ◇ ((X1 ◇ X0) ◇ X1)))) ◇ X2) := superpose step52 step813
  have step960 (X0 X1 X2 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ X2) = ((((X1 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X0) ◇ (X1 ◇ ((X1 ◇ X0) ◇ X1))) ◇ X2) := superpose step77 step877
  have step1024 (X0 X1 X2 : G) :  (((X2 ◇ ((X2 ◇ X2) ◇ X2)) ◇ X2) ◇ (X2 ◇ ((X2 ◇ X2) ◇ X2))) = ((((X2 ◇ ((X2 ◇ X2) ◇ X2)) ◇ X2) ◇ (X2 ◇ ((X2 ◇ X2) ◇ X2))) ◇ (X0 ◇ ((X0 ◇ (X1 ◇ ((X1 ◇ (X2 ◇ ((X2 ◇ X2) ◇ X2))) ◇ X1))) ◇ X0))) := superpose step52 step27
  have step1052 (X0 X1 X2 : G) :  (((X2 ◇ ((X2 ◇ X2) ◇ X2)) ◇ X2) ◇ (X2 ◇ ((X2 ◇ X2) ◇ X2))) = ((X2 ◇ (X2 ◇ X2)) ◇ (X0 ◇ ((X0 ◇ (X1 ◇ ((X1 ◇ (X2 ◇ ((X2 ◇ X2) ◇ X2))) ◇ X1))) ◇ X0))) := superpose step960 step1024
  have step1086 (X0 X2 : G) :  (((X2 ◇ ((X2 ◇ X2) ◇ X2)) ◇ X2) ◇ (X2 ◇ ((X2 ◇ X2) ◇ X2))) = ((X2 ◇ (X2 ◇ X2)) ◇ (X0 ◇ ((X0 ◇ (X2 ◇ (X2 ◇ X2))) ◇ X0))) := superpose step53 step1052
  have step1103 (X2 : G) :  (X2 ◇ (X2 ◇ X2)) = (((X2 ◇ ((X2 ◇ X2) ◇ X2)) ◇ X2) ◇ (X2 ◇ ((X2 ◇ X2) ◇ X2))) := superpose step9 step1086
  have step8996 (X0 : G) :  (X0 ◇ ((X0 ◇ X0) ◇ X0)) = ((X0 ◇ (X0 ◇ X0)) ◇ ((((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0))) := superpose step1103 step12
  have step9090 (X0 : G) :  (X0 ◇ ((X0 ◇ X0) ◇ X0)) = ((((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0)) := superpose step334 step8996
  have step9155 (X0 : G) :  (X0 ◇ ((X0 ◇ X0) ◇ X0)) = ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0)) := superpose step960 step9090
  have step15597 (X0 X1 : G) :  (X1 ◇ ((X1 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ X1)) = ((X0 ◇ (X0 ◇ X0)) ◇ (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) ◇ (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))))) := superpose step9155 step92
  have step15664 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ X0) = (X1 ◇ ((X1 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ X1)) := superpose step12 step15597
  have step15735 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose step53 step15664
  have step16304 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose step15735 step12
  have step17126 (X0 : G) :  (X0 ◇ ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0)))) = X0 := superpose step16304 step94
  have step17193 (X0 : G) :  (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = X0 := superpose step12 step17126
  have step17732 : sK0 ≠ sK0 := superpose step17193 step10
  subsumption step17732 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation643_implies_Equation255 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation643 G) : Equation255 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ (X1 ◇ ((X1 ◇ X1) ◇ X1))) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ (((sK0 ◇ sK0) ◇ sK0) ◇ sK0) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step20 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ X0) ◇ X1)) = (X1 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X0 ◇ X1))) := superpose step11 step11
  have step23 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step184 (X0 : G) :  (X0 ◇ ((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0))) = (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ ((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)))) := superpose step9 step20
  have step189 (X0 : G) :  (X0 ◇ ((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0))) = X0 := superpose step11 step184
  have step204 (X0 : G) :  (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) = X0 := superpose step23 step189
  have step218 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ X0) = X0 := superpose step204 step12
  have step297 : sK0 ≠ sK0 := superpose step218 step10
  subsumption step297 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation667_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation667 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step10 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X1))) = X0 := mod_symm (h ..)
  have step11 : sK0 ≠ sK1 := mod_symm nh
  have step12 (X Y : G) : ((Y ◇ X) ◇ (((Y ◇ X) ◇ (Y ◇ X)) ◇ Y)) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (s ◇ ((s ◇ s) ◇ Y))) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (Y ◇ s)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (Y ◇ s)) (fun s => (s ◇ ((s ◇ s) ◇ Y))) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step13 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step14 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step19 (X0 : G) :  (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose step13 step10
  have step20 (X0 X1 : G) :  ((X0 ◇ (((X1 ◇ X1) ◇ X0) ◇ (X1 ◇ X1))) ◇ (X1 ◇ X0)) = X1 := superpose step13 step10
  have step21 (X0 X1 : G) :  (X0 ◇ ((X0 ◇ X0) ◇ X1)) = (X0 ◇ ((X1 ◇ X0) ◇ X1)) := superpose step10 step14
  have step26 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = ((X1 ◇ X0) ◇ (((X1 ◇ (X1 ◇ X0)) ◇ X1) ◇ (X0 ◇ (X1 ◇ X0)))) := superpose step14 step13
  have step31 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ ((X0 ◇ X0) ◇ (X1 ◇ X0))) := superpose step14 step12
  have step32 (X0 X1 : G) :  (((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ ((X0 ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step66 (X0 X1 : G) :  ((X0 ◇ X0) ◇ X1) = (X0 ◇ (((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X0))) := superpose step21 step13
  have step72 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X1) = ((X0 ◇ ((X0 ◇ X0) ◇ X1)) ◇ ((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X1))) ◇ X0)) := superpose step21 step14
  have step75 (X0 X1 : G) :  ((X0 ◇ X0) ◇ X1) = ((X1 ◇ X0) ◇ X1) := superpose step14 step72
  have step83 (X0 : G) :  ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) = X0 := superpose step14 step20
  have step111 (X0 : G) :  (((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) = X0 := superpose step75 step83
  have step127 (X0 X1 : G) :  (((X0 ◇ X1) ◇ X0) ◇ (((X1 ◇ X1) ◇ ((X0 ◇ X1) ◇ X0)) ◇ (X1 ◇ X1))) = X0 := superpose step75 step14
  have step135 (X0 X1 : G) :  (((X0 ◇ X0) ◇ X1) ◇ (((X1 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) ◇ (X1 ◇ X0))) = X1 := superpose step75 step14
  have step834 (X0 : G) :  ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0)))) = ((X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ (((X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ X0)) := superpose step111 step32
  have step840 (X0 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0)))) := superpose step12 step834
  have step974 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ X0))) := superpose step26 step127
  have step1008 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) := superpose step19 step974
  have step1031 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = (((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) := superpose step75 step1008
  have step1264 (X0 X1 : G) :  ((X0 ◇ ((X0 ◇ X0) ◇ X1)) ◇ X0) = ((((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X0)) ◇ (((((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X0)) ◇ (((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X0))) ◇ ((X0 ◇ X0) ◇ X1))) := superpose step66 step31
  have step1280 (X0 X1 : G) :  ((X0 ◇ ((X0 ◇ X0) ◇ X1)) ◇ X0) = ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X0) := superpose step12 step1264
  have step1917 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) = (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0)))) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))))) ◇ (X0 ◇ (X0 ◇ X0)))) := superpose step1031 step135
  have step1969 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) = (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))) := superpose step840 step1917
  have step2019 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose step14 step1969
  have step2216 (X0 : G) :  (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose step2019 step1031
  have step2551 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) := superpose step2216 step14
  have step2608 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step14 step2551
  have step3028 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X1) = (X0 ◇ X1) := superpose step2608 step75
  have step3033 (X0 X1 : G) :  (((X1 ◇ X0) ◇ X1) ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X0)) = X1 := superpose step2608 step127
  have step3039 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ X1)) ◇ X0) = ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X0) := superpose step2608 step1280
  have step3117 (X0 X1 : G) :  (((X1 ◇ X0) ◇ X1) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) = X1 := superpose step3039 step3033
  have step3157 (X0 X1 : G) :  (((X1 ◇ X0) ◇ X1) ◇ ((X0 ◇ X1) ◇ X0)) = X1 := superpose step3028 step3117
  have step3177 (X0 X1 : G) :  (((X1 ◇ X0) ◇ X1) ◇ (X1 ◇ X0)) = X1 := superpose step3028 step3157
  have step3187 (X0 X1 : G) :  ((X1 ◇ X1) ◇ (X1 ◇ X0)) = X1 := superpose step75 step3177
  have step3192 (X0 X1 : G) :  (X1 ◇ (X1 ◇ X0)) = X1 := superpose step2608 step3187
  have step3356 (X0 X1 : G) :  (X1 ◇ X0) = X1 := superpose step13 step3192
  have step3442 (X0 X1 : G) :  (((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose step3192 step10
  have step3459 (X0 X1 : G) :  (((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X0)) = X0 := superpose step2216 step3442
  have step3531 (X0 X1 : G) :  (X1 ◇ (X0 ◇ X0)) = X0 := superpose step3028 step3459
  have step3562 (X0 X1 : G) :  X0 = X1 := superpose step3356 step3531
  have step3820 (X0 : G) :  sK0 ≠ X0 := superpose step3562 step11
  subsumption step3820 step3562


@[equational_result]
theorem Finite.Equation677_and_Equation670_implies_Equation3 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation670 G) : Equation3 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have step10 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X1))) = X0 := mod_symm (h ..)
  have step11 : sK0 ≠ (sK0 ◇ sK0) := mod_symm nh
  have step12 (X Y : G) : ((Y ◇ X) ◇ (((Y ◇ X) ◇ Y) ◇ Y)) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (s ◇ ((s ◇ Y) ◇ Y))) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (Y ◇ s)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (Y ◇ s)) (fun s => (s ◇ ((s ◇ Y) ◇ Y))) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step13 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step14 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step15 (X0 X1 : G) :  ((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X1 ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X1))))) = X1 := superpose step10 step10
  have step19 (X0 X1 : G) :  (X0 ◇ ((X0 ◇ X1) ◇ X1)) = (X0 ◇ ((X1 ◇ X0) ◇ X1)) := superpose step13 step12
  have step27 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose step13 step14
  have step42 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X1) = ((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ (((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ X0) ◇ X0)) := superpose step19 step12
  have step45 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X1) = ((X1 ◇ X0) ◇ X1) := superpose step12 step42
  have step454 (X0 : G) :  ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) = X0 := superpose step13 step15
  have step491 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = X0 := superpose step454 step27
  have step502 (X0 : G) :  (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) = (((X0 ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) := superpose step454 step45
  have step515 (X0 : G) :  (((X0 ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) = X0 := superpose step13 step502
  have step529 (X0 : G) :  (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) = X0 := superpose step491 step515
  have step537 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step491 step529
  have step616 : sK0 ≠ sK0 := superpose step537 step11
  subsumption step616 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation679_implies_Equation255 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation679 G) : Equation255 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have step10 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X1) ◇ X0))) = X0 := mod_symm (h ..)
  have step11 : sK0 ≠ (((sK0 ◇ sK0) ◇ sK0) ◇ sK0) := mod_symm nh
  have step12 (X Y : G) : ((Y ◇ X) ◇ ((Y ◇ Y) ◇ (Y ◇ X))) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (s ◇ ((Y ◇ Y) ◇ s))) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (Y ◇ s)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (Y ◇ s)) (fun s => (s ◇ ((Y ◇ Y) ◇ s))) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step13 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step14 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step19 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ X1) ◇ X0)) = (X0 ◇ ((X1 ◇ X0) ◇ X1)) := superpose step13 step12
  have step30 (X0 : G) :  (X0 ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) := superpose step12 step14
  have step51 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X1) = ((X0 ◇ ((X1 ◇ X1) ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ ((X1 ◇ X1) ◇ X0)))) := superpose step19 step12
  have step53 (X0 X1 : G) :  ((X1 ◇ X1) ◇ X0) = ((X1 ◇ X0) ◇ X1) := superpose step12 step51
  have step57 (X0 X1 : G) :  (X0 ◇ X1) = ((X1 ◇ X1) ◇ (X0 ◇ ((X1 ◇ X1) ◇ X0))) := superpose step10 step53
  have step73 (X0 X1 : G) :  ((X0 ◇ X1) ◇ (X0 ◇ (((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X1)))) = X0 := superpose step53 step13
  have step115 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) := superpose step30 step10
  have step328 (X0 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose step30 step73
  have step446 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X0 ◇ X1))) = X1 := superpose step328 step10
  have step454 (X0 X1 : G) :  (X0 ◇ X1) = (((X0 ◇ (X0 ◇ X0)) ◇ X1) ◇ (X0 ◇ (X0 ◇ X0))) := superpose step328 step53
  have step455 (X0 X1 : G) :  (X1 ◇ (X0 ◇ (X0 ◇ X0))) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := superpose step328 step57
  have step582 (X0 X1 : G) :  (X0 ◇ (X1 ◇ X0)) = (((X1 ◇ (X1 ◇ X1)) ◇ ((X1 ◇ (X1 ◇ X1)) ◇ (X1 ◇ (X1 ◇ X1)))) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0)) := superpose step446 step446
  have step654 (X0 X1 : G) :  (X0 ◇ (X1 ◇ X0)) = (((X1 ◇ (X1 ◇ X1)) ◇ ((X1 ◇ (X1 ◇ X1)) ◇ (X1 ◇ (X1 ◇ X1)))) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X0))) := superpose step53 step582
  have step665 (X0 X1 : G) :  (X0 ◇ (X1 ◇ X0)) = (((X1 ◇ (X1 ◇ X1)) ◇ X1) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X0))) := superpose step328 step654
  have step667 (X0 X1 : G) :  (X0 ◇ (X1 ◇ X0)) = (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X0))) := superpose step53 step665
  have step732 (X0 X1 : G) :  ((X0 ◇ ((X1 ◇ X1) ◇ X0)) ◇ (X1 ◇ (X1 ◇ X1))) = (X1 ◇ ((X0 ◇ ((X1 ◇ X1) ◇ X0)) ◇ X0)) := superpose step10 step455
  have step815 (X0 X1 : G) :  ((X0 ◇ ((X1 ◇ X1) ◇ X0)) ◇ (X1 ◇ (X1 ◇ X1))) = (X1 ◇ ((X0 ◇ X0) ◇ ((X1 ◇ X1) ◇ X0))) := superpose step53 step732
  have step1537 (X0 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) = (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))) := superpose step115 step446
  have step1540 (X0 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) = (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ X0))) := superpose step454 step1537
  have step1555 (X0 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) = (X0 ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) := superpose step815 step1540
  have step1563 (X0 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ (X0 ◇ X0))) := superpose step667 step1555
  have step1762 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose step12 step1563
  have step2019 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose step1762 step53
  have step2029 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ X0) = X0 := superpose step12 step2019
  have step2293 : sK0 ≠ sK0 := superpose step2029 step11
  subsumption step2293 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation704_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation704 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step12 (X0 X1 : G) :  (X1 ◇ (X1 ◇ ((X0 ◇ X0) ◇ X1))) = X0 := mod_symm (h ..)
  have step13 : sK0 ≠ sK1 := mod_symm nh
  have step14 (X Y : G) : ((Y ◇ (Y ◇ (X ◇ Y))) ◇ (Y ◇ (Y ◇ (X ◇ Y)))) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (s ◇ s)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (Y ◇ (Y ◇ (s ◇ Y)))) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (Y ◇ (Y ◇ (s ◇ Y)))) (fun s => (s ◇ s)) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step15 (X Y : G) : (((Y ◇ (Y ◇ X)) ◇ (Y ◇ (Y ◇ X))) ◇ Y) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => ((s ◇ s) ◇ Y)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (Y ◇ (Y ◇ s))) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (Y ◇ (Y ◇ s))) (fun s => ((s ◇ s) ◇ Y)) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step16 (X Y : G) : (Y ◇ (((Y ◇ X) ◇ (Y ◇ X)) ◇ Y)) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (Y ◇ ((s ◇ s) ◇ Y))) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (Y ◇ s)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (Y ◇ s)) (fun s => (Y ◇ ((s ◇ s) ◇ Y))) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step17 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step18 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step26 (X0 X1 : G) :  (((((X1 ◇ X1) ◇ X0) ◇ ((X1 ◇ X1) ◇ X0)) ◇ (X1 ◇ X1)) ◇ (((((X1 ◇ X1) ◇ X0) ◇ ((X1 ◇ X1) ◇ X0)) ◇ (X1 ◇ X1)) ◇ X0)) = X1 := superpose step16 step12
  have step28 (X0 X1 : G) :  (((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ ((X1 ◇ X0) ◇ X1)) := superpose step16 step18
  have step29 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step18 step18
  have step34 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = ((X1 ◇ X0) ◇ (((X1 ◇ (X1 ◇ X0)) ◇ X1) ◇ (X0 ◇ (X1 ◇ X0)))) := superpose step18 step17
  have step40 (X0 X1 : G) :  (X0 ◇ ((((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ (X1 ◇ X0))) ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ (X1 ◇ X0))))) = X1 := superpose step15 step18
  have step88 (X0 X1 : G) :  (((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X0)) ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X0))) = X1 := superpose step17 step14
  have step96 (X0 X1 X2 : G) :  (X1 ◇ (X1 ◇ (X0 ◇ X1))) = (X2 ◇ (X2 ◇ (X0 ◇ X2))) := superpose step14 step12
  have step153 (X0 X1 X2 : G) :  (X1 ◇ X2) = ((X2 ◇ (X1 ◇ X2)) ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X2)) := superpose step96 step18
  have step213 (X0 X1 : G) :  ((X0 ◇ X0) ◇ (X1 ◇ X0)) = (((X1 ◇ (X1 ◇ X0)) ◇ X1) ◇ (X0 ◇ (X1 ◇ X0))) := superpose step18 step28
  have step557 (X0 X1 X2 : G) :  ((X2 ◇ (X2 ◇ (X0 ◇ X2))) ◇ X1) = ((X0 ◇ X1) ◇ (((X1 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X0 ◇ X1)))) := superpose step153 step18
  have step569 (X0 X1 X2 : G) :  ((X2 ◇ (X2 ◇ (X0 ◇ X2))) ◇ X1) = ((X1 ◇ (X1 ◇ (X0 ◇ X1))) ◇ X1) := superpose step29 step557
  have step702 (X0 X1 X2 : G) :  ((X2 ◇ (X2 ◇ (X1 ◇ X2))) ◇ X2) = (((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X0)) ◇ X2) := superpose step17 step569
  have step757 (X0 X1 X2 X3 : G) :  ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X2) = ((X3 ◇ (X3 ◇ (X1 ◇ X3))) ◇ X2) := superpose step569 step569
  have step1188 (X0 X1 X2 : G) :  ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X2 ◇ (X2 ◇ (X1 ◇ X2)))) = X1 := superpose step757 step14
  have step1189 (X0 X1 X2 : G) :  (X1 ◇ X2) = (((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X2 ◇ (X2 ◇ (X1 ◇ X2)))) ◇ X2) := superpose step757 step15
  have step2761 (X0 : G) :  (X0 ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))))) = X0 := superpose step15 step40
  have step2963 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) := superpose step2761 step15
  have step3225 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ X0) = X0 := superpose step2963 step15
  have step3486 (X0 : G) :  (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) := superpose step3225 step28
  have step3521 (X0 : G) :  ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) = X0 := superpose step17 step3486
  have step3725 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) := superpose step3521 step34
  have step3728 (X0 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) = X0 := superpose step3521 step213
  have step3795 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = (((X0 ◇ X0) ◇ X0) ◇ X0) := superpose step3728 step3725
  have step3826 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = X0 := superpose step3225 step3795
  have step4047 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose step3826 step2963
  have step4064 (X0 X1 X2 : G) :  ((X1 ◇ (X1 ◇ (X0 ◇ X1))) ◇ X2) = ((X0 ◇ X0) ◇ X2) := superpose step3826 step757
  have step4090 (X0 X1 : G) :  (X1 ◇ (X1 ◇ (X0 ◇ X1))) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) := superpose step3826 step96
  have step4099 (X0 X1 X2 : G) :  ((X1 ◇ (X1 ◇ (X0 ◇ X1))) ◇ X2) = (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ X2) := superpose step3826 step757
  have step4106 (X0 : G) :  (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) = X0 := superpose step3826 step12
  have step4125 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step3521 step4106
  have step4131 (X0 X1 X2 : G) :  (X0 ◇ X2) = ((X1 ◇ (X1 ◇ (X0 ◇ X1))) ◇ X2) := superpose step3521 step4099
  have step4139 (X0 X1 : G) :  (X1 ◇ (X1 ◇ (X0 ◇ X1))) = X0 := superpose step3521 step4090
  have step4239 (X0 X1 X2 : G) :  (X1 ◇ (X0 ◇ X1)) = (((((X2 ◇ (X2 ◇ (X0 ◇ X2))) ◇ X1) ◇ ((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1)))) ◇ ((((X2 ◇ (X2 ◇ (X0 ◇ X2))) ◇ X1) ◇ ((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1)))) ◇ ((X2 ◇ (X2 ◇ (X0 ◇ X2))) ◇ X1))) ◇ ((((X2 ◇ (X2 ◇ (X0 ◇ X2))) ◇ X1) ◇ ((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1)))) ◇ ((((X2 ◇ (X2 ◇ (X0 ◇ X2))) ◇ X1) ◇ ((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1)))) ◇ ((X2 ◇ (X2 ◇ (X0 ◇ X2))) ◇ X1)))) := superpose step153 step88
  have step4261 (X0 X1 X2 : G) :  ((X2 ◇ (X2 ◇ (X0 ◇ X2))) ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1)))) = (((X1 ◇ ((X0 ◇ X1) ◇ ((X2 ◇ (X2 ◇ (X0 ◇ X2))) ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1)))))) ◇ ((X1 ◇ ((X0 ◇ X1) ◇ ((X2 ◇ (X2 ◇ (X0 ◇ X2))) ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1)))))) ◇ X1)) ◇ ((X1 ◇ ((X0 ◇ X1) ◇ ((X2 ◇ (X2 ◇ (X0 ◇ X2))) ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1)))))) ◇ ((X1 ◇ ((X0 ◇ X1) ◇ ((X2 ◇ (X2 ◇ (X0 ◇ X2))) ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1)))))) ◇ X1))) := superpose step1189 step88
  have step4323 (X0 X1 X2 : G) :  (((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ ((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1)) ◇ X2) = ((X2 ◇ (((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ ((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1)) ◇ X2)) ◇ ((((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ ((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1)) ◇ (((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ ((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1)) ◇ X0)) ◇ X2)) := superpose step88 step153
  have step4344 (X0 X1 X2 : G) :  (((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ ((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1)) ◇ X2) = ((X2 ◇ (((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ ((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1)) ◇ X2)) ◇ ((((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ ((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1)) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0)) ◇ X2)) := superpose step702 step4323
  have step4381 (X0 X1 X2 : G) :  ((X2 ◇ (X2 ◇ (X0 ◇ X2))) ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1)))) = ((X1 ◇ ((X0 ◇ X1) ◇ ((X2 ◇ (X2 ◇ (X0 ◇ X2))) ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1)))))) ◇ ((X1 ◇ ((X0 ◇ X1) ◇ ((X2 ◇ (X2 ◇ (X0 ◇ X2))) ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1)))))) ◇ X1)) := superpose step4125 step4261
  have step4402 (X0 X1 X2 : G) :  (X1 ◇ (X0 ◇ X1)) = ((((X2 ◇ (X2 ◇ (X0 ◇ X2))) ◇ X1) ◇ ((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1)))) ◇ ((((X2 ◇ (X2 ◇ (X0 ◇ X2))) ◇ X1) ◇ ((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1)))) ◇ ((X2 ◇ (X2 ◇ (X0 ◇ X2))) ◇ X1))) := superpose step4125 step4239
  have step4435 (X0 X1 X2 : G) :  (((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ ((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1)) ◇ X2) = ((X2 ◇ (((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ ((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1)) ◇ X2)) ◇ ((((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ ((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1)) ◇ ((X0 ◇ X0) ◇ X0)) ◇ X2)) := superpose step4064 step4344
  have step4463 (X0 X1 : G) :  ((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ ((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1)) = X0 := superpose step1188 step4381
  have step4482 (X0 X1 : G) :  (X1 ◇ (X0 ◇ X1)) = (((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1)))) ◇ (((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1)))) ◇ (X0 ◇ X1))) := superpose step4131 step4402
  have step4514 (X0 X1 X2 : G) :  (((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ ((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1)) ◇ X2) = ((X2 ◇ (((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ ((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1)) ◇ X2)) ◇ ((((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ ((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1)) ◇ (X0 ◇ X0)) ◇ X2)) := superpose step4047 step4435
  have step4550 (X0 X1 : G) :  (X1 ◇ (X0 ◇ X1)) = ((X1 ◇ X1) ◇ (((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1)))) ◇ (X0 ◇ X1))) := superpose step4064 step4482
  have step4576 (X0 X1 X2 : G) :  (((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ ((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1)) ◇ X2) = ((X2 ◇ (((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ ((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1)) ◇ X2)) ◇ ((((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ ((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1)) ◇ X0) ◇ X2)) := superpose step4125 step4514
  have step4601 (X0 X1 : G) :  (X1 ◇ (X0 ◇ X1)) = ((X1 ◇ X1) ◇ ((X1 ◇ X1) ◇ (X0 ◇ X1))) := superpose step4064 step4550
  have step4618 (X0 X1 X2 : G) :  (((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ ((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1)) ◇ X2) = ((X2 ◇ (((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ ((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1)) ◇ X2)) ◇ (((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) ◇ X2)) := superpose step702 step4576
  have step4637 (X0 X1 : G) :  (X1 ◇ (X0 ◇ X1)) = (X1 ◇ (X1 ◇ (X0 ◇ X1))) := superpose step4125 step4601
  have step4649 (X0 X1 X2 : G) :  (((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ ((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1)) ◇ X2) = ((X2 ◇ (((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ ((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1)) ◇ X2)) ◇ (((X0 ◇ X0) ◇ X0) ◇ X2)) := superpose step4064 step4618
  have step4663 (X0 X1 : G) :  (X1 ◇ (X0 ◇ X1)) = X0 := superpose step4139 step4637
  have step4672 (X0 X1 X2 : G) :  (((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ ((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1)) ◇ X2) = ((X2 ◇ (((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ ((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1)) ◇ X2)) ◇ ((X0 ◇ X0) ◇ X2)) := superpose step4047 step4649
  have step4689 (X0 X1 X2 : G) :  (((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ ((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1)) ◇ X2) = ((X2 ◇ (((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ ((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1)) ◇ X2)) ◇ (X0 ◇ X2)) := superpose step4125 step4672
  have step4702 (X0 X1 X2 : G) :  (((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ ((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1)) ◇ X2) = (((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ ((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1)) ◇ (X0 ◇ X2)) := superpose step4663 step4689
  have step4710 (X0 X2 : G) :  (X0 ◇ X2) = (X0 ◇ (X0 ◇ X2)) := superpose step4463 step4702
  have step4731 (X0 X1 : G) :  ((((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X0) ◇ ((((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X0) ◇ X1)) = X0 := superpose step4125 step26
  have step4781 (X0 X1 : G) :  (X0 ◇ ((X0 ◇ X1) ◇ X0)) = X1 := superpose step4125 step16
  have step4823 (X0 X1 : G) :  (X0 ◇ X1) = X1 := superpose step4663 step4781
  have step4853 (X0 X1 : G) :  ((((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X0) ◇ X1) = X0 := superpose step4710 step4731
  have step4876 (X0 X1 : G) :  X0 = X1 := superpose step4823 step4853
  have step5242 (X0 : G) :  sK0 ≠ X0 := superpose step4876 step13
  subsumption step5242 step4876


@[equational_result]
theorem Finite.Equation677_and_Equation707_implies_Equation3 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation707 G) : Equation3 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have step13 : sK0 ≠ (sK0 ◇ sK0) := mod_symm nh
  have step14 (X Y : G) : ((Y ◇ (Y ◇ (X ◇ Y))) ◇ Y) = X := by
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
  have step15 (X Y : G) : (((Y ◇ (Y ◇ X)) ◇ Y) ◇ Y) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => ((s ◇ Y) ◇ Y)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (Y ◇ (Y ◇ s))) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (Y ◇ (Y ◇ s))) (fun s => ((s ◇ Y) ◇ Y)) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step16 (X Y : G) : (Y ◇ (((Y ◇ X) ◇ Y) ◇ Y)) = X := by
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
  have step18 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step21 (X0 X1 : G) :  (X1 ◇ (X1 ◇ (X0 ◇ X1))) = ((X1 ◇ (X1 ◇ X0)) ◇ X1) := superpose step14 step14
  have step54 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step18 step18
  have step57 (X0 X1 : G) :  (X0 ◇ X1) = ((X1 ◇ (X0 ◇ X1)) ◇ X0) := superpose step14 step18
  have step80 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = X0 := superpose step57 step15
  have step100 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = X0 := superpose step80 step16
  have step106 (X0 : G) :  (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0))) = X0 := superpose step80 step18
  have step108 (X0 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ X0) = X0 := superpose step54 step106
  have step111 (X0 : G) :  (X0 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose step21 step108
  have step114 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step100 step111
  have step159 : sK0 ≠ sK0 := superpose step114 step13
  subsumption step159 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation713_implies_Equation3 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation713 G) : Equation3 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have step12 : sK0 ≠ (sK0 ◇ sK0) := mod_symm nh
  have step14 (X Y : G) : (Y ◇ ((Y ◇ (Y ◇ X)) ◇ (Y ◇ X))) = X := by
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
  have step15 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step16 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step22 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = (X0 ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) := superpose step15 step14
  have step24 (X0 X1 : G) :  (X1 ◇ ((X1 ◇ X0) ◇ X0)) = ((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)) := superpose step14 step14
  have step27 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose step15 step22
  have step40 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose step15 step16
  have step45 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := superpose step27 step40
  have step47 (X0 : G) :  (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose step24 step45
  have step48 (X0 : G) :  (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose step27 step47
  have step52 (X0 : G) :  (X0 ◇ X0) = (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) := superpose step48 step14
  have step56 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step14 step52
  have step83 : sK0 ≠ sK0 := superpose step56 step12
  subsumption step83 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation716_implies_Equation1426 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation716 G) : Equation1426 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have step12 : sK0 ≠ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := mod_symm nh
  have step13 (X Y : G) : ((Y ◇ Y) ◇ (Y ◇ (Y ◇ X))) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => ((Y ◇ Y) ◇ s)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (Y ◇ (Y ◇ s))) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (Y ◇ (Y ◇ s))) (fun s => ((Y ◇ Y) ◇ s)) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  subsumption step12 step13


@[equational_result]
theorem Finite.Equation677_and_Equation716_implies_Equation255 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation716 G) : Equation255 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X1 ◇ ((X1 ◇ X1) ◇ X0))) = X0 := mod_symm (h ..)
  have step12 : sK0 ≠ (((sK0 ◇ sK0) ◇ sK0) ◇ sK0) := mod_symm nh
  have step13 (X Y : G) : ((Y ◇ Y) ◇ (Y ◇ (Y ◇ X))) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => ((Y ◇ Y) ◇ s)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (Y ◇ (Y ◇ s))) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (Y ◇ (Y ◇ s))) (fun s => ((Y ◇ Y) ◇ s)) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step14 (X Y : G) : (Y ◇ ((Y ◇ Y) ◇ (Y ◇ X))) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (Y ◇ ((Y ◇ Y) ◇ s))) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (Y ◇ s)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (Y ◇ s)) (fun s => (Y ◇ ((Y ◇ Y) ◇ s))) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step15 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step16 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step17 (X0 X1 : G) :  (X1 ◇ (X1 ◇ X0)) = ((X1 ◇ X1) ◇ (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ X0)) := superpose step11 step11
  have step18 (X0 X1 : G) :  (X1 ◇ ((X1 ◇ X1) ◇ X0)) = ((X1 ◇ X1) ◇ (X1 ◇ X0)) := superpose step11 step13
  have step19 (X0 X1 : G) :  (X1 ◇ (X1 ◇ X0)) = (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ ((X1 ◇ X1) ◇ X0)) := superpose step13 step13
  have step28 (X0 : G) :  (X0 ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) := superpose step15 step14
  have step29 (X0 X1 : G) :  (X1 ◇ (X1 ◇ X0)) = (X0 ◇ (((X1 ◇ X1) ◇ X0) ◇ (X1 ◇ X1))) := superpose step15 step11
  have step30 (X0 X1 : G) :  (X1 ◇ ((X1 ◇ X1) ◇ X0)) = (X0 ◇ ((X1 ◇ X0) ◇ X1)) := superpose step15 step14
  have step31 (X0 X1 : G) :  ((X1 ◇ X1) ◇ (X1 ◇ X0)) = (X0 ◇ ((X1 ◇ X0) ◇ X1)) := superpose step15 step13
  have step37 (X0 X1 : G) :  ((X1 ◇ X1) ◇ X0) = ((X1 ◇ ((X1 ◇ X1) ◇ X0)) ◇ (X0 ◇ X1)) := superpose step11 step16
  have step54 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0))) := superpose step28 step16
  have step60 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0))) := superpose step28 step54
  have step66 (X0 X1 : G) :  (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ X0) = ((X1 ◇ X1) ◇ (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ (X1 ◇ (X1 ◇ X0)))) := superpose step13 step18
  have step68 (X0 X1 : G) :  ((X1 ◇ X1) ◇ X0) = (X1 ◇ ((X1 ◇ X1) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1)))) := superpose step15 step18
  have step71 (X0 X1 : G) :  ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X1))) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X1))) := superpose step18 step18
  have step80 (X0 X1 : G) :  ((X0 ◇ X0) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ X1))) = X1 := superpose step18 step14
  have step96 (X0 X1 : G) :  ((X0 ◇ X0) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X1))) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X1))) := superpose step18 step71
  have step99 (X0 X1 : G) :  (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ X0) = (X1 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X0)))) := superpose step17 step66
  have step104 (X0 X1 : G) :  (X1 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X0)))) = ((X1 ◇ ((X1 ◇ X1) ◇ X1)) ◇ X0) := superpose step18 step99
  have step113 (X0 X1 : G) :  ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X1))) = ((X0 ◇ X1) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X1)) ◇ (X0 ◇ X0))) := superpose step18 step30
  have step138 (X0 X1 : G) :  ((X0 ◇ X1) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X1)) ◇ (X0 ◇ X0))) = (X0 ◇ (X0 ◇ (X0 ◇ X1))) := superpose step17 step113
  have step235 (X0 X1 : G) :  (X1 ◇ (X1 ◇ (((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ (X0 ◇ X0)))) = ((((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X1))) ◇ (X1 ◇ X1))) := superpose step29 step29
  have step254 (X0 X1 : G) :  (((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ (X0 ◇ X0)) = (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1))))) := superpose step29 step11
  have step261 (X0 X1 : G) :  ((X1 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) = ((((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X1)) := superpose step29 step31
  have step273 (X0 X1 : G) :  (X1 ◇ (X1 ◇ (((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ (X0 ◇ X0)))) = (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1)))) := superpose step261 step235
  have step280 (X0 X1 : G) :  (X1 ◇ (X1 ◇ (((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ (X0 ◇ X0)))) = ((X1 ◇ ((X1 ◇ X1) ◇ X1)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1)))) := superpose step18 step273
  have step285 (X0 X1 : G) :  (X1 ◇ (X1 ◇ (((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ (X0 ◇ X0)))) = (X1 ◇ (X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1))))))) := superpose step104 step280
  have step392 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := superpose step60 step13
  have step414 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))) := superpose step254 step392
  have step439 (X0 X1 : G) :  ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ X1)) := superpose step18 step17
  have step505 (X0 X1 : G) :  ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) = (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ X1))))) := superpose step104 step439
  have step522 (X0 X1 : G) :  ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) = (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (((X0 ◇ X0) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0))) ◇ X1))))) := superpose step96 step505
  have step531 (X0 X1 : G) :  ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) = (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X1))))) := superpose step138 step522
  have step1255 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X1) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X1 ◇ ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X1) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))))) := superpose step19 step68
  have step1358 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X1) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)))) := superpose step29 step1255
  have step1387 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X1) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)))) := superpose step18 step1358
  have step1404 (X0 X1 : G) :  ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X1) = (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1))))))) := superpose step104 step1387
  have step1416 (X0 X1 : G) :  ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)))) = ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X1) := superpose step531 step1404
  have step1626 (X0 : G) :  ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))))) = ((X0 ◇ X0) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)))) := superpose step414 step80
  have step1689 (X0 : G) :  ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))))) = ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))))))) := superpose step104 step1626
  have step1732 (X0 : G) :  (X0 ◇ (X0 ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)))) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))))) := superpose step13 step1689
  have step1765 (X0 : G) :  ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)))) := superpose step1416 step1732
  have step1783 (X0 : G) :  ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))))) := superpose step285 step1765
  have step1795 (X0 : G) :  (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) = ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0)) := superpose step414 step1783
  have step1800 (X0 : G) :  ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0)) = X0 := superpose step15 step1795
  have step2065 (X0 : G) :  (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) = (((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))) ◇ X0) := superpose step1800 step37
  have step2072 (X0 : G) :  (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) = ((X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))) ◇ X0) := superpose step17 step2065
  have step2091 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) := superpose step414 step2072
  have step2108 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) := superpose step18 step2091
  have step2118 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ X0) = (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))))) := superpose step104 step2108
  have step2127 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ X0) = (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) := superpose step414 step2118
  have step2134 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ X0) = X0 := superpose step15 step2127
  have step2348 : sK0 ≠ sK0 := superpose step2134 step12
  subsumption step2348 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation716_implies_Equation817 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation716 G) : Equation817 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have step12 : sK0 ≠ (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := mod_symm nh
  have step14 (X Y : G) : (Y ◇ ((Y ◇ Y) ◇ (Y ◇ X))) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (Y ◇ ((Y ◇ Y) ◇ s))) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (Y ◇ s)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (Y ◇ s)) (fun s => (Y ◇ ((Y ◇ Y) ◇ s))) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  subsumption step12 step14


@[equational_result]
theorem Finite.Equation677_and_Equation75_implies_Equation3 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation75 G) : Equation3 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X1 ◇ (X1 ◇ (X1 ◇ X0))) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ (sK0 ◇ sK0) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step15 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose step11 step9
  have step16 (X0 X1 : G) :  (X1 ◇ (X1 ◇ X0)) = (X0 ◇ ((X1 ◇ X0) ◇ X1)) := superpose step11 step9
  have step30 (X0 : G) :  ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = X0 := superpose step15 step9
  have step36 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose step15 step16
  have step41 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X0) = (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1)))) := superpose step16 step9
  have step352 (X0 : G) :  (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))))) := superpose step36 step41
  have step353 (X0 : G) :  (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) := superpose step36 step352
  have step363 (X0 : G) :  (X0 ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) := superpose step30 step353
  have step373 (X0 : G) :  (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) = (X0 ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) := superpose step363 step16
  have step378 (X0 : G) :  ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = (X0 ◇ (X0 ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)))) := superpose step363 step41
  have step379 (X0 : G) :  ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) := superpose step15 step378
  have step384 (X0 : G) :  (X0 ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := superpose step30 step373
  have step390 (X0 : G) :  (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose step36 step379
  have step395 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose step15 step384
  have step401 (X0 : G) :  (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = X0 := superpose step30 step390
  have step407 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = X0 := superpose step395 step401
  have step480 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step407 step30
  have step602 : sK0 ≠ sK0 := superpose step480 step10
  subsumption step602 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation75_implies_Equation716 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation75 G) : Equation716 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X1 ◇ (X1 ◇ (X1 ◇ X0))) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ (sK1 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ sK0))) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step15 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose step11 step9
  have step16 (X0 X1 : G) :  (X1 ◇ (X1 ◇ X0)) = (X0 ◇ ((X1 ◇ X0) ◇ X1)) := superpose step11 step9
  have step30 (X0 : G) :  ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = X0 := superpose step15 step9
  have step36 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ X0)) = (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose step15 step16
  have step42 (X0 X1 : G) :  ((X0 ◇ X1) ◇ X0) = (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1)))) := superpose step16 step9
  have step352 (X0 : G) :  (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))))) := superpose step36 step42
  have step353 (X0 : G) :  (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) := superpose step36 step352
  have step363 (X0 : G) :  (X0 ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) := superpose step30 step353
  have step373 (X0 : G) :  (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) = (X0 ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) := superpose step363 step16
  have step378 (X0 : G) :  ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = (X0 ◇ (X0 ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)))) := superpose step363 step42
  have step379 (X0 : G) :  ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) := superpose step15 step378
  have step384 (X0 : G) :  (X0 ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := superpose step30 step373
  have step390 (X0 : G) :  (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose step36 step379
  have step395 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose step15 step384
  have step401 (X0 : G) :  (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = X0 := superpose step30 step390
  have step407 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = X0 := superpose step395 step401
  have step462 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step407 step9
  have step601 : sK0 ≠ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) := superpose step462 step10
  subsumption step601 step9


@[equational_result]
theorem Finite.Equation677_and_Equation836_implies_Equation283 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation836 G) : Equation283 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X1))) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ (((sK1 ◇ sK1) ◇ sK1) ◇ sK0) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step16 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ X0) ◇ X1)) = ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1))) := superpose step11 step9
  have step17 (X0 X1 : G) :  ((X1 ◇ X0) ◇ (X1 ◇ X1)) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose step9 step12
  have step18 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step19 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose step11 step12
  have step20 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = ((X1 ◇ X0) ◇ (((X1 ◇ (X1 ◇ X0)) ◇ X1) ◇ (X0 ◇ (X1 ◇ X0)))) := superpose step12 step11
  have step23 (X0 X1 : G) :  (X1 ◇ ((X1 ◇ X1) ◇ X1)) = (((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) := superpose step17 step17
  have step27 (X0 X1 : G) :  (X1 ◇ (((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) = X1 := superpose step17 step9
  have step41 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) := superpose step19 step9
  have step345 (X0 X1 : G) :  (X1 ◇ ((((X0 ◇ X0) ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X0))) = X1 := superpose step41 step9
  have step584 (X0 X1 : G) :  (X1 ◇ ((((X0 ◇ X0) ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X0))) = ((X1 ◇ ((((X0 ◇ X0) ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X0))) ◇ (X1 ◇ ((X0 ◇ X0) ◇ X0))) := superpose step41 step16
  have step635 (X0 X1 : G) :  (X1 ◇ (X1 ◇ ((X0 ◇ X0) ◇ X0))) = X1 := superpose step345 step584
  have step674 (X0 X1 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ ((X1 ◇ X1) ◇ X1)) ◇ ((X0 ◇ (X0 ◇ ((X1 ◇ X1) ◇ X1))) ◇ X0)) := superpose step635 step18
  have step679 (X0 X1 : G) :  ((X1 ◇ X1) ◇ X1) = ((X0 ◇ X0) ◇ X0) := superpose step12 step674
  have step815 (X0 X1 : G) :  (X1 ◇ ((((X0 ◇ X0) ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X0))) = (((X1 ◇ X1) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X1 ◇ X1)) := superpose step679 step18
  have step825 (X0 : G) :  sK0 ≠ (((X0 ◇ X0) ◇ X0) ◇ sK0) := superpose step679 step10
  have step833 (X0 X1 : G) :  (((X1 ◇ X1) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X1 ◇ X1)) = X1 := superpose step345 step815
  have step1221 (X0 X1 : G) :  (((X1 ◇ X1) ◇ ((X1 ◇ X1) ◇ X1)) ◇ (X1 ◇ X1)) = (((X1 ◇ X1) ◇ X1) ◇ ((((X1 ◇ X1) ◇ ((X1 ◇ X1) ◇ X1)) ◇ (X1 ◇ X1)) ◇ (((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))))) := superpose step23 step20
  have step1276 (X0 X1 : G) :  (((X1 ◇ X1) ◇ X1) ◇ (X1 ◇ (((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))))) = X1 := superpose step833 step1221
  have step1303 (X1 : G) :  (((X1 ◇ X1) ◇ X1) ◇ X1) = X1 := superpose step27 step1276
  have step1353 : sK0 ≠ sK0 := superpose step1303 step825
  subsumption step1353 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation843_implies_Equation1426 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation843 G) : Equation1426 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ X1) ◇ (X0 ◇ X1))) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := mod_symm nh
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step21 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose step12 step9
  have step24 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose step21 step12
  have step52 : sK0 ≠ sK0 := superpose step24 step10
  subsumption step52 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation843_implies_Equation255 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation843 G) : Equation255 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ X1) ◇ (X0 ◇ X1))) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ (((sK0 ◇ sK0) ◇ sK0) ◇ sK0) := mod_symm nh
  have step11 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step12 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step14 (X0 X1 : G) :  ((X1 ◇ X1) ◇ (X0 ◇ X1)) = (X0 ◇ (((X1 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X0))) := superpose step9 step11
  have step17 (X0 X1 : G) :  ((X1 ◇ X1) ◇ (X0 ◇ X1)) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose step9 step12
  have step18 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step12 step12
  have step19 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose step9 step12
  have step20 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose step11 step12
  have step21 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose step12 step9
  have step24 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose step21 step12
  have step27 (X0 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))))) = X0 := superpose step21 step11
  have step36 (X0 X1 X2 : G) :  ((X0 ◇ X0) ◇ (X1 ◇ X0)) = ((X2 ◇ X2) ◇ (X1 ◇ X2)) := superpose step17 step17
  have step44 (X0 X1 : G) :  ((X1 ◇ X1) ◇ X1) = (((X0 ◇ X0) ◇ (X1 ◇ X0)) ◇ ((X1 ◇ ((X0 ◇ X0) ◇ (X1 ◇ X0))) ◇ X1)) := superpose step17 step12
  have step47 (X0 X1 : G) :  ((X1 ◇ X1) ◇ X1) = (((X0 ◇ X0) ◇ (X1 ◇ X0)) ◇ (X1 ◇ X1)) := superpose step9 step44
  have step52 (X0 : G) :  ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) = (((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) := superpose step24 step17
  have step57 (X0 : G) :  ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) = (((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) := superpose step47 step52
  have step80 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) = ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0)) := superpose step24 step18
  have step99 (X0 : G) :  (X0 ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) := superpose step12 step80
  have step108 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) := superpose step99 step9
  have step109 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) := superpose step47 step108
  have step218 (X0 X1 : G) :  ((X0 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X1)) ◇ X0)) = X1 := superpose step36 step12
  have step329 (X0 X1 : G) :  (((((X0 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X1)) ◇ X0)) ◇ ((X1 ◇ (X1 ◇ X1)) ◇ (X1 ◇ (X1 ◇ X1)))) ◇ (((X0 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X1)) ◇ X0)) ◇ ((X1 ◇ (X1 ◇ X1)) ◇ (X1 ◇ (X1 ◇ X1))))) ◇ ((X0 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X1)) ◇ X0))) = X1 := superpose step14 step218
  have step349 (X0 X1 : G) :  (X1 ◇ ((X1 ◇ X1) ◇ X1)) = (X0 ◇ (X1 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))))) := superpose step218 step17
  have step353 (X0 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) = (X0 ◇ (((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0)) := superpose step218 step24
  have step370 (X0 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) = (X0 ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0))) := superpose step57 step353
  have step377 (X1 : G) :  (((X1 ◇ ((X1 ◇ (X1 ◇ X1)) ◇ (X1 ◇ (X1 ◇ X1)))) ◇ (X1 ◇ ((X1 ◇ (X1 ◇ X1)) ◇ (X1 ◇ (X1 ◇ X1))))) ◇ X1) = X1 := superpose step218 step329
  have step382 (X1 : G) :  (((X1 ◇ (X1 ◇ ((X1 ◇ X1) ◇ ((X1 ◇ X1) ◇ X1)))) ◇ (X1 ◇ (X1 ◇ ((X1 ◇ X1) ◇ ((X1 ◇ X1) ◇ X1))))) ◇ X1) = X1 := superpose step370 step377
  have step689 (X0 : G) :  (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))) = ((X0 ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))))) ◇ (X0 ◇ X0)) := superpose step218 step19
  have step723 (X0 : G) :  ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) = (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))) := superpose step349 step689
  have step735 (X0 : G) :  ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)))) := superpose step370 step723
  have step743 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)))) := superpose step20 step735
  have step1051 (X0 : G) :  (((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ X0))) = (((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))) := superpose step21 step47
  have step1111 (X0 : G) :  ((X0 ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0))) ◇ (X0 ◇ (X0 ◇ X0))) = (((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)))) := superpose step370 step1051
  have step1139 (X0 : G) :  (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)))) = ((X0 ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0))) ◇ (X0 ◇ (X0 ◇ X0))) := superpose step24 step1111
  have step1152 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0))) ◇ (X0 ◇ (X0 ◇ X0))) := superpose step743 step1139
  have step1177 (X0 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ X0)))) = (((X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))) ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))))) ◇ X0) := superpose step27 step17
  have step1190 (X0 : G) :  (((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)))) ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0))))) ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0))) ◇ (X0 ◇ (X0 ◇ X0)))) := superpose step370 step1177
  have step1206 (X0 : G) :  (((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)))) ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0))))) ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) := superpose step1152 step1190
  have step1218 (X0 : G) :  ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) = X0 := superpose step382 step1206
  have step1229 (X0 : G) :  ((((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) = X0 := superpose step1218 step218
  have step1256 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ X0) = X0 := superpose step109 step1229
  have step1368 : sK0 ≠ sK0 := superpose step1256 step10
  subsumption step1368 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation843_implies_Equation817 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation843 G) : Equation817 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have step9 (X0 X1 : G) :  (X0 ◇ ((X1 ◇ X1) ◇ (X0 ◇ X1))) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := mod_symm nh
  have step14 : sK0 ≠ sK0 := superpose step9 step10
  subsumption step14 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation882_implies_Equation3 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation882 G) : Equation3 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have step10 (X0 X1 : G) :  (X1 ◇ ((X0 ◇ X1) ◇ (X1 ◇ X0))) = X0 := mod_symm (h ..)
  have step11 : sK0 ≠ (sK0 ◇ sK0) := mod_symm nh
  have step12 (X Y : G) : (((Y ◇ X) ◇ Y) ◇ (Y ◇ (Y ◇ X))) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => ((s ◇ Y) ◇ (Y ◇ s))) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (Y ◇ s)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (Y ◇ s)) (fun s => ((s ◇ Y) ◇ (Y ◇ s))) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step13 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step14 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step17 (X0 X1 : G) :  ((X0 ◇ X1) ◇ (X1 ◇ X0)) = (X1 ◇ (((X0 ◇ X1) ◇ (X1 ◇ X0)) ◇ (X0 ◇ X1))) := superpose step10 step13
  have step21 (X0 X1 : G) :  ((X0 ◇ X1) ◇ (X1 ◇ X0)) = (X0 ◇ ((X1 ◇ X0) ◇ X1)) := superpose step13 step12
  have step23 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) ◇ X0) := superpose step13 step12
  have step24 (X0 X1 : G) :  (X1 ◇ (X1 ◇ X0)) = (((X1 ◇ X0) ◇ X1) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1)))) := superpose step12 step13
  have step28 (X0 X1 : G) :  (X1 ◇ (X1 ◇ X0)) = (X0 ◇ ((((X1 ◇ X0) ◇ X1) ◇ X0) ◇ ((X1 ◇ X0) ◇ X1))) := superpose step12 step14
  have step29 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose step14 step14
  have step30 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose step13 step14
  have step43 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = (((X1 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ X0) ◇ X1)) ◇ X0) := superpose step12 step21
  have step53 (X0 X1 : G) :  (X1 ◇ X0) = ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (((X0 ◇ X1) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) ◇ (X0 ◇ X1))) := superpose step21 step14
  have step58 (X0 X1 : G) :  ((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = ((X1 ◇ (((X1 ◇ X0) ◇ X1) ◇ (X1 ◇ X0))) ◇ X0) := superpose step21 step43
  have step68 (X0 : G) :  (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) ◇ (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0)))) = X0 := superpose step23 step13
  have step74 (X0 : G) :  (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) = X0 := superpose step13 step68
  have step84 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (((X0 ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ (X0 ◇ X0))) := superpose step30 step21
  have step86 (X0 : G) :  (X0 ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) := superpose step53 step84
  have step115 (X0 : G) :  ((((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0)) = (X0 ◇ ((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0))) := superpose step23 step29
  have step141 (X0 : G) :  ((((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0)) = (X0 ◇ (X0 ◇ X0)) := superpose step28 step115
  have step143 (X0 : G) :  (X0 ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0)) = (X0 ◇ (X0 ◇ X0)) := superpose step74 step141
  have step149 (X0 : G) :  ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0)) := superpose step143 step14
  have step155 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) := superpose step14 step149
  have step253 (X0 : G) :  (X0 ◇ ((X0 ◇ X0) ◇ X0)) = (((X0 ◇ X0) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0)) := superpose step21 step155
  have step254 (X0 : G) :  ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) = X0 := superpose step155 step74
  have step276 (X0 : G) :  (X0 ◇ ((X0 ◇ X0) ◇ X0)) = (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose step30 step253
  have step279 (X0 : G) :  (X0 ◇ ((X0 ◇ X0) ◇ X0)) = (X0 ◇ (X0 ◇ X0)) := superpose step254 step276
  have step384 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0))) := superpose step21 step254
  have step407 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) := superpose step30 step384
  have step414 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) := superpose step279 step407
  have step417 (X0 : G) :  (X0 ◇ X0) = (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0))) := superpose step21 step414
  have step420 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose step29 step417
  have step449 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) = ((X0 ◇ X0) ◇ ((((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) ◇ ((X0 ◇ X0) ◇ X0))) := superpose step30 step17
  have step450 (X0 : G) :  (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0))) = (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0))) ◇ X0)) := superpose step254 step17
  have step487 (X0 : G) :  (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0))) = (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) := superpose step58 step450
  have step488 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0))) := superpose step86 step449
  have step518 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0))) := superpose step24 step487
  have step519 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose step254 step488
  have step531 (X0 : G) :  (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose step29 step518
  have step536 (X0 : G) :  (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose step420 step531
  have step553 (X0 : G) :  (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0)))) := superpose step519 step10
  have step580 (X0 : G) :  (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose step536 step553
  have step602 (X0 : G) :  (X0 ◇ X0) = X0 := superpose step10 step580
  have step791 : sK0 ≠ sK0 := superpose step602 step11
  subsumption step791 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation907_implies_Equation1426 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation907 G) : Equation1426 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have step10 (X0 X1 : G) :  (X1 ◇ ((X1 ◇ X0) ◇ (X0 ◇ X1))) = X0 := mod_symm (h ..)
  have step11 : sK0 ≠ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := mod_symm nh
  have step12 (X Y : G) : ((Y ◇ (Y ◇ X)) ◇ ((Y ◇ X) ◇ Y)) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => ((Y ◇ s) ◇ (s ◇ Y))) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (Y ◇ s)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (Y ◇ s)) (fun s => ((Y ◇ s) ◇ (s ◇ Y))) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step13 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step14 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step17 (X0 X1 : G) :  ((X1 ◇ X0) ◇ (X0 ◇ X1)) = (X1 ◇ (((X1 ◇ X0) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1))) := superpose step10 step13
  have step21 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = (X0 ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0)) := superpose step13 step12
  have step22 (X0 X1 : G) :  ((X1 ◇ X0) ◇ (X0 ◇ X1)) = (X0 ◇ ((X1 ◇ X0) ◇ X1)) := superpose step13 step12
  have step23 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X1) = (((X1 ◇ (X1 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0)))) := superpose step12 step12
  have step24 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X1) = ((X1 ◇ (X1 ◇ X0)) ◇ (((X1 ◇ X0) ◇ X1) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0))))) := superpose step12 step13
  have step30 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose step13 step14
  have step37 (X0 X1 : G) :  ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X0 ◇ X1)) = (X0 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X1)) := superpose step13 step22
  have step53 (X0 X1 : G) :  (X0 ◇ X1) = ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (((X1 ◇ X0) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) ◇ (X1 ◇ X0))) := superpose step22 step14
  have step82 (X0 : G) :  (((X0 ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X0 ◇ X0) ◇ X0)) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (((X0 ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ (X0 ◇ X0))) := superpose step30 step22
  have step83 (X0 : G) :  (X0 ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X0 ◇ X0) ◇ X0)) := superpose step53 step82
  have step277 (X0 : G) :  (((X0 ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X0 ◇ X0) ◇ X0)) = ((X0 ◇ X0) ◇ ((((X0 ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0))) := superpose step30 step17
  have step306 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0))) := superpose step83 step277
  have step619 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ X0) = (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0)) ◇ (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) := superpose step21 step23
  have step625 (X0 : G) :  (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) = (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0))) := superpose step306 step23
  have step664 (X0 : G) :  (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) = (((X0 ◇ X0) ◇ X0) ◇ (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0))) := superpose step22 step625
  have step670 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ X0) = (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) ◇ (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) := superpose step22 step619
  have step686 (X0 : G) :  (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) = X0 := superpose step14 step664
  have step690 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ X0) = X0 := superpose step14 step670
  have step772 (X0 : G) :  (X0 ◇ X0) = (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := superpose step22 step690
  have step806 (X0 : G) :  (X0 ◇ X0) = ((X0 ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0)) ◇ (X0 ◇ X0)) := superpose step37 step772
  have step813 (X0 : G) :  (X0 ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) := superpose step21 step806
  have step838 (X0 : G) :  (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ ((((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)))) := superpose step306 step24
  have step879 (X0 : G) :  (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ ((((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) := superpose step813 step838
  have step903 (X0 : G) :  ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose step686 step879
  have step924 : sK0 ≠ sK0 := superpose step903 step11
  subsumption step924 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation907_implies_Equation255 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation907 G) : Equation255 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have step11 : sK0 ≠ (((sK0 ◇ sK0) ◇ sK0) ◇ sK0) := mod_symm nh
  have step12 (X Y : G) : ((Y ◇ (Y ◇ X)) ◇ ((Y ◇ X) ◇ Y)) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => ((Y ◇ s) ◇ (s ◇ Y))) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (Y ◇ s)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (Y ◇ s)) (fun s => ((Y ◇ s) ◇ (s ◇ Y))) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have step13 (X0 X1 : G) :  (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h2 ..)
  have step14 (X0 X1 : G) :  ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := (Finite.Equation677_implies_Equation19855 G h2 _ _).symm
  have step21 (X0 : G) :  ((X0 ◇ X0) ◇ X0) = (X0 ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0)) := superpose step13 step12
  have step22 (X0 X1 : G) :  ((X1 ◇ X0) ◇ (X0 ◇ X1)) = (X0 ◇ ((X1 ◇ X0) ◇ X1)) := superpose step13 step12
  have step23 (X0 X1 : G) :  ((X1 ◇ X0) ◇ X1) = (((X1 ◇ (X1 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0)))) := superpose step12 step12
  have step619 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ X0) = (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0)) ◇ (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) := superpose step21 step23
  have step670 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ X0) = (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) ◇ (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) := superpose step22 step619
  have step690 (X0 : G) :  (((X0 ◇ X0) ◇ X0) ◇ X0) = X0 := superpose step14 step670
  have step793 : sK0 ≠ sK0 := superpose step690 step11
  subsumption step793 rfl


@[equational_result]
theorem Finite.Equation677_and_Equation907_implies_Equation817 (G : Type*) [Magma G] [Finite G] (h2 : Equation677 G) (h : Equation907 G) : Equation817 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have step10 (X0 X1 : G) :  (X1 ◇ ((X1 ◇ X0) ◇ (X0 ◇ X1))) = X0 := mod_symm (h ..)
  have step11 : sK0 ≠ (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := mod_symm nh
  have step17 : sK0 ≠ sK0 := superpose step10 step11
  subsumption step17 rfl
