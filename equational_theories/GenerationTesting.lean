-- This file is just for testing, should be deleted before merging the PR
import equational_theories.Subgraph
open Subgraph

theorem lift_to_law  (hnot : forall (G : Type) [Magma G], Equation3 G → Equation39 G) : Law3.implies Law39 :=
  fun {G : Type} inst h ↦ (Law39.models_iff G).mpr (hnot G ((Law3.models_iff G).mp h))

theorem lower_to_eq (h : Law3.implies Law39) : forall (G : Type) [Magma G], Equation3 G → Equation39 G :=
  fun G inst h3 ↦ Law39.models_iff G |>.mp (h ((Law3.models_iff G).mpr h3))

theorem Law3_not_implies_Law39 : Not (@Law.MagmaLaw.implies.{0} Nat Law3 Law39) := by
  intro hcontra
  have hnot := lower_to_eq hcontra
  have ⟨G,⟨inst,⟨hN,hM⟩ ⟩⟩ := Equation3_not_implies_Equation39
  exact hM <| hnot G hN

set_option pp.all true in
#print Law3_not_implies_Law39
