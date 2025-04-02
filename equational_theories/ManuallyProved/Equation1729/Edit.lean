
import Mathlib.Data.Fintype.Basic
import Mathlib.Logic.Embedding.Basic
import Init.Classical
import Init.Prelude

namespace Function.Embedding

-- this is for convenience
open Classical

def attains {X' X: Type*} (ι : X' ↪ X) (x : X) : Prop := ∃ x' : X', ι x' = x

def avoids {X' X: Type*} (ι : X' ↪ X) (x : X) : Prop := ∀ x' : X', ι x' ≠ x

lemma attains_image {X' X: Type*} (ι : X' ↪ X) (x' : X') : ι.attains (ι x') := ⟨ x', rfl ⟩

lemma attains_iff_not_avoids {X' X: Type*} (ι : X' ↪ X) (x : X) :  ι.attains x ↔ ¬ ι.avoids x :=
  by
   simp only [attains, avoids, ne_eq, not_forall, not_not]

lemma avoids_iff_not_attains {X' X: Type*} (ι : X' ↪ X) (x : X) : ι.avoids x ↔ ¬ ι.attains x :=
  by
   simp only [avoids, ne_eq, attains, not_exists]

noncomputable def range_finset {X' X: Type*} (ι : X' ↪ X) [Fintype X'] : Finset X := Finset.image ι Finset.univ

lemma attains_iff_in_range {X' X: Type*} (ι : X' ↪ X) [Fintype X'] (x : X) :
  ι.attains x ↔ x ∈ ι.range_finset :=
  by
    simp only [attains, range_finset, Finset.mem_image, Finset.mem_univ, true_and]

lemma attains_iff_in_range' {X' X: Type*} (ι : X' ↪ X) [Fintype X'] (x' : X') :ι x' ∈ ι.range_finset :=
(ι.attains_iff_in_range (ι x')).mp $ ι.attains_image x'


lemma avoids_iff_not_in_range {X' X: Type*} (ι : X' ↪ X) [Fintype X'] (x : X) :
  ι.avoids x ↔ x ∉ ι.range_finset := by
    rw [ι.avoids_iff_not_attains]
    exact not_congr $ ι.attains_iff_in_range x

noncomputable def edit {X X' Y: Type*} (ι : X' ↪ X) (f : X → Y) (f' : X' → Y) (x:X) : Y := if h: ι.attains x then f' h.choose else f x

lemma edit_of_attains {X X' Y: Type*} (ι : X' ↪ X) (f : X → Y) (f' : X' → Y) (x': X') : ι.edit f f' (ι x') = f' x' := by
  set h := ι.attains_image x'
  simp only [edit, h, ↓reduceDIte, EmbeddingLike.apply_eq_iff_eq, choose_eq]

lemma edit_of_avoids {X X' Y: Type*} (ι : X' ↪ X) (f : X → Y) (f' : X' → Y) {x: X} (h: ι.avoids x) : ι.edit f f' x = f x := by
  rw [avoids_iff_not_attains] at h
  simp only [edit, h, ↓reduceDIte]



end Function.Embedding
