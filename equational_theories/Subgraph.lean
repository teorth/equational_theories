import Mathlib.Tactic
import Mathlib.Data.Nat.Defs
import Batteries.Util.ProofWanted
import equational_theories.Equations

/- This is a subproject of the main project to completely describe a small subgraph of the entire
implication graph.  Currently we are focusing only on the following equations:

1-8, 38-43, 46, 168, 387, 4512, 4513, 4522, 4582

Implications here should be placed inside the "Subgraph" namespace.
-/

namespace Subgraph

/- Positive implications -/

theorem Equation1_true (G: Type*) [Magma G] : Equation1 G :=
  fun _ ↦ rfl

theorem Equation2_implies_Equation3 (G: Type*) [Magma G] (h: Equation2 G) : Equation3 G :=
  fun _ ↦ h _ _

theorem Equation2_implies_Equation4 (G: Type*) [Magma G] (h: Equation2 G) : Equation4 G :=
  fun _ _ ↦ h _ _

theorem Equation2_implies_Equation5 (G: Type*) [Magma G] (h: Equation2 G) : Equation5 G :=
  fun _ _ ↦ h _ _

theorem Equation2_implies_Equation6 (G: Type*) [Magma G] (h: Equation2 G) : Equation6 G :=
  fun _ _ ↦ h _ _

theorem Equation2_implies_Equation7 (G: Type*) [Magma G] (h: Equation2 G) : Equation7 G :=
  fun _ _ _ ↦ h _ _

theorem Equation2_implies_Equation8 (G: Type*) [Magma G] (h: Equation2 G) : Equation8 G :=
  fun _ ↦ h _ _

theorem Equation2_implies_Equation38 (G: Type*) [Magma G] (h: Equation2 G) : Equation38 G :=
  fun _ _ ↦ h _ _

theorem Equation2_implies_Equation39 (G: Type*) [Magma G] (h: Equation2 G) : Equation39 G :=
  fun _ _ ↦ h _ _

theorem Equation2_implies_Equation40 (G: Type*) [Magma G] (h: Equation2 G) : Equation40 G :=
  fun _ _ ↦ h _ _

theorem Equation2_implies_Equation41 (G: Type*) [Magma G] (h: Equation2 G) : Equation41 G :=
  fun _ _ _ ↦ h _ _

theorem Equation2_implies_Equation42 (G: Type*) [Magma G] (h: Equation2 G) : Equation42 G :=
  fun _ _ _ ↦ h _ _

theorem Equation2_implies_Equation43 (G: Type*) [Magma G] (h: Equation2 G) : Equation43 G :=
  fun _ _ ↦ h _ _

theorem Equation2_implies_Equation46 (G: Type*) [Magma G] (h: Equation2 G) : Equation46 G :=
  fun _ _ _ _ ↦ h _ _

theorem Equation2_implies_Equation168 (G: Type*) [Magma G] (h: Equation2 G) : Equation168 G :=
  fun _ _ _ ↦ h _ _

theorem Equation2_implies_Equation387 (G: Type*) [Magma G] (h: Equation2 G) : Equation387 G :=
  fun _ _ ↦ h _ _

theorem Equation2_implies_Equation4512 (G: Type*) [Magma G] (h: Equation2 G) : Equation4512 G :=
  fun _ _ _ ↦ h _ _

theorem Equation2_implies_Equation4513 (G: Type*) [Magma G] (h: Equation2 G) : Equation4513 G :=
  fun _ _ _ _ ↦ h _ _

theorem Equation2_implies_Equation4522 (G: Type*) [Magma G] (h: Equation2 G) : Equation4522 G :=
  fun _ _ _ _ _ ↦ h _ _

theorem Equation2_implies_Equation4582 (G: Type*) [Magma G] (h: Equation2 G) : Equation4582 G :=
  fun _ _ _ _ _ _ ↦ h _ _

theorem Equation3_implies_Equation8 (G: Type*) [Magma G] (h: Equation3 G) : Equation8 G :=
  fun x ↦ by repeat rw [← h]

theorem Equation4_implies_Equation3 (G: Type*) [Magma G] (h: Equation4 G) : Equation3 G :=
  fun _ ↦ by rw [← h]

theorem Equation4_implies_Equation8 (G: Type*) [Magma G] (h: Equation4 G) : Equation8 G :=
  fun _ ↦ h _ _

theorem Equation4_implies_Equation42 (G: Type*) [Magma G] (h: Equation4 G) : Equation42 G :=
  fun _ _ _ ↦ by rw [← h, ← h]

theorem Equation4_implies_Equation4522 (G: Type*) [Magma G] (h: Equation4 G) : Equation4522 G :=
  fun _ _ _ _ _ ↦ by repeat rw [← h]

theorem Equation5_implies_Equation3 (G: Type*) [Magma G] (h: Equation5 G) : Equation3 G :=
  fun _ ↦ h _ _

theorem Equation5_implies_Equation8 (G: Type*) [Magma G] (h: Equation5 G) : Equation8 G :=
  fun _  ↦ by repeat rw [← h]

theorem Equation5_implies_Equation39 (G: Type*) [Magma G] (h: Equation5 G) : Equation39 G :=
  fun _ _ ↦ by repeat rw [← h]

theorem Equation5_implies_Equation4512 (G: Type*) [Magma G] (h: Equation5 G) : Equation4512 G :=
  fun _ _ _  ↦ by repeat rw [← h]

theorem Equation6_implies_Equation2 (G: Type*) [Magma G] (h: Equation6 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a, ← h]

theorem Equation6_implies_Equation3 (G: Type*) [Magma G] (h: Equation6 G) : Equation3 G :=
  fun _ ↦ h _ _

theorem Equation7_implies_Equation2 (G: Type*) [Magma G] (h: Equation7 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation7_implies_Equation3 (G: Type*) [Magma G] (h: Equation7 G) : Equation3 G :=
  fun _ ↦ h _ _ _

theorem Equation7_implies_Equation41 (G: Type*) [Magma G] (h: Equation7 G) : Equation41 G :=
  fun _ _ _ ↦ by rw [← h]

theorem Equation38_implies_Equation42 (G: Type*) [Magma G] (h: Equation38 G) : Equation42 G :=
  fun _ _ _ ↦ by rw [← h, h]

theorem Equation41_implies_Equation40 (G: Type*) [Magma G] (h: Equation41 G) : Equation40 G :=
  fun _ _ ↦ by rw [h]

theorem Equation41_implies_Equation46 (G: Type*) [Magma G] (h: Equation41 G) : Equation46 G :=
  fun _ _ _ _ ↦ by rwa [← h, h]

theorem Equation42_implies_Equation38 (G: Type*) [Magma G] (h: Equation42 G) : Equation38 G :=
  fun _ _ ↦ by rw [h]

theorem Equation46_implies_Equation40 (G: Type*) [Magma G] (h: Equation46 G) : Equation40 G :=
  fun x y ↦ h x x y y

theorem Equation46_implies_Equation41 (G: Type*) [Magma G] (h: Equation46 G) : Equation41 G :=
  fun _ _ _ => h _ _ _ _

theorem Equation46_implies_Equation42 (G: Type*) [Magma G] (h: Equation46 G) : Equation42 G :=
  fun _ _ _ ↦ h _ _ _ _

theorem Equation46_implies_Equation387 (G: Type*) [Magma G] (h: Equation46 G) : Equation387 G :=
  fun _ _ ↦ h _ _ _ _

theorem Equation46_implies_Equation4582 (G: Type*) [Magma G] (h: Equation46 G) : Equation4582 G :=
  fun _ _ _ _ _ _ ↦ h _ _ _ _

/-- This proof is from https://mathoverflow.net/a/450905/766 -/
theorem Equation387_implies_Equation43 (G: Type*) [Magma G] (h: Equation387 G) : Equation43 G := by
  have idem (x : G) : (x ∘ x) ∘ (x ∘ x) = (x ∘ x) := by rw [← h, ← h]
  have comm (x y : G) : (x ∘ x) ∘ y = y ∘ (x ∘ x) := by rw [← idem, ← h, idem]
  have op_idem (x y : G) : (x ∘ x) ∘ (y ∘ y) = x ∘ y := by rw [← h, ← h]
  exact fun _ _ ↦ by rw [← op_idem, comm, op_idem]

theorem Equation4513_implies_Equation4512 (G: Type*) [Magma G] (h: Equation4513 G) : Equation4512 G :=
  fun _ _ _ ↦ h _ _ _ _

theorem Equation4522_implies_Equation4513 (G: Type*) [Magma G] (h: Equation4522 G) : Equation4513 G :=
  fun _ _ _ _ ↦ h _ _ _ _ _

theorem Equation4582_implies_Equation4522 (G: Type*) [Magma G] (h: Equation4582 G) : Equation4522 G :=
  fun _ _ _ _ _ ↦ h _ _ _ _ _ _

/- Counterexamples -/

theorem Equation3_not_implies_Equation42 : ∃ (G: Type) (_: Magma G), Equation3 G ∧ ¬ Equation42 G := by
  let hG : Magma Nat := { op := fun _ y ↦ y }
  refine ⟨ℕ, hG, fun _ ↦ rfl, ?_⟩
  by_contra h
  specialize h 0 1 2
  simp [hG] at h

theorem Equation3_not_implies_Equation4512 : ∃ (G: Type) (_: Magma G), Equation3 G ∧ ¬ Equation4512 G := by
  let hG : Magma Nat := { op := fun x y ↦ if x = y then x else x + 1 }
  refine ⟨ℕ, hG, fun _ ↦ by simp [hG], ?_⟩
  by_contra h
  specialize h 1 2 3
  simp [hG] at h

-- The 2 element magma that satisfies 4 does not satisfy 40.
proof_wanted Equation4_not_implies_Equation40 : ∃ (G: Type) (_: Magma G), Equation4 G ∧ ¬ Equation40 G

theorem Equation4_not_implies_Equation43 : ∃ (G: Type) (_: Magma G), Equation4 G ∧ ¬ Equation43 G := by
  let hG : Magma Nat := { op := fun x _ ↦ x }
  refine ⟨ℕ, hG, fun _ _ ↦ rfl, ?_⟩
  by_contra h
  specialize h 1 0
  dsimp [hG] at h
  linarith

theorem Equation4_not_implies_Equation4582 : ∃ (G: Type) (_: Magma G), Equation4 G ∧ ¬ Equation4582 G := by
  let hG : Magma Nat := { op := fun x _ ↦ x }
  refine ⟨ℕ, hG, fun _ _ ↦ rfl, ?_⟩
  by_contra h
  specialize h 0 0 0 1 0 0
  dsimp [hG] at h
  linarith

-- The magma with 2 elements a and b which satisfies equation 5 serves as counterexamples here. For 43, a * b = b, but b * a = a. For 4513, a * (a * a) = a, but (a * a) * b = b.

theorem Equation5_not_implies_Equation42 : ∃ (G: Type) (_: Magma G), Equation5 G ∧ ¬ Equation42 G := by
  let a : Type := Fin 2
  let hG : Magma a := { op := fun _ x ↦ x }
  refine ⟨a, hG, fun _ ↦ by simp [hG], ?_⟩
  by_contra h
  specialize h 0 1 0
  simp [hG] at h

theorem Equation5_not_implies_Equation43 : ∃ (G: Type) (_: Magma G), Equation5 G ∧ ¬ Equation43 G := by
  let a : Type := Fin 2
  let hG : Magma a := { op := fun _ x ↦ x }
  refine ⟨a, hG, fun _ ↦ by simp [hG], ?_⟩
  by_contra h
  specialize h 0 1
  simp [hG] at h

theorem Equation5_not_implies_Equation4513 : ∃ (G: Type) (_: Magma G), Equation5 G ∧ ¬ Equation4513 G := by
  let a : Type := Fin 2
  let hG : Magma a := { op := fun _ x ↦ x }
  refine ⟨a, hG, fun _ ↦ by simp [hG], ?_⟩
  by_contra h
  specialize h 0 0 0 1
  simp [hG] at h

-- For the next few implications, use the "implies" magma with two elements, true and false, where "true implies false" is false and all other pairs are true

proof_wanted Equation40_not_implies_Equation3 : ∃ (G: Type) (_: Magma G), Equation40 G ∧ ¬ Equation3 G

proof_wanted Equation40_not_implies_Equation8 : ∃ (G: Type) (_: Magma G), Equation40 G ∧ ¬ Equation8 G

proof_wanted Equation40_not_implies_Equation42 : ∃ (G: Type) (_: Magma G), Equation40 G ∧ ¬ Equation42 G

proof_wanted Equation40_not_implies_Equation43 : ∃ (G: Type) (_: Magma G), Equation40 G ∧ ¬ Equation43 G

proof_wanted Equation40_not_implies_Equation4512 : ∃ (G: Type) (_: Magma G), Equation40 G ∧ ¬ Equation4512 G

theorem Equation42_not_implies_Equation43 : ∃ (G: Type) (_: Magma G), Equation42 G ∧ ¬ Equation43 G := by
  let hG : Magma Nat := { op := fun x _ ↦ x }
  refine ⟨ℕ, hG, fun _ _ _ ↦ rfl, ?_⟩
  by_contra h
  specialize h 0 1
  dsimp [hG] at h
  linarith

theorem Equation42_not_implies_Equation4512 : ∃ (G: Type) (_: Magma G), Equation42 G ∧ ¬ Equation4512 G := by
  let hG : Magma Nat := { op := fun x _ ↦ x + 1 }
  refine ⟨ℕ, hG, fun _ _ _ ↦ rfl, ?_⟩
  by_contra h
  specialize h 0 0 0
  dsimp [hG] at h
  linarith

theorem Equation43_not_implies_Equation3 : ∃ (G: Type) (_: Magma G), Equation43 G ∧ ¬ Equation3 G := by
  let hG : Magma Nat := { op := fun x y ↦ x+y }
  refine ⟨ℕ, hG, fun _ _ ↦ Nat.add_comm _ _, ?_⟩
  by_contra h
  specialize h 1
  simp [hG] at h

theorem Equation43_not_implies_Equation42 : ∃ (G: Type) (_: Magma G), Equation43 G ∧ ¬ Equation42 G := by
  let hG : Magma Nat := { op := fun x y ↦ x+y }
  refine ⟨ℕ, hG, fun _ _ ↦ Nat.add_comm _ _, ?_⟩
  by_contra h
  specialize h 0 0 1
  dsimp [hG] at h
  linarith

theorem Equation43_not_implies_Equation387 : ∃ (G: Type) (_: Magma G), Equation43 G ∧ ¬ Equation387 G := by
  let hG : Magma Nat := { op := fun x y ↦ x + y }
  refine ⟨ℕ, hG, fun _ _ ↦ Nat.add_comm _ _, ?_⟩
  by_contra h
  specialize h 0 1
  dsimp [hG] at h
  linarith

theorem Equation43_not_implies_Equation4512 : ∃ (G: Type) (_: Magma G), Equation43 G ∧ ¬ Equation4512 G := by
  let hG : Magma Nat := { op := fun x y ↦ x * y + 1 }
  refine ⟨ℕ, hG, fun _ _ ↦ ?_, ?_⟩
  . dsimp [hG]
    ring
  · by_contra h
    specialize h 0 0 1
    dsimp [hG] at h
    linarith

theorem Equation46_not_implies_Equation3 : ∃ (G: Type) (_: Magma G), Equation46 G ∧ ¬ Equation3 G := by
  let hG : Magma Nat := { op := fun _ _ ↦ 0 }
  refine ⟨ℕ, hG, fun _ _ _ _ ↦ rfl, ?_⟩
  by_contra h
  specialize h 1
  dsimp [hG] at h
  linarith

theorem Equation46_not_implies_Equation4 : ∃ (G: Type) (_: Magma G), Equation46 G ∧ ¬ Equation4 G := by
  let hG : Magma Nat := { op := fun _ _ ↦ 0 }
  refine ⟨ℕ, hG, fun _ _ _ _ ↦ rfl, ?_⟩
  by_contra h
  specialize h 1 0
  dsimp [hG] at h
  linarith

-- The "and" magma on the two element set of booleans satisfies 387, but does not satisfy 40.
proof_wanted Equation387_not_implies_Equation40 : ∃ (G: Type) (_: Magma G), Equation4 G ∧ ¬ Equation40 G

theorem Equation387_not_implies_Equation42 : ∃ (G: Type) (_: Magma G), Equation387 G ∧ ¬ Equation42 G := by
  let hG : Magma Bool := { op := fun x y ↦ x || y }
  refine ⟨Bool, hG, fun _ _ ↦ by simp [hG, Bool.or_comm], ?_⟩
  by_contra h
  specialize h false true false
  simp [hG] at h

theorem Equation387_not_implies_Equation4512 : ∃ (G: Type) (_: Magma G), Equation387 G ∧ ¬ Equation4512 G := by
  let hG : Magma Real := { op := fun x y ↦ (x + y) / 2 }
  refine ⟨ℝ, hG, fun _ _ ↦ ?_, ?_⟩
  . dsimp [hG]
    ring
  · by_contra h
    specialize h 0 0 1
    field_simp [hG] at h

theorem Equation4512_not_implies_Equation42 : ∃ (G: Type) (_: Magma G), Equation4512 G ∧ ¬ Equation42 G := by
  let hG : Magma Nat := { op := fun x y ↦ x + y }
  refine ⟨ℕ, hG, fun _ _ _ ↦ ?_, ?_⟩
  . dsimp [hG]
    abel
  · by_contra h
    specialize h 0 0 1
    dsimp [hG] at h
    linarith

theorem Equation4512_not_implies_Equation4513 : ∃ (G: Type) (_: Magma G), Equation4512 G ∧ ¬ Equation4513 G := by
  let hG : Magma Nat := { op := fun x y ↦ x + y }
  refine ⟨ℕ, hG, fun _ _ _ ↦ ?_, ?_⟩
  . dsimp [hG]
    abel
  · by_contra h
    specialize h 0 0 0 1
    dsimp [hG] at h
    linarith

theorem Equation4513_not_implies_Equation4522 : ∃ (G: Type) (_: Magma G), Equation4513 G ∧ ¬ Equation4522 G := by
  let hG : Magma Nat := { op := fun x y ↦ if x = 0 then (if y ≤ 2 then 1 else 2) else x }
  refine ⟨ℕ, hG, fun _ _ _ _ ↦ ?_, ?_⟩
  . dsimp [hG]
    split_ifs <;> simp_all
  · by_contra h
    specialize h 0 0 0 3 3
    dsimp [hG] at h
    linarith

-- use "saturating addition" on the set {1, 2, 3}, where we add in the normal way but cap the result at 3 (x*y = min(3, x+y)).
proof_wanted Equation4582_not_implies_Equation40 : ∃ (G: Type) (_: Magma G), Equation4582 G ∧ ¬ Equation40 G

theorem Equation4582_not_implies_Equation42 : ∃ (G: Type) (_: Magma G), Equation4582 G ∧ ¬ Equation42 G := by
  let hG : Magma Nat := { op := fun x y ↦ if x = 0 ∧ y = 0 then 1 else 2 }
  refine ⟨ℕ, hG, fun _ _ _ _ _ _ ↦ ?_, ?_⟩
  . dsimp [hG]
    split_ifs <;> simp_all
  · by_contra h
    specialize h 0 0 1
    dsimp [hG] at h
    linarith

theorem Equation4582_not_implies_Equation43 : ∃ (G: Type) (_: Magma G), Equation4582 G ∧ ¬ Equation43 G := by
  let hG : Magma Nat := { op := fun x y ↦ if x = 1 ∧ y = 2 then 3 else 4 }
  refine ⟨ℕ, hG, fun _ _ _ _ _ _ ↦ ?_, ?_⟩
  . dsimp [hG]
    split_ifs <;> simp_all
  · by_contra h
    specialize h 1 2
    dsimp [hG] at h
    linarith


end Subgraph
