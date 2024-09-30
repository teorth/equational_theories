import Mathlib.Tactic
import Mathlib.Data.Nat.Defs
import equational_theories.Conjecture
import equational_theories.EquationalResult
import equational_theories.Equations

/- This is a subproject of the main project to completely describe a small subgraph of the entire
implication graph.  Currently we are focusing only on the following equations:

1-8, 14, 23, 29, 38-43, 45-46, 168, 381, 387, 3722, 4378, 4512, 4513, 4522, 4564, 4582

Implications here should be placed inside the "Subgraph" namespace.

-/
namespace Subgraph

/- Positive implications -/

@[equational_result]
theorem Equation1_true (G: Type*) [Magma G] : Equation1 G :=
  fun _ ↦ rfl

@[equational_result]
theorem Equation2_implies_Equation3 (G: Type*) [Magma G] (h: Equation2 G) : Equation3 G :=
  fun _ ↦ h _ _

@[equational_result]
theorem Equation2_implies_Equation4 (G: Type*) [Magma G] (h: Equation2 G) : Equation4 G :=
  fun _ _ ↦ h _ _

@[equational_result]
theorem Equation2_implies_Equation5 (G: Type*) [Magma G] (h: Equation2 G) : Equation5 G :=
  fun _ _ ↦ h _ _

@[equational_result]
theorem Equation2_implies_Equation6 (G: Type*) [Magma G] (h: Equation2 G) : Equation6 G :=
  fun _ _ ↦ h _ _

@[equational_result]
theorem Equation2_implies_Equation7 (G: Type*) [Magma G] (h: Equation2 G) : Equation7 G :=
  fun _ _ _ ↦ h _ _

@[equational_result]
theorem Equation2_implies_Equation8 (G: Type*) [Magma G] (h: Equation2 G) : Equation8 G :=
  fun _ ↦ h _ _

@[equational_result]
theorem Equation2_implies_Equation23 (G: Type*) [Magma G] (h: Equation2 G) : Equation23 G :=
  fun _ ↦ h _ _

@[equational_result]
theorem Equation2_implies_Equation38 (G: Type*) [Magma G] (h: Equation2 G) : Equation38 G :=
  fun _ _ ↦ h _ _

@[equational_result]
theorem Equation2_implies_Equation39 (G: Type*) [Magma G] (h: Equation2 G) : Equation39 G :=
  fun _ _ ↦ h _ _

@[equational_result]
theorem Equation2_implies_Equation40 (G: Type*) [Magma G] (h: Equation2 G) : Equation40 G :=
  fun _ _ ↦ h _ _

@[equational_result]
theorem Equation2_implies_Equation41 (G: Type*) [Magma G] (h: Equation2 G) : Equation41 G :=
  fun _ _ _ ↦ h _ _

@[equational_result]
theorem Equation2_implies_Equation42 (G: Type*) [Magma G] (h: Equation2 G) : Equation42 G :=
  fun _ _ _ ↦ h _ _

@[equational_result]
theorem Equation2_implies_Equation43 (G: Type*) [Magma G] (h: Equation2 G) : Equation43 G :=
  fun _ _ ↦ h _ _

@[equational_result]
theorem Equation2_implies_Equation46 (G: Type*) [Magma G] (h: Equation2 G) : Equation46 G :=
  fun _ _ _ _ ↦ h _ _

@[equational_result]
theorem Equation2_implies_Equation168 (G: Type*) [Magma G] (h: Equation2 G) : Equation168 G :=
  fun _ _ _ ↦ h _ _

@[equational_result]
theorem Equation2_implies_Equation387 (G: Type*) [Magma G] (h: Equation2 G) : Equation387 G :=
  fun _ _ ↦ h _ _

@[equational_result]
theorem Equation2_implies_Equation4512 (G: Type*) [Magma G] (h: Equation2 G) : Equation4512 G :=
  fun _ _ _ ↦ h _ _

@[equational_result]
theorem Equation2_implies_Equation4513 (G: Type*) [Magma G] (h: Equation2 G) : Equation4513 G :=
  fun _ _ _ _ ↦ h _ _

@[equational_result]
theorem Equation2_implies_Equation4522 (G: Type*) [Magma G] (h: Equation2 G) : Equation4522 G :=
  fun _ _ _ _ _ ↦ h _ _

@[equational_result]
theorem Equation2_implies_Equation4582 (G: Type*) [Magma G] (h: Equation2 G) : Equation4582 G :=
  fun _ _ _ _ _ _ ↦ h _ _

@[equational_result]
theorem Equation3_implies_Equation8 (G: Type*) [Magma G] (h: Equation3 G) : Equation8 G :=
  fun x ↦ by repeat rw [← h]

@[equational_result]
theorem Equation3_implies_Equation23 (G: Type*) [Magma G] (h: Equation3 G) : Equation23 G :=
  fun x ↦ by repeat rw [← h]

theorem Equation4_implies_Equation3 (G: Type*) [Magma G] (h: Equation4 G) : Equation3 G :=
  fun _ ↦ by rw [← h]

@[equational_result]
theorem Equation4_implies_Equation8 (G: Type*) [Magma G] (h: Equation4 G) : Equation8 G :=
  fun _ ↦ h _ _

@[equational_result]
theorem Equation4_implies_Equation23 (G: Type*) [Magma G] (h: Equation4 G) : Equation23 G :=
  Equation3_implies_Equation23 G fun _ ↦ h _ _

@[equational_result]
theorem Equation4_implies_Equation42 (G: Type*) [Magma G] (h: Equation4 G) : Equation42 G :=
  fun _ _ _ ↦ by rw [← h, ← h]

@[equational_result]
theorem Equation4_implies_Equation4522 (G: Type*) [Magma G] (h: Equation4 G) : Equation4522 G :=
  fun _ _ _ _ _ ↦ by repeat rw [← h]

@[equational_result]
theorem Equation5_implies_Equation3 (G: Type*) [Magma G] (h: Equation5 G) : Equation3 G :=
  fun _ ↦ h _ _

@[equational_result]
theorem Equation5_implies_Equation8 (G: Type*) [Magma G] (h: Equation5 G) : Equation8 G :=
  fun _  ↦ by repeat rw [← h]

@[equational_result]
theorem Equation5_implies_Equation23 (G: Type*) [Magma G] (h: Equation5 G) : Equation23 G :=
  fun _  ↦ by repeat rw [← h]

@[equational_result]
theorem Equation5_implies_Equation39 (G: Type*) [Magma G] (h: Equation5 G) : Equation39 G :=
  fun _ _ ↦ by repeat rw [← h]

@[equational_result]
theorem Equation5_implies_Equation4512 (G: Type*) [Magma G] (h: Equation5 G) : Equation4512 G :=
  fun _ _ _  ↦ by repeat rw [← h]

@[equational_result]
theorem Equation6_implies_Equation2 (G: Type*) [Magma G] (h: Equation6 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a, ← h]

@[equational_result]
theorem Equation6_implies_Equation3 (G: Type*) [Magma G] (h: Equation6 G) : Equation3 G :=
  fun _ ↦ h _ _

@[equational_result]
theorem Equation7_implies_Equation2 (G: Type*) [Magma G] (h: Equation7 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

@[equational_result]
theorem Equation7_implies_Equation3 (G: Type*) [Magma G] (h: Equation7 G) : Equation3 G :=
  fun _ ↦ h _ _ _

@[equational_result]
theorem Equation7_implies_Equation41 (G: Type*) [Magma G] (h: Equation7 G) : Equation41 G :=
  fun _ _ _ ↦ by rw [← h]

/-- Dual to Problem A1 from Putnam 2001 -/
conjecture Equation14_implies_Equation29 (G: Type*) [Magma G] (h: Equation14 G) : Equation29 G

/-- This implication is Problem A1 from Putnam 2001 -/
@[equational_result]
theorem Equation29_implies_Equation14 (G: Type*) [Magma G] (h: Equation29 G) : Equation14 G :=
  fun x y ↦ Eq.trans (h x (x ∘ y)) (congrArg (fun z ↦ z ∘ (x ∘ y)) (Eq.symm (h y x)))

@[equational_result]
theorem Equation38_implies_Equation42 (G: Type*) [Magma G] (h: Equation38 G) : Equation42 G :=
  fun _ _ _ ↦ by rw [← h, h]

@[equational_result]
theorem Equation39_implies_Equation45 (G: Type*) [Magma G] (h: Equation39 G) : Equation45 G :=
  fun _ _ _ ↦ by rw[← h, h]

@[equational_result]
theorem Equation41_implies_Equation39 (G: Type*) [Magma G] (h: Equation41 G) : Equation39 G :=
  fun _ _ ↦ by rw [h]

@[equational_result]
theorem Equation41_implies_Equation40 (G: Type*) [Magma G] (h: Equation41 G) : Equation40 G :=
  fun _ _ ↦ by rw [h]

@[equational_result]
theorem Equation41_implies_Equation46 (G: Type*) [Magma G] (h: Equation41 G) : Equation46 G :=
  fun _ _ _ _ ↦ by rwa [← h, h]

@[equational_result]
theorem Equation42_implies_Equation38 (G: Type*) [Magma G] (h: Equation42 G) : Equation38 G :=
  fun _ _ ↦ by rw [h]

@[equational_result]
theorem Equation45_implies_Equation39 (G: Type*) [Magma G] (h: Equation45 G) : Equation39 G :=
  fun _ _ ↦ by rw [h]

@[equational_result]
theorem Equation46_implies_Equation39 (G: Type*) [Magma G] (h: Equation46 G) : Equation39 G :=
  fun _ _ ↦ h _ _ _ _

@[equational_result]
theorem Equation46_implies_Equation40 (G: Type*) [Magma G] (h: Equation46 G) : Equation40 G :=
  fun _ _ ↦ h _ _ _ _

@[equational_result]
theorem Equation46_implies_Equation41 (G: Type*) [Magma G] (h: Equation46 G) : Equation41 G :=
  fun _ _ _ ↦ h _ _ _ _

@[equational_result]
theorem Equation46_implies_Equation42 (G: Type*) [Magma G] (h: Equation46 G) : Equation42 G :=
  fun _ _ _ ↦ h _ _ _ _

@[equational_result]
theorem Equation46_implies_Equation387 (G: Type*) [Magma G] (h: Equation46 G) : Equation387 G :=
  fun _ _ ↦ h _ _ _ _

@[equational_result]
theorem Equation46_implies_Equation4582 (G: Type*) [Magma G] (h: Equation46 G) : Equation4582 G :=
  fun _ _ _ _ _ _ ↦ h _ _ _ _

/-- This proof is from https://mathoverflow.net/a/450905/766 -/
@[equational_result]
theorem Equation387_implies_Equation43 (G: Type*) [Magma G] (h: Equation387 G) : Equation43 G := by
  have idem (x : G) : (x ∘ x) ∘ (x ∘ x) = (x ∘ x) := by repeat rw [← h]
  have comm (x y : G) : (x ∘ x) ∘ y = y ∘ (x ∘ x) := by rw [← idem, ← h, idem]
  have op_idem (x y : G) : (x ∘ x) ∘ (y ∘ y) = x ∘ y := by repeat rw [← h]
  exact fun _ _ ↦ by rw [← op_idem, comm, op_idem]

conjecture Equation1689_implies_Equation2 (G: Type*) [Magma G] (h: Equation1689 G) : Equation2 G

/-- Putnam 1978, problem A4, part (b) -/
@[equational_result]
theorem Equation3744_implies_Equation381 (G : Type*) [Magma G] (h: Equation3744 G) : Equation381 G :=
  fun x y z ↦ Eq.trans
    (h x y z y) $ Eq.trans
    (congrArg (fun a ↦ a ∘ (y ∘ y)) (h x z z x))
    (Eq.symm $ h (x ∘ z) y (x ∘ z) y)

/-- Putnam 1978, problem A4, part (a) -/
@[equational_result]
theorem Equation3744_implies_Equation3722 (G: Type*) [Magma G] (h: Equation3744 G) : Equation3722 G :=
  fun _ _ ↦ h _ _ _ _

@[equational_result]
theorem Equation4513_implies_Equation4512 (G: Type*) [Magma G] (h: Equation4513 G) : Equation4512 G :=
  fun _ _ _ ↦ h _ _ _ _

@[equational_result]
theorem Equation4522_implies_Equation4513 (G: Type*) [Magma G] (h: Equation4522 G) : Equation4513 G :=
  fun _ _ _ _ ↦ h _ _ _ _ _

@[equational_result]
theorem Equation4582_implies_Equation4522 (G: Type*) [Magma G] (h: Equation4582 G) : Equation4522 G :=
  fun _ _ _ _ _ ↦ h _ _ _ _ _ _

@[equational_result]
theorem Equation4582_implies_Equation4564 (G: Type*) [Magma G] (h: Equation4582 G) : Equation4564 G :=
  fun _ _ _ _ ↦ h _ _ _ _ _ _

@[equational_result]
theorem Equation4582_implies_Equation4579 (G: Type*) [Magma G] (h: Equation4582 G) : Equation4579 G :=
  fun _ _ _ _ _ ↦ h _ _ _ _ _ _

/- Counterexamples -/

@[equational_result]
theorem Equation3_not_implies_Equation39 : ∃ (G: Type) (_: Magma G), Equation3 G ∧ ¬ Equation39 G :=
  ⟨Fin 3, ⟨fun x y ↦ 2 * x - y⟩, by decide⟩

@[equational_result]
theorem Equation3_not_implies_Equation42 : ∃ (G: Type) (_: Magma G), Equation3 G ∧ ¬ Equation42 G := by
  let hG : Magma ℕ := { op := fun _ y ↦ y }
  refine ⟨ℕ, hG, fun _ ↦ rfl, ?_⟩
  by_contra h
  specialize h 0 1 2
  simp [hG] at h

@[equational_result]
theorem Equation3_not_implies_Equation4512 : ∃ (G: Type) (_: Magma G), Equation3 G ∧ ¬ Equation4512 G := by
  let hG : Magma ℕ := { op := fun x y ↦ if x = y then x else x + 1 }
  refine ⟨ℕ, hG, fun _ ↦ by simp [hG], ?_⟩
  by_contra h
  specialize h 1 2 3
  simp [hG] at h

@[equational_result]
theorem Equation4_not_implies_Equation39 : ∃ (G: Type) (_: Magma G), Equation4 G ∧ ¬ Equation39 G :=
  ⟨Fin 2, ⟨fun x _ ↦ x⟩, by decide⟩

-- The 2 element magma that satisfies 4 does not satisfy 40.
@[equational_result]
theorem Equation4_not_implies_Equation40 : ∃ (G: Type) (_: Magma G), Equation4 G ∧ ¬ Equation40 G := by
  let a : Type := Fin 2
  let hG : Magma a := { op := fun x _ ↦ x }
  refine ⟨a, hG, fun _ ↦ by simp [hG], ?_⟩
  by_contra h
  specialize h 0 1
  simp [hG] at h

@[equational_result]
theorem Equation4_not_implies_Equation43 : ∃ (G: Type) (_: Magma G), Equation4 G ∧ ¬ Equation43 G := by
  let hG : Magma ℕ := { op := fun x _ ↦ x }
  refine ⟨ℕ, hG, fun _ _ ↦ rfl, ?_⟩
  by_contra h
  specialize h 1 0
  dsimp [hG] at h
  linarith

@[equational_result]
theorem Equation4_not_implies_Equation4582 : ∃ (G: Type) (_: Magma G), Equation4 G ∧ ¬ Equation4582 G := by
  let hG : Magma ℕ := { op := fun x _ ↦ x }
  refine ⟨ℕ, hG, fun _ _ ↦ rfl, ?_⟩
  by_contra h
  specialize h 0 0 0 1 0 0
  dsimp [hG] at h
  linarith

-- The magma with 2 elements a and b which satisfies equation 5 serves as counterexamples here. For 43, a * b = b, but b * a = a. For 4513, a * (a * a) = a, but (a * a) * b = b.

@[equational_result]
theorem Equation5_not_implies_Equation42 : ∃ (G: Type) (_: Magma G), Equation5 G ∧ ¬ Equation42 G := by
  let a : Type := Fin 2
  let hG : Magma a := { op := fun _ x ↦ x }
  refine ⟨a, hG, fun _ ↦ by simp [hG], ?_⟩
  by_contra h
  specialize h 0 1 0
  simp [hG] at h

@[equational_result]
theorem Equation5_not_implies_Equation43 : ∃ (G: Type) (_: Magma G), Equation5 G ∧ ¬ Equation43 G := by
  let a : Type := Fin 2
  let hG : Magma a := { op := fun _ x ↦ x }
  refine ⟨a, hG, fun _ ↦ by simp [hG], ?_⟩
  by_contra h
  specialize h 0 1
  simp [hG] at h

@[equational_result]
theorem Equation5_not_implies_Equation4513 : ∃ (G: Type) (_: Magma G), Equation5 G ∧ ¬ Equation4513 G := by
  let a : Type := Fin 2
  let hG : Magma a := { op := fun _ x ↦ x }
  refine ⟨a, hG, fun _ ↦ by simp [hG], ?_⟩
  by_contra h
  specialize h 0 0 0 1
  simp [hG] at h

@[equational_result]
theorem Equation8_not_implies_Equation3 : ∃ (G : Type) (_ : Magma G), Equation8 G ∧ ¬ Equation3 G := by
  simp only [not_forall]
  exact ⟨Fin 2, ⟨(. + .)⟩, by decide, 1, one_ne_zero⟩

@[equational_result]
theorem Equation23_not_implies_Equation3 : ∃ (G : Type) (_ : Magma G), Equation23 G ∧ ¬ Equation3 G := by
  simp only [not_forall]
  exact ⟨Fin 2, ⟨(· + ·)⟩, by decide, 1, one_ne_zero⟩

@[equational_result]
theorem Equation38_not_implies_Equation23 : ∃ (G : Type) (_ : Magma G), Equation38 G ∧ ¬ Equation23 G := by
  simp only [not_forall]
  exact ⟨ℕ, ⟨fun x _ ↦ x + 1⟩, fun _ _ ↦ rfl, 0, Nat.zero_ne_add_one _⟩

@[equational_result]
theorem Equation23_not_implies_Equation39 : ∃ (G: Type) (_: Magma G), Equation23 G ∧ ¬ Equation39 G :=
  ⟨Fin 2, ⟨fun x _ ↦ x⟩, by decide⟩

@[equational_result]
theorem Equation39_not_implies_Equation8 : ∃ (G : Type) (_ : Magma G), Equation39 G ∧ ¬ Equation8 G := by
  simp only [not_forall]
  refine ⟨ℕ, ⟨fun _ y ↦ y + 1⟩, fun _ _ ↦ rfl, 0, ?_⟩
  simp only [zero_add, Nat.reduceAdd, OfNat.zero_ne_ofNat, not_false_eq_true]

@[equational_result]
theorem Equation39_not_implies_Equation23 : ∃ (G : Type) (_ : Magma G), Equation39 G ∧ ¬ Equation23 G := by
  simp only [not_forall]
  exact ⟨ℕ, ⟨fun _ _ ↦ _ + 1⟩, fun _ _ ↦ rfl, 0, Nat.zero_ne_add_one 0⟩

@[equational_result]
theorem Equation39_not_implies_Equation40 : ∃ (G: Type) (_: Magma G), Equation39 G ∧ ¬ Equation40 G :=
  ⟨Fin 2, ⟨fun _ x ↦ x + 1⟩, by decide⟩

@[equational_result]
theorem Equation39_not_implies_Equation168 : ∃ (G : Type) (_ : Magma G), Equation39 G ∧ ¬ Equation168 G := by
  simp only [not_forall]
  exact ⟨ℕ, ⟨fun _ y ↦ y⟩, (fun _ _ ↦ rfl), 0, 0, 1, nofun⟩

@[equational_result]
theorem Equation39_not_implies_Equation4512 : ∃ (G: Type) (_: Magma G), Equation39 G ∧ ¬ Equation4512 G :=
  ⟨Fin 2, ⟨fun _ x ↦ x + 1⟩, by decide⟩

@[equational_result]
theorem Equation39_not_implies_Equation4513 : ∃ (G: Type) (_: Magma G), Equation39 G ∧ ¬ Equation4513 G :=
  ⟨Fin 2, ⟨fun _ x ↦ x + 1⟩, by decide⟩

@[equational_result]
theorem Equation39_not_implies_Equation4522 : ∃ (G: Type) (_: Magma G), Equation39 G ∧ ¬ Equation4522 G :=
  ⟨Fin 2, ⟨fun _ x ↦ x + 1⟩, by decide⟩

@[equational_result]
theorem Equation39_not_implies_Equation4564 : ∃ (G: Type) (_: Magma G), Equation39 G ∧ ¬ Equation4564 G :=
  ⟨Fin 2, ⟨fun _ x ↦ x + 1⟩, by decide⟩

@[equational_result]
theorem Equation39_not_implies_Equation4579 : ∃ (G: Type) (_: Magma G), Equation39 G ∧ ¬ Equation4579 G :=
  ⟨Fin 2, ⟨fun _ x ↦ x + 1⟩, by decide⟩

@[equational_result]
theorem Equation39_not_implies_Equation4582 : ∃ (G: Type) (_: Magma G), Equation39 G ∧ ¬ Equation4582 G :=
  ⟨Fin 2, ⟨fun _ x ↦ x + 1⟩, by decide⟩

@[equational_result]
theorem Equation40_not_implies_Equation3 : ∃ (G: Type) (_: Magma G), Equation40 G ∧ ¬ Equation3 G := by
  let a : Type := Bool
  let hG : Magma a := { op := fun x y ↦ ¬ x ∨ y }
  exact ⟨a, hG, fun _ ↦ by simp [hG], of_decide_eq_false rfl⟩

@[equational_result]
theorem Equation40_not_implies_Equation39 : ∃ (G: Type) (_: Magma G), Equation40 G ∧ ¬ Equation39 G :=
  ⟨Fin 2, ⟨fun x y ↦ x - y⟩, by decide⟩

@[equational_result]
theorem Equation40_not_implies_Equation42 : ∃ (G: Type) (_: Magma G), Equation40 G ∧ ¬ Equation42 G := by
  let a : Type := Bool
  let hG : Magma a := { op := fun x y ↦ ¬ x ∨ y }
  exact ⟨a, hG, fun _ ↦ by simp [hG], of_decide_eq_false rfl⟩

@[equational_result]
theorem Equation40_not_implies_Equation43 : ∃ (G: Type) (_: Magma G), Equation40 G ∧ ¬ Equation43 G := by
  let a : Type := Bool
  let hG : Magma a := { op := fun x y ↦ ¬ x ∨ y }
  exact ⟨a, hG, fun _ ↦ by simp [hG], of_decide_eq_false rfl⟩

@[equational_result]
theorem Equation40_not_implies_Equation4512 : ∃ (G: Type) (_: Magma G), Equation40 G ∧ ¬ Equation4512 G := by
  let a : Type := Bool
  let hG : Magma a := { op := fun x y ↦ ¬ x ∨ y }
  exact ⟨a, hG, fun _ ↦ by simp [hG], of_decide_eq_false rfl⟩

@[equational_result]
theorem Equation42_not_implies_Equation43 : ∃ (G: Type) (_: Magma G), Equation42 G ∧ ¬ Equation43 G := by
  let hG : Magma ℕ := { op := fun x _ ↦ x }
  refine ⟨ℕ, hG, fun _ _ _ ↦ rfl, ?_⟩
  by_contra h
  specialize h 0 1
  dsimp [hG] at h
  linarith

@[equational_result]
theorem Equation42_not_implies_Equation4512 : ∃ (G: Type) (_: Magma G), Equation42 G ∧ ¬ Equation4512 G := by
  let hG : Magma ℕ := { op := fun x _ ↦ x + 1 }
  refine ⟨ℕ, hG, fun _ _ _ ↦ rfl, ?_⟩
  by_contra h
  specialize h 0 0 0
  dsimp [hG] at h
  linarith

@[equational_result]
theorem Equation43_not_implies_Equation3 : ∃ (G: Type) (_: Magma G), Equation43 G ∧ ¬ Equation3 G := by
  let hG : Magma ℕ := { op := fun x y ↦ x+y }
  refine ⟨ℕ, hG, fun _ _ ↦ Nat.add_comm _ _, ?_⟩
  by_contra h
  specialize h 1
  simp [hG] at h

@[equational_result]
theorem Equation43_not_implies_Equation39 : ∃ (G: Type) (_: Magma G), Equation43 G ∧ ¬ Equation3 G := by
  let hG : Magma ℕ := { op := fun x y ↦ x+y }
  refine ⟨ℕ, hG, fun _ _ ↦ Nat.add_comm _ _, ?_⟩
  by_contra h
  specialize h 1
  simp [hG] at h

@[equational_result]
theorem Equation43_not_implies_Equation42 : ∃ (G: Type) (_: Magma G), Equation43 G ∧ ¬ Equation42 G := by
  let hG : Magma ℕ := { op := fun x y ↦ x+y }
  refine ⟨ℕ, hG, fun _ _ ↦ Nat.add_comm _ _, ?_⟩
  by_contra h
  specialize h 0 0 1
  dsimp [hG] at h
  linarith

@[equational_result]
theorem Equation43_not_implies_Equation387 : ∃ (G: Type) (_: Magma G), Equation43 G ∧ ¬ Equation387 G := by
  let hG : Magma ℕ := { op := fun x y ↦ x + y }
  refine ⟨ℕ, hG, fun _ _ ↦ Nat.add_comm _ _, ?_⟩
  by_contra h
  specialize h 0 1
  dsimp [hG] at h
  linarith

@[equational_result]
theorem Equation43_not_implies_Equation4512 : ∃ (G: Type) (_: Magma G), Equation43 G ∧ ¬ Equation4512 G := by
  let hG : Magma ℕ := { op := fun x y ↦ x * y + 1 }
  refine ⟨ℕ, hG, fun _ _ ↦ ?_, ?_⟩
  . dsimp [hG]
    ring
  · by_contra h
    specialize h 0 0 1
    dsimp [hG] at h
    linarith

@[equational_result]
theorem Equation46_not_implies_Equation3 : ∃ (G: Type) (_: Magma G), Equation46 G ∧ ¬ Equation3 G := by
  let hG : Magma ℕ := { op := fun _ _ ↦ 0 }
  refine ⟨ℕ, hG, fun _ _ _ _ ↦ rfl, ?_⟩
  by_contra h
  specialize h 1
  dsimp [hG] at h
  linarith

@[equational_result]
theorem Equation46_not_implies_Equation4 : ∃ (G: Type) (_: Magma G), Equation46 G ∧ ¬ Equation4 G := by
  let hG : Magma ℕ := { op := fun _ _ ↦ 0 }
  refine ⟨ℕ, hG, fun _ _ _ _ ↦ rfl, ?_⟩
  by_contra h
  specialize h 1 0
  dsimp [hG] at h
  linarith

@[equational_result]
theorem Equation168_not_implies_Equation8 : ∃ (G : Type) (_ : Magma G), Equation168 G ∧ ¬ Equation8 G :=
  ⟨Bool × Bool, ⟨fun x y ↦ ⟨x.snd,y.fst⟩⟩, fun _ _ _ ↦ rfl, of_decide_eq_false rfl⟩

@[equational_result]
theorem Equation168_not_implies_Equation23 : ∃ (G : Type) (_ : Magma G), Equation168 G ∧ ¬ Equation23 G :=
  ⟨Bool × Bool, ⟨fun x y ↦ ⟨x.snd,y.fst⟩⟩, fun _ _ _ ↦ rfl, of_decide_eq_false rfl⟩

@[equational_result]
theorem Equation168_not_implies_Equation39 : ∃ (G : Type) (_ : Magma G), Equation168 G ∧ ¬ Equation39 G :=
  ⟨Bool × Bool, ⟨fun x y ↦ ⟨x.snd,y.fst⟩⟩, by decide⟩

@[equational_result]
theorem Equation387_not_implies_Equation39 : ∃ (G: Type) (_: Magma G), Equation387 G ∧ ¬ Equation39 G :=
  ⟨Bool, ⟨fun x y ↦ x && y⟩, by decide⟩

-- The "and" magma on the two element set of booleans satisfies 387, but does not satisfy 40.
@[equational_result]
theorem Equation387_not_implies_Equation40 : ∃ (G: Type) (_: Magma G), Equation387 G ∧ ¬ Equation40 G := by
  let hG : Magma Bool := { op := fun x y ↦ x && y }
  exact ⟨Bool, hG, fun _ _ ↦ by simp [hG, Bool.and_comm], of_decide_eq_false rfl⟩

@[equational_result]
theorem Equation387_not_implies_Equation42 : ∃ (G: Type) (_: Magma G), Equation387 G ∧ ¬ Equation42 G := by
  let hG : Magma Bool := { op := fun x y ↦ x || y }
  exact ⟨Bool, hG, fun _ _ ↦ by simp [hG, Bool.or_comm], of_decide_eq_false rfl⟩

@[equational_result]
theorem Equation387_not_implies_Equation4512 : ∃ (G: Type) (_: Magma G), Equation387 G ∧ ¬ Equation4512 G := by
  let hG : Magma Real := { op := fun x y ↦ (x + y) / 2 }
  refine ⟨ℝ, hG, fun _ _ ↦ ?_, ?_⟩
  . dsimp [hG]
    ring
  · by_contra h
    specialize h 0 0 1
    field_simp [hG] at h

@[equational_result]
theorem Equation4512_not_implies_Equation42 : ∃ (G: Type) (_: Magma G), Equation4512 G ∧ ¬ Equation42 G := by
  let hG : Magma ℕ := { op := fun x y ↦ x + y }
  refine ⟨ℕ, hG, fun _ _ _ ↦ ?_, ?_⟩
  . dsimp [hG]
    abel
  · by_contra h
    specialize h 0 0 1
    dsimp [hG] at h
    linarith

@[equational_result]
theorem Equation4512_not_implies_Equation4513 : ∃ (G: Type) (_: Magma G), Equation4512 G ∧ ¬ Equation4513 G := by
  let hG : Magma ℕ := { op := fun x y ↦ x + y }
  refine ⟨ℕ, hG, fun _ _ _ ↦ ?_, ?_⟩
  . dsimp [hG]
    abel
  · by_contra h
    specialize h 0 0 0 1
    dsimp [hG] at h
    linarith

@[equational_result]
theorem Equation4513_not_implies_Equation4522 : ∃ (G: Type) (_: Magma G), Equation4513 G ∧ ¬ Equation4522 G := by
  let hG : Magma ℕ := { op := fun x y ↦ if x = 0 then (if y ≤ 2 then 1 else 2) else x }
  refine ⟨ℕ, hG, fun _ _ _ _ ↦ ?_, ?_⟩
  . dsimp [hG]
    split_ifs <;> simp_all
  · by_contra h
    specialize h 0 0 0 3 3
    dsimp [hG] at h
    linarith

-- use "saturating addition" on the set {1, 2, 3}, where we add in the normal way but cap the result at 3 (x*y = min(3, x+y)).

inductive Th
  | t1 : Th
  | t2 : Th
  | t3 : Th

def add : Th → Th → Th
| Th.t1, Th.t1 => Th.t2
| Th.t1, Th.t2 => Th.t3
| Th.t1, Th.t3 => Th.t3
| Th.t2, Th.t1 => Th.t3
| Th.t2, Th.t2 => Th.t3
| Th.t2, Th.t3 => Th.t3
| Th.t3, _ => Th.t3
theorem add3 (a b c :Th) : add (add a b ) c = Th.t3:= by

  cases a;
  cases b;
  cases c; trivial; trivial; trivial;
  cases c; trivial; trivial; trivial;
  cases c; trivial; trivial; trivial;
  cases b;
  cases c; trivial; trivial; trivial;
  cases c; trivial; trivial; trivial;
  cases c; trivial; trivial; trivial;
  cases b;
  cases c; trivial; trivial; trivial;
  cases c; trivial; trivial; trivial;
  cases c; trivial; trivial; trivial

theorem add3_ (a b c :Th) : add  a (add b c ) = Th.t3:= by

  cases a;
  cases b;
  cases c; trivial; trivial; trivial;
  cases c; trivial; trivial; trivial;
  cases c; trivial; trivial; trivial;
  cases b;
  cases c; trivial; trivial; trivial;
  cases c; trivial; trivial; trivial;
  cases c; trivial; trivial; trivial;
  cases b;
  cases c; trivial; trivial; trivial;
  cases c; trivial; trivial; trivial;
  cases c; trivial; trivial; trivial

@[equational_result]
theorem Equation4582_not_implies_Equation39 : ∃ (G: Type) (_: Magma G), Equation4582 G ∧ ¬ Equation39 G := by
  let hG : Magma ℕ := { op := fun x y ↦ if x = 1 ∧ y = 2 then 3 else 4 }
  refine ⟨ℕ, hG, fun _ _ _ _ _ _ ↦ ?_, ?_⟩
  . dsimp [hG]
    split_ifs <;> simp_all
  · intro h
    specialize h 2 1
    dsimp [hG] at h
    contradiction

@[equational_result]
theorem Equation4582_not_implies_Equation40 : ∃ (G: Type) (_: Magma G), Equation4582 G ∧ ¬ Equation40 G := by
  let hG : Magma Th := { op := fun x y ↦ add x y}
  have hh : Equation4582 Th := by
    intro x y z w u v
    calc
      add x (add y z) = Th.t3 := by rw [add3_ x y z]
      _ = add (add w u) v := by rw [add3 w u v]
  refine ⟨Th, hG, hh, ?_⟩
  by_contra h
  specialize h Th.t1 Th.t2
  have h1: Th.t1 ∘ Th.t1 = Th.t2 := rfl
  have h2: Th.t2 ∘ Th.t2 = Th.t3 := rfl
  have h3: Th.t1 ∘ Th.t1 ≠ Th.t2 ∘ Th.t2 := by rw[h1, h2]; intro hhh; cases hhh
  exact absurd h h3

@[equational_result]
theorem Equation4582_not_implies_Equation42 : ∃ (G: Type) (_: Magma G), Equation4582 G ∧ ¬ Equation42 G := by
  let hG : Magma ℕ := { op := fun x y ↦ if x = 0 ∧ y = 0 then 1 else 2 }
  refine ⟨ℕ, hG, fun _ _ _ _ _ _ ↦ ?_, ?_⟩
  . dsimp [hG]
    split_ifs <;> simp_all
  · by_contra h
    specialize h 0 0 1
    dsimp [hG] at h
    linarith

@[equational_result]
theorem Equation4582_not_implies_Equation43 : ∃ (G: Type) (_: Magma G), Equation4582 G ∧ ¬ Equation43 G := by
  let hG : Magma ℕ := { op := fun x y ↦ if x = 1 ∧ y = 2 then 3 else 4 }
  refine ⟨ℕ, hG, fun _ _ _ _ _ _ ↦ ?_, ?_⟩
  . dsimp [hG]
    split_ifs <;> simp_all
  · by_contra h
    specialize h 1 2
    dsimp [hG] at h
    linarith

end Subgraph
