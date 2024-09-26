import Mathlib.Data.Nat.Defs
import Mathlib.Tactic


universe u

class Magma (α : Type u) where
  /-- `a ∘ b` computes a binary operation of `a` and `b`. -/
  op : α → α → α

@[inherit_doc] infixl:65 " ∘ "   => Magma.op


/- List of equational laws being studied -/

/-- The reflexive law -/
def Equation1 (G: Type*) [Magma G] := ∀ x : G, x = x

/-- The singleton law -/
def Equation2 (G: Type*) [Magma G] := ∀ x y : G, x = y

/-- The idempotence law -/
def Equation3 (G: Type*) [Magma G] := ∀ x : G, x = x ∘ x

/-- The left absorption law -/
def Equation4 (G: Type*) [Magma G] := ∀ x y : G, x = x ∘ y

/-- The right absorption law -/
def Equation5 (G: Type*) [Magma G] := ∀ x y : G, x = y ∘ x

def Equation6 (G: Type*) [Magma G] := ∀ x y : G, x = y ∘ y

def Equation7 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ z

def Equation8 (G: Type*) [Magma G] := ∀ x : G, x = x ∘ (x ∘ x)

def Equation38 (G: Type*) [Magma G] := ∀ x y : G, x ∘ x = x ∘ y

def Equation39 (G: Type*) [Magma G] := ∀ x y : G, x ∘ x = y ∘ x

def Equation40 (G: Type*) [Magma G] := ∀ x y : G, x ∘ x = y ∘ y

def Equation41 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ x = y ∘ z

def Equation42 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = x ∘ z

def Equation43 (G: Type*) [Magma G] := ∀ x y : G, x ∘ y = y ∘ x

/-- The constant law -/
def Equation46 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ w

/-- The central groupoid law -/
def Equation168 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ x) ∘ (x ∘ z)

def Equation387 (G: Type*) [Magma G] := ∀ x y : G, x ∘ y = (y ∘ y) ∘ x

/-- The associative law -/
def Equation4512 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ (y ∘ z) = (x ∘ y) ∘ z

def Equation4513 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ z) = (x ∘ y) ∘ w

def Equation4552 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ (y ∘ z) = (x ∘ w) ∘ u

def Equation4582 (G: Type*) [Magma G] := ∀ x y z w u v: G, x ∘ (y ∘ z) = (w ∘ u) ∘ v


/- Positive implications -/

theorem Equation1_true (G: Type*) [Magma G] : Equation1 G :=
  fun _ => rfl

theorem Equation2_implies_Equation4 (G: Type*) [Magma G] (h: Equation2 G) : Equation4 G :=
  fun _ _ => h _ _

theorem Equation2_implies_Equation6 (G: Type*) [Magma G] (h: Equation2 G) : Equation6 G :=
  fun _ _ => h _ _

theorem Equation2_implies_Equation7 (G: Type*) [Magma G] (h: Equation2 G) : Equation7 G :=
  fun _ _ _ => h _ _

theorem Equation2_implies_Equation46 (G: Type*) [Magma G] (h: Equation2 G) : Equation46 G :=
  fun _ _ _ _ => h _ _

theorem Equation6_implies_Equation2 (G: Type*) [Magma G] (h: Equation6 G) : Equation2 G := by
  intro a b
  rw [h a a, ← h b]

theorem Equation7_implies_Equation2 (G: Type*) [Magma G] (h: Equation7 G) : Equation2 G := by
  intro a b
  rw [h a a a, ←h b]

theorem Equation4_implies_Equation3 (G: Type*) [Magma G] (h: Equation4 G) : Equation3 G := by
  intro _
  rw [<-h]

theorem Equation4_implies_Equation42 (G: Type*) [Magma G] (h: Equation4 G) : Equation42 G := by
  intro _ _ _
  rw [<-h, <-h]

theorem Equation4_implies_Equation4552 (G: Type*) [Magma G] (h: Equation4 G) : Equation4552 G := by
  intro x y z w u
  rw [<-h, <-h, <-h]

theorem Equation46_implies_Equation42 (G: Type*) [Magma G] (h: Equation46 G) : Equation42 G :=
  fun _ _ _ => h _ _ _ _

theorem Equation46_implies_Equation387 (G: Type*) [Magma G] (h: Equation46 G) : Equation387 G :=
  fun _ _ => h _ _ _ _

theorem Equation46_implies_Equation4582 (G: Type*) [Magma G] (h: Equation46 G) : Equation4582 G :=
  fun _ _ _ _ _ _ => h _ _ _ _

/-- This proof is from https://mathoverflow.net/a/450905/766 -/
theorem Equation387_implies_Equation43 (G: Type*) [Magma G] (h: Equation387 G) : Equation43 G := by
  have idem (x : G) : (x ∘ x) ∘ (x ∘ x) = (x ∘ x) := by
    rw [<-h, <-h]
  have comm (x y : G) : (x ∘ x) ∘ y = y ∘ (x ∘ x) := by
    rw [<-idem, <-h, idem]
  have op_idem (x y : G) : (x ∘ x) ∘ (y ∘ y) = x ∘ y := by
    rw [<-h, <-h]
  intro x y
  rw [<- op_idem, comm, op_idem]

theorem Equation4513_implies_Equation4512 (G: Type*) [Magma G] (h: Equation4513 G) : Equation4512 G :=
  fun _ _ _ => h _ _ _ _

theorem Equation4552_implies_Equation4513 (G: Type*) [Magma G] (h: Equation4552 G) : Equation4513 G :=
  fun _ _ _ _ => h _ _ _ _ _

theorem Equation4582_implies_Equation4552 (G: Type*) [Magma G] (h: Equation4582 G) : Equation4552 G :=
  fun _ _ _ _ _ => h _ _ _ _ _ _




/- Counterexamples -/

theorem Equation3_not_implies_Equation42 : ∃ (G: Type) (_: Magma G), Equation3 G ∧ ¬ Equation42 G := by
  let hG : Magma Nat := {
    op := fun _ y => y
  }
  use ℕ, hG
  constructor
  . intro _
    rfl
  by_contra h
  specialize h 0 1 2
  simp [hG] at h

theorem Equation3_not_implies_Equation4512 : ∃ (G: Type) (_: Magma G), Equation3 G ∧ ¬ Equation4512 G := by
  let hG : Magma Nat := {
    op := fun x y => if x = y then x else x + 1
  }
  use ℕ, hG
  constructor
  . intro x
    simp [hG]
  by_contra h
  specialize h 1 2 3
  simp [hG] at h

theorem Equation4_not_implies_Equation43 : ∃ (G: Type) (_: Magma G), Equation4 G ∧ ¬ Equation43 G := by
  let hG : Magma Nat := {
    op := fun x _ => x
  }
  use ℕ, hG
  constructor
  . intro _ _
    rfl
  by_contra h
  specialize h 1 0
  dsimp [hG] at h
  linarith

theorem Equation4_not_implies_Equation4582 : ∃ (G: Type) (_: Magma G), Equation4 G ∧ ¬ Equation4582 G := by
  let hG : Magma Nat := {
    op := fun x _ => x
  }
  use ℕ, hG
  constructor
  . intro _ _
    rfl
  by_contra h
  specialize h 0 0 0 1 0 0
  dsimp [hG] at h
  linarith

theorem Equation42_not_implies_Equation43 : ∃ (G: Type) (_: Magma G), Equation42 G ∧ ¬ Equation43 G := by
  let hG : Magma Nat := {
    op := fun x _ => x
  }
  use ℕ, hG
  constructor
  . intro _ _ _
    simp [hG]
  by_contra h
  specialize h 0 1
  dsimp [hG] at h
  linarith

theorem Equation42_not_implies_Equation4512 : ∃ (G: Type) (_: Magma G), Equation42 G ∧ ¬ Equation4512 G := by
  let hG : Magma Nat := {
    op := fun x _ => x + 1
  }
  use ℕ, hG
  constructor
  . intro _ _ _
    simp [hG]
  by_contra h
  specialize h 0 0 0
  dsimp [hG] at h
  linarith

theorem Equation43_not_implies_Equation3 : ∃ (G: Type) (_: Magma G), Equation43 G ∧ ¬ Equation3 G := by
  let hG : Magma Nat := {
    op := fun x y => x+y
  }
  use ℕ, hG
  constructor
  . exact Nat.add_comm
  by_contra h
  specialize h 1
  simp [hG] at h

theorem Equation43_not_implies_Equation42 : ∃ (G: Type) (_: Magma G), Equation43 G ∧ ¬ Equation42 G := by
  let hG : Magma Nat := {
    op := fun x y => x+y
  }
  use ℕ, hG
  constructor
  . exact Nat.add_comm
  by_contra h
  specialize h 0 0 1
  dsimp [hG] at h
  linarith

theorem Equation43_not_implies_Equation387 : ∃ (G: Type) (_: Magma G), Equation43 G ∧ ¬ Equation387 G := by
  let hG : Magma Nat := {
    op := fun x y => x+y
  }
  use ℕ, hG
  constructor
  . exact Nat.add_comm
  by_contra h
  specialize h 0 1
  dsimp [hG] at h
  linarith

theorem Equation43_not_implies_Equation4512 : ∃ (G: Type) (_: Magma G), Equation43 G ∧ ¬ Equation4512 G := by
  let hG : Magma Nat := {
    op := fun x y => x * y + 1
  }
  use ℕ, hG
  constructor
  . intro x y
    dsimp [hG]
    ring
  by_contra h
  specialize h 0 0 1
  dsimp [hG] at h
  linarith

theorem Equation46_not_implies_Equation3 : ∃ (G: Type) (_: Magma G), Equation46 G ∧ ¬ Equation3 G := by
  let hG : Magma Nat := {
    op := fun _ _ => 0
  }
  use ℕ, hG
  constructor
  . intro _ _ _ _
    rfl
  by_contra h
  specialize h 1
  dsimp [hG] at h
  linarith

theorem Equation46_not_implies_Equation4 : ∃ (G: Type) (_: Magma G), Equation46 G ∧ ¬ Equation4 G := by
  let hG : Magma Nat := {
    op := fun _ _ => 0
  }
  use ℕ, hG
  constructor
  . intro _ _ _ _
    rfl
  by_contra h
  specialize h 1 0
  dsimp [hG] at h
  linarith

theorem Equation387_not_implies_Equation42 : ∃ (G: Type) (_: Magma G), Equation387 G ∧ ¬ Equation42 G := by
  let hG : Magma Bool := {
    op := fun x y => x || y
  }
  use Bool, hG
  constructor
  . intro x y
    simp [hG, Bool.or_comm]
  by_contra h
  specialize h false true false
  simp [hG] at h

theorem Equation387_not_implies_Equation4512 : ∃ (G: Type) (_: Magma G), Equation387 G ∧ ¬ Equation4512 G := by
  let hG : Magma Real := {
    op := fun x y => (x + y) / 2
  }
  use ℝ, hG
  constructor
  . intro x y
    simp [hG]
    ring
  by_contra h
  specialize h 0 0 1
  field_simp [hG] at h

theorem Equation4512_not_implies_Equation42 : ∃ (G: Type) (_: Magma G), Equation4512 G ∧ ¬ Equation42 G := by
  let hG : Magma Nat := {
    op := fun x y => x + y
  }
  use ℕ, hG
  constructor
  . intro x y z
    simp [hG]
    abel
  by_contra h
  specialize h 0 0 1
  dsimp [hG] at h
  linarith

theorem Equation4512_not_implies_Equation4513 : ∃ (G: Type) (_: Magma G), Equation4512 G ∧ ¬ Equation4513 G := by
  let hG : Magma Nat := {
    op := fun x y => x + y
  }
  use ℕ, hG
  constructor
  . intro x y z
    simp [hG]
    abel
  by_contra h
  specialize h 0 0 0 1
  dsimp [hG] at h
  linarith

theorem Equation4513_not_implies_Equation4552 : ∃ (G: Type) (_: Magma G), Equation4513 G ∧ ¬ Equation4552 G := by
  let hG : Magma Nat := {
    op := fun x y => if x = 0 then (if y ≤ 2 then 1 else 2) else x
  }
  use ℕ, hG
  constructor
  . intro x y z w
    simp [hG]
    split_ifs <;> simp_all
  by_contra h
  specialize h 0 0 0 3 3
  dsimp [hG] at h
  linarith

theorem Equation4582_not_implies_Equation42 : ∃ (G: Type) (_: Magma G), Equation4582 G ∧ ¬ Equation42 G := by
  let hG : Magma Nat := {
    op := fun x y => if x = 0 ∧ y = 0 then 1 else 2
  }
  use ℕ, hG
  constructor
  . intro x y z w u v
    simp [hG]
    split_ifs <;> simp_all
  by_contra h
  specialize h 0 0 1
  dsimp [hG] at h
  linarith

theorem Equation4582_not_implies_Equation43 : ∃ (G: Type) (_: Magma G), Equation4582 G ∧ ¬ Equation43 G := by
  let hG : Magma Nat := {
    op := fun x y => if x = 1 ∧ y = 2 then 3 else 4
  }
  use ℕ, hG
  constructor
  . intro x y z w u v
    simp [hG]
    split_ifs <;> simp_all
  by_contra h
  specialize h 1 2
  dsimp [hG] at h
  linarith
