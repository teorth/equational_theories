import Mathlib.Order.BooleanAlgebra

section BooleanRingDef

-- We could use a bunch of things from mathlib, e.g.: Boolean rings are rings, of course, in sevral ways.
-- Any integration into mathlib should create such an instance, to enable tactic goodies.
-- we follow https://en.wikipedia.org/wiki/Boolean_algebra_(structure)
class BooleanRing (α : Type*) extends Mul α, Add α, Zero α, One α, HasCompl α where
  assoc₁ : ∀ a b c : α, a + (b + c) = (a + b) + c
  assoc₂ : ∀ a b c : α, a * (b * c) = (a * b) * c
  commut₁ : ∀ a b : α, a + b = b + a
  commut₂ : ∀ a b : α, a * b = b * a
  ident₁ : ∀ a : α, a + 0 = a
  ident₂ : ∀ a : α, a * 1 = a
  distrib₁ : ∀ a b c : α, a + (b * c) = (a + b) * (a + c)
  distrib₂ : ∀ a b c : α, a * (b + c) = (a * b) + (a * c)
  compl₁ : ∀ a : α, a + aᶜ = 1
  compl₂ : ∀ a : α, a * aᶜ = 0

open BooleanRing

lemma bound₁ {α : Type*} [BooleanRing α] (a : α) : a + 1 = 1 :=
by
  calc
    a + 1 = (a + 1) * 1        := by rw [ident₂]
    _     = 1 * (a + 1)        := by rw [commut₂]
    _     = (a + aᶜ) * (a + 1) := by rw [compl₁]
    _     = a + (aᶜ * 1)       := by rw [distrib₁]
    _     = a + aᶜ             := by rw [ident₂]
    _     = 1                  := by exact compl₁ a

lemma bound₂ {α : Type*} [BooleanRing α] (a : α) : a * 0 = 0 :=
by
  calc
    a * 0 = (a * 0) + 0        := by rw [ident₁]
    _     = 0 + (a * 0)        := by rw [commut₁]
    _     = (a * aᶜ) + (a * 0) := by rw [compl₂]
    _     = a * (aᶜ + 0)       := by rw [distrib₂]
    _     = a * aᶜ             := by rw [ident₁]
    _     = 0                  := by exact compl₂ a

lemma absorb₁ {α : Type*} [BooleanRing α] (a b : α) : a + (a * b) = a :=
by
  calc
    a + (a * b) = (a * 1) + (a * b) := by rw [ident₂]
    _           = a * (1 + b)       := by rw [distrib₂]
    _           = a * (b + 1)       := by conv => lhs; rw [commut₁]
    _           = a * 1             := by rw [bound₁]
    _           = a                 := by exact ident₂ a

-- it would be nice to have a "dualization" tactic. This might be some work though.
lemma absorb₂ {α : Type*} [BooleanRing α] (a b : α) : a * (a + b) = a :=
by
  calc
    a * (a + b) = (a + 0) * (a + b) := by rw [ident₁]
    _           = a + (0 * b)       := by rw [distrib₁]
    _           = a + (b * 0)       := by conv => lhs; rw [commut₂]
    _           = a + 0             := by rw [bound₂]
    _           = a                 := by exact ident₁ a

@[simp]
lemma idemp₂ {α : Type*} [BooleanRing α] (a : α) : a * a = a :=
by
  symm
  calc
    a = a * (a + 0) := by exact Eq.symm (absorb₂ a 0)
    _ = a * a       := by rw [ident₁]

instance BooleanRingLE {α : Type*} [BooleanRing α] : LE α :=
  ⟨ λ a b ↦ a = b * a ⟩

lemma BooleanRing.le_refl {α : Type*} [BooleanRing α] (a : α) : a ≤ a :=
by
  simp [BooleanRingLE]

lemma BooleanRing.le_trans {α : Type*} [BooleanRing α] (a b c : α) :
  a ≤ b → b ≤ c → a ≤ c :=
by
  simp [BooleanRingLE]
  intros h₁ h₂
  calc
    a = b * a       := by trivial
    _ = (c * b) * a := by conv => lhs; rw [h₂]
    _ = c * (b * a) := by exact Eq.symm (assoc₂ c b a)
    _ = c * a       := by rw [← h₁]

lemma BooleanRing.le_antisymm {α : Type*} [BooleanRing α] (a b : α) :
  a ≤ b → b ≤ a → a = b :=
by
  simp [BooleanRingLE]
  intros h₁ h₂
  calc
    a = b * a := by exact h₁
    _ = a * b := by exact commut₂ b a
    _ = b     := by exact id (Eq.symm h₂)

instance BooleanRingToBooleanAlg {α : Type*} [BooleanRing α] :
  BooleanAlgebra α where
sup := (. + .)
le_refl := by exact fun a ↦ BooleanRing.le_refl a
le_trans := by exact fun a b c a_1 a_2 ↦ BooleanRing.le_trans a b c a_1 a_2
le_antisymm := by apply BooleanRing.le_antisymm
le_sup_left := by
  intros a b
  simp [Sup.sup, BooleanRingLE]
  rw [commut₂]; exact Eq.symm (absorb₂ a b)
le_sup_right := by
  intros a b
  simp [Sup.sup, BooleanRingLE]
  rw [commut₂, commut₁]; exact Eq.symm (absorb₂ b a)
sup_le := by
  intros a b c
  simp [BooleanRingLE, Sup.sup]
  intros h₁ h₂
  calc
    a + b = (c * a) + b       := by conv => left; left; rw [h₁]
    _     = (c * a) + (c * b) := by conv => left; right; rw [h₂]
    _     = c * (a + b)       := by exact Eq.symm (distrib₂ c a b)
inf := (. * .)
inf_le_left := by
  intros a b; simp [Sup.sup, BooleanRingLE]
  rw [assoc₂]
  have h : a = a * a := by
    calc
      a = a * (a + 0) := by exact Eq.symm (absorb₂ a 0)
      _ = a * a := by rw [ident₁]
  rw [← h]
inf_le_right := by
  intros a b; simp [Sup.sup, BooleanRingLE]
  calc
    a * b = a * (b * b) := by simp
    _     = a * b * b   := by exact assoc₂ a b b
    _     = b * a * b   := by conv => left; left; rw [commut₂]
    _     = b * (a * b) := by exact Eq.symm (assoc₂ b a b)
le_inf := by
  intros a b c; simp [Sup.sup, BooleanRingLE]
  intros h₁ h₂
  calc
    a = b * a       := by exact h₁
    _ = b * (c * a) := by conv => left; right; rw [h₂]
    _ = b * c * a  := by exact assoc₂ b c a
le_sup_inf := by
  intros a b c; simp [Sup.sup, Inf.inf]
  rw [distrib₁]
  exact BooleanRing.le_refl ((a + b) * (a + c))
top := 1
bot := 0
inf_compl_le_bot := by intros a; simp; rw [compl₂]; apply BooleanRing.le_refl
top_le_sup_compl := by intros a; simp; rw [compl₁]; apply BooleanRing.le_refl
le_top := by intros a; simp [BooleanRingLE]; rw [commut₂]; exact Eq.symm (ident₂ a)
bot_le := by
  intros a; simp [BooleanRingLE]
  symm
  calc
    a * 0 = (a * 0) + 0        := by exact Eq.symm (ident₁ (a * 0))
    _     = 0 + (a * 0)        := by exact commut₁ (a * 0) 0
    _     = (a * aᶜ) + (a * 0) := by conv => left; left; exact Eq.symm (compl₂ a)
    _     = a * (aᶜ + 0)       := by exact Eq.symm (distrib₂ a aᶜ 0)
    _     = a * aᶜ             := by rw [ident₁]
    _     = 0                  := by exact compl₂ a

end BooleanRingDef
