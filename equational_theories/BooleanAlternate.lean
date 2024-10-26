import Mathlib.Order.BooleanAlgebra

section BooleanRingDef

-- We could use a bunch of things from mathlib, e.g.: Boolean rings are rings, of course, in sevral ways.
-- Any integration into mathlib should create such an instance, to enable tactic goodies.
-- we follow https://en.wikipedia.org/wiki/Boolean_algebra_(structure)
class BooleanRing (α : Type*) extends Mul α, Add α, Zero α, One α, HasCompl α where
  -- assoc₁ : ∀ a b c : α, a + (b + c) = (a + b) + c
  -- assoc₂ : ∀ a b c : α, a * (b * c) = (a * b) * c
  commut₁ : ∀ a b : α, a + b = b + a
  commut₂ : ∀ a b : α, a * b = b * a
  ident₁ : ∀ a : α, a + 0 = a
  ident₂ : ∀ a : α, a * 1 = a
  distrib₁ : ∀ a b c : α, a + (b * c) = (a + b) * (a + c)
  distrib₂ : ∀ a b c : α, a * (b + c) = (a * b) + (a * c)
  compl₁ : ∀ a : α, a + aᶜ = 1
  compl₂ : ∀ a : α, a * aᶜ = 0

open BooleanRing

variable {α : Type*}
variable [BooleanRing α]

@[simp]
lemma bound₁ (a : α) : a + 1 = 1 :=
by
  calc
    a + 1 = (a + 1) * 1        := by rw [ident₂]
    _     = 1 * (a + 1)        := by rw [commut₂]
    _     = (a + aᶜ) * (a + 1) := by rw [compl₁]
    _     = a + (aᶜ * 1)       := by rw [distrib₁]
    _     = a + aᶜ             := by rw [ident₂]
    _     = 1                  := by exact compl₁ a

@[simp]
lemma bound₂ (a : α) : a * 0 = 0 :=
by
  calc
    a * 0 = (a * 0) + 0        := by rw [ident₁]
    _     = 0 + (a * 0)        := by rw [commut₁]
    _     = (a * aᶜ) + (a * 0) := by rw [compl₂]
    _     = a * (aᶜ + 0)       := by rw [distrib₂]
    _     = a * aᶜ             := by rw [ident₁]
    _     = 0                  := by exact compl₂ a

@[simp] -- This simp is a little overeager.
lemma absorb₁ (a b : α) : a + (a * b) = a :=
by
  calc
    a + (a * b) = (a * 1) + (a * b) := by rw [ident₂]
    _           = a * (1 + b)       := by rw [distrib₂]
    _           = a * (b + 1)       := by conv => lhs; rw [commut₁]
    _           = a * 1             := by rw [bound₁]
    _           = a                 := by exact ident₂ a

-- it would be nice to have a "dualization" tactic. This might be some work though.
@[simp] -- This simp is a little overeager.
lemma absorb₂ (a b : α) : a * (a + b) = a :=
by
  calc
    a * (a + b) = (a + 0) * (a + b) := by rw [ident₁]
    _           = a + (0 * b)       := by rw [distrib₁]
    _           = a + (b * 0)       := by conv => lhs; rw [commut₂]
    _           = a + 0             := by rw [bound₂]
    _           = a                 := by exact ident₁ a

@[simp]
lemma idemp₂ (a : α) : a * a = a :=
by
  symm
  calc
    a = a * (a + 0) := by exact Eq.symm (absorb₂ a 0)
    _ = a * a       := by rw [ident₁]

lemma inv (a a' : α) : a + a' = 1 → a * a' = 0 → a' = aᶜ :=
by
  intros h₁ h₂
  calc
    a' = a' * 1               := by exact Eq.symm (ident₂ a')
    _  = a' * (a + aᶜ)        := by rw [compl₁]
    _  = (a' * a) + (a' * aᶜ) := by rw [distrib₂]
    _  = (a' * a) + (aᶜ * a') := by conv => left; right; exact commut₂ a' aᶜ
    _  = (a * a') + (aᶜ * a') := by conv => left; left; exact commut₂ a' a
    _  = 0 + (aᶜ * a')        := by rw [h₂]
    _  = (a * aᶜ) + (aᶜ * a') := by rw [compl₂]
    _  = (aᶜ * a) + (aᶜ * a') := by conv => left; left; exact commut₂ a aᶜ
    _  = aᶜ * (a + a')        := by rw [distrib₂]
    _  = aᶜ * 1               := by rw [h₁]
    _  = aᶜ                   := by exact ident₂ aᶜ

lemma dne (a : α) : aᶜᶜ = a :=
by
  symm
  apply inv
  . rw [commut₁]; exact compl₁ a
  . rw [commut₂]; exact compl₂ a

lemma inv_elim (a b : α) : aᶜ = bᶜ → a = b :=
by
  intros h
  have h' : aᶜᶜ = bᶜᶜ := by congr
  simp [dne] at h'; trivial

lemma cancel (a b : α) : a + bᶜ = 1 → a * bᶜ = 0 → a = b :=
by
  intros h₁ h₂
  have h : bᶜ = aᶜ := by apply inv <;> trivial
  apply inv_elim; symm; trivial

attribute [simp] BooleanRing.compl₁ BooleanRing.compl₂ BooleanRing.ident₁ BooleanRing.ident₂

@[simp]
lemma A₁ (a b : α) : a + (aᶜ + b) = 1 :=
by
  calc
    a + (aᶜ + b) = (a + (aᶜ + b)) * 1 := by rw [ident₂]
    _            = 1 * (a + (aᶜ + b)) := by rw [commut₂]
    _            = (a + aᶜ) * (a + (aᶜ + b)) := by simp
    _            = a + (aᶜ * (aᶜ + b)) := by rw [distrib₁]
    _            = a + aᶜ := by simp
    _            = 1 := by simp

@[simp]
lemma A₂ (a b : α) : a * (aᶜ * b) = 0 :=
by
  calc
    a * (aᶜ * b) = (a * (aᶜ * b)) + 0 := by rw [ident₁]
    _            = 0 + (a * (aᶜ * b)) := by rw [commut₁]
    _            = (a * aᶜ) + (a * (aᶜ * b)) := by simp
    _            = a * (aᶜ + (aᶜ * b)) := by rw [distrib₂]
    _            = a * aᶜ := by simp
    _            = 0 := by simp


@[simp]
lemma dm₁ (a b : α) : (a + b)ᶜ = aᶜ * bᶜ :=
by
  symm
  apply cancel <;> simp [dne]
  . rw [commut₁, distrib₁]
    conv => left; left; rw [commut₁]; right; left; exact Eq.symm (dne a)
    rw [A₁, commut₂, ident₂]
    rw [commut₁]; conv => left; right; rw [commut₁]; left; exact Eq.symm (dne b)
    simp
  . rw [distrib₂]
    conv => left; left; rw [commut₂]
    rw [A₂, commut₁, ident₁]
    rw [commut₂]; conv => left; right; rw [commut₂]
    simp

@[simp]
lemma dm₂ (a b : α) : (a * b)ᶜ = aᶜ + bᶜ :=
by
  symm
  apply cancel <;> simp [dne]
  . rw [commut₂, distrib₁]
    conv => left; left; rw [commut₁]; right; rw [commut₁]
    rw [A₁, commut₂, ident₂]
    rw [commut₁]
    rw [A₁]
  . rw [commut₂, distrib₂]
    conv => left; left; rw [commut₂]; right; left; exact Eq.symm (dne a)
    rw [A₂, commut₁, ident₁]
    rw [commut₂]; conv => left; right; rw [commut₂]; left; exact Eq.symm (dne b)
    rw [A₂]

lemma D₁ (a b c : α) : (a + (b + c)) + aᶜ = 1 :=
by
  rw [commut₁]
  conv => left; right; left; exact Eq.symm (dne a)
  simp

lemma E₁ (a b c : α) : b * (a + (b + c)) = b :=
by
  rw [distrib₂]
  simp; rw [commut₁]; simp

lemma E₂ (a b c : α) : b + (a * (b * c)) = b :=
by
  rw [distrib₁]
  simp; rw [commut₂]; simp

lemma F₁ (a b c : α) : (a + (b + c)) + bᶜ = 1 :=
by
  calc
    (a + (b + c)) + bᶜ = bᶜ + (a + (b + c)) := by rw [commut₁]
    _                  = 1 * (bᶜ + (a + (b + c))) := by rw [commut₂]; simp
    _                  = (b + bᶜ) * (bᶜ + (a + (b + c))) := by simp
    _                  = (bᶜ + b) * (bᶜ + (a + (b + c))) := by rw [commut₁]
    _                  = bᶜ + (b * (a + (b + c))) := by rw [distrib₁]
    _                  = bᶜ + b := by rw [E₁]
    _                  = 1 := by rw [commut₁]; simp

lemma G₁ (a b c : α) : (a + (b + c)) + cᶜ = 1 :=
by
  conv => left; left; right; rw [commut₁]
  apply F₁

lemma H₁ (a b c : α) : (a + b + c)ᶜ * a = 0 :=
by
  simp; rw [commut₂]
  calc
    a * (aᶜ * bᶜ * cᶜ) = (a * (aᶜ * bᶜ * cᶜ)) + 0 := by simp
    _                  = 0 + (a * (aᶜ * bᶜ * cᶜ)) := by rw [commut₁]
    _                  = (a * aᶜ) + (a * (aᶜ * bᶜ * cᶜ)) := by simp
    _                  = a * (aᶜ + (aᶜ * bᶜ * cᶜ)) := by rw [distrib₂]
    _                  = a * (aᶜ + (cᶜ * (aᶜ * bᶜ))) := by conv => left; right; right; rw [commut₂]
    _                  = a * aᶜ := by rw [E₂]
    _                  = 0 := by simp

lemma I₁ (a b c : α) : (a + b + c)ᶜ * b = 0 :=
by
  conv => left; left; arg 1; left; rw [commut₁]
  apply H₁

lemma J₁ (a b c : α) : (a + b + c)ᶜ * c = 0 :=
by
  simp
  rw [commut₂]
  conv => left; right; rw [commut₂]
  simp

-- Incredibly, these are derivable
@[simp]
lemma assoc₁ (a b c : α) : a + (b + c) = (a + b) + c :=
by
  apply cancel; simp
  . calc
      (a + (b + c)) + (aᶜ * bᶜ * cᶜ) = ((a + (b + c)) + (aᶜ * bᶜ)) * ((a + (b + c)) + cᶜ) := by rw [distrib₁]
      _ = ((a + (b + c) + aᶜ) * ((a + (b + c) + bᶜ))) * ((a + (b + c)) + cᶜ) := by rw [distrib₁]
      _ = (1 * 1) * 1 := by rw [D₁, F₁, G₁]
      _ = 1 := by simp
  . rw [commut₂]
    rw [distrib₂]; rw [distrib₂]
    calc
      (a + b + c)ᶜ * a + ((a + b + c)ᶜ * b + (a + b + c)ᶜ * c) = 0 + (0 + 0) := by rw [H₁, I₁, J₁]
      _ = 0 := by repeat rw [ident₁]

-- We don't try to dualize the proof here, that's too painful, we apply de Morgan liberally
@[simp]
lemma assoc₂ (a b c : α) : a * (b * c) = (a * b) * c :=
by
  apply inv_elim; simp

instance BooleanRingLE : LE α :=
  ⟨ λ a b ↦ a = b * a ⟩

lemma BooleanRing.le_refl (a : α) : a ≤ a :=
by
  simp [BooleanRingLE]

lemma BooleanRing.le_trans (a b c : α) :
  a ≤ b → b ≤ c → a ≤ c :=
by
  simp [BooleanRingLE]
  intros h₁ h₂
  calc
    a = b * a       := by trivial
    _ = (c * b) * a := by conv => lhs; rw [h₂]
    _ = c * (b * a) := by exact Eq.symm (assoc₂ c b a)
    _ = c * a       := by rw [← h₁]

lemma BooleanRing.le_antisymm (a b : α) :
  a ≤ b → b ≤ a → a = b :=
by
  simp [BooleanRingLE]
  intros h₁ h₂
  calc
    a = b * a := by exact h₁
    _ = a * b := by exact commut₂ b a
    _ = b     := by exact id (Eq.symm h₂)

instance BooleanRingToBooleanAlg :
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
inf_le_right := by
  intros a b; simp only [Sup.sup, BooleanRingLE]
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
inf_compl_le_bot := by intros a; simp; apply BooleanRing.le_refl
top_le_sup_compl := by intros a; simp; apply BooleanRing.le_refl
le_top := by intros a; simp [BooleanRingLE]; rw [commut₂]; exact Eq.symm (ident₂ a)
bot_le := by
  intros a; simp [BooleanRingLE]

end BooleanRingDef
