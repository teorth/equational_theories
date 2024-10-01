-- Statement and proof of the completeness theorem for magmas,
-- we roughly follow Baader & Nipkow's "Term Rewriting and All That",
-- and
import equational_theories.FreeMagma
import Mathlib.Data.Set.Defs

open FreeMagma

structure MagmaLaw (α : Type) where
  lhs : FreeMagma α
  rhs : FreeMagma α
deriving DecidableEq

local infix:60 " ≃ " => MagmaLaw.mk

def substFreeMagma {α β} (t : FreeMagma α) (σ : α → FreeMagma β) : FreeMagma β :=
match t with
| .Leaf a => σ a
| t₁ ⋆ t₂ => substFreeMagma t₁ σ ⋆ substFreeMagma t₂ σ

infix:66 " ⬝ " => substFreeMagma

@[inline, simp]
def Ctx α := Set (MagmaLaw α)

-- FIXME: figure out how to remove this.
instance Ctx.Membership α : Membership (MagmaLaw α) (Ctx α) := ⟨ Set.instMembership.mem ⟩

section DeriveDef

set_option hygiene false

local infix:50 " ⊢ " =>  derive

-- We keep this in type, because we're going to want to gather
-- the (finite!) set of required axioms later.
inductive derive {α} : Ctx α → MagmaLaw α → Type :=
  | Ax Γ E (h : E ∈ Γ) : Γ ⊢ E
  | Ref Γ t : Γ ⊢ (t ≃ t)
  | Sym Γ t u : Γ ⊢ (t ≃ u) → Γ ⊢ (u ≃ t)
  | Trans Γ t u v : Γ ⊢ (t ≃ u) → Γ ⊢ (u ≃ v) → Γ ⊢ (t ≃ v)
  -- This is not as polymorphic as it could be, shouldn't be an issue at the moment
  | Subst Γ t u σ : Γ ⊢ (t ≃ u) → Γ ⊢ (t ⬝ σ ≃ u ⬝ σ)
  | Cong Γ t₁ t₂ u₁ u₂ : Γ ⊢ (t₁ ≃ t₂) → Γ ⊢ (u₁ ≃ u₂) → Γ ⊢ (t₁ ⋆ u₁ ≃ t₂ ⋆ u₂)

end DeriveDef

def satisfiesPhi {α G : Type} [Magma G] (φ : α → G) (E : MagmaLaw α) : Prop :=
  E.lhs.evalInMagma φ = E.rhs.evalInMagma φ

def satisfies {α : Type} (G : Type) [Magma G] (E : MagmaLaw α) := ∀ (φ : α → G), satisfiesPhi φ E

def satisfiesSet {α : Type} (G : Type) [Magma G] (Γ : Set (MagmaLaw α)) : Prop :=
  ∀ E ∈ Γ, satisfies G E

def models {α} (Γ : Ctx α) (E : MagmaLaw α) : Prop :=
  ∀ (G : Type)[Magma G], satisfiesSet G Γ → satisfies G E

infix:50 " ⊧ " => (satisfies)

infix:50 " ⊧ " => (satisfiesSet)

infix:50 " ⊧ " => (models)

infix:50 " ⊢ " => (derive)

theorem SubstEval {α} G [Magma G] (t : FreeMagma α) (σ : α → FreeMagma α) (φ : α → G) :
    evalInMagma φ (t ⬝ σ) = evalInMagma (evalInMagma φ ∘ σ) t := by
  cases t
  case Leaf => rfl
  case Fork t₁ t₂ => simp only [evalInMagma]; repeat rw [SubstEval]

theorem Soundness {α} (Γ : Ctx α) E (h : Γ ⊢ E) : Γ ⊧ E := by
  intros G _
  cases h
  case Ax mem => exact fun a ↦ a E mem
  case Ref => exact fun _ ↦ congrFun rfl
  -- FIXME: try aesop here, might be a 1-liner
  case Sym t u prf =>
    intros φ mset
    simp only [satisfiesPhi] at *
    symm; apply Soundness _ _ prf; trivial
  case Trans _ _ _ prf₁ prf₂ =>
    intros φ mset
    simp [models, satisfiesPhi] at *
    rw [Soundness _ _ prf₁, Soundness _ _ prf₂] <;> trivial
  case Subst t u σ prf =>
    intros φ mset
    simp [models, satisfiesPhi, evalInMagma] at *
    repeat rw [SubstEval]
    rw [Soundness _ _ prf]; trivial
  case Cong _ _ _ prf₁ prf₂ =>
    intros _ _
    simp [models, satisfiesPhi, evalInMagma] at *
    rw [Soundness _ _ prf₁, Soundness _ _ prf₂] <;> trivial

-- A little trickery here: since we'd rather have the derivations in Type
-- (we want to extract the "used" axioms, e.g.) we smush the derivation
-- down to prop using Nonempty for creating a setoid.
def RelOfLaws {α} (Γ : Ctx α) : FreeMagma α → FreeMagma α → Prop :=
  λ t u ↦ Nonempty (Γ ⊢ t ≃ u)

-- eazy peezy since we basically have exactly the axioms.
theorem RelOfLaws.isEquivalence {α} (Γ : Ctx α) : Equivalence (RelOfLaws Γ) := by
  constructor <;> simp [RelOfLaws]
  case refl => intros x; constructor; apply derive.Ref
  case symm => intros x y h; cases h; constructor; apply derive.Sym; trivial
  case trans => intros x y z h₁ h₂; cases h₁; cases h₂; constructor; apply derive.Trans <;> trivial

instance SetoidOfLaws {α} (Γ : Ctx α): Setoid (FreeMagma α) :=
  ⟨ RelOfLaws Γ, RelOfLaws.isEquivalence Γ ⟩

-- This is the quotient type we care about: it will be a model of Γ.
def FreeMagmaWithLaws {α} (Γ : Ctx α) : Type := Quotient (SetoidOfLaws Γ)

@[simp]
def embed {α} (Γ : Ctx α) (x : FreeMagma α) : FreeMagmaWithLaws Γ := Quotient.mk _ x

def ForkWithLaws {α} (Γ : Ctx α) : FreeMagmaWithLaws Γ → FreeMagmaWithLaws Γ → FreeMagmaWithLaws Γ :=
  Quotient.lift₂ (λ x y ↦ embed Γ (x ⋆ y))
  (
    by
      simp [HasEquiv.Equiv, Setoid.r, RelOfLaws]
      intros x z y w d₁ d₂; cases d₁; cases d₂
      apply Quotient.sound; simp [HasEquiv.Equiv, Setoid.r, RelOfLaws]; constructor
      apply derive.Cong <;> trivial
  )

instance FreeMagmaWithLaws.Magma {α} (Γ : Ctx α) : Magma (FreeMagmaWithLaws Γ) :=
  { op := ForkWithLaws Γ }

theorem FreeMagmaWithLaws.evalInMagmaIsQuot {α} (Γ : Ctx α) (t : FreeMagma α) (σ : α → FreeMagma α):
    evalInMagma (embed Γ ∘ σ) t = embed Γ (t ⬝ σ) := by
  cases t <;> rw [evalInMagma]
  case Leaf => rfl
  case Fork =>
    simp only [Magma.op, ForkWithLaws]
    repeat rw [FreeMagmaWithLaws.evalInMagmaIsQuot]
    simp only [Quotient.lift₂]
    apply Quot.sound; rw [substFreeMagma]
    exact ⟨derive.Ref _ _⟩

theorem substLFId {α} (t : FreeMagma α) : t ⬝ Lf = t := by
  cases t <;> simp [substFreeMagma]
  constructor <;> apply substLFId

@[simp]
def LfEmbed {α} (Γ : Ctx α) : α → FreeMagmaWithLaws Γ := embed Γ ∘ Lf

-- Mostly forward reasoning here, so we delay the intros.
theorem FreeMagmaWithLaws.isDerives {α} (Γ : Ctx α) (E : MagmaLaw α) :
  FreeMagmaWithLaws Γ ⊧ E → Nonempty (Γ ⊢ E) := by
  simp [satisfies, satisfiesPhi, evalInMagma]
  intros eq; have h := (eq (LfEmbed Γ))
  simp only [LfEmbed] at h
  repeat rw [FreeMagmaWithLaws.evalInMagmaIsQuot] at h
  have h' := Quotient.exact h
  simp [HasEquiv.Equiv, Setoid.r, RelOfLaws] at h'
  repeat rw [substLFId] at h'
  exact h'

-- Sadly, we falter here and use choice. Somewhat confident it's not needed.
theorem PhiAsSubst_aux {α} (Γ : Ctx α) (φ : α → FreeMagmaWithLaws Γ) :
  ∃ (σ : α → FreeMagma α), ∀ x, φ x = (embed Γ) (σ x) := by
  apply Classical.axiomOfChoice (r := λ x y ↦ φ x = (embed Γ) y)
  intros x
  have ⟨a, h⟩ := (Quotient.exists_rep (φ x))
  exists a
  symm; trivial

theorem PhiAsSubst {α} (Γ : Ctx α) (φ : α → FreeMagmaWithLaws Γ) :
  ∃ (σ : α → FreeMagma α), φ = (embed Γ) ∘ σ := by
  have ⟨σ, h⟩ := PhiAsSubst_aux Γ φ
  exact ⟨σ, funext fun x ↦ h x⟩

theorem FreeMagmaWithLaws.isModel {α} (Γ : Ctx α) : FreeMagmaWithLaws Γ ⊧ Γ := by
  simp [satisfiesSet]
  intros E mem φ
  simp [satisfiesPhi]
  have ⟨σ, eq_sig⟩ := (PhiAsSubst _ φ)
  rw [eq_sig]
  repeat rw [FreeMagmaWithLaws.evalInMagmaIsQuot]
  apply Quotient.sound; simp [HasEquiv.Equiv, Setoid.r, RelOfLaws]
  exact ⟨derive.Subst _ _ _ _ (derive.Ax _ _ mem)⟩

-- Birkhoff's completeness theorem
theorem Completeness {α} (Γ : Ctx α) (E : MagmaLaw α) (h : Γ ⊧ E) : Nonempty (Γ ⊢ E) :=
  FreeMagmaWithLaws.isDerives _ _ (h _ (FreeMagmaWithLaws.isModel _))
