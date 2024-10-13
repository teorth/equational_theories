-- Statement and proof of the completeness theorem for magmas,
-- we roughly follow Baader & Nipkow's "Term Rewriting and All That",
-- and
import equational_theories.FreeMagma
import equational_theories.MagmaLaw
import Mathlib.Data.Set.Defs

open FreeMagma
open Law

theorem Soundness'_u {α β G : Type*} [Magma G] {Γ : Ctx α} {E : MagmaLaw β} (h : Γ ⊢' E) :
    G ⊧ Γ → G ⊧ E := by
  induction h with
  | @SubstAx E mem σ =>
    intro H φ
    simp [satisfiesPhi, SubstEval]
    exact H E mem _
  | Ref => exact fun _ ↦ congrFun rfl
  -- FIXME: try aesop here, might be a 1-liner
  | @Sym t u _ ih =>
    intro φ mset
    simp only [satisfiesPhi] at *
    symm; apply ih; trivial
  | Trans _ _ ih₁ ih₂ =>
    intro φ mset
    simp [models, satisfiesPhi] at *
    rw [ih₁, ih₂] <;> trivial
  | Cong _ _ ih₁ ih₂ =>
    intro _ _
    simp [models, satisfiesPhi, evalInMagma] at *
    rw [ih₁, ih₂] <;> trivial

theorem Soundness' {α β : Type*} {Γ : Ctx α} {E : MagmaLaw β} (h : Γ ⊢' E) : Γ ⊧ E :=
  fun _ => Soundness'_u h

theorem Soundness {α : Type*} {Γ : Ctx α} {E} (h : Γ ⊢ E) : Γ ⊧ E :=
  Soundness' (derive'_of_derive h)

-- A little trickery here: since we'd rather have the derivations in Type
-- (we want to extract the "used" axioms, e.g.) we smush the derivation
-- down to prop using Nonempty for creating a setoid.
def RelOfLaws {α} (β) (Γ : Ctx α) : FreeMagma β → FreeMagma β → Prop :=
  λ t u ↦ Nonempty (Γ ⊢' t ≃ u)

-- eazy peezy since we basically have exactly the axioms.
theorem RelOfLaws.isEquivalence {α} (β) (Γ : Ctx α) : Equivalence (RelOfLaws β Γ) := by
  constructor <;> simp [RelOfLaws]
  case refl => intro x; constructor; apply derive'.Ref
  case symm =>
    intro x y h
    exact ⟨derive'.Sym h⟩
  case trans =>
    intro x y z h₁ h₂
    constructor
    apply derive'.Trans
      <;> trivial

instance SetoidOfLaws {α} (β) (Γ : Ctx α) : Setoid (FreeMagma β) :=
  ⟨ RelOfLaws β Γ, RelOfLaws.isEquivalence β Γ ⟩

-- This is the quotient type we care about: it will be a model of Γ.
def FreeMagmaWithLaws.{u} {α} (β : Type u) (Γ : Ctx α) : Type u := Quotient (SetoidOfLaws β Γ)

@[simp]
def embed {α β} (Γ : Ctx α) (x : FreeMagma β) : FreeMagmaWithLaws β Γ := Quotient.mk _ x

def ForkWithLaws {α β} {Γ : Ctx α} :
    FreeMagmaWithLaws β Γ → FreeMagmaWithLaws β Γ → FreeMagmaWithLaws β Γ :=
  Quotient.lift₂ (λ x y ↦ embed Γ (x ⋆ y)) <| by
    simp only [HasEquiv.Equiv, Setoid.r, RelOfLaws, embed, Nonempty.forall]
    intro x z y w d₁ d₂
    apply Quotient.sound
    simp only [HasEquiv.Equiv, Setoid.r, RelOfLaws]
    exact ⟨derive'.Cong d₁ d₂⟩

protected instance FreeMagmaWithLaws.Magma {α} (β) (Γ : Ctx α) : Magma (FreeMagmaWithLaws β Γ) :=
  { op := ForkWithLaws }

theorem FreeMagmaWithLaws.evalInMagmaIsQuot {α β γ} (Γ : Ctx α)
    (t : FreeMagma β) (σ : β → FreeMagma γ) :
    t ⬝ (embed Γ ∘ σ) = embed Γ (t ⬝ σ) := by
  cases t <;> rw [evalInMagma]
  case Leaf => rfl
  case Fork =>
    simp only [Magma.op, ForkWithLaws]
    repeat rw [FreeMagmaWithLaws.evalInMagmaIsQuot]
    rw [Quotient.lift₂]
    apply Quot.sound; rw [evalInMagma]
    exact ⟨derive'.Ref⟩

@[simp]
def LfEmbed {α β} (Γ : Ctx α) : β → FreeMagmaWithLaws β Γ := embed Γ ∘ Lf

-- Mostly forward reasoning here, so we delay the intros.
theorem FreeMagmaWithLaws.isDerives {α β} {Γ : Ctx α} {E : MagmaLaw β} :
    FreeMagmaWithLaws β Γ ⊧ E → Nonempty (Γ ⊢' E) := by
  simp [satisfies, satisfiesPhi, evalInMagma]
  intro eq; have h := eq (LfEmbed Γ)
  simp only [LfEmbed] at h
  repeat rw [FreeMagmaWithLaws.evalInMagmaIsQuot] at h
  have h' := Quotient.exact h
  simp [HasEquiv.Equiv, Setoid.r, RelOfLaws] at h'
  repeat rw [evalInMagma_leaf] at h'
  exact h'

-- Sadly, we falter here and use choice. Somewhat confident it's not needed.
theorem PhiAsSubst_aux {α β γ} (Γ : Ctx α) (φ : β → FreeMagmaWithLaws γ Γ) :
    ∃ (σ : β → FreeMagma γ), ∀ x, φ x = embed Γ (σ x) := by
  refine Classical.axiomOfChoice (r := λ x y ↦ φ x = (embed Γ) y) fun x ↦ ?_
  have ⟨a, h⟩ := (Quotient.exists_rep (φ x))
  exact ⟨a, h.symm⟩

theorem PhiAsSubst {α β γ} (Γ : Ctx α) (φ : β → FreeMagmaWithLaws γ Γ) :
  ∃ (σ : β → FreeMagma γ), φ = (embed Γ) ∘ σ := by
  have ⟨σ, h⟩ := PhiAsSubst_aux Γ φ
  exact ⟨σ, funext fun _ ↦ h _⟩

theorem FreeMagmaWithLaws.isModel {α} (β) (Γ : Ctx α) : FreeMagmaWithLaws β Γ ⊧ Γ := by
  intro E mem φ
  simp only [satisfiesPhi]
  have ⟨σ, eq_sig⟩ := (PhiAsSubst _ φ)
  rw [eq_sig]
  repeat rw [FreeMagmaWithLaws.evalInMagmaIsQuot]
  exact Quotient.sound ⟨derive'.SubstAx mem _⟩

theorem FreeMagmaWithLaws.models_iff_u.{u} {α} {β : Type u} {Γ : Ctx α} {E : MagmaLaw β} :
    (∀ (G : Type u) [Magma G], G ⊧ Γ → G ⊧ E) ↔ FreeMagmaWithLaws β Γ ⊧ E := by
  refine ⟨fun H => H _ (FreeMagmaWithLaws.isModel _ _), fun H => ?_⟩
  have ⟨h'⟩ := FreeMagmaWithLaws.isDerives H
  exact fun G => Soundness'_u h'

instance {G} [Magma G] : Magma (ULift G) where
  op x y := .up (x.down ◇ y.down)

@[simps] def uliftMagmaEquiv {G} [Magma G] : G ≃◇ ULift G where
  toFun := .up
  invFun := (·.down)
  left_inv _ := rfl
  right_inv _ := rfl
  map_op' _ _ := rfl

theorem models_def' {α β} {Γ : Ctx α} {E : MagmaLaw β} :
    Γ ⊧ E ↔ ∀ (G : Type*) [Magma G], G ⊧ Γ → G ⊧ E := by
  constructor <;> intro H G _ h
  · classical
    rw [← models_toNat] at H
    have ⟨h'⟩ := FreeMagmaWithLaws.isDerives (FreeMagmaWithLaws.models_iff_u.1 H)
    exact satisfies_toNat.1 (Soundness'_u h' h)
  · exact (satisfies_equiv uliftMagmaEquiv).2 (H _ ((satisfiesSet_equiv uliftMagmaEquiv).1 h))

/-- Birkhoff's completeness theorem -/
theorem Completeness' {α β} {Γ : Ctx α} {E : MagmaLaw β} (h : Γ ⊧ E) : Nonempty (Γ ⊢' E) :=
  FreeMagmaWithLaws.isDerives (models_def'.1 h _ (FreeMagmaWithLaws.isModel β Γ))

theorem Completeness {α} {Γ : Ctx α} {E : MagmaLaw α} (h : Γ ⊧ E) : Nonempty (Γ ⊢ E) :=
  match Completeness' h with
  | .intro x => .intro (derive_of_derive' x)

def FreeMagmaWithLaws.eval {α G} {Γ : Ctx α} (φ : α → G) [Magma G] (modelsG : G ⊧ Γ) :
    FreeMagmaWithLaws α Γ → G :=
  Quotient.lift (evalInMagma φ) (by
    intro a b
    simp only [HasEquiv.Equiv, SetoidOfLaws, RelOfLaws, Nonempty.forall]
    intro h
    apply (Soundness' (E := a ≃ b))
    . exact h
    . exact modelsG)

def FreeMagmaWithLaws.evalHom {α G} {Γ : Ctx α} (φ : α → G) [ginst : Magma G] (modelsG : G ⊧ Γ) :
    FreeMagmaWithLaws α Γ →◇ G where
  toFun := FreeMagmaWithLaws.eval φ modelsG
  map_op' := by
    simp only [eval, Magma.op, ForkWithLaws, embed]
    intro x y
    -- hmpf choice again.
    have ⟨ x_bar, eqx ⟩ := Quotient.exists_rep x
    have ⟨ y_bar, eqy ⟩ := Quotient.exists_rep y
    rw [← eqx, ← eqy, Quotient.lift₂_mk]
    repeat rw [Quotient.lift_mk]
    simp [evalInMagma]

lemma eq_app : ∀ α β (f g : α → β), f = g → ∀ x, f x = g x := fun _ _ _ _ a x ↦ congrFun a x

-- FIXME: does this exist in mathlib?
lemma Quot.liftEq {α β} [s : Setoid α] (f g : Quotient s → β) (h : f ∘ (⟦.⟧) = g ∘ (⟦.⟧)) :
    f = g := by
  refine funext fun x => ?_
  let ⟨ x_bar, eq_x ⟩ := Quotient.exists_rep x
  exact eq_x ▸ congrFun h x_bar

def FreeMagmaWithLaws.mkMor {α} (Γ : Ctx α) : FreeMagma α →◇ FreeMagmaWithLaws α Γ where
  toFun a := ⟦a⟧
  map_op' := by simp [Magma.op, ForkWithLaws]

-- FIXME: golf this!
theorem FreeMaga.EvalFreeMagmaWithLawsUniversalProperty {α G} {Γ : Ctx α}
(φ : α → G) [ginst : Magma G] (modelsG : G ⊧ Γ)(ψ : FreeMagmaWithLaws α Γ →◇ G) :
    ψ ∘ (⟦.⟧) ∘ Lf = φ → FreeMagmaWithLaws.eval φ modelsG = ψ := by
  intro eq
  let ψ' := (FreeMagmaWithLaws.mkMor Γ).comp ψ
  let φ' := FreeMagmaWithLaws.eval φ modelsG ∘ (⟦.⟧)
  have h : φ' = ψ' := by
    simp only [DFunLike.coe]
    rw [← EvalFreeMagmaUniversalProperty φ]
    . simp only [FreeMagmaWithLaws.eval, φ']
      exact funext fun x ↦ rfl
    . rw [← eq]
      simp only [MagmaHom.comp, FreeMagmaWithLaws.mkMor, ψ']
      rfl
  exact Quot.liftEq (s := _) _ _ h
