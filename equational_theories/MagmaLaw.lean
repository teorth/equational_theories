import equational_theories.FreeMagma
import Mathlib.Data.Set.Defs

open FreeMagma

namespace Law

@[ext] structure MagmaLaw (α : Type*) where
  lhs : FreeMagma α
  rhs : FreeMagma α
deriving DecidableEq

infix:60 " ≃ " => MagmaLaw.mk

abbrev NatMagmaLaw := MagmaLaw Nat

open Lean in
instance {α} [ToJson α] : ToJson (MagmaLaw α) where
  toJson := fun ⟨lhs, rhs⟩ => .mkObj [("lhs", Lean.toJson lhs), ("rhs", Lean.toJson rhs)]

instance {α} [ToString α] : ToString (MagmaLaw α) where
  toString := fun ⟨lhs, rhs⟩ => s!"{lhs} ≃ {rhs}"

end Law

open Law

abbrev Ctx α := Set (MagmaLaw α)

-- FIXME: figure out how to remove this.
instance Ctx.Membership α : Membership (MagmaLaw α) (Ctx α) := ⟨ Set.instMembership.mem ⟩

instance {α : Type} : Singleton (MagmaLaw α) (Ctx α) := ⟨Set.singleton⟩


section DeriveDef

set_option hygiene false

/-- Local Notation for derivability -/
local infix:50 " ⊢ " =>  derive

-- We keep this in type, because we're going to want to gather
-- the (finite!) set of required axioms later.
/-- Definition for derivability -/
inductive derive.{u} {α : Type u} (Γ : Ctx α) : MagmaLaw α → Type u :=
  | Ax {E} (h : E ∈ Γ) : Γ ⊢ E
  | Ref {t} : Γ ⊢ t ≃ t
  | Sym {t u} : Γ ⊢ t ≃ u → Γ ⊢ u ≃ t
  | Trans {t u v} : Γ ⊢ t ≃ u → Γ ⊢ u ≃ v → Γ ⊢ t ≃ v
  -- This is not as polymorphic as it could be, shouldn't be an issue at the moment
  | Subst {t u} σ : Γ ⊢ t ≃ u → Γ ⊢ t ⬝ σ ≃ u ⬝ σ
  | Cong {t₁ t₂ u₁ u₂} : Γ ⊢ (t₁ ≃ t₂) → Γ ⊢ (u₁ ≃ u₂) → Γ ⊢ (t₁ ⋆ u₁ ≃ t₂ ⋆ u₂)

local infix:50 " ⊢' " =>  derive'

/-- Definition for derivability where Subst can only be applied to Ax -/
inductive derive'.{u, v} {α : Type u} {β : Type v} (Γ : Ctx α) : MagmaLaw β → Type (max u v) :=
  | SubstAx {E} (h : E ∈ Γ) (σ) : Γ ⊢' E.lhs ⬝ σ ≃ E.rhs ⬝ σ
  | Ref {t} : Γ ⊢' t ≃ t
  | Sym {t u} : Γ ⊢' t ≃ u → Γ ⊢' u ≃ t
  | Trans {t u v} : Γ ⊢' t ≃ u → Γ ⊢' u ≃ v → Γ ⊢' t ≃ v
  | Cong {t₁ t₂ u₁ u₂} : Γ ⊢' t₁ ≃ t₂ → Γ ⊢' u₁ ≃ u₂ → Γ ⊢' t₁ ⋆ u₁ ≃ t₂ ⋆ u₂

def derive_of_derive' {α} {Γ : Ctx α} {E : MagmaLaw α} : Γ ⊢' E → Γ ⊢ E
  | .SubstAx (E := E) h σ => derive.Subst σ (derive.Ax h)
  | .Ref  => derive.Ref
  | .Sym h => derive.Sym (derive_of_derive' h)
  | .Trans htu huv => derive.Trans (derive_of_derive' htu) (derive_of_derive' huv)
  | .Cong h₁ h₂ => derive.Cong (derive_of_derive' h₁) (derive_of_derive' h₂)

def derive'_of_derive {α} {Γ : Ctx α} {E : MagmaLaw α} (H : Γ ⊢ E) : Γ ⊢' E := by
  simpa [evalInMagma_leaf] using go Lf H
where
  go {β} (σ : α → FreeMagma β) {E} : Γ ⊢ E → Γ ⊢' E.lhs ⬝ σ ≃ E.rhs ⬝ σ
  | .Ax h => derive'.SubstAx h σ
  | .Ref  => .Ref
  | .Sym h => .Sym (go σ h)
  | .Trans htu huv => .Trans (go σ htu :) (go σ huv)
  | .Subst σ h => by simpa [SubstEval] using go _ h
  | .Cong h₁ h₂ => .Cong (go σ h₁) (go σ h₂)

end DeriveDef

/-- Definitions of entailment -/
def satisfiesPhi {α G} [Magma G] (φ : α → G) (E : MagmaLaw α) : Prop :=
  E.lhs ⬝ φ = E.rhs ⬝ φ

/-- `satisfies G E`, or `G ⊧ E`, means that all evaluations of `E` in `G` are true. -/
def satisfies {α} (G) [Magma G] (E : MagmaLaw α) := ∀ (φ : α → G), satisfiesPhi φ E

/-- `satisfiesSet G Γ`, or `G ⊧ Γ`, means that `G` satisfies every element of `Γ`. -/
def satisfiesSet {α} (G) [Magma G] (Γ : Ctx α) : Prop :=
  ∀ E ∈ Γ, satisfies G E

/-- `models Γ E`, or `Γ ⊧ E`, means that every magma `G` satisfying `Γ` also satisfies `E`. -/
def models {α β} (Γ : Ctx α) (E : MagmaLaw β) : Prop :=
  ∀ (G : Type) [Magma G], satisfiesSet G Γ → satisfies G E

/-! Notation for derivability and entailment -/

@[inherit_doc] infix:50 " ⊧ " => satisfies

@[inherit_doc] infix:50 " ⊧ " => satisfiesSet

@[inherit_doc] infix:50 " ⊧ " => models

@[inherit_doc] infix:50 " ⊢ " => derive

@[inherit_doc] infix:50 " ⊢' " => derive'

namespace Law

namespace MagmaLaw

def symm {α} (l : MagmaLaw α) : MagmaLaw α := {lhs := l.rhs, rhs := l.lhs}

@[simp]
theorem symm_symm {α} (l : MagmaLaw α) : l.symm.symm = l :=
  rfl

def map {α β} (f : α → β) : MagmaLaw α → MagmaLaw β
  | ⟨lhs, rhs⟩ => ⟨fmapHom f lhs, fmapHom f rhs⟩

theorem map_id {α} (m : MagmaLaw α) : m.map id = m := by
  simp [map, fmapHom_id]

theorem map_comp {α β γ} (f : α → β) (g : β → γ) (m : MagmaLaw α) :
    (m.map f).map g = m.map (g ∘ f) := by
  simp [map, fmapHom_comp']

theorem map_symm {α β} (f : α → β) (m : MagmaLaw α) : m.symm.map f = (m.map f).symm := rfl

def Mem {α} (a : α) (m : MagmaLaw α) : Prop :=
  m.lhs.Mem a ∨ m.rhs.Mem a

def toList {α} (m : MagmaLaw α) : List α := m.lhs.toList ++ m.rhs.toList

@[simp] def map_toList {α β} (m : MagmaLaw α) (f : α → β) :
    (m.map f).toList = m.toList.map f := by simp [map, toList]

def elems {α} [DecidableEq α] (m : MagmaLaw α) :
    {l : List α // l.Nodup ∧ ∀ a, a ∈ l ↔ Mem a m} := by
  let ⟨l, _, hl⟩ := m.lhs.elems
  let ⟨r, nr, hr⟩ := m.rhs.elems
  use l ∪ r, .union _ nr; simp [Mem, hl, hr]

instance {α} [DecidableEq α] (a : α) (m : MagmaLaw α) : Decidable (Mem a m) :=
  decidable_of_iff _ (m.elems.2.2 _)

def finEquiv {α} [DecidableEq α] (m : MagmaLaw α) : Fin m.elems.1.length ≃ {a // Mem a m} := by
  convert ← m.elems.2.1.getEquiv; apply m.elems.2.2

def pmap {α β} : ∀ (m : MagmaLaw α), (∀ a, Mem a m → β) → MagmaLaw β
  | ⟨lhs, rhs⟩, f =>
    ⟨lhs.pmap fun a h => f a (.inl h), rhs.pmap fun a h => f a (.inr h)⟩

def attach {α} (m : MagmaLaw α) : MagmaLaw {a // Mem a m} := pmap m .mk

theorem attach_map_val {α} (m : MagmaLaw α) : m.attach.map (·.val) = m := by
  apply congrArg₂ MagmaLaw.mk <;> exact (evalInMagma_pmap _ (by simp)).trans (fmapHom_id _)

def toFin {α} [DecidableEq α] (m : MagmaLaw α) : MagmaLaw (Fin m.elems.1.length) :=
  m.attach.map (finEquiv m).symm

def toNat {α} [DecidableEq α] (m : MagmaLaw α) : MagmaLaw ℕ :=
  (toFin m).map (·.val)

theorem pmap_eq_map {α β} (m : MagmaLaw α)
    (f : (a : α) → Mem a m → β) (g : α → β) (h : ∀ a h, f a h = g a) :
    m.pmap f = m.map g := by
  simp only [pmap, map, mk.injEq]; constructor <;> exact FreeMagma.pmap_eq_map _ _ _ fun _ _ ↦ h _ _
end MagmaLaw

theorem satisfiesPhi_symm_law {α G} [Magma G] (φ : α → G) (E : MagmaLaw α)
    (h : satisfiesPhi φ E) : satisfiesPhi φ E.symm := by
  rw [satisfiesPhi, MagmaLaw.symm]; exact h.symm

theorem satisfiesPhi_map {α β G} [Magma G] {φ : β → G} {f : α → β} {E : MagmaLaw α} :
    satisfiesPhi φ (E.map f) ↔ satisfiesPhi (φ ∘ f) E := by
  simp [satisfiesPhi, MagmaLaw.map, evalInMagma_fmapHom]

theorem satisfiesPhi_pmap {α β G} [Magma G] {φ : β → G} {ψ : α → G}
    (E : MagmaLaw α) (f : (a : α) → E.Mem a → β) (H : ∀ a h, φ (f a h) = ψ a) :
    satisfiesPhi φ (E.pmap f) ↔ satisfiesPhi ψ E := by
  simp only [satisfiesPhi, MagmaLaw.pmap]
  rw [evalInMagma_pmap _ fun a h => H a (.inl h), evalInMagma_pmap _ fun a h => H a (.inr h)]

theorem satisfiesPhi_pmap_mk {α G} [Magma G] {φ : α → G} {E : MagmaLaw α}
    (P : α → Prop) (hp : ∀ a, E.Mem a → P a) :
    satisfiesPhi (φ ·.1) (E.pmap fun a h => Subtype.mk a (hp a h)) ↔ satisfiesPhi φ E :=
  satisfiesPhi_pmap _ _ (fun _ _ ↦ rfl)

theorem satisfiesPhi_attach {α G} [Magma G] {φ : α → G} {E : MagmaLaw α} :
    satisfiesPhi (φ ·.1) E.attach ↔ satisfiesPhi φ E := satisfiesPhi_pmap_mk ..

theorem satisfiesPhi_symm {α G} [Magma G] (φ : α → G) (w₁ w₂ : FreeMagma α)
    (h : satisfiesPhi φ (w₁ ≃ w₂)) : satisfiesPhi φ (w₂ ≃ w₁) :=
  satisfiesPhi_symm_law φ (w₁ ≃ w₂) h


theorem satisfiesPhi_evalHom {α G : Type} [Magma G] (φ : α → G) (E : MagmaLaw α) (f : G →◇ G) :
    satisfiesPhi (f ∘ φ) E ↔ f (E.lhs ⬝ φ) = f (E.rhs ⬝ φ) := by
  rw [satisfiesPhi, ← @evalInMagma_hom, ← evalInMagma_hom]

theorem equiv_satisfiesPhi {α G H} [Magma G] [Magma H] {φ : α → G} (e : G ≃◇ H) {E : MagmaLaw α} :
    satisfiesPhi (e ∘ φ) E ↔ satisfiesPhi φ E := by
  simp [satisfiesPhi, ← evalInMagma_equiv]

theorem satisfies_symm_law {α G} [Magma G] {E : MagmaLaw α} (h : G ⊧ E) :
    G ⊧ E.symm :=
  fun φ ↦ satisfiesPhi_symm_law φ E (h φ)

theorem satisfies_map {α β G} [Magma G] (f : α → β) {E : MagmaLaw α} (h : G ⊧ E) :
    G ⊧ E.map f := fun _ ↦ satisfiesPhi_map.2 (h _)

theorem satisfies_map_injective {α β G} [Magma G] (f : α → β) (hf : f.Injective) {E : MagmaLaw α} :
    G ⊧ E.map f ↔ G ⊧ E := by
  refine ⟨fun H φ => ?_, satisfies_map _⟩
  have : Inhabited α := ⟨E.lhs.first⟩
  have ⟨g, hg⟩ := hf.hasLeftInverse
  rw [← MagmaLaw.map_id E, ← show g ∘ f = id from funext hg, ← MagmaLaw.map_comp, satisfiesPhi_map]
  exact H _

theorem satisfies_map_equiv {α β G} [Magma G] (f : α ≃ β) {E : MagmaLaw α} :
    G ⊧ E.map f ↔ G ⊧ E :=
  satisfies_map_injective _ f.injective

theorem satisfies_pmap_mk {α G} [DecidableEq α] [Magma G] {E : MagmaLaw α}
    (P : α → Prop) (hp : ∀ a, E.Mem a → P a) :
    G ⊧ E.pmap (fun a h => Subtype.mk a (hp a h)) ↔ G ⊧ E := by
  refine ⟨fun h φ => (satisfiesPhi_pmap_mk _ _).1 (h _), fun h φ => ?_⟩
  have : Inhabited G := ⟨φ ⟨E.lhs.first, hp _ <| .inl E.lhs.first_mem⟩⟩
  let ψ a := if h : E.Mem a then φ ⟨a, hp _ h⟩ else default
  exact (satisfiesPhi_pmap (ψ := ψ) _ _ (fun a h => by simp [ψ, h])).2 (h _)

theorem satisfies_attach {α G} [DecidableEq α] [Magma G] {E : MagmaLaw α} :
    G ⊧ E.attach ↔ G ⊧ E := satisfies_pmap_mk ..

theorem satisfies_toFin {α G} [DecidableEq α] [Magma G] {E : MagmaLaw α} :
    G ⊧ E.toFin ↔ G ⊧ E :=
  (satisfies_map_equiv _).trans satisfies_attach

theorem satisfies_toNat {α G} [DecidableEq α] [Magma G] {E : MagmaLaw α} :
    G ⊧ E.toNat ↔ G ⊧ E :=
  (satisfies_map_injective _ Fin.val_injective).trans satisfies_toFin

theorem satisfies_symm {α G} [Magma G] {w₁ w₂ : FreeMagma α} (h : G ⊧ w₁ ≃ w₂) :
    G ⊧ w₂ ≃ w₁ :=
  satisfies_symm_law h

theorem satisfies_equiv {α G H} [Magma G] [Magma H] (e : G ≃◇ H) {E : MagmaLaw α} :
    G ⊧ E ↔ H ⊧ E := by
  constructor <;> intro h φ
  · rw [← equiv_satisfiesPhi e.symm]; exact h _
  · rw [← equiv_satisfiesPhi e]; exact h _

theorem satisfiesSet_symm {α G} [Magma G] {Γ : Ctx α}
  (h :  G ⊧ Γ) : G ⊧ (·.symm) '' Γ :=
  fun _ ⟨_, ⟨hEsymm, hEsymmE⟩⟩ ↦ hEsymmE ▸ Law.satisfies_symm (h _ hEsymm)

theorem satisfiesSet_singleton {α G} [Magma G] {E : MagmaLaw α} : G ⊧ {E} ↔ G ⊧ E := by
  simp [satisfiesSet]

theorem satisfiesSet_equiv {α G H} [Magma G] [Magma H] (e : G ≃◇ H) {Γ : Ctx α} :
    G ⊧ Γ ↔ H ⊧ Γ :=
  forall_congr' fun _ => forall_congr' fun _ => satisfies_equiv e

theorem satisfiesSet_toNat {α G} [DecidableEq α] [Magma G] {Γ : Ctx α} :
    G ⊧ (·.toNat) '' Γ ↔ G ⊧ Γ :=
  ⟨fun H _ h => satisfies_toNat.1 (H _ ⟨_, h, rfl⟩),
   fun | H, _, ⟨_, h, rfl⟩ => satisfies_toNat.2 (H _ h)⟩

theorem models_symm_law {α} {Γ : Ctx α} {E : MagmaLaw α} (h : Γ ⊧ E) : Γ ⊧ E.symm :=
  fun G [Magma G] hsatisfiesSet ↦ satisfies_symm_law (h G hsatisfiesSet)

theorem models_symm {α} (Γ : Ctx α) (w₁ w₂ : FreeMagma α) (h : Γ ⊧ w₁ ≃ w₂) : Γ ⊧ w₂ ≃ w₁ :=
  Law.models_symm_law h

theorem models_toNat {α β} [DecidableEq β] {Γ : Ctx α} {E : MagmaLaw β} :
    Γ ⊧ E.toNat ↔ Γ ⊧ E :=
  forall_congr' fun _ => forall_congr' fun _ => imp_congr_right fun _ => satisfies_toNat

theorem toNat_models {α β} [DecidableEq α] {Γ : Ctx α} {E : MagmaLaw β} :
    (·.toNat) '' Γ ⊧ E ↔ Γ ⊧ E :=
  forall_congr' fun _ => forall_congr' fun _ => imp_congr_left satisfiesSet_toNat

def derive'_map {α β γ} {f : β → γ} : ∀ {Γ : Ctx α} {E : MagmaLaw β}, Γ ⊢' E → Γ ⊢' E.map f
  | _, _, .SubstAx h σ => by simp [MagmaLaw.map, evalInMagma_hom]; exact .SubstAx h _
  | _, _, .Ref => .Ref
  | _, _, .Sym h => .Sym (derive'_map h)
  | _, _, .Trans h1 h2 => .Trans (derive'_map h1) (derive'_map h2)
  | _, _, .Cong h1 h2 => .Cong (derive'_map h1) (derive'_map h2)

theorem derive'_map_injective {α β γ} {f : β → γ} (hf : f.Injective) {Γ : Ctx α} {E : MagmaLaw β} :
    Nonempty (Γ ⊢' E.map f) ↔ Nonempty (Γ ⊢' E) := by
  refine ⟨fun ⟨h⟩ => ?_, fun ⟨h⟩ => ⟨derive'_map h⟩⟩
  have : Inhabited β := ⟨E.lhs.first⟩
  have ⟨g, hg⟩ := hf.hasLeftInverse
  rw [← MagmaLaw.map_id E, ← show g ∘ f = id from funext hg, ← MagmaLaw.map_comp]
  exact ⟨derive'_map h⟩

def derive'_pmap {α β γ} [DecidableEq β] {Γ : Ctx α} {E : MagmaLaw β} (f : ∀ a, E.Mem a → γ) :
    Γ ⊢' E → Γ ⊢' E.pmap f := by
  have : Inhabited γ := ⟨f _ (.inl (first_mem _))⟩
  let k a := if h : _ then f a h else default
  rw [MagmaLaw.pmap_eq_map E f k fun a h => by simp [k, h]]
  apply derive'_map

def derive'_attach {α β} [DecidableEq β] {Γ : Ctx α} {E : MagmaLaw β} :
    Γ ⊢' E → Γ ⊢' E.attach := derive'_pmap _

theorem derive'_attach_iff {α β} [DecidableEq β] {Γ : Ctx α} {E : MagmaLaw β} :
    Nonempty (Γ ⊢' E.attach) ↔ Nonempty (Γ ⊢' E) :=
  ⟨fun ⟨h⟩ => ⟨(MagmaLaw.attach_map_val _ ▸ derive'_map h :)⟩, fun ⟨h⟩ => ⟨derive'_attach h⟩⟩

theorem derive'_toFin_iff {α β} [DecidableEq β] {Γ : Ctx α} {E : MagmaLaw β} :
    Nonempty (Γ ⊢' E.toFin) ↔ Nonempty (Γ ⊢' E) :=
  (derive'_map_injective (Equiv.injective _)).trans derive'_attach_iff

theorem derive'_toNat_iff {α β} [DecidableEq β] {Γ : Ctx α} {E : MagmaLaw β} :
    Nonempty (Γ ⊢' E.toNat) ↔ Nonempty (Γ ⊢' E) :=
  (derive'_map_injective Fin.val_injective).trans derive'_toFin_iff

theorem satisfies_fin_satisfies_nat {n : Nat} (G) [Magma G] (E : MagmaLaw (Fin n)) :
    G ⊧ E.map Fin.val ↔ G ⊧ E :=
  satisfies_map_injective _ Fin.val_injective

end Law
