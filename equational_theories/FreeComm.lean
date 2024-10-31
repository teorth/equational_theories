/-
  Define the free associative-commutative magma as the multisets with union.
  Prove lemma 3.8: Any consequence of a word equation with equal occurrences of
  vars on the lhs and rhs must also have that property.

-/
import Mathlib.Data.Multiset.Basic
import Mathlib.Algebra.BigOperators.Finprod
import equational_theories.FreeMagma
import equational_theories.MagmaLaw


open Law
variable {α : Type*}

instance Multiset.isMagma : Magma (Multiset α) := { op := (· + ·) }

def FreeMagma.vars (w : FreeMagma α) : Multiset α :=
  evalInMagma (fun x ↦ ({x} : Multiset α)) w

@[simp] lemma FreeMagma.vars_leaf (a : α) : (Lf a).vars = {a} := rfl
@[simp] lemma FreeMagma.vars_fork (v w : FreeMagma α) : (v ⋆ w).vars = v.vars + w.vars := rfl

variable [DecidableEq α]
@[simp]
def FreeMagma.count (w : FreeMagma α) (a : α) : ℕ :=
  match w with
  | .Leaf x => if a = x then 1 else 0
  | .Fork w₁ w₂ => w₁.count a + w₂.count a

lemma FreeMagma.count_vars {w : FreeMagma α} {a : α} :
    w.vars.count a = w.count a := by
  induction w with
  | Leaf _ => simp [evalInMagma, Multiset.count_singleton]
  | Fork _ _ ih₁ ih₂ => simp [evalInMagma, Magma.op, ih₁, ih₂]

-- This (crucial) lemma and the next were devised and proven by Floris van Doorn
-- https://florisvandoorn.com/
lemma FreeMagma.count_subst' {ι : Type*} [DecidableEq ι] {t : FreeMagma ι} {σ : ι → FreeMagma α}
    {a : α} {s : Finset ι} (hs : t.vars ⊆ s.1) : (t ⬝ σ).count a = ∑ i ∈ s, t.count i * (σ i).count a := by
  induction t with
  | Leaf b =>
    simp at hs
    simp [evalInMagma, hs]
  | Fork a b iha ihb =>
    simp at hs
    simp [iha (Multiset.Subset.trans Multiset.subset_add_left hs),
          ihb (Multiset.Subset.trans Multiset.subset_add_right hs),
          Finset.sum_add_distrib, Multiset.isMagma, add_mul]

lemma FreeMagma.count_subst {ι : Type*} [DecidableEq ι] {t : FreeMagma ι} {σ : ι → FreeMagma α}
    {a : α} : (t ⬝ σ).count a = ∑ i ∈ t.vars.toFinset, t.count i * (σ i).count a :=
  t.count_subst' (s := t.vars.toFinset) (hs := by simp)

def Law.MagmaLaw.SameCount {α} [DecidableEq α] (E : MagmaLaw α) :=
  ∀ a, E.lhs.count a = E.rhs.count a

lemma Law.MagmaLaw.SameCount.vars_eq {α} [DecidableEq α] {E : MagmaLaw α} (h : E.SameCount) :
    E.lhs.vars = E.rhs.vars := by
  ext a
  simp_rw [FreeMagma.count_vars, h a]

theorem Law.MagmaLaw.SameCount.derive {α} [DecidableEq α] {Γ : Ctx α} {E : MagmaLaw α}
  (hE : Γ ⊢ E) (hΓ : ∀ E ∈ Γ, E.SameCount) : E.SameCount := by
  induction hE with
  | Ax h => exact hΓ _ h
  | Ref => intro a; rfl
  | Sym _ ih => intro a; symm; exact ih a
  | Trans _ _ ihu ihv => intro a; exact ihu a |>.trans <| ihv a
  | Subst σ _ ih => intro a; simp [FreeMagma.count_subst, ih _, ih.vars_eq]
  | Cong _ _ ih₁ ih₂ => intro a; simp_rw [FreeMagma.count, ih₁ a, ih₂ a]
