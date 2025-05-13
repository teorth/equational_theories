import equational_theories.FreeMagma
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import Mathlib.Tactic.NthRewrite
import Mathlib.Tactic.CasesM

namespace FreeMagma

variable {α : Type}

def Everywhere (P : FreeMagma α → Prop) : FreeMagma α → Prop
  | .Leaf x => P (.Leaf x)
  | x ⋆ y => x.Everywhere P ∧ y.Everywhere P ∧ P (x ⋆ y)

theorem Everywhere.top {P : FreeMagma α → Prop} : {x : FreeMagma α} → Everywhere P x → P x
  | .Leaf _ => fun h => h
  | _ ⋆ _ => fun h => h.2.2

theorem Everywhere.left {P : FreeMagma α → Prop} {x y : FreeMagma α} (h: Everywhere P (x ⋆ y)): Everywhere P x :=
  h.1

theorem Everywhere.right {P : FreeMagma α → Prop} {x y : FreeMagma α} (h: Everywhere P (x ⋆ y)): Everywhere P y :=
  h.2.1

@[simp]
theorem Everywhere_idem {P : FreeMagma α → Prop} : Everywhere (Everywhere P) = Everywhere P := by
  ext x
  constructor <;> intro h
  · induction x with
    | Leaf => exact h
    | Fork x y ihx ihy => exact ⟨ihx h.1, ihy h.2.1,  h.2.2.2.2⟩
  · induction x with
    | Leaf => exact h
    | Fork x y ihx ihy => exact ⟨ihx h.1, ihy h.2.1, h⟩

def SubtermOf (x : FreeMagma α) : (y : FreeMagma α) → Prop
| .Leaf a => x = .Leaf a
| a ⋆ b => x = a ⋆ b ∨ SubtermOf x a ∨ SubtermOf x b

@[refl]
theorem SubtermOf.refl (x : FreeMagma α) : SubtermOf x x := by
  cases x with
  | Leaf => rfl
  | Fork x y => exact Or.inl rfl

lemma SubtermOf.left {x a b: FreeMagma α} (h : SubtermOf x a) : SubtermOf x (a ⋆ b) :=
  Or.inr (Or.inl h)

lemma SubtermOf.right {x a b: FreeMagma α} (h : SubtermOf x b) : SubtermOf x (a ⋆ b) :=
  Or.inr (Or.inr h)

theorem everywhere_of_subterm_of_everywhere {P : FreeMagma α → Prop} {x} (h : x.Everywhere P) {y}
    (hsub : SubtermOf y x) : y.Everywhere P := by
  induction x with
  | Leaf =>
    cases hsub
    exact h.top
  | Fork x y ihx ihy =>
    obtain (rfl | hsub | hsub) := hsub
    · exact h
    · exact ihx h.1 hsub
    · exact ihy h.2.1 hsub

theorem subterm_everywhere {P : FreeMagma α → Prop} {x} (h : x.Everywhere P) {y} (hsub : SubtermOf y x) : P y :=
  (everywhere_of_subterm_of_everywhere h hsub).top

theorem length_le_of_subterm {x y: FreeMagma α} (h: SubtermOf x y) : x.length ≤ y.length := by
  induction y with
  | Leaf =>
    rw [h]
  | Fork x y ihx ihy =>
    obtain (heq | hsub | hsub) := h
    · rw [heq]
    · rw [FreeMagma.length.eq_2]
      exact Nat.le_add_right_of_le (ihx hsub)
    · rw [FreeMagma.length.eq_2, Nat.add_comm]
      exact Nat.le_add_right_of_le (ihy hsub)

variable (rw : FreeMagma α → FreeMagma α)

class IsProj : Prop where
  proj : ∀ x, SubtermOf (rw x) x

variable [hproj: IsProj rw]

@[simp]
lemma projection_leaf (x): rw (.Leaf x) = x :=
  hproj.proj (.Leaf x)

lemma length_le_of_projection (x): (rw x).length ≤ x.length :=
  length_le_of_subterm (hproj.proj x)

theorem everywhere_of_projection_of_everywhere P:
    ∀ x, Everywhere P x → (rw x).Everywhere P :=
  fun x he ↦ everywhere_of_subterm_of_everywhere he (IsProj.proj x)

theorem projection_everywhere P :
    ∀ x, Everywhere P x → P (rw x) :=
  fun x he ↦ subterm_everywhere he (IsProj.proj x)

end FreeMagma

namespace Confluence

open FreeMagma

variable {α : Type}

variable (rw : FreeMagma α → FreeMagma α)

def bu : FreeMagma α → FreeMagma α
  | .Leaf x => rw x
  | x ⋆ y => rw (bu x ⋆ bu y)

attribute [simp] bu.eq_1

abbrev buFixed x := bu rw x = x

@[simp] theorem bu_op_eq_rw_op {x} {y}
    (hx: buFixed rw x) (hy: buFixed rw y): bu rw (x ⋆ y) = rw (x ⋆ y) := by
  nth_rw 2 [← hx, ← hy]
  rw [← bu.eq_2 rw]

lemma length_bu_le [hproj : IsProj rw] (x): (bu rw x).length ≤ x.length := by
  induction x with
  | Leaf =>
    simp
  | Fork x y ihx ihy  =>
    rw [bu.eq_2]
    apply Nat.le_trans (length_le_of_projection rw _) ?_
    simp only [FreeMagma.length.eq_2]
    exact Nat.add_le_add ihx ihy

def NF (x : FreeMagma α) : Prop := x.Everywhere (fun y => rw y = y)

def buNF (x : FreeMagma α) : Prop := x.Everywhere (fun y => bu rw y = y)

lemma buNF_iff_NF {x}: buNF rw x ↔ NF rw x := by
  induction x with
  | Leaf =>
    unfold NF buNF Everywhere
    simp
  | Fork x y ihx ihy =>
    have ih  := and_congr ihx ihy
    unfold NF buNF at ih ⊢
    unfold Everywhere
    simp only [← and_assoc, ← ih]
    apply and_congr_right
    intro ⟨hbx, hby⟩
    simp only [bu, hbx.top, hby.top]

lemma buFixed_of_NF {x : FreeMagma α} (h : NF rw x) : buFixed rw x :=
  ((buNF_iff_NF rw).mpr h).top

lemma rw_eq_self_of_NF {x} (h: NF rw x): rw x = x :=
  h.top

class IsProjOrNF : Prop where
  proj_or_nf : ∀ x, SubtermOf (rw x) x ∨ NF rw (rw x)

instance [hproj: IsProj rw]: IsProjOrNF rw where
  proj_or_nf x := .inl (hproj.proj x)

variable [hproj: IsProjOrNF rw]

theorem bu_nf : ∀ x, NF rw (bu rw x) := by
  intro x
  induction x with
  | Leaf a =>
    simp only [NF, bu, Everywhere]
    obtain (hsub | hnf) := hproj.proj_or_nf (a)
    · unfold SubtermOf at hsub
      unfold Everywhere
      simp [hsub]
    · exact hnf
  | Fork x y ihx ihy =>
    simp only [NF, bu]
    obtain ((heq | hsub | hsub) | hnf) := hproj.proj_or_nf (bu rw x ⋆ bu rw y)
    · simp only [Everywhere, heq, and_true]
      exact ⟨ihx, ihy⟩
    · exact everywhere_of_subterm_of_everywhere ihx hsub
    · exact everywhere_of_subterm_of_everywhere ihy hsub
    · exact hnf

lemma NF_iff_buFixed {x}: NF rw x ↔ buFixed rw x := ⟨buFixed_of_NF rw, fun h ↦ h ▸ bu_nf _ _⟩

@[simp] theorem bu_idem x : buFixed rw (bu rw x) := buFixed_of_NF rw (bu_nf rw x)

@[simp] theorem buFixed_rw_op {x} {y}
    (hx: bu rw x = x) (hy: bu rw y = y): buFixed rw (rw (x ⋆ y)) := by
  rw [← hx, ← hy, ← bu.eq_2 rw]
  exact bu_idem rw _

theorem NF_rw_op_of_buFixed {x} {y}
    (hx: bu rw x = x) (hy: bu rw y = y): NF rw (rw (x ⋆ y)) :=
  (NF_iff_buFixed rw).mpr (buFixed_rw_op rw hx hy)

theorem NF_rw_op {x} {y}
    (hx: NF rw x) (hy: NF rw y): NF rw (rw (x ⋆ y)) := by
  rw [NF_iff_buFixed] at hx hy ⊢
  exact buFixed_rw_op rw hx hy

@[simp] theorem rw_op_idem {x} {y}
  (hx: bu rw x = x) (hy: bu rw y = y): rw (rw (x ⋆ y)) = rw (x ⋆ y) := by
  have := buFixed_rw_op rw hx hy
  rw [← NF_iff_buFixed] at this
  exact rw_eq_self_of_NF rw this

theorem bu_rw_op_eq_rw_rw_op {x} {y}
    (hx: bu rw x = x) (hy: bu rw y = y): bu rw (rw (x ⋆ y)) = rw (rw (x ⋆ y)) := by
  rw [buFixed_rw_op rw hx hy, rw_op_idem rw hx hy]

def ConfMagma := {x : FreeMagma α // bu rw x = x }

instance : Coe α (ConfMagma rw) where
  coe x := ⟨bu rw x, bu_idem rw x⟩

instance : Magma (ConfMagma rw) where
  op := fun x y ↦ ⟨bu rw (x.1 ◇ y.1), bu_idem rw _⟩

instance [DecidableEq α] : DecidableEq (ConfMagma rw) :=
  inferInstanceAs (DecidableEq {x : FreeMagma α // buFixed rw x })

/-- Refutation tactic for dedicable FreeMagma equations -/
macro "refute" : tactic =>
  `(tactic |(
    show (¬ ∀ _,_)
    push_neg
    first
    | (use (0 : Nat); decide)
    | (use (0 : Nat), (1 : Nat); decide)
    | (use (0 : Nat), (1 : Nat), (2: Nat); decide)
    | (use (0 : Nat), (1 : Nat), (2: Nat), (3: Nat); decide)
    | (use (0 : Nat), (1 : Nat), (2: Nat), (3: Nat), (4: Nat); decide)
    | (use (0 : Nat), (1 : Nat), (2: Nat), (3: Nat), (4: Nat), (5: Nat); decide)
    ))

-- doesn't work in the same file where it's declared
register_simp_attr confluence_simps

scoped syntax "subterm" : tactic

scoped macro_rules
| `(tactic| subterm) => `(tactic|
  first
  | apply FreeMagma.SubtermOf.refl
  | apply FreeMagma.SubtermOf.left
    subterm
  | apply FreeMagma.SubtermOf.right
    subterm
)

scoped syntax "everywhere" " at " ident : tactic

scoped macro_rules
| `(tactic| everywhere at $h:ident) => `(tactic|
  first
  | assumption
  | apply FreeMagma.Everywhere.left at $h
    everywhere at $h
  | apply FreeMagma.Everywhere.right at $h
    everywhere at $h
)

scoped syntax "bufixed" : tactic

scoped macro_rules
| `(tactic| bufixed) => `(tactic|
  first
  | assumption
  | apply Confluence.buFixed_rw_op
    all_goals bufixed
)

end Confluence
