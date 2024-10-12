import equational_theories.ConfluenceAttr
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
  | Fork x y => left; rfl

lemma SubtermOf.left {x a b: FreeMagma α} (h : SubtermOf x a) : SubtermOf x (a ⋆ b) := by
  right
  left
  exact h

lemma SubtermOf.right {x a b: FreeMagma α} (h : SubtermOf x b) : SubtermOf x (a ⋆ b) := by
  right
  right
  exact h

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
    · rw [FreeMagma.length.eq_2]
      rw [Nat.add_comm]
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

lemma buFixed_of_NF {x : FreeMagma α} (h : NF rw x) : buFixed rw x := by
  apply ((buNF_iff_NF rw).mpr h).top

lemma rw_eq_self_of_NF {x} (h: NF rw x): rw x = x := by
  apply h.top

class IsProjOrNF : Prop where
  proj_or_nf : ∀ x, SubtermOf (rw x) x ∨ NF rw (rw x)

instance [hproj: IsProj rw]: IsProjOrNF rw where
  proj_or_nf x := .inl (hproj.proj x)

variable [hproj: IsProjOrNF rw]

theorem bu_nf : ∀ x, NF rw (bu rw x) := by
  intro x
  induction x with
  | Leaf a =>
    simp [NF, bu, Everywhere]
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

lemma NF_iff_buFixed {x}: NF rw x ↔ buFixed rw x := by
  constructor
  · exact buFixed_of_NF rw
  · intro h
    rw [← h]
    apply bu_nf

@[simp] theorem bu_idem x : buFixed rw (bu rw x) := buFixed_of_NF rw (bu_nf rw x)

@[simp] theorem buFixed_rw_op {x} {y}
    (hx: bu rw x = x) (hy: bu rw y = y): buFixed rw (rw (x ⋆ y)) := by
  rw [← hx, ← hy, ← bu.eq_2 rw]
  exact bu_idem rw _

theorem NF_rw_op_of_buFixed {x} {y}
    (hx: bu rw x = x) (hy: bu rw y = y): NF rw (rw (x ⋆ y)) := by
  apply (NF_iff_buFixed rw).mpr
  exact buFixed_rw_op rw hx hy

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

/-! This is the end of the setup, the rest is for concrete laws -/

namespace rw477

variable [DecidableEq α]

-- equation 477 := x = y ◇ (x ◇ (y ◇ (y ◇ y)))
def rule : FreeMagma α → FreeMagma α
  | m@(y1 ⋆ (x ⋆ (y2 ⋆ (y3 ⋆ y4)))) =>
      if y1 = y2 ∧ y1 = y3 ∧ y1 = y4 then
        x
      else
        m
  | m => m

instance rule_projection : IsProj (@rule α _) where
  proj := by
    intro x
    unfold rule
    split
    · split
      · right; right; right; left; rfl
      · rfl
    · rfl

@[simp]
theorem rule_yy (y : FreeMagma α) : rule (y ⋆ y) = y ⋆ y := by
  unfold rule
  split
  · rename_i m2' y1 x y2 y3 y4 heq
    simp only [Fork.injEq] at heq
    obtain ⟨rfl, heq⟩ := heq
    split
    · exfalso
      rename_i hys
      obtain ⟨rfl, rfl, rfl⟩ := hys
      have := congrArg FreeMagma.length heq
      simp [FreeMagma.length] at this
      have := FreeMagma.length_pos y
      omega
    · simp [heq]
  · rfl

@[simp]
theorem rule_yyy {α} [DecidableEq α] (y : FreeMagma α) :
    rule (y ⋆ (y ⋆ y)) = y ⋆ (y ⋆ y) := by
  unfold rule
  split
  · rename_i m2' y1 x y2 y3 y4 heq
    simp only [Fork.injEq] at heq
    obtain ⟨rfl, rfl, heq⟩ := heq
    split
    · exfalso
      rename_i hys
      obtain ⟨rfl, rfl, rfl⟩ := hys
      have := congrArg FreeMagma.length heq
      simp [FreeMagma.length] at this
    · simp [heq]
  · rfl

@[simp]
theorem rule_xyyy {α} [DecidableEq α] (x y : FreeMagma α) :
    rule (x ⋆ (y ⋆ (y ⋆ y))) = x ⋆ (y ⋆ (y ⋆ y)) := by
  unfold rule
  split
  · rename_i m2' y1 x y2 y3 y4 heq
    simp only [Fork.injEq] at heq
    obtain ⟨rfl, rfl, rfl, heq⟩ := heq
    split
    · exfalso
      rename_i hys
      obtain ⟨rfl, rfl, rfl⟩ := hys
      have := congrArg FreeMagma.length heq
      simp [FreeMagma.length] at this
    · simp [heq]
  · rfl

@[simp]
theorem rule_yxyyy {α} [DecidableEq α] (x y : FreeMagma α) :
    rule (y ⋆ (x ⋆ (y ⋆ (y ⋆ y)))) = x := by
  simp [rule]

@[equational_result]
theorem «Facts» :
  ∃ (G : Type) (_ : Magma G), Facts G [477] [1426, 1519, 2035, 2128, 3050, 3150] := by
  use ConfMagma (@rule Nat _), inferInstance
  repeat' apply And.intro
  · rintro ⟨x, hx⟩ ⟨y, hy⟩
    simp [Magma.op, bu, hx, hy]
  all_goals refute

end rw477

namespace rw467

variable [DecidableEq α]

-- equation 467 := x = y ◇ (x ◇ (x ◇ (y ◇ y)))
def rule : FreeMagma α → FreeMagma α
  | m@(y1 ⋆ (x ⋆ (x2 ⋆ (y2 ⋆ y3)))) =>
      if y1 = y2 ∧ y1 = y3 ∧ x = x2 then
        x
      else
        m
  | m => m

instance rule_projection : IsProj (@rule α _) where
  proj := by
    intro x
    unfold rule
    split
    · split
      · right; right; right; left; rfl
      · rfl
    · rfl

@[simp]
theorem rule_yy (y : FreeMagma α) : rule (y ⋆ y) = y ⋆ y := by
  unfold rule
  split
  · rename_i m2' y1 x y2 y3 y4 heq
    simp only [Fork.injEq] at heq
    obtain ⟨rfl, heq⟩ := heq
    split
    · exfalso
      rename_i hys
      obtain ⟨rfl, rfl, rfl⟩ := hys
      have := congrArg FreeMagma.length heq
      simp [FreeMagma.length] at this
      have := FreeMagma.length_pos y
      omega
    · simp [heq]
  · rfl

@[simp]
theorem rule_xyy {α} [DecidableEq α] (x y : FreeMagma α) :
    rule (x ⋆ (y ⋆ y)) = x ⋆ (y ⋆ y) := by
  unfold rule
  split
  · rename_i m2' y1 x y2 y3 y4 heq
    simp only [Fork.injEq] at heq
    obtain ⟨rfl, rfl, heq⟩ := heq
    split
    · exfalso
      rename_i hys
      obtain ⟨rfl, rfl, rfl⟩ := hys
      have := congrArg FreeMagma.length heq
      simp [FreeMagma.length] at this
    · simp [heq]
  · rfl

@[simp]
theorem rule_xxyy {α} [DecidableEq α] (x y : FreeMagma α) :
    rule (x ⋆ (x ⋆ (y ⋆ y))) = x ⋆ (x ⋆ (y ⋆ y)) := by
  unfold rule
  split
  · rename_i m2' y1 x y2 y3 y4 heq
    simp only [Fork.injEq] at heq
    obtain ⟨rfl, rfl, rfl, heq⟩ := heq
    split
    · exfalso
      rename_i hys
      obtain ⟨rfl, rfl, rfl⟩ := hys
      have := congrArg FreeMagma.length heq
      simp [FreeMagma.length] at this
    · simp [heq]
  · rfl

@[simp]
theorem rule_yxxyy {α} [DecidableEq α] (x y : FreeMagma α) :
    rule (y ⋆ (x ⋆ (x ⋆ (y ⋆ y)))) = x := by
  simp [rule]

@[equational_result]
theorem «Facts» : ∃ (G : Type) (_ : Magma G), Facts G [467] [2847] := by
  use ConfMagma (@rule Nat _), inferInstance
  repeat' apply And.intro
  · rintro ⟨x, hx⟩ ⟨y, hy⟩
    simp [Magma.op, bu, hx, hy]
  all_goals refute

end rw467

namespace rw504

variable [DecidableEq α]

-- equation 504 := x = y ◇ (y ◇ (x ◇ (y ◇ y)))
def rule : FreeMagma α → FreeMagma α
  | m@(y1 ⋆ (y2 ⋆ (x ⋆ (y3 ⋆ y4)))) =>
      if y1 = y2 ∧ y1 = y3 ∧ y1 = y4 then
        x
      else
        m
  | m => m

instance rule_projection : IsProj (@rule α _) where
  proj := by
    intro x
    unfold rule
    split
    · split
      · right; right; right; right; right; left; rfl
      · rfl
    · rfl

@[simp]
theorem rule_yy (y : FreeMagma α) : rule (y ⋆ y) = y ⋆ y := by
  unfold rule
  split
  · rename_i m2' y1 x y2 y3 y4 heq
    simp only [Fork.injEq] at heq
    obtain ⟨rfl, heq⟩ := heq
    split
    · exfalso
      rename_i hys
      obtain ⟨rfl, rfl, rfl⟩ := hys
      have := congrArg FreeMagma.length heq
      simp [FreeMagma.length] at this
    · simp [heq]
  · rfl

@[simp]
theorem rule_xyy {α} [DecidableEq α] (x y : FreeMagma α) :
    rule (x ⋆ (y ⋆ y)) = x ⋆ (y ⋆ y) := by
  unfold rule
  split
  · rename_i m2' y1 x y2 y3 y4 heq
    simp only [Fork.injEq] at heq
    obtain ⟨rfl, rfl, heq⟩ := heq
    split
    · exfalso
      rename_i hys
      obtain ⟨rfl, rfl, rfl⟩ := hys
      have := congrArg FreeMagma.length heq
      simp [FreeMagma.length] at this
      have := FreeMagma.length_pos x
      omega
    · simp [heq]
  · rfl

@[simp]
theorem rule_yxyy {α} [DecidableEq α] (x y : FreeMagma α) :
    rule (y ⋆ (x ⋆ (y ⋆ y))) = y ⋆ (x ⋆ (y ⋆ y)) := by
  unfold rule
  split
  · rename_i m2' y1 x y2 y3 y4 heq
    simp only [Fork.injEq] at heq
    obtain ⟨rfl, rfl, rfl, heq⟩ := heq
    split
    · exfalso
      rename_i hys
      obtain ⟨rfl, rfl, rfl⟩ := hys
      have := congrArg FreeMagma.length heq
      simp [FreeMagma.length] at this
    · simp [heq]
  · rfl

@[simp]
theorem rule_yyxyy {α} [DecidableEq α] (x y : FreeMagma α) :
    rule (y ⋆ (y ⋆ (x ⋆ (y ⋆ y)))) = x := by
  simp [rule]

@[equational_result]
theorem «Facts» : ∃ (G : Type) (_ : Magma G), Facts G [504] [817, 1629, 1832, 1925] := by
  use ConfMagma (@rule Nat _), inferInstance
  repeat' apply And.intro
  · rintro ⟨x, hx⟩ ⟨y, hy⟩
    simp [Magma.op, bu, hx, hy]
  all_goals refute

end rw504

namespace rw1515

variable [DecidableEq α]

-- equation 1515 := x = (y ◇ y) ◇ (x ◇ (x ◇ x))
def rule : FreeMagma α → FreeMagma α
  | m@((y1 ⋆ y2) ⋆ (x ⋆ (x1 ⋆ x2))) =>
      if y1 = y2 ∧ x = x1 ∧ x = x2 then
        x
      else
        m
  | m => m

instance rule_projection : IsProj (@rule α _) where
  proj := by
    intro x
    unfold rule
    split
    · split
      · right; right; right; left; rfl
      · rfl
    · rfl

@[simp]
theorem rule_yy (y : FreeMagma α) : rule (y ⋆ y) = y ⋆ y := by
  unfold rule
  split
  · rename_i m2' y1 x y2 y3 y4 heq
    simp only [Fork.injEq] at heq
    obtain ⟨rfl, heq⟩ := heq
    simp only [Fork.injEq] at heq
    obtain ⟨rfl, heq⟩ := heq
    split
    · exfalso
      rename_i hys
      obtain ⟨rfl, rfl, rfl⟩ := hys
      have := congrArg FreeMagma.length heq
      simp [FreeMagma.length] at this
    · simp [heq]
  · rfl

@[simp]
theorem rule_xyy {α} [DecidableEq α] (x y : FreeMagma α) :
    rule (x ⋆ (y ⋆ y)) = x ⋆ (y ⋆ y) := by
  unfold rule
  split
  · rename_i m2' y1 x y2 y3 y4 heq
    simp only [Fork.injEq] at heq
    obtain ⟨rfl, rfl, heq⟩ := heq
    split
    · exfalso
      rename_i hys
      obtain ⟨rfl, rfl, rfl⟩ := hys
      have := congrArg FreeMagma.length heq
      simp [FreeMagma.length] at this
    · simp [heq]
  · rfl

@[simp]
theorem rule_yyxxx {α} [DecidableEq α] (x y : FreeMagma α) :
    rule ((y ⋆ y) ⋆ (x ⋆ (x ⋆ x))) = x := by
  simp [rule]

@[equational_result]
theorem «Facts» : ∃ (G : Type) (_ : Magma G), Facts G [1515] [4590] := by
  use ConfMagma (@rule Nat _), inferInstance
  repeat' apply And.intro
  · rintro ⟨x, hx⟩ ⟨y, hy⟩
    simp [Magma.op, bu, hx, hy]
  all_goals refute

end rw1515


namespace rw2038

variable [DecidableEq α]

-- equation 2038 := x = ((x ◇ x) ◇ x) ◇ (y ◇ y)
def rule : FreeMagma α → FreeMagma α
  | m@(((x ⋆ x1) ⋆ x2) ⋆ (y1 ⋆ y2)) =>
      if y1 = y2 ∧ x = x1 ∧ x = x2 then
        x
      else
        m
  | m => m

instance rule_projection : IsProj (@rule α _) where
  proj := by
    intro x
    unfold rule
    split
    · split
      · right; left; right; left; right; left; rfl
      · rfl
    · rfl

@[simp]
theorem rule_yy (y : FreeMagma α) : rule (y ⋆ y) = y ⋆ y := by
  unfold rule
  split
  · rename_i m2' y1 x y2 y3 y4 heq
    simp only [Fork.injEq] at heq
    obtain ⟨rfl, heq⟩ := heq
    simp only [Fork.injEq] at heq
    obtain ⟨rfl, heq⟩ := heq
    split
    · exfalso
      rename_i hys
      obtain ⟨rfl, rfl, rfl⟩ := hys
      have := congrArg FreeMagma.length heq
      simp [FreeMagma.length] at this
    · simp [heq]
  · rfl

@[simp]
theorem rule_xyy {α} [DecidableEq α] (x y : FreeMagma α) :
    rule ((y ⋆ y) ⋆ x) = (y ⋆ y) ⋆ x := by
  unfold rule
  split
  · rename_i m2' y1 x y2 y3 y4 heq
    simp only [Fork.injEq] at heq
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := heq
    split
    · exfalso
      rename_i hys
      obtain ⟨rfl, rfl, heq⟩ := hys
      have := congrArg FreeMagma.length heq
      simp [FreeMagma.length] at this
    · rfl
  · rfl

@[simp]
theorem rule_xxxyy {α} [DecidableEq α] (x y : FreeMagma α) :
    rule (((x ⋆ x) ⋆ x) ⋆ (y ⋆ y)) = x := by
  simp [rule]

@[equational_result]
theorem «Facts» : ∃ (G : Type) (_ : Magma G), Facts G [2038] [4270] := by
  use ConfMagma (@rule Nat _), inferInstance
  repeat' apply And.intro
  · rintro ⟨x, hx⟩ ⟨y, hy⟩
    simp [Magma.op, bu, hx, hy]
  all_goals refute

end rw2038


namespace rw3140

variable [DecidableEq α]

-- equation 3140 := x = (((y ◇ y) ◇ x) ◇ x) ◇ y
def rule : FreeMagma α → FreeMagma α
  | m@((((y1 ⋆ y2) ⋆ x) ⋆ x1) ⋆ y3) =>
      if y1 = y2 ∧ y1 = y3 ∧ x = x1 then
        x
      else
        m
  | m => m

instance rule_projection : IsProj (@rule α _) where
  proj := by
    intro x
    unfold rule
    split
    · split
      · right; left; right; left; right; right; rfl
      · rfl
    · rfl

@[simp]
theorem rule_yy (y : FreeMagma α) : rule (y ⋆ y) = y ⋆ y := by
  unfold rule
  split
  · rename_i m2' y1 x y2 y3 y4 heq
    simp only [Fork.injEq] at heq
    obtain ⟨heq, rfl⟩ := heq
    split
    · exfalso
      rename_i hys
      obtain ⟨rfl, rfl, rfl⟩ := hys
      have := congrArg FreeMagma.length heq
      simp [FreeMagma.length] at this
      have := FreeMagma.length_pos y1
      omega
    · simp [heq]
  · rfl

@[simp]
theorem rule_yyx {α} [DecidableEq α] (x y : FreeMagma α) :
    rule ((y ⋆ y) ⋆ x) = (y ⋆ y) ⋆ x := by
  unfold rule
  split
  · rename_i m2' y1 x y2 y3 y4 heq
    simp only [Fork.injEq] at heq
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := heq
    split
    · exfalso
      rename_i hys
      obtain ⟨rfl, rfl, heq⟩ := hys
      have := congrArg FreeMagma.length heq
      simp [FreeMagma.length] at this
    · rfl
  · rfl

@[simp]
theorem rule_yyxx {α} [DecidableEq α] (x y : FreeMagma α) :
    rule (((y ⋆ y) ⋆ x) ⋆ x) = ((y ⋆ y) ⋆ x) ⋆ x := by
  unfold rule
  split
  · rename_i m2' y1 x y2 y3 y4 heq
    simp only [Fork.injEq] at heq
    obtain ⟨⟨⟨heq, rfl⟩, rfl⟩, rfl⟩ := heq
    split
    · exfalso
      rename_i hys
      obtain ⟨rfl, rfl, rfl⟩ := hys
      have := congrArg FreeMagma.length heq
      simp [FreeMagma.length] at this
    · simp [heq]
  · rfl

@[simp]
theorem rule_yyxxy {α} [DecidableEq α] (x y : FreeMagma α) :
    rule ((((y ⋆ y) ⋆ x) ⋆ x) ⋆ y) = x := by
  simp [rule]

@[equational_result]
theorem «Facts» : ∃ (G : Type) (_ : Magma G), Facts G [3140] [614] := by
  use ConfMagma (@rule Nat _), inferInstance
  repeat' apply And.intro
  · rintro ⟨x, hx⟩ ⟨y, hy⟩
    simp [Magma.op, bu, hx, hy]
  all_goals refute

end rw3140

namespace rw3143

variable [DecidableEq α]

-- equation 3143 := x = (((y ◇ y) ◇ x) ◇ y) ◇ y
def rule : FreeMagma α → FreeMagma α
  | m@((((y1 ⋆ y2) ⋆ x) ⋆ y3) ⋆ y4) =>
      if y1 = y2 ∧ y1 = y3 ∧ y1 = y4 then
        x
      else
        m
  | m => m

instance rule_projection : IsProj (@rule α _) where
  proj := by
    intro x
    unfold rule
    split
    · split
      · right; left; right; left; right; right; rfl
      · rfl
    · rfl

@[simp]
theorem rule_yy (y : FreeMagma α) : rule (y ⋆ y) = y ⋆ y := by
  unfold rule
  split
  · rename_i m2' y1 x y2 y3 y4 heq
    simp only [Fork.injEq] at heq
    obtain ⟨heq, rfl⟩ := heq
    split
    · exfalso
      rename_i hys
      obtain ⟨rfl, rfl, rfl⟩ := hys
      have := congrArg FreeMagma.length heq
      simp [FreeMagma.length] at this
    · simp [heq]
  · rfl

@[simp]
theorem rule_yyx {α} [DecidableEq α] (x y : FreeMagma α) :
    rule ((y ⋆ y) ⋆ x) = (y ⋆ y) ⋆ x := by
  unfold rule
  split
  · rename_i m2' y1 x y2 y3 y4 heq
    simp only [Fork.injEq] at heq
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := heq
    split
    · exfalso
      rename_i hys
      obtain ⟨rfl, heq, rfl⟩ := hys
      have := congrArg FreeMagma.length heq
      simp [FreeMagma.length] at this
      have := FreeMagma.length_pos y1
      omega
    · rfl
  · rfl

@[simp]
theorem rule_yyxy {α} [DecidableEq α] (x y : FreeMagma α) :
    rule (((y ⋆ y) ⋆ x) ⋆ y) = ((y ⋆ y) ⋆ x) ⋆ y := by
  unfold rule
  split
  · rename_i m2' y1 x y2 y3 y4 heq
    simp only [Fork.injEq] at heq
    obtain ⟨⟨⟨heq, rfl⟩, rfl⟩, rfl⟩ := heq
    split
    · exfalso
      rename_i hys
      obtain ⟨rfl, rfl, rfl⟩ := hys
      have := congrArg FreeMagma.length heq
      simp [FreeMagma.length] at this
    · simp [heq]
  · rfl

@[simp]
theorem rule_yyxyy {α} [DecidableEq α] (x y : FreeMagma α) :
    rule ((((y ⋆ y) ⋆ x) ⋆ y) ⋆ y) = x := by
  simp [rule]

@[equational_result]
theorem «Facts» : ∃ (G : Type) (_ : Magma G), Facts G [3143] [1629, 1832, 2644] := by
  use ConfMagma (@rule Nat _), inferInstance
  repeat' apply And.intro
  · rintro ⟨x, hx⟩ ⟨y, hy⟩
    simp [Magma.op, bu, hx, hy]
  all_goals refute

end rw3143


namespace rw3150

variable [DecidableEq α]

-- equation 3150 := x = (((y ◇ y) ◇ y) ◇ x) ◇ y
def rule : FreeMagma α → FreeMagma α
  | m@((((y1 ⋆ y2) ⋆ y3) ⋆ x) ⋆ y4) =>
      if y1 = y2 ∧ y1 = y3 ∧ y1 = y4 then
        x
      else
        m
  | m => m

instance rule_projection : IsProj (@rule α _) where
  proj := by
    intro x
    unfold rule
    split
    · split
      · right; left; right; right; rfl
      · rfl
    · rfl

@[simp]
theorem rule_yy (y : FreeMagma α) : rule (y ⋆ y) = y ⋆ y := by
  unfold rule
  split
  · rename_i m2' y1 x y2 y3 y4 heq
    simp only [Fork.injEq] at heq
    obtain ⟨heq, rfl⟩ := heq
    split
    · exfalso
      rename_i hys
      obtain ⟨rfl, rfl, rfl⟩ := hys
      have := congrArg FreeMagma.length heq
      simp [FreeMagma.length] at this
      have := FreeMagma.length_pos y1
      omega
    · simp [heq]
  · rfl

@[simp]
theorem rule_yyx {α} [DecidableEq α] (y : FreeMagma α) :
    rule ((y ⋆ y) ⋆ y) = (y ⋆ y) ⋆ y := by
  unfold rule
  split
  · rename_i m2' y1 x y2 y3 y4 heq
    simp only [Fork.injEq] at heq
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := heq
    split
    · exfalso
      rename_i hys
      obtain ⟨rfl, rfl, heq⟩ := hys
      have := congrArg FreeMagma.length heq
      simp [FreeMagma.length] at this
    · rfl
  · rfl

@[simp]
theorem rule_yyyx {α} [DecidableEq α] (x y : FreeMagma α) :
    rule (((y ⋆ y) ⋆ y) ⋆ x) = ((y ⋆ y) ⋆ y) ⋆ x := by
  unfold rule
  split
  · rename_i m2' y1 x y2 y3 y4 heq
    simp only [Fork.injEq] at heq
    obtain ⟨⟨⟨heq, rfl⟩, rfl⟩, rfl⟩ := heq
    split
    · exfalso
      rename_i hys
      obtain ⟨rfl, rfl, rfl⟩ := hys
      have := congrArg FreeMagma.length heq
      simp [FreeMagma.length] at this
    · simp [heq]
  · rfl

@[simp]
theorem rule_yyyxy {α} [DecidableEq α] (x y : FreeMagma α) :
    rule ((((y ⋆ y) ⋆ y) ⋆ x) ⋆ y) = x := by
  simp [rule]

@[equational_result]
theorem «Facts» : ∃ (G : Type) (_ : Magma G), Facts G [3150] [411, 1426, 2035] := by
  use ConfMagma (@rule Nat _), inferInstance
  repeat' apply And.intro
  · rintro ⟨x, hx⟩ ⟨y, hy⟩
    simp [Magma.op, bu, hx, hy]
  all_goals refute

end rw3150

namespace rw1110

variable [DecidableEq α]

-- equation 1110 := x = y ◇ ((y ◇ (x ◇ x)) ◇ y)
def rule : FreeMagma α → FreeMagma α
  | m@(y1 ⋆ ((y2 ⋆ (x ⋆ x1)) ⋆ y3)) =>
      if y1 = y2 ∧ y1 = y3 ∧ x = x1 then
        x
      else
        m
  | m => m

instance rule_projection : IsProj (@rule α _) where
  proj := by
    intro x
    unfold rule
    split
    · split
      · right; right; right; left; right; right; right; left; rfl
      · rfl
    · rfl

@[simp]
theorem rule_yy (y : FreeMagma α) : rule (y ⋆ y) = y ⋆ y := by
  unfold rule
  split
  · rename_i m2' y1 x y2 y3 y4 heq
    simp only [Fork.injEq] at heq
    obtain ⟨heq, rfl⟩ := heq
    split
    · exfalso
      rename_i hys
      obtain ⟨rfl, rfl, rfl⟩ := hys
      have := congrArg FreeMagma.length heq
      simp [FreeMagma.length] at this
    · simp [heq]
  · rfl

@[simp]
theorem rule_yxx {α} [DecidableEq α] (x y : FreeMagma α) :
    rule (y ⋆ (x ⋆ x)) = y ⋆ (x ⋆ x) := by
  unfold rule
  split
  · rename_i m2' y1 x y2 y3 y4 heq
    simp only [Fork.injEq] at heq
    obtain ⟨rfl, rfl, rfl⟩ := heq
    split
    · exfalso
      rename_i hys
      obtain ⟨rfl, heq, rfl⟩ := hys
      have := congrArg FreeMagma.length heq
      simp [FreeMagma.length] at this
    · rfl
  · rfl

@[simp]
theorem rule_yxxy {α} [DecidableEq α] (x y : FreeMagma α) :
    rule ((y ⋆ (x ⋆ x)) ⋆ y) = (y ⋆ (x ⋆ x)) ⋆ y:= by
  unfold rule
  split
  · rename_i m2' y1 x y2 y3 y4 heq
    simp only [Fork.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    split
    · exfalso
      rename_i hys
      obtain ⟨_, heq, rfl⟩ := hys
      have := congrArg FreeMagma.length heq
      simp [FreeMagma.length] at this
      have := FreeMagma.length_pos x
      omega
    · rfl
  · rfl

@[simp]
theorem rule_yyxxy {α} [DecidableEq α] (x y : FreeMagma α) :
    rule (y ⋆ ((y ⋆ (x ⋆ x)) ⋆ y)) = x := by
  simp [rule]

@[equational_result]
theorem «Facts» : ∃ (G : Type) (_ : Magma G), Facts G [1110] [8, 411, 1629, 1832, 3253, 3319, 3862, 3915] := by
  use ConfMagma (@rule Nat _), inferInstance
  repeat' apply And.intro
  · rintro ⟨x, hx⟩ ⟨y, hy⟩
    simp [Magma.op, bu, hx, hy]
  all_goals refute

end rw1110



open Lean.Parser.Tactic

attribute [confluence_simps] not_true_eq_false not_false_eq_true false_implies implies_true imp_false false_and and_true and_self not_and and_imp
attribute [confluence_simps] ite_eq_right_iff
attribute [confluence_simps] Option.ite_none_right_eq_some Option.some.injEq
attribute [confluence_simps] forall_apply_eq_imp_iff₂
attribute [confluence_simps] Fork.injEq

simproc [confluence_simps] confluenceReduceCtorEq (_) := reduceCtorEq

-- for some reason if I try to use Not.eq_def directly from a tactic it can't find it!
private def not_eq_def := Not.eq_def

local macro "separate" : tactic => `(tactic| (
  try intros
  try simp only [not_eq_def]
  try intros
  try injections
  try casesm* _ ∨ _, _ ∧ _, Exists _
  try any_goals
    try subst_eqs
    try trivial
))

local macro "autosplit" : tactic => `(tactic| (
  try any_goals separate
  repeat'
    split at *
    try any_goals separate
))

local macro "prove_elim" : tactic => `(tactic| (
  autosplit
  all_goals simp_all only [confluence_simps, exists_and_right, exists_eq_right_right', exists_eq_right', false_iff, not_exists, true_and]
  separate
  try simp_all only [not_true_eq_false, imp_false]
  try
    constructor
    · intro h
      subst_eqs
      repeat constructor
    · autosplit
  try any_goals
    try autosplit
    try simp_all only [not_true_eq_false, imp_false]
))

local macro "prove_elim_not" : tactic => `(tactic| (
  autosplit
  all_goals simp_all only [confluence_simps, false_iff, not_exists, not_and, true_iff, forall_eq', forall_apply_eq_imp_iff, true_iff, not_false_eq_true]
  separate
  try simp_all only [not_true_eq_false, imp_false]
  try any_goals autosplit
  try any_goals
    try simp_all only [not_true_eq_false, imp_false]
    try rename_i h
    try apply h
    try any_goals apply Eq.refl _
    try any_goals trivial
))

local syntax "subterm" : tactic

local macro_rules
| `(tactic| subterm) => `(tactic|
  first
  | apply SubtermOf.refl
  | apply SubtermOf.left
    subterm
  | apply SubtermOf.right
    subterm
)

local syntax "everywhere" " at " ident : tactic

local macro_rules
| `(tactic| everywhere at $h:ident) => `(tactic|
  first
  | assumption
  | apply Everywhere.left at $h
    everywhere at $h
  | apply Everywhere.right at $h
    everywhere at $h
)

local syntax "bufixed" : tactic

local macro_rules
| `(tactic| bufixed) => `(tactic|
  first
  | assumption
  | apply buFixed_rw_op
    all_goals bufixed
)

open Lean hiding HashMap
open Meta Elab Command Term Parser Syntax
open Std (HashMap)

local syntax (name := ruleSystem) "rule_system " ident " {" ident* " : " term "}" ("-" ident)* (ppLine "|" term "=>" term)+ : command

private partial def makePattern (inc: Nat) : Syntax → StateM (HashMap Name Nat) (TSyntax `term)
| .node info kind args => do
  pure <| TSyntax.mk <| Syntax.node info kind (← args.mapM (makePattern inc ·))
| s@(.ident _ _ name _) =>
  modifyGet (λ m ↦ match m[name]? with
  | some n => ((mkIdentFrom s (.mkSimple s!"{name}{n}")), m.insert name (n + inc))
  | _ => (TSyntax.mk s, m))
| s@_ => pure <| TSyntax.mk s

private partial def countVars : Syntax → StateM (HashMap Name Nat) Unit
| .node _ _ args => args.forM countVars
| .ident _ _ name _ => modify (λ m ↦ match m[name]? with
  | some n => m.insert name (n + 1)
  | _ => m)
| _ => pure ()

macro_rules
| `(command| rule_system $system:ident {$vars:ident* : $type:term} $[-$disable:ident]* $[| $lhs:term => $rhs:term]*) => do
  let mut decls := #[]

  let mut ruleIdents := #[]
  let mut ruleElims := #[]
  let mut ruleElimNots := #[]
  let mut ruleUsedVars := #[]

  let systemName := system.getId
  let numRules := lhs.size

  for idx in [:numRules] do
    let lhs := TSyntax.mk <| lhs[idx]!
    let rhs := TSyntax.mk <| rhs[idx]!
    let mut varSet := Std.HashMap.empty
    for var in vars do
      varSet := varSet.insert var.getId 0
    let (_, varCounts) := StateT.run (countVars lhs) varSet

    let mut varIdx := Std.HashMap.empty
    for (name, count) in varCounts do
      if count > 1 then
        varIdx := varIdx.insert name 1

    let (lhsP, _) := StateT.run (makePattern 1 lhs) varIdx
    let (rhsP, _) := StateT.run (makePattern 0 rhs) varIdx

    let mut cond := none
    for var in vars.reverse do
      let varName := var.getId
      for n in (List.range <| (varCounts.getD varName 0) - 1).reverse do
        let id1 := Lean.mkIdent <| .mkSimple s!"{varName}{n + 1}"
        let id2 := Lean.mkIdent <| .mkSimple s!"{varName}{n + 2}"
        let eq := mkCApp `Eq #[id1, id2]
        cond := some <| match cond with
        | none => eq
        | some e => mkCApp `And #[eq, e]

    let rhsP ← match cond with
    | some cond' => `(if $cond' then some $rhsP else none)
    | none => `(some $rhsP)

    let ruleName := .str systemName s!"rule{idx+1}"
    let ruleId := Lean.mkIdent ruleName
    ruleIdents := ruleIdents.push ruleId
    decls := decls.push <| ← `(
      set_option linter.unusedVariables false in
      def $ruleId : $type → Option ($type)
      | $lhsP => $rhsP
      | _ => none
    )

    let usedVars := vars.filter (λ v ↦ varCounts.getD (v.getId) 0 > 0)
    ruleUsedVars := ruleUsedVars.push usedVars

    let elim := Lean.mkIdent <| .str (ruleName) "elim"
    ruleElims := ruleElims.push elim
    decls := decls.push <| ← `(
      def $elim (e r: $type): $ruleId e = some r ↔
          ∃ $[$usedVars:ident]*, e = $lhs ∧ r = $rhs := by
        simp only [$ruleId:ident]
        prove_elim
    )

    let elimNot := Lean.mkIdent <| .str (ruleName) "elim_not"
    ruleElimNots := ruleElimNots.push elimNot
    decls := decls.push <| ← `(
      def $elimNot (e: $type): $ruleId e = none ↔
        ¬∃ $[$usedVars:ident]*, e = $lhs := by
        simp only [$ruleId:ident]
        prove_elim_not
    )

  let mut ruleEqs := #[]
  let mut body := ← `(x)
  for inner in (List.range numRules).reverse do
    body := (← `(
      match $(ruleIdents[inner]!):ident x with
      | some x => x
      | none => $body
    ))

  decls := decls.push <| ← `(
    def $system (x: $type): $type :=
      $body
  )

  for idx in [:numRules] do
    let eq := Lean.mkIdent <| .str systemName s!"eq{idx+1}"
    ruleEqs := ruleEqs.push eq
    decls := decls.push <| ← `(
      def $eq ($(ruleUsedVars[idx]!)*: $type):
        $system $(TSyntax.mk <| lhs[idx]!):term = $(TSyntax.mk <| rhs[idx]!):term := by
        simp only [$system:ident, $[$ruleIdents:ident],*, and_self, ↓reduceIte]
        autosplit
    )

  let or := (← ruleIdents.mapM (λ n ↦ `($n e = some r))).foldr (init := none) λ
  | x, some s => mkCApp `Or #[x, s]
  | x, none => x

  let andNot := (← ruleIdents.mapM (λ n ↦ `($n e = none))).foldr (init := none) λ
  | x, some s => mkCApp `And #[x, s]
  | x, none => x

  let elim' := Lean.mkIdent <| .str systemName "elim'"
  let cases ← (ruleElims.zip ruleEqs).mapM (λ (l1, l2) ↦ `(tactic| · simp_all only [$l1:ident]; separate; simp_all only [$l2:ident]))
  decls := decls.push <| ← `(
    def $elim' (e r: $type): $system e = r ↔
        $(or.get!) ∨ (e = r ∧ $(andNot.get!)) := by
      constructor
      · intro h
        simp only [$system:ident] at h
        autosplit
        all_goals simp_all only [or_self, and_self, or_true, true_or, and_true, true_and]
      · intro h
        separate
        $[$cases];*
        simp_all only [$system:ident]
  )

  let elim := Lean.mkIdent <| .str systemName "elim"
  decls := decls.push <| ← `(
    def $elim (e r: $type) := by
      simpa only [$[$ruleElims:ident],*, $[$ruleElimNots:ident],*] using $elim' e r
  )

  if ¬disable.any (·.getId == `IsProj) then
    let instIsProj := Lean.mkIdent <| .str systemName "instIsProj"
    decls := decls.push <| ← `(
      instance $instIsProj:ident : IsProj ($system : $type → $type) where
        proj := by
          intro x
          simp only [$system:ident, $[$ruleIdents:ident],*]
          autosplit
          all_goals subterm
    )

  pure <| mkListNode decls

namespace rw680

variable [DecidableEq α]

rule_system rules {x y: FreeMagma α}
| (x ⋆ (y ⋆ ((x ⋆ x) ⋆ x))) => y
| (((x ⋆ x) ⋆ x) ⋆ (((x ⋆ x) ⋆ x) ⋆ ((x ⋆ x) ⋆ x))) => x

theorem comp1_2 {x y : FreeMagma α}:
    rules (y ⋆ rules (x ⋆ (y ⋆ y ⋆ y))) = x := by
  generalize h: rules (x ⋆ (y ⋆ y ⋆ y)) = e
  simp only [rules.elim] at h
  separate
  · apply rules.eq2
  · apply rules.eq1

theorem comp1_3 {x y : FreeMagma α}:
    rules (y ⋆ rules (x ⋆ rules (y ⋆ y ⋆ y))) = x := by
  generalize h: rules (y ⋆ y ⋆ y) = e
  simp only [rules.elim] at h
  separate
  apply comp1_2

theorem comp1_4 {x y : FreeMagma α}:
    rules (y ⋆ rules (x ⋆ rules (rules (y ⋆ y) ⋆ y))) = x := by
  generalize h: rules (y ⋆ y) = e
  simp only [rules.elim] at h
  separate
  apply comp1_3

@[equational_result]
theorem «Facts» :
  ∃ (G : Type) (_ : Magma G), Facts G [680] [1629, 1695, 1832, 2847, 2947] := by
  use ConfMagma (@rules Nat _), inferInstance
  repeat' apply And.intro
  · rintro ⟨x, hx⟩ ⟨y, hy⟩
    simp (disch := bufixed) only [Magma.op, bu, hx, hy, buFixed_rw_op]
    symm
    congr! 1
    apply comp1_4
  all_goals refute

end rw680

namespace rw1443

variable [DecidableEq α]

rule_system rules {x y z: FreeMagma α}
| ((x ⋆ y) ⋆ (x ⋆ (x ⋆ z))) => x
| (x ⋆ ((x ⋆ y) ⋆ x)) => (x ⋆ y)
| (x ⋆ ((x ⋆ y) ⋆ ((x ⋆ y) ⋆ z))) => (x ⋆ y)
| (((x ⋆ y) ⋆ z) ⋆ ((x ⋆ y) ⋆ x)) => (x ⋆ y)

theorem comp1_2 {x y z : FreeMagma α}:
    rules (rules (x ⋆ y) ⋆ (x ⋆ (x ⋆ z))) = x := by
  generalize h: rules (x ⋆ y) = e
  simp only [rules.elim] at h
  separate
  · apply rules.eq3
  · apply rules.eq1
  · apply rules.eq1
  · apply rules.eq3
  · apply rules.eq1

theorem comp1_3 {x y z : FreeMagma α}:
    rules (rules (x ⋆ y) ⋆ rules (x ⋆ (x ⋆ z))) = x := by
  generalize h: rules (x ⋆ (x ⋆ z)) = e
  simp only [rules.elim] at h
  separate
  · apply comp1_2

theorem comp4_2 {x y z : FreeMagma α}:
    rules (rules (x ⋆ y ⋆ z) ⋆ (x ⋆ y ⋆ x)) = x ⋆ y := by
  generalize h: rules (x ⋆ y ⋆ z) = e
  simp only [rules.elim] at h
  separate
  · apply rules.eq2
  · apply rules.eq4
  · apply rules.eq4
  · apply rules.eq2
  · apply rules.eq4

theorem comp4_3 {x y z : FreeMagma α}:
    rules (rules (x ⋆ y ⋆ z) ⋆ rules (x ⋆ y ⋆ x)) = x ⋆ y := by
  generalize h: rules (x ⋆ y ⋆ x) = e
  simp only [rules.elim] at h
  separate
  apply comp4_2

theorem comp1_4 {x y z : FreeMagma α}:
    rules (rules (x ⋆ y) ⋆ rules (x ⋆ rules (x ⋆ z))) = x := by
  generalize h: rules (x ⋆ z) = e
  simp only [rules.elim] at h
  separate
  · apply comp4_3
  · apply comp1_3
  · apply comp1_3
  · apply comp4_3
  · apply comp1_3

@[equational_result]
theorem «Facts» :
  ∃ (G : Type) (_ : Magma G), Facts G [1443] [23, 1629, 1630, 2441, 3050, 3055, 3522, 4065, 4067, 4118, 4268, 4282] := by
  use ConfMagma (@rules Nat _), inferInstance
  repeat' apply And.intro
  · rintro ⟨x, hx⟩ ⟨y, hy⟩ ⟨z, hz⟩
    simp (disch := bufixed) only [Magma.op, bu, hx, hy, hz, buFixed_rw_op]
    symm
    congr! 1
    apply comp1_4
  all_goals refute

end rw1443

namespace rw481

variable [Inhabited α] [DecidableEq α]

rule_system rules {x y z: FreeMagma α} -IsProj
| y ⋆ (x ⋆ (y ⋆ (z ⋆ z))) => x
| (z ⋆ z) ⋆ (x ⋆ (z ⋆ z)) => x
| x ⋆ x => default ⋆ default

instance: IsProjOrNF (rules : FreeMagma α → _) where
  proj_or_nf := by
    intro x
    generalize h: rules x = e
    simp only [rules.elim] at h
    separate
    · left
      subterm
    · left
      subterm
    · right
      simp [NF, Everywhere]
      constructor
      · simp [rules, rules.rule1, rules.rule2, rules.rule3]
      · apply rules.eq3
    · left
      rfl

theorem comp1_2 {x y : FreeMagma α} (hx: NF rules x):
    rules (y ⋆ rules (x ⋆ (y ⋆ (default ⋆ default)))) = x := by
  generalize h: rules (x ⋆ (y ⋆ (default ⋆ default))) = e
  simp only [rules.elim] at h
  separate
  · apply rules.eq3
  · apply hx.top
  · apply rules.eq1

theorem comp2_2 {x : FreeMagma α} (hx: NF rules x):
    rules (default ⋆ default ⋆ rules (x ⋆ (default ⋆ default))) = x := by
  generalize h: rules (x ⋆ (default ⋆ default)) = e
  simp only [rules.elim] at h
  separate
  · apply rules.eq3
  · apply rules.eq2

theorem comp1_3 {x y : FreeMagma α} (hx: NF rules x):
    rules (y ⋆ rules (x ⋆ rules (y ⋆ (default ⋆ default)))) = x := by
  generalize h: rules (y ⋆ (default ⋆ default)) = e
  simp only [rules.elim] at h
  separate
  · apply comp2_2 hx
  · apply comp1_2 hx

theorem comp1_4 {x y z : FreeMagma α} (hx: NF rules x):
    rules (y ⋆ rules (x ⋆ rules (y ⋆ rules (z ⋆ z)))) = x := by
  generalize h: rules (z ⋆ z) = e
  simp only [rules.elim] at h
  separate
  · apply comp1_3 hx
  · exfalso
    simp_all only [Fork.injEq, not_exists, not_and, exists_eq', not_true_eq_false]

@[equational_result]
theorem «Facts» :
  ∃ (G : Type) (_ : Magma G), Facts G [481] [1488, 1492, 1496, 2035, 2038, 2041, 2124, 2128, 2132, 2135, 3050, 3056, 3139, 3150, 3161] := by
  use ConfMagma (@rules Nat _ _), inferInstance
  repeat' apply And.intro
  · rintro ⟨x, hx⟩ ⟨y, hy⟩ ⟨z, hz⟩
    simp (disch := bufixed) only [Magma.op, bu, hx, hy, hz, buFixed_rw_op]
    symm
    congr! 1
    apply comp1_4 ((NF_iff_buFixed rules).mpr hx)
  all_goals refute

end rw481

namespace rw2126

variable [DecidableEq α]

rule_system rules {x y z w: FreeMagma α}
| y ⋆ y ⋆ x ⋆ (x ⋆ z) => x
| x ⋆ x ⋆ (x ⋆ x ⋆ y ⋆ z) => x ⋆ x ⋆ y
| x ⋆ x ⋆ (y ⋆ y ⋆ z) ⋆ z => y ⋆ y ⋆ z
| (x ⋆ x ⋆ y) ⋆ (x ⋆ x ⋆ y ⋆ z ⋆ w) => x ⋆ x ⋆ y ⋆ z

theorem comp1_2 {x y z : FreeMagma α}:
    rules (y ⋆ y ⋆ x ⋆ rules (x ⋆ z)) = x := by
  generalize h: rules (x ⋆ z) = e
  simp only [rules.elim] at h
  separate
  · apply rules.eq3
  · apply rules.eq1
  · apply rules.eq3
  · apply rules.eq1
  · apply rules.eq1

theorem comp2_2 {x y z : FreeMagma α} (hxxy: NF rules (x ⋆ x ⋆ y)):
    rules (x ⋆ x ⋆ rules (x ⋆ x ⋆ y ⋆ z)) = x ⋆ x ⋆ y := by
  generalize h: rules (x ⋆ x ⋆ y ⋆ z) = e
  simp only [rules.elim] at h
  separate
  · apply hxxy.top
  · apply rules.eq2
  · apply hxxy.top
  · apply rules.eq2
  · apply rules.eq2

theorem comp4_2 {x y z w : FreeMagma α} (hxxyz: NF rules (x ⋆ x ⋆ y ⋆ z)):
    rules (((x ⋆ x) ⋆ y) ⋆ rules ((((x ⋆ x) ⋆ y) ⋆ z) ⋆ w)) = (((x ⋆ x) ⋆ y) ⋆ z) := by
  generalize h: rules ((((x ⋆ x) ⋆ y) ⋆ z) ⋆ w) = e
  simp only [rules.elim] at h
  separate
  · apply hxxyz.top
  · apply rules.eq4
  · apply hxxyz.top
  · apply rules.eq2
  · apply rules.eq4

theorem comp1_3 {x y z : FreeMagma α} (hx: NF rules x):
    rules (rules (y ⋆ y ⋆ x) ⋆ rules (x ⋆ z)) = x := by
  generalize h: rules (y ⋆ y ⋆ x) = e
  simp only [rules.elim] at h
  separate
  · apply comp2_2 hx
  · apply comp4_2 hx
  · apply comp1_2
  · apply comp4_2 hx
  · apply comp1_2

theorem comp1_4 {x y z : FreeMagma α} (hx: NF rules x):
    rules (rules (rules (y ⋆ y) ⋆ x) ⋆ rules (x ⋆ z)) = x := by
  generalize h: rules (y ⋆ y) = e
  simp only [rules.elim] at h
  separate
  all_goals apply comp1_3 hx

@[equational_result]
theorem «Facts» :
  ∃ (G : Type) (_ : Magma G), Facts G [2126] [151, 152, 167, 168, 1426, 1427, 1428, 1429, 1430, 1478, 1479, 1480, 1481, 1482, 1483, 1484, 1485, 1486, 2050, 2051, 2052, 2087, 2088, 2089, 2161, 2162, 2163, 3456, 3457, 3511, 3512, 3513, 3862, 3877, 3918, 3955, 3993] := by
  use ConfMagma (@rules Nat _), inferInstance
  repeat' apply And.intro
  · rintro ⟨x, hx⟩ ⟨y, hy⟩ ⟨z, hz⟩
    simp only [Magma.op, bu, hx, hy, hz, buFixed_rw_op]
    symm
    congr! 1
    apply comp1_4 ((NF_iff_buFixed rules).mpr hx)
  all_goals refute

end rw2126

namespace rw115

variable [DecidableEq α]

rule_system rules {x y: FreeMagma α}
| y ⋆ ((x ⋆ x) ⋆ y) => x
| ((y ⋆ y) ⋆ (x ⋆ x)) ⋆ y => x

theorem comp2 {x y : FreeMagma α} (hx: NF rules x):
    rules (y ⋆ rules (x ⋆ x ⋆ y)) = x := by
  generalize h: rules (x ⋆ x ⋆ y) = e
  simp only [rules.elim] at h
  separate
  · apply rules.eq2
  · apply rw_eq_self_of_NF rules hx
  · apply rules.eq1

theorem comp3 {x y : FreeMagma α} (hx: NF rules x):
    rules (y ⋆ rules (rules (x ⋆ x) ⋆ y)) = x := by
  generalize h: rules (x ⋆ x) = e
  simp only [rules.elim] at h
  separate
  exact comp2 hx

@[equational_result]
theorem «Facts» :
  ∃ (G : Type) (_ : Magma G), Facts G [115] [2707, 4273, 4332] := by
  use ConfMagma (@rules Nat _), inferInstance
  repeat' apply And.intro
  · rintro ⟨x, hx⟩ ⟨y, hy⟩
    simp only [Magma.op, bu, hx, hy, buFixed_rw_op]
    symm
    congr! 1
    apply comp3 ((NF_iff_buFixed rules).mpr hx)
  all_goals refute

end rw115

namespace rw3588

variable [DecidableEq α]

rule_system rules {x y z w: FreeMagma α}
| z ⋆ ((x ⋆ y) ⋆ z) => x ⋆ y
| ((z ⋆ w) ⋆ (x ⋆ y)) ⋆ (z ⋆ w) => x ⋆ y

theorem comp2 {x y z : FreeMagma α} (hxy: NF rules (x ⋆ y)):
    rules (z ⋆ rules (x ⋆ y ⋆ z)) = x ⋆ y := by
  generalize h: rules (x ⋆ y ⋆ z) = e
  simp only [rules.elim] at h
  separate
  · apply rules.eq2
  · apply rw_eq_self_of_NF rules hxy
  · apply rules.eq1

theorem comp3 {x y z : FreeMagma α} (hx: NF rules x) (hy: NF rules y):
    rules (z ⋆ rules (rules (x ⋆ y) ⋆ z)) = rules (x ⋆ y) := by
  generalize h: rules (x ⋆ y) = e
  simp only [rules.elim] at h
  separate
  all_goals apply comp2
  · apply Everywhere.left hy
  · apply Everywhere.right hx
  · rw [NF, Everywhere]
    refine ⟨hx, hy, ?_⟩
    simp only [rules.elim]
    right
    constructorm* _ ∧ _
    all_goals trivial

@[equational_result]
theorem «Facts» :
  ∃ (G : Type) (_ : Magma G), Facts G [3588] [3862, 3878, 3917, 3955] := by
  use ConfMagma (@rules Nat _), inferInstance
  repeat' apply And.intro
  · rintro ⟨x, hx⟩ ⟨y, hy⟩ ⟨z, hz⟩
    simp only [Magma.op, bu, hx, hy, hz, buFixed_rw_op]
    symm
    congr! 1
    apply comp3 ((NF_iff_buFixed rules).mpr hx) ((NF_iff_buFixed rules).mpr hy)
  all_goals refute

end rw3588

namespace rw1086

variable [DecidableEq α]

-- equation 1086 := x = y ◇ ((x ◇ (y ◇ y)) ◇ y)
def rule : FreeMagma α → FreeMagma α
  | m@(y1 ⋆ ((x ⋆ (y2 ⋆ y3)) ⋆ y4)) =>
      if y1 = y2 ∧ y1 = y3 ∧ y1 = y4 then
        x
      else
        m
  | m => m

instance rule_projection : IsProj (@rule α _) where
  proj := by
    intro x
    unfold rule
    split
    · split
      · right; right; right; left; right; left; rfl
      · rfl
    · rfl

@[simp]
theorem rule_yy (y : FreeMagma α) : rule (y ⋆ y) = y ⋆ y := by
  unfold rule
  split
  · rename_i m2' y1 x y2 y3 y4 heq
    simp only [Fork.injEq] at heq
    obtain ⟨heq, rfl⟩ := heq
    split
    · exfalso
      rename_i hys
      obtain ⟨rfl, rfl, rfl⟩ := hys
      have := congrArg FreeMagma.length heq
      simp [FreeMagma.length] at this
    · simp [heq]
  · rfl

@[simp]
theorem rule_xyy {α} [DecidableEq α] (x y : FreeMagma α) :
    rule (x ⋆ (y ⋆ y)) = x ⋆ (y ⋆ y) := by
  unfold rule
  split
  · rename_i m2' y1 x y2 y3 y4 heq
    simp only [Fork.injEq] at heq
    obtain ⟨rfl, rfl, rfl⟩ := heq
    split
    · exfalso
      rename_i hys
      obtain ⟨rfl, rfl, heq⟩ := hys
      have := congrArg FreeMagma.length heq
      simp [FreeMagma.length] at this
      have := FreeMagma.length_pos x
      omega
    · rfl
  · rfl

@[simp]
theorem rule_xyyy {α} [DecidableEq α] (x y : FreeMagma α) :
    rule ((x ⋆ (y ⋆ y)) ⋆ y) = (x ⋆ (y ⋆ y)) ⋆ y:= by
  unfold rule
  split
  · rename_i m2' y1 x y2 y3 y4 heq
    simp only [Fork.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    split
    · exfalso
      rename_i hys
      obtain ⟨heq, _, _⟩ := hys
      have := congrArg FreeMagma.length heq
      simp [FreeMagma.length] at this
      have := FreeMagma.length_pos x
      omega
    · rfl
  · rfl

@[simp]
theorem rule_yxyyy {α} [DecidableEq α] (x y : FreeMagma α) :
    rule (y ⋆ ((x ⋆ (y ⋆ y)) ⋆ y)) = x := by
  simp [rule]

@[equational_result]
theorem «Facts» : ∃ (G : Type) (_ : Magma G), Facts G [1086] [1832, 1898, 2644, 2710] := by
  use ConfMagma (@rule Nat _), inferInstance
  repeat' apply And.intro
  · rintro ⟨x, hx⟩ ⟨y, hy⟩
    simp [Magma.op, bu, hx, hy]
  all_goals refute

end rw1086

namespace rw2497

variable [DecidableEq α]

-- equation 2497 := x = (y ◇ ((x ◇ x) ◇ y)) ◇ y
def rule : FreeMagma α → FreeMagma α
  | m@((y1 ⋆ (((x ⋆ x1) ⋆ y2))) ⋆ y3) =>
      if y1 = y2 ∧ y1 = y3 ∧ x = x1 then
        x
      else
        m
  | m => m

instance rule_projection : IsProj (@rule α _) where
  proj := by
    intro x
    unfold rule
    split
    · split
      · right; left; right; right; right; left; right; left; rfl
      · rfl
    · rfl

@[simp]
theorem rule_xx (x : FreeMagma α) : rule (x ⋆ x) = x ⋆ x := by
  unfold rule
  split
  · rename_i m2' y1 x y2 y3 y4 heq
    simp only [Fork.injEq] at heq
    obtain ⟨heq, rfl⟩ := heq
    split
    · exfalso
      rename_i hys
      obtain ⟨rfl, rfl, rfl⟩ := hys
      have := congrArg FreeMagma.length heq
      simp [FreeMagma.length] at this
    · simp [heq]
  · rfl

@[simp]
theorem rule_xxy {α} [DecidableEq α] (x y : FreeMagma α) :
    rule ((x ⋆ x) ⋆ y) = (x ⋆ x) ⋆ y := by
  unfold rule
  split
  · rename_i m2' y1 x y2 y3 y4 heq
    simp only [Fork.injEq] at heq
    obtain ⟨⟨rfl, heq⟩, rfl⟩ := heq
    split
    · exfalso
      rename_i hys
      obtain ⟨heq2, _, _⟩ := hys
      rw [heq2] at heq
      have := congrArg FreeMagma.length heq
      simp [FreeMagma.length] at this
    · simp [heq]
  · rfl

@[simp]
theorem rule_yxxy {α} [DecidableEq α] (x y : FreeMagma α) :
    rule (y ⋆ ((x ⋆ x) ⋆ y)) = (y ⋆ ((x ⋆ x) ⋆ y)) := by
  unfold rule
  split
  · rename_i m2' y1 x y2 y3 y4 heq
    simp only [Fork.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    split
    · exfalso
      rename_i hys
      obtain ⟨rfl, heq, _⟩ := hys
      have := congrArg FreeMagma.length heq
      simp [FreeMagma.length] at this
      have := FreeMagma.length_pos x
      omega
    · rfl
  · rfl

@[simp]
theorem rule_yxxyy {α} [DecidableEq α] (x y : FreeMagma α) :
    rule ((y ⋆ ((x ⋆ x) ⋆ y)) ⋆ y) = x := by
  simp [rule]

@[equational_result]
theorem «Facts» : ∃ (G : Type) (_ : Magma G), Facts G [2497] [23, 1629, 1832, 3050, 3456, 3522, 4065, 4118] := by
  use ConfMagma (@rule Nat _), inferInstance
  repeat' apply And.intro
  · rintro ⟨x, hx⟩ ⟨y, hy⟩
    simp [Magma.op, bu, hx, hy]
  all_goals refute

end rw2497

namespace rw2541

variable [DecidableEq α]

-- equation 2541 := x = (y ◇ ((y ◇ y) ◇ x)) ◇ y
def rule : FreeMagma α → FreeMagma α
  | m@((y1 ⋆ (((y2 ⋆ y3) ⋆ x))) ⋆ y4) =>
      if y1 = y2 ∧ y1 = y3 ∧ y1 = y4 then
        x
      else
        m
  | m => m

instance rule_projection : IsProj (@rule α _) where
  proj := by
    intro x
    unfold rule
    split
    · split
      · right; left; right; right; right; right; rfl
      · rfl
    · rfl

@[simp]
theorem rule_yy (y : FreeMagma α) : rule (y ⋆ y) = y ⋆ y := by
  unfold rule
  split
  · rename_i m2' y1 x y2 y3 y4 heq
    simp only [Fork.injEq] at heq
    obtain ⟨heq, rfl⟩ := heq
    split
    · exfalso
      rename_i hys
      obtain ⟨rfl, rfl, rfl⟩ := hys
      have := congrArg FreeMagma.length heq
      simp [FreeMagma.length] at this
    · simp [heq]
  · rfl

@[simp]
theorem rule_yyx {α} [DecidableEq α] (x y : FreeMagma α) :
    rule ((y ⋆ y) ⋆ x) = (y ⋆ y) ⋆ x := by
  unfold rule
  split
  · rename_i m2' y1 x y2 y3 y4 heq
    simp only [Fork.injEq] at heq
    obtain ⟨⟨rfl, heq⟩, rfl⟩ := heq
    split
    · exfalso
      rename_i hys
      obtain ⟨rfl, _, _⟩ := hys
      have := congrArg FreeMagma.length heq
      simp [FreeMagma.length] at this
      have := FreeMagma.length_pos y2
      omega
    · simp [heq]
  · rfl

@[simp]
theorem rule_yyyx {α} [DecidableEq α] (x y : FreeMagma α) :
    rule (y ⋆ ((y ⋆ y) ⋆ x)) = (y ⋆ ((y ⋆ y) ⋆ x)) := by
  unfold rule
  split
  · rename_i m2' y1 x y2 y3 y4 heq
    simp only [Fork.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    split
    · exfalso
      rename_i hys
      obtain ⟨_, _, heq⟩ := hys
      have := congrArg FreeMagma.length heq
      simp [FreeMagma.length] at this
      have := FreeMagma.length_pos x
      omega
    · rfl
  · rfl

@[simp]
theorem rule_yyyxy {α} [DecidableEq α] (x y : FreeMagma α) :
    rule ((y ⋆ ((y ⋆ y) ⋆ x)) ⋆ y) = x := by
  simp [rule]

@[equational_result]
theorem «Facts» : ∃ (G : Type) (_ : Magma G), Facts G [2541] [817, 917, 1629, 1729] := by
  use ConfMagma (@rule Nat _), inferInstance
  repeat' apply And.intro
  · rintro ⟨x, hx⟩ ⟨y, hy⟩
    simp [Magma.op, bu, hx, hy]
  all_goals refute

end rw2541

end Confluence
