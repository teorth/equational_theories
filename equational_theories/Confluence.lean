import equational_theories.ConfluenceAttr
import equational_theories.FreeMagma
import equational_theories.AllEquations
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

variable [hproj: IsProj rw]

theorem bu_nf : ∀ x, NF rw (bu rw x) := by
  intro x
  induction x with
  | Leaf => simp [NF, bu, Everywhere]
  | Fork x y ihx ihy =>
    simp only [NF, bu]
    have hsub := hproj.proj (bu rw x ⋆ bu rw y)
    obtain (heq | hsub | hsub) := hsub
    · refine everywhere_of_projection_of_everywhere _ _ _ ⟨ihx, ihy, ?_⟩
      simp [bu, Everywhere, *, ihx.top, ihy.top]
    · exact everywhere_of_subterm_of_everywhere ihx hsub
    · exact everywhere_of_subterm_of_everywhere ihy hsub

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
    first | (use (0 : Nat); decide)
          | (use (0 : Nat), (1 : Nat); decide)
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
attribute [confluence_simps] Option.or Option.getD Option.ite_none_right_eq_some Option.some.injEq
attribute [confluence_simps] forall_apply_eq_imp_iff₂
attribute [confluence_simps] Fork.injEq

simproc [confluence_simps] confluenceReduceCtorEq (_) := reduceCtorEq

local macro "separate" : tactic => `(tactic| (
  try intros
  try repeat
    simp only [Not.eq_1]
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
  all_goals simp_all only [confluence_simps, exists_and_right, exists_eq_right_right', exists_eq_right', false_iff, not_exists]
  constructor
  · intro h
    subst_eqs
    repeat constructor
  · autosplit
))

local macro "prove_elim_not" : tactic => `(tactic| (
  autosplit
  all_goals simp_all only [confluence_simps, false_iff, not_exists, not_and, true_iff, forall_eq', forall_apply_eq_imp_iff, true_iff, not_false_eq_true]
  try separate
  rename_i h
  rw [eq_comm]
  apply h
  try trivial
))

local macro "compute" lemmus:simpLemma : tactic => `(tactic| (
  simp only [$lemmus, ↓reduceIte, and_self]
))

namespace rw3588

variable [DecidableEq α]

-- equation 3588 := x ◇ y = z ◇ ((x ◇ y) ◇ z)
def rule1 : FreeMagma α → Option (FreeMagma α)
  | z1 ⋆ ((x ⋆ y) ⋆ z2) =>
    if z1 = z2 then
      x ⋆ y
    else
      none
  | _ => none

-- generated by Knuth-Bendix completion with Vampire or kbcv
def rule2 : FreeMagma α → Option (FreeMagma α)
  | ((z1 ⋆ w1) ⋆ (x ⋆ y)) ⋆ (z2 ⋆ w2) =>
    if z1 = z2 ∧ w1 = w2 then
      x ⋆ y
    else
      none
  | _ => none

def rule (x: FreeMagma α): FreeMagma α :=
  ((rule1 x).or (rule2 x)).getD x

def rule_eq_rule21' (x: FreeMagma α):
  rule x = ((rule2 x).or (rule1 x)).getD x := by
  simp only [rule, Option.or, Option.getD]
  autosplit
  any_goals simp_all only [Option.some.injEq]
  exfalso
  simp_all only [rule1, rule2]
  autosplit

def rule_eq_rule12 (x: FreeMagma α) := by
  simpa [rule1, rule2, Option.or, Option.getD] using rule.eq_def x

def rule_eq_rule21 {x: FreeMagma α} := by
  simpa [rule1, rule2, Option.or, Option.getD] using rule_eq_rule21' x

def rule2.elim (e r: FreeMagma α): rule2 e = some r ↔
  ∃ x y z w, e = ((z ⋆ w) ⋆ (x ⋆ y)) ⋆ (z ⋆ w) ∧ r = x ⋆ y := by
  simp only [rule2]
  prove_elim

def rule2.elim_not (e: FreeMagma α): rule2 e = none ↔
  ¬∃ x y z w, e = ((z ⋆ w) ⋆ (x ⋆ y)) ⋆ (z ⋆ w) := by
  simp only [rule2]
  prove_elim_not

def rule1.elim (e r: FreeMagma α): rule1 e = some r ↔
  ∃ x y z, e = z ⋆ ((x ⋆ y) ⋆ z) ∧ r = x ⋆ y := by
  simp only [rule1]
  prove_elim

def rule1.elim_not (e: FreeMagma α): rule1 e = none ↔
  ¬∃ x y z, e = z ⋆ ((x ⋆ y) ⋆ z) := by
  simp only [rule1]
  prove_elim_not

def rule.elim' (x y: FreeMagma α): rule x = y ↔
  rule1 x = some y ∨ rule2 x = some y ∨ (x = y ∧ rule1 x = none ∧ rule2 x = none) := by
  constructor
  · intro h
    simp only [rule, Option.or, Option.getD] at h
    autosplit
    all_goals simp_all
  · intro h
    rcases h with h1 | h2 | ⟨h0, h1, h2⟩
    next h1 => simp only [rule, h1, Option.or, Option.getD]
    next h2 => simp only [rule_eq_rule21', h2, Option.or, Option.getD]
    next h' => simp only [rule, ← h0, h1, h2, Option.or, Option.getD]

def rule.elim (e r: FreeMagma α) := by
  simpa only [rule1.elim, rule2.elim, rule1.elim_not, rule2.elim_not] using rule.elim' e r

instance rule_projection : IsProj (@rule α _) where
  proj := by
    intro x
    simp only [rule, rule1, rule2, Option.or, Option.getD]
    autosplit
    · apply SubtermOf.right
      apply SubtermOf.left
      rfl
    · apply SubtermOf.left
      apply SubtermOf.right
      rfl
    · apply SubtermOf.left
      apply SubtermOf.right
      rfl

theorem comp1 {α} [DecidableEq α] {x y z : FreeMagma α}:
    rule (z ⋆ (x ⋆ y ⋆ z)) = x ⋆ y := by
  compute rule_eq_rule12

theorem comp2 {α} [DecidableEq α] {x y z : FreeMagma α} (hxy: NF rule (x ⋆ y)):
    rule (z ⋆ rule (x ⋆ y ⋆ z)) = x ⋆ y := by
  generalize h: rule (x ⋆ y ⋆ z) = e
  simp only [rule.elim] at h
  separate
  · compute rule_eq_rule21
  · apply rw_eq_self_of_NF rule hxy
  · exact comp1

theorem comp3 {α} [DecidableEq α] {x y z : FreeMagma α} (hx: NF rule x) (hy: NF rule y):
    rule (z ⋆ rule (rule (x ⋆ y) ⋆ z)) = rule (x ⋆ y) := by
  generalize h: rule (x ⋆ y) = e
  simp only [rule.elim] at h
  separate
  all_goals apply comp2
  · apply Everywhere.left hy
  · apply Everywhere.right hx
  · rw [NF, Everywhere]
    refine ⟨hx, hy, ?_⟩
    simp only [rule.elim]
    right
    right
    constructorm* _ ∧ _
    all_goals trivial

@[equational_result]
theorem «Facts» :
  ∃ (G : Type) (_ : Magma G), Facts G [3588] [3862, 3878, 3917, 3955] := by
  use ConfMagma (@rule Nat _), inferInstance
  repeat' apply And.intro
  · rintro ⟨x, hx⟩ ⟨y, hy⟩ ⟨z, hz⟩
    simp only [Magma.op, bu, hx, hy, hz, buFixed_rw_op]
    symm
    congr! 1
    apply comp3 ((NF_iff_buFixed rule).mpr hx) ((NF_iff_buFixed rule).mpr hy)
  all_goals refute

end rw3588

end Confluence
