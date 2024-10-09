import equational_theories.FreeMagma
import equational_theories.AllEquations
import equational_theories.FactsSyntax

namespace FreeMagma

variable {α : Type}

def Everywhere (P : FreeMagma α → Prop) : FreeMagma α → Prop
  | .Leaf x => P (.Leaf x)
  | x ⋆ y => x.Everywhere P ∧ y.Everywhere P ∧ P (x ⋆ y)

theorem Everywhere.top {P : FreeMagma α → Prop} : {x : FreeMagma α} → Everywhere P x → P x
  | .Leaf _ => fun h => h
  | _ ⋆ _ => fun h => h.2.2

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

class IsProj (rw : FreeMagma α → FreeMagma α) : Prop where
  proj : ∀ x, SubtermOf (rw x) x

theorem everywhere_of_projection_of_everywhere
    (rw : FreeMagma α → FreeMagma α) [IsProj rw] P :
    ∀ x, Everywhere P x → (rw x).Everywhere P :=
  fun x he ↦ everywhere_of_subterm_of_everywhere he (IsProj.proj x)

theorem projection_everywhere
    (rw : FreeMagma α → FreeMagma α) [IsProj rw] P :
    ∀ x, Everywhere P x → P (rw x) :=
  fun x he ↦ subterm_everywhere he (IsProj.proj x)

end FreeMagma

namespace Confluence

open FreeMagma

variable {α : Type}

variable (rw : FreeMagma α → FreeMagma α)

def bu : FreeMagma α → FreeMagma α
  | .Leaf x => .Leaf x
  | x ⋆ y => rw (bu x ⋆ bu y)

attribute [simp] bu.eq_1

def NF (x : FreeMagma α) : Prop := x.Everywhere (fun y => bu rw y = y)

def bu_nf [hproj : IsProj rw] : ∀ x, NF rw (bu rw x) := by
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

theorem idem_of_NF {x : FreeMagma α} (h : NF rw x) : bu rw x = x := h.top

variable [IsProj rw]

@[simp] theorem bu_idem x : bu rw (bu rw x) = bu rw x := idem_of_NF rw (bu_nf rw x)

def ConfMagma := {x : FreeMagma α // bu rw x = x }

instance : Coe α (ConfMagma rw) where
  coe x := ⟨x, rfl⟩

instance : Magma (ConfMagma rw) where
  op := fun x y ↦ ⟨bu rw (x.1 ◇ y.1), bu_idem rw _⟩

instance [DecidableEq α] : DecidableEq (ConfMagma rw) :=
  inferInstanceAs (DecidableEq {x : FreeMagma α // bu rw x = x })

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

end Confluence
