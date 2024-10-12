import equational_theories.Confluence

open FreeMagma Confluence
variable {α: Type}

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
