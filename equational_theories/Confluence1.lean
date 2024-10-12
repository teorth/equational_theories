import equational_theories.Confluence

open FreeMagma Confluence
variable {α: Type} [DecidableEq α]

local macro "prove" rule:ident : tactic => `(tactic| (
  unfold $rule
  split
  · injections
    subst_eqs
    split
    · exfalso
      casesm* _ ∧ _
      subst_eqs
    · rfl
  · rfl
))

local macro "prove_proj" rule:ident : tactic => `(tactic| (
  intro x
  unfold $rule
  repeat' split
  any_goals subterm
))

namespace rw477

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
    prove_proj rule

@[simp]
theorem rule_yy (y : FreeMagma α) : rule (y ⋆ y) = y ⋆ y := by
  prove rule

@[simp]
theorem rule_yyy (y : FreeMagma α) :
    rule (y ⋆ (y ⋆ y)) = y ⋆ (y ⋆ y) := by
  prove rule

@[simp]
theorem rule_xyyy (x y : FreeMagma α) :
    rule (x ⋆ (y ⋆ (y ⋆ y))) = x ⋆ (y ⋆ (y ⋆ y)) := by
  prove rule

@[simp]
theorem rule_yxyyy (x y : FreeMagma α) :
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
    prove_proj rule

@[simp]
theorem rule_yy (y : FreeMagma α) : rule (y ⋆ y) = y ⋆ y := by
  prove rule

@[simp]
theorem rule_xyy (x y : FreeMagma α) :
    rule (x ⋆ (y ⋆ y)) = x ⋆ (y ⋆ y) := by
  prove rule

@[simp]
theorem rule_xxyy (x y : FreeMagma α) :
    rule (x ⋆ (x ⋆ (y ⋆ y))) = x ⋆ (x ⋆ (y ⋆ y)) := by
  prove rule

@[simp]
theorem rule_yxxyy (x y : FreeMagma α) :
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
    prove_proj rule

@[simp]
theorem rule_yy (y : FreeMagma α) : rule (y ⋆ y) = y ⋆ y := by
  prove rule

@[simp]
theorem rule_xyy (x y : FreeMagma α) :
    rule (x ⋆ (y ⋆ y)) = x ⋆ (y ⋆ y) := by
  prove rule

@[simp]
theorem rule_yxyy (x y : FreeMagma α) :
    rule (y ⋆ (x ⋆ (y ⋆ y))) = y ⋆ (x ⋆ (y ⋆ y)) := by
  prove rule

@[simp]
theorem rule_yyxyy (x y : FreeMagma α) :
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
    prove_proj rule

@[simp]
theorem rule_yy (y : FreeMagma α) : rule (y ⋆ y) = y ⋆ y := by
  prove rule

@[simp]
theorem rule_xyy (x y : FreeMagma α) :
    rule (x ⋆ (y ⋆ y)) = x ⋆ (y ⋆ y) := by
  prove rule

@[simp]
theorem rule_yyxxx (x y : FreeMagma α) :
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
    prove_proj rule

@[simp]
theorem rule_yy (y : FreeMagma α) : rule (y ⋆ y) = y ⋆ y := by
  prove rule

@[simp]
theorem rule_xyy (x y : FreeMagma α) :
    rule ((y ⋆ y) ⋆ x) = (y ⋆ y) ⋆ x := by
  prove rule

@[simp]
theorem rule_xxxyy (x y : FreeMagma α) :
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
    prove_proj rule

@[simp]
theorem rule_yy (y : FreeMagma α) : rule (y ⋆ y) = y ⋆ y := by
  prove rule

@[simp]
theorem rule_yyx (x y : FreeMagma α) :
    rule ((y ⋆ y) ⋆ x) = (y ⋆ y) ⋆ x := by
  prove rule

@[simp]
theorem rule_yyxx (x y : FreeMagma α) :
    rule (((y ⋆ y) ⋆ x) ⋆ x) = ((y ⋆ y) ⋆ x) ⋆ x := by
  prove rule

@[simp]
theorem rule_yyxxy (x y : FreeMagma α) :
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
    prove_proj rule

@[simp]
theorem rule_yy (y : FreeMagma α) : rule (y ⋆ y) = y ⋆ y := by
  prove rule

@[simp]
theorem rule_yyx (x y : FreeMagma α) :
    rule ((y ⋆ y) ⋆ x) = (y ⋆ y) ⋆ x := by
  prove rule

@[simp]
theorem rule_yyxy (x y : FreeMagma α) :
    rule (((y ⋆ y) ⋆ x) ⋆ y) = ((y ⋆ y) ⋆ x) ⋆ y := by
  prove rule

@[simp]
theorem rule_yyxyy (x y : FreeMagma α) :
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
    prove_proj rule

@[simp]
theorem rule_yy (y : FreeMagma α) : rule (y ⋆ y) = y ⋆ y := by
  prove rule

@[simp]
theorem rule_yyx (y : FreeMagma α) :
    rule ((y ⋆ y) ⋆ y) = (y ⋆ y) ⋆ y := by
  prove rule

@[simp]
theorem rule_yyyx (x y : FreeMagma α) :
    rule (((y ⋆ y) ⋆ y) ⋆ x) = ((y ⋆ y) ⋆ y) ⋆ x := by
  prove rule

@[simp]
theorem rule_yyyxy (x y : FreeMagma α) :
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
    prove_proj rule

@[simp]
theorem rule_yy (y : FreeMagma α) : rule (y ⋆ y) = y ⋆ y := by
  prove rule

@[simp]
theorem rule_yxx (x y : FreeMagma α) :
    rule (y ⋆ (x ⋆ x)) = y ⋆ (x ⋆ x) := by
  prove rule

@[simp]
theorem rule_yxxy (x y : FreeMagma α) :
    rule ((y ⋆ (x ⋆ x)) ⋆ y) = (y ⋆ (x ⋆ x)) ⋆ y:= by
  prove rule

@[simp]
theorem rule_yyxxy (x y : FreeMagma α) :
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
    prove_proj rule

@[simp]
theorem rule_yy (y : FreeMagma α) : rule (y ⋆ y) = y ⋆ y := by
  prove rule

@[simp]
theorem rule_xyy (x y : FreeMagma α) :
    rule (x ⋆ (y ⋆ y)) = x ⋆ (y ⋆ y) := by
  prove rule

@[simp]
theorem rule_xyyy (x y : FreeMagma α) :
    rule ((x ⋆ (y ⋆ y)) ⋆ y) = (x ⋆ (y ⋆ y)) ⋆ y:= by
  prove rule

@[simp]
theorem rule_yxyyy (x y : FreeMagma α) :
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
    prove_proj rule

@[simp]
theorem rule_xx (x : FreeMagma α) : rule (x ⋆ x) = x ⋆ x := by
  prove rule

@[simp]
theorem rule_xxy (x y : FreeMagma α) :
    rule ((x ⋆ x) ⋆ y) = (x ⋆ x) ⋆ y := by
  prove rule

@[simp]
theorem rule_yxxy (x y : FreeMagma α) :
    rule (y ⋆ ((x ⋆ x) ⋆ y)) = (y ⋆ ((x ⋆ x) ⋆ y)) := by
  prove rule

@[simp]
theorem rule_yxxyy (x y : FreeMagma α) :
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
    prove_proj rule

@[simp]
theorem rule_yy (y : FreeMagma α) : rule (y ⋆ y) = y ⋆ y := by
  prove rule

@[simp]
theorem rule_yyx (x y : FreeMagma α) :
    rule ((y ⋆ y) ⋆ x) = (y ⋆ y) ⋆ x := by
  prove rule

@[simp]
theorem rule_yyyx (x y : FreeMagma α) :
    rule (y ⋆ ((y ⋆ y) ⋆ x)) = (y ⋆ ((y ⋆ y) ⋆ x)) := by
  prove rule

@[simp]
theorem rule_yyyxy (x y : FreeMagma α) :
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
