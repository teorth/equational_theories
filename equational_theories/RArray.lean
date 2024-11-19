import Lean.ToExpr

/-!
A data structure for modelling `Fin n → α` (or `Array α`) optimized for a fast kernel-reduction get
operation.

For now not universe-polymorphic; smaller proof objects and no complication with the `ToExpr` type
class.
-/

inductive RArray (α : Type) : Type  where
  | leaf : α → RArray α
  | branch : Nat → RArray α → RArray α → RArray α

variable {α : Type}

/-- The crucial operation, written with very little abstractional overhead -/
noncomputable def RArray.get (a : RArray α) (n : Nat) : α :=
  RArray.rec (fun x _ => x) (fun p _ _ l r n => (p.ble n).rec (l n) (r (n.sub p))) a n

theorem RArray.get_eq_def (a : RArray α) (n : Nat) :
  a.get n = match a with
    | .leaf x => x
    | .branch p l r => (Nat.ble p n).rec (l.get n) (r.get (n.sub p)) := by
  conv => lhs; unfold RArray.get
  split <;> rfl

def RArray.getImpl (a : RArray α) (n : Nat) : α :=
  match a with
  | .leaf x => x
  | .branch p l r => if n < p then l.getImpl n else r.getImpl (n - p)

@[csimp]
theorem RArray.get_eq_getImpl : @RArray.get = @RArray.getImpl := by
  ext α a n
  induction a generalizing n with
  | leaf _ => rfl
  | branch p l r ihl ihr =>
    rw [RArray.getImpl, RArray.get_eq_def]
    simp only [ihl, ihr]
    cases hnp : Nat.ble p n
    · replace hnp := ne_true_of_eq_false hnp
      simp at hnp
      rw [if_pos]
      omega
    · simp at hnp
      rw [if_neg]; rfl
      omega

instance : GetElem (RArray α) Nat α (fun _ _ => True) where
  getElem a n _ := a.get n

def RArray.size : RArray α → Nat
  | leaf _ => 1
  | branch _ l r => l.size + r.size

def RArray.checkSize : RArray α → Option Nat
  | leaf _ => some 1
  | branch n l r =>
    l.checkSize.bind fun a =>
    r.checkSize.bind fun b =>
    bif n.beq a then some (a + b) else none

def RArray.WF : RArray α → Prop
  | leaf _ => True
  | branch n l r => n = l.size ∧ l.WF ∧ r.WF

theorem RArray.checkSize_iff {arr : RArray α} {n} :
    arr.checkSize = some n ↔ arr.WF ∧ arr.size = n := by
  induction arr generalizing n <;>
    simp only [checkSize, Option.some.injEq, WF, size, true_and, Option.bind_eq_some, and_assoc,
      exists_and_left, exists_eq_left', and_left_comm, *]
  repeat apply and_congr_right'
  rename_i i l _ _ _
  cases e : i.beq l.size <;> simp [Bool.eq_false_iff] at e <;> simp [e]

instance (arr : RArray α) : Decidable arr.WF :=
  decidable_of_bool arr.checkSize.isSome <| by simp [Option.isSome_iff_exists, RArray.checkSize_iff]

def RArray.ofFn {n : Nat} (f : Fin n → α) (h : 0 < n) : RArray α :=
  go 0 n h (Nat.le_refl _)
where
  go (lb ub : Nat) (h1 : lb < ub) (h2 : ub ≤ n) : RArray α :=
    if h : lb + 1 = ub then
      .leaf (f ⟨lb, Nat.lt_of_lt_of_le h1 h2⟩)
    else
      let mid := (lb + ub)/2
      .branch (mid - lb) (go lb mid (by omega) (by omega)) (go mid ub (by omega) h2)

def ofArray (xs : Array α) (h : 0 < xs.size) : RArray α :=
  .ofFn (fun i => xs.get i) h

theorem RArray.ofFn_correct {n : Nat} (f : Fin n → α) (h : 0 < n) (i : Fin n):
    RArray.get (.ofFn f h) i = f i :=
  go 0 n h (Nat.le_refl _) (Nat.zero_le _) i.2
where
  go lb ub h1 h2 (h3 : lb ≤ i.val) (h3 : i.val < ub) :
      RArray.get (.ofFn.go f lb ub h1 h2) (i - lb) = f i := by
    induction lb, ub, h1, h2 using RArray.ofFn.go.induct (f := f) (n := n)
    case case1 =>
      simp [ofFn.go, RArray.get_eq_getImpl, RArray.getImpl]
      congr
      omega
    case case2 ih1 ih2 hiu =>
      rw [ofFn.go]; simp only [↓reduceDIte, *]
      simp [RArray.get_eq_getImpl, RArray.getImpl] at *
      split
      · rw [ih1] <;> omega
      · rw [Nat.sub_sub, Nat.add_sub_cancel' (by omega)]
        rw [ih2] <;> omega

def RArray.toArray : RArray α → (out : Array α := #[]) → Array α
  | .leaf x, out => out.push x
  | .branch _ a b, out => b.toArray (a.toArray out)

section Meta
open Lean

def RArray.toExpr (ty : Expr) (f : α → Expr) : RArray α → Expr
  | .leaf x       =>
    mkApp2 (mkConst ``RArray.leaf) ty (f x)
  | .branch p l r =>
    mkApp4 (mkConst ``RArray.branch) ty (.lit (.natVal p)) (l.toExpr ty f) (r.toExpr ty f)

instance [ToExpr α] : ToExpr (RArray α) where
  toExpr a := a.toExpr (toTypeExpr α) (toExpr ·)
  toTypeExpr := mkApp (mkConst ``RArray) (toTypeExpr α)

end Meta
