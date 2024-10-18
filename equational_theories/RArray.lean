import Lean

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
  RArray.rec (fun x => x) (fun p _ _ l r => (Nat.ble p n).rec l r) a

theorem RArray.get_eq_def (a : RArray α) (n : Nat) :
  a.get n = match a with
    | .leaf x => x
    | .branch p l r => (Nat.ble p n).rec (l.get n) (r.get n) := by
  conv => lhs; unfold RArray.get
  split <;> rfl

def RArray.getImpl (a : RArray α) (n : Nat) : α :=
  match a with
  | .leaf x => x
  | .branch p l r => if n < p then l.getImpl n else r.getImpl n

@[csimp]
theorem RArray.get_eq_getImpl : @RArray.get = @RArray.getImpl := by
  ext α a n
  induction a with
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
      rw [if_neg]
      omega

instance : GetElem (RArray α) Nat α (fun _ _ => True) where
  getElem a n _ := a.get n

def RArray.size : RArray α → Nat
  | leaf _ => 1
  | branch _ l r => l.size + r.size

def RArray.ofFn {n : Nat} (f : Fin n → α) (h : 0 < n) : RArray α :=
  go 0 n h (Nat.le_refl _)
where
  go (lb ub : Nat) (h1 : lb < ub) (h2 : ub ≤ n) : RArray α :=
    if h : lb + 1 = ub then
      .leaf (f ⟨lb, Nat.lt_of_lt_of_le h1 h2⟩)
    else
      let mid := (lb + ub)/2
      .branch mid (go lb mid (by omega) (by omega)) (go mid ub (by omega) h2)

def ofArray (xs : Array α) (h : 0 < xs.size) : RArray α :=
  .ofFn (fun i => xs.get i) h

theorem RArray.ofFn_correct {n : Nat} (f : Fin n → α) (h : 0 < n) (i : Fin n):
    RArray.get (.ofFn f h) i = f i :=
  go 0 n h (Nat.le_refl _) (Nat.zero_le _) i.2
where
  go lb ub h1 h2 (h3 : lb ≤ i.val) (h3 : i.val < ub) : RArray.get (.ofFn.go f lb ub h1 h2) i = f i := by
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
      · rw [ih2] <;> omega


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
