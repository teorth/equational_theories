import Mathlib.Data.Set.Finite.Basic

import equational_theories.FreshGenerator
import equational_theories.EquationalResult
import equational_theories.Equations.All

/- Refutes the implications from 1323.

When the proof is done, update the blueprint with \lean and \leanok tags as appropriate.
-/


namespace Eq1323


section Ingredients
-- Define the direct sum of copies of Z/2, the sign group, type for roots, and ϕ

open symmDiff

variable {α : Type}

def FreeAbGrpExp2 (α : Type) : Type := Finset α

def FreeAbGrpExp2.mk : Finset α → FreeAbGrpExp2 α := id
def FreeAbGrpExp2.coords : FreeAbGrpExp2 α → Finset α := id
@[simp] theorem FreeAbGrpExp2.mk_coords (a : FreeAbGrpExp2 α) : FreeAbGrpExp2.mk a.coords = a := rfl
@[simp] theorem FreeAbGrpExp2.coords_mk (a : Finset α) : (FreeAbGrpExp2.mk a).coords = a := rfl

instance [DecidableEq α] : DecidableEq (FreeAbGrpExp2 α) := inferInstanceAs (DecidableEq (Finset α))

instance [DecidableEq α] : Add (FreeAbGrpExp2 α) where
  add a b := FreeAbGrpExp2.mk (a.coords ∆ b.coords)
instance : Zero (FreeAbGrpExp2 α) where zero := ⟨∅, by simp⟩
instance : Neg (FreeAbGrpExp2 α) where neg := id
theorem FreeAbGrpExp2.add_def [DecidableEq α] (a b : FreeAbGrpExp2 α) :
  a + b = FreeAbGrpExp2.mk (a.coords ∆ b.coords) := rfl
theorem FreeAbGrpExp2.zero_def : (Zero.zero : FreeAbGrpExp2 α) = ⟨∅, by simp⟩ := rfl
theorem FreeAbGrpExp2.neg_def (a : FreeAbGrpExp2 α) : -a = a := rfl
@[simp] theorem FreeAbGrpExp2.coords_0 : (0 : FreeAbGrpExp2 α).coords = ∅ := rfl
@[simp] theorem FreeAbGrpExp2.mk_empty : (FreeAbGrpExp2.mk ∅ : FreeAbGrpExp2 α) = 0 := rfl

instance [DecidableEq α] : AddCommGroup (FreeAbGrpExp2 α) where
  add_zero x := by simp [FreeAbGrpExp2.add_def, symmDiff_def]
  zero_add := by simp [FreeAbGrpExp2.add_def, symmDiff_def]
  add_comm := by simp [FreeAbGrpExp2.add_def, symmDiff_comm]
  add_assoc := by simp [FreeAbGrpExp2.add_def, symmDiff_assoc]
  nsmul := nsmulRec
  zsmul := zsmulRec
  neg_add_cancel := by simp [FreeAbGrpExp2.add_def, FreeAbGrpExp2.neg_def]

@[simp] theorem FreeAbGrpExp2.add_cancel {α : Type} [inst : DecidableEq α] (x : FreeAbGrpExp2 α) :
  x + x = 0 := by simp [FreeAbGrpExp2.add_def]

abbrev Sq := FreeAbGrpExp2 Nat

abbrev Sq' := {g : Sq // g ≠ 0}

inductive Sign where | plus | minus

instance : Mul Sign where mul
  | .plus, .plus | .minus, .minus => .plus | .plus, .minus | .minus, .plus => .minus
instance : One Sign where one := .plus
instance : Inv Sign where inv := id
instance : Div Sign where div a b := a * b⁻¹
theorem sign_mul (a b : Sign) : a * b = match a, b with
  | .plus, .plus | .minus, .minus => .plus | .plus, .minus | .minus, .plus => .minus := by rfl
theorem sign_one : 1 = Sign.plus := rfl
theorem sign_inv_self (a : Sign) : a⁻¹ = a := rfl
theorem Sign.div_eq_mul_inv (a b : Sign) : a / b = a * b := rfl
instance : CommGroup Sign where
  mul_one a := by cases a <;> simp [sign_mul]
  one_mul a := by cases a <;> simp [sign_mul]
  mul_comm a b := by cases a <;> cases b <;> simp [sign_mul]
  mul_assoc a b c := by cases a <;> cases b <;> cases c <;> simp [sign_mul]
  inv_mul_cancel a := by simp [sign_one, sign_inv_self]; cases a <;> (simp [sign_mul])
  div_eq_mul_inv := Sign.div_eq_mul_inv

theorem sign_mul_cancel : (a : Sign) → a * a = 1
  | .plus => by simp [sign_mul, sign_one] | .minus => by simp [sign_mul, sign_one]

-- Corresponds to ℚˣ in the blueprint
def Rt' := Sign × FreeGroup Nat

abbrev Rt := Rt' × Sq'

instance : Group Rt' := inferInstanceAs (Group (Sign × FreeGroup Nat))
instance : Neg Rt' where neg x := ⟨.minus, 1⟩ * x
@[simp] theorem RtId_neg {x : Rt'} : -x = ⟨.minus, 1⟩ * x := rfl
theorem RtId_mul_eta {x y : Rt'} : (x * y) = (x.1 * y.1, x.2 * y.2) := rfl
theorem RtId_inv_eta {x : Rt'} : x⁻¹ = (x.1⁻¹, x.2⁻¹) := rfl

theorem RtId_mul_fst (x y : Rt') : (x * y).1 = x.1 * y.1 := rfl
theorem RtId_mul_snd (x y : Rt') : (x * y).2 = x.2 * y.2 := rfl
theorem RtId_inv_fst (x : Rt') : x⁻¹.1 = x.1⁻¹ := rfl
theorem RtId_inv_snd (x : Rt') : x⁻¹.2 = x.2⁻¹ := rfl

def ϕ (a : Sq') (b : Sq) : Rt' := sorry

def invϕ (a : Sq') (x : Rt') : Sq := sorry

@[simp]
theorem ϕ_0 {a : Sq'} : ϕ a 0 = 1 := sorry

theorem ϕ_duality {a : Sq'} {b : Sq} : ϕ a (a + b) = -ϕ a b := sorry

@[simp]
theorem ϕ_self {a : Sq'} : ϕ a a = -1 := by rw [←add_zero a.val, ϕ_duality]; simp

@[simp]
theorem ϕ_invϕ {a : Sq'} {x : Rt'} : ϕ a (invϕ a x) = x := sorry

@[simp]
theorem invϕ_ϕ {a : Sq'} {b : Sq} : invϕ a (ϕ a b) = b := sorry

@[simp]
theorem invϕ_0 {a : Sq'} : invϕ a 1 = 0 := sorry

end Ingredients


section Greedy

def isProper (c : Rt → Rt → Rt) : Prop := ∀ x y,
  x.2 ≠ y.2 → (c x y).2 ≠ x.2 ∧ (c x y).2 ≠ y.2 ∧ c y (c x y) = (x.1 * ϕ x.2 y.2, x.2)

theorem existsProdSquare : ∃ c, isProper c := sorry

end Greedy


inductive G where
  | square : Sq → G
  | root : Rt → G

def op (c : Rt → Rt → Rt) : G → G → G
  | .square a, .square b => .square (a + b)
  | .root x, .square b => .root (x.1 * ϕ x.2 b, x.2)
  | .square b, .root x => .root (x.1 * (ϕ x.2 b)⁻¹, x.2)
  | .root x, .root y =>
    if x.2 = y.2
      then .square (x.2 + invϕ x.2 (y.1⁻¹ * x.1))
      else .root (c x y)


theorem op_RSy_LSy_eq_Id c : (x : G) → (y : G) → op c (op c (op c y y) x) (op c y y) = x
  | .square a, .square b => by simp [op]
  | .root (x, a), .square b => by simp [op]
  | .square b, .root (x, a) => by simp [op]; rw [add_comm, ←add_assoc]; simp
  | .root (x, a), .root (y, b) => by simp [op]


theorem roots_LyRy {x y a b c} (h : a ≠ b) (proper : isProper c) :
    op c (.root (y, b)) (op c (.root (x, a)) (.root (y, b))) = .root (x * ϕ a b, a) := by
  replace proper := proper (x, a) (y, b) h
  simp [op, h, proper, proper.2.1.symm]

theorem op_Ly_Ry_eq_LSy c (proper : isProper c) : (x : G) → (y : G) → op c y (op c x y) = op c x (op c y y)
  | .square a, .square b => by simp [op]; rw [add_comm, add_assoc]; simp
  | .root (x, a), .square b => by simp [op, mul_assoc]
  | .square b, .root (x, a) => by simp [op]; apply add_comm
  | .root (x, a), .root (y, b) =>
    if h : a = b
    then by
      simp [op, h, ϕ_duality]
      apply Prod.ext <;> {
        simp only [RtId_mul_eta, RtId_inv_eta]
        try nth_rewrite 2 [mul_comm]  -- we need to exploit commutativity of the signs group
        group
      }
    else by
      simp [roots_LyRy h proper]
      simp [op]


theorem eq1323_if_conditions (G : Type) (_ : Magma G) (h1 : ∀ x y : G, ((y ◇ y) ◇ x) ◇ (y ◇ y) = x)
    (h2 : ∀ x y : G, y ◇ (x ◇ y) = x ◇ (y ◇ y)) : Equation1323 G := by
  intro x y
  rw [h2, h1]
  -- λ x y => (h2 ((y ◇ y) ◇ x) y ▸ h1 x y).symm


/-- https://leanprover.zulipchat.com/#narrow/channel/458659-Equational/topic/1323/near/481475622 -/
-- @[equational_result]
theorem Equation1323_not_implies_Equation2744 :
    ∃ (G: Type) (_: Magma G), Equation1323 G ∧ ¬ Equation2744 G := by

  let ⟨c, proper⟩ := existsProdSquare
  use G, ⟨op c⟩

  constructor
  · apply eq1323_if_conditions G _
    apply op_RSy_LSy_eq_Id c
    apply op_Ly_Ry_eq_LSy c proper
  · sorry


end Eq1323
