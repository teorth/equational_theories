import Mathlib.Data.Finset.Order
import Mathlib.Data.Set.Finite.Basic

import equational_theories.FreshGenerator
import equational_theories.EquationalResult
import equational_theories.Equations.All
import equational_theories.Mathlib.Order.Greedy

/- Refutes the implications from 1323.

When the proof is done, update the blueprint with \lean and \leanok tags as appropriate.
-/


namespace Eq1323


section Ingredients

open symmDiff

variable {α : Type}

def FreeAbGrpExp2 (α : Type) : Type := Finset α

def FreeAbGrpExp2.mk : Finset α → FreeAbGrpExp2 α := id
def FreeAbGrpExp2.of (x : α) : FreeAbGrpExp2 α := FreeAbGrpExp2.mk {x}
def FreeAbGrpExp2.coords : FreeAbGrpExp2 α → Finset α := id
@[simp] theorem FreeAbGrpExp2.mk_coords (a : FreeAbGrpExp2 α) : FreeAbGrpExp2.mk a.coords = a := rfl
@[simp] theorem FreeAbGrpExp2.coords_mk (a : Finset α) : (FreeAbGrpExp2.mk a).coords = a := rfl

instance [DecidableEq α] : DecidableEq (FreeAbGrpExp2 α) := inferInstanceAs (DecidableEq (Finset α))
instance [Countable α] : Countable (FreeAbGrpExp2 α) := inferInstanceAs (Countable (Finset α))
instance [Infinite α] : Infinite (FreeAbGrpExp2 α) := inferInstanceAs (Infinite (Finset α))

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
theorem FreeAbGrpExp2.of_nonzero (x : α) : FreeAbGrpExp2.of x ≠ 0 := Finset.singleton_ne_empty _
theorem FreeAbGrpExp2.of_injective : Function.Injective (FreeAbGrpExp2.of : α → FreeAbGrpExp2 α) :=
  Finset.singleton_injective
theorem FreeAbGrpExp2.of_injective' {x y : α} : x ≠ y → FreeAbGrpExp2.of x ≠ FreeAbGrpExp2.of y :=
  mt (of_injective ·)
theorem FreeAbGrpExp2.add_coords [DecidableEq α] (a b : FreeAbGrpExp2 α) : (a + b).coords = a.coords ∆ b.coords :=
  by dsimp [FreeAbGrpExp2.add_def]

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

theorem sq'_infinite : {g : Sq | g ≠ 0}.Infinite := by
  apply Set.infinite_of_finite_compl
  rw [Set.compl_ne_eq_singleton]
  exact Set.finite_singleton _

instance : Infinite Sq' := ⟨sq'_infinite⟩

inductive Sign where | plus | minus deriving Inhabited, DecidableEq
instance : Countable Sign where
  exists_injective_nat' := ⟨
    fun | .plus => 0 | .minus => 1,
    by intro a b; cases a <;> cases b <;> simp
  ⟩

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
deriving DecidableEq

abbrev Rt := Rt' × Sq'

instance : Countable Rt' := inferInstanceAs (Countable (Sign × FreeGroup Nat))

instance : Group Rt' := inferInstanceAs (Group (Sign × FreeGroup Nat))
instance : Neg Rt' where neg x := ⟨.minus, 1⟩ * x
@[simp] theorem RtId_neg {x : Rt'} : -x = ⟨.minus, 1⟩ * x := rfl
theorem RtId_mul_eta {x y : Rt'} : (x * y) = (x.1 * y.1, x.2 * y.2) := rfl
theorem RtId_inv_eta {x : Rt'} : x⁻¹ = (x.1⁻¹, x.2⁻¹) := rfl
theorem RtId_pow_eta {x : Rt'} {n : ℕ} : x ^ n = (x.1 ^ n, x.2 ^ n) := rfl

theorem RtId_mul_fst (x y : Rt') : (x * y).1 = x.1 * y.1 := rfl
theorem RtId_mul_snd (x y : Rt') : (x * y).2 = x.2 * y.2 := rfl
theorem RtId_inv_fst (x : Rt') : x⁻¹.1 = x.1⁻¹ := rfl
theorem RtId_inv_snd (x : Rt') : x⁻¹.2 = x.2⁻¹ := rfl
theorem RtId_pow_fst (x : Rt') (n : ℕ) : (x ^ n).1 = x.1 ^ n := rfl
theorem RtId_pow_snd (x : Rt') (n : ℕ) : (x ^ n).2 = x.2 ^ n := rfl

-- inductive Mod3 (n : ℤ) : Prop
--   | rem0 : (k : ℤ) → n = 3 * k → Mod3 n
--   | rem1 : (k : ℤ) → n = 3 * k + 1 → Mod3 n
--   | rem2 : (k : ℤ) → n = 3 * k + 2 → Mod3 n

-- theorem Mod3.of (n : ℤ) : Mod3 n :=
--   let q := n / 3
--   let r := n % 3
--   let ⟨decomp, hl, hu⟩ := (Int.ediv_emod_unique (by simp)).mp ⟨Eq.refl q, Eq.refl r⟩
--   let decomp : n = 3 * q + r := by simp [decomp, add_comm]
--   if heq : r = 0 then .rem0 q (by simp [heq, decomp]) else
--   let hl := Int.le_of_sub_one_lt <| lt_of_le_of_ne hl <| Ne.symm heq
--   if heq : r = 1 then .rem1 q (by simp [heq, decomp]) else
--   let hl := Int.le_of_sub_one_lt <| lt_of_le_of_ne hl <| Ne.symm heq
--   if heq : r = 2 then .rem2 q (by simp [heq, decomp]) else
--   let hl := Int.le_of_sub_one_lt <| lt_of_le_of_ne hl <| Ne.symm heq
--   absurd hl (Int.not_le_of_gt hu)

inductive Mod3 (n : ℕ) : Prop
  | rem0 : (k : ℕ) → n = 3 * k → Mod3 n
  | rem1 : (k : ℕ) → n = 3 * k + 1 → Mod3 n
  | rem2 : (k : ℕ) → n = 3 * k + 2 → Mod3 n

theorem Mod3.of (n : ℕ) : Mod3 n :=
  let q := n / 3
  let r := n % 3
  have decomp : n = 3 * q + r := by simp [q, r, Nat.div_add_mod]
  match h : r with
  | 0 => .rem0 q decomp
  | 1 => .rem1 q decomp
  | 2 => .rem2 q decomp
  | r' + 3 => by
    have : r < 3 := by simp [r, Nat.mod_lt]
    simp [h, add_assoc] at this

theorem Finset.eq_rot3 {α : Type} [DecidableEq α] {a b c : α} : {a, b, c} = ({b, c, a} : Finset α) := by
  simp [Finset.insert_eq]
  rw [Finset.union_comm, Finset.union_assoc]

end Ingredients


section Phi

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
theorem invϕ_0 {a : Sq'} : invϕ a 1 = 0 := ϕ_0 ▸ invϕ_ϕ

theorem ϕ_eq_diff_0_or_a {a : Sq'} {b c : Sq} (h : (ϕ a b).2 = (ϕ a c).2) : b = c ∨ b = a + c := by
  match h1 : (ϕ a b).1, h2 : (ϕ a c).1 with
  | .plus, .plus | .minus, .minus =>
    have : ϕ a b = ϕ a c := Prod.ext (h1 ▸ h2) h
    apply_fun invϕ a at this
    simp at this
    tauto
  | .plus, .minus | .minus, .plus =>
    have : ϕ a b = -ϕ a c := by
      simp [Neg.neg, RtId_mul_eta, h2, sign_mul]
      apply Prod.ext <;> tauto
    rw [←ϕ_duality] at this
    apply_fun invϕ a at this
    simp_all

theorem ϕ_unit_0_or_a {a : Sq'} {b : Sq} (h : (ϕ a b).2 = 1) : b = 0 ∨ b = a := by
  have := ϕ_eq_diff_0_or_a (a := a) (b := b) (c := 0)
  simp at this
  exact this h

end Phi


section Relations

structure Relation where
  x : Rt
  y : Rt
  z : Rt
  nonDiag : x.2 ≠ y.2 ∧ y.2 ≠ z.2 ∧ z.2 ≠ x.2
deriving DecidableEq

structure NePair where
  x : Rt
  y : Rt
  nonDiag : x.2 ≠ y.2

def NePair.toPair (p : NePair) := (p.x, p.y)
theorem NePair.toPair.inj : Function.Injective NePair.toPair
  | ⟨x1, y1, h1⟩, ⟨x2, y2, h2⟩ => by simp [toPair]

instance : Countable NePair := Function.Injective.countable NePair.toPair.inj

variable {rel : Relation}
variable {n m : ℕ}

def Relation.lhs : NePair := ⟨rel.x, rel.y, rel.nonDiag.1⟩

@[simp] def Relation.next (rel : Relation) : Relation :=
  ⟨rel.y, rel.z, ⟨rel.x.1 * ϕ rel.x.2 rel.y.2, rel.x.2⟩, by have := rel.nonDiag; tauto⟩

@[simp] def Relation.skip : ℕ → Relation → Relation := Nat.repeat Relation.next

theorem Relation.next_3 : Nat.repeat Relation.next 3 rel =
  ⟨⟨rel.x.1 * ϕ rel.x.2 rel.y.2, rel.x.2⟩,
   ⟨rel.y.1 * ϕ rel.y.2 rel.z.2, rel.y.2⟩,
   ⟨rel.z.1 * ϕ rel.z.2 rel.x.2, rel.z.2⟩, rel.nonDiag⟩ := rfl

theorem Nat.repeat_add {α : Type} (f : α → α) (n m : ℕ) (x : α)
    : Nat.repeat f (n + m) x = Nat.repeat f n (Nat.repeat f m x):= by
  induction n with
  | zero => simp [Nat.repeat]
  | succ n ih => nth_rewrite 2 [add_comm]; rw [add_assoc, add_comm]; simp [ih, Nat.repeat]

@[simp] theorem Relation.next_3_n : Nat.repeat Relation.next (3 * n) rel =
    ⟨⟨rel.x.1 * ϕ rel.x.2 rel.y.2 ^ n, rel.x.2⟩,
     ⟨rel.y.1 * ϕ rel.y.2 rel.z.2 ^ n, rel.y.2⟩,
     ⟨rel.z.1 * ϕ rel.z.2 rel.x.2 ^ n, rel.z.2⟩, rel.nonDiag⟩ := by
  induction n
  case zero => simp [Nat.repeat]
  case succ hi =>
    simp [add_comm, mul_add, Nat.repeat_add, next_3, hi]
    group
    trivial

def Relation.orbit : Set Relation := { Nat.repeat Relation.next n rel | n : ℕ }

theorem Relation.orbit_self : rel ∈ rel.orbit := ⟨0, by simp [Nat.repeat]⟩

theorem Relation.orbit_next : rel.next ∈ rel.orbit := ⟨1, by simp [Nat.repeat]⟩

theorem Relation.orbit_trans {a b c : Relation} : a ∈ b.orbit → b ∈ c.orbit → a ∈ c.orbit := by
  simp [orbit]
  intro n hn m hm
  use n + m
  simp [Nat.repeat_add, hm, hn]

def isFunc (A : Set Relation) : Prop :=
  ∀ {rel rel' : Relation}, rel ∈ A → rel' ∈ A → rel.lhs = rel'.lhs → rel.z = rel'.z

theorem Relation.orbit_func' (n : ℕ) (h : (rel.skip n).lhs = rel.lhs) : n = 0 := by
  have := rel.nonDiag
  simp [lhs, skip] at h
  match Mod3.of n with
  | .rem0 k hk =>
    if hk0 : k = 0 then simp [hk, hk0] else
    simp [hk] at h
    have hx := congr_arg (Prod.snd ∘ Prod.fst) h.left
    simp [RtId_mul_snd, RtId_pow_snd] at hx
    rw [←FreeGroup.pow_eq_one_iff hk0] at hx
    apply ϕ_unit_0_or_a at hx
    simp [rel.y.2.prop] at hx
    apply Subtype.eq at hx
    tauto
  | .rem1 k hk | .rem2 k hk =>
    simp [hk] at h
    have hx := congr_arg Prod.snd h.right
    simp [Nat.repeat] at hx
    tauto

theorem Relation.orbit_func : isFunc rel.orbit := by
  intro rel rel' ⟨n, hrel⟩ ⟨n', hrel'⟩ h
  rcases Nat.lt_trichotomy n n' with hn | hn | hn
  · exfalso
    have : n' = (n' - n) + n := by simp [Nat.sub_add_eq_max, le_of_lt, hn]
    rw [this, Nat.repeat_add] at hrel'
    apply_fun (·.lhs) at hrel'
    simp [hrel, ←h] at hrel'
    apply rel.orbit_func' _ at hrel'
    apply Nat.sub_ne_zero_of_lt hn hrel'
  · simp [←hrel, ←hrel', hn]
  · exfalso
    have : n = (n - n') + n' := by simp [Nat.sub_add_eq_max, le_of_lt, hn]
    rw [this, Nat.repeat_add] at hrel
    apply_fun (·.lhs) at hrel
    simp [hrel', h] at hrel
    apply rel'.orbit_func' _ at hrel
    apply Nat.sub_ne_zero_of_lt hn hrel

def Relation.squares : Finset Sq' := {rel.x.2, rel.y.2, rel.z.2}

theorem Relation.x_square : rel.x.2 ∈ rel.squares := by simp [squares]
theorem Relation.y_square : rel.y.2 ∈ rel.squares := by simp [squares]
theorem Relation.z_square : rel.z.2 ∈ rel.squares := by simp [squares]

theorem Relation.orbit_squares {rel'} (h : rel' ∈ rel.orbit) : rel'.squares = rel.squares := by
  obtain ⟨n, h⟩ := h
  apply_fun (·.squares) at h
  match Mod3.of n with
  | .rem0 k hk => simp [hk, squares] at h; simp [h, squares]
  | .rem1 k hk => simp [hk, squares, Nat.repeat] at h; rw [←Finset.eq_rot3] at h; simp [h, squares]
  | .rem2 k hk => simp [hk, squares, Nat.repeat] at h; rw [Finset.eq_rot3] at h; simp [h, squares]

end Relations


section Iteration

abbrev ChosenRelations := Finset Relation
abbrev PartialFunction := Set Relation

def ChosenRelations.closure (F : ChosenRelations) : PartialFunction := ⋃ rel ∈ F, rel.orbit

theorem ChosenRelations.mem_closure (F : ChosenRelations) {rel : Relation}
    : rel ∈ F.closure ↔ ∃ base ∈ F, rel ∈ base.orbit := by
  constructor
  · intro ⟨_, ⟨base, hb⟩, hr⟩
    simp [←hb] at hr
    exact ⟨base, hr⟩
  · intro ⟨base, hb, hr⟩
    simp [closure]
    use base

theorem ChosenRelations.le_closure (F : ChosenRelations) : F.toSet ≤ F.closure := by
  intro rel h
  simp [closure]
  exact ⟨rel, h, rel.orbit_self⟩

theorem ChosenRelations.closure_mono {F1 F2 : ChosenRelations} (h : F1 ≤ F2) :
    F1.closure ≤ F2.closure := by
  unfold closure
  intro _ ⟨_, ⟨_, h1⟩, h2⟩
  simp [←h1] at h2
  simp
  exact ⟨_, h h2.1, h2.2⟩

def PartialFunction.definedAt (F : PartialFunction) (u v : Rt) : Prop :=
  ∃ rel ∈ F, rel.x = u ∧ rel.y = v

theorem PartialFunction.closure_next (F : ChosenRelations) {rel : Relation}
    (h : rel ∈ F.closure) : rel.next ∈ F.closure := by
  obtain ⟨base, hb, hr⟩ := F.mem_closure.mp h
  apply Relation.orbit_trans rel.orbit_next at hr
  simp only [ChosenRelations.closure, Set.mem_iUnion, exists_prop]
  exact ⟨base, hb, hr⟩

structure Extension where
  core : ChosenRelations
  func : isFunc core.closure
  u : Rt
  v : Rt
  u_neq_v : u.2 ≠ v.2
  not_def : ¬core.closure.definedAt u v

variable (E : Extension)

noncomputable def Extension.oldSquares : Finset Sq' :=
  {E.u.2, E.v.2} ∪ E.core.biUnion (·.squares)

noncomputable def Extension.oldRtIds : Finset Rt' :=
  let fromValues := {E.u.1, E.v.1} ∪ E.core.biUnion fun a => {a.x.1, a.y.1, a.z.1}
  let fromPhis := (E.oldSquares ×ˢ E.oldSquares).image fun (x, y) => ϕ x y
  fromValues ∪ fromPhis

theorem Extension.oldSquares_u_2 : E.u.2 ∈ E.oldSquares := by simp [oldSquares]
theorem Extension.oldSquares_v_2 : E.v.2 ∈ E.oldSquares := by simp [oldSquares]

theorem Extension.oldSquares_core_squares {rel x} (h : rel ∈ E.core) (h2 : x ∈ rel.squares)
    : x ∈ E.oldSquares := by
  simp [oldSquares]
  repeat right
  use rel

theorem Extension.oldRtIds_v_1 : E.v.1 ∈ E.oldRtIds := by simp [oldRtIds]

theorem Extension.oldRtIds_phi_v_2_u2 : ϕ E.v.2 E.u.2 ∈ E.oldRtIds := by
  simp [oldRtIds]
  repeat right
  exact ⟨_, E.v.2.prop, _, ⟨E.oldSquares_v_2, E.u.2.prop, E.oldSquares_u_2⟩, rfl⟩

theorem Extension.oldRtIds_phi_v_2_square {rel x} (h : rel ∈ E.core) (h2 : x ∈ rel.squares)
    : ϕ E.v.2 x ∈ E.oldRtIds := by
  simp [oldRtIds]
  repeat right
  exact ⟨_, E.v.2.prop, _, ⟨E.oldSquares_v_2, x.prop, E.oldSquares_core_squares h h2⟩, rfl⟩

theorem Extension.oldRtIds_phi_square_square {rel x y} (h : rel ∈ E.core) (h2 : x ∈ rel.squares)
     (h3 : y ∈ rel.squares) : ϕ x y ∈ E.oldRtIds := by
  simp [oldRtIds]
  repeat right
  exact ⟨_, x.prop, _, ⟨E.oldSquares_core_squares h h2, y.prop, E.oldSquares_core_squares h h3⟩, rfl⟩

noncomputable def Extension.freshGeneratorName : Nat :=
  FreshGenerator.freshGeneratorName <| E.oldRtIds.image Prod.snd

noncomputable def Extension.freshRtId : Rt' :=
  (.plus, FreeGroup.of E.freshGeneratorName)

noncomputable def Extension.freshSquare : Sq' :=
  let c := invϕ E.v.2 E.freshRtId
  have : c ≠ 0 := fun hc => by
    apply_fun ϕ E.v.2 at hc
    apply_fun Prod.snd at hc
    simp [c, Extension.freshRtId] at hc
  ⟨c, this⟩

@[simp] theorem Extension.phi_v_2_freshRoot : ϕ E.v.2 E.freshSquare = E.freshRtId := by
  simp [freshSquare]

noncomputable def Extension.projectFresh (x : Rt') : ℤ :=
  FreshGenerator.projectFresh (E.oldRtIds.image Prod.snd) x.2

@[simp] theorem Extension.projectFresh_mul {x y} : E.projectFresh (x * y) = E.projectFresh x + E.projectFresh y := by simp [projectFresh, RtId_mul_snd]; rfl
@[simp] theorem Extension.projectFresh_pow {x} {n : ℕ} : E.projectFresh (x ^ n) = n * E.projectFresh x := by simp [projectFresh, RtId_pow_snd]; rfl
@[simp] theorem Extension.projectFresh_freshRtId : E.projectFresh E.freshRtId = 1 := by simp [projectFresh, freshRtId, freshGeneratorName, ←FreshGenerator.freshGenerator.eq_1]

@[simp] theorem Extension.projectFresh_old {r : Rt'} (h : r ∈ E.oldRtIds) : E.projectFresh r = 0 := by
  simp [projectFresh]
  apply FreshGenerator.projectFresh_old
  rw [Finset.mem_image]
  use r

theorem Extension.projectFresh_closure_y_1 {rel} (h : rel ∈ E.core.closure) : E.projectFresh rel.y.1 = 0 := by
  obtain ⟨base, hb, ⟨n, hr⟩⟩ := E.core.mem_closure.mp h
  cases Mod3.of n
  repeat {
    rename_i hk
    simp [hk, Nat.repeat] at hr
    simp only [←hr]
    simp [projectFresh_mul, projectFresh_pow,
          E.oldRtIds_phi_square_square hb base.y_square base.z_square,
          E.oldRtIds_phi_square_square hb base.z_square base.x_square,
          E.oldRtIds_phi_square_square hb base.x_square base.y_square]
    apply E.projectFresh_old
    simp [oldRtIds]
    right; right; left
    exact ⟨_, hb, by tauto⟩
  }

noncomputable def Extension.w : Rt := ⟨1, E.freshSquare⟩

noncomputable def Extension.newRelation : Relation := .mk E.u E.v E.w <| by
  split_ands
  exact E.u_neq_v
  by_contra hc
  apply_fun fun x => (ϕ E.v.2 x).1 at hc
  simp [w, freshSquare, freshRtId] at hc
  by_contra hc
  apply_fun fun x => E.projectFresh (ϕ E.v.2 x) at hc
  simp [w, oldRtIds_phi_v_2_u2] at hc

theorem Extension.closure_x_not_w {rel} (h : rel ∈ E.core.closure) : rel.x.2 ≠ E.freshSquare := by
  suffices ϕ E.v.2 rel.x.2 ∈ E.oldRtIds by
    by_contra hc
    apply_fun fun x => E.projectFresh (ϕ E.v.2 x) at hc
    simp [freshSquare, this] at hc
  obtain ⟨_, hb, hr⟩ := E.core.mem_closure.mp h
  apply E.oldRtIds_phi_v_2_square hb
  rw [←Relation.orbit_squares hr]
  simp [Relation.squares]

theorem Extension.closure_y_not_w {rel} (h : rel ∈ E.core.closure) : rel.y.2 ≠ E.freshSquare := by
  suffices ϕ E.v.2 rel.y.2 ∈ E.oldRtIds by
    by_contra hc
    apply_fun fun x => E.projectFresh (ϕ E.v.2 x) at hc
    simp [freshSquare, this] at hc
  obtain ⟨_, hb, hr⟩ := E.core.mem_closure.mp h
  apply E.oldRtIds_phi_v_2_square hb
  rw [←Relation.orbit_squares hr]
  simp [Relation.squares]

theorem Extension.new_unrelated {rel} (h : rel ∈ E.newRelation.orbit)
    : ¬∃ rel' ∈ E.core.closure, rel'.lhs = rel.lhs := by
  intro ⟨rel', hc, heq⟩
  simp [Relation.lhs] at heq
  have ⟨hx, hy⟩ := heq
  replace ⟨n, h⟩ := h
  match Mod3.of n with
  | .rem0 k hk =>
    by_cases h0 : k = 0
    · simp [hk, h0] at h
      rw [←h] at hx hy
      exact E.not_def ⟨rel', hc, hx, hy⟩
    · simp [hk, newRelation] at h
      apply_fun fun x => E.projectFresh (x.y.1) at h
      simp [w, E.oldRtIds_v_1, ←hy, E.projectFresh_closure_y_1 hc] at h
      exact h0 h
  | .rem1 k hk =>
    simp [hk, newRelation, Relation.next] at h
    apply_fun (·.y.2) at h
    simp [w, Nat.repeat] at h
    exact E.closure_y_not_w hc (hy ▸ h.symm)
  | .rem2 k hk =>
    simp [hk, newRelation, Relation.next] at h
    apply_fun (·.x.2) at h
    simp [w, Nat.repeat] at h
    exact E.closure_x_not_w hc (hx ▸ h.symm)

noncomputable def Extension.next : ChosenRelations := E.core ∪ {E.newRelation}

theorem Extension.next_func : isFunc E.next.closure := by
  simp only [isFunc, ChosenRelations.closure]
  intro rel rel' hrel hrel' h
  obtain ⟨base, hb, base_rel⟩ := E.next.mem_closure.mp hrel
  obtain ⟨base', hb', base'_rel'⟩ := E.next.mem_closure.mp hrel'
  simp [next] at hb hb'
  rcases hb, hb' with ⟨hrel | hrel, hrel' | hrel'⟩
  · apply E.func
      (E.core.mem_closure.mpr ⟨base, hrel, base_rel⟩)
      (E.core.mem_closure.mpr ⟨base', hrel', base'_rel'⟩)
      h
  · exfalso
    apply E.new_unrelated (hrel' ▸ base'_rel')
    simp [ChosenRelations.closure]
    exact ⟨rel, ⟨base, hrel, base_rel⟩, h⟩
  · exfalso
    apply E.new_unrelated (hrel ▸ base_rel)
    simp [ChosenRelations.closure]
    exact ⟨rel', ⟨base', hrel', base'_rel'⟩, h.symm⟩
  · rw [hrel] at base_rel
    rw [hrel'] at base'_rel'
    exact E.newRelation.orbit_func base_rel base'_rel' h

end Iteration


section Greedy

def PartialSolution := {core : ChosenRelations | isFunc core.closure}

theorem extend (S : PartialSolution) (u v : Rt) (heq : u.2 ≠ v.2) : ∃ S', S ≤ S' ∧ S'.val.closure.definedAt u v := by
  if not_def : S.val.closure.definedAt u v then use S else
  let E : Extension := {core := S, func := S.prop, u, v, u_neq_v := heq, not_def}
  use ⟨E.next, E.next_func⟩
  split_ands
  · intro _ _
    simp [Extension.next]
    tauto
  · exact ⟨E.newRelation, by apply ChosenRelations.le_closure; simp [Extension.next], rfl, rfl⟩

def Fn1323 (f : NePair → Rt) : Prop := ∀ p : NePair,
  ∃ p' : NePair, p'.x = p.y ∧ p'.y = f p ∧ f p' = (p.x.1 * ϕ p.x.2 p.y.2, p.x.2)

theorem exists_complete_function (seed : PartialSolution) :
    ∃ f, Fn1323 f ∧ (∀ rel, rel ∈ seed.val → f rel.lhs = rel.z) := by
  have ⟨c, hc, h1, h2, h3⟩ := exists_greedy_chain
    (fun ⟨u, v, _⟩ => {S | S.val.closure.definedAt u v})
    (fun S (⟨u, v, nonDiag⟩ : NePair) => by exact extend S u v nonDiag)
    seed
  choose F hF f hf using h3
  let inF rel := f rel.lhs = rel
  have hInF p : inF (f p) := by simp [inF, Relation.lhs, hf]
  have hf' {rel} (h : inF rel) : inF rel.next := by
    simp [Relation.lhs, Relation.next, inF]
    rw [Relation.mk.injEq]
    simp [hf]
    simp [Relation.lhs, Relation.next, inF] at h
    have hn := (hf rel.lhs).1
    apply PartialFunction.closure_next at hn
    simp [Relation.lhs, Relation.next, hf, h] at hn
    let p' : NePair := ⟨rel.y, rel.z, rel.nonDiag.2.1⟩
    let F' p : {S // S ∈ c} := ⟨F p, hF p⟩
    obtain ⟨⟨⟨S, func⟩, hS⟩, hS1, hS2⟩ := hc.directed (F' rel.lhs) (F' p')
    have hSn := ChosenRelations.closure_mono hS1 hn
    have hSfp' := ChosenRelations.closure_mono hS2 (hf p').1
    exact func hSfp' hSn (by simp [hf]) (by simp [hf])
  use fun p => (f p).z
  split_ands
  · intro p
    use (f p).next.lhs
    have := congr_arg (·.z) <| hf' (hInF p)
    simp [Relation.lhs, Relation.next, hf] at this
    simp [Relation.lhs, Relation.next, hf, this]
  · intro rel h
    obtain ⟨hc, hx, hy⟩ := hf rel.lhs
    exact (F _).prop hc ((F _).val.le_closure <| h2 _ (hF _) h) hx hy

end Greedy


inductive G where
  | square : Sq → G
  | root : Rt → G

def op (f : NePair → Rt) : G → G → G
  | .square a, .square b => .square (a + b)
  | .root x, .square b => .root (x.1 * ϕ x.2 b, x.2)
  | .square b, .root x => .root (x.1 * (ϕ x.2 b)⁻¹, x.2)
  | .root x, .root y =>
    if h : x.2 = y.2
      then .square (x.2 + invϕ x.2 (y.1⁻¹ * x.1))
      else .root (f ⟨x, y, h⟩)


theorem op_RSy_LSy_eq_Id f : (x : G) → (y : G) → op f (op f (op f y y) x) (op f y y) = x
  | .square a, .square b => by simp [op]
  | .root (x, a), .square b => by simp [op]
  | .square b, .root (x, a) => by simp [op]; rw [add_comm, ←add_assoc]; simp
  | .root (x, a), .root (y, b) => by simp [op]


@[simp] theorem f_y {f p} (h : Fn1323 f) : (f p).2 ≠ p.y.2 := by
  have ⟨p', h1, h2, h3⟩ := h p
  rw [←h1, ←h2]
  exact Ne.symm p'.nonDiag

@[simp] theorem f_x {f p} (h : Fn1323 f) : (f p).2 ≠ p.x.2 := by
  have ⟨p', h1, h2, h3⟩ := h p
  have ⟨p'', h4, h5, h6⟩ := h p'
  apply_fun Prod.snd at h3 h6
  simp at h3 h6
  rw [←h3, ←h2]
  exact Ne.symm (f_y h)

theorem roots_LyRy {x y a b f} (h : a ≠ b) (proper : Fn1323 f) :
    op f (.root (y, b)) (op f (.root (x, a)) (.root (y, b))) = .root (x * ϕ a b, a) := by
  have : b ≠ (f ⟨(x,a), (y,b), h⟩).2 := Ne.symm (f_y proper)
  simp [op, h, this]
  replace ⟨_, hx, hy, proper⟩ := proper ⟨(x, a), (y, b), h⟩
  rw [←proper]
  congr <;> simp [hx, hy]


theorem op_Ly_Ry_eq_LSy f (proper : Fn1323 f) : (x : G) → (y : G) → op f y (op f x y) = op f x (op f y y)
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


def a : Sq' := ⟨FreeAbGrpExp2.of 1, FreeAbGrpExp2.of_nonzero _⟩
def b : Sq' := ⟨FreeAbGrpExp2.of 2, FreeAbGrpExp2.of_nonzero _⟩
def b' : Sq' := ⟨FreeAbGrpExp2.of 3, FreeAbGrpExp2.of_nonzero _⟩
def c : Sq' := ⟨FreeAbGrpExp2.of 4, FreeAbGrpExp2.of_nonzero _⟩

def seed1 : Relation := .mk (1, a) (1, b) (1, c) (by simp [a, b, c]; split_ands <;> {apply FreeAbGrpExp2.of_injective'; simp})
def seed2 : Relation := .mk (1, a) (1, b') (1, c) (by simp [a, b', c]; split_ands <;> {apply FreeAbGrpExp2.of_injective'; simp})

def seed' : ChosenRelations := {seed1, seed2}
def seed : PartialSolution := .mk seed' <| by
  intro rel rel' hrel hrel' heq
  simp [Relation.lhs] at heq
  obtain ⟨base, hb, hr⟩ := seed'.mem_closure.mp hrel
  obtain ⟨base', hb', hr'⟩ := seed'.mem_closure.mp hrel'
  simp [seed', seed1, seed2] at hb hb'
  rcases hb, hb' with ⟨rfl | rfl, rfl | rfl⟩
  · apply Relation.orbit_func
    assumption
    assumption
    simp [Relation.lhs]
    assumption
  · replace ⟨n, hr⟩ := hr
    replace ⟨m, hr'⟩ := hr'
    rcases Mod3.of n, Mod3.of m with ⟨⟨k, hk⟩ | ⟨k, hk⟩ | ⟨k, hk⟩, ⟨l, hl⟩ | ⟨l, hl⟩ | ⟨l, hl⟩⟩
    repeat {
      simp [hk, hl] at hr hr'
      simp [←hr, ←hr', a, b, b', c, Nat.repeat, FreeAbGrpExp2.of_injective'] at heq
    }
    simp [hk, hl] at hr hr'
    simp [←hr, ←hr', a, b, b', c, Nat.repeat, FreeAbGrpExp2.of_injective'] at heq
    by_cases h : k = l
    · have hy := congr_arg Prod.snd heq.right
      simp [←h, RtId_mul_snd, RtId_pow_snd] at hy
      group at hy
      apply FreeGroup.pow_injective (by simp : 1 + k ≠ 0) at hy
      absurd ϕ_eq_diff_0_or_a hy
      decide
    · have hx := congr_arg Prod.snd heq.left
      simp [RtId_pow_snd] at hx
      have := Function.not_injective_iff.mpr ⟨_, _, hx, h⟩
      have := mt injective_pow_iff_not_isOfFinOrder.mpr this
      apply mt (FreeGroup.infinite_order _) at this
      simp at this
      absurd ϕ_unit_0_or_a this
      decide
  · sorry
  · apply Relation.orbit_func
    assumption
    assumption
    simp [Relation.lhs]
    assumption


/-- https://leanprover.zulipchat.com/#narrow/channel/458659-Equational/topic/1323/near/481475622 -/
@[equational_result]
theorem Equation1323_not_implies_Equation2744 :
    ∃ (G: Type) (_: Magma G), Equation1323 G ∧ ¬ Equation2744 G := by

  let ⟨f, proper, hf⟩ := exists_complete_function seed
  use G, ⟨op f⟩

  constructor
  · apply eq1323_if_conditions G _
    apply op_RSy_LSy_eq_Id f
    apply op_Ly_Ry_eq_LSy f proper
  · unfold Equation2744
    by_contra hc
    have neq : a ≠ b ∧ a ≠ b' := by simp [a, b, b', FreeAbGrpExp2.of_injective']
    have noninj : op f (.root (1, a)) (.root (1, b)) = op f (.root (1, a)) (.root (1, b')) := by
      simp [op, neq]
      have h1 := hf seed1 (by simp [seed, seed'])
      simp [Relation.lhs, seed1] at h1
      have h2 := hf seed2 (by simp [seed, seed'])
      simp [Relation.lhs, seed2] at h2
      simp [h1, h2]
    have h1 := hc (.root (1, b)) (.root (1, a))
    have h2 := hc (.root (1, b')) (.root (1, a))
    simp [Magma.op] at h1 h2
    rw [←noninj, ←h1] at h2
    simp [b, b', FreeAbGrpExp2.of_injective'] at h2


end Eq1323
