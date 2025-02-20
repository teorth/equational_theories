import equational_theories.FreshGenerator
import equational_theories.EquationalResult
import equational_theories.Equations.All
import equational_theories.Mathlib.Order.Greedy

/- Refutes the implications from 1323.

When the proof is done, update the blueprint with \lean and \leanok tags as appropriate.
-/


namespace Eq1323
noncomputable section


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
@[simp] theorem FreeAbGrpExp2.of_injective' {x y : α} : x ≠ y → FreeAbGrpExp2.of x ≠ FreeAbGrpExp2.of y :=
  mt (of_injective ·)

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
@[simp] theorem FreeAbGrpExp2.add_cancel_2 {α : Type} [inst : DecidableEq α] (x y : FreeAbGrpExp2 α) :
  x + y + y = x := by simp [FreeAbGrpExp2.add_def]
@[simp] theorem FreeAbGrpExp2.add_cancel_3 {α : Type} [inst : DecidableEq α] (x y : FreeAbGrpExp2 α) :
  y + x + y = x := by simp [FreeAbGrpExp2.add_def]
@[simp] theorem FreeAbGrpExp2.add_cancel_4 {α : Type} [inst : DecidableEq α] (x y z : FreeAbGrpExp2 α) :
  x + y + z + y = x + z := by nth_rewrite 2 [add_comm]; nth_rewrite 4 [add_comm]; simp [←add_assoc]
@[simp] theorem FreeAbGrpExp2.add_cancel_5 {α : Type} [inst : DecidableEq α] (x y z : FreeAbGrpExp2 α) :
  x + y + z + y + z = x := by nth_rewrite 2 [add_comm]; nth_rewrite 4 [add_comm]; simp [←add_assoc]

abbrev S := FreeAbGrpExp2 Nat

abbrev S' := {g : S // g ≠ 0}

instance : Infinite S' :=
  ⟨Set.infinite_of_finite_compl <| Set.compl_ne_eq_singleton _ ▸ Set.finite_singleton _⟩

inductive Sign where | plus | minus deriving DecidableEq
instance : Countable Sign where
  exists_injective_nat' := ⟨
    fun | .plus => 0 | .minus => 1,
    by intro a b; cases a <;> cases b <;> simp
  ⟩
theorem Sign.plus_or_minus (a : Sign) : a = .plus ∨ a = .minus := by cases a <;> trivial

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
  inv_mul_cancel a := by simp [sign_one, sign_inv_self]; cases a <;> simp [sign_mul]
  div_eq_mul_inv := Sign.div_eq_mul_inv

-- A corresponds to ℚˣ in the blueprint
abbrev A₀ := FreeGroup Nat
def A := Sign × A₀ deriving DecidableEq

instance : Countable A := inferInstanceAs (Countable (Sign × A₀))

instance : Group A := inferInstanceAs (Group (Sign × A₀))
instance : Neg A where neg x := ⟨.minus, 1⟩ * x
@[simp] theorem A.neg {x : A} : -x = ⟨.minus, 1⟩ * x := rfl
theorem A.mul_eta {x y : A} : (x * y) = (x.1 * y.1, x.2 * y.2) := rfl
theorem A.inv_eta {x : A} : x⁻¹ = (x.1⁻¹, x.2⁻¹) := rfl

@[simp] theorem A.mul_snd (x y : A) : (x * y).2 = x.2 * y.2 := rfl
@[simp] theorem A.pow_snd (x : A) (n : ℕ) : (x ^ n).2 = x.2 ^ n := rfl

abbrev R := A × S'

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
  repeat rw [Finset.insert_eq]
  rw [Finset.union_comm, Finset.union_assoc]

end Ingredients


section Phi

instance : Denumerable S := Denumerable.finset

def iS : S ≃ ℕ := Denumerable.eqv S

def S'_a_1 (a : S') : Set S := { x : S | iS x < iS (x + a) }
def S'_a_2 (a : S') : Set S := { x : S | iS x > iS (x + a) }

theorem S'_a_complete {a : S'} : S'_a_1 a ∪ S'_a_2 a = Set.univ := by
  simp [S'_a_1, S'_a_2, ←Set.setOf_or, a.prop]

def S'_a_1_2_equiv {a : S'} : S'_a_1 a ≃ S'_a_2 a where
  toFun x := ⟨x + a, by simp [S'_a_2]; exact x.prop⟩
  invFun x := ⟨x + a, by simp [S'_a_1]; exact x.prop⟩
  left_inv x := by simp
  right_inv x := by simp

instance {a : S'} : Infinite (S'_a_1 a) where
  not_finite h := by
    have h' : Finite (S'_a_2 a) := Finite.of_equiv _ S'_a_1_2_equiv
    have := Set.finite_union.mpr ⟨h, h'⟩
    rw [S'_a_complete, Set.finite_univ_iff] at this
    apply instInfiniteFreeAbGrpExp2.not_finite this

inductive SignS (a : S') (b : S)
  | class1 : iS b < iS (b + a) → SignS a b
  | class2 : iS (b + a) < iS b → SignS a b

def project_SignS a b : SignS a b :=
  if h : iS b < iS (b + a)
  then .class1 h
  else .class2 <| lt_of_le_of_ne' (le_of_not_lt h) (by simp [a.prop])

def ϕ₀ (a : S') : S'_a_1 a ≃ A₀ := nonempty_equiv_of_countable.some

def ϕ_offset (a : S') := (ϕ₀ a).invFun 1

def ϕ (a : S') (b : S) : A :=
  let b' := b + ϕ_offset a
  match project_SignS a b' with
  | .class1 h => ⟨.plus, ϕ₀ a ⟨b', h⟩⟩
  | .class2 h => ⟨.minus, ϕ₀ a ⟨b' + a, by simp [S'_a_1, h]⟩⟩

@[simp] abbrev ϕ' (a : S') (b : S) : A₀ := (ϕ a b).2

def invϕ (a : S') (x : A) : S :=
  let b₀ : S := (ϕ₀ a).invFun x.2 + ϕ_offset a
  match x.1 with
  | .plus => b₀
  | .minus => b₀ + a

@[simp]
theorem ϕ_0 {a : S'} : ϕ a 0 = 1 := by
  simp [ϕ, project_SignS]
  split_ifs
  case pos h => simp [ϕ_offset]; rfl
  case neg h => exfalso; exact h (ϕ_offset a).prop

theorem ϕ'_0 {a : S'} : ϕ' a 0 = 1 := by simp [ϕ']

theorem ϕ_duality {a : S'} {b : S} : ϕ a (a + b) = -ϕ a b := by
  simp [ϕ, project_SignS]
  split_ifs
  · exfalso
    rename_i h1 h2
    nth_rewrite 1 2 [add_assoc] at h1
    generalize b + ϕ_offset a = b' at h1 h2
    simp at h1 h2
    rw [add_comm] at h1
    exact not_lt_of_lt h1 h2
  · simp [A.mul_eta, sign_mul]
    apply Prod.ext <;> simp
    rw [add_assoc, add_comm]
  · simp [A.mul_eta, sign_mul]
    apply Prod.ext <;> simp
    rw [add_comm]
    simp [←add_assoc]
  · exfalso
    rename_i h1 h2
    nth_rewrite 1 2 [add_assoc] at h1
    generalize b + ϕ_offset a = b' at h1 h2
    simp at h1 h2
    absurd (eq_of_le_of_le (add_comm b' a ▸ h1) h2)
    simp [a.prop]

@[simp]
theorem ϕ_self {a : S'} : ϕ a a = -1 := by rw [←add_zero a.val, ϕ_duality]; simp

@[simp]
theorem ϕ_invϕ {a : S'} {x : A} : ϕ a (invϕ a x) = x := by
  simp [ϕ, project_SignS]
  split_ifs
  · simp [invϕ]
    rcases x.1.plus_or_minus with h | h
    · apply Prod.ext <;> simp [h]
    · exfalso
      rename_i h'
      simp [invϕ, h] at h'
      exact not_lt_of_lt h' ((ϕ₀ a).invFun x.2).prop
  · simp [invϕ]
    rcases x.1.plus_or_minus with h | h
    · exfalso
      rename_i h'
      simp only [invϕ, h, Equiv.invFun_as_coe, FreeAbGrpExp2.add_cancel_2] at h'
      exact h' ((ϕ₀ a).invFun x.2).prop
    · apply Prod.ext <;> simp [h]

@[simp]
theorem invϕ_ϕ {a : S'} {b : S} : invϕ a (ϕ a b) = b := by
  simp [ϕ, project_SignS]
  split_ifs <;> simp [invϕ]

@[simp]
theorem invϕ_0 {a : S'} : invϕ a 1 = 0 := ϕ_0 ▸ invϕ_ϕ

theorem ϕ_eq_diff_0_or_a {a : S'} {b c : S} (h : ϕ' a b = ϕ' a c) : b = c ∨ b = a + c := by
  match h1 : (ϕ a b).1, h2 : (ϕ a c).1 with
  | .plus, .plus | .minus, .minus =>
    have : ϕ a b = ϕ a c := Prod.ext (h1 ▸ h2.symm) h
    apply_fun invϕ a at this
    simp_all
  | .plus, .minus | .minus, .plus =>
    have : ϕ a b = -ϕ a c := by
      simp [Neg.neg, A.mul_eta, h2, sign_mul]
      apply Prod.ext <;> tauto
    rw [←ϕ_duality] at this
    apply_fun invϕ a at this
    simp_all

theorem ϕ_unit_0_or_a {a : S'} {b : S} (h : ϕ' a b = 1) : b = 0 ∨ b = a := by
  have := ϕ_eq_diff_0_or_a (a := a) (b := b) (c := 0)
  rw [ϕ'_0, add_zero] at this
  exact this h

end Phi


section Relations

structure Relation where
  x : R
  y : R
  z : R
  nonDiag : x.2 ≠ y.2 ∧ y.2 ≠ z.2 ∧ z.2 ≠ x.2
deriving DecidableEq

structure RelationLHS where
  x : R
  y : R
  nonDiag : x.2 ≠ y.2

def RelationLHS.toPair (p : RelationLHS) := (p.x, p.y)
theorem RelationLHS.toPair.inj : Function.Injective RelationLHS.toPair
  | ⟨x1, y1, h1⟩, ⟨x2, y2, h2⟩ => by simp [toPair]

instance : Countable RelationLHS := Function.Injective.countable RelationLHS.toPair.inj

variable {rel rel' : Relation}
variable {n m : ℕ}

def Relation.lhs : RelationLHS := ⟨rel.x, rel.y, rel.nonDiag.1⟩

def isFunc (A : Set Relation) : Prop :=
  ∀ {rel rel' : Relation}, rel ∈ A → rel' ∈ A → rel.lhs = rel'.lhs → rel.z = rel'.z

@[simp] def Relation.next (rel : Relation) : Relation :=
  ⟨rel.y, rel.z, ⟨rel.x.1 * ϕ rel.x.2 rel.y.2, rel.x.2⟩, by have := rel.nonDiag; tauto⟩

def Relation.skip : ℕ → Relation → Relation := Nat.repeat Relation.next

@[simp] theorem Relation.skip_0 : rel.skip 0 = rel := rfl
@[simp] theorem Relation.skip_succ : rel.skip n.succ = (rel.skip n).next := rfl
@[simp] theorem Relation.skip_add : rel.skip (n + m) = (rel.skip m).skip n := by
  induction n with
  | zero => simp
  | succ _ ih => simp [add_right_comm, ih]

@[simp] theorem Relation.next_3_n : rel.skip (3 * n) =
    ⟨⟨rel.x.1 * ϕ rel.x.2 rel.y.2 ^ n, rel.x.2⟩,
     ⟨rel.y.1 * ϕ rel.y.2 rel.z.2 ^ n, rel.y.2⟩,
     ⟨rel.z.1 * ϕ rel.z.2 rel.x.2 ^ n, rel.z.2⟩, rel.nonDiag⟩ := by
  induction n with
  | zero => simp
  | succ _ hi => simp [mul_add, hi]; group; trivial

def Relation.orbit : Set Relation := { rel.skip n | n : ℕ }

theorem Relation.orbit_self : rel ∈ rel.orbit := ⟨0, by simp⟩

theorem Relation.orbit_next : rel ∈ rel'.orbit → rel.next ∈ rel'.orbit := by
  intro ⟨n, hn⟩
  use 1 + n
  simp [hn]

theorem Relation.orbit_func' (n : ℕ) (h : (rel.skip n).lhs = rel.lhs) : n = 0 := by
  have := rel.nonDiag
  match Mod3.of n with
  | .rem0 k hk =>
    cases Nat.eq_zero_or_pos k with
    | inl hz => simp [hk, hz]
    | inr hp =>
      have : ϕ' rel.x.2 rel.y.2 ^ k = 1 := by
        simp [hk, lhs] at h
        replace h := congr_arg (Prod.snd ∘ Prod.fst) h.left
        simpa using h
      have : ϕ' rel.x.2 rel.y.2 = 1 :=
        not_imp_not.mp (FreeGroup.infinite_order _) <| isOfFinOrder_iff_pow_eq_one.mpr ⟨k, hp, this⟩
      apply ϕ_unit_0_or_a at this
      simp [rel.y.2.prop] at this
      apply Subtype.eq at this
      tauto
  | .rem1 k hk | .rem2 k hk =>
    simp [hk, lhs] at h
    replace h := congr_arg Prod.snd h.right
    tauto

theorem Relation.orbit_func : isFunc rel.orbit := by
  intro rel rel' ⟨n, hrel⟩ ⟨n', hrel'⟩ h
  wlog hn : n ≤ n'
  · symm; exact this _ hrel' _ hrel h.symm (Nat.le_of_not_le hn)
  rcases Nat.lt_or_eq_of_le hn with hn | hn
  · exfalso
    have : n' = (n' - n) + n := by simp [Nat.sub_add_eq_max, le_of_lt, hn]
    rw [this] at hrel'
    apply_fun (·.lhs) at hrel'
    simp [hrel, ←h] at hrel'
    exact Nat.sub_ne_zero_of_lt hn (rel.orbit_func' _ hrel')
  · simp [←hrel, ←hrel', hn]

abbrev Relation.squares : Finset S' := {rel.x.2, rel.y.2, rel.z.2}

theorem Relation.orbit_squares {rel'} (h : rel' ∈ rel.orbit) : rel'.squares = rel.squares := by
  obtain ⟨n, h⟩ := h
  apply_fun (·.squares) at h
  unfold squares at h ⊢
  match Mod3.of n with
  | .rem0 k hk => simp [hk] at h; simp [h]
  | .rem1 k hk => simp [hk] at h; rw [←Finset.eq_rot3] at h; simp [h]
  | .rem2 k hk => simp [hk] at h; rw [Finset.eq_rot3] at h; simp [h]

def closure (F : Finset Relation) : Set Relation := { rel' | ∃ rel ∈ F, rel' ∈ rel.orbit }

theorem le_closure (F : Finset Relation) : F.toSet ≤ closure F := by
  intro rel h
  simp [closure]
  exact ⟨rel, h, rel.orbit_self⟩

theorem closure_mono {F1 F2 : Finset Relation} (h : F1 ≤ F2) :
    closure F1 ≤ closure F2 := by
  intro _ ⟨_, h1, h2⟩
  exact ⟨_, h h1, h2⟩

def definedAt (F : Set Relation) (p : RelationLHS) : Prop := ∃ rel ∈ F, rel.lhs = p

theorem closure_next (F : Finset Relation) {rel : Relation}
    (h : rel ∈ closure F) : rel.next ∈ closure F := by
  obtain ⟨base, hb, hr⟩ := h
  apply Relation.orbit_next at hr
  use base

end Relations


section Greedy

class Extension where
  core : Finset Relation
  func : isFunc (closure core)
  p : RelationLHS
  not_def : ¬definedAt (closure core) p

namespace Extension
variable [Extension]

def oldSquares : Finset S' := {p.x.2, p.y.2} ∪ core.biUnion fun a => a.squares

@[local simp] theorem mem_oldSquares_p_x_2 : p.x.2 ∈ oldSquares := by simp [oldSquares]
@[local simp] theorem mem_oldSquares_p_y_2 : p.y.2 ∈ oldSquares := by simp [oldSquares]
@[local simp] theorem mem_oldSquares_core_squares {rel} (h : rel ∈ core) : rel.squares ⊆ oldSquares := by
  intro a ha
  simp [Relation.squares] at ha
  simp [oldSquares]
  right; right
  use rel, h

@[local simp] theorem mem_oldSquares_closure {rel} (h : rel ∈ closure core) : rel.squares ⊆ oldSquares := by
  intro a ha
  obtain ⟨rel', hb, hr⟩ := h
  rw [Relation.orbit_squares hr] at ha
  simp only [oldSquares, Finset.insert_union, Finset.mem_insert, Finset.mem_union]
  simp only [Finset.mem_biUnion]
  right; right
  use rel'

def old : Finset A₀ :=
  let fromValues := {p.x.1.2, p.y.1.2} ∪ core.biUnion fun a => {a.x.1.2, a.y.1.2, a.z.1.2}
  let fromPhis := (oldSquares ×ˢ oldSquares).image fun (x, y) => ϕ' x y
  fromValues ∪ fromPhis

@[local simp] theorem mem_old_p_x_1_2 : p.y.1.2 ∈ old := by simp [old]
@[local simp] theorem mem_old_p_y_1_2 : p.y.1.2 ∈ old := by simp [old]

@[local simp] theorem mem_old_core_xyz_1_2 {rel} (h : rel ∈ core)
    : rel.x.1.2 ∈ old ∧ rel.y.1.2 ∈ old ∧ rel.z.1.2 ∈ old := by
  simp [old]
  split_ands <;> { right; right; left; use rel; simp [h] }

@[local simp] theorem mem_old_ϕ_oldSquares_oldSquares {a b} (ha : a ∈ oldSquares) (hb : b ∈ oldSquares)
    : ϕ' a b ∈ old := by
  simp [old]
  right; right; right
  use a, a.prop, b
  simp [ha, hb, a.prop, b.prop]

abbrev freshA : A := ⟨.plus, FreeGroup.of <| FreshGenerator.freshGeneratorName old⟩
abbrev w : R := ⟨1, ⟨invϕ p.y.2 freshA, by apply_fun ϕ' p.y.2; simp⟩⟩

def projectFresh (x : A) : ℤ := FreshGenerator.projectFresh old x.2

@[local simp] theorem projectFresh_1 : projectFresh 1 = (0 : ℤ) := rfl
@[local simp] theorem projectFresh_mul {x y} : projectFresh (x * y) = projectFresh x + projectFresh y := by simp [projectFresh]; rfl
@[local simp] theorem projectFresh_pow {x} {n : ℕ} : projectFresh (x ^ n) = n * projectFresh x := by simp [projectFresh]; rfl

@[local simp] theorem projectFresh_old {r : A} : r.2 ∈ old → projectFresh r = 0 := FreshGenerator.projectFresh_old
@[local simp] theorem projectFresh_freshA : projectFresh freshA = 1 := by simp [projectFresh, ←FreshGenerator.freshGenerator.eq_1]

@[local simp] theorem projectFresh_closure_y_1 {rel} (h : rel ∈ closure core) : projectFresh rel.y.1 = 0 := by
  obtain ⟨rel', hb, ⟨n, hr⟩⟩ := h
  have Int.succ_mul {n m : ℤ} : (n + 1) * m = n * m + m := by ring
  rcases Mod3.of n with ⟨k, hk⟩ | ⟨k, hk⟩ | ⟨k, hk⟩
  repeat {
    simp [←hr, hk, hb, ←Int.succ_mul]
    right
    apply FreshGenerator.projectFresh_old
    apply mem_old_ϕ_oldSquares_oldSquares <;> { apply mem_oldSquares_core_squares hb; simp [Relation.squares] }
  }

def newRelation : Relation := .mk p.x p.y w <| by
  split_ands
  · exact p.nonDiag
  · apply_fun fun a => ϕ' p.y.2 a.val
    simp
  · apply_fun fun a => projectFresh (ϕ p.y.2 a.val)
    simp

theorem newRelation_lhs {rel} (h : rel ∈ newRelation.orbit)
    : ¬∃ rel' ∈ closure core, rel'.lhs = rel.lhs := by
  intro ⟨rel', hc, heq⟩
  simp [Relation.lhs] at heq
  have ⟨hx, hy⟩ := heq
  replace ⟨n, h⟩ := h
  match Mod3.of n with
  | .rem0 k hk =>
    suffices k = 0 by
      apply not_def
      use rel'
      simp [hc, hx, hy, ←h, newRelation, hk, this, Relation.lhs]
    apply_fun fun a => projectFresh a.y.1 at h
    simpa [←hy, hk, newRelation, w,  hc] using h
  | .rem1 k hk =>
    have : rel'.y.2 ∈ oldSquares := by apply mem_oldSquares_closure hc; simp [Relation.squares]
    apply_fun fun a => projectFresh (ϕ p.y.2 a.y.2) at h
    simp [←hy, hk, newRelation, w, this] at h
  | .rem2 k hk =>
    have : rel'.x.2 ∈ oldSquares := by apply mem_oldSquares_closure hc; simp [Relation.squares]
    apply_fun fun a => projectFresh (ϕ p.y.2 a.x.2) at h
    simp [←hx, hk, newRelation, w, this] at h

def next : Finset Relation := core ∪ {newRelation}

theorem next_func : isFunc (closure next) := by
  intro rel rel' ⟨base, hb, base_rel⟩ ⟨base', hb', base'_rel'⟩ h
  simp only [next, Finset.mem_union, Finset.mem_singleton] at hb hb'
  rcases hb, hb' with ⟨hrel | hrel, hrel' | hrel'⟩
  · exact func ⟨base, hrel, base_rel⟩ ⟨base', hrel', base'_rel'⟩ h
  · exfalso
    apply newRelation_lhs (hrel' ▸ base'_rel')
    have : rel ∈ closure core := ⟨base, hrel, base_rel⟩
    use rel
  · exfalso
    apply newRelation_lhs (hrel ▸ base_rel)
    have : rel' ∈ closure core := ⟨base', hrel', base'_rel'⟩
    symm at h
    use rel'
  · exact newRelation.orbit_func (hrel ▸ base_rel) (hrel' ▸ base'_rel') h

end Extension


def PartialSolution := { core : Finset Relation | isFunc (closure core) }

theorem extend (S : PartialSolution) (p : RelationLHS) (not_def : ¬definedAt (closure S.val) p)
    : ∃ S', S ≤ S' ∧ definedAt (closure S'.val) p := by
  let E : Extension := {core := S, func := S.prop, p, not_def}
  use ⟨E.next, E.next_func⟩
  split_ands
  · intro _ _
    simp [Extension.next]
    tauto
  · exact ⟨E.newRelation, by apply le_closure; simp [Extension.next], rfl⟩

def Fn1323 (f : RelationLHS → R) : Prop := ∀ p : RelationLHS,
  ∃ p' : RelationLHS, p'.x = p.y ∧ p'.y = f p ∧ f p' = (p.x.1 * ϕ p.x.2 p.y.2, p.x.2)

theorem exists_complete_function (seed : PartialSolution) :
    ∃ f, Fn1323 f ∧ (∀ rel, rel ∈ seed.val → f rel.lhs = rel.z) := by
  have ⟨c, hc, h1, h2, h3⟩ := exists_greedy_chain
    (fun p => {S | definedAt (closure S.val) p})
    (fun S (p : RelationLHS) => by
     if h : definedAt (closure S.val) p
       then use S; simp [h]
       else exact extend S p h)
    seed
  choose F hF f hf using h3
  let hf' p : (f p).x = p.x ∧ (f p).y = p.y := RelationLHS.mk.injEq .. ▸ (hf p).2
  let inF rel := f rel.lhs = rel
  have hInF p : inF (f p) := by simp [inF, hf]
  have hn {rel} (h : inF rel) : inF rel.next := by
    let F' p : {S // S ∈ c} := ⟨F p, hF p⟩
    obtain ⟨⟨⟨S, func⟩, hS⟩, hS1, hS2⟩ := hc.directed (F' rel.next.lhs) (F' rel.lhs)
    have hval := closure_mono hS1 (hf _).1
    have hnext := closure_mono hS2 <| closure_next _ (hf _).1
    simp [Relation.lhs, Relation.next, inF] at h
    simp [Relation.lhs, Relation.next, hf, h] at hnext
    simp [inF, Relation.lhs]
    rw [Relation.mk.injEq]
    simp [hf']
    exact func hval hnext (hf _).2
  use fun p => (f p).z
  split_ands
  · intro p
    use (f p).next.lhs
    have := congr_arg (·.z) <| hn (hInF p)
    simp_all [Relation.lhs]
  · intro _ h
    exact (F _).prop (hf _).1 (le_closure (F _).val <| h2 _ (hF _) h) (hf _).2

end Greedy


inductive G where
  | square : S → G
  | root : R → G

def op (f : RelationLHS → R) : G → G → G
  | .square a, .square b => .square (a + b)
  | .root x, .square b => .root (x.1 * ϕ x.2 b, x.2)
  | .square b, .root x => .root (x.1 * (ϕ x.2 b)⁻¹, x.2)
  | .root x, .root y =>
    if h : x.2 = y.2
      then .square (x.2 + invϕ x.2 (y.1⁻¹ * x.1))
      else .root (f ⟨x, y, h⟩)


theorem op_RSy_LSy_eq_Id f x y : op f (op f (op f y y) x) (op f y y) = x := by
  cases x <;> cases y <;> simp [op]


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
  | .square a, .square b => by simp [op, ←add_assoc]
  | .root (x, a), .square b => by simp [op, mul_assoc]
  | .square b, .root (x, a) => by simp [op]; apply add_comm
  | .root (x, a), .root (y, b) =>
    if h : a = b
    then by
      simp [op, h, ϕ_duality]
      apply Prod.ext <;> {
        simp only [A.mul_eta, A.inv_eta]
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


def a : S' := ⟨FreeAbGrpExp2.of 1, FreeAbGrpExp2.of_nonzero _⟩
def b : S' := ⟨FreeAbGrpExp2.of 2, FreeAbGrpExp2.of_nonzero _⟩
def b' : S' := ⟨FreeAbGrpExp2.of 3, FreeAbGrpExp2.of_nonzero _⟩
def c : S' := ⟨FreeAbGrpExp2.of 4, FreeAbGrpExp2.of_nonzero _⟩

def seed1 : Relation := .mk (1, a) (1, b) (1, c) (by simp [a, b, c])
def seed2 : Relation := .mk (1, a) (1, b') (1, c) (by simp [a, b', c])

theorem seed_lhs_disjoint (n m : ℕ) : (seed1.skip n).lhs ≠ (seed2.skip m).lhs := by
  intro heq
  simp [Relation.lhs] at heq
  have hx := congr_arg Prod.snd heq.left
  have hy := congr_arg Prod.snd heq.right
  rcases Mod3.of n, Mod3.of m with ⟨⟨k, hk⟩ | ⟨k, hk⟩ | ⟨k, hk⟩, ⟨l, hl⟩ | ⟨l, hl⟩ | ⟨l, hl⟩⟩
  repeat simp [hk, hl, seed1, seed2, a, b, b', c] at hx hy
  -- Remaining case: n = m = 2  (mod 3)
  have hx := congr_arg (Prod.snd ∘ Prod.fst) heq.left
  have hy := congr_arg (Prod.snd ∘ Prod.fst) heq.right
  simp [hk, hl, seed1, seed2] at hx hy
  group at hy
  have : ϕ' c a ≠ 1 := by
    apply mt ϕ_unit_0_or_a
    decide
  have k_eq_l : k = l :=
    (injective_pow_iff_not_isOfFinOrder.mpr (FreeGroup.infinite_order _ this)) hx
  have hl : (1 : ℤ) + l ≠ 0 := by
    apply ne_of_gt
    rw [←Int.ofNat_eq_natCast, add_comm, ←Int.succ]
    apply Int.succ_ofNat_pos
  rw [k_eq_l, ←FreeGroup.zpow_injective hl] at hy
  · absurd ϕ_eq_diff_0_or_a hy
    decide

def seed : PartialSolution := .mk {seed1, seed2} <| by
  intro rel rel' ⟨base, hb, n, hr⟩ ⟨base', hb', n', hr'⟩ heq
  simp [seed1, seed2] at hb hb'
  rcases hb, hb' with ⟨rfl | rfl, rfl | rfl⟩
  · apply Relation.orbit_func ⟨n, hr⟩ ⟨n', hr'⟩ heq
  · exfalso
    rw [←hr, ←hr'] at heq
    apply seed_lhs_disjoint n n' heq
  · exfalso
    rw [←hr, ←hr'] at heq
    apply seed_lhs_disjoint n' n heq.symm
  · apply Relation.orbit_func ⟨n, hr⟩ ⟨n', hr'⟩ heq


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
    have neq : a ≠ b ∧ a ≠ b' := by simp [a, b, b']
    have noninj : op f (.root (1, a)) (.root (1, b)) = op f (.root (1, a)) (.root (1, b')) := by
      simp [op, neq]
      have h1 := hf seed1 (by simp [seed])
      simp [Relation.lhs, seed1] at h1
      have h2 := hf seed2 (by simp [seed])
      simp [Relation.lhs, seed2] at h2
      simp [h1, h2]
    by_contra hc
    have h1 := hc (.root (1, b)) (.root (1, a))
    have h2 := hc (.root (1, b')) (.root (1, a))
    simp [Magma.op] at h1 h2
    rw [←noninj, ←h1] at h2
    simp [b, b'] at h2

end
end Eq1323
