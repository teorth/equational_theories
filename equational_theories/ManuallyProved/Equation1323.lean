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
-- Define the direct sum of copies of Z/2, the sign group, type for roots, and ϕ

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
instance : Infinite Sq' := sorry

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

abbrev Rt := Rt' × Sq'
instance : DecidableEq Rt' := inferInstanceAs (DecidableEq (Sign × FreeGroup Nat))
instance : DecidableEq Rt := inferInstance
instance : Countable Rt' := inferInstanceAs (Countable (Sign × FreeGroup Nat))
-- def Rt.square (x : Rt) : Sq := x.2.val

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


section Iteration

abbrev PartialFunction := Rt → Rt → Rt → Prop

def offset (x y : Rt) (n : Nat) : Rt := (x.1 * (ϕ x.2 y.2)^n, x.2)

@[simp] theorem offset_0 (x y : Rt) : offset x y 0 = x := by simp [offset]
@[simp] theorem offset_2 (x y : Rt) (n : Nat) : (offset x y n).2 = x.2 := by simp [offset]

def related (x y z : Rt) : Set (Rt × Rt × Rt) :=
  ⋃ n : Nat, {
    (offset x y n, offset y z n, offset z x n),
    (offset y z n, offset z x n, offset x y (n+1)),
    (offset z x n, offset x y (n+1), offset y z (n+1))
  }
def related' : Rt × Rt × Rt → Set (Rt × Rt × Rt) | (x, y, z) => related x y z

theorem self_in_related {x y z : Rt} : (x, y, z) ∈ related x y z :=
  Set.mem_iUnion.mpr ⟨0, by simp⟩

def PartialFunction.graph (F : PartialFunction) : Set (Rt × Rt × Rt) := {(x, y, z) | F x y z}

def PartialFunction.closureSet (F : PartialFunction) : Set (Rt × Rt × Rt) :=
  ⋃ x : F.graph, related' x.val

def PartialFunction.closure (F : PartialFunction) : PartialFunction :=
  fun x y z => (x, y, z) ∈ F.closureSet

theorem PartialFunction.closure_graph_eq_closureSet (F : PartialFunction) :
  F.closure.graph = F.closureSet := rfl

def PartialFunction.isFunc (F : PartialFunction) : Prop := ∀ x y z z', F x y z → F x y z' → z = z'

theorem PartialFunction.le_closure (F : PartialFunction) : F ≤ F.closure := by
  intro x y z h
  apply Set.mem_iUnion.mpr
  exact ⟨⟨(x, y, z), h⟩, self_in_related⟩

theorem PartialFunction.graph_mono (F1 F2 : PartialFunction) (h : F1 ≤ F2) : F1.graph ⊆ F2.graph := by
  solve_by_elim [h]

theorem PartialFunction.closure_mono (F1 F2 : PartialFunction) (h : F1 ≤ F2) :
    F1.closure ≤ F2.closure := by
  unfold closure closureSet
  simp
  intro x y z h
  sorry

theorem PartialFunction.closure_idem (F : PartialFunction) : F.closure.closure = F.closure := by
  ext x y z
  sorry

theorem PartialFunction.closure_LyRy (x y z w : Rt) (F : PartialFunction) (hc : F = F.closure)
    (h1 : F x y z) (h2 : F y z w) (hne : z.2 ≠ y.2) : w = (x.1 * ϕ x.2 ↑y.2, x.2) := by
  sorry

def PartialFunction.squares (F : PartialFunction) : Set Sq' :=
  ⋃₀ F.graph.image fun (x, y, z) => {x.2, y.2, z.2}

def PartialFunction.aux_cond (F : PartialFunction) := ∀ x y z, F.closure x y z → z.2 ≠ y.2

structure Extension where
  core : PartialFunction
  finite : core.graph.Finite
  func : core.closure.isFunc
  aux : core.aux_cond
  u : Rt
  v : Rt
  not_def : ∀ z, ¬core.closure u v z

def tupleSquares : Rt × Rt × Rt → Finset Sq' | (x, y, z) => {x.2, y.2, z.2}

def Extension.oldSquares (E : Extension) : Set Sq' :=
  {E.u.2, E.v.2} ∪ ⋃ x ∈ E.core.closure.graph, tupleSquares x

theorem Extension.oldSquares_direct (E : Extension) :
    ⋃ x ∈ E.core.closure.graph, tupleSquares x = (E.finite.toFinset.biUnion tupleSquares).toSet := by
  apply Set.ext
  intro x
  constructor
  · sorry
  · intro h
    sorry

theorem Extension.oldSquaresFinite (E : Extension) : (E.oldSquares).Finite := by
  simp [oldSquares]
  rw [oldSquares_direct E]
  apply Finset.finite_toSet

noncomputable def Extension.squares (E : Extension) : Finset Sq' :=
  {E.u.2, E.v.2} ∪ E.oldSquaresFinite.toFinset

def Extension.freshSquare (E : Extension) : ∃ s : Sq', s ∉ E.squares := Finset.exists_not_mem _

noncomputable def Extension.freshRoot (E : Extension) : Rt := (1, E.freshSquare.choose)

def Extension.next (E : Extension) : PartialFunction :=
  fun x y z => E.core x y z ∨ x = E.u ∧ y = E.v ∧ z = E.freshRoot

theorem Extension.next_finite (E : Extension) : E.next.graph.Finite := by
  unfold PartialFunction.graph Extension.next
  simp only [Set.setOf_or, Set.finite_union]
  exact ⟨E.finite, by simp [←Prod.mk.injEq]⟩

theorem Extension.next_func (E : Extension) : E.next.closure.isFunc := by
  sorry

theorem Extension.next_aux (E : Extension) : E.next.aux_cond := by
  sorry

end Iteration


section Greedy

def PartialSolution := {core : PartialFunction | core.graph.Finite ∧ core.closure.isFunc ∧ core.aux_cond }

theorem extend (S : PartialSolution) (u v : Rt) : ∃ S', S ≤ S' ∧ ∃ z, S'.val.closure u v z := by
  by_cases h : ∃ z, S.val.closure u v z
  · use S
  have ⟨core, finite, func, aux⟩ := S
  let E : Extension := {core, finite, func, aux, u, v, not_def := forall_not_of_not_exists h}
  use ⟨E.next, E.next_finite, E.next_func, E.next_aux⟩
  split_ands
  · tauto
  · use E.freshRoot
    apply PartialFunction.le_closure
    tauto

def Fn1323 (f : Rt → Rt → Rt) : Prop := ∀ x y,
  x.2 ≠ y.2 → (f x y).2 ≠ y.2 ∧ f y (f x y) = (x.1 * ϕ x.2 y.2, x.2)

theorem exists_complete_function (seed : PartialSolution) :
    ∃ f, Fn1323 f ∧ (∀ {x y z}, seed.val x y z → f x y = z) := by
  have ⟨c, hc, h1, h2, h3⟩ := exists_greedy_chain
    (fun (x, y) => {S | ∃ z, S.val.closure x y z}) (fun S (u, v) => extend S u v) seed
  replace h3 : ∀ x y, _ := fun x y => h3 (x, y)
  choose F hF f hf using h3
  refine ⟨f, fun {x y} h => ?_, fun {x y z} h => ?_⟩
  · let F' x y : {S // S ∈ c} := ⟨F x y, hF x y⟩
    obtain ⟨⟨S, hS⟩, hS1, hS2⟩ := hc.directed (F' x y) (F' y (f x y))
    split_ands
    · exact S.prop.2.2 _ _ (f ..) ((F ..).val.closure_mono _ hS1 _ _ _ (hf ..))
    · have val1 := (F ..).val.closure_mono _ hS1 _ _ _ (hf ..)
      have val2 := (F ..).val.closure_mono _ hS2 _ _ _ (hf ..)
      exact S.val.closure.closure_LyRy _ _ _ _ S.val.closure_idem.symm val1 val2 (S.2.2.2 _ _ _ val1)
  · exact (F ..).2.2.1 _ _ _ _ (hf ..) ((F ..).1.le_closure _ _ _ (h2 _ (hF ..) _ _ _ h))

end Greedy


inductive G where
  | square : Sq → G
  | root : Rt → G

def op (f : Rt → Rt → Rt) : G → G → G
  | .square a, .square b => .square (a + b)
  | .root x, .square b => .root (x.1 * ϕ x.2 b, x.2)
  | .square b, .root x => .root (x.1 * (ϕ x.2 b)⁻¹, x.2)
  | .root x, .root y =>
    if x.2 = y.2
      then .square (x.2 + invϕ x.2 (y.1⁻¹ * x.1))
      else .root (f x y)


theorem op_RSy_LSy_eq_Id f : (x : G) → (y : G) → op f (op f (op f y y) x) (op f y y) = x
  | .square a, .square b => by simp [op]
  | .root (x, a), .square b => by simp [op]
  | .square b, .root (x, a) => by simp [op]; rw [add_comm, ←add_assoc]; simp
  | .root (x, a), .root (y, b) => by simp [op]


theorem roots_LyRy {x y a b f} (h : a ≠ b) (proper : Fn1323 f) :
    op f (.root (y, b)) (op f (.root (x, a)) (.root (y, b))) = .root (x * ϕ a b, a) := by
  replace proper := proper (x, a) (y, b) h
  simp [op, h, proper, proper.1.symm]

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
  -- λ x y => (h2 ((y ◇ y) ◇ x) y ▸ h1 x y).symm


def seed : PartialSolution := sorry


/-- https://leanprover.zulipchat.com/#narrow/channel/458659-Equational/topic/1323/near/481475622 -/
-- @[equational_result]
theorem Equation1323_not_implies_Equation2744 :
    ∃ (G: Type) (_: Magma G), Equation1323 G ∧ ¬ Equation2744 G := by

  let ⟨f, proper, hf⟩ := exists_complete_function seed
  use G, ⟨op f⟩

  constructor
  · apply eq1323_if_conditions G _
    apply op_RSy_LSy_eq_Id f
    apply op_Ly_Ry_eq_LSy f proper
  · sorry


end Eq1323
