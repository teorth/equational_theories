import equational_theories.Mathlib.Data.List.Defs
import equational_theories.Mathlib.Order.Greedy
import Mathlib.Data.Finset.Order
import Mathlib.Data.Prod.Lex
import Mathlib.Data.List.AList
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Functor
import Mathlib.Tactic.DeriveFintype

import equational_theories.Equations.All
import equational_theories.FactsSyntax

import Mathlib.Data.FinEnum

namespace Eq1076
namespace Greedy
noncomputable section

--TODO: find better name
def adjoinFresh' {F : Type} [fE: FinEnum F]: ℕ ≃ ℕ ⊕ F where
  toFun n := if h: n < fE.card then .inr $ fE.equiv.symm ⟨n,h⟩ else .inl $ n - fE.card
  invFun a := match a with
  | .inl n => n + fE.card
  | .inr f => fE.equiv f
  left_inv n := by
    simp only
    split
    case h_1 h =>
      split at h
      · injection h
      · injection h
        omega
    case h_2 h =>
      split at h
      · injection h with h
        rw [← h]
        simp
      · injection h
  right_inv a := by cases a <;> simp

def adjoinFresh {F : Type} (e : ℕ ≃ ℕ ⊕ F) (m : ℕ) : ℕ ≃ ℕ ⊕ F where
  toFun n := if n < m then .inl n else match e (n - m) with
    | .inl k => .inl (k + m)
    | .inr c => .inr c
  invFun
    | .inl k => if k < m then k else e.symm (.inl (k-m)) + m
    | .inr c => e.symm (.inr c) + m
  left_inv n := by
    dsimp
    by_cases h : n < m
    · simp [h]
    · simp [h]
      split
      cases h' : e (n -m)
      next k' eq' k'' =>
        rw [h'] at eq'
        simp only [Sum.inl.injEq] at eq'
        rw [← eq']
        have  : ¬ k'' + m < m := by omega
        simp only [this, ↓reduceIte, Nat.add_sub_cancel]
        rw [← h']
        simp only [Equiv.symm_apply_apply]
        omega
      · simp_all
      next h' =>
        split at h'
        · simp_all
        next h'' =>
          rw [← h',← h'']
          simp only [Equiv.symm_apply_apply]
          omega
  right_inv a := by
    cases a
    case inl n =>
      simp only
      by_cases h : n < m
      · simp [h]
      · simp only [h, ↓reduceIte, Nat.add_sub_cancel, Equiv.apply_symm_apply]
        have : ¬ (e.symm (Sum.inl (n - m)) + m < m) := by omega
        simp only [this, ↓reduceIte, Sum.inl.injEq]
        omega
    case inr => simp

theorem adjoinFresh_fixed {F : Type} {e : ℕ ≃ ℕ ⊕ F} {m k: ℕ} (h : k  < m) :
  adjoinFresh e m k = .inl k := by unfold adjoinFresh ; simp [h]

theorem adjoinFresh_fixed' {F : Type} {e : ℕ ≃ ℕ ⊕ F} {m k: ℕ} (h : k  < m) :
  (adjoinFresh e m).symm (.inl k) = k := by unfold adjoinFresh ; simp [h]

abbrev PreExtension (α : Type) := α → α → Set α

structure PreExtension.OK {α : Type} (E : PreExtension α) : Prop where
  finite : Set.Finite {x : (α × α) × α | x.2 ∈ E x.1.1 x.1.2}
  func {x y} : Set.Subsingleton (E x y)
  eq1076 {x y xy xxy} : xy ∈ E x y → xxy ∈ E x xy → ∃xxyy, xxyy ∈ E xxy y ∧ x ∈ E y xxyy
  not_idempotent {x} : x ∉ E x x

private abbrev Equiv.movePreExtension {α β : Type} (e : α ≃ β) (E : PreExtension β) : PreExtension α :=
  fun a b => { c | e c ∈ E (e a) (e b) }

def Equiv.movePreExtensionOK {α β : Type} (e : α ≃ β) (E : PreExtension β) (ok : E.OK) :
  (Equiv.movePreExtension e E).OK where
  finite := by
    apply ok.finite.of_equiv
    constructor
    case toFun =>
      refine fun ⟨((a,b),c),h⟩ => ⟨((e.symm a, e.symm b),e.symm c),?_⟩
      simp_all
    case invFun =>
      refine fun ⟨((a,b),c),h⟩ => ⟨((e a, e b),e c),?_⟩
      simp_all
    case left_inv =>
      refine fun ⟨((a,b),c),h⟩ => ?_
      simp_all
    case right_inv =>
      refine fun ⟨((a,b),c),h⟩ => ?_
      simp_all
  func {x y} z z_mem z' z'_mem := by
    have := ok.func z_mem z'_mem
    simpa
  eq1076 xy_mem xxy_mem := by
    obtain ⟨xxyy, xxyy_mem, eq⟩ := ok.eq1076 xy_mem xxy_mem
    exact ⟨e.symm xxyy, by simpa using xxyy_mem, by simpa using eq⟩
  not_idempotent h := by simpa using ok.not_idempotent (by simpa using h)



abbrev Extension α:= {E : PreExtension α // E.OK}

class ExtensionBase where
  E : PreExtension ℕ
  ok : E.OK
  a : ℕ
  b : ℕ
  not_def {c} : c ∉ E a b

namespace ExtensionBase
variable [ExtensionBase]

-- Not show how to call this
structure FreshSolution (F : Type) (E' : PreExtension (ℕ ⊕ F)) : Prop where
  base {a b c} : c ∈ E a b → (.inl c) ∈ E' (.inl a) (.inl b)
  ok : E'.OK
  ab_def : (E' (.inl a) (.inl b)).Nonempty

abbrev FreshExtension (F : Type) := {E' : PreExtension (ℕ ⊕ F) // FreshSolution F E'}

scoped infix:80 " ◯ " => E
def dom : Finset ℕ :=
  insert a <| insert b <| ok.finite.toFinset.biUnion fun ((a, b), c) => {a, b, c}

theorem mem_dom {a b c x}
    (h1 : c ∈ a ◯ b) (h2 : x ∈ ({a, b, c} : Finset ℕ)) : x ∈ dom := by
  refine Finset.mem_insert_of_mem <| Finset.mem_insert_of_mem ?_
  simp only [dom, Finset.mem_biUnion, Set.Finite.mem_toFinset, Set.mem_setOf_eq, Prod.exists]
  exact ⟨_, _, _, h1, h2⟩

@[scoped aesop safe forward]
theorem dom_l {a b c} (h : c ∈ a ◯ b) : a ∈ dom := mem_dom h (by simp)
@[scoped aesop safe forward]
theorem dom_r {a b c} (h : c ∈ a ◯ b) : b ∈ dom := mem_dom h (by simp)
@[scoped aesop safe forward]
theorem dom_o {a b c} (h : c ∈ a ◯ b) : c ∈ dom := mem_dom h (by simp)
@[scoped aesop safe forward]
theorem dom_a : a ∈ dom := Finset.mem_insert_self ..
@[scoped aesop safe forward]
theorem dom_b : b ∈ dom := Finset.mem_insert_of_mem <| Finset.mem_insert_self ..

def dom_bound := dom.sup id + 1

theorem lt_dom_bound {x} (h : x ∈ dom) : x < dom_bound := Nat.lt_succ.2 <| dom.le_sup (f := id) h

namespace FreshExtension

variable {F : Type} [FinEnum F] (E' : FreshExtension F)

def adjoin : PreExtension ℕ :=
  Equiv.movePreExtension (adjoinFresh adjoinFresh' dom_bound) E'.1

theorem adjoin_ok : E'.adjoin.OK :=
  Equiv.movePreExtensionOK (adjoinFresh adjoinFresh' dom_bound) E'.1 E'.2.ok

theorem adjoin_le : E ≤ E'.adjoin := by
  intro a b c h
  unfold adjoin Equiv.movePreExtension
  simp only [Set.mem_setOf_eq]
  unfold adjoinFresh
  simp only [Equiv.coe_fn_mk, lt_dom_bound (dom_l h), ↓reduceIte, lt_dom_bound (dom_r h),
    lt_dom_bound (dom_o h)]
  exact E'.2.base h

theorem adjoin_ab_def :
  E'.adjoin ∈ { e : (PreExtension ℕ) | Nonempty (e a b)} := by
  obtain ⟨c, c_mem⟩ := E'.2.ab_def
  use ((adjoinFresh adjoinFresh' dom_bound).symm c)
  unfold adjoin Equiv.movePreExtension
  simp only [Set.mem_setOf_eq, Equiv.apply_symm_apply]
  unfold adjoinFresh
  simp [lt_dom_bound dom_a, lt_dom_bound dom_b, c_mem]

end FreshExtension
end ExtensionBase

--no extra assumptions, keep this to be consistent with other methods
class Extension1 extends ExtensionBase where


namespace Extension1
variable [Extension1]
open ExtensionBase

/-- We use `F := Unit ⊕ Fin dom_bound ⊕ Fin dom_bound` for our fresh variables.
The unit corresponds to c, the first Fin to c'ᵢ, the second one to c''ᵢ.
To easily infer FinEnum we keep it as is, might also be possible to define an inductive type instead -/
private abbrev F := Unit ⊕ Fin dom_bound ⊕ Fin dom_bound

example : FinEnum F := by infer_instance

open ExtensionBase
--unfold constructors to get better pattern matching
@[scoped aesop unsafe 50% [constructors]]
inductive Next : ℕ ⊕ F → ℕ ⊕ F → ℕ ⊕ F → Prop
  | base {x y z} : z ∈ x ◯ y → Next (.inl x) (.inl y) (.inl z)
  | new : Next (.inl a) (.inl b) (.inr $ .inl ())
  | extra1 {d} (h : b ∈ a ◯ d) :
    Next (.inr $ .inl ()) (.inl d) (.inr $ .inr $ .inl ⟨d, lt_dom_bound $ dom_r h⟩)
  | extra2 {d} (h : b ∈ a ◯ d) :
    Next (.inl d) (.inr $ .inr $ .inl ⟨d, lt_dom_bound $ dom_r h⟩) (.inl a)
  | extra3_1 {d e} (h : b ∈ a ◯ d) : d ≠ e → e ∈ d ◯ a →
    Next (.inr $ .inr $ .inl ⟨d, lt_dom_bound $ dom_r h⟩)
      (.inr $ .inr $ .inr ⟨d, lt_dom_bound $ dom_r h⟩) (.inl d)
  | extra3_2 {d e} (h : b ∈ a ◯ d) : d ≠ e → e ∈ d ◯ a →
    Next (.inl e) (.inr $ .inr $ .inl ⟨d, lt_dom_bound $ dom_r h⟩)
      (.inr $ .inr $ .inr ⟨d, lt_dom_bound $ dom_r h⟩)
  | extra4_1 {d} (h : b ∈ a ◯ d) : d ∈ d ◯ a →
    Next (.inr $ .inr $ .inl ⟨d, lt_dom_bound $ dom_r h⟩) (.inl a) (.inl d)
  | extra4_2 {d} (h : b ∈ a ◯ d) : d ∈ d ◯ a →
    Next (.inl d) (.inr $ .inr $ .inl ⟨d, lt_dom_bound $ dom_r h⟩) (.inl a)

abbrev next : PreExtension (ℕ ⊕ F) := fun a b => {c | Next a b c}

theorem next_func : ∀ {x y}, Set.Subsingleton (next x y) := by
  intro x y z z_mem z' z'_mem
  cases z_mem <;>
  cases z'_mem <;> try rfl
  case base.base x y z z_mem z' z'_mem =>
    congr
    exact ok.func z_mem z'_mem
  all_goals try tauto
  all_goals exfalso ; apply not_def ; assumption

-- variant for better dependent pattern matching
theorem next_not_idempotent {x y} : x = y → x ∉ next x y := by
  intro eq x_mem
  cases x_mem
  case base h =>
    simp only [Sum.inl.injEq] at eq
    rw [eq] at h
    apply ok.not_idempotent h
  case extra4_2 h =>
    apply ok.not_idempotent h
  case extra2 => injection eq

theorem next_eq1076 {x y xy xxy} : xy ∈ next x y → xxy ∈ next x xy → ∃xxyy, xxyy ∈ next xxy y ∧ x ∈ next y xxyy := by
  intro xy_mem xxy_mem
  cases xy_mem
    <;> generalize ha : a = a' at *
    <;> generalize hb : b = b' at *
    <;> cases xxy_mem
  case base.base xy_mem _ xxy_mem =>
    obtain ⟨xxyy, xxyy_mem, eq⟩ := ok.eq1076 xy_mem xxy_mem
    exact ⟨.inl xxyy, .base xxyy_mem, .base eq⟩
  case base.new h =>
    exact ⟨_, .extra1 h, .extra2 h⟩
  case extra2.base d h e h' =>
    rw [← ha , ← hb] at *
    by_cases eq : d = e
    · exact ⟨_, eq ▸ .extra2 h, .extra4_1 h (eq ▸ h')⟩
    · exact ⟨_, .extra3_2 h eq h', .extra3_1 h eq h'⟩
  case extra2.new h =>
    rw [ha, hb] at h
    exact (ok.not_idempotent h).elim
  case extra3_1.extra4_1 h => exact (ok.not_idempotent h).elim
  case extra4_1.extra4_1 h => exact (ok.not_idempotent h).elim
  case extra4_2.new h _ => exact (not_def h).elim
  case extra4_2.base d d_mem h e h' =>
    have eq : d = e := ok.func d_mem h'
    rw [←ha, ←hb ] at *
    exact ⟨_, eq ▸ .extra2 h, .extra4_1 h (eq ▸ h')⟩

def domFresh : Finset (ℕ ⊕F )  := Finset.image (.inl) dom ∪ Finset.image (.inr) Finset.univ

theorem next_ok : next.OK where
  finite := by
    apply Set.Finite.subset (s := ((domFresh ×ˢ domFresh) ×ˢ domFresh).toSet) (Finset.finite_toSet _)
    refine fun ((x,y),z) hx => ?_
    unfold domFresh
    simp at hx ⊢; cases hx with
    | base h => simp [dom_o h, dom_l h, dom_r h]
    | new => simp [dom_a, dom_b]
    | extra1 h => simp [dom_a, dom_b, dom_r h]
    | extra3_2 h _ h' => simp [dom_a, dom_b, dom_r h, dom_o h']
    | _ h => simp [dom_a, dom_b, dom_r h]
  func {x y xy} hxy {xy'} hxy' := next_func hxy hxy'
  not_idempotent := next_not_idempotent rfl
  eq1076 := next_eq1076

def next_freshSolution : FreshSolution F Next where
  base := Next.base
  ok := next_ok
  ab_def := ⟨_, Next.new⟩

end Extension1
open ExtensionBase

theorem lift : ∀ (E : Extension ℕ) (a b : ℕ),
  ∃ E' : Extension ℕ, E ≤ E' ∧ E' ∈ {e : Extension ℕ | (e.1 a b).Nonempty} := fun ⟨E, ok⟩ a b => by
  if h : (E a b).Nonempty then exact ⟨_, le_rfl, h⟩ else
  let E1 : Extension1 :=
    { E, ok, a, b, not_def := (fun h' => h ⟨_, h'⟩)}
  let FE : FreshExtension _ := ⟨_, E1.next_freshSolution⟩
  exact ⟨⟨FE.adjoin,FE.adjoin_ok⟩,FE.adjoin_le, by simpa using FE.adjoin_ab_def⟩


variable (e₀ : Extension ℕ)

theorem exists_extension :
    ∃ op : ℕ → ℕ → ℕ,
    (∀ x y, x = op y (op (op x (op x y)) y)) ∧
    (∀ {x y z}, z ∈ e₀.1 x y → z = op x y) := by
  classical
  have ⟨c, hc, h1, h2, h3⟩ := exists_greedy_chain (a := e₀)
    (task := fun x : _ × _ => {e | (e.1 x.1 x.2).Nonempty}) fun ⟨E, ok⟩ ⟨a, b⟩ => by
      apply lift
  simp only [Subtype.exists, Prod.forall] at h3
  classical
  choose f hf1 hf2 op hop using h3
  refine ⟨op, fun x y => ?_, fun {x y z} H => ?_⟩
  · let S : Finset _ := {(x, y), (x, op x y), (op x (op x y), y), (y, op (op x (op x y)) y)}
    have ⟨⟨e, he⟩, le⟩ := hc.directed.finset_le (hι := ⟨⟨_, h1⟩⟩)
      (S.image fun (a, b) => ⟨⟨f a b, hf1 a b⟩, hf2 a b⟩)
    replace le a ha := Finset.forall_image.1 le a ha _ _ (hop a.1 a.2)
    simp only [Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq, S] at le
    obtain ⟨xy, xxy, xxyy, final⟩ := le
    obtain ⟨xxyy', xxyy'_def, eq⟩ := (e.2.eq1076 xy xxy)
    exact e.2.func eq ((e.2.func xxyy xxyy'_def) ▸ final)
  · exact (hf1 ..).func (h2 _ (hf2 x y) _ _ H) (hop ..)

def GreedyMagma (_ : Extension ℕ) := ℕ

instance (n) : OfNat (GreedyMagma e₀) n := inferInstanceAs (OfNat Nat n)

noncomputable instance instMagma : Magma (GreedyMagma e₀) where
  op := (exists_extension e₀).choose

theorem Extension.eq1076 : Equation1076 (GreedyMagma e₀) :=
  (exists_extension e₀).choose_spec.1


theorem Extension.base : ∀ {x y z : GreedyMagma e₀}, z ∈ e₀.1 x y → z = x ◇ y :=
  (exists_extension e₀).choose_spec.2

def fromList (S : List ((Nat × Nat) × Nat)) : PreExtension ℕ := fun a b => {c | ((a, b), c) ∈ S}

theorem fromList_ok {S : List ((Nat ×ₗ Nat) × Nat)}
    (sorted : S.Chain' (fun a b => a.1 < b.1) := by decide)
    (eq1076 : ∀ a ∈ S, ∀ b ∈ S, a.1.1 = b.1.1 → a.2 = b.1.2 →
      ∃ c ∈ S, ∃ d ∈ S, c.1.1 = b.2 ∧ c.1.2 = a.1.2 ∧ d.1.2 = c.2 ∧ d.1.1 = a.1.2 ∧ d.2 = a.1.1 := by decide)
    (not_idempotent : ∀ a ∈ S, a.1.1 = a.1.2 → a.2 ≠ a.1.1 := by decide) :
    (fromList S).OK where
  finite := List.finite_toSet S
  func h1 _ h2 := Decidable.by_contra fun h =>
    have : IsTrans ((ℕ ×ₗ ℕ) × ℕ) (·.1 < ·.1) := ⟨fun _ _ _ => lt_trans⟩
    (List.chain'_iff_pairwise.1 sorted) |>.imp (fun h => h.ne)
      |>.forall (fun _ _ => (·.symm)) h1 h2 (by rintro ⟨⟩; exact h rfl) rfl
  eq1076 h1 h2 := by -- variable names are off, copy pase from 1722 just worked
    obtain ⟨⟨⟨y, y'⟩,yy⟩, yy_mem, ⟨⟨yy', xyy⟩,x⟩, eq_mem, y_def,
    y'_def, yy'_def, xyy_def, x_def⟩ := eq1076 _ h1 _ h2 rfl rfl
    simp only at yy_mem eq_mem y_def y'_def yy_mem yy'_def xyy_def x_def
    exists yy
    rewrite [y_def, y'_def] at yy_mem
    use yy_mem
    use yy'_def ▸xyy_def ▸ x_def ▸ eq_mem
  not_idempotent h := not_idempotent _ h rfl rfl


theorem fromList_eval {e : Extension ℕ} {S : List ((Nat × Nat) × Nat)} (hS : e.1 = fromList S)
    (a b c : Nat) (h : ((a, b), c) ∈ S := by decide) :
    haveI : Magma Nat := instMagma e; a ◇ b = c :=
  (Extension.base e (hS ▸ h)).symm

theorem fromList_eval' {e : Extension ℕ} {S : List ((Nat × Nat) × Nat)} (hS : e.1 = fromList S)
    (s) (h : s ∈ S) :
    haveI : Magma Nat := instMagma e; s.1.1 ◇ s.1.2 = s.2 :=
  (Extension.base e (hS ▸ h)).symm

end
end Greedy
open Greedy
/-- see https://leanprover.zulipchat.com/#narrow/channel/458659-Equational/topic/713.2C.201289.2C.201447/near/483735768
for the seed data -/

def seed1 : List ((Nat × Nat) × Nat) := [
  ((0,0),1),
  ((0,1),2),
  ((0,3),0),
  ((1,0),1),
  ((1,3),1),
  ((2,0),3),
  ((3,1),0),
]

@[equational_result]
theorem refute_seed1 : ∃ (G : Type) (_ : Magma G), Facts G [1076] [3, 23, 99, 203, 307, 375, 1223, 2441, 3050, 3456, 3722, 3915, 4118, 4435] := by
  have ⟨e, he⟩ : ∃ e : Extension ℕ, e.1 = fromList seed1 :=
    ⟨⟨_, fromList_ok⟩, rfl⟩
  refine ⟨GreedyMagma e, inferInstance, e.eq1076, ?_⟩
  have rules := fromList_eval' he
  simp [seed1, List.mem_cons, List.mem_singleton, forall_eq_or_imp,
    forall_eq] at rules
  split_ands
  all_goals first
    | intro h ; have := h 0 ; simp [rules] at this ; (try cases this); done
    | intro h ; have := h 0 0 ; simp [rules] at this ; (try cases this); done
    | intro h ; have := h 0 3 ; simp [rules] at this

def seed2 : List ((Nat × Nat) × Nat) := [
  ((0,0),1),
  ((0,2),1),
  ((1,0),1),
  ((1,1),2),
  ((2,0),2),
]


@[equational_result]
theorem refute_seed2 : ∃ (G : Type) (_ : Magma G), Facts G [1076] [151, 326, 817, 1629, 2035, 2644, 3522, 3715, 4470
] := by
  have ⟨e, he⟩ : ∃ e : Extension ℕ, e.1 = fromList seed2 :=
    ⟨⟨_, fromList_ok⟩, rfl⟩
  refine ⟨GreedyMagma e, inferInstance, e.eq1076, ?_⟩
  have rules := fromList_eval' he
  simp [seed2, List.mem_cons, List.mem_singleton, forall_eq_or_imp,
    forall_eq] at rules
  split_ands
  all_goals first
    | intro h ; have := h 0 ; simp [rules] at this ; done
    | intro h ; have := h 0 0 ; simp [rules] at this ; (try cases this); done
    | intro h ; have := h 0 1 ; simp [rules] at this ; (try cases this); done
    | intro h ; have := h 1 0 ; simp [rules] at this ; (try cases this)

def seed3 : List ((Nat × Nat) × Nat) := [
  ((0,0),1),
  ((0,1),2),
  ((0,2),4),
  ((0,3),0),
  ((0,4),1),
  ((1,2),5),
  ((1,3),1),
  ((1,4),0),
  ((2,0),3),
  ((2,4),2),
  ((2,5),0),
  ((3,1),0),
  ((3,5),0),
  ((4,1),4),
  ((4,2),0),
  ((5,0),2),
]

@[equational_result]
theorem refute_seed3 : ∃ (G : Type) (_ : Magma G), Facts G [1076] [8, 411, 1426, 2294, 3253, 3862] := by
  have ⟨e, he⟩ : ∃ e : Extension ℕ, e.1 = fromList seed3 :=
    ⟨⟨_, fromList_ok⟩, rfl⟩
  refine ⟨GreedyMagma e, inferInstance, e.eq1076, ?_⟩
  have rules := fromList_eval' he
  simp [seed3, List.mem_cons, List.mem_singleton, forall_eq_or_imp,
    forall_eq] at rules
  split_ands
  all_goals first
    | intro h ; have := h 0 ; simp [rules] at this ; (try cases this); done
    | intro h ; have := h 0 1 ; simp [rules] at this ;

def seed4 : List ((Nat × Nat) × Nat) := [
  ((0,0),1),
  ((0,1),2),
  ((0,2),4),
  ((0,3),0),
  ((1,2),0),
  ((1,3),1),
  ((2,0),3),
  ((3,1),0),
  ((4,0),2),
  ((4,1),2),
]

@[equational_result]
theorem refute_seed4 : ∃ (G : Type) (_ : Magma G), Facts G [1076] [47,2238,3319] := by
  have ⟨e, he⟩ : ∃ e : Extension ℕ, e.1 = fromList seed4 :=
    ⟨⟨_, fromList_ok⟩, rfl⟩
  refine ⟨GreedyMagma e, inferInstance, e.eq1076, ?_⟩
  have rules := fromList_eval' he
  simp [seed4, List.mem_cons, List.mem_singleton, forall_eq_or_imp,
    forall_eq] at rules
  split_ands
  all_goals first
    | intro h ; have := h 0 ; simp [rules] at this ; done
    | intro h ; have := h 0 0 ; simp [rules] at this ; (try cases this)

def seed5 : List ((Nat × Nat) × Nat) := [
  ((0,0),1),
  ((0,1),2),
  ((0,3),0),
  ((1,2),0),
  ((1,3),2),
  ((2,0),3),
  ((3,0),1),
  ((3,2),0),
]

@[equational_result]
theorem refute_seed5 : ∃ (G : Type) (_ : Magma G), Facts G [1076] [2847] := by
  have ⟨e, he⟩ : ∃ e : Extension ℕ, e.1 = fromList seed5 :=
    ⟨⟨_, fromList_ok⟩, rfl⟩
  refine ⟨GreedyMagma e, inferInstance, e.eq1076, ?_⟩
  have rules := fromList_eval' he
  simp [seed5, List.mem_cons, List.mem_singleton, forall_eq_or_imp,
    forall_eq] at rules
  intro h ; have := h 0 ; simp [rules] at this

def seed6 : List ((Nat × Nat) × Nat) := [
  ((0,0),1),
  ((0,2),0),
  ((0,3),1),
  ((1,0),2),
  ((1,2),3),
  ((2,3),0),
  ((3,0),3),
]

@[equational_result]
theorem refute_seed6 : ∃ (G : Type) (_ : Magma G), Facts G [1076] [359] := by
  have ⟨e, he⟩ : ∃ e : Extension ℕ, e.1 = fromList seed6 :=
    ⟨⟨_, fromList_ok⟩, rfl⟩
  refine ⟨GreedyMagma e, inferInstance, e.eq1076, ?_⟩
  have rules := fromList_eval' he
  simp [seed6, List.mem_cons, List.mem_singleton, forall_eq_or_imp,
    forall_eq] at rules
  intro h ; have := h 0 ; simp [rules] at this; cases this

def seed7 : List ((Nat × Nat) × Nat) := [
  ((0,0),1),
  ((0,2),1),
  ((1,0),2),
  ((2,0),2)
]

@[equational_result]
theorem refute_seed7 : ∃ (G : Type) (_ : Magma G), Facts G [1076] [255,4065] := by
  have ⟨e, he⟩ : ∃ e : Extension ℕ, e.1 = fromList seed7 :=
    ⟨⟨_, fromList_ok⟩, rfl⟩
  refine ⟨GreedyMagma e, inferInstance, e.eq1076, ?_⟩
  have rules := fromList_eval' he
  simp [seed7, List.mem_cons, List.mem_singleton, forall_eq_or_imp,
    forall_eq] at rules
  split_ands
  all_goals intro h ; have := h 0 ; simp [rules] at this ; try cases this

def seed8 : List ((Nat × Nat) × Nat) := [
  ((0,0),1),
  ((0,1),2),
  ((0,3),0),
  ((1,3),1),
  ((2,0),3),
  ((2,1),2),
  ((3,1),0),
]

@[equational_result]
theorem refute_seed8 : ∃ (G : Type) (_ : Magma G), Facts G [1076] [1832] := by
  have ⟨e, he⟩ : ∃ e : Extension ℕ, e.1 = fromList seed8 :=
    ⟨⟨_, fromList_ok⟩, rfl⟩
  refine ⟨GreedyMagma e, inferInstance, e.eq1076, ?_⟩
  have rules := fromList_eval' he
  simp [seed8, List.mem_cons, List.mem_singleton, forall_eq_or_imp,
    forall_eq] at rules
  intro h ; have := h 0 ; simp [rules] at this

def seed9 : List ((Nat × Nat) × Nat) := [
  ((0,0),1),
  ((1,1),0),
]

@[equational_result]
theorem refute_seed9 : ∃ (G : Type) (_ : Magma G), Facts G [1076] [3659] := by
  have ⟨e, he⟩ : ∃ e : Extension ℕ, e.1 = fromList seed9 :=
    ⟨⟨_, fromList_ok⟩, rfl⟩
  refine ⟨GreedyMagma e, inferInstance, e.eq1076, ?_⟩
  have rules := fromList_eval' he
  simp [seed9, List.mem_cons, List.mem_singleton, forall_eq_or_imp,
    forall_eq] at rules
  intro h ; have := h 0 ; simp [rules] at this

end Eq1076