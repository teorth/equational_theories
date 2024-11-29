import equational_theories.Mathlib.Data.List.Defs
import equational_theories.Mathlib.Order.Greedy
import Mathlib.Data.Finset.Order
import Mathlib.Data.Prod.Lex
import Mathlib.Data.List.AList
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Functor
import Mathlib.Tactic.DeriveFintype

import equational_theories.AdjoinFresh
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.PartialMagma

namespace Eq1289
namespace Greedy
noncomputable section
open AdjoinFresh PartialMagma

structure Laws {α : Type} (E : PreExtension α) : Prop where
  eq1289 {x y xy xyy xyyy} : xy ∈ E x y → xyy ∈ E xy y → xyyy ∈ E xyy y → x ∈ E y xyyy
  right_cancel {x y z xy zy} : xy ∈ E x y → zy ∈ E z y → xy = zy → x = z
  idem_l {x y xy} : xy ∈ E x y → x ∈ E x x
  idem_r {x y xy} : xy ∈ E x y → y ∈ E y y
  idem_o {x y xy} : xy ∈ E x y → xy ∈ E xy xy

def Laws_equiv {α β : Type} (e : α ≃ β) (E : PreExtension β) (ok : Laws E) :
  Laws (Equiv.movePreExtension e E) where
  eq1289 xy_mem xyy_mem xyyy_mem := by simpa using ok.eq1289 xy_mem xyy_mem xyyy_mem
  right_cancel xy_mem zy_mem := by simpa using ok.right_cancel xy_mem zy_mem
  idem_l xy_mem := by simpa using ok.idem_l xy_mem
  idem_r xy_mem := by simpa using ok.idem_r xy_mem
  idem_o xy_mem := by simpa using ok.idem_o xy_mem

scoped instance : ExtensionRules where
  laws := Laws
  laws_equiv := Laws_equiv

-- First case: b = a, but not in the table => just add a ◇ a = a
class Extension1 extends ExtensionBase where
  b_eq_a : b = a
  not_im_l {y z}: z ∉ E a y
  not_im_r {x z}: z ∉ E x a
  not_im_o {x y}: a ∉ E x y

namespace Extension1
variable [Extension1]
attribute [scoped aesop safe destruct] not_im_l
attribute [scoped aesop safe destruct] not_im_r
attribute [scoped aesop safe destruct] not_im_o

/- we don't need any fresh variables. in principle one can remove the dependency on adjoinFresh, not
clear if this is worth it
-/
abbrev F := Empty

open ExtensionBase
--unfold constructors to get better pattern matching
@[scoped aesop unsafe 50% [constructors]]
inductive Next : ℕ ⊕ F → ℕ ⊕ F → ℕ ⊕ F → Prop
  | base {x y z} : z ∈ x ◯ y → Next (.inl x) (.inl y) (.inl z)
  | new : Next (.inl a) (.inl a) (.inl a)

@[scoped aesop safe destruct]
theorem not_def' {c} : c ∉ E a a := b_eq_a ▸ not_def (c:= c)

abbrev next : PreExtension (ℕ ⊕ F) := fun a b => {c | Next a b c}

theorem next_func : ∀ {x y}, Set.Subsingleton (next x y) := by
  intro x y z z_mem z' z'_mem
  cases z_mem <;>
  cases z'_mem <;> try rfl
  case base.base x y z z_mem z' z'_mem =>
    congr
    exact ok.func z_mem z'_mem
  all_goals exfalso ; apply not_def' ; assumption


theorem next_right_cancel {x y z xy zy} : xy ∈ next x y → zy ∈ next z y → xy = zy → x = z:= by
  intro xy_mem zy_mem eq
  cases xy_mem <;> cases zy_mem
  case base.base xy_mem _ _ zy_mem =>
    simp only [Sum.inl.injEq]
    exact ok.laws.right_cancel xy_mem zy_mem (by simpa using eq)
  all_goals aesop

theorem next_idem_l {x y xy} : xy ∈ next x y → x ∈ next x x := by
  intro xy_mem
  cases xy_mem
  case base xy_mem => exact (.base <| ok.laws.idem_l xy_mem)
  all_goals aesop

theorem next_idem_r {x y xy} : xy ∈ next x y → y ∈ next y y := by
  intro xy_mem
  cases xy_mem
  case base xy_mem => exact (.base <| ok.laws.idem_r xy_mem)
  all_goals aesop

theorem next_idem_o {x y xy} : xy ∈ next x y → xy ∈ next xy xy := by
  intro xy_mem
  cases xy_mem
  case base xy_mem => exact (.base <| ok.laws.idem_o xy_mem)
  all_goals aesop

theorem next_eq1289 {x y xy xyy xyyy} : xy ∈ next x y → xyy ∈ next xy y → xyyy ∈ next xyy y →
  x ∈ next y xyyy := by
  intro xy_mem xyy_mem xyyy_mem
  cases xy_mem <;> cases xyy_mem <;> cases xyyy_mem
  case base.base.base xy_mem _ xyy_mem _ xyyy_mem =>
    exact .base <| ok.laws.eq1289 xy_mem xyy_mem xyyy_mem
  all_goals aesop


def domFresh : Finset (ℕ ⊕F )  := Finset.image (.inl) dom ∪ Finset.image (.inr) Finset.univ

theorem next_ok : next.OK where
  finite := by
    apply Set.Finite.subset (s := ((domFresh ×ˢ domFresh) ×ˢ domFresh).toSet) (Finset.finite_toSet _)
    refine fun ((x,y),z) hx => ?_
    unfold domFresh
    simp at hx ⊢; cases hx with
    | base h => simp [dom_o h, dom_l h, dom_r h]
    | _ => simp [dom_a, dom_b]
  func {x y xy} hxy {xy'} hxy' := next_func hxy hxy'
  laws := {
  right_cancel := next_right_cancel
  eq1289 := next_eq1289
  idem_l := next_idem_l
  idem_r := next_idem_r
  idem_o := next_idem_o
  }

def next_freshSolution : FreshSolution F Next where
  base := Next.base
  ok := next_ok
  ab_def := ⟨.inl a, b_eq_a ▸ Next.new⟩

end Extension1
class Extension2 extends ExtensionBase where
   a_ne_b : a ≠ b
   a_idem : a ∈ E a a
   b_idem : b ∈ E b b

namespace Extension2
variable [Extension2]
open ExtensionBase
attribute [scoped aesop safe destruct] a_ne_b
attribute [scoped aesop safe forward] a_idem
attribute [scoped aesop safe forward] b_idem

inductive Relevant : ℕ → Prop
  | mk {d e} : e ∈ d ◯ b  → a ∈ e ◯ b → Relevant d

theorem Relevant.unique {d d'} : Relevant d → Relevant d' → d = d'
  | .mk h1 h2, .mk h1' h2' => ok.laws.right_cancel h1 h1' (ok.laws.right_cancel h2 h2' rfl)

theorem Relevant.idem {d} : Relevant d → d ∈ d ◯ d
  | .mk h1 _ => ok.laws.idem_l h1

theorem Relevant.ne_b {d} : Relevant d → b ≠ d
  | .mk h1 h2, rfl => a_ne_b (ok.func h2 (ok.func b_idem h1 ▸ h1))

abbrev F := Unit

@[scoped aesop unsafe 50% [constructors]]
inductive Next : ℕ ⊕ F → ℕ ⊕ F → ℕ ⊕ F → Prop
  | base {x y z} : z ∈ x ◯ y → Next (.inl x) (.inl y) (.inl z)
  | new : Next (.inl a) (.inl b) (.inr ())
  | idem : Next (.inr ()) (.inr ()) (.inr ())
  | extra {d} : Relevant d → Next (.inl b) (.inr ()) (.inl d)


abbrev next : PreExtension (ℕ ⊕ F) := fun a b => {c | Next a b c}

theorem next_func : ∀ {x y}, Set.Subsingleton (next x y) := by
  intro x y z z_mem z' z'_mem
  cases z_mem
    <;> generalize ha : a = a' at *
    <;> generalize hb : b = b' at *
    <;> cases z'_mem <;> try rfl
  case base.base x y z z_mem z' z'_mem =>
    congr
    exact ok.func z_mem z'_mem
  case extra.extra d hd d' hd' => simp [hd.unique hd']
  all_goals rw [← ha, ← hb] at *
  all_goals exfalso ; apply not_def ; assumption

theorem next_right_cancel {x y z xy zy} : xy ∈ next x y → zy ∈ next z y → xy = zy → x = z:= by
  intro xy_mem zy_mem eq
  cases xy_mem <;> cases zy_mem
  case base.base xy_mem _ _ zy_mem =>
    simp only [Sum.inl.injEq]
    exact ok.laws.right_cancel xy_mem zy_mem (by simpa using eq)
  all_goals aesop

theorem next_idem_l {x y xy} : xy ∈ next x y → x ∈ next x x := by
  intro xy_mem
  cases xy_mem
  case base xy_mem => exact (.base <| ok.laws.idem_l xy_mem)
  all_goals aesop

theorem next_idem_r {x y xy} : xy ∈ next x y → y ∈ next y y := by
  intro xy_mem
  cases xy_mem
  case base xy_mem => exact (.base <| ok.laws.idem_r xy_mem)
  all_goals aesop

theorem next_idem_o {x y xy} : xy ∈ next x y → xy ∈ next xy xy := by
  intro xy_mem
  cases xy_mem
  case base xy_mem => exact (.base <| ok.laws.idem_o xy_mem)
  case extra h => exact .base <| h.idem
  all_goals aesop

theorem next_eq1289 {x y xy xyy xyyy} : xy ∈ next x y → xyy ∈ next xy y → xyyy ∈ next xyy y →
  x ∈ next y xyyy := by
  intro xy_mem xyy_mem xyyy_mem
  cases xy_mem <;> cases xyy_mem <;> cases xyyy_mem
  case base.base.base xy_mem _ xyy_mem _ xyyy_mem =>
    exact .base <| ok.laws.eq1289 xy_mem xyy_mem xyyy_mem
  case base.base.new h1 h2 =>
    exact .extra <| .mk h1 h2
  case extra.extra.extra h =>
    exact (h.ne_b rfl).elim
  all_goals aesop


def domFresh : Finset (ℕ ⊕ F)  := Finset.image (.inl) dom ∪ Finset.image (.inr) Finset.univ

theorem next_ok : next.OK where
  finite := by
    apply Set.Finite.subset (s := ((domFresh ×ˢ domFresh) ×ˢ domFresh).toSet) (Finset.finite_toSet _)
    refine fun ((x,y),z) hx => ?_
    unfold domFresh
    simp at hx ⊢; match hx with
    | .base h => simp [dom_o h, dom_l h, dom_r h]
    | .new => simp [dom_a, dom_b]
    | .extra (.mk h1 h2) => simp [dom_l h1, dom_b]
    | .idem => simp
  func {x y xy} hxy {xy'} hxy' := next_func hxy hxy'
  laws := {
  right_cancel := next_right_cancel
  eq1289 := next_eq1289
  idem_l := next_idem_l
  idem_r := next_idem_r
  idem_o := next_idem_o
  }

def next_freshSolution : FreshSolution F Next where
  base := Next.base
  ok := next_ok
  ab_def := ⟨_, Next.new⟩

end Extension2
open ExtensionBase

theorem liftS : ∀ (E : Extension ℕ) (a: ℕ),
  ∃ E' : Extension ℕ, E ≤ E' ∧ E' ∈ {e : Extension ℕ  | (e.1 a a).Nonempty} := fun ⟨E, ok⟩ a => by
  if h : (E a a).Nonempty then exact ⟨_, le_rfl, h⟩ else
  if im_l : ∃ y z, z ∈ E a y then
    obtain ⟨y, z, mem⟩ := im_l
    exact ⟨⟨E, ok⟩ , le_rfl, ⟨_,ok.laws.idem_l mem⟩⟩
  else if im_r : ∃ x z, z ∈ E x a then
    obtain ⟨_, _, mem⟩ := im_r
    exact ⟨⟨E, ok⟩ , le_rfl, ⟨_,ok.laws.idem_r mem⟩⟩
  else if im_o : ∃ x y, a ∈ E x y then
    obtain ⟨_, _, mem⟩ := im_o
    exact ⟨⟨E, ok⟩ , le_rfl, ⟨_,ok.laws.idem_o mem⟩⟩
  else
  let E1 : Extension1 :=
    { E, ok, a, b := a, not_def := (fun h' => h ⟨_, h'⟩), b_eq_a := rfl,
      not_im_l := fun h => im_l ⟨_,_, h⟩,
      not_im_r := fun h => im_r ⟨_,_, h⟩,
      not_im_o := fun h => im_o ⟨_,_, h⟩,
      }
  let FE : FreshExtension _ := ⟨_, E1.next_freshSolution⟩
  exact ⟨⟨FE.adjoin,FE.adjoin_ok⟩,FE.adjoin_le, by simpa using FE.adjoin_ab_def⟩

theorem lift : ∀ (E : Extension ℕ) (a b : ℕ),
  ∃ E' : Extension ℕ, E ≤ E' ∧ E' ∈ {e : Extension ℕ | (e.1 a b).Nonempty} := fun ⟨E, ok⟩ a b => by
  if h : (E a b).Nonempty then exact ⟨_, le_rfl, h⟩ else
  if b_eq_a : b = a then exact b_eq_a ▸ liftS ⟨E,ok⟩ a else
  obtain ⟨E',le,⟨aa, aa_def⟩⟩ := liftS ⟨E, ok⟩ a
  obtain ⟨E'',le',⟨bb, bb_def⟩⟩ := liftS E' b
  if h' : (E''.1 a b).Nonempty then exact ⟨E'', le_trans le le', h'⟩ else
  let E2 : Extension2 :=
    { E:= E''.1, ok := E''.2, a, b, not_def := (fun h'' => h' ⟨_, h''⟩), a_ne_b := by tauto,
      a_idem := le' _ _ <| E'.2.laws.idem_r aa_def,
      b_idem := E''.2.laws.idem_r bb_def,
    }
  let FE : FreshExtension _ := ⟨_, E2.next_freshSolution⟩
  exact ⟨⟨FE.adjoin,FE.adjoin_ok⟩,le_trans le <| le_trans le' FE.adjoin_le, by simpa using FE.adjoin_ab_def⟩


variable (e₀ : Extension ℕ)

theorem exists_extension :
    ∃ op : ℕ → ℕ → ℕ,
    (∀ x y, x = op y (op (op (op x y) y) y)) ∧
    (∀ {x y z}, z ∈ e₀.1 x y → z = op x y) := by
  classical
  have ⟨c, hc, h1, h2, h3⟩ := exists_greedy_chain (a := e₀)
    (task := fun x : _ × _ => {e | (e.1 x.1 x.2).Nonempty}) fun ⟨E, ok⟩ ⟨a, b⟩ => by
      apply lift
  simp only [Subtype.exists, Prod.forall] at h3
  classical
  choose f hf1 hf2 op hop using h3
  refine ⟨op, fun x y => ?_, fun {x y z} H => ?_⟩
  · let S : Finset _ := {(x,y), (op x y, y), (op (op x y) y, y), (y, op (op (op x y) y) y)}
    have ⟨⟨e, he⟩, le⟩ := hc.directed.finset_le (hι := ⟨⟨_, h1⟩⟩)
      (S.image fun (a, b) => ⟨⟨f a b, hf1 a b⟩, hf2 a b⟩)
    replace le a ha := Finset.forall_image.1 le a ha _ _ (hop a.1 a.2)
    simp only [Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq, S] at le
    obtain ⟨xy, xyy, xyyy, final⟩ := le
    exact e.2.func (e.2.laws.eq1289 xy xyy xyyy) final
  · exact (hf1 ..).func (h2 _ (hf2 x y) _ _ H) (hop ..)

def GreedyMagma (_ : Extension ℕ) := ℕ

instance (n) : OfNat (GreedyMagma e₀) n := inferInstanceAs (OfNat Nat n)

noncomputable instance instMagma : Magma (GreedyMagma e₀) where
  op := (exists_extension e₀).choose

theorem _root_.PartialMagma.Extension.eq1289 : Equation1289 (GreedyMagma e₀) :=
  (exists_extension e₀).choose_spec.1


theorem Extension.base : ∀ {x y z : GreedyMagma e₀}, z ∈ e₀.1 x y → z = x ◇ y :=
  (exists_extension e₀).choose_spec.2

def fromList (S : List ((Nat × Nat) × Nat)) : PreExtension ℕ := fun a b => {c | ((a, b), c) ∈ S}

theorem fromList_ok {S : List ((Nat ×ₗ Nat) × Nat)}
    (sorted : S.Chain' (fun a b => a.1 < b.1) := by decide)
    (eq1289 : ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, a.1.2 = b.1.2 → a.2 = b.1.1 →
       c.1.1 = b.2 → c.1.2 = a.1.2 → ∃ d ∈ S, d.1.1 = a.1.2 ∧ d.1.2 = c.2 ∧ d.2 = a.1.1 := by decide)
    (right_cancel : ∀ a ∈ S, ∀ b ∈ S, a.1.2 = b.1.2 → a.2 = b.2 → a.1.1 = b.1.1 := by decide)
    (idem_l : ∀ a ∈ S, ∃ b ∈ S, a.1.1 = b.1.1 ∧ a.1.1 = b.1.2 ∧ a.1.1 = b.2 := by decide)
    (idem_r : ∀ a ∈ S, ∃ b ∈ S, a.1.2 = b.1.1 ∧ a.1.2 = b.1.2 ∧ a.1.2 = b.2 := by decide)
    (idem_o : ∀ a ∈ S, ∃ b ∈ S, a.2 = b.1.1 ∧ a.2 = b.1.2 ∧ a.2 = b.2 := by decide) :
    (fromList S).OK where
  finite := List.finite_toSet S
  func h1 _ h2 := Decidable.by_contra fun h =>
    have : IsTrans ((ℕ ×ₗ ℕ) × ℕ) (·.1 < ·.1) := ⟨fun _ _ _ => lt_trans⟩
    (List.chain'_iff_pairwise.1 sorted) |>.imp (fun h => h.ne)
      |>.forall (fun _ _ => (·.symm)) h1 h2 (by rintro ⟨⟩; exact h rfl) rfl
  laws := {
  eq1289 := fun h1 h2 h3 => by
    obtain ⟨⟨⟨_,_⟩,_⟩,mem,rfl,rfl,rfl⟩ := eq1289 _ h1 _ h2 _ h3 rfl rfl rfl rfl
    exact mem
  right_cancel := fun h h' => right_cancel _ h _  h' rfl
  idem_l := fun h => by
    obtain ⟨⟨⟨_,_⟩,_⟩,mem,rfl,rfl,rfl⟩ := idem_l _ h
    exact mem
  idem_r := fun h => by
    obtain ⟨⟨⟨_,_⟩,_⟩,mem,rfl,rfl,rfl⟩ := idem_r _ h
    exact mem
  idem_o := fun h => by
    obtain ⟨⟨⟨_,_⟩,_⟩,mem,rfl,rfl,rfl⟩ := idem_o _ h
    exact mem
  }

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
open Greedy PartialMagma
def seed : List ((Nat × Nat) × Nat) := [
  ((0,0),0),
  ((0,1),2),
  ((0,2),1),
  ((0,4),1),
  ((1,0),2),
  ((1,1),1),
  ((2,0),3),
  ((2,2),2),
  ((3,0),4),
  ((3,3),3),
  ((4,4),4),
]

@[equational_result]
theorem not_3116_4435 : ∃ (G : Type) (_ : Magma G), Facts G [1289] [3116, 4435] := by
  have ⟨e, he⟩ : ∃ e : Extension ℕ, e.1 = fromList seed :=
    ⟨⟨_, fromList_ok⟩, rfl⟩
  have rules := fromList_eval' he
  simp [seed, List.mem_cons, List.mem_singleton, forall_eq_or_imp,
    forall_eq] at rules
  refine ⟨GreedyMagma e, inferInstance, e.eq1289, fun h => ?_, fun h => ?_⟩
  · have := h 2 0
    simp [rules] at this
    cases this
  · have := h 0 1
    simp [rules] at this
    cases this

end Eq1289
