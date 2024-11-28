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

namespace Eq713
namespace Greedy
noncomputable section
open AdjoinFresh PartialMagma

structure Laws {α : Type} (E : PreExtension α) : Prop where
  eq713 {x y yx yxx} : yx ∈ E y x → yxx ∈ E yx x → ∃yyxx, yyxx ∈ E y yxx ∧ x ∈ E y yyxx
  law2 {x y} : y ∉ E x y
  law3 {x xx} : xx ∈ E x x → ∃ xxx, xxx ∈ E xx x

def Laws_equiv {α β : Type} (e : α ≃ β) (E : PreExtension β) (ok : Laws E) :
  Laws (Equiv.movePreExtension e E) where
  eq713 yx_mem yxx_mem := by
    obtain ⟨yyxx, yyxx_mem, eq⟩ := ok.eq713 yx_mem yxx_mem
    exact ⟨e.symm yyxx, by simpa using yyxx_mem, by simpa using eq⟩
  law2 xy_mem := by simpa using ok.law2 xy_mem
  law3 xx_mem := by
    obtain ⟨xxx, h⟩ := ok.law3 xx_mem
    exact ⟨e.symm xxx,  by simpa using h⟩


scoped instance : ExtensionRules where
  laws := Laws
  laws_equiv := Laws_equiv

class Extension1 extends ExtensionBase where
  b_eq_a : b = a

namespace Extension1
variable [Extension1]

abbrev F := Fin 3

open ExtensionBase
--unfold constructors to get better pattern matching
@[scoped aesop unsafe 50% [constructors]]
inductive Next : ℕ ⊕ F → ℕ ⊕ F → ℕ ⊕ F → Prop
  | base {x y z} : z ∈ x ◯ y → Next (.inl x) (.inl y) (.inl z)
  | new : Next (.inl a) (.inl a) (.inr 0)
  | extra1 : Next (.inr 0) (.inl a) (.inr 1)
  | extra2 : Next (.inl a) (.inr 1) (.inr 2)
  | extra3 : Next (.inl a) (.inr 0) (.inr 2)
  | extra4 : Next (.inl a) (.inr 2) (.inl a)


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

theorem next_law2 {x y } : y ∉ next x y := by
  intro xy_mem
  cases xy_mem
  case base xy_mem =>
    exact ok.laws.law2 xy_mem

theorem next_law3 {x xx} : xx ∈ next x x → ∃ xxx, xxx ∈ next xx x := by
  intro xx_mem
  cases xx_mem
  case base h =>
    obtain ⟨xxx, xxx_mem⟩ := ok.laws.law3 h
    exact ⟨.inl xxx, .base xxx_mem⟩
  all_goals simp_all
  all_goals aesop

theorem next_eq713 {x y yx yxx} : yx ∈ next y x → yxx ∈ next yx x → ∃
  yyxx, yyxx ∈ next y yxx ∧ x ∈ next y yyxx := by
  intro yx_mem yxx_mem
  cases yx_mem <;> cases yxx_mem
  case base.base yx_mem _ yxx_mem =>
    obtain ⟨yyxx, yyxx_mem, eq⟩ := ok.laws.eq713 yx_mem yxx_mem
    exact ⟨.inl yyxx, .base yyxx_mem, .base eq⟩
  case base.new h =>
    exact (ok.laws.law2 h).elim
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
  law2 := next_law2
  eq713 := next_eq713
  law3 := next_law3
  }

def next_freshSolution : FreshSolution F Next where
  base := Next.base
  ok := next_ok
  ab_def := ⟨.inr 0, b_eq_a ▸ Next.new⟩

end Extension1
class Extension2 extends ExtensionBase where
   a_ne_b : a ≠ b

namespace Extension2
variable [Extension2]
open ExtensionBase
attribute [scoped aesop safe destruct] a_ne_b



inductive Relevant : ℕ → Prop
  | mk {d} : a ∈ d ◯ b → Relevant d

theorem Relevant.ne_b {d} : Relevant d → b ≠ d
  | .mk h, rfl => by
    obtain ⟨bbb, bbb_mem⟩ := ok.laws.law3 h
    exact (not_def bbb_mem)

theorem Relevant.bound {d} : Relevant d →  d < dom_bound
  | .mk h => lt_dom_bound (dom_l h)

abbrev F := Unit ⊕ Fin dom_bound

inductive Next : ℕ ⊕ F → ℕ ⊕ F → ℕ ⊕ F → Prop
  | base {x y z} : z ∈ x ◯ y → Next (.inl x) (.inl y) (.inl z)
  | new : Next (.inl a) (.inl b) (.inr $ .inl ())
  | extra1 {d} (h: Relevant d) : Next (.inl d) (.inr $ .inl $ ()) (.inr $ .inr ⟨d, h.bound⟩)
  | extra2 {d} (h: Relevant d) : Next (.inl d) (.inr $ .inr ⟨d, h.bound⟩) (.inl b)


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
  all_goals rw [← ha, ← hb] at *
  all_goals exfalso ; apply not_def ; assumption

theorem next_law2 {x y} :  y ∉ next x y := by
  intro xy_mem
  cases xy_mem
  case base xy_mem =>
    exact ok.laws.law2 xy_mem

-- better for pattern matching
theorem next_law3' {x y xy} : x = y → xy ∈ next x y → ∃ xyx, xyx ∈ next xy x:= by
  intro x_eq_y xy_mem
  cases xy_mem
  case base h =>
    simp only [Sum.inl.injEq] at x_eq_y
    rw [← x_eq_y] at h
    obtain ⟨xxx, xxx_mem⟩ := ok.laws.law3 h
    exact ⟨.inl xxx, .base xxx_mem⟩
  all_goals simp_all
  all_goals aesop

theorem next_eq713 {x y yx yxx} : yx ∈ next y x → yxx ∈ next yx x → ∃
  yyxx, yyxx ∈ next y yxx ∧ x ∈ next y yyxx := by
  intro yx_mem yxx_mem
  cases yx_mem
    <;> generalize ha : a = a' at *
    <;> generalize hb : b = b' at *
    <;> cases yxx_mem
  case base.base yx_mem _ yxx_mem =>
    obtain ⟨yyxx, yyxx_mem, eq⟩ := ok.laws.eq713 yx_mem yxx_mem
    exact ⟨.inl yyxx, .base yyxx_mem, .base eq⟩
  case extra2.extra2 h =>
    exact (h.ne_b hb).elim
  case base.new h =>
    exact ⟨_, .extra1 (.mk h), .extra2 (.mk h)⟩

def domFresh : Finset (ℕ ⊕ F)  := Finset.image (.inl) dom ∪ Finset.image (.inr) Finset.univ

theorem next_ok : next.OK where
  finite := by
    apply Set.Finite.subset (s := ((domFresh ×ˢ domFresh) ×ˢ domFresh).toSet) (Finset.finite_toSet _)
    refine fun ((x,y),z) hx => ?_
    unfold domFresh
    simp at hx ⊢; cases hx with
    | base h => simp [dom_o h, dom_l h, dom_r h]
    | new => simp [dom_a, dom_b]
    | extra1 h => simp [dom_l h.1]
    | extra2 h => simp [dom_l h.1, dom_b]
  func {x y xy} hxy {xy'} hxy' := next_func hxy hxy'
  laws := {
  law2 := next_law2
  eq713 := next_eq713
  law3 := next_law3' rfl
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
  let E1 : Extension1 :=
    { E, ok, a, b := a, not_def := (fun h' => h ⟨_, h'⟩), b_eq_a := rfl }
  let FE : FreshExtension _ := ⟨_, E1.next_freshSolution⟩
  exact ⟨⟨FE.adjoin,FE.adjoin_ok⟩,FE.adjoin_le, by simpa using FE.adjoin_ab_def⟩

theorem lift : ∀ (E : Extension ℕ) (a b : ℕ),
  ∃ E' : Extension ℕ, E ≤ E' ∧ E' ∈ {e : Extension ℕ | (e.1 a b).Nonempty} := fun ⟨E, ok⟩ a b => by
  if h : (E a b).Nonempty then exact ⟨_, le_rfl, h⟩ else
  if b_eq_a : b = a then exact b_eq_a ▸ liftS ⟨E,ok⟩ a else
  let E2 : Extension2 :=
    { E, ok, a, b, not_def := (fun h' => h ⟨_, h'⟩), a_ne_b := by tauto }
  let FE : FreshExtension _ := ⟨_, E2.next_freshSolution⟩
  exact ⟨⟨FE.adjoin,FE.adjoin_ok⟩,FE.adjoin_le, by simpa using FE.adjoin_ab_def⟩


variable (e₀ : Extension ℕ)

theorem exists_extension :
    ∃ op : ℕ → ℕ → ℕ,
    (∀ x y, x = op y (op y (op (op y x) x))) ∧
    (∀ {x y z}, z ∈ e₀.1 x y → z = op x y) := by
  classical
  have ⟨c, hc, h1, h2, h3⟩ := exists_greedy_chain (a := e₀)
    (task := fun x : _ × _ => {e | (e.1 x.1 x.2).Nonempty}) fun ⟨E, ok⟩ ⟨a, b⟩ => by
      apply lift
  simp only [Subtype.exists, Prod.forall] at h3
  classical
  choose f hf1 hf2 op hop using h3
  refine ⟨op, fun x y => ?_, fun {x y z} H => ?_⟩
  · let S : Finset _ := {(y,x), (op y x, x), (y, op (op y x) x), (y, op y (op (op y x) x))}
    have ⟨⟨e, he⟩, le⟩ := hc.directed.finset_le (hι := ⟨⟨_, h1⟩⟩)
      (S.image fun (a, b) => ⟨⟨f a b, hf1 a b⟩, hf2 a b⟩)
    replace le a ha := Finset.forall_image.1 le a ha _ _ (hop a.1 a.2)
    simp only [Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq, S] at le
    obtain ⟨yx, yxx, yyxx, final⟩ := le
    obtain ⟨yyxx', yyxx'_def, eq⟩ := (e.2.laws.eq713 yx yxx)
    exact e.2.func eq ((e.2.func yyxx yyxx'_def) ▸ final)
  · exact (hf1 ..).func (h2 _ (hf2 x y) _ _ H) (hop ..)

def GreedyMagma (_ : Extension ℕ) := ℕ

instance (n) : OfNat (GreedyMagma e₀) n := inferInstanceAs (OfNat Nat n)

noncomputable instance instMagma : Magma (GreedyMagma e₀) where
  op := (exists_extension e₀).choose

theorem _root_.PartialMagma.Extension.eq713 : Equation713 (GreedyMagma e₀) :=
  (exists_extension e₀).choose_spec.1


theorem Extension.base : ∀ {x y z : GreedyMagma e₀}, z ∈ e₀.1 x y → z = x ◇ y :=
  (exists_extension e₀).choose_spec.2

def fromList (S : List ((Nat × Nat) × Nat)) : PreExtension ℕ := fun a b => {c | ((a, b), c) ∈ S}

theorem fromList_ok {S : List ((Nat ×ₗ Nat) × Nat)}
    (sorted : S.Chain' (fun a b => a.1 < b.1) := by decide)
    (eq713 : ∀ a ∈ S, ∀ b ∈ S, a.1.2 = b.1.2 → a.2 = b.1.1 →
      ∃ c ∈ S, ∃ d ∈ S, c.1.1 = a.1.1 ∧ c.1.2 = b.2 ∧ d.1.1 = a.1.1 ∧ d.1.2 = c.2 ∧ d.2 = a.1.2 := by decide)
    (law2 : ∀ a ∈ S, a.1.2 ≠ a.2 := by decide)
    (law3 : ∀ a ∈ S, a.1.1 = a.1.2 → ∃ b ∈ S, b.1.1 = a.2 ∧ b.1.2 = a.1.1 := by decide) :
    (fromList S).OK where
  finite := List.finite_toSet S
  func h1 _ h2 := Decidable.by_contra fun h =>
    have : IsTrans ((ℕ ×ₗ ℕ) × ℕ) (·.1 < ·.1) := ⟨fun _ _ _ => lt_trans⟩
    (List.chain'_iff_pairwise.1 sorted) |>.imp (fun h => h.ne)
      |>.forall (fun _ _ => (·.symm)) h1 h2 (by rintro ⟨⟩; exact h rfl) rfl
  laws := {
  eq713 := fun h1 h2 => by --TODO variable names are off
    obtain ⟨⟨⟨y, y'⟩,yy⟩, yy_mem, ⟨⟨yy', xyy⟩,x⟩, eq_mem, y_def,
    y'_def, yy'_def, xyy_def, x_def⟩ := eq713 _ h1 _ h2 rfl rfl
    simp only at yy_mem eq_mem y_def y'_def yy_mem yy'_def xyy_def x_def
    exists yy
    rewrite [y_def, y'_def] at yy_mem
    use yy_mem
    use yy'_def ▸xyy_def ▸ x_def ▸ eq_mem
  law2 := fun h => law2 _ h rfl
  law3 := fun h => by
    obtain ⟨⟨⟨x,x'⟩, xxx⟩, xxx_mem, rfl, rfl⟩ := law3 _ h rfl
    exact ⟨xxx, xxx_mem⟩
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
((0,0),1),
((0,1),3),
((0,2),3),
((0,3),0),
((1,0),2),
((1,1),0),
((1,2),1),
((1,3),2),
((1,4),3),
((2,0),2),
((2,2),4),
((2,4),0),
((4,1),2),
((4,2),4),
((4,3),2),
((4,4),1),
]

@[equational_result]
theorem not_817_1426_3862_4065 : ∃ (G : Type) (_ : Magma G), Facts G [713] [817,1426,3862,4065] := by
  have ⟨e, he⟩ : ∃ e : Extension ℕ, e.1 = fromList seed :=
    ⟨⟨_, fromList_ok⟩, rfl⟩
  have rules := fromList_eval' he
  simp [seed, List.mem_cons, List.mem_singleton, forall_eq_or_imp,
    forall_eq] at rules
  refine ⟨GreedyMagma e, inferInstance, e.eq713, fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩
  · have := h 0
    simp [rules] at this
  · have := h 0
    simp [rules] at this
  · have := h 2
    simp [rules] at this
    cases this
  · have := h 0
    simp [rules] at this
    cases this

end Eq713
