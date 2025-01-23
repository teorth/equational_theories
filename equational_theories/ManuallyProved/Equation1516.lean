import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.Data.Finmap
import Mathlib.Data.Finset.Max
import Mathlib.Data.List.Basic
import Mathlib.Data.Finset.Order
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Order.CompletePartialOrder

import Mathlib.Data.Fintype.Card
import equational_theories.FactsSyntax
import equational_theories.FreshGenerator
import equational_theories.Mathlib.Order.Greedy
import equational_theories.EquationalResult
import equational_theories.Equations.All
import equational_theories.ForMathlib.GroupTheory.FreeGroup.ReducedWords


import Mathlib.Data.Rel
import Mathlib.Tactic.Linarith.Frontend
import Init.Core
--import Mathlib.Tactic.Group --This breaks some instance, I haven't understood why exactly

namespace Eq1516

open FreeGroup
open FreshGenerator

private abbrev A := FreeGroup Nat


private abbrev x : Nat → A := FreeGroup.of
private abbrev x₁ := x 1
private abbrev x₂ := x 2
private abbrev x₃ := x 3
private abbrev x₄ := x 4
private abbrev x₅ := x 5
private abbrev x₆ := x 6


/-- We will use `Finmap (fun _ : A => A)` to model the set E. There is no nondependent version of Finmap, so we have
to use a trivial Sigma type. -/
private abbrev TE := Finmap (fun _ : A => A)

notation:63 f:63 " ⬝ " a:64 => Finmap.lookup a f

instance inst_LE_TE: PartialOrder TE where
  le := fun E E' => ∀ {a a'}, a' ∈ E ⬝ a → a' ∈ E' ⬝ a
  le_refl := by tauto
  le_trans := by tauto
  le_antisymm := by
    intro E E' le1 le2
    apply Finmap.ext_lookup
    intro x
    cases ex: E ⬝ x <;> cases ex' : E' ⬝ x
    · rfl
    · have := le2 ex'
      rw [this] at ex
      injection ex
    . have := le1 ex
      rw [this] at ex'
      injection ex'
    · have := le1 ex
      rw [← this, ex']

theorem TE_le_iff (E E' : TE) : E ≤ E' ↔ (∀ a a', a' ∈ E ⬝ a → a' ∈ E' ⬝ a) := by rfl

@[simp]
theorem TE_lookup_isSome {E : TE} {a : A} : (E ⬝ a).isSome = true ↔ a ∈ E :=
Finmap.lookup_isSome

@[simp]
theorem TE_lookup_exists {E : TE} {a : A} : (∃ d, d ∈ (E ⬝ a)) ↔ a ∈ E := by
rw [← TE_lookup_isSome]
cases E ⬝ a <;> tauto

theorem TE_lookup_mem' {E : TE} {a d : A} : d ∈ (E ⬝ a) → a ∈ E := by
rw [← TE_lookup_isSome]
cases E ⬝ a <;> tauto

theorem Finmap.mem_lookup_disjoint_union {α : Type} {β : α → Type} [DecidableEq α] {a : α} {b : β a}
{s₁ : Finmap β} {s₂ : Finmap β} (h : s₁.Disjoint s₂) : b ∈ Finmap.lookup a (s₁ ∪ s₂) ↔ b ∈
Finmap.lookup a s₁ ∨ b ∈ Finmap.lookup a s₂ := by
rw [Finmap.mem_lookup_union]
constructor
· tauto
· intro h'
  cases h' with
  | inl h' => tauto
  | inr h' =>
    right
    have a_in_s2 : a ∈ s₂ := by
      apply Finmap.lookup_isSome.mp
      rw [h']
      rfl
    use Finmap.Disjoint.symm _ _ h a a_in_s2

theorem TE_mem_singleton' : ∀ {x y z w : A},  y ∈ ((Finmap.singleton w z : TE) ⬝ x) ↔ x = w ∧ y = z := by
  intro x y z w
  constructor
  · intro h
    have x_mem := Finmap.mem_of_lookup_eq_some h
    rw [Finmap.mem_singleton] at x_mem
    use x_mem
    rw [x_mem] at h
    simp only [Finmap.lookup_singleton_eq, Option.mem_def, Option.some.injEq] at h
    tauto
  · intro ⟨eq1, eq2⟩
    rw [eq1, eq2]
    simp

@[ext]
structure PartialSolution where
  E : TE
  --A partial solution is a function f : A → A satisfying certain invariants, with finite domain Dom.
  -- (1,1) ∈ E
  fId : 1 ∈ E ⬝ 1
  cond4 : ∀ a ∈ E, ∀ b ∈ E ⬝ a, ∀ c ∈ E ⬝ b,  a⁻¹ ∈ E ⬝ (c * a⁻¹)
  cond5 : ∀ a ∈ E, ∀ a' ∈ E, ∀ d ∈ E ⬝ (a⁻¹), ∀ d' ∈ E ⬝ (a'⁻¹),
     E ⬝ a = E ⬝ a' → d * a = d' * a' → a = a'
  cond6 : ∀ a ∈ E, a⁻¹ ∈ E ⬝ a → a = 1
  cond7 : ∀ a ∈ E, ∀ a' ∈ E, ∀ d ∈ E ⬝ a⁻¹, E ⬝ a = E ⬝ a' → a ≠ a' → d * a ≠ a'
  cond8 : ∀ a ∈ E, 1 ∈ E ⬝ a → a = 1

instance inst_LE_PartialSolution: PartialOrder PartialSolution where
  le x y := x.E ≤ y.E
  le_refl x := by apply le_refl x.E
  le_trans a b c := by apply le_trans (α := TE)
  le_antisymm a b := by
    intros
    apply PartialSolution.ext
    apply le_antisymm <;> assumption

theorem PartialSolution.le_iff (ps ps': PartialSolution) : ps ≤ ps' ↔ ps.E ≤ ps'.E := by rfl

def PartialSolution.DomId (ps : PartialSolution) : 1 ∈ ps.E := by
  apply TE_lookup_isSome.mp
  rw [ps.fId]
  rfl

def PartialSolution.Im (ps : PartialSolution) : Finset A :=
  (ps.E.entries.map Sigma.snd).toFinset

def helper {α β γ} (g : α → β) (f : ∀ b : α, γ (g b)) (h_g : Function.Injective g) (s : Finset α)
: Finmap γ where
  entries := Multiset.map (fun a => ⟨g a, f a⟩) s.1
  nodupKeys := by
    rw [← Multiset.nodup_keys]
    unfold Multiset.keys
    simp only [Multiset.map_map, Function.comp_apply]
    rw [Multiset.nodup_map_iff_of_injective]
    exact s.2
    exact h_g

theorem helper_mem {α β} {γ : β → Type} [DecidableEq β] (g : α → β) (f : ∀ b : α, γ (g b))
(h_g : Function.Injective g) (s : Finset α) (b : β) (c : γ b) :
c ∈ Finmap.lookup b (helper g f h_g s) ↔ ∃ a ∈ s, g a = b ∧ HEq (f a) c := by
  unfold helper
  rw [Finmap.mem_lookup_iff]
  simp


def helper' {α β γ} (g : α → β) (f : ∀ b : α, γ (g b)) (s : Finset α) (d : ∀ x ∈ s, ∀ y ∈ s, g x = g y → x = y)
: Finmap γ where
  entries := Multiset.map (fun a => ⟨g a, f a⟩) s.1
  nodupKeys := by
    rw [← Multiset.nodup_keys]
    unfold Multiset.keys
    simp only [Multiset.map_map, Function.comp_apply]
    rw [Multiset.nodup_map_iff_of_inj_on]
    exact s.2
    exact d

theorem helper'_mem {α β} {γ : β → Type} [DecidableEq β] (g : α → β) (f : ∀ b : α, γ (g b))
(s : Finset α) (d : ∀ x ∈ s, ∀ y ∈ s, g x = g y → x = y) (b : β) (c : γ b) :
c ∈ Finmap.lookup b (helper' g f s d) ↔ ∃ a ∈ s, g a = b ∧ HEq (f a) c := by
  unfold helper'
  rw [Finmap.mem_lookup_iff]
  simp


section extension

structure ExtensionTask where
  ps : PartialSolution
  b : A

namespace ExtensionTask

variable (t : ExtensionTask)

theorem b_ne_1 [b_not_in_dom : Fact (t.b ∉ t.ps.E)] : t.b ≠ 1 := by
  intro eq
  have h := b_not_in_dom
  rw [eq] at h
  apply h.out t.ps.DomId

def preimages_of_b := t.ps.E.keys.filter (fun a' => t.b ∈ t.ps.E ⬝ a')

theorem preimages_of_b_spec (a' : A) : a' ∈ t.preimages_of_b ↔ t.b ∈ t.ps.E ⬝ a' := by
  unfold preimages_of_b
  rw [Finset.mem_filter]
  constructor
  · tauto
  · intro h
    rw [Finmap.mem_keys]
    constructor
    rw [←Finmap.lookup_isSome,h]
    simp
    assumption

def s := t.preimages_of_b.filter (fun a' => a'⁻¹ ∈ t.ps.E)

theorem s_spec (a' : A) : a' ∈ t.s ↔ t.b ∈ t.ps.E ⬝ a' ∧  ∃ d', d' ∈ t.ps.E ⬝ a'⁻¹ := by
  unfold s
  rw [Finset.mem_filter, preimages_of_b_spec, TE_lookup_exists]

theorem preimages_of_b_Dom : t.preimages_of_b ⊆ t.ps.E.keys := Finset.filter_subset _ _

theorem s_preimages_of_b : t.s ⊆ t.preimages_of_b := Finset.filter_subset _ _

theorem s_Dom : t.s ⊆ t.ps.E.keys := by trans <;> apply Finset.filter_subset

def old := (t.ps.E.keys ∪ t.ps.Im) ∪ {t.b}

theorem dom_old (x : A) (h : x ∈ t.ps.E) : x ∈ t.old := by
  unfold old
  simp [Finmap.mem_keys,h]

theorem dom_old_subgroup {t : ExtensionTask} {x : A} (h : x ∈ t.ps.E) : x ∈ Subgroup.closure t.old := by
  apply Subgroup.subset_closure
  simp [dom_old (h:=h)]

theorem dom_old' (x y : A) (h : y ∈ t.ps.E ⬝ x ) : x ∈ t.old := by
  unfold old
  simp [Finmap.mem_keys, Finmap.mem_of_lookup_eq_some h]


theorem dom_old'_subgroup {t : ExtensionTask} {x y : A} (h : y ∈ t.ps.E ⬝ x) : x ∈ Subgroup.closure t.old := by
  apply Subgroup.subset_closure
  simp [dom_old' (h:=h)]

theorem im_old (x y : A) (h : y ∈ t.ps.E ⬝ x) : y ∈ t.old := by
  unfold old
  simp only [PartialSolution.Im, Finset.union_assoc, Finset.mem_union, Multiset.mem_toFinset,
    Multiset.mem_map, Finmap.mem_lookup_iff.symm, Sigma.exists, exists_eq_right,
    Finset.mem_singleton]
  tauto

theorem im_old_subgroup {t : ExtensionTask} {x y : A} (h : y ∈ t.ps.E ⬝ x) : y ∈ Subgroup.closure t.old := by
  apply Subgroup.subset_closure
  simp [im_old (h:=h)]

theorem b_old : t.b ∈ t.old := by
  unfold old
  simp

theorem b_old_subgroup : t.b ∈ Subgroup.closure t.old := by
  apply Subgroup.subset_closure
  simp [b_old]

macro "triv_subgroup" : tactic => `(tactic|
  first |
    (apply Subgroup.one_mem  ) |
    (apply im_old_subgroup ; tauto ) |
    (apply dom_old'_subgroup ; tauto) |
    (rw [← Subgroup.inv_mem_iff]; apply dom_old'_subgroup ; tauto) |
    (apply b_old_subgroup) |
    (rw [Subgroup.inv_mem_iff] ; apply b_old_subgroup)
    )

noncomputable def c := freshGenerator t.old

theorem c_not_old_subgroup : t.c ∉ Subgroup.closure t.old := by
  apply freshGenerator_not_in_span

theorem c_not_old : t.c ∉ t.old := by
  intro h
  apply t.c_not_old_subgroup
  apply Subgroup.subset_closure
  simp [h]

noncomputable def e0 : TE := Finmap.singleton t.b t.c

noncomputable def e1 : TE := helper (fun a' => t.c * a'⁻¹) (fun a' => a'⁻¹) (by intro x y ; simp) t.preimages_of_b

noncomputable def e2 : TE := helper' (fun a' => (t.ps.E ⬝ (a'⁻¹)).iget * a' * t.c⁻¹) (fun a' => a' *  t.c⁻¹) t.s (by
    simp only [mul_left_inj]
    intro a' a'_mem_s a'' a''_mem_s
    eapply t.ps.cond5 a' (t.s_Dom a'_mem_s) a'' (t.s_Dom a''_mem_s) ((t.ps.E ⬝ a'⁻¹).iget) _ ((t.ps.E ⬝ a''⁻¹).iget) _
    rw [(Finset.mem_filter.mp (t.s_preimages_of_b a'_mem_s)).2, (Finset.mem_filter.mp (t.s_preimages_of_b a''_mem_s)).2]
    apply Option.iget_mem
    simp only [TE_lookup_isSome]
    apply (Finset.mem_filter.mp (a'_mem_s)).2
    apply Option.iget_mem
    simp only [TE_lookup_isSome]
    apply (Finset.mem_filter.mp (a''_mem_s)).2
  )

theorem e0_spec : ∀ x y,  y ∈ t.e0 ⬝ x ↔ x = t.b ∧ y = t.c := by
  intro x y
  unfold e0
  apply TE_mem_singleton'

theorem e1_spec : ∀ x y, y ∈ t.e1 ⬝ x ↔ ∃ a', t.b ∈ t.ps.E ⬝ a' ∧ t.c * a'⁻¹ = x ∧ a'⁻¹ = y := by
intro x y
unfold e1
rw [helper_mem]
simp only [heq_eq_eq, Option.mem_def]
constructor
intro ⟨a', h⟩
rw [t.preimages_of_b_spec] at h
use a'
tauto
intro ⟨a', h⟩
use a'
rw [t.preimages_of_b_spec]
tauto

theorem e2_spec : ∀ x y, y ∈ t.e2 ⬝ x ↔ ∃ a' d', t.b ∈ t.ps.E ⬝ a' ∧ d' ∈ t.ps.E ⬝ (a'⁻¹) ∧ d' * a' * t.c⁻¹ = x ∧  a' * t.c⁻¹ = y := by
unfold e2
intro x y
rw [helper'_mem]
simp only [heq_eq_eq, Option.mem_def, exists_and_left]
constructor
intro ⟨a', h⟩
rw [t.s_spec] at h
use a'
rcases h with ⟨⟨eq1, d', eqd'⟩ ,eq2, eq3⟩
use eq1, d', eqd'
rw [eqd'] at eq2
use eq2, eq3
intro ⟨a', eq1, d', eqd', eq2, eq3⟩
use a'
rw [t.s_spec]
use ⟨eq1, d', eqd'⟩
rw [eqd']
use eq2, eq3

noncomputable def newE : TE := t.ps.E ∪ t.e0 ∪ t.e1 ∪ t.e2

theorem disjoint_old_e0 [b_not_in_dom : Fact (t.b ∉ t.ps.E)]: t.ps.E.Disjoint t.e0 := by
  intro x hold he0
  have := TE_lookup_exists.mpr he0
  cases this with
  | intro y h =>
    rw [e0_spec] at h
    cases h with
    | intro left right =>
      rw [left] at hold
      apply b_not_in_dom.out hold

theorem disjoint_old_e1 : t.ps.E.Disjoint t.e1 := by
  intro x hold he1
  have := TE_lookup_exists.mpr he1
  cases this with
  | intro y h =>
    rw [e1_spec] at h
    match h with
    | ⟨a', left, eq, _⟩  =>
      apply fresh_ineq t.old x a'⁻¹
      apply Subgroup.subset_closure
      simp [dom_old _ _ hold]
      simp only [inv_mem_iff]
      apply Subgroup.subset_closure
      simp [dom_old' _ _ _ left]
      exact eq.symm


theorem disjoint_old_e2 : t.ps.E.Disjoint t.e2 := by
  intro x hold he2
  have := TE_lookup_exists.mpr he2
  cases this with
  | intro y h =>
    rw [e2_spec] at h
    match h with
    | ⟨a', d', eq_b_a', eq_d'_a', eq, _⟩  =>
      apply fresh_ineq' t.old (d' * a') x _ _ eq
      · apply Subgroup.mul_mem
        · apply Subgroup.subset_closure
          simp [im_old _ _ _ eq_d'_a']
        · apply Subgroup.subset_closure
          simp [dom_old' _ _ _ eq_b_a']
      · apply Subgroup.subset_closure
        · simp [dom_old _ _ hold]

theorem disjoint_e0_e1 : t.e0.Disjoint t.e1 := by
  intro x he0 he1
  rcases TE_lookup_exists.mpr he0 with ⟨y, e_x_y⟩
  rcases TE_lookup_exists.mpr he1 with ⟨z, e_x_z⟩
  rw [e0_spec, e1_spec] at *
  rcases e_x_y with ⟨eq_x_b, eq_y_c⟩
  rcases e_x_z with ⟨a', e_a'_b, eq, _⟩
  apply fresh_ineq t.old x a'⁻¹ _ _ eq.symm
  · rw [eq_x_b]
    apply Subgroup.subset_closure
    simp [b_old]
  · simp only [inv_mem_iff]
    apply Subgroup.subset_closure
    simp [dom_old' _ _ _ e_a'_b]

theorem disjoint_e0_e2 : t.e0.Disjoint t.e2 := by
  intro x he0 he2
  rcases TE_lookup_exists.mpr he0 with ⟨y, e_x_y⟩
  rcases TE_lookup_exists.mpr he2 with ⟨z, e_x_z⟩
  rw [e0_spec, e2_spec] at *
  rcases e_x_y with ⟨eq_x_b, eq_y_c⟩
  rcases e_x_z with ⟨a', d', e_a'_b, e_a'_inv_d', eq, _⟩
  apply fresh_ineq' t.old _ _ _ _ eq
  · apply Subgroup.mul_mem
    · apply Subgroup.subset_closure
      simp [im_old _ _ _ e_a'_inv_d']
    · apply Subgroup.subset_closure
      simp [dom_old' _ _ _ e_a'_b]
  · apply Subgroup.subset_closure
    rw [eq_x_b]
    simp [b_old]

theorem disjoint_e1_e2 : t.e1.Disjoint t.e2 := by
  intro x he1 he2
  rcases TE_lookup_exists.mpr he1 with ⟨y, e_x_y⟩
  rcases TE_lookup_exists.mpr he2 with ⟨z, e_x_z⟩
  rw [e1_spec, e2_spec] at *
  rcases e_x_y with ⟨a', e_a'_b, eq1, _⟩
  rcases e_x_z with ⟨a'', d'', e_a''_b, e_a''_inv_d'', eq2, _⟩
  rw [← eq1] at eq2
  apply fresh_ineq'' _ _ _ _ _ eq2
  · apply Subgroup.mul_mem
    · apply Subgroup.subset_closure
      simp [im_old _ _ _ e_a''_inv_d'']
    · apply Subgroup.subset_closure
      simp [dom_old' _ _ _ e_a''_b]
  · simp only [inv_mem_iff]
    apply Subgroup.subset_closure
    simp [dom_old' _ _ _ e_a'_b]

variable [b_not_in_dom : Fact (t.b ∉ t.ps.E)]

theorem newE_spec  : ∀ x y,  y ∈ t.newE ⬝ x ↔ ((((y ∈ t.ps.E ⬝ x) ∨ (x = t.b ∧ y = t.c)) ∨ (∃ a', t.b ∈ t.ps.E ⬝ a' ∧ t.c * a'⁻¹ = x ∧ a'⁻¹ = y))
∨ ∃ a' d', t.b ∈ t.ps.E ⬝ a' ∧ d' ∈ t.ps.E ⬝ (a'⁻¹) ∧  d' * a' * t.c⁻¹ = x ∧ a' * t.c⁻¹ = y) := by
  intro x y
  unfold newE
  repeat rw [Finmap.mem_lookup_disjoint_union]
  rw [t.e0_spec, t.e1_spec, t.e2_spec]
  · apply disjoint_old_e0
  · simp [Finmap.disjoint_union_left, disjoint_old_e1, disjoint_e0_e1]
  · simp [Finmap.disjoint_union_left, disjoint_old_e2, disjoint_e0_e2, disjoint_e1_e2]

theorem newE_spec_old_imp : ∀ {x y}, y ∈ t.ps.E ⬝ x → y ∈ t.newE ⬝ x := by
  intros
  rw [newE_spec]
  tauto

theorem newE_b : t.c ∈ t.newE ⬝ t.b := by rw [newE_spec]; tauto

theorem newE_eq_c : ∀ x, t.c ∈ t.newE ⬝ x → x = t.b := by
  intro x e_x_c
  rw [newE_spec] at e_x_c
  rcases e_x_c  with ⟨⟨old | e0⟩ | e1⟩ | e2
  · exfalso
    apply freshGenerator_not_in_span (S := t.old)
    triv_subgroup
  · tauto
  · exfalso
    rcases e1 with ⟨a', e_a'_b, eq, eq'⟩
    apply_fun Inv.inv at eq'
    rw [inv_inv] at eq'
    rw [eq'] at e_a'_b
    apply freshGenerator_not_in_span (S := t.old)
    triv_subgroup
  · exfalso
    rcases e2 with ⟨a', d', e_a'_b, e_a'_inv_d', eq, right⟩
    have : a' * t.c⁻¹ = t.c * 1 := by simp [right]
    apply fresh_ineq'' (eq:= this)
    · triv_subgroup
    · apply Subgroup.one_mem



theorem newE_dom_and_inv : ∀ x y, y ∈ t.newE ⬝ x → x⁻¹ ∈ t.newE → y ∈ t.ps.E ⬝ x ∨ (x = t.b ∧ y = t.c) := by
  intro x y e_x_y e_x_inv_mem
  rw [← TE_lookup_exists] at e_x_inv_mem
  rcases e_x_inv_mem with ⟨z, e_x_inv_z⟩
  rw [newE_spec] at *
  rcases e_x_y  with ⟨⟨old | e0⟩ | e1⟩ | e2
  · tauto
  · tauto
  . exfalso
    rcases e1 with ⟨a', e_a'_b, eq, _⟩
    rcases e_x_inv_z with ⟨⟨old' | e0'⟩ | e1'⟩ | e2'
    · apply fresh_ineq (eq:= eq.symm)
      · rw [← Subgroup.inv_mem_iff]
        apply dom_old'_subgroup old'
      · simp [dom_old'_subgroup e_a'_b]
    · apply fresh_ineq (eq:= eq.symm)
      · rw [← Subgroup.inv_mem_iff, e0'.1]
        apply b_old_subgroup
      · simp [dom_old'_subgroup e_a'_b]
    · rcases e1' with ⟨a'', e_a''_b, eq', _⟩
      rw [← eq] at eq'
      simp only [mul_inv_rev, inv_inv] at eq'
      apply fresh_ineq'' (eq:= eq'.symm)
      · simp [dom_old'_subgroup e_a'_b]
      · simp [dom_old'_subgroup e_a''_b]
    · rcases e2' with ⟨a'', d'', e_a''_b, e_a''_inv_d'', eq', _⟩
      rw [← eq] at eq'
      simp only [mul_inv_rev, inv_inv, mul_left_inj] at eq'
      apply t.ps.cond7 a'' (TE_lookup_mem' e_a''_b) a' (TE_lookup_mem' e_a'_b) d'' e_a''_inv_d''
      rw [e_a'_b, e_a''_b]
      intro eq_a'_a''
      have eq_d''_1 : d'' = 1 := by
        rw [eq_a'_a''] at eq'
        simp only [mul_left_inj, mul_left_eq_self] at eq'
        exact eq'
      have eq_a''_1 : (a'')⁻¹ = 1 := by
        apply t.ps.cond8
        apply TE_lookup_mem' e_a''_inv_d''
        rw [← eq_d''_1]
        apply e_a''_inv_d''
      apply b_ne_1 t
      simp only [inv_eq_one] at eq_a''_1
      rw [eq_a''_1, t.ps.fId] at e_a''_b
      injection e_a''_b
      tauto
      tauto
  · exfalso
    rcases e2 with ⟨a', d', e_a'_b, e_a'_inv_d', eq, _⟩
    rcases e_x_inv_z with ⟨⟨old' | e0'⟩ | e1'⟩ | e2'
    · apply fresh_ineq' (eq:= eq)
      · apply Subgroup.mul_mem
        · simp [im_old_subgroup e_a'_inv_d']
        · simp [dom_old'_subgroup e_a'_b]
      · rw [← Subgroup.inv_mem_iff]
        apply dom_old'_subgroup old'
    · apply fresh_ineq' (eq:= eq)
      · apply Subgroup.mul_mem
        · simp [im_old_subgroup e_a'_inv_d']
        · simp [dom_old'_subgroup e_a'_b]
      · rw [← Subgroup.inv_mem_iff, e0'.1]
        apply b_old_subgroup
    · rcases e1' with ⟨a'', e_a''_b, eq', _⟩ -- this is a symmetric case, could be specialized to a lemma
      rw [← eq] at eq'
      apply_fun (fun x => x⁻¹) at eq'
      simp only [mul_inv_rev, inv_inv, mul_left_inj] at eq'
      apply t.ps.cond7 a' (TE_lookup_mem' e_a'_b) a'' (TE_lookup_mem' e_a''_b) d' e_a'_inv_d'
      rw [e_a'_b, e_a''_b]
      intro eq_a'_a''
      have eq_d'_1 : d' = 1 := by
        rw [eq_a'_a''] at eq'
        simp only [self_eq_mul_left] at eq'
        exact eq'
      have eq_a'_1 : (a')⁻¹ = 1 := by
        apply t.ps.cond8
        apply TE_lookup_mem' e_a'_inv_d'
        rw [← eq_d'_1]
        apply e_a'_inv_d'
      apply b_ne_1 t
      simp only [inv_eq_one] at eq_a'_1
      rw [eq_a'_1, t.ps.fId] at e_a'_b
      injection e_a'_b
      tauto
      tauto
    · rcases e2' with ⟨a'', d'', e_a''_b, e_a''_inv_d'', eq', _⟩
      rw [← eq] at eq'
      simp only [mul_inv_rev, inv_inv] at eq'
      apply fresh_ineq'' (eq := eq') <;> apply Subgroup.mul_mem <;>
      simp [im_old_subgroup e_a''_inv_d'', im_old_subgroup e_a'_inv_d', dom_old'_subgroup e_a'_b,
      dom_old'_subgroup e_a''_b]

-- stronger variant of the above theorem, by applying it symmetrically, excluding one impossible case
theorem newE_dom_and_inv' : ∀ x y, y ∈ t.newE ⬝ x → x⁻¹ ∈ t.newE → y ∈ t.ps.E ⬝ x ∧ t.ps.E ⬝ x⁻¹ = t.newE ⬝ x⁻¹ ∨
(x = t.b ∧ y = t.c) ∧ t.ps.E ⬝ x⁻¹ = t.newE ⬝ x⁻¹ ∨ y ∈ t.ps.E ⬝ x ∧ x⁻¹ = t.b ∧ t.c ∈ t.newE ⬝ x⁻¹ := by
  intro x y e_x_y x_inv_mem
  rcases (newE_dom_and_inv t x y e_x_y x_inv_mem) with old | e0
  · rw [← TE_lookup_exists] at x_inv_mem
    rcases (x_inv_mem) with ⟨d, e_x_inv_d⟩
    rcases (newE_dom_and_inv t x⁻¹ d e_x_inv_d (by simp [TE_lookup_mem' e_x_y])) with old' | e0'
    · rw [e_x_inv_d,old']
      simp [old]
    · rw [e0'.2] at e_x_inv_d
      simp [old, e0'.1, e_x_inv_d]
  · rw [← TE_lookup_exists] at x_inv_mem
    rcases (x_inv_mem) with ⟨d, e_x_inv_d⟩
    rcases (newE_dom_and_inv t x⁻¹ d e_x_inv_d (by simp [TE_lookup_mem' e_x_y])) with old' | e0'
    · rw [e_x_inv_d, old']
      simp [e0]
    · exfalso
      apply ne_inv_of_ne_one t.b_ne_1
      nth_rw 1 [← e0.1, ← e0'.1]
      simp

theorem extension_cond4 : ∀ a ∈ t.newE, ∀ b ∈ t.newE ⬝ a, ∀ c ∈ t.newE ⬝ b, a⁻¹ ∈ t.newE ⬝ c * a⁻¹ := by
  intro x x_dom y e_x_y z e_y_z
  rw [newE_spec] at *
  rcases e_x_y  with ⟨⟨old | e0⟩ | e1⟩ | e2
  · rcases e_y_z with ⟨⟨old' | e0'⟩ | e1'⟩ | e2'
    · have := t.ps.cond4 x (TE_lookup_mem' old) y old z old'
      tauto
    · left
      right
      use x
      simp [old, e0'.1.symm, e0'.2]
    · exfalso
      rcases e1' with ⟨a', e_a'_b, eq, _⟩
      apply fresh_ineq (eq := eq.symm)
      · apply Subgroup.subset_closure
        simp [im_old _ _ _ old]
      · simp only [inv_mem_iff]
        apply Subgroup.subset_closure
        simp [dom_old' _ _ _ e_a'_b]
    · exfalso
      rcases e2' with ⟨a', d', e_a'_b, e_a'_inv_d', eq, _⟩
      apply fresh_ineq' (eq:= eq)
      · apply Subgroup.mul_mem
        · apply Subgroup.subset_closure
          simp [im_old _ _ _ e_a'_inv_d']
        · apply Subgroup.subset_closure
          simp [dom_old' _ _ _ e_a'_b]
      · apply Subgroup.subset_closure
        simp [im_old _ _ _ old]
  · rcases e_y_z with ⟨⟨old' | e0'⟩ | e1'⟩ | e2'
    · exfalso
      apply freshGenerator_not_in_span (S := t.old)
      unfold c at e0
      rw [← e0.2 ]
      apply Subgroup.subset_closure
      simp [dom_old' _ _ _ old']
    · exfalso
      apply freshGenerator_not_in_span (S := t.old)
      unfold c at *
      rw [← e0.2, e0'.1]
      apply Subgroup.subset_closure
      simp [b_old]
    · exfalso
      rcases e1' with ⟨a', e_a'_b, eq, _⟩
      have a'_eq_1 : a' = 1 := by
        rw [e0.2] at eq
        simp only [mul_right_eq_self, inv_eq_one] at eq
        exact eq
      apply t.b_ne_1
      rw [a'_eq_1, t.ps.fId] at e_a'_b
      injection e_a'_b
      tauto
    · exfalso
      rcases e2' with ⟨a', d', e_a'_b, e_a'_inv_d', eq, _⟩
      have eq' : d' * a' * t.c⁻¹ = t.c * 1 := by
        simp[eq, e0.2]
      apply fresh_ineq'' (eq:=eq')
      · apply Subgroup.mul_mem
        · apply Subgroup.subset_closure
          simp [im_old _ _ _ e_a'_inv_d']
        · apply Subgroup.subset_closure
          simp [dom_old' _ _ _ e_a'_b]
      · apply Subgroup.one_mem
  · rcases e_y_z with ⟨⟨old' | e0'⟩ | e1'⟩ | e2'
    · right
      rcases e1 with ⟨a', e_a'_b, eq, eq_a'_inv_y⟩
      use a', z, e_a'_b
      rw [eq_a'_inv_y]
      use old'
      rw [← eq]
      simp [mul_assoc]
    · exfalso
      rcases e1 with ⟨a', e_a'_b, eq, eq_a'_inv_y⟩
      have eq_a'_1 : a' = 1 := by
        apply t.ps.cond6
        apply TE_lookup_mem' e_a'_b
        rw [eq_a'_inv_y, e0'.1]
        exact e_a'_b
      apply t.b_ne_1
      rw [← e0'.1, ← eq_a'_inv_y, eq_a'_1]
      simp
    · exfalso
      rcases e1 with ⟨a', e_a'_b, eq, eq_a'_inv_y⟩
      rcases e1' with ⟨a'', e_a''_b, eq, eq_a''_inv_z⟩
      rw [← eq_a'_inv_y] at eq
      apply fresh_ineq (eq:= eq.symm)
      · simp only [inv_mem_iff]
        apply Subgroup.subset_closure
        simp [dom_old' _ _ _ e_a'_b]
      · simp only [inv_mem_iff]
        apply Subgroup.subset_closure
        simp [dom_old' _ _ _ e_a''_b]
    · exfalso
      rcases e1 with ⟨a', e_a'_b, eq, eq_a'_inv_y⟩
      rcases e2' with ⟨a'', d'', e_a''_b, e_a''_inv_d'', eq, _⟩
      rw [← eq_a'_inv_y] at eq
      apply fresh_ineq' (eq:=eq)
      · apply Subgroup.mul_mem
        · apply Subgroup.subset_closure
          simp [im_old _ _ _ e_a''_inv_d'']
        · apply Subgroup.subset_closure
          simp [dom_old' _ _ _ e_a''_b]
      · apply Subgroup.inv_mem
        apply Subgroup.subset_closure
        simp [dom_old' (h := e_a'_b)]
  · rcases e2 with ⟨a', d', e_a'_b, e_a'_inv_d', _, eq⟩
    have a'_mem : a' ∈ Subgroup.closure t.old := by
      apply dom_old'_subgroup e_a'_b
    rcases e_y_z with ⟨⟨old' | e0'⟩ | e1'⟩ | e2'
    · exfalso
      apply (fresh_ineq' (eq := eq))
      · exact a'_mem
      · exact dom_old'_subgroup old'
    · exfalso
      apply (fresh_ineq' (eq := eq))
      · exact a'_mem
      · rw [e0'.1]
        apply b_old_subgroup
    · exfalso
      rcases e1' with ⟨a'', e_a''_b, eq', eq_a''_inv_z⟩
      rw [← eq'] at eq
      apply (fresh_ineq'' (eq := eq))
      · exact a'_mem
      · simp [dom_old'_subgroup e_a''_b]
    · exfalso
      rcases e2' with ⟨a'', d'', e_a''_b, e_a''_inv_d'', eq', _⟩
      apply t.ps.cond7 a'' (TE_lookup_mem' e_a''_b) a' (TE_lookup_mem' e_a'_b) d'' e_a''_inv_d''
      · rw [e_a'_b, e_a''_b]
      · intro eq_a'_a''
        have eq_d''_1 : d'' = 1 := by
          rw [← eq, eq_a'_a''] at eq'
          simp only [mul_left_inj, mul_left_eq_self] at eq'
          exact eq'
        have eq_a''_1 : (a'')⁻¹ = 1 := by
          apply t.ps.cond8
          apply TE_lookup_mem' e_a''_inv_d''
          rw [← eq_d''_1]
          apply e_a''_inv_d''
        apply b_ne_1 t
        simp only [inv_eq_one] at eq_a''_1
        rw [eq_a''_1, t.ps.fId] at e_a''_b
        injection e_a''_b
        tauto
      · rw [← eq'] at eq
        simp only [mul_left_inj] at eq
        tauto

theorem extension_cond5_old_old (t : ExtensionTask) (a' : A) (a'_mem : a' ∈ t.newE) (a'' : A)
  (a''_mem : a'' ∈ t.newE) (d' : A) (d'' : A)
  (eq1 : t.newE ⬝ a' = t.newE ⬝ a'') (eq2 : d' * a' = d'' * a'')
  (old : d' ∈ t.ps.E ⬝ a'⁻¹ ∧ t.ps.E ⬝ a'⁻¹⁻¹ = t.newE ⬝ a'⁻¹⁻¹)
  (old' : d'' ∈ t.ps.E ⬝ a''⁻¹ ∧ t.ps.E ⬝ a''⁻¹⁻¹ = t.newE ⬝ a''⁻¹⁻¹) : a' = a'' := by
  apply t.ps.cond5
  · rw [inv_inv] at old
    rw [←TE_lookup_isSome,← old.2,TE_lookup_isSome] at a'_mem
    exact a'_mem
  · rw [inv_inv] at old'
    rw [←TE_lookup_isSome,← old'.2,TE_lookup_isSome] at a''_mem
    exact a''_mem
  · exact old.1
  · exact old'.1
  · rewrite [inv_inv] at old old'
    rw [old.2, old'.2, eq1]
  . exact eq2

theorem extension_cond5_old_new1 (t : ExtensionTask) (a' : A) (a'' : A)
  (d' : A) (d'' : A)
  (eq2 : d' * a' = d'' * a'')
  (old : d' ∈ t.ps.E ⬝ a'⁻¹)
  (eq_a''_inv_b : a''⁻¹ = t.b)
  (eq_d''_c : d'' = t.c)
  : False := by
  rw [eq_d''_c] at eq2
  apply fresh_ineq (eq:= eq2)
  · apply Subgroup.mul_mem
    · exact im_old_subgroup old
    · rw [← Subgroup.inv_mem_iff]
      exact dom_old'_subgroup old
  · rw [← Subgroup.inv_mem_iff, eq_a''_inv_b]
    exact t.b_old_subgroup

theorem extension_cond5_old_new2 (t : ExtensionTask) (a' : A) (a'' : A)
  (eq1 : t.newE ⬝ a' = t.newE ⬝ a'')
  (old2 : t.ps.E ⬝ a'⁻¹⁻¹ = t.newE ⬝ a'⁻¹⁻¹)
  (new3 : t.c ∈ t.newE ⬝ a''⁻¹⁻¹) : False := by
  rw [inv_inv] at *
  rw [← eq1, ← old2] at new3
  apply freshGenerator_not_in_span (α := Nat)
  apply im_old_subgroup
  exact new3

theorem extension_cond5_new1_new1 (t : ExtensionTask) (a' : A) (a'' : A)
  (new1 : (a'⁻¹ = t.b))
  (new1' : (a''⁻¹ = t.b)) : a' = a'' := by
  apply_fun (fun x => x⁻¹)
  · simp [new1, new1']
  · exact inv_injective

theorem extension_cond5_new1_new2 (t : ExtensionTask) (a' : A) (a'' : A)
  (d' : A) (d'' : A)
  (eq2 : d' * a' = d'' * a'')
  (eq_a'_inv_b : (a'⁻¹ = t.b)) (eq_d'_c : d' = t.c)
  (e_a''_inv_d'' : d'' ∈ t.ps.E ⬝ a''⁻¹)  (eq_a''_b : a''⁻¹⁻¹ = t.b) : False := by
  rw [eq_d'_c] at eq2
  apply fresh_ineq (eq:= eq2.symm)
  · apply Subgroup.mul_mem
    · apply im_old_subgroup e_a''_inv_d''
    · rw [inv_inv] at *
      rw [eq_a''_b]
      apply b_old_subgroup
  · rw [← Subgroup.inv_mem_iff, eq_a'_inv_b]
    apply b_old_subgroup




theorem extension_cond5 : ∀ a ∈ t.newE, ∀ a' ∈ t.newE, ∀ d ∈ t.newE ⬝ a⁻¹, ∀ d' ∈ t.newE ⬝ a'⁻¹, t.newE ⬝ a = t.newE ⬝ a' → d * a = d' * a' → a = a' := by
  intro a' a'_mem a'' a''_mem d' e_a'_inv_d' d'' e_a''_inv_d'' eq1 eq2
  rcases (newE_dom_and_inv' t a'⁻¹ d' e_a'_inv_d' (by simpa)) with old | new1 | new2
  · rcases (newE_dom_and_inv' t a''⁻¹ d'' e_a''_inv_d'' (by simpa)) with old' | new1' | new2'
    · apply extension_cond5_old_old t a' _ a'' <;> assumption
    . exfalso
      apply extension_cond5_old_new1 t a' a'' d' d'' <;> tauto
    · exfalso
      apply extension_cond5_old_new2 t a' a'' <;> tauto
  · rcases (newE_dom_and_inv' t a''⁻¹ d'' e_a''_inv_d'' (by simpa)) with old' | new1' | new2'
    · exfalso
      apply extension_cond5_old_new1 t a'' a' d'' d' <;> tauto
    · apply extension_cond5_new1_new1 t a' a'' <;> tauto
    · exfalso
      apply extension_cond5_new1_new2 t a' a'' d' d'' <;> tauto
  · rcases (newE_dom_and_inv' t a''⁻¹ d'' e_a''_inv_d'' (by simpa)) with old' | new1' | new2'
    · exfalso
      apply extension_cond5_old_new2 t a'' a' <;> tauto
    · exfalso
      apply extension_cond5_new1_new2 t a'' a' d'' d' <;> tauto
    · rw [inv_inv] at *
      rw [new2.2.1, new2'.2.1]

theorem extension_cond6 (a : A) : a ∈ t.newE → a⁻¹ ∈ t.newE ⬝ a → a = 1 := by
  intro a_mem eq
  rw [newE_spec] at eq
  rcases eq with ⟨⟨old | e0⟩ | e1⟩ | e2
  · apply t.ps.cond6 a (TE_lookup_mem' old) old
  · exfalso
    apply freshGenerator_not_in_span (S := t.old)
    unfold c at *
    rw [← e0.2, e0.1]
    simp [b_old_subgroup]
  · rcases e1 with ⟨a', e_a'_b, eq, eq_a'_inv_y⟩
    exfalso
    apply fresh_ineq (eq:= eq.symm)
    · simp only [inv_inj] at eq_a'_inv_y
      rw [← eq_a'_inv_y]
      apply dom_old'_subgroup e_a'_b
    · simp [dom_old'_subgroup e_a'_b]
  · rcases e2 with ⟨a', d', e_a'_b, e_a'_inv_d', eq, eq'⟩
    exfalso
    rw [←eq] at eq'
    simp only [mul_inv_rev, inv_inv] at eq'
    apply fresh_ineq'' (eq:= eq')
    · apply dom_old'_subgroup e_a'_b
    · apply Subgroup.mul_mem
      · simp [dom_old'_subgroup e_a'_b]
      · simp [im_old_subgroup e_a'_inv_d']

theorem extension_cond7  (a : A) :
  a ∈ t.newE → ∀ a' ∈ t.newE, ∀ d ∈ t.newE ⬝ a⁻¹, t.newE ⬝ a = t.newE ⬝ a' → a ≠ a' → d * a ≠ a' := by
  intro a_mem a' a'_mem d e_a_inv_d eq_e_a_e_a' ineq_a_a'
  rw [← TE_lookup_exists] at a'_mem
  rcases a'_mem with ⟨d', e_a'_d'⟩
  rw [newE_spec] at e_a'_d'
  rcases inv_inv a ▸ newE_dom_and_inv' t a⁻¹ d e_a_inv_d (by simp [a_mem]) with old | new1 | new2
  · rcases e_a'_d' with ⟨⟨old' | e0'⟩ | e1'⟩ | e2'
    · apply t.ps.cond7
      · have old'' := newE_spec_old_imp _ old'
        rw [old'',← old.2] at eq_e_a_e_a'
        apply TE_lookup_mem' eq_e_a_e_a'
      · apply TE_lookup_mem' old'
      · apply old.1
      · have old'' := newE_spec_old_imp _  old'
        rw [old', old.2, eq_e_a_e_a',old'']
      · assumption
    · rw [e0'.1, newE_b, ← old.2] at eq_e_a_e_a'
      exfalso
      apply freshGenerator_not_in_span (S := t.old)
      apply im_old_subgroup eq_e_a_e_a'
    · rcases e1' with ⟨a'', e_a''_b, eq', eq_a''_inv_d⟩
      intro eq
      apply fresh_ineq (eq := eq'.symm)
      · rw [← eq]
        apply Subgroup.mul_mem
        · apply im_old_subgroup old.1
        · rw [← Subgroup.inv_mem_iff]
          apply dom_old'_subgroup old.1
      · simp [dom_old'_subgroup e_a''_b]
    · rcases e2' with ⟨a'', d'', e_a''_b, e_a''_inv_d'', eq, eq'⟩
      intro eq''
      apply fresh_ineq' (eq:= eq)
      · apply Subgroup.mul_mem <;> triv_subgroup
      · rw [← eq'']
        apply Subgroup.mul_mem <;> triv_subgroup
  · rcases new1 with ⟨⟨eq_a_inv_b, eq_d_c⟩, eq⟩
    rw [eq_d_c]
    apply_fun (fun x => x⁻¹) at eq_a_inv_b
    simp only [inv_inv] at eq_a_inv_b
    rw [eq_a_inv_b]
    rcases e_a'_d' with ⟨⟨old' | e0'⟩ | e1'⟩ | e2'
    · symm
      apply fresh_ineq <;> triv_subgroup
    · symm
      rw [e0'.1]
      apply fresh_ineq <;> triv_subgroup
    · rcases e1' with ⟨a'', e_a''_b, eq', eq_a''_inv_d⟩
      rw [← eq']
      simp only [ne_eq, mul_right_inj, inv_inj]
      intro eq
      rw [← eq] at e_a''_b
      apply b_not_in_dom.out
      apply TE_lookup_mem' e_a''_b
    · rcases e2' with ⟨a'', d'', e_a''_b, e_a''_inv_d', eq, eq''⟩
      rw [← eq]
      symm
      apply fresh_ineq''
      · apply Subgroup.mul_mem <;> triv_subgroup
      · triv_subgroup
  · rcases new2 with ⟨e_a_inv_d, eq_a_b, eq_e_a_c⟩
    rw [eq_a_b]
    rw [eq_e_a_c] at eq_e_a_e_a'
    rw [← newE_eq_c t a'] at eq_a_b
    exfalso
    tauto
    tauto

theorem extension_cond8  (a : A) : a ∈ t.newE → 1 ∈ t.newE ⬝ a → a = 1 := by
  intro a_mem e_a_1
  rw [newE_spec] at e_a_1
  rcases e_a_1 with ⟨⟨old | e0⟩ | e1⟩ | e2
  · apply t.ps.cond8 a (TE_lookup_mem' old) old
  · exfalso
    apply FreeGroup.of_ne_one _ (e0.2.symm)
  · rcases e1 with ⟨a', e_a'_b, eq, eq_a'_inv_y⟩
    exfalso
    apply t.b_ne_1
    simp only [inv_eq_one] at eq_a'_inv_y
    rw [eq_a'_inv_y, t.ps.fId] at e_a'_b
    injection e_a'_b
    tauto
  · rcases e2 with ⟨a', d', e_a'_b, e_a'_inv_d', eq, eq'⟩
    exfalso
    apply fresh_ineq' (eq := eq')
    · apply dom_old'_subgroup e_a'_b
    · apply Subgroup.one_mem

noncomputable def extension : PartialSolution := by
  use t.newE
  case fId =>
    rw [newE_spec]
    simp [t.ps.fId]
  case cond4 => apply extension_cond4
  case cond5 => apply extension_cond5
  case cond6 => apply extension_cond6
  case cond7 => apply extension_cond7
  case cond8 => apply extension_cond8

theorem extension_spec : t.ps.E ≤ t.newE ∧ ∃ c, c ∈ t.newE ⬝ t.b := by
  use newE_spec_old_imp t
  use t.c
  apply t.newE_b

end ExtensionTask

section extension2
namespace ExtensionTask

variable (t : ExtensionTask)

noncomputable def newE2 := t.ps.E ∪ (Finmap.singleton t.c (t.b*t.c))

theorem old_ne_c (x : A) : x ∈ t.old → x ≠ t.c := by
  intro mem h
  rw [h] at mem
  apply freshGenerator_not_in_span (S := t.old)
  apply Subgroup.subset_closure
  apply mem

theorem newE2_disjoint : Finmap.Disjoint t.ps.E (Finmap.singleton t.c (t.b*t.c)) := by
  intro x x_mem
  simp only [Finmap.mem_singleton]
  apply old_ne_c
  apply dom_old
  assumption

theorem newE2_spec {x y : A} : y ∈ t.newE2 ⬝ x ↔ y ∈ t.ps.E ⬝ x ∨ x = t.c ∧ y = t.b*t.c:= by
  unfold newE2
  repeat rw [Finmap.mem_lookup_disjoint_union]
  repeat rw [TE_mem_singleton']
  · unfold Finmap.Disjoint
    simp only [Finmap.mem_singleton]
    intro x h
    apply old_ne_c
    apply dom_old
    exact h

theorem newE2_of_old {x y : A} : y ∈ t.ps.E ⬝ x → y ∈ t.newE2 ⬝ x := by
  rw [newE2_spec]
  tauto


theorem newE2_comp {x y z : A} [b_ne_1 : Fact (t.b ≠ 1)] :  y ∈ t.newE2 ⬝ x → z ∈ t.newE2 ⬝ y → y ∈ t.ps.E ⬝ x ∧ z ∈ t.ps.E ⬝ y := by
  repeat rw [newE2_spec]
  rintro (old | new) (old' | new')
  · tauto
  · exfalso
    apply t.old_ne_c
    apply im_old
    exact old
    tauto
  · exfalso
    apply fresh_ineq''' (eq:=new.2) <;> triv_subgroup
  · exfalso
    apply b_ne_1.out
    have : t.b * t.c = t.c := by rw [← new.2, new'.1]
    simp only [mul_left_eq_self] at this
    assumption

theorem newE2_dom_and_inv {x y z :A } : y ∈ t.newE2 ⬝ x → z ∈ t.newE2 ⬝ x⁻¹ → y ∈ t.ps.E ⬝ x ∧ z ∈ t.ps.E ⬝ x⁻¹  := by
  repeat rw [newE2_spec]
  rintro (old | new) (old' | new')
  · tauto
  · exfalso
    apply freshGenerator_not_in_span (S := t.old)
    unfold c at new'
    rw [← new'.1]
    simp only [inv_mem_iff]
    triv_subgroup
  · exfalso
    apply freshGenerator_not_in_span (S := t.old)
    unfold c at new
    rw [← new.1]
    triv_subgroup
  · exfalso
    have : t.c * 1 = 1 * (t.c)⁻¹ := by nth_rw 1 [← new.1] ; rw [← new'.1] ; simp
    apply fresh_ineq'' (eq:= this.symm) <;> apply Subgroup.one_mem

noncomputable def extension2 [b_ne_1 : Fact (t.b ≠ 1)] : PartialSolution where
  E := t.newE2
  fId := by
    rw [newE2_spec]
    simp [t.ps.fId]
  cond4 := by
    intro a a_mem b b_mem c c_mem
    apply newE2_of_old
    have this := newE2_comp t b_mem c_mem
    apply t.ps.cond4 a (TE_lookup_mem' this.1) b this.1 c this.2
  cond5 := by
    intro a a_mem a' a'_mem d e_a_inv_d d' e_a'_inv_d' eq
    rw [← TE_lookup_exists] at a_mem
    rcases a_mem with ⟨b, e_a_b⟩
    have e_a'_b : b ∈ t.newE2 ⬝ a' := eq ▸ e_a_b
    obtain ⟨e_a_b, e_a_inv_d⟩ := t.newE2_dom_and_inv e_a_b e_a_inv_d
    obtain ⟨e_a'_b,e_a'_inv_d'⟩ := t.newE2_dom_and_inv e_a'_b e_a'_inv_d'
    apply t.ps.cond5 a (TE_lookup_mem' e_a_b) a' (TE_lookup_mem' e_a'_b) d e_a_inv_d d' e_a'_inv_d'
    rw [e_a_b,e_a'_b]
  cond6 := by
    intro a a_mem
    rw [newE2_spec]
    rintro (old | new)
    · apply t.ps.cond6
      apply TE_lookup_mem' old
      apply old
    · exfalso
      have : t.b⁻¹ * t.c⁻¹ = t.c * 1 := by rw [← new.1,new.2,new.1] ; simp
      apply fresh_ineq'' (eq := this)
      · triv_subgroup
      · apply Subgroup.one_mem
  cond7 := by
    intro a a_mem a' a'_mem d e_a_inv_d eq
    rw [← TE_lookup_exists] at a_mem
    rcases a_mem with ⟨b, e_a_b⟩
    obtain ⟨e'_a_b, e_a_inv_d⟩ := t.newE2_dom_and_inv e_a_b e_a_inv_d
    have e_a'_b : b ∈ t.newE2 ⬝ a' := eq ▸ e_a_b
    rw [newE2_spec] at e_a'_b
    cases e_a'_b with
    | inl e_a'_b =>
      apply t.ps.cond7 a (TE_lookup_mem' e'_a_b) a' (TE_lookup_mem' e_a'_b) d e_a_inv_d
      rw [e_a'_b, e'_a_b]
    | inr h =>
      exfalso
      apply fresh_ineq''' (eq := h.2) <;> triv_subgroup
  cond8 := by
    intro a a_mem
    rw [newE2_spec]
    rintro (old | new)
    · apply t.ps.cond8 a (TE_lookup_mem' old) old
    · exfalso
      apply fresh_ineq''' (eq := new.2)
      · apply Subgroup.one_mem
      · triv_subgroup

theorem extension2_E [b_ne_1 : Fact (t.b ≠ 1)] : t.extension2.E = t.newE2 := rfl

theorem extension2_spec : t.ps.E ≤ t.newE2 ∧
Finset.card {c ∈ t.newE2.keys | (t.b*c) ∈ t.newE2 ⬝ c } =
Finset.card {c ∈ t.ps.E.keys | (t.b*c) ∈ t.ps.E ⬝ c } + 1 := by
  use newE2_of_old t
  have : {c ∈ t.ps.E.keys | (t.b*c) ∈ t.newE2 ⬝ c } =
         {c ∈ t.ps.E.keys | (t.b*c) ∈ t.ps.E ⬝ c } := by
    apply Finset.filter_congr
    intro x x_mem
    rw [newE2_spec]
    constructor
    · rintro (old | new)
      · assumption
      · exfalso
        apply freshGenerator_not_in_span (S := t.old)
        unfold c at new
        rw [← new.1]
        rw [Finmap.mem_keys] at x_mem
        apply Subgroup.subset_closure
        simp [dom_old (h := x_mem)]
    · tauto
  unfold newE2 at *
  simp only [Finmap.keys_union, Finset.filter_union] at *
  rw [this]
  simp only [Option.mem_def, Finmap.mem_lookup_disjoint_union t.newE2_disjoint,
    Finmap.keys_singleton, Finset.filter_singleton, Finmap.lookup_singleton_eq, or_true, ↓reduceIte]
  rw [Finset.card_union_eq_card_add_card.mpr]
  · simp
  · simp only [Finset.disjoint_singleton_right, Finset.mem_filter, not_and]
    intro c_mem
    exfalso
    apply c_not_old
    apply t.dom_old
    apply c_mem

end ExtensionTask
end extension2

theorem extension_or_nop  : ∀ (ps : PartialSolution) (b : A), ∃ ps', ps ≤ ps' ∧ ∃ c, c ∈ ps'.E ⬝ b := by
  intro ps b
  by_cases h : b ∈ ps.E
  case pos =>
    use ps, (by rfl)
    rw [TE_lookup_exists]
    assumption
  case neg =>
    let t : ExtensionTask := { ps := ps, b := b}
    have : Fact (t.b ∉ t.ps.E) := by use h
    use t.extension
    apply t.extension_spec

theorem extension2 (ps : PartialSolution) (b : A) (h : b ≠ 1) (n : Nat) :
∃ ps', ps ≤ ps' ∧ Finset.card {c ∈ ps'.E.keys | (b*c) ∈ ps'.E ⬝ c } ≥ n := by
  induction n with
  | zero => use ps ; simp
  | succ n ih =>
    obtain ⟨ps', le, ineq⟩ := ih
    let t : ExtensionTask := { ps := ps', b := b}
    have : Fact (t.b ≠ 1) := by use h
    use t.extension2
    have := t.extension2_spec
    constructor
    · rw [PartialSolution.le_iff]
      apply le_trans (α := TE) (b := ps'.E)
      · apply le
      · exact this.1
    · rw [t.extension2_E]
      have def_t_ps : t.ps = ps' := rfl
      have def_b : t.b = b := rfl
      rw [def_t_ps] at this
      rw [def_b] at this
      omega

def translation_invariant_1516 (f : A → A) : Prop := ∀ (x : A), (f ( f ( f x )* x⁻¹ * (f 1)⁻¹)) = x⁻¹ * (f 1)⁻¹

theorem completion (ps : PartialSolution) : ∃ (f : A → A), translation_invariant_1516 f ∧ (∀ x y, y ∈ ps.E ⬝ x → f x = y)
∧ ∀ b, (b ≠ 1) → Set.encard {c | b*c = f c } ≥ 3 := by
  have ⟨c, hc, h1, h2, h3⟩  := exists_greedy_chain (α := PartialSolution) (β := A ⊕ {b : A // b ≠ 1})
    (task := fun b ps => match b with
      | .inl b => ∃ c, c ∈ ps.E ⬝ b
      | .inr ⟨b, _⟩   => Finset.card {c ∈ ps.E.keys | (b*c) ∈ ps.E ⬝ c } ≥ 3)
    ( fun ps b => match b with
      | .inl b => extension_or_nop ps b
      | .inr ⟨b, h⟩   => extension2 ps b h 3) ps
  classical
  simp only [Sum.forall, Subtype.forall] at h3
  choose g hg1 f hf using h3.1
  refine ⟨f, fun x => ?_, fun x y => ?_, fun b h => ?_⟩
  · let S : Finset _ := {x, 1, f x, (f (f x) * x⁻¹ * (f 1)⁻¹)}
    have ⟨⟨e, he⟩, le⟩ := hc.directed.finset_le (hι := ⟨⟨_, h1⟩⟩)
      (S.image fun a => ⟨g a, hg1 a⟩)
    replace le a ha := Finset.forall_image.1 le a ha (hf a)
    simp only [Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq, S] at le
    obtain ⟨fx, f1, ffx, fffx⟩ := le
    rw [e.fId] at f1
    injection f1 with eq1
    rw [← eq1] at fffx
    rw [← eq1]
    simp only [inv_one, mul_one] at *
    apply_fun some
    rw [← (e.cond4 x (TE_lookup_mem' fx) (f x) fx (f (f x)) ffx), ← fffx]
    rw [inv_one, mul_one]
    exact Option.some_injective A
  · intro h
    specialize h2 (g x) (hg1 x) h
    specialize hf x
    rw [hf] at h2
    injection h2
  · obtain ⟨ps, ps_in_c, card_ps⟩ := h3.2 b h
    let S : Finset _ := ps.E.keys
    have : ∀ x ∈ S, b* x ∈ ps.E ⬝ x → b * x = f x := by
      intro x x_mem hyp
      obtain ⟨⟨ps', ps'_in_c⟩, hps'1, hps'2⟩ := hc.directed ⟨ps, ps_in_c⟩ ⟨g x, hg1 x⟩
      simp only at hps'1 hps'2
      apply Option.some_injective
      rw [← hps'1 hyp, ← hps'2 (hf x)]
    trans {c ∈ S | b * c ∈ ps.E ⬝ c}.toSet.encard
    · apply Set.encard_le_card
      simp only [Option.mem_def, Finset.coe_filter, Set.setOf_subset_setOf, and_imp]
      apply this
    · rw [Set.encard_coe_eq_coe_finsetCard]
      simp only [ge_iff_le, Nat.ofNat_le_cast]
      apply card_ps

def E0 : List (A × A) := [(1, 1), (x₁, x₂), (x₁⁻¹,x₃), (x₃ * x₁, x₄), (x₄ * x₂⁻¹, x₅), (x₆⁻¹, x₆^2), (x₆^3, x₆)]

def f0 (a : A) : A := (List.lookup a E0).getD 1

def initial : PartialSolution := by
  use List.toFinmap (E0.map Prod.toSigma) <;> decide

noncomputable def f := (completion initial).choose
end extension

theorem fromList_eval (a b: A) (h : (a,b) ∈ E0 := by decide) : f a = b := by
  apply (completion initial).choose_spec.2.1
  unfold initial
  simp only [Finmap.dlookup_list_toFinmap]
  rw [List.mem_dlookup_iff, List.mem_map]
  refine ⟨_, h, ?_⟩
  · simp
  · unfold List.NodupKeys
    decide

theorem f_translation_invariant_1516 : translation_invariant_1516 f := by
  unfold f
  apply (completion initial).choose_spec.1

theorem f_extends_initial : ∀ a b : A, b ∈ initial.E ⬝ a → f a = b := (completion initial).choose_spec.2.1

noncomputable scoped instance magA : Magma A := { op := fun x y => f (y*x⁻¹) * x  }

theorem magA_op_def (x y : A) : magA.op x y = f (y*x⁻¹) * x := rfl

theorem A_satisfies_Equation1516 : Equation1516 A := by
  unfold Equation1516
  intro x y
  repeat rw [magA_op_def]
  simp only [mul_inv_cancel_right, mul_inv_cancel, mul_inv_rev]
  have := f_translation_invariant_1516 (y*x⁻¹)
  apply_fun fun a => a * (f 1) * y at this
  simp only [mul_inv_rev, inv_inv, inv_mul_cancel_right] at this
  repeat rw [mul_assoc] at *
  exact this.symm

theorem A_idempotent (x : A) : x ◇ x = x := by
  rw [magA_op_def]
  simp [fromList_eval 1 1]

theorem base1 (a b : A) (ineq : a ≠ b) : {c | c ◇ a = b}.encard ≥ 3 := by
  have eq1 : {c | c ◇ a = b} =  {c | f (a*c⁻¹) *  c = b} := by
    ext
    simp [magA_op_def]
  let bij : A ≃ A := ⟨fun (c :A ) => a * c⁻¹, fun (c :A ) => c⁻¹ * a, fun _ => by simp, fun _ => by simp⟩
  have eq2 :  {c| (b * a⁻¹) *c = f c} ≃ {c| f (a*c⁻¹) *  c = b} := by
    simp only [Set.coe_setOf]
    trans
    · apply (Equiv.subtypeEquivOfSubtype bij).symm
    · apply Equiv.subtypeEquivRight
      intro x
      unfold bij
      simp only [Equiv.coe_fn_mk]
      group
      constructor
      · intro h ; rw [←h] ; group
      · intro h ; rw [←h] ; group
  rw [eq1, ← (Set.encard_congr eq2)]
  have := (completion initial).choose_spec.2.2 (b * a⁻¹)
  apply this
  apply_fun (fun x => x * a)
  simp [ineq.symm]

theorem base2 : ∀ a : A, ∃ b : A, b ≠ a ∧ a ◇ (b ◇ a) = b := by
  intro a
  use x₆ * a
  constructor
  · simp
  · repeat rw [magA_op_def]
    group
    rw [fromList_eval (x₆^(-1)) (x₆^2), fromList_eval (x₆^2 * x₆) (x₆^1)]
    simp

theorem A_op_surj_right (a b : A) : ∃ c : A, a ◇ c = b := by
  --doable, first check if there is already a proof in some lemma around here, I did a quick search and didn't find one. The proof of this is:
  /-By construction, $S$ is already defined and equal to the identity on $\Z$, and we have the 1516 equation
$$ L_{Sa} L_b L_b a = b$$
for $a,b \in \Z$, with the left multiplication operators $L_b$ currently only defined as maps from $\Z$ to $\Z$.  Among other things, this means that $L_a = L_{Sa}$ is surjective as a map from $\Z$ to $\Z$ for any $a \in \Z$.-/
  sorry

theorem A_op_eq_self_iff {a c : A} : c ◇ a = a ↔ c = a := by
  -- doable, just use A_satisfies_Equation1516
  sorry

section Refutation255

-- Follows https://teorth.github.io/equational_theories/blueprint/1516-chapter.html
-- We try to mimick the proof structure from Equation63 for the greedy construction parts. For now we are focusing on the second greedy construction (the one to prove axioms A and C) as it looks to be simpler than the other one. There are still big chunks of copy pasted and commented code. We will try to uncomment and adapt it as we go.
-- There are some sorries marked with `doable`, those can be tackled with relatively limited effort, without having to first understand all the greedy construction.
-- Current big task: build `next` for the second greedy construction


def G' := {(a, b, _) : A × A × ℕ | a ≠ b}

-- G is the disjoint union of A and G'
def G := A ⊕ G'

instance : Countable G' := inferInstance

instance : Countable G := inferInstanceAs (Countable (_ ⊕ _))

-- coercion from A to G
instance : Coe A G := ⟨.inl⟩

-- coercion from G' to G
instance : Coe G' G := ⟨.inr⟩

-- square function: on A it is the identity, on G' it is (a, b, n) ↦ a
def S : G → A
  | .inl a => a
  | .inr g => g.1.1

-- we take a special x₀ = (*, 0, 0) ∈ G', where * is the identity of A, i.e. the empty word
-- this is needed for Corollary 17.7, note that by doing this we are taking a sligthly different route from the proof of the corollary in the blueprint, in particular we make an explicit example of an element that does not verify eq 255
def x₀ : G := .inr ⟨⟨1, x 0, 0⟩, fun h ↦ one_ne_of 0 h⟩

namespace GreedyB
-- Greedy construction to extend the operation from A×A to A×G' in order to satisfy Axiom B

lemma exists_extension_aux (a : A) : ∃ c : A → A,
    c.Injective ∧ (∀ b, a ◇ ((c b) ◇ b) = c b) ∧ (∀ b, c b ≠ b):= by
  rcases base2 a with ⟨c₁, hc1a, hc1b⟩
  have c_aux (b : A) (h : a ≠ b) : ∃ c, c ◇ a = b ∧ c ≠ c₁ ∧ c ≠ b := by
    have enc := base1 a b h
    have noempty' : ({c | c ◇ a = b} \ {c₁, b}).Nonempty := by
      refine Set.encard_ne_zero.mp (ne_of_gt ?_)
      calc
        _ < (3 : ENat) - 2 := by norm_num
        _ ≤ _ := by
          gcongr
          refine Set.insert_eq _ _ ▸ (Set.encard_union_le _ _).trans ?_
          simp_rw [Set.encard_singleton]
          norm_num
        {c | c ◇ a = b}.encard - _ ≤ _ := Set.tsub_encard_le_encard_diff _ {c₁, b}
    rcases noempty' with ⟨c, hc1, hc2⟩
    use c
    simp_all
  let c := fun b : A ↦ if h : a = b then c₁ else (c_aux b h).choose
  use c
  refine ⟨?_, ?_, ?_⟩
  · unfold Function.Injective
    intro x y
    unfold c
    rcases ne_or_eq a x  with hx | ha <;> rcases ne_or_eq a y with hy | ha'
    · rw [dif_neg hx,dif_neg hy]
      intro hind
      have prop : (c_aux x hx).choose ◇ a = (c_aux y hy).choose ◇ a := by rw [hind]
      have h_aux : (c_aux x hx).choose ◇ a = x := by
        apply (c_aux x hx).choose_spec.1
      have h_aux2 : (c_aux y hy).choose ◇ a = y := by
        apply (c_aux y hy).choose_spec.1
      rw [h_aux,h_aux2] at prop
      exact prop
    · rw [dif_neg hx, dif_pos ha']
      intro hind
      exfalso
      have h_aux : (c_aux x hx).choose ≠  c₁ := by
        apply (c_aux x hx).choose_spec.2.1
      tauto
    · rw [dif_pos ha,dif_neg hy]
      intro hind
      exfalso
      have h_aux : (c_aux y hy).choose ≠  c₁ := by
        apply (c_aux y hy).choose_spec.2.1
      tauto
    · intro h
      rw [← ha, ← ha']
  · intro b
    rcases ne_or_eq a b with h1 | h2
    · unfold c
      rw [dif_neg h1]
      have h_aux : (c_aux b h1).choose ◇ a = b := by  -- R_a c_(y,b) = b
        apply (c_aux b h1).choose_spec.1   -- è la dim che (c_aux b h1).choose soddisfa la p: _ ◇ a = b
      have idem : a ◇ a = a := A_idempotent a
      nth_rw 1 [← idem]
      nth_rw 4 [← h_aux]
      symm
      apply A_satisfies_Equation1516
    · rw [← h2]
      unfold c
      rw [dif_pos rfl]
      exact hc1b
  · intro b
    rcases ne_or_eq a b with h1 | h2
    · simp_rw [c, dif_neg h1]
      exact (c_aux b h1).choose_spec.2.2
    · simp_rw [c, dif_pos h2, ← h2]
      exact hc1a

noncomputable abbrev c (a : A) : A → A := (exists_extension_aux a).choose

lemma c_injective (a : A) : (c a).Injective := (exists_extension_aux a).choose_spec.1

lemma c_spec (a b : A) : a ◇ ((c a b) ◇ b) = c a b := (exists_extension_aux a).choose_spec.2.1 b

lemma c_ne (a b : A) : c a b ≠ b := (exists_extension_aux a).choose_spec.2.2 b

--- here I try to mimic the structure of GreedyAC below

/- Problem with the proof in the blueprint: the greedy procedure seems to be adding not only the image of the special pair `(d,g)` that is not yet in the domain, but also an infinite number of other images of pairs in order to make the function infinitely surjective. How can we do this inside the greedy extension framework that we are trying to mimic? I have 2 ways in mind:
- we can drop the finiteness requirement in `OK`, this would allow us to actually add an infinite number of images even in intermediate steps. The issue is that I'm not sure wether the finiteness will prove to be crucial in some of the later proofs. To do this we will probably need to add a requirement to `OK` asking that some set be infinite. This is likely not doable, I think the informal proof actually uses the finiteness of the `PartialSolution` in a crucial way.
- we can try to add a new requirement to OK asking that the size of the counter images is bigger than some number, we need to use a number that we can easily show to grow indefinitely and I would rather not add a new variable altogether, because it may be hard to make it fit into the proof structure. One quantity that we have at our disposal could be something related to the size of the domain, but we need something that can grow indefinitely but does not grow too much when we add the new elements for the infinite surjectivity, otherwise we may end up trying to reach a target that moves as we advance towards it. Alternatively try to find a way to use the size of the domain of the previous iteration, instead of the current one (to do this I think I need to work directly inside Next, instead than inside the `PartialSolution`, not sure wether this is feasible).

I try to implement the second solution. Since I want to add, for every `b ∈ A` and every `x ∈ G'`, an infinite number relations of the form `E b y x`, there are 3 things I need to keep in check during the iteration to avoid adding an infinite number of elements in a single step:
1. the number of `b ∈ A` I am considering
2. the number of `x ∈ G'` I am considering
3. the number of `y` I am adding for each `b` and `x`

Solutions:
1. I already have a finite set `{(a, x, y) | E a x y}`, so in this case I can just take the projection of the set on the first element, i.e. `dom_projL := {a | ∃ x y, E a x y}`, this is finite and I can just ask that `b ∈ dom_projL`. Moreover this set does not change if I add new elements of the form `E b y x` with `b` aready in `dom_projL`.
2. The naive idea could be to take the set `dom_projR := {x : G' | ∃ a y, E a x y}` and ask for `x ∈ dom_projR`. However as we add new elements of the form `E b y x`, the set `dom_projR` will grow, so we need a way do limit the number of `x`s without relying on this set. Remember, however, that elements of `G'` are of the form `(a, c, n) ∈ A × A × ℕ`, so we can use the set `dom_projL` again to limit the number of `x`s in the following way: we can ask that `a, c ∈ dom_projL` and that `n < dom_projL.card`. For this reason it may be useful to define `dom_projL` as a finset, so that we can use `.card` inside `ℕ`, avoiding coercions.
Moreover, if we use a seed composed of only one element (I think it may be useful to use the seed `E * x₀ *`), it becomes easy to prove that it satisfies the requirement, because then `dom_projL = {*}` and there is no element of `G'` of the form `(*, *, n)`. (Maybe it will actually be enough to use an empty seed).
3. Since we are using `dom_projL` for the other quantities we may as well use it for this one too. In parcitular we can limit the addition of new elements `y` in the following way: we add new relations `E b y x` until the cardinality of the set `{y | E b y x}` is bigger than `dom_projL.card`. This guarantees us that the number of new elements is finite for each of the (finitely many thanks to 1. and 2.) pairs `(b,x)` we are considering. Moreover we can easily send the quantity `dom_projL.card` to infinity.
Moreover, note that in 1. and 2. we further restrict the situation by only considering `(b, x)` such that `L b x` is already defined, this will be done implicitely in the construction of `Next` by putting as a condition `Next b x w` or `Next b x c` and is needed because the elements `y` that we add for the infinite surjectivity depend on the value of `L b x`.
-/

noncomputable
def dom_projL {E : A → G → G → Prop} (hE : {(a, x, y) | E a x y}.Finite) : Finset A :=
  have := hE.fintype
  Finset.image (fun (a, _, _) ↦ a) {(a, x, y) | E a x y}.toFinset

lemma dom_projL_eq {E : A → G → G → Prop} (hE : {(a, x, y) | E a x y}.Finite) :
    dom_projL hE = {a | ∃ x y, E a x y} := by simp [dom_projL, Set.image]
--TODO: add a lemma saying that dom_projL of Next is equal to dom_projL of the previous iteration union {d}, if it is needed

@[mk_iff]
structure Relevant_aux (s : Finset A) (x : G') :
    Prop where
  h1 : x.1.1 ∈ s
  h2 : x.1.2.1 ∈ s
  h3 : x.1.2.2 ≤ s.card

def relevant_aux_set (s : Finset A) : Set G' :=
  {x | Relevant_aux s x}

lemma relevant_aux_set_eq (s : Finset A) :
    relevant_aux_set s = {x | x.1.1 ∈ s ∧ x.1.2.1 ∈ s ∧ x.1.2.2 ≤ s.card} := by
  ext
  simp [relevant_aux_set, relevant_aux_iff]

lemma relevant_aux_set_finite (s : Finset A) :
    (relevant_aux_set s).Finite := by
  -- have : fun x ↦ (x.1.1, x.1.2.1, x.1.2.2) |>.Injective
  -- should be doable, maybe try to pass to a set in A × A × ℕ with an injective function, then this should be the product of 3 finite sets
  sorry

@[mk_iff]
structure Relevant {E : A → G → G → Prop} (hE : {(a, x, y) | E a x y}.Finite) (b : A) (x : G') :
    Prop where
  hbx : ∃ z, E b x z
  hb : b ∈ dom_projL hE
  hx : Relevant_aux (dom_projL hE) x

-- @[mk_iff]
-- structure Relevant {E : A → G → G → Prop} (hE : {(a, x, y) | E a x y}.Finite) (b : A) (x : G') :
--     Prop where
--   hbx : ∃ z, E b x z
--   hb : b ∈ dom_projL hE
--   hx1 : x.1.1 ∈ dom_projL hE
--   hx2 : x.1.2.1 ∈ dom_projL hE
--   hxn : x.1.2.2 ≤ (dom_projL hE).card

structure OK (E : A → G → G → Prop) : Prop where
  finite : {(a, x, y) | E a x y}.Finite
  func {a x y y'} : E a x y → E a x y' → y = y'
  extend {a b : A} {x} : E a b x → x = .inl (a ◇ b)
  -- hx₀ : E 1 x₀ (.inl 1)
  hx₀ {x} : E 1 x₀ x → x = .inl 1
  -- aux1 {x y z w} : E x y z → E x z w → E (S y) w x --eq1516
  aux1 {x y z w k} : E x y z → E x z w → E (S y) w k → k = x --eq1516
  aux2 (b) (x : G') : -- technical condition to ensure the infinite surjectivity
    Relevant finite b x → (dom_projL finite).card ≤ {y : G' | E b y x}.ncard
  aux3 {a} {y : G'} {x} : S y = a → y.1.2.2 ≠ 0 → E a y x → x = .inr ⟨⟨y.1.1, y.1.2.1, 0⟩, y.2⟩
  aux4 {a} {y : G'} {x} : S y = a → y.1.2.2 = 0 → E a y x → x = .inl a
  aux5 {c} {y : G'} {x} : S y ≠ c → E c y x → x ≠ .inl c

abbrev PartialSolution := {E : A → G → G → Prop // OK E}

class Extension where
  E : A → G → G → Prop
  ok : OK E
  d : A
  g : G
  not_def {z} : ¬E d g z

namespace Extension

-- set_option diagnostics true
-- define the element that should be the image of `L_c y`
noncomputable def partL (c' : A) (y : G) : G := by
  rcases y with (a | ⟨⟨a, b, n⟩, habn⟩)
  · exact .inl (c' ◇ a)
  · by_cases ha : a = c'
    · by_cases hn : n = 0
      · exact .inl a
      · exact .inr ⟨(a, b, 0), habn⟩
    by_cases hb : ∃ b', c' = c a b'
    · exact .inl hb.choose
    -- TODO: change the blueprint, the proof is incorrect, in the blueprint in this case we use the surjectivity once to find b such that a ◇ b = c', I didn't find a way to make this work, so I used the surjectivity twice to also find b' such that c' ◇ b' = b, this way it seems to be working. Also remember to notify the zulip chat about this.
    · exact .inl (A_op_surj_right c' (A_op_surj_right a c').choose).choose


lemma partL_of_inl (d : A) (a : A) : partL d a = d ◇ a := rfl

lemma partL_of_inr_same_of_zero {a b : A} (hab : a ≠ b) : partL a (.inr ⟨(a, b, 0), hab⟩) = a := by
  simp only [partL]
  rfl

lemma partL_of_inr_same_of_zero' {a : A} {y : G'} (hSy : S y = a) (hn : y.1.2.2 = 0) :
    partL a y = a := by
  simp only [partL]
  rw [S] at hSy
  rw [dif_pos hSy, dif_pos hn, hSy]

lemma partL_of_inr_same_of_ne_zero {a b : A} (hab : a ≠ b) {n : ℕ} (hn : n ≠ 0) :
    partL a (.inr ⟨(a, b, n), hab⟩) = .inr ⟨(a, b, 0), hab⟩ := by
  simp only [partL, hn]
  rfl

lemma partL_of_inr_same_of_ne_zero' {a : A} {y : G'} (hSy : S y = a) (hn : y.1.2.2 ≠ 0) :
    partL a y = .inr ⟨(y.1.1, y.1.2.1, 0), y.2⟩ := by
  simp only [partL]
  rw [S] at hSy
  rw [dif_pos hSy, dif_neg hn]

lemma partL_of_inr_of_exists {c' a b b' : A} (n : ℕ) (had : a ≠ c') (hab : a ≠ b) (hdab' : c' = c a b') :
    partL c' (.inr ⟨(a, b, n), hab⟩) = b' := by
  simp only [partL, had, ↓reduceDIte]
  rw [dif_pos ⟨b', hdab'⟩]
  congr
  refine c_injective a ?_
  rw [← hdab']
  exact (⟨b', hdab'⟩ : ∃ b', c' = c a b').choose_spec.symm

lemma partL_of_inr_of_exists' {c' b' : A} {y : G'} (had : S y ≠ c') (hdab' : c' = c (S y) b') :
    partL c' y = b' := by
  rw [S] at had
  simp only [partL, had, ↓reduceDIte]
  rw [dif_pos ⟨b', hdab'⟩]
  congr
  refine c_injective (S y) ?_
  rw [← hdab']
  exact (⟨b', hdab'⟩ : ∃ b', c' = _).choose_spec.symm

lemma partL_of_inr_of_not_exists {c' a b : A} (n : ℕ) (had : a ≠ c') (hab : a ≠ b) (h : ¬∃ b', c' = c a b') :
    partL c' (.inr ⟨(a, b, n), hab⟩) =
      (A_op_surj_right c' (A_op_surj_right a c').choose).choose := by
  simp [partL, had, ↓reduceDIte, h]

lemma partL_of_inr_of_not_exists_spec {c' a b : A} (n : ℕ) (had : a ≠ c') (hab : a ≠ b) (h : ¬∃ b', c' = c a b') :
    ∃ b' b'' : A, partL c' (.inr ⟨(a, b, n), hab⟩) = b'' ∧
      a ◇ b' = c' ∧ c' ◇ b'' = b' := by
  rw [partL_of_inr_of_not_exists _ had hab h]
  refine ⟨(A_op_surj_right a c').choose, (A_op_surj_right c' _).choose, rfl,
    (A_op_surj_right _ _).choose_spec, (A_op_surj_right _ _).choose_spec⟩

lemma partL_of_inr_of_not_exists' {c' : A} {y : G'} (hSy : S y ≠ c') (h : ¬∃ b', c' = c (S y) b') :
    partL c' y = (A_op_surj_right c' (A_op_surj_right (S y) c').choose).choose := by
  simp only [partL]
  rw [S] at hSy h
  rw [dif_neg hSy, dif_neg h]

lemma partL_of_inr_of_not_exists'_spec {c' : A} {y : G'} (hSy : S y ≠ c') (h : ¬∃ b', c' = c (S y) b') :
    ∃ b b' : A, partL c' y = b' ∧ S y ◇ b = c' ∧ c' ◇ b' = b := by
  rw [partL_of_inr_of_not_exists' hSy h]
  exact ⟨(A_op_surj_right _ _).choose, (A_op_surj_right _ _).choose,
    rfl, (A_op_surj_right _ _).choose_spec, (A_op_surj_right _ _).choose_spec⟩

lemma partL_ne_c' {c' : A} {y : G'} (hSy : S y ≠ c') : partL c' y ≠ c' := by
  rw [S] at hSy
  by_cases hb' : ∃ b', c' = c (S y) b'
  · obtain ⟨b', hb'⟩ := hb'
    rw [partL_of_inr_of_exists' hSy hb', hb']
    refine Function.Injective.ne Sum.inl_injective (c_ne _ _).symm
  · obtain ⟨b, b', hb, hSb, hSb'⟩ := partL_of_inr_of_not_exists'_spec hSy hb'
    rw [hb]
    intro h
    apply Sum.inl_injective at h
    simp_all only
    rw [A_idempotent] at hSb'
    rw [← hSb', S] at hSb
    exact hSy (A_op_eq_self_iff.mp hSb)

lemma partL_ne_y {c' : A} {y : G} (h : .inl c' ≠ y) : partL c' y ≠ y := by
  rcases y with (a | ⟨⟨a, b, n⟩, habn⟩)
  · rw [partL_of_inl]
    contrapose! h
    rw [A_op_eq_self_iff.mp (Sum.inl_injective h)]
  · by_cases ha : a = c'
    · by_cases hn : n = 0
      · rw [hn, ← ha, partL_of_inr_same_of_zero habn]
        exact Sum.inl_ne_inr
      · rw [← ha, partL_of_inr_same_of_ne_zero habn hn]
        intro hh
        have := Sum.inr_injective hh
        simp_all
    by_cases hb : ∃ b', c' = c a b'
    · rw [partL_of_inr_of_exists n ha habn hb.choose_spec]
      exact Sum.inl_ne_inr
    · rw [partL_of_inr_of_not_exists _ ha habn hb]
      exact Sum.inl_ne_inr

--this lemma should be put into Mathlib, maybe in Set.ncard_le_encard somewhere after the definition of Set.ncard
lemma _root_.Set.ncard_le_encard {α : Type*} (s : Set α) : Set.ncard s ≤ Set.encard s :=
    ENat.coe_toNat_le_self _

--this lemma should be put into Mathlib, maybe in Mathlib.Order.WithBot after WithTop.coe_ne_top
lemma _root_.WithTop.eq_coe_of_ne_top {α : Type*} {a : WithTop α} (ha : a ≠ ⊤) :
    ∃ b : α, b = a := Option.ne_none_iff_exists.mp ha

--this lemma should be put into Mathlib, maybe in Mathlib.Order.WithBot after WithBot.coe_ne_bot
lemma _root_.WithBot.eq_coe_of_ne_bot {α : Type*} {a : WithBot α} (ha : a ≠ ⊥) :
    ∃ b : α, b = a := Option.ne_none_iff_exists.mp ha

--this lemma should be put into Mathlib, maybe in Mathlib.Data.ENat.Basic next to ENat.ne_top_iff_exists
lemma _root_.ENat.eq_top_iff_forall_ne (n : ENat) : n = ⊤ ↔ ∀ m : ℕ, ↑m ≠ n :=
  WithTop.forall_ne_iff_eq_top.symm

--this lemma should be put into Mathlib, maybe in Mathlib.Data.ENat.Basic next to ENat.ne_top_iff_exists
lemma _root_.ENat.eq_top_iff_forall_lt (n : ENat) : n = ⊤ ↔ ∀ m : ℕ, m < n := by
  rw [ENat.eq_top_iff_forall_ne]
  refine ⟨fun h m ↦ ?_, fun a m ↦ (a m).ne⟩
  contrapose! h
  exact WithTop.eq_coe_of_ne_top fun a ↦ ENat.coe_ne_top _ <| top_le_iff.mp (a ▸ h)

--this lemma should be put into Mathlib, maybe in Mathlib.Data.ENat.Basic next to ENat.ne_top_iff_exists
lemma _root_.ENat.eq_top_iff_forall_le (n : ENat) : n = ⊤ ↔ ∀ m : ℕ, m ≤ n := by
  rw [ENat.eq_top_iff_forall_lt]
  refine ⟨fun h m ↦ le_of_lt (h m), fun h m ↦ (h (m + 1)).trans_lt' ?_⟩
  exact (ENat.lt_add_one_iff (ENat.coe_ne_top m)).mpr (le_refl _)

variable [Extension]

--here I will put the definition and API for next


/- Problem I am encountering while defining Next: I need to define the extra cases on the basis of Relevant (in a pair (c', y) is relevant with respect to Next I should add something to Next), the problem is that I cannot even state this inside Next, because in order to even say that (c', y) are Relevant wrt Next I need the fact that Next.2.finite, which I can only establish after having defined it.
The soultion I will try to implement is this:
instead of defining Next in one go, I define an auxiliary structure Next_aux, where I just add the base and new cases, this will of course not be a PratialSolution, but I can still use its Relevant set since its domain will still be finite.
Then I will define Next as the extension of Next_aux, adding the extra cases. The control to add the extra cases will be based on Relevant wrt Next_aux and not Next, however it should be easy to prove that the relevant set does not change between Next_aux and Next, because the extra cases only add relations E a y x with a already in dom_projL, so dom_projL does not change
-/

@[mk_iff]
inductive Next_aux : A → G → G → Prop
  | base {a y x} : E a y x → Next_aux a y x
  | new : Next_aux d g (partL d g)

lemma next_aux_finite : {(a, x, y) | Next_aux a x y}.Finite := by
  simp [next_aux_iff, Set.setOf_or, ← Prod.mk.injEq, ok.finite]

lemma next_aux_func {a x y y'} : Next_aux a x y → Next_aux a x y' → y = y'
  | .base hb, .base hb' => ok.func hb hb'
  | .new , .new  => rfl
  | .base hb, .new | .new, .base hb => (not_def hb).elim

lemma next_aux_extend {a b : A} {x} : Next_aux a b x → x = .inl (a ◇ b) := by
  simp only [next_aux_iff]
  rintro (h | ⟨had, hbg, hx⟩)
  · exact ok.extend h
  · rw [hx, ← hbg, partL_of_inl, had]

lemma next_aux_x₀ {x} : Next_aux 1 x₀ x → x = .inl 1 := by
  simp only [next_aux_iff]
  rintro (h | ⟨hd, hg, hx⟩)
  · exact ok.hx₀ h
  · rw [hx, ← hd, ← hg, x₀, partL_of_inr_same_of_zero]

lemma next_aux_aux3 {a} {y : G'} {x} (hSy : S y = a) (hn : y.1.2.2 ≠ 0) (h : Next_aux a y x) :
    x = .inr ⟨⟨y.1.1, y.1.2.1, 0⟩, y.2⟩ := by
  rw [next_aux_iff] at h
  rcases h with (h | ⟨had, hbg, hx⟩)
  · exact ok.aux3 hSy hn h
  · rw [hx, ← hbg, ← had, partL_of_inr_same_of_ne_zero' hSy hn]

lemma next_aux_aux4 {a} {y : G'} {x} (hSy : S y = a) (hn : y.1.2.2 = 0) (h : Next_aux a y x) :
    x = .inl a := by
  rw [next_aux_iff] at h
  rcases h with (h | ⟨had, hbg, hx⟩)
  · exact ok.aux4 hSy hn h
  · rw [hx, ← hbg, ← had, partL_of_inr_same_of_zero' hSy hn]

lemma next_aux_aux5 {c} {y : G'} {x} (h : S y ≠ c) (h' : Next_aux c y x) : x ≠ .inl c := by
  rw [next_aux_iff] at h'
  rcases h' with (h' | ⟨had, hbg, hx⟩)
  · exact ok.aux5 h h'
  · rw [hx, ← had, ← hbg]
    exact partL_ne_c' h

lemma next_aux_aux1 {x y z w k} : Next_aux x y z → Next_aux x z w → Next_aux (S y) w k → k = x
  | .base hb => by
    rw [next_aux_iff]
    rintro (h | ⟨had, hbg, hx⟩)
    · rw [next_aux_iff]
      rintro (h' | ⟨had', hbg', hx'⟩)
      · exact ok.aux1 hb h h'
      ·
        --??? I need to figure this out, I'm not sure how though
        simp_all
        clear hbg' hx'

        sorry
        -- rcases hg : g with (a | ⟨⟨a, b, n⟩, habn⟩)
        -- ·
        --   exact .inl (c' ◇ a)
        -- ·
        --   by_cases ha : a = d
        --   · by_cases hn : n = 0
        --     ·
        --       simp_all
        --       rw [partL_of_inr_same_of_zero]
        --       exact .inl a
        --     · exact .inr ⟨(a, b, 0), habn⟩
        --   by_cases hb : ∃ b', c' = c a b'
        --   · exact .inl hb.choose
        --   · exact .inl (A_op_surj_right a c').choose
        -- rw [hbg'] at h

        -- sorry
      -- exact Next_aux.base <| ok.aux1 hb h _
    · rw [next_aux_iff]
      rintro (h' | ⟨had', hbg', hx'⟩)
      · simp_all
        clear had hbg hx
        -- divide the different cases of partL?
        rcases hg : g with (a | ⟨⟨a, b, n⟩, habn⟩)
        · rw [hg, partL_of_inl] at h'
          rw [ok.extend h']
          clear h'
          rcases hy : y with (a' | ⟨⟨a', b', n'⟩, habn'⟩)
          · rw [hy] at hb
            rw [ok.extend hb] at hg
            apply Sum.inl_injective at hg
            have := A_idempotent _ ▸ A_satisfies_Equation1516 d a'
            rw [← hg, S, ← this]
          · simp_all only [S]
            clear hg hy
            congr

            sorry

        ·
          sorry
      · by_cases h : .inl d = g
        · rw [hx', ← h, partL_of_inl, A_idempotent, had]
        · rw [hbg'] at hx
          refine (partL_ne_y h hx.symm).elim
  | .new => by
    rw [next_aux_iff]
    rintro (h | ⟨had, hbg, hx⟩)
    · rw [next_aux_iff]
      rintro (h' | ⟨had', hbg', hx'⟩)
      · rcases hg : g with (a | ⟨⟨a, b, n⟩, habn⟩)
        · rw [hg, partL_of_inl] at h
          rw [ok.extend h] at h'
          rw [ok.extend h', hg, S]
          nth_rw 3 [A_satisfies_Equation1516 d a]
          rw [A_idempotent]
        · simp_rw [hg, S] at h'
          by_cases had : a = d
          · by_cases hn : n = 0
            · rw [hg, ← had, hn, partL_of_inr_same_of_zero] at h
              rw [ok.extend h, A_idempotent] at h'
              rw [ok.extend h', A_idempotent, had]
            · rw [hg, ← had, partL_of_inr_same_of_ne_zero _ hn] at h
              rw [ok.aux4 (by rw [S]) rfl h] at h'
              rw [ok.extend h', A_idempotent, had]
          · by_cases hb : ∃ b', d = c a b'
            · obtain ⟨b', hb'⟩ := hb
              rw [hg, partL_of_inr_of_exists _ had habn hb'] at h
              rw [ok.extend h] at h'
              rw [ok.extend h', hb', c_spec]
            · have ⟨b', b'', hdg, hab', hdb''⟩ := partL_of_inr_of_not_exists_spec n had habn hb
              rw [hg, hdg] at h
              rw [ok.extend h] at h'
              simp_rw [ok.extend h', hdb'', hab']
      · rw [hx']
        rcases hg : g with (a | ⟨⟨a, b, n⟩, habn⟩)
        · rw [hg, S] at had'
          rw [partL_of_inl, had', A_idempotent]
        · by_cases hn : n = 0
          · rw [hn, partL_of_inr_same_of_zero' _ (by simp)]
            simp_all
          · simp_rw [hg, S] at had'
            rw [← had', hg, partL_of_inr_same_of_ne_zero _ hn] at h
            have := ok.aux4 (by rw [S]) rfl h
            rw [hbg', hg] at this
            exact (Sum.inr_ne_inl this).elim
    · by_cases h : .inl d = g
      · intro h'
        rw [hx, hbg, ← h, S] at h'
        rw [next_aux_extend h', A_idempotent]
      · exact (partL_ne_y h hbg).elim

def relevant_set : Set (A × G') := {(c', y) | Relevant next_aux_finite c' y}

def relevant_set' : Set (A × G) := (fun (a, x) ↦ (a, .inr x)) '' relevant_set

lemma relevant_set'_finite : relevant_set'.Finite := by
  have : Set.Finite {(c', (y : G)) | ∃ w, Next_aux c' y w} := by
    convert Set.Finite.image (fun (a, x, y) ↦ (a, x)) next_aux_finite
    ext p
    aesop
  refine Set.Finite.subset this fun _ h ↦ ?_
  simp only [relevant_set', relevant_set, Set.mem_image, Set.mem_setOf_eq, Prod.exists,
    Subtype.exists] at h
  have ⟨_, _, _, _, _, h_rel, h_eq⟩ := h
  exact Set.mem_of_eq_of_mem h_eq.symm h_rel.hbx

lemma relevant_set_finite : relevant_set.Finite := by
  refine relevant_set'_finite.of_finite_image fun _ _ _ _ h ↦ ?_
  simp only [Prod.mk.injEq] at h
  ext : 1
  · exact h.1
  · exact Sum.inr_injective h.2

section extra_set

/-
Construction of `extra_set`:
extra_set will be a function that takes `c'` and `y` such that `Relevant_aux c' y` and returns a finset of elements `z` to add the relations `E c' z y` for the last part of the construction.
This finset will need to have a fixed cadinality that will be needed in the proof of the infinite surjectivity.
There are 3 different cases to consider:
1. `L c' y = w ∈ G'`
2. `L c' y = b ∈ A` and `S y ≠ c'`
3. `L c' y = b ∈ A` and `S y = c'` and `y.1.2.2 = 0`
The case where `L c' y = b ∈ A` and `S y = c'` and `y.1.2.2 ≠ 0` is already considered in 1. and the case where `L c' y` is not defined is already ruled out by `Relevant_aux c' y`

So `extra_set` will be defined as an if then else expression and we need to define 3 different sets `extra_set1`, `extra_set2`, `extra_set3` for the 3 different cases.
To define each set I will be using the fact that some set `A` is infinite and to add some propeerties to the elements of the finset I will be subtracting from `A` some finite set `B`, excluding elements not meeting the properties.
Doing this is fine, and we could do it for each `(c', y)` separately, the problem is that we actually need to do it in sucha way that the resulting finsets are all disjoint.
Imposing the disjointness of `extra_seti` and `extra_setj` for `i ≠ j` is easy, it is sufficient to ask in the construction of `extra_set2` that the elements are not in any `extra_set1` and the same for `extra_set3`.
The problem arises when we need to impose the disjointness of some `extra_seti (c'₁, y₁)` and `extra_seti (c'₂, y₂)`, the difficulty is enhanced by the fact that the infinite and finite sets `A₁` `B₁` and `A₂` `B₂` are different for each pair of elements (otherwise we could have taken the number `N` of pairs `(c', y)` such that `Relevant_aux c' y`, then take a subset of `A \ B` of cardinality `N` times the required cardinality and just partition it in N different parts, one for each pair `(c', y)`).
The only way I am seeing to overcome this is by constructing the sets iteratively, in such a way that in the construction of each set I actively exclude the elements of the preceding sets.
Rather than implementing this for the special case of the extra sets, I will implement it in a more general and reuasble manner, saying that if we have a finite set of indexes `ι`, some infinite sets `A : ι → Set α`, some finite sets `B : ι → Set α` and some numbers `n : ι → ℕ`, then we can construct a collection of disjoint finsets `s : ι → Finset α` such that `s i ⊆ A i \ B i` and such that the cardinality of `s i` is `n i`.
For now I am leaving the proof of this lemma sorried, maybe there is already some similar result in mathlib. However if it is not the case the I think that the key will be to be able to give an order to ι and then construct the sets iteratively as suggested above (maybe via an induction on the cardinality of `ι`?) at each step one could use a lemma like `Finset.exists_card_eq` applied to `A i` and `B i ∪ ⋃ j < i, s j`.
-/



-- remember, during the construction of the extra sets, to also exclude the elements in relevant_aux_set (dom_projL ok.finite)

-- lemma exists_multiple_sets {α : Type*}

-- lemma exists_extra_set1 :
--     -- ∃ s : {(c', y) | Relevant c' y ∧ ∃ w : G', }

--     ∃ s : Finset G', s.card = (dom_projL ok.finite).card ∧
--       ∀ z ∈ s, z.1.1 = c w1 c' ∧ z.1.2.1 = c' ∧ .inr z ≠ g ∧ ∀ x, ¬ E c' z x := by
--   have : Set.Infinite <| ({((⟨⟨c w1 c', c', n'⟩, c_ne w1 c'⟩ : G') : G) | n'} \
--       {y : G| ∃ w, E c' y w}) \ {g} := by
--     refine (Set.Infinite.diff ?_ ?_).diff (Set.finite_singleton g)
--     ·
--       --doable, this set is the image of ℕ through the function n ↦ ⟨⟨c w1 c', c', n⟩, c_ne w1 c'⟩, which is injective
--       sorry
--     ·
--       --doable, the set is the image of the set {(c', y, x) | E c' y x} ⊆ {(a, x, y) | E a x y}, which is finite
--       sorry
--   -- doable, use Finset.exists_card_eq
--   sorry

lemma exists_extra_set1 (c' w1 : A) :
    ∃ s : Finset G', s.card = (dom_projL ok.finite).card ∧
      ∀ z ∈ s, z.1.1 = c w1 c' ∧ z.1.2.1 = c' ∧ .inr z ≠ g ∧ ∀ x, ¬ E c' z x := by
  have : Set.Infinite <| ({((⟨⟨c w1 c', c', n'⟩, c_ne w1 c'⟩ : G') : G) | n'} \
      {y : G| ∃ w, E c' y w}) \ {g} := by
    refine (Set.Infinite.diff ?_ ?_).diff (Set.finite_singleton g)
    ·
      --doable, this set is the image of ℕ through the function n ↦ ⟨⟨c w1 c', c', n⟩, c_ne w1 c'⟩, which is injective
      sorry
    ·
      --doable, the set is the image of the set {(c', y, x) | E c' y x} ⊆ {(a, x, y) | E a x y}, which is finite
      sorry
  -- doable, use Finset.exists_card_eq
  sorry

noncomputable def extra_set1 (c' w1 : A) : Finset G' := (exists_extra_set1 c' w1).choose

lemma extra_set1_card (c' w1 : A) : (extra_set1 c' w1).card = (dom_projL ok.finite).card :=
    (exists_extra_set1 c' w1).choose_spec.1

lemma extra_set1_eq1 (c' w1 : A) {z : G'} (hz : z ∈ extra_set1 c' w1) : z.1.1 = c w1 c' :=
  (exists_extra_set1 c' w1).choose_spec.2 z hz |>.1

lemma extra_set1_eq2 (c' w1 : A) {z : G'} (hz : z ∈ extra_set1 c' w1) : z.1.2.1 = c' :=
  (exists_extra_set1 c' w1).choose_spec.2 z hz |>.2.1

lemma extra_set1_not_g (c' w1 : A) {z : G'} (hz : z ∈ extra_set1 c' w1) : .inr z ≠ g :=
  (exists_extra_set1 c' w1).choose_spec.2 z hz |>.2.2.1

lemma extra_set1_not_E (c' w1 : A) {z : G'} (hz : z ∈ extra_set1 c' w1) : ∀ x, ¬ E c' z x :=
  (exists_extra_set1 c' w1).choose_spec.2 z hz |>.2.2.2

-- NB: during the iteration it will not be guaranteed that L a' b is already defined, however this should not be an issue, in fact we only need to prove the 1516 if all its members are well defined and in this case L (S z) <| L c' <| L c' z = L a' <| L c' y = L a' b, if it it not well defined we are ok
lemma exists_extra_set2 (c' b : A) :
  ∃ s : Finset G', s.card = (dom_projL ok.finite).card ∧
    -- (∀ c'₀ w1, Relevant ok.finite c' w1 → Disjoint s (extra_set1 c'₀ w1)) ∧
    ∃ (a' : A), a' ◇ b = c' ∧ a' ≠ c' ∧
      ∀ z ∈ s, z.1.1 = a' ∧ z.1.2.1 = c' ∧ .inr z ≠ g ∧ ∀ x, ¬ E c' z x := by
  -- say that a' exists
  -- have : Set.Infinite <| ({((⟨⟨a', c', n'⟩, c_ne a' c'⟩ : G') : G
  sorry

noncomputable def extra_set2 (c' b : A) : Finset G' := (exists_extra_set2 c' b).choose

lemma extra_set2_card (c' b : A) : (extra_set2 c' b).card = (dom_projL ok.finite).card :=
  (exists_extra_set2 c' b).choose_spec.1

-- lemma extra_set2_disjoint (c' b : A) (c'₀ w1 : A) : Disjoint (extra_set2 c' b) (extra_set1 c'₀ w1) :=
  -- (exists_extra_set2 c' b).choose_spec.2 c'₀ w1


noncomputable def extra_set3 : Finset G' := sorry

-- maybe it's useless
-- noncomputable def relevant_finset : Finset (A × G') :=
--   letI := Set.Finite.fintype relevant_set_finite
--   relevant_set.toFinset

--
-- this set will hold all the different extra_sets generated by the greedy construction at a specific step, I will need to prove that it is finite, then it will be useful to prove finiteness later
-- def extra_set_tot : Set G' := ⋃ c'y ∈ relevant_set, extra_set1 c'y.1 c'y.2.1.1
-- def extra_set_tot : Set G := ⋃ c'y ∈ relevant_set, (Finset.image Sum.inr (extra_set c'y.1 c'y.2.1.1)).toSet
-- -- def extra_set_tot : Set G' := ⋃ c', ⋃ w, ⋃ (_ : Relevant ok.finite c' w), extra_set1 c' w.1.1

-- -- for now I am not golfing the proof since this will change when I add more sets to extra_set_tot
-- lemma extra_set_tot_finite : extra_set_tot.Finite := by
--   simp_rw [extra_set_tot]
--   refine Set.Finite.biUnion relevant_set_finite fun (c', y) h ↦ ?_
--   exact Finset.finite_toSet _

lemma exists_disjoint_sets {α ι : Type*} [Finite ι] (n : ι → ℕ)
    (A : ι → Set α) (hA : ∀ i, (A i).Infinite)
    (B : ι → Set α) (hB : ∀ i, (B i).Finite) :
    ∃ s : ι → Finset α, (∀ i, (s i).toSet ⊆ A i \ B i) ∧
      (∀ i, (s i).card = n i) ∧ ∀ i j, i ≠ j → Disjoint (s i) (s j) := by
  sorry


-- lemma exists_extra_set

def extra_set (c' : A) (y : G') : Finset G' := sorry

lemma extra_set_not_next_aux {c' : A} {y z : G'} (hz : z ∈ extra_set c' y) : ∀ x, ¬ Next_aux c' z x := sorry
  -- (exists_extra_set c' y).choose_spec.2 z hz |>.2.2.2

lemma extra_set_not_x₀ {c' : A} {y z : G'} (hz : z ∈ extra_set c' y) : .inr z ≠ x₀ := sorry
  -- (exists_extra_set c' y).choose_spec.2 z hz |>.2.2.1

lemma extra_set_disj {c'₁ c'₂ : A} {y y' : G'} (h : c'₁ ≠ c'₂ ∨ y ≠ y') : Disjoint (extra_set c'₁ y) (extra_set c'₂ y') := sorry
  -- (exists_extra_set c' y).choose_spec.2 z hz |>.2.2.2

-- def extra_set_tot : Set G := ⋃ c'y ∈ relevant_set, (Finset.image Sum.inr (extra_set c'y.1 c'y.2)).toSet
def extra_set_tot : Set G := ⋃ c'y ∈ relevant_set, (Sum.inr '' (extra_set c'y.1 c'y.2))
-- def extra_set_tot : Set G' := ⋃ c', ⋃ w, ⋃ (_ : Relevant ok.finite c' w), extra_set1 c' w.1.1

-- for now I am not golfing the proof since this will change when I add more sets to extra_set_tot
lemma extra_set_tot_finite : extra_set_tot.Finite := by
  simp_rw [extra_set_tot]
  refine Set.Finite.biUnion relevant_set_finite fun (c', y) h ↦ ?_
  exact (Finset.finite_toSet _).image _

end extra_set

@[mk_iff]
inductive Next : A → G → G → Prop
  -- | base {a y x} : E a y x → Next_aux a y x
  -- | new : Next_aux d g (partL d g)
  | aux {a y x} : Next_aux a y x → Next a y x

  --this extra is how it should look at the end
  | extra {c' y z} : Relevant next_aux_finite c' y → z ∈ extra_set c' y → Next c' z y

  -- | extra1 {c' y} {w z : G'} : -- case1
  --   -- we need to define the extra_set1 which should be a set of cardinality (dom_projL finite).card of elements z = (c w c', c', n') such that L c' z is not yet defined (i.e. is not defined neither in base or in new, we can directly ask that z ≠ g and ¬ E c' z p for any p), we can do something like a lemma stating that {(c w c', c', n') | n'} is infinite and we just subtract from it {y | ∃ w, E c' y w} ∪ {g} which is finite, so there is a subset of cardinality (dom_projL finite).card
  --     Relevant next_aux_finite c' y → Next c' y w → z ∈ extra_set1 c' w.1.1 → Next c' z y
  --     -- Relevant ok.finite c' y' → Next c' y' w' → z ∈ extra_set1 c' w'.1.1 → Next c' z y'
  --   -- sorry
  -- | extra2 {c' y} {b : A} {z : G'} : --case2
  --     Relevant next_aux_finite c' y → Next c' y b → S y ≠ c' → z ∈ extra_set2 c' b → Next c' z y
  -- | extra3 {c' y} {b : A} {z : G'} : --case4, we skipped case 3 because we are asking that L c' y is already defined
  --     -- not finished! this is only a temporary test
  --     Relevant next_aux_finite c' y → Next c' y b → S y = c' → y.1.2.2 = 0 → z ∈ extra_set3 → Next c' z y

lemma Next_base {a y x} : E a y x → Next a y x := fun h ↦ Next.aux (Next_aux.base h)

lemma Next_new : Next d g (partL d g) := Next.aux Next_aux.new

lemma finite_relevant_extra_set_tot :
    {(c', z, y) | (c', y) ∈ relevant_set' ∧ z ∈ extra_set_tot}.Finite := by
  -- doable, it is the cartesian product of two finite sets
  sorry

def next_finite : {(a, x, y) | Next a x y}.Finite := by
  simp_rw (config := {singlePass := true}) [next_iff]
  simp only [Set.setOf_or, Set.finite_union]
  refine ⟨next_aux_finite, ?_⟩
  · refine Set.Finite.subset finite_relevant_extra_set_tot ?_
    intro ⟨c', z, y⟩ ⟨y', z', h_rel, h_extra_set, hy', hz'⟩
    simp only [Set.mem_setOf_eq] at *
    refine ⟨?_, ?_⟩
    · simp only [relevant_set', relevant_set, Set.mem_image, Set.mem_setOf_eq, Prod.mk.injEq]
      use (c', y')
      simp_all
    · simp only [extra_set_tot, Set.mem_iUnion, Set.mem_image, Finset.mem_coe,
         exists_prop, relevant_set]
      use (c', y')
      simp only [Set.mem_setOf_eq, true_and, h_rel]
      exact ⟨z', h_extra_set, hy'.symm⟩

lemma dom_projL_next_aux : dom_projL next_finite = dom_projL next_aux_finite := by
  -- doable, one direction should be imediate, for the other if there is a ∈ dom_projL next_finite then Next a y x for some x y, then either Next_aux a y x or the extra case, but in the extra case it must hold Relevant next_aux_finite a y, so a ∈ dom_projL next_aux_finite
  sorry


lemma relevant_next_iff_next_aux {c' y} :
    Relevant next_finite c' y ↔ Relevant next_aux_finite c' y := by
  -- dom_projL_next_aux to eliminate the dom_projL conditions in both directions, for the E c' y w condition one direction is immediate, for the other if there is a Next c' y w then either Next_aux c' y w (and so we are done) or the extra case, in particular in the extra case we have that y ∈ extra_set, so ¬ Relevant_aux (dom_projL ) y, which is absurd because we have Relevant c' y
  sorry

def next_func {a y x x'} : Next a y x → Next a y x' → x = x'
  | .aux hx, .aux hx' => next_aux_func hx hx'
  | .aux ha, .extra h_rel h_ex => (extra_set_not_next_aux h_ex x ha).elim
  | .extra h_rel h_ex, .aux ha => (extra_set_not_next_aux h_ex x' ha).elim
  | .extra h_rel h_ex, .extra h_rel' h_ex' => by
    rename_i z y z' y'
    by_contra h_ne
    have : y ≠ y' := fun h ↦ (h ▸ h_ne) rfl
    have : Disjoint (extra_set a y).toSet (extra_set a y').toSet :=
      Finset.disjoint_coe.mpr <| extra_set_disj (Or.inr this)
    exact Set.not_disjoint_iff.mpr ⟨z', h_ex, h_ex'⟩ <| this

def next_extend {a b : A} {x} : Next a b x → x = .inl (a ◇ b) := by
  simp only [next_iff, reduceCtorEq, false_and, and_false, exists_false, or_false]
  exact fun h ↦ next_aux_extend h

def next_hx₀ {x} : Next 1 x₀ x → x = .inl 1
  | .aux ha => next_aux_x₀ ha
  | .extra _ h_ex => (extra_set_not_x₀ h_ex rfl).elim

def next_aux1 {x y z w k} : Next x y z → Next x z w → Next (S y) w k → k = x := by
  sorry

def next_aux2 (b) (x : G') :
    Relevant next_finite b x → (dom_projL next_finite).card ≤ {y : G' | Next b y x}.ncard := by
  sorry

def next_aux3 {a} {y : G'} {x} : S y = a → y.1.2.2 ≠ 0 → Next a y x → x = .inr ⟨⟨y.1.1, y.1.2.1, 0⟩, y.2⟩ := by
  sorry

def next_aux4 {a} {y : G'} {x} : S y = a → y.1.2.2 = 0 → Next a y x → x = .inl a := by
  sorry

def next_aux5 {c} {y : G'} {x} : S y ≠ c → Next c y x → x ≠ .inl c := by
  sorry

def next : PartialSolution :=
  ⟨Next, next_finite, next_func, next_extend, next_hx₀, next_aux1, next_aux2,

  next_aux3, next_aux4, next_aux5⟩

end Extension

--maybe in  this part of the prof we can actually avoid using the greedy construction, at first glance it seems to me that we actually explicitely define the function at each
set_option pp.proofs true
theorem exists_extension (seed : PartialSolution) :
    ∃ L : A → G → G,
      (∀ a b : A, L a b = a ◇ b) ∧ -- Lb extends a : A ↦ b ◇ a
      (∀ b : A, ∀ x : G', (L (S x) <| L b <| L b x) = b) ∧ -- Axiom B
      (L 1 x₀ = .inl 1) ∧
      (∀ b : A, ∀ x : G', {y : G' | L b y = x}.Infinite) -- infinite surjectivity
    -- (∀ b : A, ∀ x : G', L b x ≠ x)
    := by
  classical
  have ⟨c, hc, h1, h2, h3⟩ := exists_greedy_chain (a := seed)
    (task := fun (a, x) ↦ {e | ∃ y, e.1 a x y})
    fun ⟨E, ok⟩ ((d, g) : A × G) ↦ by
      if h : ∃ z, E d g z then exact ⟨_, le_rfl, h⟩
      else
        let E1 : Extension := { E, ok, d, g, not_def := fun h' ↦ h ⟨_, h'⟩ }
        exact ⟨E1.next, fun _ _ _ ↦ (.base ·), _, .new⟩
  choose e he L hL using h3
  have L_of_e {a : A} {y x : G} {e₀ : PartialSolution} (he₀ : e₀   ∈ c)
      (h : e₀.val a y x) : L (a, y) = x := by
    rcases hc.total he₀ (he (a, y)) with (h_le | h_le)
    · exact (e (a, y)).2.func (hL (a, y)) (h_le _ _ _ h)
    · exact e₀.2.func (h_le _ _ _ (hL (a, y))) h

  refine ⟨L.curry,
    fun a b ↦ (e (a, b)).2.extend (hL (a, b)),
    fun a x ↦ ?_,
    (e (1, x₀)).2.hx₀ (hL (1, x₀)),
    fun b ⟨x, hx⟩ ↦ ?_⟩
  · let T : Finset (A × G) := {
      (a, (x : G)),
      (a, (L (a, x))),
      (S x, L (a, (L (a, x))))}
    have ⟨⟨e, he⟩, le⟩ := hc.directed.finset_le (hι := ⟨⟨_, h1⟩⟩)
      (T.image fun p ↦ ⟨e p, he p⟩)
    have hT := fun p hp ↦ Finset.forall_image.mp le p hp _ _ _ (hL p)
    simp only [Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq, T] at hT
    have ⟨e_a_x, e_a_L, e_Sx_L⟩ := hT
    exact L_of_e he <| e.2.aux1 e_a_x e_a_L
  · rw [← Set.encard_eq_top_iff, ENat.eq_top_iff_forall_le]
    intro n
    set m := max n x.2.2
    -- we have to find a PartialSolution e in the chain c such that n, x.2.2 ≤ {a | ∃ x y, ↑e a x y}.ncard, we do it by setting T' : Finset A that contains at least max(n, x.2.2) arbitrary elements of A, then we define T as {(a, x₀) | a ∈ T' ∪ {b, x.1, x.2.1}} and proceed as in the previous subproofs
    have ⟨(T' : Finset A), hT'⟩ := Finset.exists_card_eq m
    let T := Finset.image (fun a ↦ (a, x₀)) (T' ∪ {b, x.1, x.2.1}) ∪ {(b, .inr (⟨x, hx⟩ : G'))}
    -- let T := Finset.image (fun a ↦ (a, x₀)) (T' ∪ {b, x.1, x.2.1})
    have ⟨⟨e, he⟩, le⟩ := hc.directed.finset_le (hι := ⟨⟨_, h1⟩⟩)
      (T.image fun p ↦ ⟨e p, he p⟩)
    have hT := fun p hp ↦ Finset.forall_image.mp le p hp _ _ _ (hL p)

    simp only [Finset.union_comm T', Finset.insert_union, ← Finset.insert_eq, Finset.image_insert,
      Finset.mem_insert, Finset.mem_union, Finset.mem_image, Finset.mem_singleton, or_imp,
      forall_exists_index, and_imp, forall_and, forall_eq, forall_apply_eq_imp_iff₂, T] at hT

    have ⟨e_b, e_x1, e_x2, e_T', e_bx⟩ := hT

    have h := e.2.aux2 b ⟨x, hx⟩
    simp_rw [relevant_iff, ← Finset.mem_coe, ← Set.ncard_coe_Finset, dom_projL_eq e.2.finite] at h
    have h_finite : {a | ∃ x y, e.1 a x y}.Finite := by
      convert Set.Finite.image (fun (a, _, _) ↦ a) e.2.finite
      ext a
      simp
    have h_le : m ≤ {a | ∃ x y, e.1 a x y}.ncard := by
      rw [← hT', ← Set.ncard_coe_Finset T']
      refine Set.ncard_le_ncard ?_ h_finite
      exact fun t ht ↦ ⟨_, _, e_T' _ ht⟩

    specialize h ⟨⟨_, e_bx⟩, ⟨_, _, e_b⟩, ⟨_, _, e_x1⟩, ⟨_, _, e_x2⟩, (le_max_right _ _).trans h_le⟩

    calc
      _ ≤ Nat.cast {a | ∃ x y, e.1 a x y}.ncard :=
        Nat.cast_le.mpr <| (le_max_left _ _).trans <| h_le
      _ ≤ _ := (Nat.cast_le.mpr h).trans (Set.ncard_le_encard _)
      _ ≤ _ := Set.encard_le_card fun y hy ↦ L_of_e he hy

-- the empty seed, see if this actually works, otherwise maybe we can use the seed `E * x₀ *`
def seed : A → G → G → Prop := fun _ _ _ ↦ false

theorem seed_ok : OK seed where
  finite := by simp [seed]
  extend := by simp [seed]
  hx₀ := by simp [seed]
  func h1 h2 := by simp_all [seed]
  aux1 := by simp [seed]
  aux2 := by simp [seed, dom_projL]

noncomputable def L : A → G → G := (exists_extension ⟨seed, seed_ok⟩).choose

theorem L_extends (a b : A) : L a b = a ◇ b := (exists_extension ⟨seed, seed_ok⟩).choose_spec.1 a b

theorem L_1516 (b : A) (x : G') : (L (S x) <| L b <| L b x) = b :=
  (exists_extension ⟨seed, seed_ok⟩).choose_spec.2.1 b x

theorem L_x₀ : L 1 x₀ = .inl 1 := (exists_extension ⟨seed, seed_ok⟩).choose_spec.2.2.1

theorem L_surjective (b : A) (x : G') : {y : G' | L b y = x}.Infinite :=
  (exists_extension ⟨seed, seed_ok⟩).choose_spec.2.2.2 b x

-- theorem L_ne (b : A) (x : G') : L b x ≠ x := exists_extension.choose_spec.2.2 b x

theorem L_self (a : A) : L a a = S a := by
  rw [L_extends a a, A_idempotent]
  rfl  -- by def of S

end GreedyB

namespace GreedyAC
open GreedyB

variable (x : G')

structure OK (E : Rel G G) : Prop where
  finite : Set.Finite {(x, y) : G × G | E x y}
  func {x y y'} : E x y → E x y' → y = y'
  inj {x x' y} : E x y → E x' y → x = x'
  aux1 : E x (S x) --Eq4 in the dim
  aux2 {y z w} : E y z → E z w → L (S y) w = x --Eq5 in the dim, we are renaming L x y = z, L x z = w, so we are saying that (L (S y) <| L x <| L x y) = x, which is equation 1516

abbrev PartialSolution := {E : Rel G G // OK x E}

class Extension where
  E : Rel G G
  ok : OK x E
  d : G
  not_def {y} : ¬E d y


namespace Extension

variable [Extension x]

def partial_domain' : Set G := (E x).dom

#check Set.Infinite.diff -- this may be useful to prove the following lemmas
instance : Fintype (partial_domain' x) := by
  -- doable
  -- this set should be some kind of slice of {(x, y) : G × G | E x y}, which we already know to be finite (OK.finite)
  -- find the right definition of slice, then there will probably already be an instance proving the finiteness of a slice given the finiteness of the initial set
  sorry

def partial_domain : Finset G := (partial_domain' x).toFinset


def partial_range' : Set G := (E x).codom

instance : Fintype (partial_range' x) := by
  -- doable, same as above for the domain
  sorry

def partial_range : Finset G := (partial_range' x).toFinset

-- NOTE: I added the requirement that w ≠ d for technical reasons, consider adding it to the blueprint
lemma exists_not_in_domain_range : ∃ w, w ∉ partial_domain x ∧ w ∉ partial_range x ∧ w ≠ d x := by
  -- doable
  -- we know that the domain and the image are finite while G is infinite, so we can just take an element that is not in either
  sorry

lemma exists_not_in_domain_range' (z : G) : ∃ w, L (S z) w = x ∧ w ∉ partial_domain x ∧ w ∉ partial_range x ∧ w ≠ d x := by
  -- doable
  -- use the infinite surjectivity of L, then proceed like in the previous lemma
  sorry

-- Given an extension, which is a partial solution with an undefined element of the domain called `d`, we define a new element `w` that represents the image of `d` (`Lₓ d`).
noncomputable def w : G := by
  classical
  exact if h : (∃ (z : G), E x z (d x)) then (exists_not_in_domain_range' x h.choose).choose
    else (exists_not_in_domain_range x).choose

-- set_option pp.proofs true
lemma w_not_in_domain : w x ∉ partial_domain x := by
  by_cases h : (∃ (z : G), E x z (d x))
  · simp only [w, h]
    exact (exists_not_in_domain_range' x _).choose_spec.2.1
  · simp only [w, h]
    exact (exists_not_in_domain_range x).choose_spec.1

lemma w_not_in_range : w x ∉ partial_range x := by
  by_cases h : (∃ (z : G), E x z (d x))
  · simp only [w, h]
    exact (w.proof_1 x _).choose_spec.2.2.1
  · simp only [w, h]
    exact (exists_not_in_domain_range x).choose_spec.2.1

lemma w_ne_d : w x ≠ d x := by
  by_cases h : (∃ (z : G), E x z (d x))
  · simp only [w, h]
    exact (exists_not_in_domain_range' x _).choose_spec.2.2.2
  · simp only [w, h]
    exact (exists_not_in_domain_range x).choose_spec.2.2

lemma w_equation (h : (∃ (z : G), E x z (d x))) : L (S h.choose) (w x) = x := by
  simp only [w, h]
  exact (exists_not_in_domain_range' x _).choose_spec.1

lemma z_unique {z z' : G} (hz : E x z (d x)) (hz' : E x z' (d x)) : z = z' := ok.inj hz hz'

lemma w_equation' {z : G} (hz : E x z (d x)) : L (S z) (w x) = x := by
  have hh : ∃ z, E x z (d x) := ⟨z, hz⟩
  convert w_equation x hh
  exact z_unique x hz hh.choose_spec

@[mk_iff]
inductive Next : G → G → Prop
  | base {a b} : E x a b → Next a b
  | new : Next (d x) (w x)

theorem next_d_is_w {y} : Next x (d x) y → y = w x
  | .base hb => False.elim <| not_def hb
  | .new => rfl

theorem prev_w_is_d {y} : Next x y (w x) → y = d x
  | .base h => by
    have := w_not_in_range x
    simp only [partial_range, partial_range', Rel.codom, Set.mem_toFinset, Set.mem_setOf_eq,
      not_exists] at this
    exact (this y h).elim
  | .new => rfl

def next_finite : Set.Finite {(z, y) : G × G | Next x z y} := by
  simp [next_iff, Set.setOf_or, ← Prod.mk.injEq, ok.finite]

def next_func {z y y'} : Next x z y → Next x z y' → y = y'
  | .base hb, .base hb' => ok.func hb hb'
  | .new , .new  => rfl
  | .base hb, .new | .new, .base hb => (not_def hb).elim

def next_inj {z z' y} : Next x z y → Next x z' y → z = z'
  | .base hb, .base hb' => ok.inj hb hb'
  | .new, .new => rfl
  | .base hz, .new => prev_w_is_d _ (.base hz)
  | .new, .base hz' => (prev_w_is_d _ (.base hz')).symm

def next_aux1 : Next x x (S x) := Next.base ok.aux1

def next_aux2 {y z t} : Next x y z → Next x z t → L (S y) t = x := by
  intro next1 next2
  rcases next1 with ⟨hb⟩
  · rcases next2 with ⟨hb'⟩ | ⟨⟩
    · exact ok.aux2 hb hb'
    · exact w_equation' x hb
  · rw [next_iff] at next2
    rcases next2 with h | h
    · have := w_not_in_domain x
      simp only [partial_domain, partial_domain', Rel.dom, Set.mem_toFinset, Set.mem_setOf_eq,
        not_exists] at this
      exact (this t h).elim
    · exact (w_ne_d x h.1).elim

def next : PartialSolution x :=
  ⟨Next x, next_finite x, next_func x, next_inj x, next_aux1 x, next_aux2 x⟩

end Extension

theorem exists_extension (x : G') (seed : PartialSolution x) :
    ∃ Lₓ : G → G,
      Lₓ x = S x ∧ -- Axiom A
      (∀ y : G, (L (S y) <| Lₓ <| Lₓ y) = x) -- Axiom C
    := by
  classical
  have ⟨c, hc, h1, h2, h3⟩ := exists_greedy_chain (a := seed)
    (task := fun x' ↦ {e | ∃ y, e.1 x' y})
    fun ⟨E, ok⟩ d ↦ by
      if h : ∃ y, E d y then exact ⟨_, le_rfl, h⟩ else
        let E1 : Extension x := { E, ok, d, not_def := fun h' ↦ h ⟨_, h'⟩ }
        exact ⟨E1.next, fun _ _ ↦ (.base ·), _, .new⟩
  choose e he Lₓ hLₓ using h3

  refine ⟨Lₓ, (e x).2.func (e x).2.aux1 (hLₓ x) |>.symm, fun y ↦ ?_⟩
  /- We have a chain of partial solutions (i.e. partial functions Lₓ : G → G) that saturates the space,
  which means that if we have a finite number of elements of G we can find a single partial solution of
  the chain that captures all the elements, here we state this with `y` and `Lₓ y`. -/
  let T : Finset G := {y, Lₓ y}
  have ⟨⟨e, he⟩, le⟩ := hc.directed.finset_le (hι := ⟨⟨_, h1⟩⟩)
    (T.image fun a ↦ ⟨e a, he a⟩)
  have hT := fun a ha ↦ Finset.forall_image.mp le a ha _ _ (hLₓ a)
  simp only [Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq, T] at hT
  have ⟨ey, eLₓy⟩ := hT
  exact e.2.aux2 ey eLₓy

end GreedyAC

open GreedyAC GreedyB

def seed (x : G') : Rel G G := fun a b ↦ a = x ∧ b = S x

theorem seed_ok (x : G') : OK x (seed x) where
  finite := by   -- x = (a, b, _), so the only element in the set is (x, y = a)
    have h' : S (Sum.inr x) = x.1.1 := rfl
    have final : {(Sum.inr x, Sum.inl x.1.1)} = {(x_2, y) | seed x x_2 y} := by
      have incl1 : {(Sum.inr x, Sum.inl x.1.1)} ⊆ {(x_2, y) | seed x x_2 y}:= by
        rw [Set.singleton_subset_iff]
        exact Set.mem_sep rfl rfl
      have incl2 : {(x_2, y) | seed x x_2 y} ⊆ {(Sum.inr x, Sum.inl x.1.1)} := by
        simp only [Set.subset_singleton_iff, Set.mem_setOf_eq, Prod.forall, Prod.mk.injEq]
        exact fun a b a ↦ a
      exact Set.Subset.antisymm incl1 incl2
    rw [← final]
    exact Set.finite_singleton (Sum.inr x, Sum.inl x.1.1)
  inj x₁ x₂ := by simp_all [seed]
  func h1 h2 := by rw [h1.2, h2.2]
  aux1 := by simp [seed]
  aux2 h1 h2 := by simp_all [seed]

noncomputable def L' (x : G') : G → G := (exists_extension x ⟨seed x, seed_ok x⟩).choose

lemma L'_self (x : G') : L' x x = S x := (exists_extension x ⟨seed x, seed_ok x⟩).choose_spec.1

lemma L'_1516 (x : G') (y : G) : (L (S y) <| L' x <| L' x y) = x :=
  (exists_extension x ⟨seed x, seed_ok x⟩).choose_spec.2 y

noncomputable scoped instance magG : Magma G := {
    op := fun x y =>
      match x with
      | .inl a => L a y
      | .inr g => L' g y
    }

theorem magG_op_def_A (a : A) (g : G) : magG.op a g = L a g := rfl

theorem magG_op_def_G (g' : G') (g : G) : magG.op g' g = L' g' g := rfl

theorem G_satisfies_Equation1516 : Equation1516 G := by
  intro x y
  rcases x with (a | g) <;> rcases y with (a' | g')
  · simp_rw [magG_op_def_A,L_extends]
    rw [magG_op_def_A (a' ◇ a'),L_extends,← A_satisfies_Equation1516]
  · simp_rw [magG_op_def_G, magG_op_def_A]
    rw [L'_self, magG_op_def_A, L_1516 a g'] -- uso l'Ax B per concludere
  · simp_rw [magG_op_def_A]
    rw [L_self,magG_op_def_A]
    simp_rw [magG_op_def_G, L'_1516]
  · simp_rw [magG_op_def_G, L'_self, magG_op_def_A]
    rw [L'_1516]

--we may need to add some additional thesis to the theorem about the construction of L, so that the way L is defined is explicited
lemma op_x₀_self : x₀ ◇ x₀ = (1 : A) := by
  unfold x₀
  rw [magG_op_def_G, L'_self]
  simp [S]

lemma op_1_x₀ : (.inl (1 : A)) ◇ x₀ = (1 : A) := L_x₀

lemma x₀_255_rhs : ((x₀ ◇ x₀) ◇ x₀) ◇ x₀ = (1 : A) := by
  simp_rw [op_x₀_self, op_1_x₀]

lemma x₀_ne_1 : x₀ ≠ (1 : A) := Sum.inr_ne_inl

end Refutation255

@[equational_result]
theorem _root_.Equation1516_not_implies_Equation1489 : ∃ (G : Type) (_ : Magma G), Equation1516 G ∧ ¬ Equation1489 G := by
  let magA : Magma A := { op := fun x y => f (y*x⁻¹) * x  }
  refine ⟨A, magA, ?_, ?_⟩
  · intro x y
    repeat rw [magA_op_def]
    simp only [mul_inv_cancel_right, mul_inv_cancel, mul_inv_rev]
    have := f_translation_invariant_1516 (y * x⁻¹)
    apply_fun fun a ↦ a * (f 1) * y at this
    simp only [mul_inv_rev, inv_inv, inv_mul_cancel_right] at this
    repeat rw [mul_assoc] at *
    exact this.symm
  · simp only [not_forall]
    exists x₁, 1
    repeat rw [magA_op_def]
    simp only [one_mul, fromList_eval x₁⁻¹ x₃, inv_one, mul_one, fromList_eval (x₃ * x₁) x₄,
      fromList_eval x₁ x₂, fromList_eval (x₄ * x₂⁻¹) x₅]
    decide

@[equational_result]
theorem Finite.Equation1516_implies_Equation255 (G : Type) [Magma G] [Finite G] (h : Equation1516 G) : Equation255 G := by
  let S (x:G) := x ◇ x
  let C (x:G) := (S x) ◇ x
  let L (y x:G) := y ◇ x
  have inv_LS : ∀ y, Function.Injective (L (S y)) := by
    intro y
    rw [Finite.injective_iff_surjective]
    intro x
    use x ◇ (x ◇ y)
    dsimp [L, S]
    rw [← h]
  have inv_S : Function.Surjective S := by
    rw [← Finite.injective_iff_surjective]
    intro x y hxy
    have hS x : S x = (L (S x) <| L (S x) <| L (S x) <| x) := h (S x) x
    have hSy := hS y
    rw [← hxy] at hSy
    nth_rewrite 1 [hS x] at hSy
    exact inv_LS x <| inv_LS x <| inv_LS x <| hSy
  have SC_id x : S x = (S (C x)) ◇ S x := by
    convert h .. using 2
    exact h ..
  have SC_CS_id x : S (C x) = C (S x) := by rw [h (S (C x)) (S x), ← SC_id x, ← SC_id x]
  intro x
  obtain ⟨y, hy⟩ := inv_S x
  rw [← hy]
  nth_rewrite 1 [SC_id y]
  rw [SC_CS_id y]

-- @[equational_result]
theorem _root_.Equation1516_not_implies_Equation255 : ∃ (G : Type) (_ : Magma G), Equation1516 G ∧ ¬ Equation255 G := by
  refine ⟨G, magG, G_satisfies_Equation1516, ?_⟩
  unfold Equation255
  push_neg
  exact ⟨x₀, x₀_255_rhs ▸ x₀_ne_1⟩

/--  https://teorth.github.io/equational_theories/blueprint/1516-chapter.html -/
@[equational_result]
conjecture Equation1516_facts : ∃ (G : Type) (_ : Magma G), Facts G [1516] [255]


end Eq1516
