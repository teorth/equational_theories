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
import Mathlib.Tactic.Group

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
private abbrev x₇ := x 7


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

theorem e0_spec : ∀ x y,  y ∈ t.e0 ⬝ x ↔ x = t.b ∧ y = t.c := fun _ _ ↦ TE_mem_singleton'

theorem e1_spec : ∀ x y, y ∈ t.e1 ⬝ x ↔ ∃ a', t.b ∈ t.ps.E ⬝ a' ∧ t.c * a'⁻¹ = x ∧ a'⁻¹ = y := by
  intro x y
  unfold e1
  rw [helper_mem]
  simp only [heq_eq_eq, Option.mem_def]
  refine ⟨fun ⟨a', h⟩ ↦ ?_, fun ⟨a', h⟩ ↦ ?_⟩
  · rw [t.preimages_of_b_spec] at h
    exact ⟨a', h⟩
  · use a'
    rw [t.preimages_of_b_spec]
    assumption

theorem e2_spec : ∀ x y, y ∈ t.e2 ⬝ x ↔ ∃ a' d', t.b ∈ t.ps.E ⬝ a' ∧ d' ∈ t.ps.E ⬝ (a'⁻¹) ∧ d' * a' * t.c⁻¹ = x ∧  a' * t.c⁻¹ = y := by
  unfold e2
  intro x y
  rw [helper'_mem]
  simp only [heq_eq_eq, Option.mem_def, exists_and_left]
  constructor
  · intro ⟨a', h⟩
    rw [t.s_spec] at h
    use a'
    rcases h with ⟨⟨eq1, d', eqd'⟩ ,eq2, eq3⟩
    use eq1, d', eqd'
    rw [eqd'] at eq2
    use eq2, eq3
  · intro ⟨a', eq1, d', eqd', eq2, eq3⟩
    use a'
    rw [t.s_spec]
    use ⟨eq1, d', eqd'⟩
    exact eqd' ▸ ⟨eq2, eq3⟩

noncomputable def newE : TE := t.ps.E ∪ t.e0 ∪ t.e1 ∪ t.e2

theorem disjoint_old_e0 [b_not_in_dom : Fact (t.b ∉ t.ps.E)]: t.ps.E.Disjoint t.e0 := by
  intro x hold he0
  cases TE_lookup_exists.mpr he0 with
  | intro y h =>
    rw [e0_spec] at h
    cases h with
    | intro left right =>
      rw [left] at hold
      exact b_not_in_dom.out hold

theorem disjoint_old_e1 : t.ps.E.Disjoint t.e1 := by
  intro x hold he1
  have := TE_lookup_exists.mpr he1
  cases this with
  | intro y h =>
    rw [e1_spec] at h
    match h with
    | ⟨a', left, eq, _⟩  =>
      apply fresh_ineq t.old x a'⁻¹
      · apply Subgroup.subset_closure
        simp [Subgroup.subset_closure, dom_old _ _ hold]
      · rw [inv_mem_iff]
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
    simp [eq_x_b, b_old]

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
        exact dom_old'_subgroup old'
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
        simp only [mul_left_inj, mul_eq_right] at eq'
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
        simp only [right_eq_mul] at eq'
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
        simp only [mul_eq_left, inv_eq_one] at eq
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
          simp only [mul_left_inj, mul_eq_right] at eq'
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
    rw [← TE_lookup_isSome,← old.2,TE_lookup_isSome] at a'_mem
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
  exact im_old_subgroup new3

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
    simp only [mul_eq_right] at this
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
    exact t.dom_old _ c_mem

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
    have : Fact (t.b ∉ t.ps.E) := ⟨h⟩
    exact ⟨t.extension, t.extension_spec⟩

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
      · exact le
      · exact this.1
    · rw [t.extension2_E]
      have def_t_ps : t.ps = ps' := rfl
      have def_b : t.b = b := rfl
      rw [def_t_ps, def_b] at this
      omega

def translation_invariant_1516 (f : A → A) : Prop := ∀ (x : A), (f ( f ( f x )* x⁻¹ * (f 1)⁻¹)) = x⁻¹ * (f 1)⁻¹

theorem completion (ps : PartialSolution) :
    ∃ (f : A → A), translation_invariant_1516 f ∧ (∀ x y, y ∈ ps.E ⬝ x → f x = y) ∧
      ∀ b, (b ≠ 1) → Set.encard {c | b * c = f c } ≥ 4 := by
  have ⟨c, hc, h1, h2, h3⟩  := exists_greedy_chain (α := PartialSolution) (β := A ⊕ {b : A // b ≠ 1})
    (task := fun b ps => match b with
      | .inl b => ∃ c, c ∈ ps.E ⬝ b
      | .inr ⟨b, _⟩   => Finset.card {c ∈ ps.E.keys | (b*c) ∈ ps.E ⬝ c } ≥ 4)
    ( fun ps b => match b with
      | .inl b => extension_or_nop ps b
      | .inr ⟨b, h⟩   => extension2 ps b h 4) ps
  classical
  simp only [Sum.forall, Subtype.forall] at h3
  choose g hg1 f hf using h3.1
  refine ⟨f, fun x => ?_, fun x y => ?_, fun b h => ?_⟩
  · let S : Finset _ := {x, 1, f x, (f (f x) * x⁻¹ * (f 1)⁻¹)}
    have ⟨⟨e, he⟩, le⟩ := hc.directed.finset_le (hι := ⟨⟨_, h1⟩⟩)
      (S.image fun a => ⟨g a, hg1 a⟩)
    replace le a (ha : a ∈ S) := Finset.forall_mem_image.1 le ha (hf a)
    simp only [Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq, S] at le
    obtain ⟨fx, f1, ffx, fffx⟩ := le
    rw [e.fId] at f1
    injection f1 with eq1
    rw [← eq1] at fffx
    rw [← eq1]
    simp only [inv_one, mul_one] at *
    apply_fun some
    rw [← (e.cond4 x (TE_lookup_mem' fx) (f x) fx (f (f x)) ffx), ← fffx, inv_one, mul_one]
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
    · apply Set.encard_le_encard
      simp only [Option.mem_def, Finset.coe_filter, Set.setOf_subset_setOf, and_imp]
      exact this
    · rw [Set.encard_coe_eq_coe_finsetCard]
      simp only [ge_iff_le, Nat.ofNat_le_cast]
      exact card_ps

def E0 : List (A × A) := [(1, 1), (x₁, x₂), (x₁⁻¹,x₃), (x₃ * x₁, x₄), (x₄ * x₂⁻¹, x₅),
  (x₆⁻¹, x₆^2), (x₆^3, x₆), (x₇⁻¹, x₇^2), (x₇^3, x₇)]

def f0 (a : A) : A := (List.lookup a E0).getD 1

def initial : PartialSolution := by use List.toFinmap (E0.map Prod.toSigma) <;> decide

noncomputable def f := (completion initial).choose
end extension

theorem fromList_eval (a b : A) (h : (a,b) ∈ E0 := by decide) : f a = b := by
  apply (completion initial).choose_spec.2.1
  unfold initial
  simp only [Finmap.dlookup_list_toFinmap]
  rw [List.mem_dlookup_iff, List.mem_map]
  refine ⟨_, h, ?_⟩
  · simp
  · unfold List.NodupKeys
    decide

theorem f_translation_invariant_1516 : translation_invariant_1516 f := (completion initial).choose_spec.1

theorem f_extends_initial : ∀ a b : A, b ∈ initial.E ⬝ a → f a = b := (completion initial).choose_spec.2.1

noncomputable scoped instance magA : Magma A := { op := fun x y => f (y*x⁻¹) * x  }

theorem magA_op_def (x y : A) : magA.op x y = f (y*x⁻¹) * x := rfl

theorem A_satisfies_Equation1516 : Equation1516 A := by
  intro x y
  repeat rw [magA_op_def]
  simp only [mul_inv_cancel_right, mul_inv_cancel, mul_inv_rev]
  have := f_translation_invariant_1516 (y*x⁻¹)
  apply_fun fun a => a * (f 1) * y at this
  simp only [mul_inv_rev, inv_inv, inv_mul_cancel_right] at this
  repeat rw [mul_assoc] at *
  exact this.symm

theorem A_idempotent (x : A) : x ◇ x = x := by simp [magA_op_def, fromList_eval 1 1]

theorem base1 {a b : A} (ineq : a ≠ b) : {c | c ◇ a = b}.encard ≥ 4 := by
  have eq1 : {c | c ◇ a = b} =  {c | f (a*c⁻¹) *  c = b} := by simp [magA_op_def]
  let bij : A ≃ A := ⟨fun (c : A) ↦ a * c⁻¹, fun c ↦ c⁻¹ * a, fun _ ↦ by simp, fun _ ↦ by simp⟩
  have eq2 : {c | (b * a⁻¹) * c = f c} ≃ {c | f (a*c⁻¹) *  c = b} := by
    simp only [Set.coe_setOf]
    refine (Equiv.subtypeEquivOfSubtype bij).symm.trans (Equiv.subtypeEquivRight fun x ↦ ?_)
    simp only [bij, Equiv.coe_fn_mk]
    group
    constructor <;> {intro h ; rw [← h] ; group}
  rw [eq1, ← (Set.encard_congr eq2)]
  refine (completion initial).choose_spec.2.2 (b * a⁻¹) ?_
  apply_fun (fun x ↦ x * a)
  simp [ineq.symm]

theorem base1' {a b : A} (hab : a ≠ b) (c₁ c₂ c₃ : A) : ∃ c, c ◇ a = b ∧ c ≠ c₁ ∧ c ≠ c₂ ∧ c ≠ c₃ := by
  have := base1 hab
  have h : ({c | c ◇ a = b} \ {c₁, c₂, c₃}).Nonempty := by
    refine Set.encard_ne_zero.mp (ne_of_gt ?_)
    calc
      _ < (4 : ENat) - 3 := by norm_num
      _ ≤ _ := by
        gcongr
        simp_rw [Set.insert_eq]
        refine (Set.encard_union_le _ _).trans ?_
        rw [Set.encard_singleton, show (3 : ENat) = 1 + 2 from rfl]
        gcongr
        refine (Set.encard_union_le _ _).trans ?_
        simp_rw [Set.encard_singleton]
        norm_num
      {c | c ◇ a = b}.encard - _ ≤ _ := Set.tsub_encard_le_encard_diff _ {c₁, c₂, c₃}
  rcases h with ⟨c, hc1, hc2⟩
  refine ⟨c, hc1, ?_⟩
  simp_all

theorem base2 (a : A) : ∃ b₁ b₂, b₁ ≠ a ∧ b₂ ≠ a ∧ b₁ ≠ b₂ ∧
    a ◇ (b₁ ◇ a) = b₁ ∧ a ◇ (b₂ ◇ a) = b₂ := by
  refine ⟨x₆ * a, x₇ * a, ?_, ?_, ?_, ?_, ?_⟩
  · simp
  · simp
  · rw [ne_eq, mul_left_inj]
    exact ne_of_beq_false rfl
  · repeat rw [magA_op_def]
    group
    rw [fromList_eval (x₆^(-1)) (x₆^2), fromList_eval (x₆^2 * x₆) (x₆^1)]
    simp
  · repeat rw [magA_op_def]
    group
    rw [fromList_eval (x₇^(-1)) (x₇^2), fromList_eval (x₇^2 * x₇) (x₇^1)]
    simp

theorem base2' (a a' : A) : ∃ b, b ≠ a ∧ b ≠ a' ∧ a ◇ (b ◇ a) = b := by
  rcases base2 a with ⟨b₁, b₂, hb₁a, hb₂a, hb₁b₂, hb₁, hb₂⟩
  by_cases h : b₁ = a'
  · exact ⟨b₂, hb₂a, h ▸ hb₁b₂.symm, hb₂⟩
  · exact ⟨b₁, hb₁a, h, hb₁⟩

theorem A_op_surj_right (a b : A) : ∃ c : A, a ◇ c = b :=
  ⟨b ◇ (b ◇ a), (A_idempotent a ▸ A_satisfies_Equation1516 b a).symm⟩

theorem A_op_eq_self_iff {a c : A} : c ◇ a = a ↔ c = a := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ A_idempotent _⟩
  have := A_satisfies_Equation1516 c a
  simp_rw [h, A_idempotent] at this
  exact this

section Refutation255


/-
Follows https://teorth.github.io/equational_theories/blueprint/1516-chapter.html.
We try to mimick the proof structure from Equation63 for the greedy construction parts.
-/

def G' := {(a, b, _) : A × A × ℕ | a ≠ b}

def G := A ⊕ G'

instance : Countable G' := inferInstance

instance : Countable G := inferInstanceAs (Countable (_ ⊕ _))

instance : Infinite G := inferInstanceAs (Infinite (_ ⊕ _))

instance : Coe A G := ⟨.inl⟩

instance : Coe G' G := ⟨.inr⟩

/-- Square function: `S a = a ◇ a`.
On `A` it is the identity, on `G'` it corresponds to the function `(a, b, n) ↦ a`. -/
def S : G → A
  | .inl a => a
  | .inr g => g.1.1

/- We consider a special element `x₀ = (*, 0, 0) ∈ G'`, where `*` is the identity of `A`, i.e. the empty word.
This is needed for Corollary 17.7; note that by doing this we are taking a sligthly different route from the proof of the corollary in the blueprint, in particular we make an explicit example of an element that does not verify eq 255. -/
def x₀ : G := .inr ⟨⟨1, x 0, 0⟩, fun h ↦ one_ne_of 0 h⟩

namespace GreedyB
-- Greedy construction to extend the operation from A×A to A×G' in order to satisfy Axiom B, we try to mimic the structure of GreedyAC below

lemma exists_useful_c (y : G') : ∃ c : A → A, c.Injective ∧
    ∀ b, y.1.1 ◇ ((c b) ◇ b) = c b ∧ c b ≠ b ∧ c b ≠ y.1.1 ∧ c b ≠ y.1.2.1 := by
  rcases base2' y.1.1 y.1.2.1 with ⟨c₁, hc₁a, hc₁c, hc₁⟩
  have c_aux {b : A} (h : y.1.1 ≠ b) : ∃ c, c ◇ y.1.1 = b ∧ c ≠ c₁ ∧ c ≠ b ∧ c ≠ y.1.2.1 :=
    base1' h c₁ b y.1.2.1
  let c := fun b : A ↦ if h : y.1.1 = b then c₁ else (c_aux h).choose
  refine ⟨c, fun b₁ b₂ ↦ ?_, fun b ↦ ?_⟩
  · unfold c
    rcases ne_or_eq y.1.1 b₁ with hx | ha <;> rcases ne_or_eq y.1.1 b₂ with hy | ha'
    · rw [dif_neg hx, dif_neg hy]
      intro hind
      have prop : (c_aux hx).choose ◇ y.1.1 = (c_aux hy).choose ◇ y.1.1 := by rw [hind]
      have h_aux : (c_aux hx).choose ◇ y.1.1 = b₁ := (c_aux hx).choose_spec.1
      have h_aux2 : (c_aux hy).choose ◇ y.1.1 = b₂ := (c_aux hy).choose_spec.1
      rw [h_aux, h_aux2] at prop
      exact prop
    · rw [dif_neg hx, dif_pos ha']
      exact fun h ↦ ((c_aux hx).choose_spec.2.1 h).elim
    · rw [dif_pos ha, dif_neg hy]
      exact fun h ↦ ((c_aux hy).choose_spec.2.1 h.symm).elim
    · exact fun h ↦ ha ▸ ha'
  · unfold c
    rcases ne_or_eq y.1.1 b with h1 | h2
    · rw [dif_neg h1]
      refine ⟨?_, ⟨(c_aux h1).choose_spec.2.2.1, ?_, (c_aux h1).choose_spec.2.2.2⟩⟩
      · nth_rw 1 [← A_idempotent y.1.1]
        nth_rw 4 [← (c_aux h1).choose_spec.1]
        exact (A_satisfies_Equation1516 _ _).symm
      · by_contra h
        have := A_idempotent _ ▸ h ▸ (c_aux h1).choose_spec.1
        exact h1 this
    · simp_rw [dif_pos h2, ← h2, hc₁]
      exact ⟨trivial, hc₁a, hc₁a, hc₁c⟩

noncomputable abbrev useful_c (y : G') : A → A := (exists_useful_c y).choose

lemma useful_c_injective (y : G') : (useful_c y).Injective := (exists_useful_c y).choose_spec.1

lemma useful_c_spec (y : G') (b : A) : y.1.1 ◇ ((useful_c y b) ◇ b) = useful_c y b :=
  (exists_useful_c y).choose_spec.2 b |>.1

lemma useful_c_ne_b (y : G') (b : A) : useful_c y b ≠ b :=
  (exists_useful_c y).choose_spec.2 b |>.2.1

lemma useful_c_ne_y₁ (y : G') (b : A) : useful_c y b ≠ y.1.1 :=
  (exists_useful_c y).choose_spec.2 b |>.2.2.1

lemma useful_c_ne_y₂ (y : G') (b : A) : useful_c y b ≠ y.1.2.1 :=
  (exists_useful_c y).choose_spec.2 b |>.2.2.2

structure OK (E : A → G → G → Prop) : Prop where
  func {a x y y'} : E a x y → E a x y' → y = y'
  extend (a b : A) : E a b (.inl (a ◇ b)) -- (a)
  h_b {a : A} {y : G'} : S y = a → y.1.2.2 = 0 → E a y a -- (b)
  h_c {a : A} {y : G'} : S y = a → y.1.2.2 ≠ 0 → E a y (.inr ⟨⟨y.1.1, y.1.2.1, 0⟩, y.2⟩) -- (c)
  h_d {b : A} {y : G'} : E (useful_c y b) y b -- (d)
  finite {a c : A} (hac : a ≠ c) : {n | ∃ x, E c (.inr ⟨⟨a, c, n⟩, hac⟩) x}.Finite -- (e)
  h_1516 {c' : A} {y : G'} {x : G} : E c' y x → ∃ w, E c' x w ∧ E (S y) w c' -- (f)
  h_g {c' : A} {y : G'} {x : G} : S y ≠ c' → E c' y x → x ≠ .inl c' -- (g)

abbrev PartialSolution := {E : A → G → G → Prop // OK E}

lemma E_1_x₀ {E : PartialSolution} : E.val 1 x₀ (.inl 1) := E.property.h_b rfl rfl

lemma def_trichotomy {E : A → G → G → Prop} (h_ok : OK E) {a : A} {y : G'} {x : G} (h : E a y x) :
    (∃ w : G', E a y w) ∨ (S y ≠ a ∧ ∃ b : A, E a y b) ∨
      (S y = a ∧ y.1.2.2 = 0 ∧ E a y a) := by
  rcases x with (b | w)
  · by_cases hSy : S y = a
    · by_cases hn : y.1.2.2 = 0
      · exact Or.inr (Or.inr ⟨hSy, hn, h_ok.h_b hSy hn⟩)
      · exact Or.inl ⟨_, h_ok.h_c hSy hn⟩
    · exact Or.inr <| Or.inl ⟨hSy, ⟨_, h⟩⟩
  · exact Or.inl ⟨_, h⟩

/-- A partial soution, along with a pair `(d, g)` such that `L d g` is not yet defined. -/
class Extension1 where
  E : A → G → G → Prop
  ok : OK E
  d : A
  y : G'
  not_def {z} : ¬E d y z

/-- A partial solution, along with a pair `(a, y)` such that `L a y` is already defined and
`n ∈ ℕ`, a lower bound for the cardinality of `{z | E a z y}` after the extension step. -/
class Extension2 where
  E : A → G → G → Prop
  ok : OK E
  d : A
  y : G'
  g : G
  h_def : E d y g
  n : ℕ

namespace Extension1

/-- For a pair `(c', y)` such that `L c' y` is not yet defined, we define `L c' y` as `b` such that `L a <| L c' b = c'`. -/
noncomputable def partL (c' : A) (y : G') : G :=
  .inl (A_op_surj_right c' (A_op_surj_right (S y) c').choose).choose

lemma partL_spec (c' : A) (y : G') :
    ∃ b b' : A, partL c' y = b' ∧ S y ◇ b = c' ∧ c' ◇ b' = b :=
  ⟨(A_op_surj_right y.1.1 c').choose, (A_op_surj_right c' _).choose, rfl,
    (A_op_surj_right _ _).choose_spec, (A_op_surj_right _ _).choose_spec⟩

variable [Extension1]

@[mk_iff]
inductive Next1 : A → G → G → Prop
  | base {a y x} : E a y x → Next1 a y x
  | new : Next1 d y (partL d y)

lemma next1_func {a x y y'} : Next1 a x y → Next1 a x y' → y = y'
  | .base hy, .base hy' => ok.func hy hy'
  | .new, .new => rfl
  | .base hy, .new | .new, .base hy => (not_def hy).elim

lemma next1_extend (a b : A) : Next1 a b (.inl (a ◇ b)) := Next1.base (ok.extend _ _)

lemma next1_h_b {a : A} {y : G'} (hSy : S y = a) (hn : y.1.2.2 = 0) : Next1 a y (.inl a) :=
  .base (ok.h_b hSy hn)

lemma next1_h_c {a : A} {y : G'} (hSy : S y = a) (hn : y.1.2.2 ≠ 0) :
    Next1 a y (.inr ⟨⟨y.1.1, y.1.2.1, 0⟩, y.2⟩) := .base (ok.h_c hSy hn)

lemma next1_h_d {b : A} {y : G'} : Next1 (useful_c y b) y b := .base ok.h_d

lemma next1_finite {a c : A} (hac : a ≠ c) :
    {n | ∃ x, Next1 c (.inr ⟨⟨a, c, n⟩, hac⟩) x}.Finite := by
  simp only [next1_iff, exists_or, exists_and_left, Set.setOf_or, Set.finite_union,
    ok.finite, true_and]
  refine (Set.finite_singleton y.1.2.2).subset fun n hn ↦ ?_
  simp [← Sum.inr_injective hn.2.1]

lemma next1_h_1516 {c' : A} {z : G'} {x : G} : Next1 c' z x → ∃ w, Next1 c' x w ∧ Next1 (S z) w c'
  | .base h =>
    have ⟨w, hw1, hw2⟩ := ok.h_1516 h
    ⟨w, Next1.base hw1, Next1.base hw2⟩
  | .new => by
    have ⟨b, b', hb', hab, hdb'⟩ := partL_spec d y
    rw [hb']
    refine ⟨_, .base (ok.extend d _), ?_⟩
    rw [hdb', ← hab]
    exact next1_extend _ _

lemma next1_h_g {c' : A} {z : G'} {x : G} (hSy : S z ≠ c') : Next1 c' z x → x ≠ .inl c'
  | .base h => ok.h_g hSy h
  | .new => by
    have ⟨b, b', hb', hab, hdb'⟩ := partL_spec d y
    rw [hb']
    intro h
    apply Sum.inl_injective at h
    exact hSy (A_op_eq_self_iff.mp ((A_idempotent _ ▸ h ▸ hdb') ▸ hab))

def next1 : PartialSolution :=
  ⟨Next1, next1_func, next1_extend, next1_h_b, next1_h_c, next1_h_d, next1_finite,
    next1_h_1516, next1_h_g⟩

end Extension1

namespace Extension2

variable [Extension2]

lemma exists_extra_set1 (w : G') : ∃ s : Finset G',
    s.card = n ∧ ∀ z ∈ s, z.1.1 = useful_c w d ∧ z.1.2.1 = d ∧ ∀ x, ¬ E d z x := by
  have h_infinite : Set.Infinite <| ({(⟨⟨_, d, n'⟩, useful_c_ne_b w d⟩ : G') | n'} \
      (fun m ↦ ⟨⟨_, d, m⟩, useful_c_ne_b w d⟩) ''
        {n | ∃ x, E d (.inr ⟨⟨_, d, n⟩, useful_c_ne_b w d⟩) x}) := by
    refine (Set.Infinite.diff ?_ ((ok.finite _).image _))
    let f : ℕ → G' := fun n ↦ ⟨⟨_, d, n⟩, useful_c_ne_b w d⟩
    have f_inj : f.Injective := by
      intro n m h
      simp_all only [Subtype.mk.injEq, Prod.mk.injEq, f]
    exact Set.infinite_range_of_injective f_inj
  have ⟨s, hs_sub, hs_card⟩ := Set.Infinite.exists_subset_card_eq h_infinite n
  refine ⟨s, hs_card, fun z hz ↦ ?_⟩
  have hz := hs_sub hz
  simp only [Set.mem_diff, Set.mem_image, not_exists, not_and] at hz
  have ⟨⟨n', hn'z⟩, h_not_E⟩ := hz
  simp only [← hn'z, true_and]
  exact fun x hx ↦ h_not_E _ ⟨_, hx⟩ hn'z

noncomputable def extra_set1 (w : G') : Finset G' := (exists_extra_set1 w).choose

lemma extra_set1_card (w : G') : (extra_set1 w).card = n := (exists_extra_set1 w).choose_spec.1

lemma extra_set1_eq1 {w z : G'} (hz : z ∈ extra_set1 w) :
    z.1.1 = useful_c w d := (exists_extra_set1 w).choose_spec.2 z hz |>.1

lemma extra_set1_eq2 {w z : G'} (hz : z ∈ extra_set1 w) :
    z.1.2.1 = d := (exists_extra_set1 w).choose_spec.2 z hz |>.2.1

lemma extra_set1_not_E {w z : G'} (hz : z ∈ extra_set1 w) {x : G} :
    ¬ E d z x := (exists_extra_set1 w).choose_spec.2 z hz |>.2.2 x

lemma exists_extra_set2 {b : A} (hb : E d y b) (hSy : S y ≠ d) :
    ∃ (a' : A), a' ◇ b = d ∧ a' ≠ d ∧
      ∃ s : Finset G', s.card = n ∧ ∀ z ∈ s, z.1.1 = a' ∧ z.1.2.1 = d ∧ ∀ x, ¬ E d z x := by
  have ⟨a', ha'b, ha'd, _, _⟩ := base1' (fun (h : b = d) ↦ ok.h_g hSy hb (h ▸ rfl)) d d d
  refine ⟨a', ha'b, ha'd, ?_⟩
  have h_infinite : Set.Infinite <| ({(⟨⟨a', d, n'⟩, ha'd⟩ : G') | n'} \
      (fun m ↦ ⟨⟨a', d, m⟩, ha'd⟩) '' {n | ∃ x, E d (.inr ⟨⟨a', d, n⟩, ha'd⟩) x}) := by
    refine (Set.Infinite.diff ?_ ((ok.finite _).image _))
    let f : ℕ → G' := fun n ↦ ⟨⟨a', d, n⟩, ha'd⟩
    have f_inj : f.Injective := by
      intro n m h
      simp_all only [Subtype.mk.injEq, Prod.mk.injEq, f]
    exact Set.infinite_range_of_injective f_inj
  have ⟨s, hs_sub, hs_card⟩ := Set.Infinite.exists_subset_card_eq h_infinite n
  refine ⟨s, hs_card, fun z hz ↦ ?_⟩
  have hz := hs_sub hz
  simp only [Set.mem_diff, Set.mem_image, not_exists, not_and] at hz
  have ⟨⟨n', hn'z⟩, h_not_E⟩ := hz
  simp only [← hn'z, true_and]
  exact fun x hx ↦ h_not_E _ ⟨_, hx⟩ hn'z

noncomputable def es2_a' {b : A} (hb : E d y b) (hSy : S y ≠ d) : A :=
  (exists_extra_set2 hb hSy).choose

lemma es2_a'_spec {b : A} (hb : E d y b) (hSy : S y ≠ d) :
    es2_a' hb hSy ◇ b = d := (exists_extra_set2 hb hSy).choose_spec.1

lemma es2_a'_ne {b : A} (hb : E d y b) (hSy : S y ≠ d) :
    es2_a' hb hSy ≠ d := (exists_extra_set2 hb hSy).choose_spec.2.1

noncomputable def extra_set2 {b : A} (hb : E d y b) (hSy : S y ≠ d) : Finset G' :=
  (exists_extra_set2 hb hSy).choose_spec.2.2.choose

lemma extra_set2_card {b : A} (hb : E d y b) (hSy : S y ≠ d) : (extra_set2 hb hSy).card = n :=
  (exists_extra_set2 hb hSy).choose_spec.2.2.choose_spec.1

lemma extra_set2_eq1 {b : A} (hb : E d y b) (hSy : S y ≠ d)
    {z : G'} (hz : z ∈ extra_set2 hb hSy) : z.1.1 = es2_a' hb hSy :=
  (exists_extra_set2 hb hSy).choose_spec.2.2.choose_spec.2 z hz |>.1

lemma extra_set2_eq2 {b : A} (hb : E d y b) (hSy : S y ≠ d)
    {z : G'} (hz : z ∈ extra_set2 hb hSy) : z.1.2.1 = d :=
  (exists_extra_set2 hb hSy).choose_spec.2.2.choose_spec.2 z hz |>.2.1

lemma extra_set2_not_E {b : A} (hb : E d y b) (hSy : S y ≠ d)
    {z : G'} (hz : z ∈ extra_set2 hb hSy) {x : G} : ¬ E d z x :=
  (exists_extra_set2 hb hSy).choose_spec.2.2.choose_spec.2 z hz |>.2.2 _

@[mk_iff]
inductive Next2 : A → G → G → Prop
  | base {a z x} : E a z x → Next2 a z x
  | extra1 {z} {w₁ : G'} (hw₁ : E d y w₁) : z ∈ extra_set1 w₁ → Next2 d z y
  | extra2 {z} {b : A} (hb : E d y b) (hSy : S y ≠ d) : z ∈ extra_set2 hb hSy → Next2 d z y

lemma next2_func {a x y y'} : Next2 a x y → Next2 a x y' → y = y'
  | .base h, .base h' => ok.func h h'
  | .base h, .extra1 _ hz => (extra_set1_not_E hz h).elim
  | .base h, .extra2 hb hSy hz => (extra_set2_not_E hb hSy hz h).elim
  | .extra1 _ hz, .base h => (extra_set1_not_E hz h).elim
  | .extra1 .., .extra1 .. => rfl
  | .extra1 .., .extra2 .. => rfl
  | .extra2 hb hSy hz, .base h => (extra_set2_not_E hb hSy hz h).elim
  | .extra2 .., .extra1 .. => rfl
  | .extra2 .., .extra2 .. => rfl

lemma next2_extend (a b : A) : Next2 a b (.inl (a ◇ b)) := Next2.base (ok.extend _ _)

lemma next2_h_b {a : A} {y : G'} (hSy : S y = a) (hn : y.1.2.2 = 0) : Next2 a y (.inl a) :=
  .base (ok.h_b hSy hn)

lemma next2_h_c {a : A} {y : G'} (hSy : S y = a) (hn : y.1.2.2 ≠ 0) :
    Next2 a y (.inr ⟨⟨y.1.1, y.1.2.1, 0⟩, y.2⟩) := .base (ok.h_c hSy hn)

lemma next2_h_d {b : A} {y : G'} : Next2 (useful_c y b) y b := .base ok.h_d

lemma next2_finite {a c : A} (hac : a ≠ c) :
    {n | ∃ x, Next2 c (.inr ⟨⟨a, c, n⟩, hac⟩) x}.Finite := by
  simp only [next2_iff, exists_or, Set.setOf_or, Set.finite_union, ok.finite, true_and]
  rcases hw : g with (b | w)
  · have {z} : ¬ E d y (.inr z) := fun h ↦ Sum.inr_ne_inl <| hw ▸ ok.func h h_def
    simp only [this, false_and, exists_false, Set.setOf_false, Set.finite_empty, true_and]
    by_cases hSy : S y = d
    · simp [hSy]
    · refine Set.Finite.subset (s := {n' | ∃ z ∈ extra_set2 (hw ▸ h_def) hSy, z.1.2.2 = n'}) ?_ ?_
      · exact (Finset.finite_toSet _).image _
      · intro n' ⟨y₁, z, b₁, hb₁, _, hz_in, _, hz, hy₁⟩
        simp only [Set.mem_setOf_eq]
        refine ⟨z, ?_, ?_⟩
        · convert hz_in
          exact Sum.inl_injective <| ok.func (hw ▸ h_def) hb₁
        · rw [← Sum.inr_injective hz]
  · have {a} : ¬ E d y (.inl a) := fun h ↦ Sum.inl_ne_inr <| hw ▸ ok.func h h_def
    simp only [this, IsEmpty.exists_iff, exists_false, Set.setOf_false, Set.finite_empty, and_true]
    refine ((Finset.finite_toSet _).image _).subset (s := (fun z : G' ↦ z.1.2.2) '' (extra_set1 w))
      fun n' ⟨y₁, ⟨z, w₁, hw₁, hz_in, _, hz, _⟩⟩ ↦ ⟨z, ?_, Sum.inr_injective hz ▸ rfl⟩
    simp only [Sum.inr_injective <| ok.func (hw ▸ h_def) hw₁, Finset.mem_coe, hz_in]

lemma next2_h_1516 {c' : A} {z : G'} {x : G} : Next2 c' z x → ∃ w₁, Next2 c' x w₁ ∧ Next2 (S z) w₁ c'
  | .base h => by
    have ⟨w₂, hw1, hw2⟩ := ok.h_1516 h
    exact ⟨w₂, Next2.base hw1, Next2.base hw2⟩
  | .extra1 hw₀ hz => by
    rw [S, extra_set1_eq1 hz]
    exact ⟨_, .base hw₀, .base ok.h_d⟩
  | .extra2 hb hSy hz => by
    refine ⟨_, .base hb, .base ?_⟩
    rw [S, extra_set2_eq1 hb hSy hz, ← es2_a'_spec hb hSy]
    exact ok.extend ..

lemma next2_h_g {c' : A} {z : G'} {x : G} (hSy : S z ≠ c') : Next2 c' z x → x ≠ .inl c'
  | .base h => ok.h_g hSy h
  | .extra1 .. | .extra2 .. => Sum.inr_ne_inl

def next2 : PartialSolution :=
  ⟨Next2, next2_func, next2_extend, next2_h_b, next2_h_c, next2_h_d, next2_finite,
    next2_h_1516, next2_h_g⟩

lemma next2_le_encard : n ≤ {z : G' | Next2 d z y}.encard := by
  rcases def_trichotomy ok h_def with (⟨w, hw⟩ | ⟨hSy, ⟨b, hb⟩⟩ | ⟨hSy, hn, _⟩)
  · rw [← extra_set1_card, ← Set.encard_coe_eq_coe_finsetCard]
    exact Set.encard_mono fun z hz ↦ .extra1 hw hz
  · rw [← extra_set2_card hb hSy, ← Set.encard_coe_eq_coe_finsetCard]
    exact Set.encard_mono fun z hz ↦ .extra2 hb hSy hz
  · let f : ℕ → G' := fun m ↦ ⟨⟨y.1.1, y.1.2.1, m + 1⟩, y.2⟩
    have f_inj : f.Injective := by
      intro n m h
      simp_all only [Subtype.mk.injEq, Prod.mk.injEq, add_left_inj, f]
    calc
      (n : ENat) = (Finset.range n).card := by rw [Finset.card_range n]
      _ = (Finset.range n).toSet.encard := (Set.encard_coe_eq_coe_finsetCard _).symm
      _ = (f '' (Finset.range n)).encard := (f_inj.encard_image _).symm
      _ ≤ _ := by
        refine Set.encard_mono fun z hz ↦ ?_
        have ⟨m, hm, hz⟩ := hz
        simp_rw [← hz, Set.mem_setOf_eq, f]
        convert next2_h_c ..
        · rw [S, ← hSy, S]
        · exact Nat.add_one_ne_zero m

end Extension2

-- PRed to Mathlib, see #21473
lemma _root_.ENat.eq_top_iff_forall_lt (n : ENat) : n = ⊤ ↔ ∀ m : ℕ, m < n := by
  rw [ENat.eq_top_iff_forall_ne]
  refine ⟨fun h m ↦ ?_, fun a m ↦ (a m).ne⟩
  contrapose! h
  exact Option.ne_none_iff_exists.mp fun a ↦ ENat.coe_ne_top _ <| top_le_iff.mp (a ▸ h)

--this lemma should be put into Mathlib, maybe in Mathlib.Data.ENat.Basic next to ENat.ne_top_iff_exists
lemma _root_.ENat.eq_top_iff_forall_le (n : ENat) : n = ⊤ ↔ ∀ m : ℕ, m ≤ n := by
  rw [ENat.eq_top_iff_forall_lt]
  refine ⟨fun h m ↦ le_of_lt (h m), fun h m ↦ (h (m + 1)).trans_lt' ?_⟩
  exact (ENat.lt_add_one_iff (ENat.coe_ne_top m)).mpr (le_refl _)

theorem exists_extension (seed : PartialSolution) : ∃ L : A → G → G,
      (∀ a b : A, L a b = a ◇ b) ∧ -- Lb extends a : A ↦ b ◇ a
      (∀ b : A, ∀ x : G', (L (S x) <| L b <| L b x) = b) ∧ -- Axiom B
      (L 1 x₀ = .inl 1) ∧
      (∀ b : A, ∀ y : G', {z : G' | L b z = y}.Infinite) -- infinite surjectivity
    := by
  have ⟨c, hc, h1, h2, h3⟩ := exists_greedy_chain (a := seed)
    (task := fun (a, y, n) ↦ {e | (∃ x, e.1 a y x) ∧ ((∃ a, y = .inl a) ∨ n ≤ {z : G' | e.1 a z y}.encard)})
    fun ⟨E, ok⟩ ((d, y, n) : A × G × ℕ) ↦ by
      rcases y with (a | y)
      · exact ⟨⟨E, ok⟩, fun _ _ _ a ↦ a, ⟨⟨_, ok.extend d a⟩, Or.inl ⟨a, rfl⟩⟩⟩
      if hg : ∃ g, E d y g then
        have ⟨g, h_def⟩ := hg
        let E2 : Extension2 := { E, ok, d, y, g, h_def, n }
        exact ⟨E2.next2, fun _ _ _ ↦ (.base ·), ⟨_, .base h_def⟩, Or.inr E2.next2_le_encard⟩
      else
        let E1 : Extension1 := { E, ok, d, y, not_def := fun h ↦ hg ⟨_, h⟩ }
        match h : E1.next1 with | ⟨E, ok⟩ => ?_
        simp_rw [Extension1.next1, Subtype.mk.injEq, eq_comm] at h
        have h_def : E d y (Extension1.partL d y) := by convert Extension1.Next1.new
        let E2 : Extension2 := { E, ok, d, y, g := _, h_def, n}
        refine ⟨E2.next2, fun _ _ _ ha ↦ .base ?_, ⟨_, .base h_def⟩, Or.inr E2.next2_le_encard⟩
        convert Extension1.Next1.base ha
  choose! e he L hL_card using h3
  choose L hL using L
  have L_of_e {a : A} {y x : G} (n : ℕ) {e₀ : PartialSolution} (he₀ : e₀ ∈ c)
      (h : e₀.val a y x) : L (a, y, n) = x := by
    rcases hc.total he₀ (he (a, y, n)) with (h_le | h_le)
    · exact (e (a, y, n)).2.func (hL (a, y, n)) (h_le _ _ _ h)
    · exact e₀.2.func (h_le _ _ _ (hL (a, y, n))) h
  have L_func (a : A) (y : G) (n n' : ℕ) : L (a, y, n) = L (a, y, n') := by
    classical
    let T : Finset (A × G × ℕ) := {
      (a, y, n),
      (a, y, n')}
    have ⟨⟨e, he⟩, le⟩ := hc.directed.finset_le (hι := ⟨⟨_, h1⟩⟩)
      (T.image fun p ↦ ⟨e p, he p⟩)
    have hT := fun p hp ↦ Finset.forall_mem_image.mp le hp _ _ _ (hL p)
    simp only [Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq, T] at hT
    have ⟨e_n, e_n'⟩ := hT
    exact e.2.func e_n e_n'
  refine ⟨fun a y ↦ L (a, y, 0), fun a b ↦ L_of_e _ h1 (seed.property.extend a b), fun a x ↦ ?_,
    L_of_e _ h1 E_1_x₀, fun b y ↦ ?_⟩
  · have ⟨w, e_a_L, e_Sx_L⟩ := (e _).2.h_1516 (hL (a, x, 0))
    exact L_of_e 0 (he _) (L_of_e 0 (he _) e_a_L ▸ e_Sx_L)
  · rw [← Set.encard_eq_top_iff, ENat.eq_top_iff_forall_le]
    intro n
    have h_le := hL_card (b, y, n)
    simp only [reduceCtorEq, exists_const, false_or] at h_le
    simp_rw [L_func _ _ _ n]
    refine h_le.trans <| Set.encard_mono fun z hz ↦ L_of_e n (he _) hz

@[mk_iff]
inductive seed : A → G → G → Prop
  | case0 (a b : A) : seed a b (.inl (a ◇ b))
  | case1 {c'} {y : G'} : S y = c' → y.1.2.2 = 0 → seed c' y c'
  | case2 {c'} {y : G'} : S y = c' → y.1.2.2 ≠ 0 → seed c' y (.inr ⟨⟨y.1.1, y.1.2.1, 0⟩, y.2⟩)
  | case3 (y : G') (b) : seed (useful_c y b) y b

lemma seed_func {a x y y'} : seed a x y → seed a x y' → y = y' := by
  intro h h'
  rcases h with (_ | ⟨hSy, hn⟩ | ⟨hSy, hn⟩)
  · rcases h'
    rfl
  · rcases h' with (_ | ⟨hSy', hn'⟩ | ⟨hSy', hn'⟩)
    · rfl
    · exact (hn' hn).elim
    · exact (useful_c_ne_y₁ _ _ hSy.symm).elim
  · rcases h' with (⟨hSy', hn'⟩ | ⟨hSy', hn'⟩ | _)
    · exact (hn hn').elim
    · rfl
    · exact (useful_c_ne_y₁ _ _ hSy.symm).elim
  · rw [seed_iff] at h'
    rcases h' with (⟨b, hyb, _⟩ | ⟨_, hS, _, hy, _⟩ | ⟨_, hS, _, hy, _⟩ | ⟨_, b', hc, hy, hy'⟩)
    · exact (Sum.inr_ne_inl hyb).elim
    · rw [Sum.inr_injective hy, S] at hS
      exact (useful_c_ne_y₁ _ _ hS.symm).elim
    · rw [Sum.inr_injective hy, S] at hS
      exact (useful_c_ne_y₁ _ _ hS.symm).elim
    · rw [Sum.inr_injective hy] at hc
      rw [hy', useful_c_injective _ hc]

lemma seed_extend (a b : A) : seed a b (.inl (a ◇ b)) := .case0 a b

lemma seed_h_b {a : A} {y : G'} (hSy : S y = a) (hn : y.1.2.2 = 0) : seed a y a := .case1 hSy hn

lemma seed_h_c {a : A} {y : G'} (hSy : S y = a) (hn : y.1.2.2 ≠ 0) :
    seed a y (.inr ⟨⟨y.1.1, y.1.2.1, 0⟩, y.2⟩) := .case2 hSy hn

lemma seed_h_d {b : A} {y : G'} : seed (useful_c y b) y b := .case3 y b

lemma not_seed_of_eq_snd {a c : A} (hac : a ≠ c) (n : ℕ) (x : G) :
    ¬ seed c (.inr ⟨⟨a, c, n⟩, hac⟩) x := by
  intro h
  rw [seed_iff] at h
  rcases h with (⟨b, hb, hx⟩ | ⟨y, hSy, hn, hy, _⟩ | ⟨y, hSy, hn, hy, _⟩ | ⟨y, b', hc, hy, _⟩)
  · exact Sum.inr_ne_inl hb
  · rw [← hy] at hSy
    exact hac hSy
  · rw [← hy] at hSy
    exact hac hSy
  · rw [← Sum.inr_injective hy] at hc
    exact useful_c_ne_y₂ _ _ hc.symm

lemma seed_finite {a c : A} (hac : a ≠ c) : {n | ∃ x, seed c (.inr ⟨⟨a, c, n⟩, hac⟩) x}.Finite := by
  convert Set.finite_empty
  rw [Set.eq_empty_iff_forall_notMem]
  exact fun n ⟨x, hx⟩ ↦ not_seed_of_eq_snd hac n x hx

lemma seed_h_1516 {c' : A} {y : G'} {x : G} : seed c' y x → ∃ w, seed c' x w ∧ seed (S y) w c'
  | .case1 hSy _ => by
    have hc' := A_idempotent _ ▸ seed.case0 c' c'
    exact ⟨c', hc', hSy ▸ hc'⟩
  | .case2 hSy _ => by
    have hc' := A_idempotent _ ▸ seed.case0 c' c'
    refine ⟨c', seed.case1 ?_ rfl, hSy ▸ hc'⟩
    rw [S, ← hSy, S]
  | .case3 y b => by
    have h := useful_c_spec _ _ ▸ seed.case0 (S y) (useful_c y b ◇ b)
    exact ⟨.inl (useful_c y b ◇ b), seed.case0 .., h⟩

lemma seed_h_g {c' : A} {y : G'} {x : G} (hSy : S y ≠ c') : seed c' y x → x ≠ .inl c'
  | .case1 hSy' _ => (hSy hSy').elim
  | .case2 hSy' _ => (hSy hSy').elim
  | .case3 y b => Sum.inl_injective.mt (useful_c_ne_b y b).symm

lemma seed_ok : OK seed where
  func := seed_func
  extend := seed_extend
  h_b := seed_h_b
  h_c := seed_h_c
  h_d := seed_h_d
  finite := seed_finite
  h_1516 := seed_h_1516
  h_g := seed_h_g

noncomputable def L : A → G → G := (exists_extension ⟨seed, seed_ok⟩).choose

theorem L_extends (a b : A) : L a b = a ◇ b := (exists_extension ⟨seed, seed_ok⟩).choose_spec.1 a b

theorem L_1516 (b : A) (x : G') : (L (S x) <| L b <| L b x) = b :=
  (exists_extension ⟨seed, seed_ok⟩).choose_spec.2.1 b x

theorem L_x₀ : L 1 x₀ = .inl 1 := (exists_extension ⟨seed, seed_ok⟩).choose_spec.2.2.1

theorem L_surjective (b : A) (x : G') : {y : G' | L b y = x}.Infinite :=
  (exists_extension ⟨seed, seed_ok⟩).choose_spec.2.2.2 b x

theorem L_self (a : A) : L a a = S a := by rw [L_extends a a, A_idempotent, S]

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

/-- {y : G | ∃ z, E x y z} -/
def partial_domain' : Set G := (E x).dom

noncomputable instance : Fintype (partial_domain' x) := by
  suffices h : Set.Finite {z : G | ∃ y, E x z y} by exact h.fintype
  let f : G × G → G := fun x ↦ x.1
  have h1 : f '' {(z, y) : G × G | E x z y} ⊆ {z : G | ∃ (y : G) , E x z y} := by
    intro a ha
    simp only [Set.mem_image, Set.mem_setOf_eq, Prod.exists] at ha
    rcases ha with ⟨a1, a2, ha1, ha2⟩
    rw [← ha2]
    tauto
  have h2 : {z : G | ∃ y, E x z y} ⊆ f '' {(z, y) : G × G | E x z y} := by
    intro y hy
    simp only [Set.mem_image, Set.mem_setOf_eq, Prod.exists]
    rcases hy with ⟨y2, hy2⟩
    use y, y2
  exact h1.antisymm h2 ▸ Set.Finite.image f ok.finite

/-- {y : G | ∃ z, E x y z} as a Finset. -/
noncomputable def partial_domain : Finset G := (partial_domain' x).toFinset

/-- {z : G | ∃ y, E x y z} -/
def partial_range' : Set G := (E x).codom

noncomputable instance : Fintype (partial_range' x) := by
  suffices h : Set.Finite {y : G | ∃ z, E x z y} by exact h.fintype
  let f : G × G → G := fun x ↦ x.2
  have h1 : f '' {(z, y) : G × G | E x z y} ⊆ {y : G | ∃ z, E x z y} := by
    intro a ha
    simp only [Set.mem_image, Prod.exists, exists_eq_right] at ha
    simp_all [f]
  have h2 : {y : G | ∃ z, E x z y} ⊆ f '' {(z, y) : G × G | E x z y} := by
    intro y hy
    simp only [Set.mem_image, Prod.exists, exists_eq_right]
    simp_all [f]
  exact h1.antisymm h2 ▸ Set.Finite.image f ok.finite

/-- {z : G | ∃ y, E x y z} as a Finset. -/
noncomputable def partial_range : Finset G := (partial_range' x).toFinset

lemma exists_not_in_domain_range : ∃ w, w ∉ partial_domain x ∧ w ∉ partial_range x ∧ w ≠ d x := by
  have hA : (partial_domain x).toSet.Finite := by
    rw [partial_domain, Set.coe_toFinset]
    exact (partial_domain' x).toFinite
  have hB : (partial_range x).toSet.Finite := by
    rw [partial_range, Set.coe_toFinset]
    exact (partial_range' x).toFinite
  have h2 : ¬ Set.Finite (Set.univ : Set G) := Set.finite_univ_iff.mp.mt Infinite.not_finite
  rcases (Set.Infinite.nontrivial (.diff (.diff h2 hA) hB)).exists_ne (d x) with ⟨x1, hx1, hx2⟩
  exact ⟨x1, Set.notMem_of_mem_diff (Set.mem_of_mem_diff hx1), ⟨Set.notMem_of_mem_diff hx1, hx2⟩⟩

lemma exists_not_in_domain_range' (z : G) : ∃ w, L (S z) w = x ∧
    w ∉ partial_domain x ∧ w ∉ partial_range x ∧ w ≠ d x := by
  have Iinf : ¬ Set.Finite {y : G' | L (S z) y = x} := L_surjective (S z) x
  have hA : (partial_domain x).toSet.Finite := by
    rw [partial_domain, Set.coe_toFinset]
    exact (partial_domain' x).toFinite
  have hB : (partial_range x).toSet.Finite := by
    rw [partial_range, Set.coe_toFinset]
    exact (partial_range' x).toFinite
  rcases (Set.Infinite.nontrivial (.diff (.diff (.image (fun _ _ _ _ a ↦ Sum.inr_injective a)
    (L_surjective _ _)) hA) hB)).exists_ne (d x) with ⟨ x1, hx1, hx2⟩
  have hx1' := Set.mem_of_mem_diff hx1
  rcases (Set.mem_of_mem_diff hx1') with ⟨w, hw1, hw2⟩
  exact ⟨x1, hw2 ▸ hw1, ⟨Set.notMem_of_mem_diff hx1', ⟨Set.notMem_of_mem_diff hx1, hx2⟩⟩⟩

/-- Given an extension, which is a partial solution with an undefined element of the domain
called `d`, we define a new element `w` that represents the image of `d` under `Lₓ`. -/
noncomputable def w : G := by
  classical
  exact if h : ∃ z, E x z (d x) then (exists_not_in_domain_range' x h.choose).choose
    else (exists_not_in_domain_range x).choose

lemma w_not_in_domain : w x ∉ partial_domain x := by
  by_cases h : ∃ z, E x z (d x) <;> simp only [w, h]
  · exact (exists_not_in_domain_range' x _).choose_spec.2.1
  · exact (exists_not_in_domain_range x).choose_spec.1

lemma w_not_in_range : w x ∉ partial_range x := by
  by_cases h : ∃ z, E x z (d x) <;> simp only [w, h]
  · exact (exists_not_in_domain_range' x _).choose_spec.2.2.1
  · exact (exists_not_in_domain_range x).choose_spec.2.1

lemma w_ne_d : w x ≠ d x := by
  by_cases h : ∃ z, E x z (d x) <;> simp only [w, h]
  · exact (exists_not_in_domain_range' x _).choose_spec.2.2.2
  · exact (exists_not_in_domain_range x).choose_spec.2.2

lemma w_equation (h : ∃ z, E x z (d x)) : L (S h.choose) (w x) = x := by
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
  rintro (hb | _)
  · rintro (hb' | _)
    · exact ok.aux2 hb hb'
    · exact w_equation' x hb
  · rw [next_iff]
    rintro (h | h)
    · have h' := w_not_in_domain x
      simp only [partial_domain, partial_domain', Rel.dom, Set.mem_toFinset, Set.mem_setOf_eq,
        not_exists] at h'
      exact (h' t h).elim
    · exact (w_ne_d x h.1).elim

def next : PartialSolution x :=
  ⟨Next x, next_finite x, next_func x, next_inj x, next_aux1 x, next_aux2 x⟩

end Extension

theorem exists_extension (x : G') (seed : PartialSolution x) : ∃ Lₓ : G → G,
    Lₓ x = S x ∧ ∀ y, (L (S y) <| Lₓ <| Lₓ y) = x := by
  have ⟨c, hc, h1, h2, h3⟩ := exists_greedy_chain (a := seed)
    (task := fun x' ↦ {e | ∃ y, e.1 x' y})
    fun ⟨E, ok⟩ d ↦ by
      if h : ∃ y, E d y then exact ⟨_, le_rfl, h⟩ else
        let E1 : Extension x := { E, ok, d, not_def := fun h' ↦ h ⟨_, h'⟩ }
        exact ⟨E1.next, fun _ _ ↦ (.base ·), _, .new⟩
  choose e he Lₓ hLₓ using h3
  refine ⟨Lₓ, (e x).2.func (e x).2.aux1 (hLₓ x) |>.symm, fun y ↦ ?_⟩
  /- We have a chain of partial solutions (i.e. partial functions `Lₓ : G → G`) that saturates the
  space, which means that if we have a finite number of elements of `G` we can find a single partial
  solution of the chain that captures all the elements, here we state this with `y` and `Lₓ y`. -/
  classical
  let T : Finset G := {y, Lₓ y}
  have ⟨⟨e, he⟩, le⟩ := hc.directed.finset_le (hι := ⟨⟨_, h1⟩⟩) (T.image fun a ↦ ⟨e a, he a⟩)
  have hT := fun a ha ↦ Finset.forall_mem_image.mp le ha _ _ (hLₓ a)
  simp only [Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq, T] at hT
  exact e.2.aux2 hT.1 hT.2

end GreedyAC

open GreedyAC GreedyB

def seed (x : G') : Rel G G := fun a b ↦ a = x ∧ b = S x

theorem seed_ok (x : G') : OK x (seed x) where
  finite := by
    refine (Set.finite_singleton (Sum.inr x, Sum.inl x.1.1)).subset ?_
    simp only [Set.subset_singleton_iff, Prod.forall, Prod.mk.injEq]
    exact fun _ _ a ↦ a
  inj _ _ := by simp_all [seed]
  func h1 h2 := by rw [h1.2, h2.2]
  aux1 := by simp [seed]
  aux2 _ _ := by simp_all [seed]

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
  rintro (a | g) (a' | g')
  · simp_rw [magG_op_def_A, L_extends]
    rw [magG_op_def_A (a' ◇ a'), L_extends, ← A_satisfies_Equation1516]
  · simp_rw [magG_op_def_G, magG_op_def_A]
    rw [L'_self, magG_op_def_A, L_1516 a g']
  · simp_rw [magG_op_def_A]
    rw [L_self, magG_op_def_A]
    simp_rw [magG_op_def_G, L'_1516]
  · simp_rw [magG_op_def_G, L'_self, magG_op_def_A]
    rw [L'_1516]

lemma op_x₀_self : x₀ ◇ x₀ = (1 : A) := by rw [x₀, magG_op_def_G, L'_self, S]

lemma op_1_x₀ : (.inl (1 : A)) ◇ x₀ = (1 : A) := L_x₀

lemma x₀_255_rhs : ((x₀ ◇ x₀) ◇ x₀) ◇ x₀ = (1 : A) := by simp_rw [op_x₀_self, op_1_x₀]

lemma x₀_ne_1 : x₀ ≠ (1 : A) := Sum.inr_ne_inl

end Refutation255

@[equational_result]
theorem _root_.Equation1516_not_implies_Equation1489 :
    ∃ (G : Type) (_ : Magma G), Equation1516 G ∧ ¬ Equation1489 G := by
  let magA : Magma A := { op := fun x y => f (y*x⁻¹) * x  }
  refine ⟨A, magA, fun x y ↦ ?_, ?_⟩
  · repeat rw [magA_op_def]
    simp only [mul_inv_cancel_right, mul_inv_cancel, mul_inv_rev]
    have := f_translation_invariant_1516 (y * x⁻¹)
    apply_fun fun a ↦ a * (f 1) * y at this
    simp only [mul_inv_rev, inv_inv, inv_mul_cancel_right] at this
    repeat rw [mul_assoc] at *
    exact this.symm
  · simp only [not_forall]
    use x₁, 1
    repeat rw [magA_op_def]
    simp only [one_mul, fromList_eval x₁⁻¹ x₃, inv_one, mul_one, fromList_eval (x₃ * x₁) x₄,
      fromList_eval x₁ x₂, fromList_eval (x₄ * x₂⁻¹) x₅]
    decide

@[equational_result]
theorem Finite.Equation1516_implies_Equation255 (G : Type) [Magma G] [Finite G]
    (h : Equation1516 G) : Equation255 G := by
  let S (x : G) := x ◇ x
  let C (x : G) := (S x) ◇ x
  let L (y x : G) := y ◇ x
  have inv_LS (y : G) : (L (S y)).Injective := by
    refine Finite.injective_iff_surjective.mpr fun x ↦ ⟨x ◇ (x ◇ y), ?_⟩
    simp_rw [L, S, ← h]
  have inv_S : S.Surjective := by
    refine Finite.injective_iff_surjective.mp fun x y hxy ↦ ?_
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

@[equational_result]
theorem _root_.Equation1516_not_implies_Equation255 : ∃ (G : Type) (_ : Magma G), Equation1516 G ∧ ¬ Equation255 G := by
  refine ⟨G, magG, G_satisfies_Equation1516, ?_⟩
  unfold Equation255
  push_neg
  exact ⟨x₀, x₀_255_rhs ▸ x₀_ne_1⟩

/--  https://teorth.github.io/equational_theories/blueprint/1516-chapter.html -/
@[equational_result]
conjecture Equation1516_facts : ∃ (G : Type) (_ : Magma G), Facts G [1516] [255]

end Eq1516
