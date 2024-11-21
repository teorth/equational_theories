import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.Data.Finmap
import Mathlib.Data.Finset.Max
import Mathlib.Data.List.Basic
import Mathlib.Data.Finset.Order

import equational_theories.EquationalResult
import equational_theories.Equations.All
import equational_theories.ForMathlib.GroupTheory.FreeGroup.ReducedWords
import equational_theories.Mathlib.Order.Greedy


--import Mathlib.Tactic.Group --This breaks some instance, I haven't understood why exactly

namespace Eq1516

open FreeGroup

private abbrev A := FreeGroup Nat

instance : Countable A := by
  apply Function.Surjective.countable (Quot.mk_surjective)


def maxIndex' : (List (Nat × Bool)) → Nat
| [] => 0
| ((x,_) :: l) => max x $ maxIndex' l

def maxIndex (a : A) : Nat := (maxIndex' $ FreeGroup.toWord a)

def freshIndex (old : Finset A) : Nat := Nat.succ $ (Finset.image maxIndex old).max.unbot' 0

def freshGenerator (old : Finset A) := FreeGroup.of (freshIndex old)

theorem maxIndex'_sublist (L₁ L₂ : List (Nat × Bool)) (H : L₁.Sublist L₂) : maxIndex' L₁ ≤ maxIndex' L₂ := by
induction H with
| slnil => rfl
| cons a _ _ => simp only [maxIndex', le_max_iff] ; tauto
| cons₂ a _ _ => simp only [maxIndex', le_max_iff] ; omega

theorem maxIndex_mk_le (L : List (Nat × Bool)) : maxIndex (FreeGroup.mk L) ≤ maxIndex' L :=
  maxIndex'_sublist _ _ (FreeGroup.reduce.red (L := L)).sublist

theorem maxIndex'_append (L₁ L₂ : List (Nat × Bool)) : maxIndex' (L₁ ++ L₂) = max (maxIndex' L₁) (maxIndex' L₂) := by
induction L₁ with
| nil => simp [maxIndex']
| cons head tail ih => simp [maxIndex',ih] ; omega

theorem maxIndex_mul_le (x y : A) : maxIndex (x * y) ≤ max (maxIndex x) (maxIndex y) := by
  calc
    maxIndex (x * y) = maxIndex (FreeGroup.mk (x.toWord ++ y.toWord)) := by rw [← FreeGroup.mul_mk, FreeGroup.mk_toWord, FreeGroup.mk_toWord]
    _ ≤ maxIndex' (x.toWord ++ y.toWord) := maxIndex_mk_le _
    _ = max (maxIndex x) (maxIndex y) := maxIndex'_append _ _

theorem maxIndex'_invRev (L : List (Nat × Bool)) : maxIndex' (FreeGroup.invRev L) = maxIndex' L := by
induction L with
| nil => rfl
| cons head tail ih =>
  unfold FreeGroup.invRev at *
  simp [maxIndex',maxIndex'_append,ih,max_comm]

theorem maxIndex_inv (x : A) : maxIndex x⁻¹ = maxIndex x := by
unfold maxIndex
rw [FreeGroup.toWord_inv]
apply maxIndex'_invRev

theorem maxIndex_subgroup_lt_freshIndex (old : Finset A) (g : A) : g ∈ Subgroup.closure old →
  maxIndex g < freshIndex old := set_option pp.all true in by
  apply Subgroup.closure_induction
  · simp only [Finset.mem_coe]
    unfold freshIndex
    intro x h
    have : maxIndex x ≤ (Finset.image maxIndex old).max.unbot' 0 := by
      rw [← Finset.coe_max']
      simp only [WithBot.unbot'_coe]
      apply Finset.le_max'
      simp only [Finset.mem_image]
      use x, h
    omega
  · unfold maxIndex
    simp [maxIndex']
    unfold freshIndex
    omega
  · intro x y _ _ ineqx ineqy
    have this := maxIndex_mul_le x y
    omega
  · intro x _ ineqx
    have this := maxIndex_inv x
    omega

theorem maxIndex_fresh (old : Finset A) : maxIndex (freshGenerator old) = freshIndex old := by
unfold freshGenerator
simp [maxIndex,maxIndex']

theorem freshGenerator_not_in_span (old : Finset A) : freshGenerator old ∉ Subgroup.closure old := by
intro contra
have this := maxIndex_subgroup_lt_freshIndex _ _ contra
have that := maxIndex_fresh old
omega

theorem fresh_ineq (old : Finset A) (x y : A) (x_mem : x ∈ Subgroup.closure old) (y_mem : y ∈ Subgroup.closure old) (eq : x = freshGenerator old * y)
: False := by
have eq' : x * y⁻¹ = freshGenerator old := by
  rw [eq]
  simp only [mul_inv_cancel_right]
apply freshGenerator_not_in_span
rw [← eq']
exact Subgroup.mul_mem _ x_mem (Subgroup.inv_mem _ y_mem)

theorem fresh_ineq' (old : Finset A) (x y : A) (x_mem :  x ∈ Subgroup.closure old) (y_mem : y ∈ Subgroup.closure old)
(eq : x * (freshGenerator old)⁻¹ =  y) : False := by
have eq' : y⁻¹ * x = freshGenerator old := by
  rw [← eq]
  simp only [mul_inv_rev, inv_inv, inv_mul_cancel_right]
apply freshGenerator_not_in_span
rw [← eq']
exact Subgroup.mul_mem _ (Subgroup.inv_mem _ y_mem) x_mem

theorem head_maxIndex (x : A) (m : Nat) (f : Bool) : (m,f) ∈ (FreeGroup.toWord x).head? → m ≤ maxIndex x := by
unfold maxIndex
cases FreeGroup.toWord x
· tauto
· intro h
  injection h with eq
  rw [eq]
  simp only [maxIndex']
  omega


@[simp]
theorem freshGenerator_toWord (old : Finset A) : FreeGroup.toWord (freshGenerator old) = [(freshIndex old, true)] := rfl

@[simp]
theorem freshGenerator_inv_toWord (old : Finset A) : FreeGroup.toWord (freshGenerator old)⁻¹ = [(freshIndex old, false)] := rfl


-- TODO: It might be better to go via CoprodI (or now with the reduced lemmas)
theorem fresh_old_no_cancellation (old : Finset A) (x : A) : x ∈ Subgroup.closure old →
  FreeGroup.toWord (freshGenerator old * x) = FreeGroup.toWord (freshGenerator old) ++ FreeGroup.toWord x := by
  intro x_mem
  rw [toWord_mul]
  simp only [freshGenerator_toWord, List.singleton_append, FreeGroup.reduce.cons, Bool.true_eq,
    Bool.not_eq_eq_eq_not, Bool.not_true, FreeGroup.reduce_toWord]
  cases h : FreeGroup.toWord x
  case nil => rfl
  case cons head tail =>
    simp only [ite_eq_right_iff, and_imp]
    intro eq1 eq2
    exfalso
    have ineq1 := maxIndex_subgroup_lt_freshIndex old x x_mem
    have ineq2 : freshIndex old ≤ maxIndex x := by
      apply head_maxIndex
      rw [h, eq1]
      trivial
    omega

theorem fresh_old_inv_no_cancellation (old : Finset A) (x : A) : x ∈ Subgroup.closure old →
  FreeGroup.toWord (x * (freshGenerator old)⁻¹) = FreeGroup.toWord x ++ (FreeGroup.toWord (freshGenerator old)⁻¹) := by
  intro x_mem
  have eq : x * (freshGenerator old)⁻¹ = ((freshGenerator old) * x⁻¹)⁻¹ := by simp
  rw [eq, FreeGroup.toWord_inv, fresh_old_no_cancellation old _ (Subgroup.inv_mem _ x_mem),
  invRev_append, ← FreeGroup.toWord_inv]
  simp [FreeGroup.invRev]

theorem fresh_ineq'' (old : Finset A) (x y : A) (x_mem : x ∈ Subgroup.closure old) (y_mem : y ∈ Subgroup.closure old)
(eq : x * (freshGenerator old)⁻¹ = (freshGenerator old) * y) : False := by
apply_fun FreeGroup.toWord at eq
revert eq
rw [fresh_old_no_cancellation _ _ y_mem]
rw [fresh_old_inv_no_cancellation _ _ x_mem]
cases h : FreeGroup.toWord x with
| nil => simp
| cons head tail =>
  simp only [freshGenerator_inv_toWord, List.cons_append, freshGenerator_toWord,
  List.singleton_append, ne_eq, List.cons.injEq, not_and]
  intro eq'
  -- TODO: proof here very similar to fresh_old_no_cancellation
  exfalso
  have ineq1 := maxIndex_subgroup_lt_freshIndex old x x_mem
  have ineq2 : freshIndex old ≤ maxIndex x := by
    apply head_maxIndex
    rw [h, eq'.1]
    trivial
  omega

theorem fresh_ineq''' (old : Finset A) (x y : A) (x_mem : x ∈ Subgroup.closure old) (y_mem : y ∈ Subgroup.closure old) (eq : x = y * freshGenerator old)
: False := by
have eq' : y⁻¹ * x = freshGenerator old := by
  rw [eq]
  simp
apply freshGenerator_not_in_span
rw [← eq']
exact Subgroup.mul_mem _ (Subgroup.inv_mem _ y_mem) x_mem

private abbrev x : Nat -> A := FreeGroup.of
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



def helper {α β γ} (g : α -> β) (f : ∀ b : α, γ (g b)) (h_g : Function.Injective g) (s : Finset α)
: Finmap γ where
  entries := Multiset.map (fun a => ⟨g a, f a⟩) s.1
  nodupKeys := by
    rw [← Multiset.nodup_keys]
    unfold Multiset.keys
    simp only [Multiset.map_map, Function.comp_apply]
    rw [Multiset.nodup_map_iff_of_injective]
    exact s.2
    exact h_g

theorem helper_mem {α β} {γ : β -> Type} [DecidableEq β] (g : α -> β) (f : ∀ b : α, γ (g b))
(h_g : Function.Injective g) (s : Finset α) (b : β) (c : γ b) :
c ∈ Finmap.lookup b (helper g f h_g s) ↔ ∃ a ∈ s, g a = b ∧ HEq (f a) c := by
  unfold helper
  rw [Finmap.mem_lookup_iff]
  simp


def helper' {α β γ} (g : α -> β) (f : ∀ b : α, γ (g b)) (s : Finset α) (d : ∀ x ∈ s, ∀ y ∈ s, g x = g y → x = y)
: Finmap γ where
  entries := Multiset.map (fun a => ⟨g a, f a⟩) s.1
  nodupKeys := by
    rw [← Multiset.nodup_keys]
    unfold Multiset.keys
    simp only [Multiset.map_map, Function.comp_apply]
    rw [Multiset.nodup_map_iff_of_inj_on]
    exact s.2
    exact d

theorem helper'_mem {α β} {γ : β -> Type} [DecidableEq β] (g : α -> β) (f : ∀ b : α, γ (g b))
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

def c := freshGenerator t.old

theorem c_not_old_subgroup : t.c ∉ Subgroup.closure t.old := by
  apply freshGenerator_not_in_span

theorem c_not_old : t.c ∉ t.old := by
  intro h
  apply t.c_not_old_subgroup
  apply Subgroup.subset_closure
  simp [h]

def e0 : TE := Finmap.singleton t.b t.c

def e1 : TE := helper (fun a' => t.c * a'⁻¹) (fun a' => a'⁻¹) (by intro x y ; simp) t.preimages_of_b

def e2 : TE := helper' (fun a' => (t.ps.E ⬝ (a'⁻¹)).iget * a' * t.c⁻¹) (fun a' => a' *  t.c⁻¹) t.s (by
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

def newE : TE := t.ps.E ∪ t.e0 ∪ t.e1 ∪ t.e2

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
    apply freshGenerator_not_in_span (old := t.old)
    triv_subgroup
  · tauto
  · exfalso
    rcases e1 with ⟨a', e_a'_b, eq, eq'⟩
    apply_fun Inv.inv at eq'
    rw [inv_inv] at eq'
    rw [eq'] at e_a'_b
    apply freshGenerator_not_in_span (old := t.old)
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
      apply freshGenerator_not_in_span (old := t.old)
      unfold c at e0
      rw [← e0.2 ]
      apply Subgroup.subset_closure
      simp [dom_old' _ _ _ old']
    · exfalso
      apply freshGenerator_not_in_span (old := t.old)
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
  apply freshGenerator_not_in_span
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
    apply freshGenerator_not_in_span (old := t.old)
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
      apply freshGenerator_not_in_span (old := t.old)
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

def extension : PartialSolution := by
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

def newE2 := t.ps.E ∪ (Finmap.singleton t.c (t.b*t.c))

theorem old_ne_c (x : A) : x ∈ t.old → x ≠ t.c := by
  intro mem h
  rw [h] at mem
  apply freshGenerator_not_in_span (old := t.old)
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
    apply freshGenerator_not_in_span (old := t.old)
    unfold c at new'
    rw [← new'.1]
    simp only [inv_mem_iff]
    triv_subgroup
  · exfalso
    apply freshGenerator_not_in_span (old := t.old)
    unfold c at new
    rw [← new.1]
    triv_subgroup
  · exfalso
    have : t.c * 1 = 1 * (t.c)⁻¹ := by nth_rw 1 [← new.1] ; rw [← new'.1] ; simp
    apply fresh_ineq'' (eq:= this.symm) <;> apply Subgroup.one_mem

def extension2 [b_ne_1 : Fact (t.b ≠ 1)] : PartialSolution where
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
        apply freshGenerator_not_in_span (old := t.old)
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

theorem completion (ps : PartialSolution) : ∃ (f : A → A), translation_invariant_1516 f ∧ (∀ x y, y ∈ ps.E ⬝ x -> f x = y)
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


@[equational_result]
theorem _root_.Equation1516_not_implies_Equation1489 : ∃ (G : Type) (_ : Magma G), Equation1516 G ∧ ¬ Equation1489 G := by
  let magA : Magma A := { op := fun x y => f (y*x⁻¹) * x  }
  use A, magA
  constructor
  · unfold Equation1516
    intro x y
    repeat rw [magA_op_def]
    simp only [mul_inv_cancel_right, mul_inv_cancel, mul_inv_rev]
    have := f_translation_invariant_1516 (y*x⁻¹)
    apply_fun fun a => a * (f 1) * y at this
    simp only [mul_inv_rev, inv_inv, inv_mul_cancel_right] at this
    repeat rw [mul_assoc] at *
    exact this.symm
  · unfold Equation1489
    simp only [not_forall]
    exists x₁, 1
    repeat rw [magA_op_def]
    simp only [one_mul, fromList_eval x₁⁻¹ x₃, inv_one, mul_one, fromList_eval (x₃ * x₁) x₄,
      fromList_eval x₁ x₂, fromList_eval (x₄ * x₂⁻¹) x₅]
    decide



end Eq1516
