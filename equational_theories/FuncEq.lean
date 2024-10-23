--use DFinSupp since it's computable and reducible unlike Finsupp
import Mathlib.Data.DFinsupp.Basic
import Mathlib.Data.DFinsupp.Notation
import Mathlib.Data.DFinsupp.Lex
import Mathlib.LinearAlgebra.DFinsupp
import Mathlib.LinearAlgebra.FinsuppVectorSpace
import Mathlib.LinearAlgebra.Pi

import Init.Data.Fin.Fold
import Batteries.Data.Vector.Basic
import Batteries.Data.Vector.Lemmas
import Batteries.Data.Fin.Lemmas
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.Group.WithOne.Defs
import Mathlib.LinearAlgebra.Span
import Mathlib.Data.Nat.SuccPred

open Batteries (Vector)

def choose_n_gt {α} [DecidableEq α] [Preorder α] [SuccOrder α] [NoMaxOrder α]
    (a: α) (n: ℕ): {f: Vector α n // (∀ i j: Fin n, i < j → f[i] < f[j]) ∧ ∀ i: Fin n, a < f[i]} :=
  let motive := λ s ↦ {e: Vector α s × α // (a ≤ e.2 ∧ (∀ i: Fin s, e.1[i] ≤ e.2)) ∧ ((∀ i j: Fin s, i < j → e.1[i] < e.1[j]) ∧ ∀ i: Fin s, a < e.1[i])}
  let ⟨⟨as, _⟩, ⟨_, hs⟩⟩: motive n := Nat.recOn n ⟨⟨Vector.empty, a⟩, by simp⟩ (λ n ⟨⟨as, m⟩, ⟨⟨ham, hxm⟩, ⟨hab, hax⟩⟩⟩ ↦
    let m' := Order.succ m
    ⟨⟨as.push m', m'⟩, by
      simp_all
      constructorm* _ ∧ _
      · apply le_trans ham ?_
        apply SuccOrder.le_succ
      · apply Fin.lastCases
        · simp
        · simp only [Fin.coe_castSucc, Fin.is_lt, Vector.getElem_push_lt]
          intro i
          specialize hxm i
          apply le_trans hxm ?_
          apply SuccOrder.le_succ
      · apply Fin.lastCases
        · intro j hnj
          exfalso
          apply Fin.ne_last_of_lt hnj
          rfl
        · intro i
          apply Fin.lastCases
          · intro _
            have := Fin.castSucc_lt_last i
            simp only [Fin.coe_castSucc, Fin.is_lt, Vector.getElem_push_lt, Fin.val_last, Vector.getElem_push_last]
            specialize hxm i
            exact Order.lt_succ_of_le hxm
          · intro j
            intro hij
            specialize hab i j hij
            have := Fin.castSucc_lt_last i
            have := Fin.castSucc_lt_last j
            simp only [Fin.coe_castSucc, Fin.is_lt, Vector.getElem_push_lt, gt_iff_lt]
            exact hab
      · apply Fin.lastCases
        · simp only [Fin.val_last, Vector.getElem_push_last]
          exact Order.lt_succ_of_le ham
        · simp only [Fin.coe_castSucc, Fin.is_lt, Vector.getElem_push_lt]
          exact hax
      ⟩)
  ⟨as, hs⟩

namespace DFinsupp
variable {α} [DecidableEq α] {β} [DecidableEq β] [Zero β]
abbrev graph (f: Π₀ _ : α, β) := f.toFinsupp.graph
lemma apply_eq_toFinsupp_apply {f: Π₀ _ : α, β} {x}: f x = (DFinsupp.toFinsupp f) x := rfl
@[simp]
theorem toFinsupp_sum {ι} {M} [Zero M] {N} [DecidableEq ι] [(m : M) → Decidable (m ≠ 0)] [DecidableEq N] [AddCommMonoid N]
    (f : Π₀ (_ : ι), M) (g : ι → M → N) :
    Finsupp.sum f.toFinsupp g = DFinsupp.sum f g := by rfl

-- the following is copied from mathlib Finsupp
variable {ι : Type*} {R : Type*} {S : Type*} {M : ι → Type*} {N : Type*}

variable [DecidableEq ι]
variable [Semiring R] [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]
variable [AddCommMonoid N] [Module R N]

open Set LinearMap Submodule

@[simp]
theorem ker_lsingle (a : ι) : ker (lsingle (M := M) (R := R) a) = ⊥ := by
  apply ker_eq_bot_of_injective
  simp only [lsingle, LinearMap.coe_mk, AddHom.coe_mk]
  apply single_injective

theorem lsingle_range_le_ker_lapply (s t : Set ι) (h : Disjoint s t) :
    ⨆ a ∈ s, LinearMap.range (lsingle (M := M) (R := R) a) ≤
      ⨅ a ∈ t, ker (lapply (M := M) (R := R) a) := by
  refine iSup_le fun a₁ => iSup_le fun h₁ => range_le_iff_comap.2 ?_
  simp only [(ker_comp _ _).symm, eq_top_iff, SetLike.le_def, mem_ker, comap_iInf, mem_iInf]
  intro b _ a₂ h₂
  have : a₁ ≠ a₂ := fun eq => h.le_bot ⟨h₁, eq.symm ▸ h₂⟩
  exact single_eq_of_ne this

omit [DecidableEq ι] in
theorem iInf_ker_lapply_le_bot : ⨅ a, ker (lapply (M := M) (R := R) a) ≤ ⊥ := by
  simp only [SetLike.le_def, mem_iInf, mem_ker, mem_bot, lapply_apply]
  exact fun a h => DFinsupp.ext h

theorem disjoint_lsingle_lsingle (s t : Set ι) (hs : Disjoint s t) :
    Disjoint (⨆ a ∈ s, LinearMap.range (lsingle (M:= M) (R := R) a))
      (⨆ a ∈ t, LinearMap.range (lsingle (M:= M) (R := R) a)) := by
  -- Porting note: 2 placeholders are added to prevent timeout.
  refine
    (Disjoint.mono
      (lsingle_range_le_ker_lapply s sᶜ ?_)
      (lsingle_range_le_ker_lapply t tᶜ ?_))
      ?_
  · apply disjoint_compl_right
  · apply disjoint_compl_right
  rw [disjoint_iff_inf_le]
  refine le_trans (le_iInf fun i => ?_) iInf_ker_lapply_le_bot
  classical
    by_cases his : i ∈ s
    · by_cases hit : i ∈ t
      · exact (hs.le_bot ⟨his, hit⟩).elim
      exact inf_le_of_right_le (iInf_le_of_le i <| iInf_le _ hit)
    exact inf_le_of_left_le (iInf_le_of_le i <| iInf_le _ his)

variable {R: Type _} {M : ι → Type _} [Ring R] [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]

theorem linearIndependent_single {φ : ι → Type*} {f : ∀ i, φ i → M i}
    (hf : ∀ i, LinearIndependent R (f i)) :
    LinearIndependent R fun ix : Σi, φ i => (DFinsupp.single ix.1 (f ix.1 ix.2)) := by
  apply @linearIndependent_iUnion_finite R _ _ _ _ ι φ fun i x => DFinsupp.single i (f i x)
  · intro i
    have h_disjoint : Disjoint (span R (range (f i))) (ker (lsingle (M := M) (R := R) i)) := by
      rw [ker_lsingle]
      exact disjoint_bot_right
    apply (hf i).map h_disjoint
  · intro i t _ hit
    refine (disjoint_lsingle_lsingle {i} t (Set.disjoint_singleton_left.2 hit)).mono ?_ ?_
    · rw [span_le]
      simp only [iSup_singleton]
      rw [range_coe]
      apply range_comp_subset_range _ (lsingle i)
    · refine iSup₂_mono fun i hi => ?_
      rw [span_le, range_coe]
      apply range_comp_subset_range _ (lsingle i)
end DFinsupp

-- use a simpler definition than the one in Mathlib that quotients the free group
abbrev FreeModule (α: Type _) (R: Type _) [Zero R] := Π₀ _ : α, R

namespace FreeModule
variable {α} [DecidableEq α] {R} [Ring R] [Nontrivial R]

def gen: α ↪ FreeModule α R :=
  ⟨λ x ↦ DFinsupp.single x 1, by
    apply DFinsupp.single_left_injective
    intro _
    exact one_ne_zero⟩

@[simp]
def gen_apply {i j: α}:
    (gen i: FreeModule α R) j = if i = j then 1 else 0 := by
  simp [gen, DFinsupp.single_apply]

def gen_ne_zero (i: α):
    gen i ≠ (0: FreeModule α R) := by
  simp [gen]

variable (α) (R) [NoZeroDivisors R] in
lemma gen_independent: LinearIndependent R (gen: α ↪ FreeModule α R)  := by
  have hl1: α → LinearIndependent R fun _: Unit ↦ (1: R) := by
    intro _
    apply linearIndependent_unique (R := R) (M := R)
    exact one_ne_zero

  let f := λ i: α ↦ (⟨i, ()⟩: Σ_, Unit)
  let hf: Function.Injective f := by
    intro x y h
    injection h

  exact (DFinsupp.linearIndependent_single hl1).comp f hf

variable [∀ x: R, Decidable (x ≠ 0)]

lemma mem_span_gen_support (x: FreeModule α R):
    x ∈ Submodule.span R (gen '' x.support) := by
    rw [← DFinsupp.toFinsupp_support]
    refine (Finsupp.mem_span_image_iff_linearCombination R).mpr ?_
    use x.toFinsupp
    constructor
    · exact Finsupp.mem_supported_support R _
    · simp [Finsupp.linearCombination_apply, gen]
      simp only [← DFinsupp.single_smul]
      simp only [smul_eq_mul, mul_one, DFinsupp.single_zero, implies_true, DFinsupp.sum_single]

lemma subset_span_gens (s: Finset (FreeModule α R)):
    s.toSet ⊆ SetLike.coe (Submodule.span R (gen '' ↑(s.sup (·.support)))) := by
  intro x hxs
  apply Set.mem_of_mem_of_subset (mem_span_gen_support x)
  apply SetLike.coe_mono
  apply Submodule.span_mono
  apply Set.image_mono
  apply Finset.coe_subset.mpr
  apply Finset.le_iff_subset.mp
  apply Finset.le_sup
  exact hxs

variable [NoZeroDivisors R]
variable [Inhabited α] [LinearOrder α]

def max_dependent_gen_idx (s: Finset (FreeModule α R)):
  {i: α // Disjoint (Submodule.span R (gen '' {j: α | i < j})) (Submodule.span R s.toSet)} :=
  let u := s.sup (DFinsupp.support ·)
  let n := u.max.recBotCoe default id
  ⟨n, by
    suffices h: Disjoint (Submodule.span R (gen '' {j: α | n < j})) (Submodule.span R (gen '' u)) by
      apply Disjoint.mono_right ?_ h
      any_goals assumption
      apply Submodule.span_le.mpr
      apply subset_span_gens

    apply (gen_independent α R).disjoint_span_image

    cases hum: u.max
    case bot =>
      rw [Finset.max_eq_bot] at hum
      simp [hum]
    case coe i =>
      apply Set.disjoint_left.mpr
      intro j hnj
      apply Finset.not_mem_of_max_lt_coe
      simp only [Set.mem_setOf_eq, n, hum, WithBot.recBotCoe_coe, id_eq] at hnj
      simpa only [hum, WithBot.coe_lt_coe]
⟩

variable [SuccOrder α] [NoMaxOrder α]

def gen_idx_not_in_finset (s: Finset (FreeModule α R)):
  {i: α // gen i ∉ s} :=
  let ⟨i, hi⟩ := max_dependent_gen_idx s
  ⟨Order.succ i, by
    intro h
    rw [Submodule.disjoint_def] at hi
    specialize hi (gen (Order.succ i))
    suffices h: gen (Order.succ i) = (0: FreeModule α R) by
      revert h
      apply gen_ne_zero (Order.succ i)
    apply hi
    · apply Set.mem_of_subset_of_mem
      · apply Submodule.subset_span
      · simp
    · apply Set.mem_of_subset_of_mem
      · apply Submodule.subset_span
      · exact h⟩

def elem_not_in_finset (s: Finset (FreeModule α R)):
  {x: FreeModule α R // x ∉ s} :=
  let ⟨i, hi⟩ := gen_idx_not_in_finset s
  ⟨gen i, hi⟩

def independent_gen_idxes (n: ℕ) (s: Finset (FreeModule α R)):
  {r: Vector α n // Disjoint (Submodule.span R (gen '' (r.toList.toFinset))) (Submodule.span R s.toSet) ∧ LinearIndependent R (λ i: Fin n ↦ (gen r[i]: FreeModule α R))} :=
  let ⟨a0, ha⟩ := max_dependent_gen_idx s
  let ⟨as, ⟨hd, hax⟩⟩ := choose_n_gt a0 n
  ⟨as, by
    constructor
    · apply Disjoint.mono_left ?_ ha
      apply Submodule.span_mono
      apply Set.image_subset
      intro x
      intro hx
      simp only [Vector.toList, List.coe_toFinset, List.mem_iff_getElem, Array.getElem_toList,
        Array.length_toList, Vector.size_eq, Set.mem_setOf_eq] at hx
      obtain ⟨i, his, hu⟩ := hx
      specialize hax ⟨i, his⟩
      simp only [getElem, Vector.get] at hax
      simpa only [hu, Fin.cast_mk, Array.get_eq_getElem] using hax
    · have gs := gen_independent α R
      apply gs.comp
      apply injective_of_increasing (· < ·) (· < ·)
      intro i j
      exact hd i j
  ⟩

def independent_elems [DecidableEq R] (n: ℕ) (s: Finset (FreeModule α R)):
  {r: Vector (FreeModule α R) n // Disjoint (Submodule.span R r.toList.toFinset) (Submodule.span R s.toSet) ∧ LinearIndependent R (λ i: Fin n ↦ r[i])} :=
  let ⟨is, h⟩ := independent_gen_idxes n s
  ⟨is.map gen, by simpa [Vector.map, Vector.toList] using h⟩

end FreeModule

abbrev FreeAbelianGroup α := FreeModule α ℤ
abbrev FreeAbelianGroup.gen {α} [DecidableEq α]: α ↪ FreeAbelianGroup α := FreeModule.gen

namespace PaceNielsen

-- don't use WithZero because we want the none/0 to be a null (i.e. x + 0 = 0), not a 0 (i.e. x + 0 = x)
local instance {α}: Zero (Option α) where
  zero := none

local instance {α} [Neg α]: Neg (Option α) where
  neg x := x.map (-·)

@[simp]
lemma opt_zero {α}: (0: Option α) = none := rfl

instance {α} [Sub α]: Sub (Option α) where
  sub := Option.map₂ (· - ·)

@[simp]
lemma neg_some {α} {x: α} [Neg α]: -(some x) = some (-x) := rfl

@[simp]
lemma neg_none {α} [Neg α]: -(none: Option α) = none := rfl

@[simp]
lemma sub_none {α} [Sub α] {x: Option α}: (x - none) = none := by
  cases x
  all_goals rfl

@[simp]
lemma sub_some {α} [Sub α] {x y: α}: ((some x) - (some y)) = some (x - y) := rfl

abbrev PartFun (α) := Π₀ _ : α, Option α

abbrev G : Type := FreeAbelianGroup ℕ
abbrev p : G := FreeAbelianGroup.gen 0
abbrev q : G := FreeAbelianGroup.gen 1
abbrev r : G := FreeAbelianGroup.gen 2
abbrev s : G := FreeAbelianGroup.gen 3

notation "∅" => (none : Option G)
notation "O" => (some 0 : Option G)

def f₀ : PartFun G :=
  fun₀
  | 0 => p
  | p => q
  | -q => r
  | q + r => O
  | q + r - p => s
  | p - q - r + s => - q - r

@[simp] def f₀_0: f₀ 0 = p := by rfl
@[simp] def f₀_p: f₀ (p) = q := by rfl
@[simp] def f₀_q: f₀ (-q) = r := by rfl
@[simp] def f₀_qr: f₀ (q + r) = O := by rfl
@[simp] def f₀_rq: f₀ (r + q) = O := by rw [add_comm]; rfl
@[simp] def f₀_qrp: f₀ (q + r - p) = s := by rfl
@[simp] def f₀_pqrs: f₀ (p - q - r + s) = - q - r := by rfl
@[simp] def f₀_spqr: f₀ (s + p - (q + r)) = - q - r := by
  have: s + p - (q + r) = p - q - r + s := by
    abel
  simp [this]

def f₀_eq {x: G}: f₀ x =
    if x = 0 then some p
    else if x = p then some q
    else if x = -q then some r
    else if x = q + r then some 0
    else if x = q + r - p then some s
    else if x = p - q - r + s then some (-q - r)
    else none := by
  repeat'
    split
    try any_goals subst_eqs
    try any_goals simp only [f₀_0, f₀_p, f₀_q, f₀_qr, f₀_qrp, f₀_pqrs, f₀_spqr, neg_some, sub_some]
  simp [f₀, Function.update]
  repeat' split
  any_goals subst_eqs
  any_goals trivial

def ℰ : Set (PartFun G) := fun f =>
  ∀ (a b c : G) (_: f a = b) (_: f b = c),
    ∃ d : G, f (a - c) = d ∧ f (d + c - a) = -a

lemma f₀inℰ : f₀ ∈ ℰ := by
  intro a b c hab hbc
  rw [f₀_eq] at hab
  repeat'
    split at hab
    try any_goals subst_eqs
    try any_goals simp only [f₀_0, f₀_p, f₀_q, f₀_qr, f₀_rq, f₀_qrp, f₀_pqrs, f₀_spqr, neg_some, sub_some, zero_sub, sub_zero, Option.some.injEq, neg_zero, exists_eq_left', neg_add_rev]
    try any_goals ac_rfl

abbrev fup {α} (f: PartFun α): Option α → Option α := λ x: Option α ↦
  match x with
  | (0: Option α) => (0: Option α)
  | Option.some x => f x

@[simp]
lemma fup_zero {α} {f: PartFun α}: fup f none = 0 := rfl

@[simp]
lemma fup_some {α} {f: PartFun α} {x: α}: fup f (some x) = f x := rfl

abbrev feq (f: PartFun G) (h: G) :=
  let f := fup f
  f ((f (h - f (f h))) - (h - f (f h))) = -h

/-
def f_a_some_of_feq {f a} (h: feq f a): {b: G // f a = b} :=
  match ha: f a with
  | none => by
    unfold feq at h
    simp [ha] at h
  | some b =>
    ⟨b, rfl⟩

def f_f_a_some_of_feq {f a} (h: feq f a): {c: G // fup f (f a) = c} :=
  let ⟨b, ha⟩ := f_a_some_of_feq h
  match hb: f b with
  | none => by
    unfold feq at h
    simp [ha, hb] at h
  | some c =>
    ⟨c, by simp [ha, hb]⟩
-/

lemma feq_of_mem_ℰ {f: PartFun G} (h: f ∈ ℰ) {a b c: G} (ha: f a = b) (hb: f b = c): feq f a := by
  unfold ℰ at h
  rw [Set.mem_def] at h
  obtain ⟨d, h1, h2⟩ := h a b c ha hb
  simp [neg_some] at h2
  simp [feq, sub_some, ha, hb, h1, ← h2, sub_sub_eq_add_sub d a c]

lemma f_eq_of_subset {f f': PartFun G} (hs : f.graph ⊆ f'.graph) {a b} (h : f a = some b) : f' a = some b := by
  rw [Finset.subset_iff] at hs
  rw [DFinsupp.apply_eq_toFinsupp_apply]
  apply Finsupp.apply_eq_of_mem_graph
  apply hs
  apply Finsupp.mk_mem_graph_iff.mpr
  constructor
  · exact h
  · simp

def graph_subset_of_update {α β} [DecidableEq α] [Zero β] [DecidableEq β] {f: Π₀ _ : α, β} {a: α} {b: β} (h: f a = 0): f.graph ⊆ (f.update a b).graph := by
  simp_rw [Finset.subset_iff, Finsupp.mem_graph_iff]
  intro ⟨x, y⟩ ⟨h, hy0⟩
  simp [Function.update_apply]
  split
  all_goals simp_all

abbrev Extension (f: PartFun G) (z: G) :=
  {f': PartFun G // f' ∈ ℰ ∧ f.graph ⊆ f'.graph ∧ (fup f' (f' z)).isSome}

def adjoin (f: PartFun G) (a c d: G) :=
  (f.update (a - c) d).update (d + c - a) (-a)

def case1 {f} (hf : f ∈ ℰ) {z : G} {b: G} (hz: f z = b): Extension f z :=
  match hb: f b with
  | some c => -- If b is the first coordinate of some pair in E
    -- then by condition (4), the functional equation already holds for z by taking E′ = E. So
    ⟨f, ⟨hf, by rfl, by simp [hz, hb, fup]⟩⟩
  | none => -- So, for the rest of this case, assume that b is not a first coordinate of any pair.
    -- Since E is finite by (1), b appears as the second coordinate of only finitely many pairs.
    let a := f.support.filter (λ x ↦ f x = b)

    -- Fix a1, . . . , an to be the list of the distinct first coordinates for such pairs
    have LO := DFinsupp.Lex.linearOrder.lift' toLex (λ _ _ h ↦ toLex_inj.mp h)
    let as := a.sort LO.le
    let n := as.length
    let a := λ i: Fin n ↦ as[i]

    -- Let S be the set of indices where there is such a pair, and for each i ∈ S fix b′ᵢ to be
    -- the unique element where (−aᵢ, b′ᵢ) ∈ E. Let T = {i ∈ S : b′ᵢ = 0}.
    let b's := as.map (f ·)
    let hb'sl: b's.length = n := by sorry
    --let b'e := b's.enum
    --let S := b'e.filterMap λ (i, b') ↦ if b'.isSome then some i else none
    --let T := b'e.filterMap λ (i, b') ↦ if b' = 0 then some i else none
    let b' := λ i: Fin n ↦ b's[i]

    -- Now, let c, di (i ∈ [1, n]), and ej (j ∈ S − T ) be a set of independent generators of A that
    -- do not appear anywhere in the support of E. We take
    let cde := FreeAbelianGroup.independent_gen_idxes (2 * n + 1) f.support
    let c := FreeAbelianGroup.gen cde.val[0]
    let d := λ i: Fin n ↦ FreeAbelianGroup.gen cde.val[1 + (i: ℕ)]
    let e := λ i: Fin n ↦ FreeAbelianGroup.gen cde.val[n + 1 + (i: ℕ)]

    -- ∀ (a b c : G) (_: f a = b) (_: f b = c),
    -- ∃ d : G, f (a - c) = d ∧ f (d + c - a) = -a

    -- note aᵢ ≠ 0, assume b is not first coordinate

    -- 1. z ∈ aᵢ => b
    -- 2. -aᵢ => b'ᵢ

    -- c, d, e new independent generators

    -- 3. b => c (to fill to prepare to make feq hold on z)
    -- 4. aᵢ - c => dᵢ   (Lfix for 1->3)
    -- 5. dᵢ + c - aᵢ => -aᵢ   (Rfix for 1->3)

    -- if b'ᵢ ≠ 0:
    --  6. dᵢ + c - aᵢ - b'ᵢ => eᵢ   (Lfix for 5->2)
    --  7. eᵢ + b'ᵢ - (dᵢ + c - aᵢ) => -(dᵢ + c - aᵢ)   (Rfix for 5->2)
    -- else:
    --  8. -c - dᵢ => aᵢ - c - dᵢ    (Rfix for 5->2, Lfix is 5 itself)

    -- 3. 0 => C
    -- 4. -C => D
    -- 5. D + C => 0
    -- 6. D + C => E
    -- 7. E - D - C => -C -D
    -- 8. -C -D => -C - D

    -- 3 requires 4+5 for all ito satisfy ℰ
    -- 5 requires 6+7+8 for same i to satisfy ℰ

    -- 3L = 5R ↔ -aᵢ = b NOPE (b not first coordinate of any pair)
    -- 5L = 6L ↔ b'ᵢ = 0 NOPE (test for b'i = 0)
    -- 8L = 8R ↔ aᵢ = 0 NOPE (start of proof consideration)

    -- for 5->2:
    --  A = dᵢ + c - aᵢ
    --  B = -aᵢ
    --  C = b'ᵢ
    --
    --  if bᵢ ≠ 0:
    --    f (dᵢ + c - aᵢ - bᵢ) = D ∧ f(D + bᵢ + aᵢ - c - dᵢ) = -(dᵢ + c - aᵢ)

    --  if bᵢ = 0:
    --    f (dᵢ + c - aᵢ) = -aᵢ ∧ f(- c - dᵢ) = -(dᵢ + c - aᵢ)

    let f' := f.update b c
    let update_i (i: Fin n) (f: PartFun G): PartFun G :=
      let f := adjoin f (a i) c (d i)
      match b' i with
      | some b'i =>
        if b'i != 0 then
          adjoin f ((d i) + c - (a i)) b'i (e i)
        else -- (-a)
          f.update (-c - (d i))  ((a i) - c - (d i))
      | none => f

    let f': PartFun G := Fin.induction f' update_i n

    ⟨f', by
      constructorm* _ ∧ _
      · sorry
      · sorry
      · sorry
    ⟩

def case2b {f} (hf : f ∈ ℰ) {z : G}
    (ha : f z = none) (hxfz : ∀ x : G, f x ≠ some z): Extension f z :=
  -- where z′ is any element of A not appearing in the support of E [correction: and distinct from a]
  have ⟨z'i, hz'⟩ := FreeAbelianGroup.gen_idx_not_in_finset (f.support ∪ {z})
  have ⟨hz's, hz'a⟩ := Finset.not_mem_union.mp hz'
  have hz'a := Finset.not_mem_singleton.mp hz'a
  let z' := FreeAbelianGroup.gen z'i

  -- by adding a new pair (z, z′),
  let f': PartFun G := f.update z z'

  -- [and checking that indeed the equation still holds and that f' z = z']
  have hs': f.graph ⊆ f'.graph := graph_subset_of_update ha
  have hf': f' ∈ ℰ := by
    intro a' b' c' ha' hb'
    rw [DFinsupp.coe_update, Function.update_apply] at ha' hb'
    repeat' split at *
    any_goals injections
    any_goals subst_eqs
    any_goals
      exfalso
      simp_all
      done
    · have ⟨d, h1, h2⟩  := hf a' b' c' ha' hb'
      use d
      exact ⟨f_eq_of_subset hs' h1, f_eq_of_subset hs' h2⟩
  have ha': f' z = z' := by
    rw [DFinsupp.coe_update, Function.update_apply]
    simp

  -- we again reduce to Case 1
  let ⟨f'', hf'', hs'', he''⟩ := case1 hf' ha'
  ⟨f'', ⟨hf'', hs'.trans hs'', he''⟩⟩

def extend_f {f} (hf : f ∈ ℰ) (z : G): Extension f z :=
  match hz: f z with
  | some b =>
    case1 hf hz
  | none => -- Case 2: Assume that z is not the first coordinate of some pair in E
    have LO: LinearOrder G := DFinsupp.Lex.linearOrder.lift' toLex (λ _ _ h ↦ toLex_inj.mp h)
    let z' := (f.support.filter (λ o ↦ f o = z)).min
    match hz's: z' with
    | some z' => -- If z appears as the second coordinate of some pair in E, say (z′, z)
      have ⟨_, hz'⟩ := Finset.mem_filter.mp <| Finset.mem_of_min hz's

      -- by applying Case 1 to z, we can extend E to a new set F so that the functional equation holds for z′
      let ⟨f', hf', hs', he'⟩ := case1 hf hz'

      -- Now, z appears as a first coordinate of a pair in F
      let b' := Option.get _ he'
      let hz'u := f_eq_of_subset hs' hz'
      have h'z: f' z = some b' := by simp [b', hz'u, fup_some]

      -- so using Case 1 again we can extend F so that the functional equation holds for z
      let ⟨f'', hf'', hs'', he''⟩ := case1 hf' h'z
      ⟨f'', ⟨hf'', hs'.trans hs'', he''⟩⟩
    | ⊤ => -- If z doesn’t appear as either a first or a second coordinate
      have hfxz: ∀ x, f x ≠ z := by
        intro x
        if hxs: x ∈ f.support then
          apply (Finset.filter_eq_empty_iff.mp <| Finset.min_eq_top.mp hz's) hxs
        else
          rw [DFinsupp.not_mem_support_iff] at hxs
          rw [hxs]
          intro h
          injection h

      -- [continues in case2b]
      case2b hf hz hfxz

end PaceNielsen
