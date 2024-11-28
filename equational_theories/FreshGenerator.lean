import equational_theories.ForMathlib.GroupTheory.FreeGroup.ReducedWords


/-! One technique for constructing magmas that serve as counterexamples for implications between laws
are [translation-invariant magmas](https://teorth.github.io/equational_theories/blueprint/infinite-magma-constructions-chapter.html#a0000000032)

One convenient carrier such magmas is the free group on countably many generators, e.g.,
`FreeGroup Nat`. This is particularly the case for "greedy" constructions.

This file develops the notion of a "fresh" generator given a finite subset of a `FreeGroup α`
with countable infinite α and shows basic lemmas about fresh generators.
-/

namespace FreshGenerator

open FreeGroup

universe u
variable {α : Type u} [DecidableEq α] [Infinite α]

instance [Countable α] : Countable (FreeGroup α) := by
  apply Function.Surjective.countable (Quot.mk_surjective)

instance [Nonempty α] : Infinite (FreeGroup α) :=
  let a := Nonempty.some (by assumption)
  Infinite.of_injective (FreeGroup.of a ^ ·) <| by
    simp [FreeGroup.norm_of_pow, infinite_order]


def generatorNames' : List (α × Bool) → Finset α
  | [] => ∅
  | ((x,_) :: l) => {x} ∪ generatorNames' l

def generatorNames (x : FreeGroup α) : Finset α := generatorNames' $ FreeGroup.toWord x

theorem existsFreshGeneratorName (A : Finset (FreeGroup α)) :
    ∃ a, a ∉ A.biUnion generatorNames := by apply Finset.exists_not_mem

noncomputable def freshGeneratorName (A : Finset (FreeGroup α)) : α :=
  (existsFreshGeneratorName A).choose

noncomputable def freshGenerator (A : Finset (FreeGroup α)) : FreeGroup α :=
  FreeGroup.of (freshGeneratorName A)

omit [Infinite α] in
theorem generatorNames'_sublist (L₁ L₂ : List (α × Bool)) (hL : L₁.Sublist L₂) :
    generatorNames' L₁ ⊆ generatorNames' L₂ := by
  induction hL with
  | slnil => rfl
  | cons a _ ih => simp [generatorNames', subset_trans ih]
  | cons₂ a _ ih => simp [generatorNames', Finset.union_subset_union _ ih]

omit [Infinite α] in
theorem generatorNames_mk_le (L : List (α × Bool)) : generatorNames (FreeGroup.mk L) ⊆ generatorNames' L :=
  generatorNames'_sublist _ _ FreeGroup.reduce.red.sublist

omit [Infinite α] in
theorem generatorNames'_append (L₁ L₂ : List (α × Bool)) :
    generatorNames' (L₁ ++ L₂) = max (generatorNames' L₁) (generatorNames' L₂) := by
  induction L₁ with
  | nil => simp [generatorNames']
  | cons _ _ ih => simp [generatorNames', List.append_eq, ih]

omit [Infinite α] in
theorem generatorNames_mul_le (x y : FreeGroup α) : generatorNames (x * y) ⊆ max (generatorNames x) (generatorNames y) := by
  calc
    generatorNames (x * y) = generatorNames (FreeGroup.mk (x.toWord ++ y.toWord)) := by rw [← FreeGroup.mul_mk, FreeGroup.mk_toWord, FreeGroup.mk_toWord]
    _ ⊆ generatorNames' (x.toWord ++ y.toWord) := generatorNames_mk_le _
    _ = max (generatorNames x) (generatorNames y) := generatorNames'_append _ _

omit [Infinite α] in
theorem generatorNames'_invRev (L : List (α × Bool)) : generatorNames' (FreeGroup.invRev L) = generatorNames' L := by
  induction L with
  | nil => rfl
  | cons _ _ ih =>
    unfold FreeGroup.invRev at *
    simp [generatorNames', generatorNames'_append, ih, max_comm, FreeGroup.invRev, Finset.union_comm]

omit [Infinite α] in
theorem generatorNames_inv (x : FreeGroup α) : generatorNames x⁻¹ = generatorNames x := by
  unfold generatorNames
  rw [FreeGroup.toWord_inv]
  apply generatorNames'_invRev

theorem freshGeneratorName_not_in_generatorNames {S : Finset (FreeGroup α)} {g : FreeGroup α} (hgS : g ∈ S) :
    freshGeneratorName S ∉ generatorNames g := fun hc => by
  apply (existsFreshGeneratorName S).choose_spec
  simp [Finset.mem_biUnion]
  simp [freshGeneratorName] at hc
  use g

theorem freshGeneratorName_not_in_closure_generatorNames (S : Finset (FreeGroup α)) (g : FreeGroup α) :
    g ∈ Subgroup.closure S → freshGeneratorName S ∉ generatorNames g := by
  apply Subgroup.closure_induction
  · simp only [Finset.mem_coe]
    apply freshGeneratorName_not_in_generatorNames
  · unfold generatorNames
    simp [generatorNames']
  · intro x y _ _ _ _
    have := generatorNames_mul_le x y
    apply mt (this ·)
    simp_all
  · intro x _ ineqx
    rw [generatorNames_inv x]
    assumption

theorem generatorNames_fresh (S : Finset (FreeGroup α)) : generatorNames (freshGenerator S) = {freshGeneratorName S} := by
  simp [freshGenerator, generatorNames, generatorNames']

theorem freshGenerator_not_in_span (S : Finset (FreeGroup α)) :
    freshGenerator S ∉ Subgroup.closure S := by
  intro contra
  have := freshGeneratorName_not_in_closure_generatorNames _ _ contra
  have := generatorNames_fresh S
  tauto

omit [Infinite α] in
theorem head_generatorNames (x : FreeGroup α) (m : α) (f : Bool) :
    (m,f) ∈ (FreeGroup.toWord x).head? → m ∈ generatorNames x := by
  unfold generatorNames
  cases FreeGroup.toWord x
  · tauto
  · intro hmf
    injection hmf with hh
    rw [hh]
    simp [generatorNames']


@[simp]
theorem freshGenerator_toWord (S : Finset (FreeGroup α)) :
    FreeGroup.toWord (freshGenerator S) = [(freshGeneratorName S, true)] :=
  rfl

@[simp]
theorem freshGenerator_inv_toWord (S : Finset (FreeGroup α)) :
    FreeGroup.toWord (freshGenerator S)⁻¹ = [(freshGeneratorName S, false)] :=
  rfl


-- TODO: It might be better to go via CoprodI (or now with the reduced lemmas)
theorem fresh_old_no_cancellation {S : Finset (FreeGroup α)} {x : FreeGroup α} (hx : x ∈ Subgroup.closure S) :
    FreeGroup.toWord (freshGenerator S * x) =
    FreeGroup.toWord (freshGenerator S) ++ FreeGroup.toWord x := by
  rw [toWord_mul]
  simp only [freshGenerator_toWord, List.singleton_append, FreeGroup.reduce.cons, Bool.true_eq,
    Bool.not_eq_eq_eq_not, Bool.not_true, FreeGroup.reduce_toWord]
  cases hx' : FreeGroup.toWord x
  case nil => rfl
  case cons head tail =>
    simp only [ite_eq_right_iff, and_imp]
    intro eq1 eq2
    exfalso
    have ineq1 := freshGeneratorName_not_in_closure_generatorNames S x hx
    refine ineq1 (head_generatorNames x (freshGeneratorName S) false ?_)
    simp [hx', eq1, ←eq2]

theorem fresh_old_inv_no_cancellation {S : Finset (FreeGroup α)} {x : FreeGroup α} (hx : x ∈ Subgroup.closure S) :
    FreeGroup.toWord (x * (freshGenerator S)⁻¹) =
    FreeGroup.toWord x ++ (FreeGroup.toWord (freshGenerator S)⁻¹) := by
  have hxS : x * (freshGenerator S)⁻¹ = ((freshGenerator S) * x⁻¹)⁻¹ := by simp
  rw [hxS, FreeGroup.toWord_inv, fresh_old_no_cancellation (Subgroup.inv_mem _ hx),
  invRev_append, ← FreeGroup.toWord_inv]
  simp [FreeGroup.invRev]

theorem fresh_ineq (S : Finset (FreeGroup α)) (x y : FreeGroup α) (x_mem : x ∈ Subgroup.closure S) (y_mem : y ∈ Subgroup.closure S) (eq : x = freshGenerator S * y)
    : False := by
  have eq' : x * y⁻¹ = freshGenerator S := by
    rw [eq]
    simp only [mul_inv_cancel_right]
  apply freshGenerator_not_in_span (α := α)
  rw [← eq']
  exact Subgroup.mul_mem _ x_mem (Subgroup.inv_mem _ y_mem)

theorem fresh_ineq' (S : Finset (FreeGroup α)) (x y : FreeGroup α) (x_mem :  x ∈ Subgroup.closure S) (y_mem : y ∈ Subgroup.closure S)
    (eq : x * (freshGenerator S)⁻¹ =  y) : False := by
  have eq' : y⁻¹ * x = freshGenerator S := by
    rw [← eq]
    simp only [mul_inv_rev, inv_inv, inv_mul_cancel_right]
  apply freshGenerator_not_in_span (α := α)
  rw [← eq']
  exact Subgroup.mul_mem _ (Subgroup.inv_mem _ y_mem) x_mem


theorem fresh_ineq'' (S : Finset (FreeGroup α)) (x y : FreeGroup α) (x_mem : x ∈ Subgroup.closure S) (y_mem : y ∈ Subgroup.closure S)
    (eq : x * (freshGenerator S)⁻¹ = (freshGenerator S) * y) : False := by
  apply_fun FreeGroup.toWord at eq
  revert eq
  rw [fresh_old_no_cancellation y_mem]
  rw [fresh_old_inv_no_cancellation x_mem]
  cases h : FreeGroup.toWord x with
  | nil => simp [invRev]
  | cons head tail =>
    simp only [freshGenerator_inv_toWord, List.cons_append, freshGenerator_toWord,
    List.singleton_append, ne_eq, List.cons.injEq, not_and]
    intro eq'
    -- TODO: proof here very similar to fresh_old_no_cancellation
    exfalso
    have ineq1 := freshGeneratorName_not_in_closure_generatorNames S x x_mem
    refine ineq1 (head_generatorNames x (freshGeneratorName S) true ?_)
    simp [h, eq']

theorem fresh_ineq''' (S : Finset (FreeGroup α)) (x y : FreeGroup α) (x_mem : x ∈ Subgroup.closure S) (y_mem : y ∈ Subgroup.closure S) (eq : x = y * freshGenerator S)
    : False := by
  have eq' : y⁻¹ * x = freshGenerator S := by
    rw [eq]
    simp
  apply freshGenerator_not_in_span (α := α)
  rw [← eq']
  exact Subgroup.mul_mem _ (Subgroup.inv_mem _ y_mem) x_mem

/- We define a group homomorphism on the free group that trivializes all generators in a given set.
This should be a convenient tool to proof inequalities involving the fresh generator that also hold
in the abelianization. -/

def dropGenerators (S : Finset α) : FreeGroup α →* FreeGroup α := lift (fun i => if i ∈ S then 1 else of i)

omit [Infinite α] in
theorem dropGenerators_generatorNames' (S : Finset α) (a : List (α × Bool)) :
    generatorNames' a ⊆ S → dropGenerators S (mk a) = 1 := by
  induction a
  case nil => tauto
  case cons head _ ih =>
    rw [← List.singleton_append]
    intro hn
    simp only [generatorNames', List.singleton_append, sup_le_iff] at hn
    rw [← mul_mk, MonoidHom.map_mul, ih]
    · suffices head.1 ∈ S by simp [dropGenerators, this]
      simp [generatorNames'] at hn
      exact Finset.singleton_subset_iff.mp (Finset.union_subset_left hn)
    · apply subset_trans _ hn; simp

omit [Infinite α] in
theorem dropGenerators_generatorNames (S : Finset α) (a : FreeGroup α) : generatorNames a ⊆ S → dropGenerators S a = 1 := by
  nth_rw 2 [← mk_toWord (x := a)]
  apply dropGenerators_generatorNames'

def forgetOld (S : Finset (FreeGroup α)) : FreeGroup α →* FreeGroup α := dropGenerators (S.biUnion generatorNames)

@[simp]
theorem forgetOld_fresh {S : Finset (FreeGroup α)} : forgetOld S (freshGenerator S) = freshGenerator S := by
  simp [forgetOld, freshGenerator, dropGenerators]
  apply freshGeneratorName_not_in_generatorNames

omit [Infinite α] in
@[simp]
theorem forgetOld_old {S : Finset (FreeGroup α)} {x : FreeGroup α} (hxS : x ∈ S) : forgetOld S x = 1 := by
  apply dropGenerators_generatorNames
  exact Finset.subset_biUnion_of_mem _ hxS

end FreshGenerator
