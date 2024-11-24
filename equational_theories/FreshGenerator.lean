import equational_theories.ForMathlib.GroupTheory.FreeGroup.ReducedWords


/-! One technique for constructing magmas that serve as counterexamples for implications between laws
are [translation-invariant magmas](https://teorth.github.io/equational_theories/blueprint/infinite-magma-constructions-chapter.html#a0000000032)

One convenient carrier such magmas is the free group on countably many generators, i.e.,
`FreeGroup Nat`. This is particularly the case for "greedy" constructions.

This file develops the notion of a "fresh" generator given a finite subset of `FreeGroup Nat`
and shows basic lemmas about fresh generators.
-/

namespace FreshGenerator

open FreeGroup

private abbrev A := FreeGroup Nat

instance : Countable A := by
  apply Function.Surjective.countable (Quot.mk_surjective)


def maxIndex' : (List (ℕ × Bool)) → Nat
| [] => 0
| ((x,_) :: l) => max x $ maxIndex' l

def maxIndex (a : A) : ℕ := (maxIndex' $ FreeGroup.toWord a)

def freshIndex (S : Finset A) : ℕ := Nat.succ $ (Finset.image maxIndex S).max.unbot' 0

def freshGenerator (S : Finset A) := FreeGroup.of (freshIndex S)

theorem maxIndex'_sublist (L₁ L₂ : List (ℕ × Bool)) (hL : L₁.Sublist L₂) :
    maxIndex' L₁ ≤ maxIndex' L₂ := by
  induction hL with
  | slnil => rfl
  | cons a _ _ => simp only [maxIndex', le_max_iff] ; tauto
  | cons₂ a _ _ => simp only [maxIndex', le_max_iff] ; omega

theorem maxIndex_mk_le (L : List (ℕ × Bool)) : maxIndex (FreeGroup.mk L) ≤ maxIndex' L :=
  maxIndex'_sublist _ _ FreeGroup.reduce.red.sublist

theorem maxIndex'_append (L₁ L₂ : List (ℕ × Bool)) :
    maxIndex' (L₁ ++ L₂) = max (maxIndex' L₁) (maxIndex' L₂) := by
  induction L₁ with
  | nil => simp [maxIndex']
  | cons _ _ ih => simp only [maxIndex', List.append_eq, ih] ; omega

theorem maxIndex_mul_le (x y : A) : maxIndex (x * y) ≤ max (maxIndex x) (maxIndex y) := by
  calc
    maxIndex (x * y) = maxIndex (FreeGroup.mk (x.toWord ++ y.toWord)) := by rw [← FreeGroup.mul_mk, FreeGroup.mk_toWord, FreeGroup.mk_toWord]
    _ ≤ maxIndex' (x.toWord ++ y.toWord) := maxIndex_mk_le _
    _ = max (maxIndex x) (maxIndex y) := maxIndex'_append _ _

theorem maxIndex'_invRev (L : List (ℕ × Bool)) : maxIndex' (FreeGroup.invRev L) = maxIndex' L := by
  induction L with
  | nil => rfl
  | cons _ _ ih =>
    unfold FreeGroup.invRev at *
    simp [maxIndex', maxIndex'_append, ih, max_comm, FreeGroup.invRev]

theorem maxIndex_inv (x : A) : maxIndex x⁻¹ = maxIndex x := by
  unfold maxIndex
  rw [FreeGroup.toWord_inv]
  apply maxIndex'_invRev

theorem maxIndex_lt_freshIndex {S : Finset A} {g : A} (hgS : g ∈ S) :
    maxIndex g < freshIndex S := by
  apply Nat.lt_succ_of_le
  rw [← Finset.coe_max']
  simp only [WithBot.unbot'_coe]
  apply Finset.le_max'
  simp only [Finset.mem_image]
  exact ⟨g, hgS, rfl⟩

theorem maxIndex_subgroup_lt_freshIndex (S : Finset A) (g : A) :
    g ∈ Subgroup.closure S → maxIndex g < freshIndex S := by
  apply Subgroup.closure_induction
  · simp only [Finset.mem_coe]
    apply maxIndex_lt_freshIndex
  · unfold maxIndex
    simp [maxIndex']
    unfold freshIndex
    omega
  · intro x y _ _ _ _
    have := maxIndex_mul_le x y
    omega
  · intro x _ ineqx
    have := maxIndex_inv x
    omega

theorem maxIndex_fresh (S : Finset A) : maxIndex (freshGenerator S) = freshIndex S := by
  simp [freshGenerator, maxIndex, maxIndex']

theorem freshGenerator_not_in_span (S : Finset A) :
    freshGenerator S ∉ Subgroup.closure S := by
  intro contra
  have := maxIndex_subgroup_lt_freshIndex _ _ contra
  have := maxIndex_fresh S
  omega

theorem head_maxIndex (x : A) (m : ℕ) (f : Bool) :
    (m,f) ∈ (FreeGroup.toWord x).head? → m ≤ maxIndex x := by
  unfold maxIndex
  cases FreeGroup.toWord x
  · tauto
  · intro hmf
    injection hmf with hh
    rw [hh]
    simp only [maxIndex']
    omega


@[simp]
theorem freshGenerator_toWord (S : Finset A) :
    FreeGroup.toWord (freshGenerator S) = [(freshIndex S, true)] :=
  rfl

@[simp]
theorem freshGenerator_inv_toWord (S : Finset A) :
    FreeGroup.toWord (freshGenerator S)⁻¹ = [(freshIndex S, false)] :=
  rfl


-- TODO: It might be better to go via CoprodI (or now with the reduced lemmas)
theorem fresh_S_no_cancellation {S : Finset A} {x : A} (hx : x ∈ Subgroup.closure S) :
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
    have ineq1 := maxIndex_subgroup_lt_freshIndex S x hx
    have ineq2 : freshIndex S ≤ maxIndex x := by
      apply head_maxIndex
      rewrite [hx', eq1]
      trivial
    omega

theorem fresh_S_inv_no_cancellation {S : Finset A} {x : A} (hx : x ∈ Subgroup.closure S) :
    FreeGroup.toWord (x * (freshGenerator S)⁻¹) =
    FreeGroup.toWord x ++ (FreeGroup.toWord (freshGenerator S)⁻¹) := by
  have hxS : x * (freshGenerator S)⁻¹ = ((freshGenerator S) * x⁻¹)⁻¹ := by simp
  rw [hxS, FreeGroup.toWord_inv, fresh_S_no_cancellation (Subgroup.inv_mem _ hx),
  invRev_append, ← FreeGroup.toWord_inv]
  simp [FreeGroup.invRev]

/- We define a group homomorphism on the free group that trivializes all generators that are indexed
by smaller indices than the fresh index. This should be a convenient tool to proof inequalities
involving the fresh generator that also hS in the abelianization. -/

def dropGenerators (n : ℕ) : A →* A := lift (fun i => if i ≤ n then 1 else of i)

theorem dropGenerators_maxIndex' (n : ℕ) (a : List (ℕ × Bool)) :
    maxIndex' a ≤ n → dropGenerators n (mk a) = 1 := by
  induction a
  case nil => tauto
  case cons _ _ ih =>
    rw [← List.singleton_append]
    intro hn
    simp only [maxIndex', List.singleton_append, sup_le_iff] at hn
    rw [← mul_mk, MonoidHom.map_mul, ih]
    · simp [dropGenerators, hn.1]
    · exact hn.2

theorem dropGenerators_maxIndex (n : ℕ) (a : A) : maxIndex a ≤ n → dropGenerators n a = 1 := by
  nth_rw 2 [← mk_toWord (x := a)]
  apply dropGenerators_maxIndex'

def forgetOld (S : Finset A) : A →* A := dropGenerators (freshIndex S - 1)

@[simp]
theorem forgetOld_fresh {S : Finset A} : forgetOld S (freshGenerator S) = freshGenerator S := by
  simp [forgetOld, freshGenerator, dropGenerators, freshIndex]

@[simp]
theorem forgetOld_old {S : Finset A} {x : A} (hxS : x ∈ S) : forgetOld S x = 1 := by
  apply dropGenerators_maxIndex
  have := maxIndex_lt_freshIndex hxS
  omega

end FreshGenerator
