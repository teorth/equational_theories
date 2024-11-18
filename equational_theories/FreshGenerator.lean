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

abbrev A := FreeGroup Nat

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

theorem maxIndex_lt_freshIndex (old : Finset A) (g : A)  (h : g ∈ old) : maxIndex g < freshIndex old := by
  unfold freshIndex
  apply Nat.lt_succ_of_le
  rw [← Finset.coe_max']
  simp only [WithBot.unbot'_coe]
  apply Finset.le_max'
  simp only [Finset.mem_image]
  use g, h

theorem maxIndex_subgroup_lt_freshIndex (old : Finset A) (g : A) : g ∈ Subgroup.closure old →
  maxIndex g < freshIndex old := set_option pp.all true in by
  apply Subgroup.closure_induction
  · simp only [Finset.mem_coe]
    apply maxIndex_lt_freshIndex
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

/- We define a group homomorphism on the free group that trivializes all generators that are indexed
by smaller indices than the fresh index. This should be a convenient tool to proof inequalities
involving the fresh generator that also hold in the abelianization. -/

def dropGenerators (n : Nat) : A →* A := lift (fun i => if i ≤ n then 1 else of i)

theorem dropGenerators_maxIndex' (n : Nat) (a : List (Nat × Bool)) : maxIndex' a ≤ n → dropGenerators n (mk a) = 1 := by
  induction a
  case nil => tauto
  case cons head tail ih =>
    rw [← List.singleton_append]
    intro h
    rw [← mul_mk]
    rw [MonoidHom.map_mul]
    rw [ih]
    · unfold dropGenerators
      unfold maxIndex' at h
      simp only [List.singleton_append, sup_le_iff] at h
      simp [h.1]
    · unfold maxIndex' at h
      simp only [List.singleton_append, sup_le_iff] at h
      exact h.2

theorem dropGenerators_maxIndex (n : Nat)  (a : A) : maxIndex a ≤ n → dropGenerators n a = 1 := by
  unfold maxIndex
  nth_rw 2 [← mk_toWord (x :=a)]
  apply dropGenerators_maxIndex'

def forgetOld (old : Finset A) : A →* A := dropGenerators (freshIndex old - 1)

@[simp]
theorem forgetOld_fresh {old : Finset A} : forgetOld old (freshGenerator old) = freshGenerator old := by
  unfold forgetOld freshGenerator dropGenerators freshIndex
  simp

@[simp]
theorem forgetOld_old {old : Finset A} {x : A} (h : x ∈ old) : forgetOld old x = 1 := by
  unfold forgetOld
  apply dropGenerators_maxIndex
  have := maxIndex_lt_freshIndex old x h
  omega

end FreshGenerator
