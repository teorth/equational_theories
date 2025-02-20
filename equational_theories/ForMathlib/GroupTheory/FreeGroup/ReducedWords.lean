import Mathlib.GroupTheory.FreeGroup.Reduce
import equational_theories.Mathlib.Data.List.Chain
import equational_theories.Mathlib.Data.List.Lemmas
import equational_theories.Mathlib.GroupTheory.OrderOfElement

/-!
This file defines some extra lemmas for free groups, in particular about (cyclically) reduced words.

## Main statements
* `FreeGroup.infinite_order` : nontrivial elements of a free group have infinite order
* corrollary `FreeGroup.ne_inv_of_ne_one` : nontrivial elements of a free group are not self-inverse.

-/
open List

universe u

variable {α : Type u}
namespace FreeGroup

variable {L L₁ L₂ : List (α × Bool)}

theorem invRev_append : invRev (L₁ ++ L₂) = invRev L₂ ++ invRev L₁ := by
  unfold invRev
  simp

theorem invRev_cons {a : (α × Bool)} : invRev (a:: L) = invRev L ++ invRev [a] := by
  unfold FreeGroup.invRev
  simp

namespace Red

def reduced (L : List (α × Bool)) : Prop := List.Chain' (fun a b => ¬(a.1 = b.1 ∧ (!a.2) = b.2)) L

@[simp]
theorem reduced_nil : reduced ([] : List (α × Bool)) := List.chain'_nil

@[simp]
theorem reduced_singleton {a : (α × Bool)} : reduced [a] := List.chain'_singleton a

theorem reduced_cons {a b: (α × Bool)} :
    reduced (a :: b :: L) ↔ ¬(a.1 = b.1 ∧ (!a.2) = b.2) ∧ reduced (b :: L) :=
  List.chain'_cons

theorem not_step_reduced : reduced L₁ → ¬ Step L₁ L₂ := by
  intro red step
  induction step with
  | @not l r x b =>
    unfold reduced at red
    simp at red

theorem not_step_reduced_iff : reduced L₁ ↔ ∀ L₂, ¬ Step L₁ L₂ := by
  constructor
  · exact fun h L₂ => not_step_reduced h
  · intro hL
    induction L₁ with
    | nil => exact reduced_nil
    | cons x l ih =>
      cases l with
      | nil => exact reduced_singleton
      | cons y l' =>
        rw [reduced_cons]
        constructor
        · intro ⟨eq1, eq2⟩
          obtain ⟨x1, x2⟩ := x
          obtain ⟨y1, y2⟩ := y
          simp only at eq1 eq2
          apply hL l'
          rw [eq1, ← eq2]
          apply Step.cons_not
        · apply ih
          intro L₂ step
          apply hL (x :: L₂)
          exact Step.cons step

theorem reduced_infix : reduced L₂ → L₁ <:+: L₂ → reduced L₁ := Chain'.infix

theorem reduced_min (h : reduced L₁) : Red L₁ L₂ ↔ L₂ = L₁ :=
  Relation.reflTransGen_iff_eq fun _ => not_step_reduced h

def cyclicallyReduced (L : List (α × Bool)) : Prop :=
  reduced L ∧ ∀ a ∈ L.getLast?, ∀ b ∈ L.head?, ¬(a.1 = b.1 ∧ (!a.2) = b.2)

@[simp]
theorem cyclicallyReduced_nil : cyclicallyReduced ([] : List (α × Bool)) := by
  simp [cyclicallyReduced]

@[simp]
theorem cyclicallyReduced_singleton {x : (α × Bool )} : cyclicallyReduced [x] := by
  simp [cyclicallyReduced]

theorem cyclicallyReduced_iff : cyclicallyReduced L ↔ reduced L ∧ ∀ a ∈ L.getLast?, ∀ b ∈ L.head?,
¬(a.1 = b.1 ∧ (!a.2) = b.2) := by rfl

theorem cyclicallyReduced_cons_append {a b : α × Bool} :
    cyclicallyReduced (b :: L ++ [a]) ↔
    reduced (b :: L ++ [a]) ∧ ¬(a.1 = b.1 ∧ (!a.2) = b.2) := by
  rw [cyclicallyReduced_iff,List.getLast?_concat]
  simp

theorem reduced_of_cyclicallyReduced (L : List (α × Bool)) : cyclicallyReduced L → reduced L :=
  fun h => h.1

theorem cyclicallyReduced_flatten_replicate (n : ℕ) (L : List (α × Bool)) (h : cyclicallyReduced L):
cyclicallyReduced (List.replicate n L).flatten := by match n, L with
| 0, _ => simp
| n+1, [] => simp
| n+1, (head::tail) =>
  unfold cyclicallyReduced at *
  unfold reduced at *
  rw [List.chain'_flatten (by simp)]
  constructor
  · constructor
    · simp only [List.mem_replicate, ne_eq, AddLeftCancelMonoid.add_eq_zero, one_ne_zero, and_false,
      not_false_eq_true, true_and, Bool.not_eq_eq_eq_not, not_and, Bool.not_eq_not, forall_eq] at *
      apply h.1
    · apply List.chain'_replicate_of_rel _ h.2
  · intro a ha b hb
    simp only [Option.mem_def] at ha hb
    rw [List.getLast?_flatten_replicate (h := by simp_arith)] at ha
    rw [List.head?_flatten_replicate (h := by simp_arith)] at hb
    apply h.2 _ ha _ hb

variable [DecidableEq α]

theorem reduced_iff_eq_reduce : reduced L ↔ reduce L = L := by
  constructor
  · intro h
    rw [← reduced_min h]
    exact reduce.red
  · intro h
    unfold reduced
    rw [List.chain'_iff_all_append_cons_cons]
    intro ⟨x₁, x₂⟩ ⟨y₁, y₂⟩ l₁ l₂ hl hx
    simp only at hl hx
    rw [hx.1, ← hx.2] at hl
    nth_rw 2 [hl] at h
    apply reduce.not h

end Red

variable [DecidableEq α]

theorem reduced_toWord {x : FreeGroup α} : Red.reduced (x.toWord) := by
  rw [Red.reduced_iff_eq_reduce]
  simp

theorem toWord_mul {x y : FreeGroup α} : (toWord (x*y)) = reduce (toWord x ++ toWord y) := by
  rw [← mk_toWord (x:= x), ← mk_toWord (x:= y), mul_mk]
  simp

theorem reduce_append: (reduce (L₁ ++ L₂)) = reduce (reduce L₁ ++ reduce L₂) := by
rw [← FreeGroup.toWord_mk, ← FreeGroup.mul_mk, toWord_mul, FreeGroup.toWord_mk, FreeGroup.toWord_mk]

theorem reduce_cons (a : α × Bool) (w : List (α × Bool)) :
    FreeGroup.reduce (a :: w) = FreeGroup.reduce (a :: FreeGroup.reduce w) := by
  simp only [FreeGroup.reduce.cons, FreeGroup.reduce.idem]

-- theorem reduce_singleton (a : α × Bool) : FreeGroup.reduce [a] = [a] := rfl

def reduceCyclically : List (α × Bool) → List (α × Bool) :=
  List.bidirectionalRec
    (nil := [])
    (singleton := fun x => [x])
    (cons_append := fun a l b rC => if (b.1 = a.1 ∧ (!b.2) = a.2) then rC else (a :: l ++ [b]))

def reduceCyclicallyConjugator : List (α × Bool) → List (α × Bool) := List.bidirectionalRec
  (nil := [])
  (singleton := fun _ => [])
  (cons_append := fun a _ b rCC => if (b.1 = a.1 ∧ (!b.2) = a.2) then a :: rCC else [] )

@[simp]
theorem reduceCyclically_nil : reduceCyclically ([] : List (α × Bool)) = [] :=
  by simp [reduceCyclically]

@[simp]
theorem reduceCyclically_singleton {a : α × Bool} : reduceCyclically [a] = [a] :=
  by simp [reduceCyclically]

@[simp]
theorem reduceCyclicallyConjugator_nil : reduceCyclicallyConjugator ([] : List (α × Bool)) = [] :=
  by simp [reduceCyclicallyConjugator]

@[simp]
theorem reduceCyclicallyConjugator_singleton {a : α × Bool} : reduceCyclicallyConjugator [a] = [] :=
  by simp [reduceCyclicallyConjugator]


theorem reduceCyclically_cons_append {a b : α × Bool} (l : List (α × Bool)) :
    reduceCyclically (a :: (l ++ [b])) =
    if (b.1 = a.1 ∧ (!b.2) = a.2) then reduceCyclically l else (a :: l ++ [b]) := by
  unfold reduceCyclically
  simp

theorem reduceCyclicallyConjugator_cons_append {a b : α × Bool} (l : List (α × Bool)) :
    reduceCyclicallyConjugator (a :: (l ++ [b])) =
    if (b.1 = a.1 ∧ (!b.2) = a.2) then a :: reduceCyclicallyConjugator l else [] := by
  unfold reduceCyclicallyConjugator
  simp

theorem reduceCyclically_conjugation (w : List (α × Bool)) :
    w = reduceCyclicallyConjugator w ++ reduceCyclically w ++ invRev (reduceCyclicallyConjugator w) := by
  induction w using List.bidirectionalRec
  case nil => simp
  case singleton => simp
  case cons_append a l b eq =>
    rw [reduceCyclically_cons_append, reduceCyclicallyConjugator_cons_append]
    split
    case isTrue h =>
      nth_rw 1 [eq]
      simp [invRev, h.1.symm, h.2.symm]
    case isFalse => simp

theorem reduceCyclically_sound (w : List (α × Bool)) :
    Red.reduced w → Red.cyclicallyReduced (reduceCyclically w) := by
  induction w using List.bidirectionalRec
  case nil => simp
  case singleton => simp
  case cons_append a l b ih =>
    intro h
    rw [reduceCyclically_cons_append]
    split
    case isTrue =>
      apply ih
      apply Red.reduced_infix h
      exists [a], [b]
    case isFalse h =>
      rw [Red.cyclicallyReduced_cons_append]
      trivial

theorem infinite_order (x : FreeGroup α) (x_ne_1 : x ≠ 1) : ¬IsOfFinOrder x := by
  let x' := FreeGroup.mk $ reduceCyclically (x.toWord)
  have conj : IsConj x' x := by
    rw [isConj_iff]
    use (FreeGroup.mk (reduceCyclicallyConjugator x.toWord))
    nth_rw 3 [← FreeGroup.mk_toWord (x := x), reduceCyclically_conjugation (w := x.toWord)]
    rw [FreeGroup.mul_mk,FreeGroup.inv_mk, FreeGroup.mul_mk]
  intro c
  obtain ⟨n, n_gt_0, eq'⟩ :=
    isOfFinOrder_iff_pow_eq_one.mp $ isOfFinOrder_of_isConj (IsConj.symm conj) c
  have x'_ne_1 : x' ≠ 1 := by
    intro eq
    rw [eq] at conj
    apply x_ne_1
    apply isConj_one_right.mp conj
  have x'_toWord_ne_nil : x'.toWord ≠ [] := fun h => x'_ne_1 (toWord_eq_nil_iff.mp h)
  rw [pow_mk] at eq'
  apply_fun toWord at eq'
  simp only [toWord_mk, toWord_one] at eq'
  rw [Red.reduced_iff_eq_reduce.mp] at eq'
  . unfold x' at x'_toWord_ne_nil
    simp only [toWord_mk, ne_eq] at x'_toWord_ne_nil
    simp only [flatten_eq_nil_iff, mem_replicate, ne_eq, and_imp, forall_eq_apply_imp_iff] at eq'
    rw [eq' (by omega)] at x'_toWord_ne_nil
    apply x'_toWord_ne_nil
    rfl
  · apply Red.reduced_of_cyclicallyReduced
    apply Red.cyclicallyReduced_flatten_replicate
    apply reduceCyclically_sound
    apply reduced_toWord

theorem ne_inv_of_ne_one {x : FreeGroup α} (x_ne_one : x ≠ 1) : x ≠ x⁻¹ := by
  apply_fun (fun r => x*r)
  simp only [mul_inv_cancel, ne_eq]
  intro eq
  apply infinite_order x x_ne_one
  rw [isOfFinOrder_iff_pow_eq_one]
  use 2, (by decide)
  rw [← eq]
  exact pow_two x

theorem pow_injective {x y : FreeGroup α} {n : ℕ} (hn : n ≠ 0) : x = y ↔ x ^ n = y ^ n := by
  sorry

theorem zpow_injective {x y : FreeGroup α} {n : ℤ} (hn : n ≠ 0) : x = y ↔ x ^ n = y ^ n := by
  rw [pow_injective (Int.natAbs_ne_zero.mpr hn)]
  rcases Int.natAbs_eq n with h | h
  · rw [h, Int.natAbs_ofNat, zpow_natCast, zpow_natCast]
  · rw [h, Int.natAbs_neg, Int.natAbs_ofNat, zpow_neg, zpow_neg, inv_inj, zpow_natCast, zpow_natCast]

end FreeGroup
