import Mathlib.Data.List.Lemmas
import Mathlib.GroupTheory.FreeGroup.Reduce
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic.Linarith

/-!
This file defines some extra lemmas for free groups, in particular about (cyclically) reduced words.

## Main statements
* `FreeGroup.infinite_order` : nontrivial elements of a free group have infinite order
* corollary `FreeGroup.ne_inv_of_ne_one` : nontrivial elements of a free group are not self-inverse.

Related mathlib PRs:
* Overall: https://github.com/leanprover-community/mathlib4/pull/22639
* [UPSTREAMED] https://github.com/leanprover-community/mathlib4/pull/23366
* [UPSTREAMED] https://github.com/leanprover-community/mathlib4/pull/23367
* https://github.com/leanprover-community/mathlib4/pull/23368
-/
open List

universe u

variable {α : Type u}
namespace FreeGroup

variable {L L₁ L₂ : List (α × Bool)}

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
  refine ⟨fun h L₂ ↦ not_step_reduced h, ?_⟩
  · intro hL
    induction L₁ with
    | nil => exact reduced_nil
    | cons x l ih =>
      cases l with
      | nil => exact reduced_singleton
      | cons y l' =>
        rw [reduced_cons]
        refine ⟨fun ⟨eq1, eq2⟩ ↦ ?_, ih fun L₂ step ↦ hL (x :: L₂) <| Step.cons step⟩
        obtain ⟨y1, y2⟩ := y
        simp only at eq1 eq2
        exact hL l' <| eq1 ▸ eq2 ▸ Step.cons_not

theorem reduced_infix : reduced L₂ → L₁ <:+: L₂ → reduced L₁ := Chain'.infix

theorem reduced_min (h : reduced L₁) : Red L₁ L₂ ↔ L₂ = L₁ :=
  Relation.reflTransGen_iff_eq fun _ ↦ not_step_reduced h

theorem reduced_cons_append_chain {x : α × Bool} {L₁ L₂ : List (α × Bool)} (h : L₁ ≠ []) :
    reduced (x :: L₁) → reduced (L₁ ++ L₂) → reduced (x :: L₁ ++ L₂) := by
  intro h1 h2
  induction L₁
  · contradiction
  · apply reduced_cons.mp at h1
    exact reduced_cons.mpr <| And.imp_right (fun a ↦ h2) h1

theorem reduced_append_chain {L₁ L₂ L₃ : List (α × Bool)} (h : L₂ ≠ []) :
    reduced (L₁ ++ L₂) → reduced (L₂ ++ L₃) → reduced (L₁ ++ L₂ ++ L₃) := by
  intro h1 h2
  induction L₁
  case nil => simp [h2]
  case cons head tail ih =>
    exact reduced_cons_append_chain (by aesop) h1 (ih (reduced_infix h1 ⟨[head], [], by simp⟩))

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
  refine ⟨⟨by simpa using h.1, List.chain'_replicate_of_rel _ h.2⟩, ?_⟩
  intro a ha b hb
  simp only [Option.mem_def] at ha hb
  rw [List.getLast?_flatten_replicate (h := by simp +arith)] at ha
  rw [List.head?_flatten_replicate (h := by simp +arith)] at hb
  exact h.2 _ ha _ hb

variable [DecidableEq α]

theorem reduced_iff_eq_reduce : reduced L ↔ reduce L = L := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rw [← reduced_min h]
    exact reduce.red
  · unfold reduced
    rw [List.chain'_iff_forall_rel_of_append_cons_cons]
    intro ⟨x₁, x₂⟩ ⟨y₁, y₂⟩ l₁ l₂ hl hx
    simp only at hl hx
    rw [hx.1, ← hx.2] at hl
    nth_rw 2 [hl] at h
    exact reduce.not h

end Red

variable [DecidableEq α]

theorem reduced_toWord {x : FreeGroup α} : Red.reduced (x.toWord) := by
  rw [Red.reduced_iff_eq_reduce]
  simp

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
theorem reduceCyclically_nil : reduceCyclically ([] : List (α × Bool)) = [] := by
  simp [reduceCyclically]

@[simp]
theorem reduceCyclically_singleton {a : α × Bool} : reduceCyclically [a] = [a] := by
  simp [reduceCyclically]

@[simp]
theorem reduceCyclicallyConjugator_nil :
    reduceCyclicallyConjugator ([] : List (α × Bool)) = [] := by
  simp [reduceCyclicallyConjugator]

@[simp]
theorem reduceCyclicallyConjugator_singleton {a : α × Bool} :
    reduceCyclicallyConjugator [a] = [] := by
  simp [reduceCyclicallyConjugator]


theorem reduceCyclically_cons_append {a b : α × Bool} (l : List (α × Bool)) :
    reduceCyclically (a :: (l ++ [b])) =
    if (b.1 = a.1 ∧ (!b.2) = a.2) then reduceCyclically l else (a :: l ++ [b]) := by
  simp [reduceCyclically]

theorem reduceCyclicallyConjugator_cons_append {a b : α × Bool} (l : List (α × Bool)) :
    reduceCyclicallyConjugator (a :: (l ++ [b])) =
    if (b.1 = a.1 ∧ (!b.2) = a.2) then a :: reduceCyclicallyConjugator l else [] := by
  simp [reduceCyclicallyConjugator]

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

theorem reduced_flatten_replicate (n : ℕ) (hn : n ≠ 0) (L₁ L₂ L₃ : List (α × Bool))
    (h1 : Red.cyclicallyReduced L₂) (h2 : Red.reduced (L₁ ++ L₂ ++ L₃))
    : Red.reduced (L₁ ++ (List.replicate n L₂).flatten ++ L₃) := by
  match n with
  | 0 => contradiction
  | n + 1 =>
    if h : L₂ = [] then simp_all else
    have h' : (replicate (n + 1) L₂).flatten ≠ [] := by simp [h]
    apply Red.reduced_append_chain h'
    · rw [replicate_succ, flatten_cons, ←append_assoc]
      apply Red.reduced_append_chain h
      · exact Red.reduced_infix h2 ⟨[], L₃, by simp⟩
      · rw [←flatten_cons, ←replicate_succ]
        apply Red.reduced_of_cyclicallyReduced
        apply Red.cyclicallyReduced_flatten_replicate _ _ h1
    · rw [replicate_succ', flatten_concat]
      apply Red.reduced_append_chain h
      · rw [←flatten_concat, ←replicate_succ']
        apply Red.reduced_of_cyclicallyReduced
        apply Red.cyclicallyReduced_flatten_replicate _ _ h1
      · exact Red.reduced_infix h2 ⟨L₁, [], by simp⟩

theorem reduce_flatten_replicate' (n : ℕ) (L : List (α × Bool)) (h : Red.reduced L) :
    reduce (List.replicate (n + 1) L).flatten = reduceCyclicallyConjugator L ++ (List.replicate (n + 1) (reduceCyclically L)).flatten ++ invRev (reduceCyclicallyConjugator L) := by
  induction n
  case zero =>
    simpa [←append_assoc, ←reduceCyclically_conjugation, ←Red.reduced_iff_eq_reduce]
  case succ n ih =>
    rw [replicate_succ, flatten_cons, ← reduce_append_reduce_reduce, ih, Red.reduced_iff_eq_reduce.mp h]
    nth_rewrite 1 [reduceCyclically_conjugation L]
    have {L₁ L₂ L₃ L₄ L₅ : List (α × Bool)} : reduce (L₁ ++ L₂ ++ invRev L₃ ++ (L₃ ++ L₄ ++ L₅)) = reduce (L₁ ++ (L₂ ++ L₄) ++ L₅) := by
      nth_rewrite 1 [append_assoc]
      nth_rewrite 2 [←append_assoc, ←append_assoc]
      nth_rewrite 1 [← reduce_append_reduce_reduce]
      nth_rewrite 3 [← reduce_append_reduce_reduce]
      nth_rewrite 4 [← reduce_append_reduce_reduce]
      simp [reduce_invRev_left_cancel, reduce_append_reduce_reduce]
    rw [this, ←flatten_cons, ←replicate_succ, ←Red.reduced_iff_eq_reduce]
    apply reduced_flatten_replicate _ (by simp) ..
    · apply reduceCyclically_sound _ h
    · rwa [←reduceCyclically_conjugation]

theorem reduce_flatten_replicate {n : ℕ} {L : List (α × Bool)} (hn : n ≠ 0) (h : Red.reduced L) :
    reduce (List.replicate n L).flatten = reduceCyclicallyConjugator L ++ (List.replicate n (reduceCyclically L)).flatten ++ invRev (reduceCyclicallyConjugator L) :=
  match n with
  | 0 => by contradiction
  | n + 1 => reduce_flatten_replicate' n L h

theorem infinite_order (x : FreeGroup α) (x_ne_1 : x ≠ 1) : ¬IsOfFinOrder x := by
  let x' := FreeGroup.mk $ reduceCyclically (x.toWord)
  have conj : IsConj x' x := by
    rw [isConj_iff]
    use (FreeGroup.mk (reduceCyclicallyConjugator x.toWord))
    nth_rw 3 [← FreeGroup.mk_toWord (x := x), reduceCyclically_conjugation (w := x.toWord)]
    rw [FreeGroup.mul_mk,FreeGroup.inv_mk, FreeGroup.mul_mk]
  intro c
  obtain ⟨n, n_gt_0, eq'⟩ :=
    isOfFinOrder_iff_pow_eq_one.mp $ conj.symm.isOfFinOrder c
  have x'_ne_1 : x' ≠ 1 := by
    intro eq
    rw [eq] at conj
    exact x_ne_1 <| isConj_one_right.mp conj
  have x'_toWord_ne_nil : x'.toWord ≠ [] := fun h => x'_ne_1 (toWord_eq_nil_iff.mp h)
  rw [pow_mk] at eq'
  apply_fun toWord at eq'
  simp only [toWord_mk, toWord_one] at eq'
  rw [Red.reduced_iff_eq_reduce.mp] at eq'
  . unfold x' at x'_toWord_ne_nil
    simp only [toWord_mk, ne_eq] at x'_toWord_ne_nil
    simp only [flatten_eq_nil_iff, mem_replicate, ne_eq, and_imp, forall_eq_apply_imp_iff] at eq'
    rw [eq' (by omega)] at x'_toWord_ne_nil
    exact x'_toWord_ne_nil rfl
  · apply Red.reduced_of_cyclicallyReduced
    apply Red.cyclicallyReduced_flatten_replicate
    apply reduceCyclically_sound
    exact reduced_toWord

theorem ne_inv_of_ne_one {x : FreeGroup α} (x_ne_one : x ≠ 1) : x ≠ x⁻¹ := by
  apply_fun (fun r => x*r)
  simp only [mul_inv_cancel, ne_eq]
  intro eq
  apply infinite_order x x_ne_one
  rw [isOfFinOrder_iff_pow_eq_one]
  exact ⟨2, (by decide), eq ▸ pow_two x⟩

theorem pow_injective {x y : FreeGroup α} {n : ℕ} (hn : n ≠ 0) : x = y ↔ x ^ n = y ^ n := by
  refine ⟨congr_arg (· ^ n), fun heq ↦ ?_⟩
  have heq2 : x ^ (2 * n) = y ^ (2 * n) := by
    apply_fun (· ^ 2) at heq
    rwa [mul_comm, pow_mul, pow_mul]
  have hn2 : 2 * n ≠ 0 := by simp [hn]
  apply_fun toWord at heq heq2
  rw [toWord_pow, toWord_pow] at heq heq2
  rw [reduce_flatten_replicate hn x.reduced_toWord,
    reduce_flatten_replicate hn y.reduced_toWord] at heq
  rw [reduce_flatten_replicate hn2 x.reduced_toWord,
    reduce_flatten_replicate hn2 y.reduced_toWord] at heq2
  have leq := congr_arg List.length heq
  have leq2 := congr_arg List.length heq2
  simp only [append_assoc, length_append, length_flatten, map_replicate, sum_replicate, smul_eq_mul,
    invRev_length] at leq leq2
  have hm : (reduceCyclically x.toWord).length = (reduceCyclically y.toWord).length := by
    apply Nat.mul_left_cancel (Nat.ne_zero_iff_zero_lt.mp hn)
    linarith
  have hc : reduceCyclicallyConjugator x.toWord = reduceCyclicallyConjugator y.toWord := by
    have : (reduceCyclicallyConjugator x.toWord).length =
        (reduceCyclicallyConjugator y.toWord).length := by
      linarith
    apply_fun (·.take (reduceCyclicallyConjugator x.toWord).length) at heq
    rwa [append_assoc, take_left' rfl, this, append_assoc, take_left' rfl] at heq
  have hm : reduceCyclically x.toWord = reduceCyclically y.toWord := by
    simp only [hc, append_assoc, append_cancel_left_eq, append_cancel_right_eq] at heq
    apply_fun (·.take (reduceCyclically x.toWord).length) at heq
    match n with
    | 0 => contradiction
    | n + 1 =>
      rw [replicate_succ, flatten_cons, take_left' rfl] at heq
      rwa [replicate_succ, flatten_cons, hm, take_left' rfl] at heq
  have := congr_arg mk <| reduceCyclically_conjugation x.toWord
  rwa [hc, hm, ←reduceCyclically_conjugation, mk_toWord, mk_toWord] at this

theorem zpow_injective {x y : FreeGroup α} {n : ℤ} (hn : n ≠ 0) : x = y ↔ x ^ n = y ^ n := by
  rw [pow_injective (Int.natAbs_ne_zero.mpr hn)]
  rcases Int.natAbs_eq n with h | h
  · rw [h, Int.natAbs_natCast, zpow_natCast, zpow_natCast]
  · rw [h, Int.natAbs_neg, Int.natAbs_natCast, zpow_neg, zpow_neg, inv_inj, zpow_natCast,
      zpow_natCast]

end FreeGroup
