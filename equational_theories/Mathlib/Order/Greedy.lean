import Mathlib.Order.Chain
import Mathlib.Data.Set.Countable

theorem Exists.classicalRecOn_eq {α : Sort*} {p : α → Prop} (h : ∃ a, p a)
    {C : Sort*} (H : ∀ a, p a → C) : ∃ a pa, h.classicalRecOn H = H a pa :=
  ⟨_, _, rfl⟩

theorem exists_greedy_chain {α β : Type*} [Preorder α] [Countable β]
    (task : β → Set α) (H : ∀ a b, ∃ a', a ≤ a' ∧ a' ∈ task b) (a : α) :
    ∃ c, IsChain (· ≤ ·) c ∧ a ∈ c ∧ (∀ x ∈ c, a ≤ x) ∧ ∀ b, ∃ a ∈ c, a ∈ task b := by
  have ⟨f, hf⟩ := exists_surjective_nat (Option β)
  let T := Σ a', {c // a' ∈ c ∧ IsChain (· ≤ ·) c ∧ ∀ x ∈ c, a ≤ x ∧ x ≤ a'}
  let G : Nat → T → T := fun n ⟨a', c, ac, hc, hl⟩ =>
    match f n with
    | none => ⟨a', c, ac, hc, hl⟩
    | some b => by
      refine (H a' b).classicalRecOn fun a'' ⟨a'a'', _⟩ => ?_
      refine ⟨a'', insert a'' c, by simp, IsChain.insert hc ?_, ?_⟩
      · exact fun d dc _ => .inr (le_trans (hl _ dc).2 a'a'')
      · refine Set.forall_mem_insert.2 ⟨⟨le_trans (hl _ ac).1 a'a'', le_rfl⟩, ?_⟩
        exact fun d dc => (hl _ dc).imp_right (le_trans · a'a'')
  let F : Nat → Σ a', {c // a' ∈ c ∧ IsChain (· ≤ ·) c ∧ ∀ x ∈ c, a ≤ x ∧ x ≤ a'} :=
    Nat.rec ⟨a, {a}, rfl, Set.subsingleton_singleton.isChain, by simp⟩ G
  have hF i : F (i+1) = G i (F i) := rfl
  have : Monotone (fun i => (F i).2.1) := monotone_nat_of_le_succ fun n => by
    rw [hF]; obtain ⟨a', c, ac, hc, hl⟩ := F n
    simp only [G]; split <;> simp only [le_refl]
    exact let ⟨a, ha, eq⟩ := Exists.classicalRecOn_eq _ _; eq ▸ by cases ha; simp
  refine ⟨⋃ i, (F i).2.1, ?_, ?_, ?_, fun b => ?_⟩
  · rintro a ⟨_, ⟨i, rfl⟩, hi⟩ b ⟨_, ⟨j, rfl⟩, hj⟩ ab; simp at hi hj ⊢
    wlog hle : i ≤ j generalizing a b i j
    · exact (this j hj i hi ab.symm ((le_total ..).resolve_left hle)).symm
    exact (F j).2.2.2.1 (this hle hi) hj ab
  · refine ⟨_, ⟨0, rfl⟩, rfl⟩
  · rintro a' ⟨_, ⟨i, rfl⟩, h⟩; exact ((F i).2.2.2.2 _ h).1
  · clear_value F
    have ⟨i, hi⟩ := hf (some b)
    specialize hF i; simp only [G] at hF
    revert hF; obtain ⟨a', c, ac, hc, hl⟩ := F i; simp [hi]
    refine let ⟨a, ha, eq⟩ := Exists.classicalRecOn_eq _ _; eq ▸ ?_
    obtain ⟨h1, h2⟩ := ha; simp; intro hF
    refine ⟨a, ⟨i+1, ?_⟩, h2⟩
    rw [hF]; simp
