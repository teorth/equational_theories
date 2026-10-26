import equational_theories.Equations.LawsComplete
import equational_theories.Preorder

/-!
# Witnesses for the implication graph

This file defines the two kinds of *witness* that the certified decision procedure produces,
together with `Bool`-valued checkers for them and the proof that anything the checkers accept
is true.

Nothing here mentions the certificate tables. A witness is checked only against `pos` and `neg`,
which are **proof-carrying**: a `PosFact` contains a proof of the implication it records, and a
`NegFact` the magma witnessing its own claim, so neither can contain anything false -- a wrong
entry does not typecheck. The tables in `Certificate.lean` only *find* witnesses, and are
untrusted: garbage there yields something the checker rejects, never a wrong theorem.

Indices are 0-based, matching `laws`: index `i` denotes `Law{i+1}`.
-/

/-!
## List-indexed satisfaction

`NegFact` is stated in terms of these: one witness covers many laws at once, which is what keeps
the cover linear (`Certificate.lean`).

Both unfold *definitionally* to a right-nested conjunction terminated by `True`, which lets
`factsProof` build a witness's proof term from plain `And.intro`/`And.left`/`And.right`.
-/

namespace Law

variable {G : Type} [Magma G]

/-- `G` satisfies every law in `ls`. -/
def SatisfiesAll (G : Type) [Magma G] : List (MagmaLaw ℕ) → Prop
  | [] => True
  | l :: ls => G ⊧ l ∧ SatisfiesAll G ls

/-- `G` refutes every law in `ls`. -/
def RefutesAll (G : Type) [Magma G] : List (MagmaLaw ℕ) → Prop
  | [] => True
  | l :: ls => ¬ (G ⊧ l) ∧ RefutesAll G ls

@[simp] theorem satisfiesAll_nil : SatisfiesAll G [] := trivial
@[simp] theorem refutesAll_nil : RefutesAll G [] := trivial

@[simp] theorem satisfiesAll_cons {l ls} :
    SatisfiesAll G (l :: ls) ↔ (G ⊧ l ∧ SatisfiesAll G ls) := Iff.rfl

@[simp] theorem refutesAll_cons {l ls} :
    RefutesAll G (l :: ls) ↔ (¬ (G ⊧ l) ∧ RefutesAll G ls) := Iff.rfl

theorem satisfiesAll_iff {ls : List (MagmaLaw ℕ)} :
    SatisfiesAll G ls ↔ ∀ l ∈ ls, G ⊧ l := by
  induction ls with
  | nil => simp [SatisfiesAll]
  | cons l ls ih => simp [SatisfiesAll, ih]

theorem refutesAll_iff {ls : List (MagmaLaw ℕ)} :
    RefutesAll G ls ↔ ∀ l ∈ ls, ¬ (G ⊧ l) := by
  induction ls with
  | nil => simp [RefutesAll]
  | cons l ls ih => simp [RefutesAll, ih]

theorem SatisfiesAll.mem {ls : List (MagmaLaw ℕ)} (h : SatisfiesAll G ls) {l} (hl : l ∈ ls) :
    G ⊧ l := satisfiesAll_iff.mp h l hl

theorem RefutesAll.mem {ls : List (MagmaLaw ℕ)} (h : RefutesAll G ls) {l} (hl : l ∈ ls) :
    ¬ (G ⊧ l) := refutesAll_iff.mp h l hl

end Law

/-!
## Witnesses
-/

namespace EndToEnd

open Law

/-- The law at (0-based) index `i`, i.e. `Law{i+1}`. -/
abbrev lawOf (i : Nat) : Law.NatMagmaLaw := laws.get i

/-- A proven implication between two laws, carrying its proof. -/
structure PosFact where
  /-- the law assumed -/
  hyp : Nat
  /-- the law concluded -/
  conc : Nat
  proof : (lawOf hyp).implies (lawOf conc)

/-- A magma satisfying every law in `satisfies` and refuting every law in `refutes`, carrying its proof.
This is the deep-embedded form of a `Facts` theorem. -/
structure NegFact where
  /-- laws the magma satisfies -/
  satisfies : List Nat
  /-- laws the magma refutes -/
  refutes : List Nat
  h : ∃ (G : Type) (_ : Magma G),
        Law.SatisfiesAll G (satisfies.map lawOf) ∧ Law.RefutesAll G (refutes.map lawOf)

/-- A derivation of `lawOf n ⟹ lawOf m`: a list of indices into `pos`, composed left to right. -/
abbrev Implication := List Nat

/-- A refutation of `lawOf n ⟹ lawOf m`: the model witness `fact`, one law `a` it satisfies with
`a ⟹ n`, and one law `b` it refutes with `m ⟹ b`, each justified by an implication. -/
structure Refutation where
  fact : Nat
  a : Nat
  b : Nat
  up : Implication
  down : Implication
deriving Repr

variable (pos : RArray PosFact) (neg : RArray NegFact)

/-- Check that `c` derives `lawOf n ⟹ lawOf m` from `pos`. -/
def checkImplication (pos : RArray PosFact) : Nat → Nat → Implication → Bool
  | n, m, [] => n == m
  | n, m, k :: ks =>
      let f := pos.get k
      (f.hyp == n) && checkImplication pos f.conc m ks

/-- Check that `r` refutes `lawOf n ⟹ lawOf m` using `neg`. -/
def checkRefutation (n m : Nat) (r : Refutation) : Bool :=
  let f := neg.get r.fact
  f.satisfies.contains r.a && f.refutes.contains r.b
    && checkImplication pos r.a n r.up && checkImplication pos m r.b r.down

theorem checkImplication_sound : ∀ (c : Implication) (n m : Nat),
    checkImplication pos n m c = true → (lawOf n).implies (lawOf m) := by
  intro c
  induction c with
  | nil =>
      intro n m h
      simp only [checkImplication, beq_iff_eq] at h
      subst h
      exact Law.MagmaLaw.implies_refl _
  | cons k ks ih =>
      intro n m h
      simp only [checkImplication, Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨hn, hrest⟩ := h
      -- `subst` rather than `rw`: the type of `(pos.get k).conc` mentions `(pos.get k).hyp`,
      -- so rewriting inside `hstep` would need an ill-typed motive.
      subst hn
      exact Law.MagmaLaw.implies_trans (pos.get k).proof (ih _ _ hrest)

theorem checkRefutation_sound (n m : Nat) (r : Refutation)
    (h : checkRefutation pos neg n m r = true) : ¬ ((lawOf n).implies (lawOf m)) := by
  simp only [checkRefutation, Bool.and_eq_true] at h
  obtain ⟨⟨⟨haS, hbR⟩, hup⟩, hdown⟩ := h
  intro himp
  obtain ⟨G, inst, hs, hr⟩ := (neg.get r.fact).h
  -- the model satisfies `lawOf r.a`, and `r.a ⟹ n`, so it satisfies `lawOf n`
  have hsa : @satisfies Nat G inst (lawOf r.a) :=
    hs.mem (List.mem_map_of_mem (List.mem_of_elem_eq_true haS))
  have hn : @satisfies Nat G inst (lawOf n) := @checkImplication_sound pos _ _ _ hup G inst hsa
  -- so it satisfies `lawOf m`, and `m ⟹ r.b`, so it satisfies `lawOf r.b`
  have hb : @satisfies Nat G inst (lawOf r.b) :=
    @checkImplication_sound pos _ _ _ hdown G inst (@himp G inst hn)
  exact (hr.mem (List.mem_map_of_mem (List.mem_of_elem_eq_true hbR))) hb

/-- Implications compose by concatenation. -/
theorem checkImplication_append : ∀ (c₁ : Implication) (n p : Nat) (c₂ : Implication) (m : Nat),
    checkImplication pos n p c₁ = true → checkImplication pos p m c₂ = true →
    checkImplication pos n m (c₁ ++ c₂) = true := by
  intro c₁
  induction c₁ with
  | nil =>
      intro n p c₂ m h₁ h₂
      simp only [checkImplication, beq_iff_eq] at h₁
      subst h₁
      simpa using h₂
  | cons k ks ih =>
      intro n p c₂ m h₁ h₂
      rw [List.cons_append]
      simp only [checkImplication, Bool.and_eq_true, beq_iff_eq] at h₁ ⊢
      exact ⟨h₁.1, ih _ p _ _ h₁.2 h₂⟩

theorem checkImplication_nil (n : Nat) : checkImplication pos n n [] = true := by
  simp [checkImplication]

/-- `lawOf n ⟹ lawOf m` is derivable from the proven implications. -/
def Implied (n m : Nat) : Prop := ∃ c, checkImplication pos n m c = true

/-- `lawOf n ⟹ lawOf m` is refuted by one of the model witnesses. -/
def Refuted (n m : Nat) : Prop := ∃ r, checkRefutation pos neg n m r = true

theorem Implied.sound {n m} (h : Implied pos n m) : (lawOf n).implies (lawOf m) := by
  obtain ⟨c, hc⟩ := h; exact checkImplication_sound pos c n m hc

theorem Refuted.sound {n m} (h : Refuted pos neg n m) : ¬ ((lawOf n).implies (lawOf m)) := by
  obtain ⟨r, hr⟩ := h; exact checkRefutation_sound pos neg n m r hr

end EndToEnd
