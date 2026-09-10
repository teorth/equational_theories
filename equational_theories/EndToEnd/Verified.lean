import equational_theories.EndToEnd.Correct
import equational_theories.Generated.EndToEndCertificate.Data
import equational_theories.Generated.EndToEndCertificate.Pos
import equational_theories.Generated.EndToEndCertificate.Neg
import equational_theories.DecideBang

/-!
# The implication graph, determined

This ties the machinery together on the real data: for every ordered pair of the 4694 laws of
order at most 4, `resolveImplication` returns either a derivation of the implication from the
proven results, or one of the project's model witnesses refuting it -- and whichever it
returns passes an independent check.

`checkCert` is discharged by `decide!`, i.e. by the Lean kernel, with no `native_decide`.
-/

namespace EndToEnd

/-- The generated certificate passes its checker. Kernel-checked. -/
theorem cert_ok : checkCert cert pos neg = true := by decide!

theorem cert_valid : Valid cert pos neg := valid_of_checkCert cert_ok

/-- **The implication graph is determined.**

For every ordered pair of laws, `resolveImplication` produces a witness that passes its
checker, and the corresponding mathematical fact holds. The return type is a `Sum`, so
totality is part of the statement: there is no pair for which it fails to answer. -/
theorem graph_determined (n m : Nat) (hn : n < 4694) (hm : m < 4694) :
    match resolveImplication cert pos neg n m with
    | .inl c => checkChain pos n m c = true ∧ (lawOf n).implies (lawOf m)
    | .inr r => checkRefutation pos neg n m r = true ∧ ¬ ((lawOf n).implies (lawOf m)) := by
  have h := resolveImplication_correct cert_valid n m hn hm
  cases hr : resolveImplication cert pos neg n m with
  | inl c =>
      rw [hr] at h
      exact ⟨h, checkChain_sound pos c n m h⟩
  | inr r =>
      rw [hr] at h
      exact ⟨h, checkRefutation_sound pos neg n m r h⟩

/-- Prop-level form: every pair is either derivable from the proven implications, or refuted
by one of the model witnesses. Note this is not `P ∨ ¬ P` -- `Reachable` and `Refutable` are
concrete relations over proof-carrying data, so excluded middle does not give it. -/
theorem reachable_or_refutable (n m : Nat) (hn : n < 4694) (hm : m < 4694) :
    Reachable pos n m ∨ Refutable pos neg n m := by
  have h := graph_determined n m hn hm
  cases hr : resolveImplication cert pos neg n m with
  | inl c => rw [hr] at h; exact Or.inl ⟨c, h.1⟩
  | inr r => rw [hr] at h; exact Or.inr ⟨r, h.1⟩

/-- The implication relation is exactly the closure of the proven implications. -/
theorem implies_iff_reachable (n m : Nat) (hn : n < 4694) (hm : m < 4694) :
    (lawOf n).implies (lawOf m) ↔ Reachable pos n m := by
  refine ⟨fun himp => ?_, Reachable.sound pos⟩
  rcases reachable_or_refutable n m hn hm with h | h
  · exact h
  · exact absurd himp (Refutable.sound pos neg h)

end EndToEnd
