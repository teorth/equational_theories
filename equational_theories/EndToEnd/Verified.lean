import equational_theories.EndToEnd.Correct
import equational_theories.Generated.EndToEndCertificate.Data
import equational_theories.Generated.EndToEndCertificate.Pos
import equational_theories.Generated.EndToEndCertificate.Neg
import equational_theories.DecideBang

/-!
# The end-to-end proof

This file shows that for every pair of 4,694 considered by the Equational Theories Project,
`resolveImplication` returns either a derivation of the implication from the
proven results, or one of the project's model witnesses refuting it. These return values are
checked by the `checkImplication`/`checkRefutation` functions.

Note that implications and refutations are witnessed by indices into a list of theorems
proved in this repository.
-/

namespace EndToEnd

/-- The generated certificate is valid. -/
theorem cert_valid : Valid cert pos neg := valid_of_checkCert (by decide!)

/-- For every ordered pair of laws, `resolveImplication` produces a witness that passes its
checker, and the corresponding mathematical fact holds. The return type is a `Sum`, so it
always returns either an implication or a refutation. -/
theorem end_to_end1 (n m : Nat) (hn : n < 4694) (hm : m < 4694) :
    match resolveImplication cert pos neg n m with
    | .inl c => checkImplication pos n m c = true ∧ (lawOf n).implies (lawOf m)
    | .inr r => checkRefutation pos neg n m r = true ∧ ¬ ((lawOf n).implies (lawOf m)) := by
  have h := resolveImplication_correct cert_valid n m hn hm
  cases hr : resolveImplication cert pos neg n m with
  | inl c =>
      rw [hr] at h
      exact ⟨h, checkImplication_sound pos c n m h⟩
  | inr r =>
      rw [hr] at h
      exact ⟨h, checkRefutation_sound pos neg n m r h⟩

/-- An alternative statement: every pair of equations is deriable as an implication or
refutation from the theorems proved in this repository. -/
theorem end_to_end2 (n m : Nat) (hn : n < 4694) (hm : m < 4694) :
    Implied pos n m ∨ Refuted pos neg n m := by
  have h := end_to_end1 n m hn hm
  cases hr : resolveImplication cert pos neg n m with
  | inl c => rw [hr] at h; exact Or.inl ⟨c, h.1⟩
  | inr r => rw [hr] at h; exact Or.inr ⟨r, h.1⟩

/-- An alternative statement: `Implied` is the same as `MagmaLaw.implies` -/
theorem end_to_end3 (n m : Nat) (hn : n < 4694) (hm : m < 4694) :
    (lawOf n).implies (lawOf m) ↔ Implied pos n m := by
  refine ⟨fun himp => ?_, Implied.sound pos⟩
  rcases end_to_end2 n m hn hm with h | h
  · exact h
  · exact absurd himp (Refuted.sound pos neg h)

end EndToEnd
