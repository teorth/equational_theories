# End-to-end proof

This directory contains the "end-to-end" proof, i.e. the statement that
after applying transitivity and duality the implications and refutations
proved in the Equational Theories Project resolve every possible implication
between any pair of laws. The proof works by verifying a certificate,
computed in `equational_theories/Generated/EndToEndCertificate`. The
certificate contains the necessary information about the implication graph
in a preprocessed-form to enable the final kernel-checked proof step to
efficiently verify that the entire implication graph has been resolved.

The final proof can be seen in `Verified.lean`, `end_to_end1` shows
that the `resolveImplication` function computes a proof of an implication
or a refutation (as a refutation/chain of implications) always matches the
expected result (e.g.  a proof of an implication/refutation always matches
a refutation/implication of the given laws.) Note that indices are 0-based,
so Law 1 is references using the index 0.

This proof is constructive and one can look at the output of the function, the
following snippet gives an example:
```lean4
import equational_theories.EndToEnd.Print

-- Print the chain of implications that Law 3 implies Law 4065
#eval printResolution 3 4065
-- Print a refutation that Law 3 does not imply Law 5
#eval printResolution 3 5
```
Note that this procedure is guaranteed to be correct but makes no attempt at
being optimal, so it is likely to return a more complicated refutation/chain of
implicatins than what is strictly minimal in the underlying data set.

## Contents

- `Basic.lean`: The basic definitions, including for implications and refutations.
- `Certificate.lean`: The definition of the Certificate data structure (this is
  generated in `equational_theories/Generated/EndToEndCertificate`.
- `Correct.lean`: A proof of correctness of the `resolveImplication` function.
- `Dual.lean`: Helper proofs for dealing with duality.
- `Load.lean`: meta-code to help load JSON files in the generated certificate and
  generate the appropriate terms.
- `Print.lean`: Helper functions to pretty-print implications/refutations.
- `Verified.lean`: The final end-to-end proof statements, stated in three different
  ways.

## Provenance

All of the lean code in this directory is AI-generated. This README is human-written.
