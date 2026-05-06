## Ramanujan law

This law implies that left multiplications are injective and right multiplications are surjective.  In finite magmas, or in quasigroups, this law is equivalent to the
[Hardy law 917](https://teorth.github.io/equational_theories/implications/?917) and [Littlewood law 2541](https://teorth.github.io/equational_theories/implications/?2541).  Without such assumptions, the Ramanujan law 1729 implies the Littlewood law 2541, but no other implication holds.  For translation-invariant models, the Hardy law is a consequence of the Ramanujan law.

The fact that the Ramanujan law does not imply the Hardy law is known via a [complex construction](https://teorth.github.io/equational_theories/blueprint/1323-chapter.html), first discovered to analyze [law 1323](https://teorth.github.io/equational_theories/implications/?1323).

The proof that it does not implies [817](https://teorth.github.io/equational_theories/implications/?817) (special case of the Hardy law) was the last one to be formalized, due to its extraordinary complexity.  It required a [blueprint of nineteen](https://teorth.github.io/equational_theories/blueprint/1729-chapter.html) custom definitions, lemmas and theorems, and accounts for roughly 10 percent of the Lean code written for the project (excluding generated code).

The laws 1729, 917, 2541 are twists of laws [125](https://teorth.github.io/equational_theories/implications/?125), [73](https://teorth.github.io/equational_theories/implications/?73), [229](https://teorth.github.io/equational_theories/implications/?229) by the squaring map.
