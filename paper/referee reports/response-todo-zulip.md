========== MESSAGE 1 of 2 — copy everything below this line ==========

**Referee reports: TO DO list (1/2 — Referee #1)**

Two referee reports are in. Referee #1 asks for **major revisions**, Referee #2 for **minor revisions**. Numbering below matches `paper/referee reports/response.tex`, where each item has a `\response{\todo}` slot waiting to be filled — so please **claim an item by replying with its number** (e.g. "claiming R1.12, R1.13"), and use the same number when you fill in the response.

Referee #2 numbered their own items, so R2.$$n$$ and R2.T$$n$$ match their report exactly. Referee #1's report is prose under five headings; R1.$$n$$ is our numbering, grouped under their headings.

**Already handled:** the 13 items struck through below are already implemented in the manuscript (R1.M1, the mechanical typos R2.T1, T2, T3, T5, T7, T8, T9, T11, T12, T13, and the two citation items R2.1 and R2.2); R2.T4 and R2.T6 are claimed. **41 items remain unclaimed.**

**Five requests are made by both referees** and need consistent answers: the unformalized transitivity/duality extension (R1.1–R1.6 + R2.4), compilation timings (R1.7 + R2.4), the trusted axiom set (R1.3 + R2.3), §11 (R1.18 + R2.13), and the phrase "proof assistant language Lean" (R1.M1 + R2.T1). Worth one person taking each cluster.

---

**REFEREE #1 — major revisions** (Referee #2's items follow in the next message)

*Exact theorem and trust base*

- **R1.1** — Correct the abstract, the introduction and §1.3: all three imply that all 22,028,942 implications were formalized in Lean. The referee calls the §1.3 sentence outright wrong.
- **R1.2** — State *early* (currently only on p. 12) that only a reduced generating set was formalized — 10,657 positive and 586,925 negative implications — with the rest obtained outside Lean. The referee is content with the decision itself, only with where it is disclosed.
- **R1.3** — State explicitly what must be trusted to believe all 22M are settled. Referee's guess: (i) the Lean kernel, (ii) the extension program, (iii) some process confirming all 22M are covered. Confirm or correct.
- **R1.4** — Clarify `full_entries.json` and explain its `"proven": false` entries, which the referee found confusing.
- **R1.5** — Give instructions for independently reconstructing the full implication table from the Lean-verified results, i.e. how to write one's own checker. The referee says that as it stands they cannot gain full confidence the graph is settled.
- **R1.6** — Say which shortcomings of Lean, or of proof assistants generally, made the split into formalized generating set + external deduction necessary.

*Discussion of the Lean 4 artifact*

- **R1.7** — Report the size of the formalization (lines) and compile times, and say which parts dominate the compile time — the ATP-derived parts or the manual ones.
- **R1.8** — Explain how the millions of theorem *statements* were generated, and why that process can be trusted.
- **R1.9** — Say which sections correspond to formalized results and which do not (referee notes §10).
- **R1.10** — Cite a specific repository tag or commit, making the intended Lean and Mathlib versions explicit.

*Discussion of the collaboration*

- **R1.11** — Add a detailed comparison with other large collaborative projects; the referee finds the paper's stated aim unsupported without it.
- **R1.12** — Discuss the Liquid Tensor Experiment: it predates PFR, was arguably the first blueprint-centred project, and was more centralized and hierarchical. Without this, the referee says the honest framing is that ETP experimentally confirmed the LTE model.
- **R1.13** — Treat BB(5) more accurately (coordinated on Discord and a wiki; largely without proof assistants, formalized after the fact) and discuss how those coordination choices compare with ours.
- **R1.14** — Discuss earlier large collaborations — Flyspeck, the odd order theorem, and more loosely the AFP and math-comp — and what distinguishes a large *mathematical* collaboration from large-scale software/proof-assistant development.
- **R1.15** — Add quantitative data on the collaboration itself: how the contributor pool varied over time, the shape of the curve along which results fell, and how the two correlate.

*Structure of the paper*

- **R1.16** — Reorganize into clearly separated parts: mathematics, methods of collaboration, tools. The referee finds the current structure chaotic and the ToC a mix of all three.
- **R1.17** — Move §§7.3.2, 7.3.3, 7.3.5, 7.3.6, 7.3.9 and Example 7.1 to an appendix. (§7 is 13 pages; §7.3 alone is 9.)
- **R1.18** — Shorten §11 and move it to an appendix: no formalized results, and the randomized control experiment was not run. *(See also R2.13, which instead asks §11 to justify itself.)*
- **R1.19** — Give more prominence to the observation that strong automation early in a project kills insights — currently buried in §14.1, and in the referee's view one of the most valuable remarks in the paper.

*Discussion of the choice of Lean 4*

- **R1.20** — Answer the *Virtues of a Formalization Project* question: did the choice of proof assistant or logical foundation crucially influence the formalization process? Referee identifies three factors: ATP capabilities, native computation, mathematical libraries.
- **R1.21** — Compare with Isabelle, where `sledgehammer` calls CVC4/Vampire natively and proof reconstruction is supported out of the box, against the custom reconstruction architecture we had to build.
- **R1.22** — Discuss how much `native_decide` would have sped up the counterexample computations of Figures 5 and 6 relative to `decide` / `decideFin!`, ideally with a build-time comparison.
- **R1.23** — Consider whether the 22M implication matrix could be validated inside a proof assistant by native computation — specifically, whether doing it in Rocq is feasible.
- **R1.24** — Address the referee's impression that Mathlib — usually the decisive reason to pick Lean — did not actually matter for this project.

*Miscellaneous*

- ~~**R1.M1**~~ **[DONE]** — p. 4: "proof assistant language Lean" is awkward; suggests "in the language of the proof assistant Lean". *(See also R2.T1.)*
- **R1.M2** — p. 11: the explanation of the custom commands (`equation`, `EquationX`, `LawX`) cannot be followed; add examples.
- **R1.M3** — p. 18: the paragraph beginning "ideally the environment" needs elaboration; unclear whether "practical implementations" means more than Lean.

========== END OF MESSAGE 1 — MESSAGE 2 of 2 starts below ==========

**Referee reports: TO DO list (2/2 — Referee #2)**

Continuing from the previous message. Same rules: claim an item by replying with its number, and use the same number when filling in `response.tex`. Referee #2's numbering below is their own, so it matches their report exactly.

**REFEREE #2 — minor revisions** ("highest recommendation for acceptance")

*Suggestions*

- ~~**R2.1**~~ **[DONE]** — Cite tools at first mention, not only where discussed topically: Lean (first mentioned p. 2 l. 9, first cited p. 17), Lean blueprint (p. 12 l. 11), `egg` and `duper` (p. 10 l. 26).
- ~~**R2.2**~~ **[DONE]** — Add missing citations for Mathlib (p. 10 l. 24), SAGE (p. 45 l. 36), GAP (p. 45 l. 37) and the GAP small group library (p. 45 l. 37). The referee supplies the canonical citation URLs for each.
- **R2.3** — p. 11 ll. 17–18 and p. 12 ll. 1–2: say which axioms are in the "small trusted set" enforced via `lean4checker`, and whether that set's consistency is well known. *(See also R1.3.)*
- **R2.4** — p. 12 ll. 3–9: give compile timing data for the full vs. reduced sets (minutes? hours? days?), say whether speeding it up has been attempted or investigated, and address whether the external transitivity/duality tools can be trusted — the referee finds it strange that we avoided `native_decide` on trust grounds but did not treat this extension with the same care. *(See also R1.1–R1.6, R1.7.)*
- **R2.5** — Replace the ten unlocated pointers to the ETP blueprint with citations to specific chapters/sections (fn. 4 p. 3; p. 7 l. 37; p. 8 ll. 11, 20; p. 9 l. 5; p. 30 l. 20; p. 33 l. 18; p. 52 ll. 19, 30; p. 67 l. 13). The blueprint is 27 chapters over 128 pages. Also replace the raw URLs on p. 64 ll. 15 and 40 with proper citations.
- **R2.6** — p. 26 ll. 6–7: the functional equations "become too complex" for $$n > 2$$ — say whether this exploration was by hand or automated, and whether "complex" is meant informally or in a formal complexity-theoretic sense.
- **R2.7** — p. 29 ll. 5–7: state explicitly whether the ATP/SAT automation for finding a greedy-extension rule set was actually implemented, and whether a Lean tactic or external program for it exists.
- **R2.8** — Remark 6.5, p. 35 l. 7: say whether matching invariants from larger-signature algebras were actually used in the formalization, and give an example if so.
- **R2.9** — fn. 14 p. 43: state the hardware used for the §7.3 timings and make clear which experiments shared hardware. Same for the "165 CPU-hours" search on p. 21 l. 2.
- **R2.10** — fn. 22 p. 53: provide evidence for the claim that this is the lowest-numbered law without full spectrum but with models of sizes 2 and 3.
- **R2.11** — p. 54 ll. 7–9: cite the article in preparation on spectra of higher-order laws. Same for the module claims (p. 54 ll. 25–27) and the extensions on p. 53 l. 3.
- **R2.12** — fn. 25 p. 57: describe the format and meaning of the linked JSON data.
- **R2.13** — §11: make explicit what advantage the CNN heuristic has over simply running Prover9 or Vampire 5.0 with tuned parameters for a fixed time and assuming failure means non-implication — which, by our own p. 48 ll. 1–9, is 100% accurate up to order 4. Also strengthen the evidence that the CNN is not learning transitivity, either via the extra tests described on p. 58 ll. 24–26 or via an interpretability analysis. *(See also R1.18, which instead asks §11 to be cut down.)*
- **R2.14** — p. 64 ll. 6–7: the qualifier "if one restricts to publicly available LLMs" implies non-public LLMs beat ATPs, with no evidence given. Either cite it, or list explicitly which LLM tools were tried and failed.

*Typos and minor comments*

- ~~**R2.T1**~~ **[DONE]** — Abstract l. 5: "all validated by the formal proof assistant language Lean" — validation is done by the kernel, not the language. Suggests "the formal proof assistant Lean" or "the interactive theorem prover Lean" (matching §4.7). *(See also R1.M1.)*
- ~~**R2.T2**~~ **[DONE]** — p. 3 l. 4: "entailment pre-ordering" → "entailment pre-order".
- ~~**R2.T3**~~ **[DONE]** — p. 4 l. 24: "contributions had to be entered in..." — "entered" is clunky; use "written" or "formalized".
- **R2.T4** **[DONE]** — p. 4 l. 30: note the Coq → Rocq rename here at first occurrence (currently only on p. 17 l. 12) and use "Rocq" thereafter.
- ~~**R2.T5**~~ **[DONE]** — p. 5 l. 10: "either 820 or 822 pairs" is confusing — if the gap is the two unknown-status implications, say so explicitly.
- **R2.T6** **[DONE]** — p. 10 l. 21: "generated as computer output" is redundant; drop "as computer output".
- ~~**R2.T7**~~ **[DONE]** — p. 10 l. 37: "two words in a free group" → "free **magma**", per the Lean definition of `EquationX`.
- ~~**R2.T8**~~ **[DONE]** — p. 12 l. 11 uses "LeanBlueprint", p. 13 l. 22 onward "Lean blueprint" — pick one.
- ~~**R2.T9**~~ **[DONE]** — p. 15 l. 30 uses "leanchecker", p. 11 l. 18 and p. 18 l. 15 use "lean4checker" — same tool or typo? If different, cite both.
- **R2.T10** — p. 17 ll. 9, 34: "relatively spartan" / "spartan language" — meaning unclear; consider another adjective.
- ~~**R2.T11**~~ **[DONE]** — p. 33 l. 15: if "versions of the greedy algorithm" means the abstract greedy algorithm of Theorem 5.12, reference the theorem.
- ~~**R2.T12**~~ **[DONE]** — p. 34 l. 9: remind the reader that free magmas were defined in §2.
- ~~**R2.T13**~~ **[DONE]** — p. 38 l. 18: "Clearly the term being rewritten is in..." → "Clearly, **if** the term being rewritten is in...".

========== END OF MESSAGE 2 ==========
