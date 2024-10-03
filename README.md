# Equational theory project

[![License: Apache 2.0](https://img.shields.io/badge/License-Apache_2.0-lightblue.svg)](https://opensource.org/licenses/Apache-2.0)
[![Website](https://img.shields.io/badge/Website-Ready-green)](https://teorth.github.io/equational_theories/)
[![Documentation](https://img.shields.io/badge/Documentation-Passing-green)](https://teorth.github.io/equational_theories/docs/)
[![Blueprint](https://img.shields.io/badge/Blueprint-WIP-blue)](https://teorth.github.io/equational_theories/blueprint/)
[![Paper](https://img.shields.io/badge/Paper-WIP-blue)](https://teorth.github.io/equational_theories/blueprint.pdf)
[![Zulip Channel](https://img.shields.io/badge/Zulip_Channel-Join-blue)](https://leanprover.zulipchat.com/#narrow/stream/458659-Equational)

The purpose of this project, launched on Sep 25, 2024, is to explore the space of equational theories of magmas, ordered by implication. To begin with we shall focus only on theories of a single equation, and specifically on the 4694 equational laws
involving at most four magma operations, up to symmetry and relabeling (here is the list [in Lean](equational_theories/AllEquations.lean) and in [plain text](https://github.com/teorth/equational_theories/blob/main/data/equations.txt)).  This creates 4694*(4694-1) = 22,028,942 implications that need to be proven or disproven, creating both "implications" and "anti-implications".

We will accumulate both "proven" and "conjectured" implications and anti-implications: proven assertions will be verified in the proof assistant language [Lean](https://www.lean-lang.org/), and "conjectured" assertions represent all claims (either human-generated or computer-generated) that have not yet been verified in Lean.  The current status of the project can be found on the [dashboard](https://teorth.github.io/equational_theories/dashboard/).

Some selected equations of interest are listed [here](equational_theories/Equations.lean) (in Lean form) and [here](https://teorth.github.io/equational_theories/blueprint/subgraph-eq.html) (in a human readable blueprint).  Examples include
- Equation 1: `x = x`.  The trivial law.
- Equation 2: `x = y`.  The singleton law.
- Equation 43: `x ∘ y = y ∘ x`.  The commutative law.
- Equation 46: `x ∘ y = z ∘ w`.  The constant law.
- Equation 168: `x = (y ∘ x) ∘ (x ∘ z)`.  The central groupoid law.
- Equation 4512: `x ∘ (y ∘ z) = (x ∘ y) ∘ z`.  The associative law.

Some automatically generated progress:
- Sep 28, 2024: [85 laws](equational_theories/Generated/Constant.lean) have been shown to be equivalent to the constant law [`Equation46`](https://teorth.github.io/equational_theories/blueprint/subgraph-eq.html#eq46), and [815 laws](equational_theories/Generated/Singleton.lean) have been shown to be equivalent to the singleton law [`Equation2`](https://teorth.github.io/equational_theories/blueprint/subgraph-eq.html#eq2).  Discussed in the blueprint [here](https://teorth.github.io/equational_theories/blueprint/sect0005.html).
- Sep 28, 2024: [18972 implications](equational_theories/Generated/SimpleRewrites/theorems) were established by simple rewrite laws.  Discussed in the blueprint [here](https://teorth.github.io/equational_theories/blueprint/sect0006.html).
- Sep 28, 2024: [4.2m implications proven by a transitive reduction of 15k theorems](equational_theories/Generated/TrivialBruteforce) were proven using simple rewrite proof scripts.  Discussed in the blueprint [here](https://teorth.github.io/equational_theories/blueprint/sect0007.html).
- Sep 29, 2024: [13.7m implications were conjectured to be refused by a collection of 515 magmas](equational_theories/Generated/All4x4Tables), collected by enumerating all 4^(4*4) operators and reducing to a covering set. Discussed in the blueprint [here](https://teorth.github.io/equational_theories/blueprint/sect0008.html).
- Oct 1, 2024: Another [~250k transitive implications](equational_theories/Generated/TrivialBruteforce) were proven by simple proof generation. Discussed in the blueprint [here](https://teorth.github.io/equational_theories/blueprint/sect0007.html).
- Oct 1, 2024: ~500k transitive implications were proven by [EquationSearch](equational_theories/Generated/EquationSearch), a custom tool that chooses hypotheses and leverages previously found implications to search by using the implied equations as substitutions.  Discussed in the blueprint [here](https://teorth.github.io/equational_theories/blueprint/sect0009.html).
- Oct 2, 2024: 86 (potentially) new implications in `Subgraph.lean` conclusively (i.e. in Lean) resolved using the [lean-egg tactic](https://github.com/marcusrossel/lean-egg). Some of these were simply missed by the transitive closure computation and technically already implied, but some were genuinely new.
- Oct 3, 2024: Another ~150k transitive implications were proven by [EquationSearch](equational_theories/Generated/EquationSearch) after improved capabilities were added.

Some statistics and data files from a given point in time:
- Sep 28, 2024: [A repository of unknown implications](https://github.com/amirlb/equational_theories/tree/unknown-implications), including all unknown implications, known equivalence classes, unknown implications modulo known equivalence, and only the strongest unknown implications.
- Sep 29, 2024: [Here](https://leanprover.zulipchat.com/user_uploads/3121/7ImuNeVLCa_gIsS8bHYIsokB/direct.tar.xz) is a text file of the (21K or so) direct implications proven to date, and [here](https://leanprover.zulipchat.com/user_uploads/3121/wnbVe2BZ1gamFjlMYFE7sIs9/closure.tar.xz) is the transitive closure of these implications (about 4.5m). More precisely, we have 21791 implications explicitly proven true, 4494090 additional relations implicitly proven true, 739207 explicitly proven false, 12764328 implicitly proven false, one additional relations explicitly conjectured true (and 64 more implicitly conjectured true), and 4014155 remaining implications which remain completely open.  Quotienting out by known equivalences, there are 3182453 open implications remaining.
- Oct 2, 2024: [A list of unknown implications whose converse is proven](https://github.com/amirlb/equational_theories/blob/extract_implications_equivalence_creators_data/scripts/equivalence_creators.json), i.e. implications that would reduce the number of equivalence classes of equations. At the time of creation we had 2969 equivalence classes. This file contains 4526 unknown implications, if all hold then it will reduce the number of equivalence classes to 1300.

Some visualizations from a given point in time:
- Sep 28, 2024: A (manually created) [Hasse diagram](https://en.wikipedia.org/wiki/Hasse_diagram) of the [dependencies obtained up to this date](equational_theories/Subgraph.lean) for the [selected equations of interest](equational_theories/Equations.lean) can be found [here](images/implications.png).  Note: the orientation in these legacy images is reversed from that in current guidance.
- Sep 28, 2024: A directed acyclic graph of automatically generated implications is [here](images/implications_092824.svg?raw=true): circular vertices are for nodes representing multiple equivalent equations and equations in green are from [`Subgraph.lean`](equational_theories/Subgraph.lean). Note: the orientation in these legacy images is reversed from that in current guidance.
- Oct 1, 2024: An image visualizing the graph of proved results can be found [here](images/outcomes_20241001.png). This was generated by [`outcomes_to_image.py`](scripts/outcomes_to_image.py).
- Oct 3, 2024: The current implications represented as a directed acylic graph were generated using [`generate_graphviz_graph.rb`](scripts/generate_graphviz_graph.rb) to visualize the [entire graph](images/implications_100324.svg?raw=true) and the smaller graph of equations [limited to 3 variables and three operations](images/implications_100324_var3_op3.svg?raw=true). As previously: circular vertices are for nodes representing multiple equivalent equations and vertices in green are from [`Subgraph.lean`](equational_theories/Subgraph.lean).

Current statistics and data files, updated automatically:
- [dashboard](https://teorth.github.io/equational_theories/dashboard/)

Current visualizations, updated automatically:
- coming soon!

For guidelines on how to contribute, see the [CONTRIBUTING.md](CONTRIBUTING.md) file.

## Building the project

To build this project after [installing Lean](https://www.lean-lang.org/lean-get-started) and cloning this repository, follow these steps:

```
% cd equational_theories/
% lake exe cache get
% lake build
```

## Links

- [Main web page](https://teorth.github.io/equational_theories/)
    - [Blueprint](https://teorth.github.io/equational_theories/blueprint/)
    - [Documentation](https://teorth.github.io/equational_theories/docs/)
    - [The Lean Zulip stream for the project](https://leanprover.zulipchat.com/#narrow/stream/458659-Equational/)
    - [Instructions on how to contribute](CONTRIBUTING.md)
- [A blog post describing the project.](https://terrytao.wordpress.com/2024/09/25/a-pilot-project-in-universal-algebra-to-explore-new-ways-to-collaborate-and-use-machine-assistance/), Sep 25, 2024.
- [Initial discussion on Zulip](https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/Proposing.20a.20universal.20algebra.20exploration.20using.20Lean), Sep 26, 2024.
- [Initial discussion on Mastodon](https://mathstodon.xyz/@tao/110736805384878353), Jul 18, 2023.
    - [Followup discussion on Mastodon](https://mathstodon.xyz/deck/@tao/113201989529992957), Sep 25, 2024.
- [The MathOverflow post that inspired the project](https://mathoverflow.net/questions/450930/is-there-an-identity-between-the-associative-identity-and-the-constant-identity), Jul 17, 2023.
    - [A related MathOverflow post](https://mathoverflow.net/questions/450890/is-there-an-identity-between-the-commutative-identity-and-the-constant-identity), Jul 16, 2023.
- [Scripts](scripts)
    - Lean
        - [`extract_implications`](scripts/extract_implications.lean) - extracts implications from one or more Lean files
    - Python
        - [`find_dual`](scripts/find_dual.py) - finds the dual of an equation
        - [`find_equation_id`](scripts/find_equation_id.py) - finds the equation number of an equation string
        - [`generate_eqs_list`](scripts/generate_eqs_list.py) - generates a list of equations
        - [`generate_graphviz_graph`](scripts/generate_graphviz_graph.rb) - generates a graphviz dot file, that can be used to create an implication graph
        - [`generate_image`](scripts/generate_image.py) - generates an image of implications
        - [`generate_most_wanted_list`](scripts/generate_most_wanted_list.py) - generates the "most wanted" implications
        - [`generate_z3_counterexample`](scripts/generate_z3_counterexample.py) - given an implication statement between two equations, calls Z3 to try to generate a counterexample
        - [`process_implications`](scripts/process_implications.py) - processes implications from one or more Lean files
    - Ruby
        - [`generate_graphviz_graph`](scripts/generate_graphviz_graph.rb) - creates a graphviz graph
        - [`graph`](scripts/graph.rb) - graph condensation tools
        - [`transitive_closure`](scripts/transitive_closure.rb) - computes the transitive closure of a set of implications
        - [`transitive_reduction`](scripts/transitive_reduction.rb) - finds a transitive reduction of a set of implications
- Automated provers for equational theories
    - [Prover9 and Mace4](https://www.cs.unm.edu/~mccune/prover9/)
        - [aa](https://github.com/gsfk/aa) - a project to use Prover9/Mace4 to brute force axioms for finite mathematical domains
    - [Vampire](https://en.wikipedia.org/wiki/Vampire_(theorem_prover))
    - [eprover](https://github.com/eprover/eprover)
    - [twee](https://nick8325.github.io/twee/)
    - [zipperposition](https://github.com/sneeuwballen/zipperposition)
    - [Z3](https://microsoft.github.io/z3guide/docs/logic/intro/)
    - [Knuckledragger](https://github.com/philzook58/knuckledragger)
    - A [blog post](https://www.philipzucker.com/tao_algebra/) by Philip Zucker testing many of the above provers on a [sample implication](https://teorth.github.io/equational_theories/blueprint/sect0003.html#387_implies_43) of this project.
    - ["Guided Equality Saturation"](https://dl.acm.org/doi/10.1145/3632900), Thomas Kœhler, Andrés Goens, Siddharth Bhat, Tobias Grosser, Phil Trinder, Michel Steuwer, Jan 5, 2024.
    - ["Rewrite Rule Inference Using Equality Saturation"](https://arxiv.org/abs/2108.10436), Chandrakana Nandi, Max Willsey, Amy Zhu, Yisu Remy Wang, Brett Saiki, Adam Anderson, Adriana Schulz, Dan Grossman, Zachary Tatlock, 23 Aug, 2021.
- Other tools
    - [egg - e-graphs good](https://egraphs-good.github.io/)
