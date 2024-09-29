# Equational theory project

[![License: Apache 2.0](https://img.shields.io/badge/License-Apache_2.0-lightblue.svg)](https://opensource.org/licenses/Apache-2.0)
[![Website](https://img.shields.io/badge/Website-Ready-green)](https://teorth.github.io/equational_theories/)
[![Documentation](https://img.shields.io/badge/Documentation-Passing-green)](https://teorth.github.io/equational_theories/docs/)
[![Blueprint](https://img.shields.io/badge/Blueprint-WIP-blue)](https://teorth.github.io/equational_theories/blueprint/)
[![Paper](https://img.shields.io/badge/Paper-WIP-blue)](https://teorth.github.io/equational_theories/blueprint.pdf)
[![Zulip Channel](https://img.shields.io/badge/Zulip_Channel-Join-blue)](https://leanprover.zulipchat.com/#narrow/stream/458659-Equational)

The purpose of this project, launched on Sep 25, 2024, is to explore the space of equational theories of magmas, ordered by implication.  To begin with we shall focus only on theories of a single equation, and specifically on [this list](equational_theories/AllEquations.lean) of 4694 equations (all laws involving at most four magma operations, up to symmetry and relabeling).  This creates 4694*(4694-1) = 22,028,942 implications that need to be proven or disproven.

Some selected equations are listed [here](equational_theories/Equations.lean).  A (manually created) [Hasse diagram](https://en.wikipedia.org/wiki/Hasse_diagram) of the [dependencies obtained so far](equational_theories/Subgraph.lean) for these selected equations can be found [here](images/implications.png). A directed acyclic graph of automatically generated implications is [here](images/implications_092824.svg?raw=true): circular vertices are for nodes representing multiple equivalent equations and equations in green are from [`Subgraph.lean`](equational_theories/Subgraph.lean).

Some automatically generated progress:
- Sep 28, 2024: [85 laws](equational_theories/Generated/Constant.lean) have been shown to be equivalent to the constant law [`Equation46`](https://teorth.github.io/equational_theories/blueprint/subgraph-eq.html#eq46), and [815 laws](equational_theories/Generated/Singleton.lean) have been shown to be equivalent to the singleton law [`Equation2`](https://teorth.github.io/equational_theories/blueprint/subgraph-eq.html#eq2).
- Sep 28, 2024: [18972 implications](equational_theories/Generated/SimpleRewrites/theorems) were established by simple rewrite laws.
- Sep 28, 2024: [4.2m implication proven by a transitive reduction of 15k theorems](equational_theories/Generated/TrivialBruteforce) were proven using simple rewrite proof scripts.

Coming soon: statistics on how many implications have been established so far, and visualization tools to explore the implication graph.

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
- [A blog post describing the project.](https://terrytao.wordpress.com/2024/09/25/a-pilot-project-in-universal-algebra-to-explore-new-ways-to-collaborate-and-use-machine-assistance/), Sep 25, 2024.
- [Initial discussion on Zulip](https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/Proposing.20a.20universal.20algebra.20exploration.20using.20Lean), Sep 26, 2024.
- [Initial discussion on Mastodon](https://mathstodon.xyz/@tao/110736805384878353), Jul 18, 2023.
    - [Followup discussion on Mastodon](https://mathstodon.xyz/deck/@tao/113201989529992957), Sep 25, 2024.
- [The MathOverflow post that inspired the project](https://mathoverflow.net/questions/450930/is-there-an-identity-between-the-associative-identity-and-the-constant-identity), Jul 17, 2023.
    - [A related MathOverflow post](https://mathoverflow.net/questions/450890/is-there-an-identity-between-the-commutative-identity-and-the-constant-identity), Jul 16, 2023.
- Scripts
    - Lean
        - [`extract_implications`](scripts/extract_implications.lean) - extracts implications from one or more Lean files
    - Python
        - [`find_dual`](scripts/find_dual.py) - finds the dual of an equation
        - [`find_equation_id`](scripts/find_equation_id.py) - finds the equation number of an equation string
        - [`generate_eqs_list`](scripts/generate_eqs_list.py) - generates a list of equations
        - [`generate_image`](scripts/generate_image.py) - generates an image of implications
        - [`generate_most_wanted_list`](scripts/generate_most_wanted_list.py) - generates the "most wanted" implications
        - [`generate_z3_counterexample`](scripts/generate_z3_counterexample.py) - given an implication statement between two equations, calls Z3 to try to generate a counterexample
        - [`process_implications`](scripts/process_implications.py) - processes implications from one or more Lean files
    - Ruby
        - [`transitive_closure`](scripts/transitive_closure.rb) - computes the transitive closure of a set of implications
        - [`transitive_reduction`](scripts/transitive_reduction.rb) - finds a transitive reduction of a set of implications
        - [`transitive_reduction_exact`](scripts/transitive_reduction_exact.rb) - finds an exact transitive reduction of a set of implications
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
