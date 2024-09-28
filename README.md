# Equational theory project

[![License: Apache 2.0](https://img.shields.io/badge/License-Apache_2.0-lightblue.svg)](https://opensource.org/licenses/Apache-2.0)
[![Website](https://img.shields.io/badge/Website-Ready-green)](https://teorth.github.io/equational_theories/)
[![Documentation](https://img.shields.io/badge/Documentation-Passing-green)](https://teorth.github.io/equational_theories/docs/)
[![Blueprint](https://img.shields.io/badge/Blueprint-WIP-blue)](https://teorth.github.io/equational_theories/blueprint/)
[![Paper](https://img.shields.io/badge/Paper-WIP-blue)](https://teorth.github.io/equational_theories/blueprint.pdf)
[![Zulip Channel](https://img.shields.io/badge/Zulip_Channel-Join-blue)](https://leanprover.zulipchat.com/#narrow/stream/458659-Equational)

The purpose of this project is to explore the space of equational theories of magmas, ordered by implication.  To begin with we shall focus only on theories of a single equation, which are listed [here](https://github.com/teorth/equational_theories/blob/main/equational_theories/AllEquations.lean).

A (manually created) graph of the dependencies obtained so far can be found [here](images/implications.png), current as of Sep 27 2024.

Links:

- [Main web page](https://teorth.github.io/equational_theories/)
    - [Blueprint](https://teorth.github.io/equational_theories/blueprint/)
    - [Documentation](https://teorth.github.io/equational_theories/docs/)
    - [The Lean Zulip stream for the project](https://leanprover.zulipchat.com/#narrow/stream/458659-Equational/)
- [A blog post describing the project.](https://terrytao.wordpress.com/2024/09/25/a-pilot-project-in-universal-algebra-to-explore-new-ways-to-collaborate-and-use-machine-assistance/), Sep 25 2024.
- [Initial discussion on Zulip](https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/Proposing.20a.20universal.20algebra.20exploration.20using.20Lean), Sep 26 2024.
- [Initial discusson on Mastodon](https://mathstodon.xyz/@tao/110736805384878353), Jul 18 2023.
    - [Followup discussion on Mastodon](https://mathstodon.xyz/deck/@tao/113201989529992957), Sep 25 2024.
- [The MathOverflow post that inspired the project](https://mathoverflow.net/questions/450930/is-there-an-identity-between-the-associative-identity-and-the-constant-identity), Jul 17 2023.
    - [A related MathOverflow post](https://mathoverflow.net/questions/450890/is-there-an-identity-between-the-commutative-identity-and-the-constant-identity), Jul 16 2023.
- Automated provers for equational theories
    - [Prover9 and Mace4](https://www.cs.unm.edu/~mccune/prover9/)
        - [aa](https://github.com/gsfk/aa) - a project to use Prover9/Mace4 to brute force axioms for finite mathematical domains
    - [Vampire](https://en.wikipedia.org/wiki/Vampire_(theorem_prover))
    - [eprover](https://github.com/eprover/eprover)
    - [twee](https://nick8325.github.io/twee/)
    - [zipperposition](https://github.com/sneeuwballen/zipperposition)
    - [Z3](https://microsoft.github.io/z3guide/docs/logic/intro/)
    - [Knuckledragger](https://github.com/philzook58/knuckledragger)
    - A [blog post](https://www.philipzucker.com/tao_algebra/) by Philip Zucker testing many of the above provers on a sample implication of this project.
    - ["Guided Equality Saturation"](https://dl.acm.org/doi/10.1145/3632900), Thomas Kœhler, Andrés Goens, Siddharth Bhat, Tobias Grosser, Phil Trinder, Michel Steuwer, Jan 5 2024.
    - ["Rewrite Rule Inference Using Equality Saturation"](https://arxiv.org/abs/2108.10436), Chandrakana Nandi, Max Willsey, Amy Zhu, Yisu Remy Wang, Brett Saiki, Adam Anderson, Adriana Schulz, Dan Grossman, Zachary Tatlock, 23 Aug 2021.
- Other tools
    - [egg - e-graphs good](https://egraphs-good.github.io/)
