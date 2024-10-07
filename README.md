# Equational theory project

[![License: Apache 2.0](https://img.shields.io/badge/License-Apache_2.0-lightblue.svg)](https://opensource.org/licenses/Apache-2.0)
[![Website](https://img.shields.io/badge/Website-Ready-green)](https://teorth.github.io/equational_theories/)
[![Documentation](https://img.shields.io/badge/Documentation-Passing-green)](https://teorth.github.io/equational_theories/docs/)
[![Blueprint](https://img.shields.io/badge/Blueprint-WIP-blue)](https://teorth.github.io/equational_theories/blueprint/)
[![Progress](https://teorth.github.io/equational_theories/dashboard/progress_badge.svg)](https://teorth.github.io/equational_theories/dashboard/)
[![Paper](https://img.shields.io/badge/Paper-WIP-blue)](https://teorth.github.io/equational_theories/blueprint.pdf)
[![Zulip Channel](https://img.shields.io/badge/Zulip_Channel-Join-blue)](https://leanprover.zulipchat.com/#narrow/stream/458659-Equational)

![Hasse diagram of selected equations](https://github.com/teorth/equational_theories/blob/main/images/subgraph.png?raw=true)

The purpose of this project, launched on Sep 25, 2024, is to explore the space of equational theories of [magmas](https://en.wikipedia.org/wiki/Magma_(algebra)), ordered by implication. To begin with we shall focus only on theories of a single equation, and specifically on the 4694 equational laws
involving at most four magma operations, up to symmetry and relabeling (here is the list [in Lean](https://github.com/teorth/equational_theories/tree/main/equational_theories/AllEquations.lean) and in [plain text](https://github.com/teorth/equational_theories/tree/main/data/equations.txt)).  This creates 4694*(4694-1) = 22,028,942 implications that need to be proven or disproven, creating both "implications" and "anti-implications".

We will accumulate both "proven" and "conjectured" implications and anti-implications: proven assertions will be verified in the proof assistant language [Lean](https://www.lean-lang.org/), and "conjectured" assertions represent all claims (either human-generated or computer-generated) that have not yet been verified in Lean.  The current status of the project can be found on the [dashboard](https://teorth.github.io/equational_theories/dashboard/).

Some selected equations of interest are listed [here](https://github.com/teorth/equational_theories/tree/main/equational_theories/Equations.lean) (in Lean form) and [here](https://teorth.github.io/equational_theories/blueprint/subgraph-eq.html) (in a human readable blueprint).  Examples include
- [Equation 1](https://teorth.github.io/equational_theories/implications/?1): `x = x`.  The trivial law.
- [Equation 2](https://teorth.github.io/equational_theories/implications/?2): `x = y`.  The singleton law.
- [Equation 43](https://teorth.github.io/equational_theories/implications/?43): `x ◇ y = y ◇ x`.  The commutative law.
- [Equation 46](https://teorth.github.io/equational_theories/implications/?46): `x ◇ y = z ◇ w`.  The constant law.
- [Equation 4512](https://teorth.github.io/equational_theories/implications/?4512): `x ◇ (y ◇ z) = (x ◇ y) ◇ z`.  The associative law.

(Note: in some legacy portions of this project, the magma operation was denoted `◦︎` instead of `◇`.)  [Here is a tour](https://github.com/teorth/equational_theories/wiki/Tour-of-selected-equations) of several selected equations, including the ones above.

Current statistics and data files, updated automatically:
- [dashboard](https://teorth.github.io/equational_theories/dashboard/)

Current visualizations, updated automatically:
- [Equation Explorer](https://teorth.github.io/equational_theories/implications) is a tool for exploring the graph of equation implications.
- An experimental tool to interactively explore a Hasse diagram of the graph is available [here](https://tsyrklevi.ch/eqviz/index.html?2)

For guidelines on how to contribute, see the [CONTRIBUTING.md](https://github.com/teorth/equational_theories/tree/main/CONTRIBUTING.md) file.  Participants are requested to abide by [our code of conduct](https://github.com/teorth/equational_theories/tree/main/CODE_OF_CONDUCT.md).

## Past progress

Some automatically generated progress:
- Sep 28, 2024: [85 laws](https://github.com/teorth/equational_theories/tree/main/equational_theories/Generated/Constant.lean) have been shown to be equivalent to the constant law ([Equation 46](https://teorth.github.io/equational_theories/implications/?46)), and [815 laws](https://github.com/teorth/equational_theories/tree/main/Generated/Singleton.lean) have been shown to be equivalent to the singleton law ([Equation2](https://teorth.github.io/equational_theories/implications/?2)).  Discussed in the blueprint [here](https://teorth.github.io/equational_theories/blueprint/sect0005.html).
- Sep 28, 2024: [18972 implications](https://github.com/teorth/equational_theories/tree/main/equational_theories/Generated/SimpleRewrites/theorems) were established by simple rewrite laws.  Discussed in the blueprint [here](https://teorth.github.io/equational_theories/blueprint/sect0006.html).
- Sep 28, 2024: [4.2m implications proven by a transitive reduction of 15k theorems](https://github.com/teorth/equational_theories/tree/main/equational_theories/Generated/TrivialBruteforce) were proven using simple rewrite proof scripts.  Discussed in the blueprint [here](https://teorth.github.io/equational_theories/blueprint/sect0007.html).
- Sep 29, 2024: [13.7m implications were conjectured to be refuted by a collection of 515 magmas](https://github.com/teorth/equational_theories/tree/main/equational_theories/Generated/All4x4Tables), collected by enumerating all 4^(4*4) operators and reducing to a covering set. Discussed in the blueprint [here](https://teorth.github.io/equational_theories/blueprint/sect0009.html).  (Update, Oct 3, 2024: these anti-implications are now formalized in Lean as theorems, and the number of implications established by this method increased to 13.8m.)
- Oct 1, 2024: Another [~250k transitive implications](https://github.com/teorth/equational_theories/tree/main/equational_theories/Generated/TrivialBruteforce) were proven by simple proof generation. Discussed in the blueprint [here](https://teorth.github.io/equational_theories/blueprint/sect00010.html).
- Oct 1, 2024: ~500k transitive implications were proven by [EquationSearch](https://github.com/teorth/equational_theories/tree/main/equational_theories/Generated/EquationSearch), a custom tool that chooses hypotheses and leverages previously found implications to search by using the implied equations as substitutions.  Discussed in the blueprint [here](https://teorth.github.io/equational_theories/blueprint/sect0011.html).
- Oct 2, 2024: 86 (potentially) new implications in [`Subgraph.lean`](https://github.com/teorth/equational_theories/tree/main/equational_theories/Subgraph.lean) conclusively (i.e. in Lean) resolved using the [lean-egg tactic](https://github.com/marcusrossel/lean-egg). Some of these were simply missed by the transitive closure computation and technically already implied, but some were genuinely new.
- Oct 3, 2024: Another ~150k transitive implications were proven by [EquationSearch](https://github.com/teorth/equational_theories/tree/main/equational_theories/Generated/EquationSearch) after improved capabilities were added.
- Oct 3, 2024: [~1m transitive implications](https://github.com/teorth/equational_theories/tree/main/equational_theories/Generated/MagmaEgg) were proven by a new custom tool that uses egraphs to find a proof and exports it to a Lean term
- Oct 5, 2024: 97% of the remaining unknown implications were resolved (transitively) by [Vampire](https://en.wikipedia.org/wiki/Vampire_(theorem_prover)), and then converted to a Lean proof using a custom script and a Lean elaborator implementing the deduction step of superposition calculus.


Some statistics and data files from a given point in time:
- Sep 28, 2024: [A repository of unknown implications](https://github.com/amirlb/equational_theories/tree/unknown-implications), including all unknown implications, known equivalence classes, unknown implications modulo known equivalence, and only the strongest unknown implications.
- Sep 29, 2024: [Here](https://leanprover.zulipchat.com/user_uploads/3121/7ImuNeVLCa_gIsS8bHYIsokB/direct.tar.xz) is a text file of the (21K or so) direct implications proven to date, and [here](https://leanprover.zulipchat.com/user_uploads/3121/wnbVe2BZ1gamFjlMYFE7sIs9/closure.tar.xz) is the transitive closure of these implications (about 4.5m). More precisely, we have 21791 implications explicitly proven true, 4494090 additional relations implicitly proven true, 739207 explicitly proven false, 12764328 implicitly proven false, one additional relations explicitly conjectured true (and 64 more implicitly conjectured true), and 4014155 remaining implications which remain completely open.  Quotienting out by known equivalences, there are 3182453 open implications remaining.
- Oct 2, 2024: [A list of unknown implications whose converse is proven](https://github.com/amirlb/equational_theories/blob/extract_implications_equivalence_creators_data/scripts/equivalence_creators.json), i.e. implications that would reduce the number of equivalence classes of equations. At the time of creation we had 2969 equivalence classes. This file contains 4526 unknown implications, if all hold then it will reduce the number of equivalence classes to 1300.
- Oct 4, 2024: Current dashboard status: 29248 explicitly proven, 7063191 implicitly proven, 605854 explicitly disproven, 13243426 implicitly disproven, 1120090 open (94.923% complete).  No conjectures at this time.  (A more formal time series of progress is planned.)
- Oct 5, 2024: Current dashboard status: 31023 explicitly proven, 8151818 implicitly proven, 581166 explicitly disproven, 13268299 implicitly proven, 29503 open (99.866% complete).  Note some pruning of redundant theorems occurred in the explicitly disproven theorems to improve compilation time.
- Oct 6, 2024: Current dashboard status (fixing an accounting error in previous dashboards): 31019 explicitly proven, 8147260 implicitly proven, 582094 explicitly disproven, 13272262 implicitly disproven, 1001 open (99.995% complete). Up to duality, only [8 implications needed](https://github.com/teorth/equational_theories/tree/main/data/outstanding_3op_implications.txt) to resolve the graph for laws of length 3, and [440 to resolve the entire graph](https://github.com/teorth/equational_theories/tree/main/data/unknowns_10_06.txt) (including 18 conjectured to be false by Vampire, marked with an asterisk)!
- Oct 7, 2024: Current dashboard status: 31019 explicitly proven, 8147260 implicitly proven, 582096 explicitly disproven, 13272262 implicitly disproven, 999 open. Deriving a minimal set of open implications is now partly automated and takes duality into account. With this, after resolving [387 implications](https://github.com/teorth/equational_theories/tree/main/data/unknowns_10_07.json) and formalizing Vampire disproofs and duality, the graph will be complete.

Some visualizations from a given point in time:
- Sep 28, 2024: A (manually created) [Hasse diagram](https://en.wikipedia.org/wiki/Hasse_diagram) of the [dependencies obtained up to this date](https://github.com/teorth/equational_theories/tree/main/equational_theories/Subgraph.lean) for the [selected equations of interest](https://github.com/teorth/equational_theories/tree/main/equational_theories/Equations.lean) can be found [here](https://github.com/teorth/equational_theories/tree/main/images/implications.png).  Note: the orientation in these legacy images is reversed from that in current guidance.
- Sep 28, 2024: A directed acyclic graph of automatically generated implications is [here](https://github.com/teorth/equational_theories/tree/main/images/implications_092824.svg?raw=true): circular vertices are for nodes representing multiple equivalent equations and equations in green are from [`Subgraph.lean`](https://github.com/teorth/equational_theories/tree/main/equational_theories/Subgraph.lean). Note: the orientation in these legacy images is reversed from that in current guidance.
- Oct 1, 2024: An image visualizing the graph of proved results can be found [here](https://github.com/teorth/equational_theories/tree/main/images/outcomes_20241001.png). This was generated by [`outcomes_to_image.py`](https://github.com/teorth/equational_theories/tree/main/scripts/outcomes_to_image.py).
- Oct 3, 2024: The current implications represented as a directed acyclic graph were generated using [`generate_graphviz_graph.rb`](https://github.com/teorth/equational_theories/tree/main/scripts/generate_graphviz_graph.rb) to visualize the [entire graph](https://github.com/teorth/equational_theories/tree/main/images/implications_100324.svg?raw=true) and the smaller graph of equations [limited to 3 variables and three operations](https://github.com/teorth/equational_theories/tree/main/images/implications_100324_var3_op3.svg?raw=true). As previously: circular vertices are for nodes representing multiple equivalent equations and vertices in green are from [`Subgraph.lean`](https://github.com/teorth/equational_theories/tree/main/equational_theories/Subgraph.lean).

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
    - [Instructions on how to contribute](https://github.com/teorth/equational_theories/tree/main/CONTRIBUTING.md)
    - [Code of conduct](https://github.com/teorth/equational_theories/tree/main/CODE_OF_CONDUCT.md)
    - [Wiki](https://github.com/teorth/equational_theories/wiki)
- [A blog post describing the project.](https://terrytao.wordpress.com/2024/09/25/a-pilot-project-in-universal-algebra-to-explore-new-ways-to-collaborate-and-use-machine-assistance/), Sep 25, 2024.
- [Initial discussion on Zulip](https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/Proposing.20a.20universal.20algebra.20exploration.20using.20Lean), Sep 26, 2024.
- [Initial discussion on Mastodon](https://mathstodon.xyz/@tao/110736805384878353), Jul 18, 2023.
    - [Followup discussion on Mastodon](https://mathstodon.xyz/deck/@tao/113201989529992957), Sep 25, 2024.
- [The MathOverflow post that inspired the project](https://mathoverflow.net/questions/450930/is-there-an-identity-between-the-associative-identity-and-the-constant-identity), Jul 17, 2023.
    - [A related MathOverflow post](https://mathoverflow.net/questions/450890/is-there-an-identity-between-the-commutative-identity-and-the-constant-identity), Jul 16, 2023.
- [Data](https://github.com/teorth/equational_theories/tree/main/data)
    - [Text list of equations](https://github.com/teorth/equational_theories/tree/main/data/equations.txt)
    - [List of duals of equations](https://github.com/teorth/equational_theories/tree/main/data/dual_equations.md)
    - [The smallest magma obeying a given equation (up to N=5)](https://github.com/teorth/equational_theories/tree/main/data/smallest_magma.txt), if it exists
- [Scripts](https://github.com/teorth/equational_theories/tree/main/scripts)
    - Shell
        - [`run_before_push`](https://github.com/teorth/equational_theories/tree/main/scripts/run_before_push.sh) - performs some of the CI checks, suitable for running just before pushing a new PR
    - Lean
        - [`extract_implications`](https://github.com/teorth/equational_theories/tree/main/scripts/extract_implications.lean) - extracts implications from one or more Lean files. This outputs the "ground truth" of implication data, for use by other scripts
    - Python
        - [`explore_magma`](https://github.com/teorth/equational_theories/tree/main/scripts/explore_magma.py) - test a given magma table against all or a subset of the equations in [`AllEquations.lean`](https://github.com/teorth/equational_theories/tree/main/equational_theories/AllEquations.lean)
        - [`find_dual`](https://github.com/teorth/equational_theories/tree/main/scripts/find_dual.py) - finds the dual of an equation
        - [`find_equation_id`](https://github.com/teorth/equational_theories/tree/main/scripts/find_equation_id.py) - finds the equation number of an equation string
        - [`find_powerful_theorems.py`](https://github.com/teorth/equational_theories/tree/main/scripts/find_powerful_theorems.py) - finds theorems that, if proved, would imply many others
        - [`generate_eqs_list`](https://github.com/teorth/equational_theories/tree/main/scripts/generate_eqs_list.py) - generates a list of equations
        - [`generate_graphviz_graph`](https://github.com/teorth/equational_theories/tree/main/scripts/generate_graphviz_graph.rb) - generates a graphviz dot file, that can be used to create an implication graph
        - [`generate_image`](https://github.com/teorth/equational_theories/tree/main/scripts/generate_image.py) - generates an image of implications
        - [`generate_most_wanted_list`](https://github.com/teorth/equational_theories/tree/main/scripts/generate_most_wanted_list.py) - generates the "most wanted" implications
        - [`generate_z3_counterexample`](https://github.com/teorth/equational_theories/tree/main/scripts/generate_z3_counterexample.py) - given an implication statement between two equations, calls Z3 to try to generate a counterexample
        - [`process_implications`](https://github.com/teorth/equational_theories/tree/main/scripts/process_implications.py) - processes implications from one or more Lean files
    - Ruby
        - [`generate_graphviz_graph`](https://github.com/teorth/equational_theories/tree/main/scripts/generate_graphviz_graph.rb) - creates a graphviz graph
        - [`graph`](https://github.com/teorth/equational_theories/tree/main/scripts/graph.rb) - graph condensation tools
        - [`transitive_closure`](https://github.com/teorth/equational_theories/tree/main/scripts/transitive_closure.rb) - computes the transitive closure of a set of implications
        - [`transitive_reduction`](https://github.com/teorth/equational_theories/tree/main/scripts/transitive_reduction.rb) - finds a transitive reduction of a set of implications
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
- Blog posts and media mentioning this project
    - "[We're Entering Uncharted Territory for Math"](https://www.theatlantic.com/technology/archive/2024/10/terence-tao-ai-interview/680153/), Matteo Wong, The Atlantic, Oct 4 2024.
    - "[On Math Platform](https://buildermath.substack.com/p/on-math-platform)", Michael Bucko, Substack von Michael, Oct 5 2024.
