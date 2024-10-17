---
# Feel free to add content and custom Front Matter to this file.
# To modify the layout, see https://jekyllrb.com/docs/themes/#overriding-theme-defaults

# layout: home
usemathjax: true
---

![Hasse diagram of selected equations](https://github.com/teorth/equational_theories/blob/main/images/subgraph.png?raw=true)

The purpose of this project, launched on Sep 25, 2024, is to explore the space of equational theories of [magmas](https://en.wikipedia.org/wiki/Magma_(algebra)), ordered by implication. To begin with we shall focus only on theories of a single equation, and specifically on the 4694 equational laws
involving at most four magma operations, up to symmetry and relabeling (here is the list [in Lean](https://github.com/teorth/equational_theories/tree/main/equational_theories/Equations/All.lean) and in [plain text](https://github.com/teorth/equational_theories/tree/main/data/equations.txt)).  This creates 4694*(4694-1) = 22,028,942 implications that need to be proven or disproven, creating both "implications" and "anti-implications".

We will accumulate both "proven" and "conjectured" implications and anti-implications: proven assertions will be verified in the proof assistant language [Lean](https://www.lean-lang.org/), and "conjectured" assertions represent all claims (either human-generated or computer-generated) that have not yet been verified in Lean.  The current status of the project can be found on the [dashboard](https://teorth.github.io/equational_theories/dashboard/).

Some selected equations of interest are listed [here](https://github.com/teorth/equational_theories/tree/main/equational_theories/Equations/Basic.lean) (in Lean form) and [here](https://teorth.github.io/equational_theories/blueprint/subgraph-eq.html) (in a human readable blueprint).  Examples include
- [Equation 1](https://teorth.github.io/equational_theories/implications/?1): `x = x`.  The trivial law.
- [Equation 2](https://teorth.github.io/equational_theories/implications/?2): `x = y`.  The singleton law.
- [Equation 43](https://teorth.github.io/equational_theories/implications/?43): `x ◇ y = y ◇ x`.  The commutative law.
- [Equation 46](https://teorth.github.io/equational_theories/implications/?46): `x ◇ y = z ◇ w`.  The constant law.
- [Equation 4512](https://teorth.github.io/equational_theories/implications/?4512): `x ◇ (y ◇ z) = (x ◇ y) ◇ z`.  The associative law.

[Here is a tour](https://github.com/teorth/equational_theories/wiki/Tour-of-selected-equations) of several selected equations, including the ones above.

Current statistics and data files, updated automatically:
- [dashboard](https://teorth.github.io/equational_theories/dashboard/)

Current visualizations, updated automatically:
- [Equation Explorer](https://teorth.github.io/equational_theories/implications) is a tool for exploring the graph of equation implications.
- [Finite Magma Explorer](https://teorth.github.io/equational_theories/fme) is a tool for exploring finite magmas and the equations they satisfy.
- [Graphiti](https://teorth.github.io/equational_theories/graphiti) is a tool for visualizing the implication graph.

For guidelines on how to contribute, see the [CONTRIBUTING.md](https://github.com/teorth/equational_theories/tree/main/CONTRIBUTING.md) file.  Participants are requested to abide by [our code of conduct](https://github.com/teorth/equational_theories/tree/main/CODE_OF_CONDUCT.md).

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
    - [Older progress](https://github.com/teorth/equational_theories/tree/main/docs/OLD_PROGRESS.md)
- [A blog post describing the project.](https://terrytao.wordpress.com/2024/09/25/a-pilot-project-in-universal-algebra-to-explore-new-ways-to-collaborate-and-use-machine-assistance/), Sep 25, 2024.
    - [The equational theories project: a brief tour](https://terrytao.wordpress.com/2024/10/12/the-equational-theories-project-a-brief-tour/), Oct 12, 2024 - a followup to the previous post.
- [Initial discussion on Zulip](https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/Proposing.20a.20universal.20algebra.20exploration.20using.20Lean/near/472914164), Sep 26, 2024.
- [Initial discussion on Mastodon](https://mathstodon.xyz/@tao/110736805384878353), Jul 18, 2023.
    - [Followup discussion on Mastodon](https://mathstodon.xyz/deck/@tao/113201989529992957), Sep 25, 2024.
- [The MathOverflow post that inspired the project](https://mathoverflow.net/questions/450930/is-there-an-identity-between-the-associative-identity-and-the-constant-identity), Jul 17, 2023.
    - [A related MathOverflow post](https://mathoverflow.net/questions/450890/is-there-an-identity-between-the-commutative-identity-and-the-constant-identity), Jul 16, 2023.
- [Data](https://github.com/teorth/equational_theories/tree/main/data)
    - [Text list of equations](https://github.com/teorth/equational_theories/tree/main/data/equations.txt).  [Larger list with equations of up to five operations](https://github.com/teorth/equational_theories/blob/main/data/eq_size5.txt)
    - [List of duals of equations](https://github.com/teorth/equational_theories/tree/main/data/dual_equations.md) ([JSON](https://github.com/teorth/equational_theories/blob/main/data/duals.json))
    - [The smallest magma obeying a given equation (up to N=5)](https://github.com/teorth/equational_theories/blob/main/data/smallest_magma.txt), if it exists (and [the magmas themselves](https://github.com/teorth/equational_theories/blob/main/data/smallest_magma_examples.txt))
    - To download the current state of the implication graph, see [this thread](https://leanprover.zulipchat.com/#narrow/stream/458659-Equational/topic/Database.20of.20implications).
- [Scripts](https://github.com/teorth/equational_theories/tree/main/scripts)
    - Shell
        - [`run_before_push`](https://github.com/teorth/equational_theories/tree/main/scripts/run_before_push.sh) - performs some of the CI checks, suitable for running just before pushing a new PR
    - Lean
        - [`extract_implications`](https://github.com/teorth/equational_theories/tree/main/scripts/extract_implications.lean) - extracts implications from one or more Lean files. This outputs the "ground truth" of implication data, for use by other scripts
    - Python
        - [`explore_magma`](https://github.com/teorth/equational_theories/tree/main/scripts/explore_magma.py) - test a given magma table against all or a subset of the equations in [`Equations/All.lean`](https://github.com/teorth/equational_theories/tree/main/equational_theories/Equations/All.lean)
        - [`find_dual`](https://github.com/teorth/equational_theories/tree/main/scripts/find_dual.py) - finds the dual of an equation
        - [`find_equation_id`](https://github.com/teorth/equational_theories/tree/main/scripts/find_equation_id.py) - finds the equation number of an equation string
        - [`find_powerful_theorems.py`](https://github.com/teorth/equational_theories/tree/main/scripts/find_powerful_theorems.py) - finds theorems that, if proved, would imply many others
        - [`generate_eqs_list`](https://github.com/teorth/equational_theories/tree/main/scripts/generate_eqs_list.py) - generates a list of equations
        - [`generate_image`](https://github.com/teorth/equational_theories/tree/main/scripts/generate_image.py) - generates an image of implications
        - [`generate_most_wanted_list`](https://github.com/teorth/equational_theories/tree/main/scripts/generate_most_wanted_list.py) - generates the "most wanted" implications
        - [`generate_z3_counterexample`](https://github.com/teorth/equational_theories/tree/main/scripts/generate_z3_counterexample.py) - given an implication statement between two equations, calls Z3 to try to generate a counterexample
        - [`process_implications`](https://github.com/teorth/equational_theories/tree/main/scripts/process_implications.py) - processes implications from one or more Lean files
    - Ruby
        - [`generate_graphviz_graph`](https://github.com/teorth/equational_theories/tree/main/scripts/generate_graphviz_graph.rb) - creates a graphviz graph
        - [`transitive_closure`](https://github.com/teorth/equational_theories/tree/main/scripts/transitive_closure.rb) - computes the transitive closure of a set of implications
        - [`transitive_reduction`](https://github.com/teorth/equational_theories/tree/main/scripts/transitive_reduction.rb) - finds a transitive reduction of a set of implications
        - [`graph`](https://github.com/teorth/equational_theories/tree/main/scripts/graph.rb) - graph library
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
    - [MiniZinc](https://www.minizinc.org/) - high-level constraint modeling language
    - [nauty](https://pallini.di.uniroma1.it/) - graph automorphism tool
    - [KBCV](http://cl-informatik.uibk.ac.at/software/kbcv/) - Knuth-Bendix completion visualizer
    - [Instagraph](https://github.com/yoheinakajima/instagraph) - knowledge graph generator
    - [Logic Programming in F#](https://github.com/jack-pappas/fsharp-logic-examples/tree/master) - Code and Examples from John Harrison's "Handbook of Practical Logic and Automated Reasoning", translated to F#
      - [Original code](https://www.cl.cam.ac.uk/~jrh13/atp/), written in OCaml
      - [Validated Knuth-Bendix code](https://www.cl.cam.ac.uk/~jrh13/atp/OCaml/completion.ml), written in OCaml
- Blog posts and media mentioning this project
    - "[We're Entering Uncharted Territory for Math"](https://www.theatlantic.com/technology/archive/2024/10/terence-tao-ai-interview/680153/), Matteo Wong, The Atlantic, Oct 4 2024.
    - "[On Math Platform](https://buildermath.substack.com/p/on-math-platform)", Michael Bucko, Substack von Michael, Oct 5 2024.
