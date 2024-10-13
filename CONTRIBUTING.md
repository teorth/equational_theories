# Contributing to the Equational Theories Project

Thank you for your interest in contributing to the Equational Theories Project! We welcome contributions from all sources: human-generated contributions from either professional mathematicians or interested members of the public, as well as computer-generated contributions from programs in various languages, automated theorem provers, or modern AI tools. (In fact, one of the main goals of this project is to learn how such a diverse pool of contributions can effectively be combined with each other to advance a common objective.)

This guide provides detailed instructions on how to effectively and efficiently contribute to the project.

## Project Coordination

The project is managed using a [GitHub project dashboard](https://github.com/users/teorth/projects/1), which tracks tasks through various stages, from assignment to completion.

## How to Contribute

Contributions to the project are made through GitHub pull requests (PRs) that correspond to specific tasks outlined in the project's issues.
The following instructions detail the process for claiming and completing tasks.

### 1. Task Identification

- Tasks are posted as GitHub issues and can be found in the `Unclaimed Outstanding Tasks` column of the project dashboard.
- Each issue represents a specific task to be completed. The issue title and description contain relevant details and requirements.

### 2. Claiming a Task

- To claim a task, comment the single word `claim` on the relevant GitHub issue.
- If no other user is assigned, you will automatically be assigned to the task, and the issue will move to the `Claimed Tasks` column.
- You may only claim one task at a time. If you decide not to work on a task after claiming it, comment the single word `disclaim` on the issue. This will unassign you and return the issue to the `Unclaimed Outstanding Tasks` column, making it available for others to claim.

### 3. Working on the Task

Once you are assigned to an issue, begin working on the corresponding task. You should create a new branch from the `main` branch to develop your solution.

> [!WARNING]
> Before pushing any changes, you have the following options:
>
> - You might want to install the git pre-push hook by running:
>
>   ```bash
>   scripts/install_pre-push.sh
>   ```
>   This will automatically run checks before every push, reducing the risk of CI check failures.
>
> - You can manually run the following script before pushing, reducing the risk of CI check failures:
>
>   ```bash
>   scripts/run_before_push.sh
>   ```
>   This requires manual execution and won't stop the push if skipped.
>
> - You may push your changes without any safeguards, increasing the risk of CI check failures.

### 4. Submitting a Pull Request

- When you are ready to submit your solution, create a PR from your working branch to the project’s `main` branch.
- After submitting the PR, comment `propose #PR_NUMBER` on the original issue. This links your PR to the task, and the task will move to the `In Progress` column on the dashboard.
- A task can only move to `In Progress` if it has been claimed by the user proposing the PR.

### 5. Withdrawing or Updating a PR

- If you need to withdraw your PR, comment the single phrase `withdraw PR #PR_NUMBER` on the issue. The task will return to the `Claimed Tasks` column, but you will remain assigned to the issue.
- To submit an updated PR after withdrawal, comment `propose #NEW_PR_NUMBER` following the same process outlined in step 4.

### 6. Review Process

- After finishing the task and ensuring your PR is ready for review, comment the single word `awaiting-review` on the PR. This will add the `awaiting-review` label to your PR and move the task from `In Progress` to the `PRs in Review` column of the dashboard.
- The project maintainers will review the PR. They may request changes, approve the PR, or provide feedback.

### 7. Task Completion

- Once the PR is approved and merged, the task will automatically move to the `Completed` column.
- If further adjustments are needed after merging, a new issue will be created to track additional work.

### Additional Guidelines and Notes

1. Please adhere to the issue claiming process. If an issue is already assigned to another contributor, refrain from working on it without prior communication with the current claimant. This ensures a collaborative and respectful workflow that values each contributor’s efforts.
2. Be aware that this contribution process is still in an experimental phase. As a result, occasional issues and inefficiencies may arise. We are committed to continuously refining the process, and your constructive feedback is highly appreciated. You can share your thoughts and suggestions on the [Lean Zulip chat channel](https://leanprover.zulipchat.com/#narrow/stream/458659-Equational/).
3. Until the integration of sufficient CI automation, the management of the project dashboard is handled manually by the maintainers. We ask for your patience and understanding as we work to keep the process running smoothly.

## Discussion

The main discussion will be held in this [Lean Zulip channel](https://leanprover.zulipchat.com/#narrow/stream/458659-Equational/).  Some secondary discussion will also be held at [this blog post](https://terrytao.wordpress.com/2024/09/25/a-pilot-project-in-universal-algebra-to-explore-new-ways-to-collaborate-and-use-machine-assistance/).

## Lean files

The core Lean files are as follows:

- [`Magma.lean`](equational_theories/Magma.lean)  This contains the API for Magmas.
- [`FreeMagma.lean`](equational_theories/FreeMagma.lean)  Contains the API for free Magmas.
- [`Generated.lean`](equational_theories/Generated.lean)  This short file imports all the generated data sets.
- [`Visualization.lean`](equational_theories/Visualization.lean) A tool to visualize the implications within the Lean infoview.
- [`Equations/Basic.lean`](equational_theories/Equations/Basic.lean)  A list of selected equations of particular interest.
- [`Equations/All.lean`](equational_theories/Equations/All.lean)  The complete set of 4692 equational laws involving at most four magma operations (up to symmetry and relabeling).  It was generated using [this script](scripts/generate_eqs_list.py).  The subgraph equations are included as an import.  If you find an equation here of particular interest to study, consider transferring it to `Equations/Basic.lean`.  The equations are split up into five smaller files to assist compilation.
- [`Subgraph.lean`](equational_theories/Subgraph.lean)  This is the file for all results concerning the specific laws of interest.
- [`Homomorphisms.lean`](equational_theories/Homomorphisms.lean)  This file defines magma homomorphisms and magma isomorphisms and provides basic API for them.

Some technical Lean files:
- [`EquationalResult.lean`](equational_theories/EquationalResult.lean)  Introduces the `@[equational_result]` attribute, which adds metadata to allow for easier aggregation of implications. Also adds `conjecture` keyword, which is a variant of `proof_wanted` which keeps the metadata produced by `@[equational_result]` (but marking it as a conjecture).
- [`Closure.lean`](equational_theories/Closure.lean)  Contains code for computing the transitive closure of the implications.
- [`ParseImplications.lean`](equational_theories/ParseImplications.lean)  Tools to help parse implications within Lean.
- [`FactsSyntax.lean`](equational_theories/FactsSyntax.lean)  Support for assertions that a given magma obeys one set of laws but fails another.
- [`DecideBang.lean`](equational_theories/DecideBang.lean) Variants of the `decide` tactic with various hacks to speed up elaboration.
- [`Equations/Command.lean`](equational_theories/Equations/Command.lean)  Speeds up elaboration of equations.
- [`MemoFinOp.lean`](equational_theories/MemoFinOp.lean) Defines the macro `memoFinOp` that memoizes a function `f : Fin n → Fin n → Fin n`.
- [`Superposition.lean`](equational_theories/Superposition.lean) The `superpose` tactic, used in several automated proofs.

In addition to these files, contributors are welcome to add additional Lean files to the project in the [`equational_theories` folder](equational_theories) or one of its subfolders, to establish more facts about equations.  In order for your contributions to be easily detected by automated tools, please try to follow the following guidelines.

- If possible, use `Equations/Basic.lean` or `Equations/All.lean` as an import, in order to use our standardized names for the equational laws.  If you transfer an equation from `Equations/All.lean` to `Equations/Basic.lean`, please add the corresponding definition in the ["selected laws" chapter of the blueprint](https://teorth.github.io/equational_theories/blueprint/subgraph-eq.html) to keep this chapter aligned with the Lean codebase.  (The Lean codebase is used as the source of ground truth of equation status, but keeping the blueprint aligned will reduce confusion.)
- The standard form for an implication "Equation X implies Equation Y" is
`theorem EquationX_implies_EquationY (G: Type*) [Magma G] (h: EquationX G) : EquationY G`
- The standard form for an anti-implication "Equation X does not imply Equation Y" is `theorem EquationX_not_implies_EquationY : ∃ (G: Type) (_: Magma G), EquationX G ∧ ¬ EquationY G`.
- Add the `@[equational_result]` attribute to theorems of the above forms to make them visible to our analysis tools.
- NOTE: We are potentially in the process of updating our base representation of equations, so that the above guidance may change in the future.  See [this Zulip thread](https://leanprover.zulipchat.com/#narrow/stream/458659-Equational/topic/Equations.20vs.20Laws/near/473472323) for some relevant discussion.
- You are also encouraged to add `conjecture` versions of these theorems, for results that were obtained by hand or by some other automated tool whose output is not in the form of a Lean proof.  If you are creating such `conjecture` statements, consider adding a sketch of the proof as a comment in the Lean file.  We can then add tasks (via Github issues) to convert such `conjecture` statements into theorems. Note that you should add `@[equational_result]` to conjectures as well.  (Technical note: to avoid linter warnings, one can replace `h: EquationX G` with `_: EquationX G` in a `conjecture` implication.)
- To establish an equivalence between two Equations X and Y, split it into two implications "Equation X implies Equation Y" and "Equation Y implies Equation X" as above.
- To avoid collisions, implications and anti-implications should be placed inside a namespace specific to your Lean file.
- Consider adding a chapter to the blueprint corresponding to the Lean file, which can for instance detail the methodology used to generate the content of that file.  Also update [this CONTRIBUTING.md file](CONTRIBUTING.md) to add a link to your Lean file.
- For computer-generated Lean files, see the "Automated Proofs" section below.
- Lean files that are outside of the [`Generated`](equational_theories/Generated) folder are considered to be part of the human-curated Lean space; it is acceptable to put some auto-generated proofs outside of this folder, but they should be human-readable, and it is acceptable to have human editors optimize these proofs for readability, aesthetics, or other concerns.  On the other hand, Lean files within the [`Generated`](equational_theories/Generated) folder should be 100% computer generated, with no additional human curation.
- Add your Lean file to the top level [`equational_theories.lean`](equational_theories.lean) file so that it gets picked by the CI and automated implication extraction tools.

Contributions to the Lean codebase will pass through continuous integration (CI) checks that ensure that the Lean code compiles.  Contributors of Lean code are highly encouraged to interact with the [Lean Zulip channel](https://leanprover.zulipchat.com/#narrow/stream/458659-Equational/) to help coordinate their contributions and resolve technical issues.

Here is a list of human-contributed Lean files with mathematical content:
- [`InfModel.lean`](equational_theories/InfModel.lean)  Studies specific laws that are known to only have infinite non-trivial models.
- [`Completeness.lean`](equational_theories/Completeness.lean)  The Birkhoff completeness theorem.
- [`Compactness.lean`](equational_theories/Compactness.lean)  The compactness theorem.
- [`Counting.lean`](equational_theories/Counting.lean) Various theorems about counting laws.
- [`MagmaOp.lean`](equational_theories/MagmaOp.lean) Magma duality.
- [`Preorder.lean`](equational_theories/Preorder.lean) Preorder on magmas.
- [`CentralGroupoids.lean`](equational_theories/CentralGroupoids.lean)  Facts about central groupoids.
- [`OrderMetatheorem.lean`](equational_theories/OrderMetatheorem.lean) Metatheorems about the ordering relation on laws.
- [`SmallMagmas.lean`](equational_theories/SmallMagmas.lean) Results about very small magmas.
- [`Z3Counterexamples.lean`](equational_theories/Z3Counterexamples.lean) Counterexamples generated automatically from the Z3 prover.
- [`StringMagmas.lean`](equational_theories/StringMagmas.lean) Studies specific specific string magmas for counterexamples.


At present, the API for magmas only allows for theorems that study a finite number of individual equational laws at a time.  We plan to expand the API to also allow one to establish metatheorems about entire classes of equations.

## Blueprint

The [blueprint for the project](blueprint) is a human-readable record of the results established (in Lean or otherwise). Not every result generated by the project needs to be explicitly included in the blueprint, but ideally the most interesting results should be present, as well as descriptions of the methodology used to automatically generate large numbers of implications.

The blueprint is written in a special form of LaTeX that supports some integration with Lean.  In particular, definitions, theorems, and proofs of theorems can be tagged with additional macros:
- A macro `\lean{leanThm}` in the statement of a definition or theorem in the blueprint, will allow the blueprint to connect that definition or theorem to the corresponding Lean definition or theorem.  It is possible to link a blueprint theorem to multiple Lean theorems, e.g., `\lean{leanThm1, leanThm2}`.  Note that in some cases you will need to specify a namespace for the Lean theorem.
- The macro `\uses{ref1, ref2}` in the statement of a definition or theorem, or a proof of that theorem, will indicate that the relevant statement or proof uses the results in the blueprint that have the indicated `\label{}`s (in this case, `\label{ref1}` and `\label{ref2}`).  These will create edges in the [dependency graph](https://teorth.github.io/equational_theories/blueprint/dep_graph_document.html) of the blueprint.
- The macro `\leanok` in the statement of a definition or theorem indicates that the statement has been formalized.  The macro `\leanok` in the proof of a theorem indicates that the proof has been formalized.  This will create various colors in the nodes of the [dependency graph](https://teorth.github.io/equational_theories/blueprint/dep_graph_document.html) of the blueprint, as explained in the legend.

Contributors are welcome to make suggestions or additions to the blueprint, whose files can be found [here](blueprint/src/chapter). When adding a chapter, make sure to give the chapter a `\label` (to give that chapter a stable URLs, and not destabilize other chapter URLs), and add your chapter as an import to [`content.tex`](https://github.com/teorth/equational_theories/blob/main/blueprint/src/content.tex).

Contributions to the blueprint will pass through continuous integration (CI) checks that ensure that the blueprint compiles.  You may first wish to test that the [print version of the blueprint](blueprint/src/print.tex) compiles locally before pushing changes to the blueprint.  Also, if using the `\lean{}` macro to link to results in the Lean files, make sure that any namespace that the Lean result is stored in is stated.  If your Lean file was recently added, you may wish to check that it is recognized by [`equational_theories.lean`](equational_theories.lean), otherwise the blueprint will not be able to locate the results in that file.

## Scripts

Contributions in programming languages other than Lean are very welcome; the code for such contributions can be placed in [this directory](scripts).  It would probably be a good idea to announce such scripts on the [Zulip channel](https://leanprover.zulipchat.com/#narrow/stream/458659-Equational) for feedback and review.

When PR'ing a new script, consider also adding a brief link and description to the script in the [README.md](README.md) file under "Scripts", according to the main language of the script.

## Data

Output from code that is not Lean proofs (or `conjecture` claims in Lean) can be placed in the [data directory](data).  One can then update the [README.md](README.md) to list this new data set.  Note: if the data set is not fully validated (e.g., due to potential bugs in the code used to generate the data), please disclose this when reporting it to [README.md](README.md).  In the blueprint, one can add a chapter describing the data set, the code used to generate it, and any further comments (such as comparisons with other data sets).

## Automated Proofs

Proofs generated programmatically are also welcome. If you do this, you are encouraged to use the following format:
- Add a new directory for your new proof technique (e.g., "equational_theories/Generated/MyTechnique"), the automatically generated theorems ("equational_theories/Generated/MyTechnique/theorems"), and the corresponding source code ("equational_theories/Generated/MyTechnique/src") that generates these theorems.
- Then add a single Lean file (e.g., "equational_theories/Generated/MyTechnique.lean") that references all your theorems.
- Add a README (e.g., "equational_theories/Generated/MyTechnique/README.md") to document how to reproduce your automatically generated theorems (to the extent possible, for randomized algorithms).
- In [.gitattributes](.gitattributes) add `equational_theories/Generated/MyTechnique.lean linguist-generated` for all automatically generated files.
- In the file `equational_theories/Generated.lean` add the import line `import equational_theories.Generated.MyTechnique` replacing "MyTechnique" with the name of your folder.
- Consider adding to the blueprint to explain the automated proof technique used.
- Proofs of implications and non-implications should be reduced to the minimum required set. See [here](docs/graph_operations.md) for more.

## Images

Any images generated by the project can be placed in [this directory](images).

### Hasse diagrams

A particular type of image that is suitable for inclusion of this project are [Hasse diagrams](https://en.wikipedia.org/wiki/Hasse_diagram) of the implication graph.  Here are our orientation conventions for such diagrams (as voted on [here](https://leanprover.zulipchat.com/#narrow/stream/458659-Equational/topic/Metatheory.3A.20meta-thread/near/474084126)):

- The pre-ordering `≤` on laws is given by implication.  That is to say, `LawX ≤ LawY` means that `LawX` implies `LawY`, i.e., every magma that obeys `LawX`, also obeys `LawY`.
- The law `x=x` is a maximal element in this pre-ordering, and `x=y` is the minimal element.  Hence, in a Hasse diagram, `x=x` should be at the top, and `x=y` should be at the bottom.
- Note the confusing change in orientation of arrows: `LawX ≤ LawY` is equivalent to `LawX ⇒ LawY`.  As such, arrows should be _upward_, and the use of double lines to indicate implication (i.e., `⇒` instead of `→`) is strongly encouraged.  If implication arrows are not available, leaving the edges unoriented is acceptable.

Some of the legacy Hasse diagrams from the first few days of the project were oriented in a different way than that in the guidelines above.  References to such diagrams should be annotated to reflect this change of orientation.

## Other ways to contribute

- Have an idea for some future directions that this project can go in?  Please contribute your thoughts to the [Future directions thread](https://leanprover.zulipchat.com/#narrow/stream/458659-Equational/topic/Future.20directions/near/473388585) on Zulip.
- Want to share some feedback, impressions, or suggestions about the project?  You are encouraged to share them at the [Thoughts and impressions thread](https://leanprover.zulipchat.com/#narrow/stream/458659-Equational/topic/Thoughts.20and.20impressions.20thread/near/472978470) on the Zulip.
- Have a correction or remark on a specific component of the project?  Drop a comment in the [Zulip channel](https://leanprover.zulipchat.com/#narrow/stream/458659-Equational/), or on the relevant [PR](https://github.com/teorth/equational_theories/pulls) or [Issue](https://github.com/teorth/equational_theories/issues) on Github. Or implement the correction or remark directly as a pull request!
