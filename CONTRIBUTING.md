# Contributing to Equational Theories

Anyone can contribute to the equational theories project! Specific guidelines for contributions are as follows.

## The Contributions Process
The project is coordinated using a [Github project dashboard](https://github.com/users/teorth/projects/1).
Contributions to the project take the form of Github pull requests that complete tasks. The detailed instructions are as follows:

1. Each task is posted as an issue that appears in the `Unclaimed Outstanding Task` column of the [dashboard](https://github.com/users/teorth/projects/1)
2. A contributor can lay claim to a task by commenting `claim` in the corresponding github issue. A user who wishes to drop their claim can comment `disclaim` on the issue.
3. If there is no other user assigned to the task, the user gets assigned to the issue. A `claim`ed issue moves to the `Claimed Tasks` column of the dashboard.
   * If you wish to give up on a task, please comment `disclaim` on it. This allows others to `claim` it. Only one github user can claim a task at a time.
5. The user creates a PR to solve the task and then comments `propose PR #xyz` under the issue. If the issue is already assigned to them, their PR is now linked to the issue. The PR now moves to the `In Progress` column of the dashboard and is shown with the linked PR.
   * _A PR proposal is only accepted if an issue has been claimed by the github user._
7. To withdraw their PR, a user can comment `withdraw PR #xyz`. The task moves to the `Claimed Tasks` column and the user remains assigned to the Github issue.
     * **Important**: _If a user wishes to propose a different PR, the user needs to first withdraw their previous PR (step 6) in one comment. In a subsequent comment, they may propose the new PR (as in step 4)._
8. Upon finishing the PR, the user may comment `awaiting-review` on the PR which is shown in the task view of the dashboard against the PR.
Maintainers review and merge it.
9. Merged tasks move to the `Completed Tasks` column of the dashboard.

### Some Rules and Notes
1. Please respect the issue claims. If an issue has been assigned to someone, please don't try to work on it simultaneously without discussing with the claimant first. This allows for a coordination process that respects every contributor's time and effort.
2. Please note that this process is still experimental. As such there are bound to be issues and bugs. We will improve this as we go along. Feedback is welcome on the [Lean Zulip chat channel](https://leanprover.zulipchat.com/#narrow/stream/458659-Equational/)
3.  Until the process above is automated with enough CI actions, maintainers of the project dashboard are manually handling things. So please be patient with us.

## Discussion

The main discussion will be held in this [Lean Zulip channel](https://leanprover.zulipchat.com/#narrow/stream/458659-Equational/).  Some secondary discussion will also be held at [this blog post](https://terrytao.wordpress.com/2024/09/25/a-pilot-project-in-universal-algebra-to-explore-new-ways-to-collaborate-and-use-machine-assistance/).

## Lean files

The core Lean files are as follows:

- [`Magma.lean`](equational_theories/Magma.lean)  This contains the API for Magmas.
- [`FreeMagma.lean`](equational_theories/FreeMagma.lean)  Contains the API for free Magmas.
- [`EquationalResults.lean`](equational_theories/EquationalResults.lean)  Introduces the `@[equational_result]` attribute, which adds metadata to allow for easier aggregation of implications. Also adds `conjecture` keyword, which is a variant of `proof_wanted` which keeps the metadata produced by `@[equational_result]` (but marking it as a conjecture).
- [`Closure.lean`](equational_theories/Closure.lean)  Contains code for computing the transitive closure of the implications.
- [`Generated.lean`](equational_theories/Generated.lean)  This short file imports all the generated data sets.
- [`EquationsCommand.lean`](equational_theories/EquationsCommand.lean)  A technical file to speed up elaboration of equations.
- [`ParseImplications.lean`](equational_theories/ParseImplications.lean)  Tools to help parse implications within Lean.
- [`Visualization.lean`](equational_theories/Visualization.lean) A tool to visualize the implications within the Lean infoview.
- [`Equations.lean`](equational_theories/Equations.lean)  A list of selected equations of particular interest, which we will refer to as "subgraph equations".
- [`AllEquations.lean`](equational_theories/AllEquations.lean)  The complete set of 4692 equational laws involving at most four magma operations (up to symmetry and relabeling).  It was generated using [this script](scripts/generate_eqs_list.py).  The subgraph equations are included as an import.  If you find an equation here of particular interest to study, consider transferring it to `Equations.lean` to give it the status of a subgraph equation.
- [`Subgraph.lean`](equational_theories/Subgraph.lean)  This is the file for all results concerning the subgraph equations specifically.

In addition to these files, contributors are welcome to add additional Lean files to the project in the [`equational_theories` folder](equational_theories) or one of its subfolders, to establish more facts about equations.  In order for your contributions to be easily detected by automated tools, please try to follow the following guidelines.

- If possible, use `Equations.lean` or `AllEquations.lean` as an import, in order to use our standardized names for the equational laws.
- The standard form for an implication "Equation X implies Equation Y" is
`theorem EquationX_implies_EquationY (G: Type*) [Magma G] (h: EquationX G) : EquationY G`
- The standard form for an anti-implication "Equation X does not imply Equation Y" is `theorem EquationX_not_implies_EquationY : ∃ (G: Type) (_: Magma G), EquationX G ∧ ¬ EquationY G`.
- Add the `@[equational_result]` attribute to theorems of the above forms to make them visible to our analysis tools.
- NOTE: We are potentially in the process of updating our base representation of equations, so that the above guidance may change in the future.  See [this Zulip thread](https://leanprover.zulipchat.com/#narrow/stream/458659-Equational/topic/Equations.20vs.20Laws) for some relevant discussion.
- You are also encouraged to add `conjecture` versions of these theorems, for results that were obtained by hand or by some other automated tool whose output is not in the form of a Lean proof.  If you are creating such `conjecture` statements, consider adding a sketch of the proof as a comment in the Lean file.  We can then add tasks (via Github issues) to convert such `conjecture` statements into theorems. Note that you should add `@[equational_result]` to conjectures as well.  (Technical note: to avoid linter warnings, one can replace `h: EquationX G` with `_: EquationX G` in a `conjecture` implication.)
- To establish an equivalence between two Equations X and Y, split it into two implications "Equation X implies Equation Y" and "Equation Y implies Equation X" as above.
- To avoid collisions, implications and anti-implications should be placed inside a namespace specific to your Lean file.
- Consider adding a chapter to the blueprint corresponding to the Lean file, which can for instance detail the methodology used to generate the content of that file.  Also update [this CONTRIBUTING.md file](CONTRIBUTING.md) to add a link to your Lean file.
- For computer-generated Lean files, see the "Automated Proofs" section below.
- Lean files that are outside of the [`Generated`](equational_theories/Generated) folder are considered to be part of the human-curated Lean space; it is acceptable to put some auto-generated proofs outside of this folder, but they should be human-readable, and it is acceptable to have human editors optimize these proofs for readability, aesthetics, or other concerns.  On the other hand, Lean files within the [`Generated`](equational_theories/Generated) folder should be 100% computer generated, with no additional human curation.

Contributions to the Lean codebase will pass through continuous integration (CI) checks that ensure that the Lean code compiles.  Contributors of Lean code are highly encouraged to interact with the [Lean Zulip channel](https://leanprover.zulipchat.com/#narrow/stream/458659-Equational/) to help coordinate their contributions and resolve technical issues.

Here is a list of human-contributed Lean files:
- [`InfModel.lean`](equational_theories/InfModel.lean)  Studies specific laws that are known to only have infinite non-trivial models.

At present, the API for magmas only allows for theorems that study a finite number of individual equational laws at a time.  We plan to expand the API to also allow one to establish metatheorems about entire classes of equations.

## Blueprint

The [blueprint for the project](blueprint) is a human-readable record of the results established (in Lean or otherwise). Not every result generated by the project needs to be explicitly included in the blueprint, but ideally the most interesting results should be present, as well as descriptions of the methodology used to automatically generate large numbers of implications.

The blueprint is written in a special form of LaTeX that supports some integration with Lean.  In particular, definitions, theorems, and proofs of theorems can be tagged with additional macros:
- A macro `\lean{leanThm}` in the statement of a definition or theorem in the blueprint, will allow the blueprint to connect that definition or theorem to the corresponding Lean definition or theorem.  It is possible to link a blueprint theorem to multiple Lean theorems, e.g., `\lean{leanThm1, leanThm2}`.  Note that in some cases you will need to specify a namespace for the Lean theorem.
- The macro `\uses{ref1, ref2}` in the statement of a definition or theorem, or a proof of that theorem, will indicate that the relevant statement or proof uses the results in the blueprint that have the indicated `\label{}`s (in this case, `\label{ref1}` and `\label{ref2}`).  These will create edges in the [dependency graph](https://teorth.github.io/equational_theories/blueprint/dep_graph_document.html) of the blueprint.
- The macro `\leanok` in the statement of a definition or theorem indicates that the statement has been formalized.  The macro `\leanok` in the proof of a theorem indicates that the proof has been formalized.  This will create various colors in the nodes of the [dependency graph](https://teorth.github.io/equational_theories/blueprint/dep_graph_document.html) of the blueprint, as explained in the legend.

Contributors are welcome to make suggestions or additions to the blueprint, whose files can be found [here](blueprint/src/chapter).

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

## Images

Any images generated by the project can be placed in [this directory](images).

## Other ways to contribute

- Have an idea for some future directions that this project can go in?  Please contribute your thoughts to the [Future directions thread](https://leanprover.zulipchat.com/#narrow/stream/458659-Equational/topic/Future.20directions) on Zulip.
- Want to share some feedback, impressions, or suggestions about the project?  You are encouraged to share them at the [Thoughts and impressions thread](https://leanprover.zulipchat.com/#narrow/stream/458659-Equational/topic/Thoughts.20and.20impressions.20thread) on the Zulip.
- Have a correction or remark on a specific component of the project?  Drop a comment in the [Zulip channel](https://leanprover.zulipchat.com/#narrow/stream/458659-Equational/), or on the relevant [PR](https://github.com/teorth/equational_theories/pulls) or [Issue](https://github.com/teorth/equational_theories/issues) on Github. Or implement the correction or remark directly as a pull request!
