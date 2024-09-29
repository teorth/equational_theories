# Contributing to Equational Theories

Anyone can contribute to the equational theories project! Specific guidelines for contributions are as follows.

## The Contributions Process
The project is coordinated using a [Github project dashboard](https://github.com/users/teorth/projects/1).
Contributions to the project take the form of Github pull requests that complete tasks. The detailed instructions are as follows:

1. Each task is posted as an issue that appears in the `Unclaimed Outstanding Task` column of the [dashboard](https://github.com/users/teorth/projects/1)
2. A contributor can lay claim to a task by commenting `claim` in the corresponding github issue. A user who wishes to drop their claim can comment `disclaim` on the issue.
3. If there is no other user assigned to the task, the user gets assigned to the issue. A `claim`ed issue moves to the `Claimed Tasks` column of the dashboard.
4. The user creates a PR to solve the task and then comments "propose PR #xyz" under the issue. If the issue is already assigned to them, their PR is now linked to the issue. The PR now moves to the `In Progress` column of the dashboard and is shown with the linked PR.
5. To withdraw their PR, a user can comment `withdraw PR #xyz`. The task moves to the `Claimed Tasks` column and the user remains assigned to the Github issue.
6. Upon finishing the PR, the user may comment `awaiting-review` on the PR which is shown in the task view of the dashboard against the PR.
Maintainers review and merge it.
7. Merged tasks move to the `Completed Tasks` column of the dashboard.

### Some Rules and Notes
1. Please respect the issue claims. If an issue has been assigned to someone, please don't try to work on it simultaneously without discussing with the claimant first. This allows for a coordination process that respects every contributor's time and effort.
2. Please note that this process is still experimental. As such there are bound to be issues and bugs. We will improve this as we go along. Feedback is welcome on the [Lean Zulip chat channel](https://leanprover.zulipchat.com/#narrow/stream/458659-Equational/)
3.  Until the process above is automated with enough CI actions, maintainers of the project dashboard are manually handling things. So please be patient with us.

## Discussion

The main discussion will be held in this [Lean Zulip channel](https://leanprover.zulipchat.com/#narrow/stream/458659-Equational/).  Some secondary discussion will also be held at [this blog post](https://terrytao.wordpress.com/2024/09/25/a-pilot-project-in-universal-algebra-to-explore-new-ways-to-collaborate-and-use-machine-assistance/).

## Lean files

The core Lean files are as follows:

- [`Magma.lean`](equational_theories/Magma.lean)  This contains the API for Magmas.
- [`Equations.lean`](equational_theories/Equations.lean)  A list of selected equations of particular interest, which we will refer to as "subgraph equations".
- [`AllEquations.lean`](equational_theories/AllEquations.lean)  The complete set of 4692 equational laws involving at most four magma operations (up to symmetry and relabeling).  It was generated using [this script](scripts/generate_eqs_list.py).  The subgraph equations are included as an import.  If you find an equation here of particular interest to study, consider transferring it to `Equations.lean` to give it the status of a subgraph equation.
- [`Subgraph.lean`](equational_theories/Subgraph.lean)  This is the file for all results concerning the subgraph equations specifically.

In addition to these files, contributors are welcome to add additional Lean files to the project in the [`equational_theories` folder](equational_theories) or one of its subfolders, to establish more facts about equations.  In order for your contributions to be easily detected by automated tools, please try to follow the following guidelines.

- If possible, use `Equations.lean` or `AllEquations.lean` as an import, in order to use our standardized names for the equational laws.
- The standard form for an implication "Equation X implies Equation Y" is
`theorem EquationX_implies_EquationY (G: Type*) [Magma G] (h: EquationX G) : EquationY G`
- The standard form for an anti-implication "Equation X does not imply Equation Y" is `theorem EquationX_not_implies_EquationY : ∃ (G: Type) (_: Magma G), EquationX G ∧ ¬ EquationY G`.
- Add the `@[equational_result]` attribute to theorems of the above forms to make them visible to our analysis tools.
- You are also encouraged to add `conjecture` versions of these theorems, for results that were obtained by hand or by some other automated tool whose output is not in the form of a Lean proof.  If you are creating such `conjecture` statements, consider adding a sketch of the proof as a comment in the Lean file.  We can then add tasks (via Github issues) to convert such `conjecture` statements into theorems.  (Technical note: to avoid linter warnings, one can replace `h: EquationX G` with `_: EquationX G` in a `conjecture` implication.)
- To establish an equivalence between two Equations X and Y, split it into two implications "Equation X implies Equation Y" and "Equation Y implies Equation X" as above.
- To avoid collisions, implications and anti-implications should be placed inside a namespace specific to your Lean file.
- Consider adding a chapter to the blueprint corresponding to the Lean file, which can for instance detail the methodology used to generate the content of that file.
- Computer-generated Lean files can go in the [`Generated`](https://github.com/teorth/equational_theories/tree/main/equational_theories/Generated) subfolder.  You are also welcome to create additional subfolders as appropriate.

Contributions to the Lean codebase will pass through continuous integration (CI) checks that ensure that the Lean code compiles.  Contributors of Lean code are highly encouraged to interact with the [Lean Zulip channel](https://leanprover.zulipchat.com/#narrow/stream/458659-Equational/) to help coordinate their contributions and resolve technical issues.

At present, the API for magmas only allows for theorems that study a finite number of individual equational laws at a time.  We plan to expand the API to also allow one to establish metatheorems about entire classes of equations.

## Blueprint

The [blueprint for the project](blueprint) is a human-readable record of the results established (in Lean or otherwise). Not every result generated by the project needs to be explicitly included in the blueprint, but ideally the most interesting results should be present, as well as descriptions of the methodology used to automatically generate large numbers of implications.

Contributors are welcome to make suggestions or additions to the blueprint, whose files can be found [here](blueprint/src/chapter).

Contributions to the blueprint will pass through continuous integration (CI) checks that ensure that the blueprint compiles.  You may first wish to test that the [print version of the blueprint](blueprint/src/print.tex) compiles locally before pushing changes to the blueprint.  Also, if using the `\lean{}` macro to link to results in the Lean files, make sure that any namespace that the Lean result is stored in is stated.  If your Lean file was recently added, you may wish to check that it is recognized by [`equational_theories.lean`](equational_theories.lean), otherwise the blueprint will not be able to locate the results in that file.

## Scripts

Contributions in programming languages other than Lean are very welcome; the code for such contributions can be placed in [this directory](scripts).  It would probably be a good idea to announce such scripts on the [Zulip channel](https://leanprover.zulipchat.com/#narrow/stream/458659-Equational) for feedback and review.

When PR'ing a new script, consider also adding a brief link and description to the script in the [README.md](README.md) file under "Scripts", according to the main language of the script.

## Data

Output from code that is not Lean proofs (or `conjecture` claims in Lean) can be placed in the [data directory](data).

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
