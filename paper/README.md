# Paper Plan

## Author list

This should be alphabetical (but see Appendix).

## Introduction

### Magmas and equational laws

Introduce the key definitions, list some past results.  Also mention OEIS sequences for number of equations with a given number of operations

Need to understand the state of the art of undecidability.  In particular, is it known that the `EquationX => Equation Y` problem for a single variable is undecidable in general?

### Equational Theories Project

Describe the initial aims and history of the project

### Results

I don't expect a large number of theoretically interesting results, but there may be some, that can be listed here, together with links to blueprint/lean etc. as needed.  Proofs can be deferred to an appendix.

* A new short Austin pair: Equation 3944 implies Equation 3588 [for finite magmas](https://teorth.github.io/equational_theories/blueprint/sect0002.html#finite_imp_3994_3588), but [not for infinite magmas](https://teorth.github.io/equational_theories/blueprint/sect0002.html#non_imp_3994_3588_thm)

## Mathematical foundations

Free magmas (including those relative to theories), completeness theorem, some abstract nonsense.  Confluence (unique simplification)

## Formal foundations

Describe the Lean framework we used to formalize the project, covering technical issues such as

* `Magma` operation symbol issues
* Syntax (`LawX`) versus semantics (`EquationX`)
* "Universe hell" issues
* Additional verification (axiom checking, Leanchecker, etc.)
* use of `conjecture` keyword

### Contributions to Mathlib

None yet, but presumably some of what we do is uploadable and should be mentioned.

## Project management

Shreyas Srinivas and Pietro Monticone have volunteered to take the lead on this section.

Discuss topics such as

* Project generation from [template](https://github.com/pitmonticone/LeanProject) (which will be extended with all the relevant project design and management lessons learnt during the development of this project)
* Github issue management ([labels](https://github.com/teorth/equational_theories/labels), [task management dashboard](https://github.com/users/teorth/projects/1))
* Use of continuous integration (project build, blueprint compilation, task status transition)
* Pre-push git hooks to save actions usage 
* Use of blueprint [small note, see #406: blueprint chapters should be given names for stable URLs)
* Use of Lean Zulip (e.g. use of polls)

Maybe give some usage statistics, e.g. drawing from https://github.com/teorth/equational_theories/actions/metrics/usage

### Handing scaling issues

Also mention some early human-managed efforts ("outstanding tasks", manually generated Hasse diagram, etc.) which suffices for the first one or two days of the project but rapidly became unable to handle the scale of the project.

Mention that some forethought in setting up a Github organizational structure with explicit admin roles etc. may have had some advantages if we had done so in the planning stages of the project, but it was workable without this structure (the main issue is that a single person - Terry - had to be the one to perform various technical admin actions).

Use of transitive reduction etc. to keep the Lean codebase manageable. Note that the project is large enough that one cannot simply accept arbitrary amounts of Lean code into the codebase, as this could make compilation times explode.

### Other design considerations
Explain what "trusting" lean really means in a large project. Highlight the kind of human issues that can interfere with this and how use of  tools like external checkers and PR reviews by people maintaining the projects still matters. Provide guidelines on good practices (such as  branch protection or watching out for spurious modifications in PRs, for example to the CI). Highlight the importance of following a proper process for discussing and accepting new tasks, avoiding overlaps etc. These issues are less likely to arise in projects with one clearly defined decision maker as in this case, and more likely to arise when the decision making has to be delegated to many maintainers.

## Finite magmas and other sources of counterexamples

Describe various sources of example magmas used in counterexamples, including the ones listed [here](https://teorth.github.io/equational_theories/blueprint/sect0005.html).  Note that linear magmas let one assign an "affine scheme" to each law that can be used to rule out many, but not all, implications.

* Discuss semi-automated creation of finite counterexamples (as discussed [here](https://leanprover.zulipchat.com/#narrow/stream/458659-Equational/topic/Counterexamples.20by.20Enumerating.20Words.20in.20Quotient.20Magma))
* Also note some "negative results" - classes of finite magmas that did not yield many additional refutations, e.g. commutative 5x5 magmas.

Discuss computational and memory efficiencies needed to brute force over extremely large sets of magmas.

## Metatheorems

List some notable metatheorems (e.g., duality).  Also include metatheorems that did not mature in time for deployment before the automated tools resolved most implications.  They could still be useful for future researchers!

## Automated theorem proving

Describe various automated theorem provers deployed in the project, with some statistics on performance

* Z3 prover
* Vampire
* More elementary substitutions
* egg

Any comparative study of semi-automated methods with fully automated ones?  In principle the semi-automated approach could be more automated using a script or "agent" to call various theorem provers.  See [this discussion](https://leanprover.zulipchat.com/#narrow/stream/458659-Equational/topic/A.20magma.20of.20order.20.3C.2013.20-.20for.20Equation2531.3F).

Draw upon the discussion [here](https://leanprover.zulipchat.com/#narrow/stream/458659-Equational/topic/Future.20of.20Using.20ATPs) on the various ways of integrating ATPs with Lean.  This project primarily used the least integrated approach, "Option 3", as it was fastest and required no dependencies on the other contributors, but it also has drawbacks.

## AI-assisted contributions

Right now not much - besides Claude assistance in coding front ends - but perhaps more will arise near the end of the project.

## User interface

Describe visualizations and explorer tools

## Statistics and experiments

Data analysis of the implication graph

* Mention the long chain 2 => 5 => 2499 => 2415 => 238 => 2716 => 28 => 2973 => 270 => 3 => 3715 => 375 => 359 => 4065 => 1 (discussed [here](https://leanprover.zulipchat.com/#narrow/stream/458659-Equational/topic/visualization.20of.20graph.20closure)).
* What are the "most difficult" implications?

Is there a way to generate a standard test set of implication problems of various difficulty levels?  Can one then use this to benchmark various automated and semi-automated methods?  Challenge: how does one automatically assign a difficulty level to a given (anti-)implication?

## Data management

Discuss how the data was handled, and how it will be stored going forward

## Reflections

Testimonies from individual participants (but perhaps this is more suited for a retrospective paper).  Utilize the [thoughts and reflections thread](https://leanprover.zulipchat.com/#narrow/stream/458659-Equational/topic/Thoughts.20and.20impressions.20thread).

* Automation often overtook the rate of human progress, for instance in developing metatheorems.  Does this create an opportunity cost?  Raised as a possible discussion point [here](https://leanprover.zulipchat.com/#narrow/stream/458659-Equational/topic/Future.20directions) by Zoltan Kocsis.

## Conclusions and future directions

Insights learned, future speculation.  Utilize the [discussion on future directions](https://leanprover.zulipchat.com/#narrow/stream/458659-Equational/topic/Future.20directions). Some ideas from that list:

* A database of triple implications (EquationX and EquationY imply EquationZ) - see also this [discussion](https://leanprover.zulipchat.com/#narrow/stream/458659-Equational/topic/Search.20space.20for.20.28EqX.20.E2.88.A7.20EqY.29.20.E2.86.92.20EqZ).
* Are there any equational laws that have no non-trivial finite models, but have [surjunctive](https://en.wikipedia.org/wiki/Surjunctive_group) models?
* Can we produce interesting examples of irreducible implications EquationX -> EquationY (no intermediate EquationZ can interpose)
* Degree of satisfiability results, e.g., if a central groupoid obeys the natural central groupoid axiom 99% of the time, is it a natural central groupoid?
* Kisielewicz's question: does 5105 have any infinite models?
* "Insight mining" the large corpus of automated proofs that have been generated.
* How machine-learnable is the implication graph?  


## Acknowlegements

Can thank the broader Lean Zulip community, and many small contributions from anyone who for whatever reason did not wish to be listed as an author

## Appendix: proofs of theoretical results

Here we add the interesting proofs mentioned in the results section; for really routine proofs we can just refer to blueprint/lean.

## Appendix: author contributions

List author contributions, possibly using the [CRediT categories](https://docs.google.com/document/d/1aJxrQXYHW5U6By3KEAHrx1Iho6ioeh3ohNsRMwsoGPM/edit#heading=h.bkwyjpjjzcq0) .  We may wish to elaborate on how we are interpreting each category at the beginning of the appendix, and possibly add subcategories to make more fine-grained distinctions.

Also add affiliations and grant acknowledgments.
