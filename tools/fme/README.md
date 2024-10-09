# Finite Magma Explorer

The Finite Magma Explorer allows you to input the operation table of a finite magma, and tells
you which equations the given magma obeys. You can access the Finite Magma Explorer from the
website.

**Features:**

* You can enter an operation table for a finite magma in a variety of human- and machine-readable formats.
* It can list all the equations your given magma satisfies, and gives counterexamples to all the equations
  that it doesn't. You can filter the dispalyed equations by their number or by their structure.
* Double-clicking an equation takes you to corresponding page in the Equation Explorer.
* If your magma refutes a previously unknown implication, it gives you instructions on how to
  contribute it to `All4x4Tables`.
* It's usually blazing fast.

**Building**

The tool is written in JavaScript and Elm. It gets the newest data from CI automatically.
See the `./build-elm.sh` script for build instructions.
