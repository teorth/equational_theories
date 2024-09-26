# Lean 4 Project Template

[![License: Apache 2.0](https://img.shields.io/badge/License-Apache_2.0-lightblue.svg)](https://opensource.org/licenses/Apache-2.0)

This repository contains a template for blueprint-driven formalization projects in Lean 4.

## Tutorial Talk Video

This is the video recording of the tutorial talk I presented at the Hausdorff Research Institute for
Mathematics ([HIM](https://www.mathematics.uni-bonn.de/him)) in Bonn.

It was designed for mathematicians at all levels to provide a comprehensive introduction to the design,
management, and implementation of blueprint-driven formalisation projects in Lean, with almost no
prerequisite knowledge of Git, GitHub, continuous integration systems, and other technical tools.

[![HIM 2024 Tutorial Talk](https://img.youtube.com/vi/KyuyTsLgkMY/maxresdefault.jpg)](https://youtu.be/KyuyTsLgkMY)

## Install Lean 4

Ensure that you have a functioning Lean 4 installation. If you do not, please follow
the [Lean installation guide](https://leanprover-community.github.io/get_started.html).

## Use this Template

To create a new repository using this template, ensure you are on the correct repository page
([LeanProject](https://github.com/pitmonticone/LeanProject)) and then follow these steps:

1. Click the **Use this template** button located at the top right of the repository page.
2. Click the **Create a new repository** button.
3. Select the account or organization where you want to create it, choose a name for the new
repository, and click the **Create repository** button.

## Configure GitHub Pages

To set up GitHub Pages for your repository, follow these steps:

1. Go to the **Settings** tab of your repository.
2. In the left sidebar, click on the **Pages** section.
3. In the **Source** dropdown, select `GitHub Actions`.

## Clone this Repository

To clone this repository to your local machine, please refer to the relevant section of the
GitHub documentation [here](https://docs.github.com/en/repositories/creating-and-managing-repositories/cloning-a-repository).

## Repository Layout

The template repository is organized as follows (listing the main folders and files):

- [`.github`](.github) contains GitHub-specific configuration files and workflows.
    - [`workflows`](.github/workflows) contains GitHub Actions workflow files.
        - [`lint.yml`](.github/workflows/lint.yml) is the style lint workflow triggered on push
        and pull request events.
    - [`dependabot.yml`](.github/dependabot.yml) is the configuration file to automate CI dependency
    updates.
- [`.vscode`](.vscode) contains Visual Studio Code configuration files
    - [`extensions.json`](.vscode/extensions.json) recommends VS Code extensions for the project.
    - [`settings.json`](.vscode/settings.json) defines the project-specific settings for VS Code.
- [`Project`](Project) should contain the Lean code files.
    - [`Mathlib`](Project/Mathlib) should contain `.lean` files with declarations missing from
    existing Mathlib developments.
    - [`ForMathlib`](Project/ForMathlib) should contain `.lean` files with new declarations to
    be upstreamed to Mathlib.
    - [`Example.lean`](Project/Example.lean) is a sample Lean file.
- [`scripts`](scripts) contains scripts to update Mathlib ensuring that the latest version is
fetched and integrated into the development environment.
- [`.gitignore`](.gitignore) specifies files and folders to be ignored by Git.
and environment.
- [`CONTRIBUTING.md`](CONTRIBUTING.md) should provide the guidelines for contributing to the
project.
- [`lakefile.toml`](lakefile.toml) is the configuration file for the Lake build system used in
Lean projects.
- [`lean-toolchain`](lean-toolchain) specifies the Lean version and toolchain used for the project.

## Customize this Template

To tailor this template to your specific project, follow these steps:

1. If you don't have a Python environment, you can install one by following the instructions in the
[Python installation guide](https://www.python.org/downloads/).
1. Verify your Python installation by running:
    ```bash
    python3 --version
    ```
1. Verify your Pip installation by running:
    ```bash
    pip3 --version
    ```
1. Ensure your terminal is in the project directory by running the following command:
    ```bash
    cd path/to/your/project
    ```
1.	Execute the customization script by running:
    ```bash
    python3 scripts/customize_template.py NewProject
    ```
    where `NewProject` must be replaced by the name of your project.

The script [`customize_template.py`](scripts/customize_template.py) will automatically rename the
project folder and update the necessary files and configurations to match the new project name.

## Blueprint

### 0. Selected Real-World Collaborative Projects

- [Fermat's Last Theorem for Exponent 3](https://pitmonticone.github.io/FLT3/) led by Riccardo Brasca.
- [Polynomial Freiman-Ruzsa Conjecture](https://github.com/teorth/pfr) led by Terence Tao.
- [Fermat's Last Theorem](https://imperialcollegelondon.github.io/FLT/) led by Kevin Buzzard.
- [Carleson Operators on Doubling Metric Measure Spaces](http://florisvandoorn.com/carleson/) led by Floris van Doorn.
- [Bonn Collaborative Formalization Seminar Series in Analysis](https://github.com/fpvandoorn/BonnAnalysis) led by Floris van Doorn.
- [Prime Number Theorem and More](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd) led by Alex Kontorovich.
- [Infinity Cosmos](https://github.com/emilyriehl/infinity-cosmos) led by Emily Riehl.
- [Analytic Number Theory Exponent Database](https://github.com/teorth/expdb) led by Terence Tao.
- [Groupoid Model of Homotopy Type Theory](https://github.com/sinhp/GroupoidModelofHoTTinLean4) led by Sina Hazratpour.

For more examples of completed and ongoing Lean projects and libraries, please
see the [Lean Reservoir](https://reservoir.lean-lang.org).

### 1. Install Dependencies

To install the necessary dependencies, follow the instructions in the
[PyGraphViz installation guide](https://pygraphviz.github.io/documentation/stable/install.html).

### 2. Install LeanBlueprint Package

Assuming you have a properly configured Python environment, install LeanBlueprint by running:

```bash
pip install leanblueprint
```

If you have an existing installation of LeanBlueprint, you can upgrade to the latest version by
running:

```bash
pip install -U leanblueprint
```

### 3. Configure Blueprint

To set up the blueprint for your project, run:

```bash
leanblueprint new
```

Then, follow the prompts and answer the questions as you like, except for a few specific
questions which should be answered as indicated below to ensure compatibility with this template.

Respond affirmatively with `y` to the following prompt:

```console
Proceed with blueprint creation? [y/n]
```

Respond affirmatively with `y` to the following prompt:

```console
Modify lakefile and lake-manifest to allow checking declarations exist? [y/n] (y)
```

Respond affirmatively with `y` to the following prompt:

```console
Modify lakefile and lake-manifest to allow building the documentation? [y/n] (y):
```

If you want to generate a Jekyll-based home page for the project, respond
affirmatively with `y` to the following prompt:

```console
Do you want to create a home page for the project, with links to the blueprint, the API documentation and the repository? [y/n]:
```

Respond affirmatively with `y` to the following prompt:

```console
Configure continuous integration to compile blueprint? [y/n] (y):
```

For more details about the LeanBlueprint package and its commands, please refer to its
[documentation](https://github.com/PatrickMassot/leanblueprint/tree/master#starting-a-blueprint).

After configuring the blueprint, please wait for the GitHub Action workflow to finish.
You can keep track of the progress in the **Actions** tab of your repository.

## Selected Projects Using this Template

- [Infinity Cosmos](https://github.com/emilyriehl/infinity-cosmos) led by Emily Riehl.
- [Analytic Number Theory Exponent Database](https://github.com/teorth/expdb) led by Terence Tao.
- [Groupoid Model of Homotopy Type Theory](https://github.com/sinhp/GroupoidModelofHoTTinLean4) led by Sina Hazratpour.
- [Soundness of FRI](https://github.com/BoltonBailey/FRISoundness) led by Bolton Bailey.
- [Weil's Converse Theorem](https://github.com/CBirkbeck/WeilConverse) led by Chris Birkbeck.
- [Proofs from THE BOOK](https://github.com/mo271/formal_book) led by Moritz Firsching.
- [Automata Theory](https://github.com/shetzl/autth) led by Stefan Hetzl.
