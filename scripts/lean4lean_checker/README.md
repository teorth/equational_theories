## Lean4lean checker script

This script is meant to be executed from the project's root directory. Its primary purpose is to
be run as part of the CI. If you wish to run it locally, then the following steps will help you do
this.

```bash
cd <PROJECT_DIRECTORY>
python -m venv ./scripts/lean4lean_checker
./scripts/lean4lean_checker/bin/python3 ./scripts/lean4lean_checker/main.py
```

### How it works
1. The script pulls a fresh clone of lean4lean checker
2. It checks and tries to match the lean-toolchain of lean4lean.
  - If the toolchain does not match, it makes a best effort attempt to match toolchains and build
    lean4lean
  - If this also fails then the script gracefully exits without stopping the CI
3. If all the above steps are successful, the script runs lean4lean on the project.
  - Here alone, if there is an error, the script returns a non-zero exit code.
