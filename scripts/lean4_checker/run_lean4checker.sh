#!/bin/bash
set -e

# Script sourced from the following link and modified
# https://github.com/leanprover/lean-action/blob/main/scripts/run_lean4checker.sh

# Group logging using the ::group:: workflow command
echo "::group::lean4checker Output"
echo "Checking environment with lean4checker"

# clone lean4checker
echo "Cloning and building lean4checker"
git clone https://github.com/leanprover/lean4checker

# build and test lean4checker in a subshell
(
# detect toolchain version from lean-toolchain file
# assumes toolchain is of the form ".*:{VERSION}" (e.g., "leanprover/lean4:v4.8.0-rc1")
toolchain_version=$(< lean-toolchain cut -d: -f 2)
echo "Detected toolchain version: $toolchain_version"

# checkout version of lean4checker corresponding to toolchain version
cd lean4checker || exit
git config advice.detachedHead false # turn off git warning about detached head
git checkout "$toolchain_version"
cp ../lean-toolchain .

# build lean4checker and test lean4checker
~/.elan/bin/lake build
#./test.sh
)

# run lean4checker
echo "Running lean4checker"
~/.elan/bin/lake env lean4checker/.lake/build/bin/lean4checker equational_theories

echo "::endgroup::"
echo
