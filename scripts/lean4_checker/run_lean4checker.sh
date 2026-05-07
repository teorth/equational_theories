#!/usr/bin/env bash

set -e

# Script sourced from the following link and modified
# https://github.com/leanprover/lean-action/blob/main/scripts/run_lean4checker.sh

# Group logging using the ::group:: workflow command
echo "::group::lean4checker Output"
echo "Checking environment with leanchecker"

# run lean4checker
echo "Running lean4checker"
~/.elan/bin/lake env leanchecker equational_theories

echo "::endgroup::"
echo
