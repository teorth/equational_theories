#!/usr/bin/env bash

set -e

# Script sourced from the following link and modified
# https://github.com/leanprover/lean-action/blob/main/scripts/run_lean4checker.sh

# Group logging using the ::group:: workflow command
echo "::group::leanchecker Output"

# https://leanprover.zulipchat.com/#narrow/channel/458659-Equational/topic/v4.2E29.20bump/near/593523380
echo "Skipping leanchecker due to excessive memory consumption for large computations(?)"
# echo "Checking environment with leanchecker"
# ~/.elan/bin/lake env leanchecker equational_theories

echo "::endgroup::"
echo
