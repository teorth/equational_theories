#!/usr/bin/env bash

set -e

# Group logging using the ::group:: workflow command
echo "::group::leanchecker Output"

echo "Checking environment with leanchecker"
LEAN_NUM_THREADS=1 ~/.elan/bin/lake env leanchecker equational_theories

echo "::endgroup::"
echo
