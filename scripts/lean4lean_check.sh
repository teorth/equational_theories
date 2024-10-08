#!/usr/bin/env bash

set -e

OPTIONALLY_PINNED_LEAN4LEAN_COMMIT=""

EQ_ROOT=$(dirname "$(realpath "${BASH_SOURCE[0]}/../")")
EQ_TOOLCHAIN=$(cat "${EQ_ROOT}/lean-toolchain")
if [[ ${EQ_TOOLCHAIN} == "" ]]; then
    echo "ERROR. Invalid toolchain: ${EQ_TOOLCHAIN}"
    exit 1
fi
if [[ ! -d lean4lean/ ]]; then
    echo "⚪ Cloning lean4lean repo"
    git clone -q https://github.com/digama0/lean4lean.git
fi
echo "⚪ Building lean4lean"
cd lean4lean/
if [[ ${OPTIONALLY_PINNED_LEAN4LEAN_COMMIT} != "" ]]; then
    git checkout -q -B "pinned-lean4lean-${OPTIONALLY_PINNED_LEAN4LEAN_COMMIT}" "${OPTIONALLY_PINNED_LEAN4LEAN_COMMIT}"
fi
lake -q build lean4lean
cd ../
LEAN4LEAN_TOOLCHAIN=$(cat lean4lean/lean-toolchain)
if [[ ${LEAN4LEAN_TOOLCHAIN} != "${EQ_TOOLCHAIN}" ]]; then
    echo "ERROR. Toolchain mismatch: LEAN4LEAN_TOOLCHAIN=${LEAN4LEAN_TOOLCHAIN}, EQ_TOOLCHAIN=${EQ_TOOLCHAIN}"
    exit 1
fi
echo "⚪ Building project"
lake exe cache get > /dev/null
lake -q build
echo "⚪ Running lean4lean"
LEAN_NUM_THREADS=2 lake env lean4lean/.lake/build/bin/lean4lean --verbose equational_theories
echo "🟢 Verification succeeded"
