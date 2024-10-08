#!/usr/bin/env bash

set -e

PINNED_LEAN4LEAN_COMMIT="bba953139f34fdcecebb45f7287c8eb6b7a8ec60"

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
git checkout -q -B pinned-lean4lean-${PINNED_LEAN4LEAN_COMMIT} ${PINNED_LEAN4LEAN_COMMIT}
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
lake env lean4lean/.lake/build/bin/lean4lean --verbose equational_theories
echo "🟢 Verification succeeded"
