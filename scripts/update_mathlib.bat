@echo off
rem Update Mathlib and the Lean toolchain.

rem Download the latest lean-toolchain file from the Mathlib4 repository
curl -L https://raw.githubusercontent.com/leanprover-community/mathlib4/master/lean-toolchain -o lean-toolchain

rem Update the Mathlib dependencies and ensure doc-gen is also updated
rem The `-Kenv=dev` flag ensures that the development environment is updated, including doc-gen
lake -Kenv=dev update

rem Retrieve and cache the latest Mathlib dependencies
lake exe cache get