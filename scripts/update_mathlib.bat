@echo off
rem Update Mathlib and the Lean toolchain.

rem Download the latest lean-toolchain file from the Mathlib4 repository
curl -L https://raw.githubusercontent.com/leanprover-community/mathlib4/master/lean-toolchain -o lean-toolchain

rem Update dependencies
lake pdate
