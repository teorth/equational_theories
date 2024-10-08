#!/usr/bin/env python3

"""
Run lean4lean verification.
"""


import os
import pathlib
import subprocess
import sys


def main():
    """
    Main function that orchestrates the following tasks:
    1. Determine the root directory of the project.
    2. Verify the Lean toolchain version from the 'lean-toolchain' file.
    3. Clone the lean4lean repository if it does not exist.
    4. Build the lean4lean project.
    5. Ensure the toolchain versions match between the project and lean4lean.
    6. Build the main project.
    7. Run the lean4lean executable with the appropriate environment configuration.
    """

    # Determine the root directory of the project
    eq_root_directory = pathlib.Path(__file__).resolve().parent.parent
    eq_toolchain_path = eq_root_directory / "lean-toolchain"

    # Read the toolchain version from the lean-toolchain file
    if not eq_toolchain_path.exists():
        print(f"ERROR. {eq_toolchain_path} does not exist")
        sys.exit(1)
    eq_toolchain_string = eq_toolchain_path.read_text().strip()
    if not eq_toolchain_string:
        print(f"ERROR. Invalid toolchain: {eq_toolchain_string}")
        sys.exit(1)

    os.chdir(eq_root_directory)

    # Clone the lean4lean repository if it doesn't exist
    if not (eq_root_directory / "lean4lean").is_dir():
        print("⚪ Cloning lean4lean repo")
        subprocess.run(
            ["git", "clone", "-q", "https://github.com/digama0/lean4lean.git"],
            check=True,
        )

    # Build the lean4lean project
    print("⚪ Building lean4lean")
    os.chdir(eq_root_directory / "lean4lean")
    subprocess.run(["lake", "-q", "build", "lean4lean"], check=True)
    os.chdir(eq_root_directory)

    # Read the toolchain version from lean4lean's lean-toolchain file
    lean4lean_toolchain_path = eq_root_directory / "lean4lean" / "lean-toolchain"
    if not lean4lean_toolchain_path.exists():
        print(f"ERROR. {lean4lean_toolchain_path} does not exist")
        sys.exit(1)
    lean4lean_toolchain_string = lean4lean_toolchain_path.read_text().strip()

    # Ensure that the toolchain versions match
    if lean4lean_toolchain_string != eq_toolchain_string:
        print(
            f"ERROR. Toolchain mismatch: {lean4lean_toolchain_string=}, {eq_toolchain_string=}"
        )
        sys.exit(1)

    # Build the main project
    print("⚪ Building project")
    subprocess.run(
        ["lake", "exe", "cache", "get"], stdout=subprocess.DEVNULL, check=True
    )
    subprocess.run(["lake", "-q", "build"], check=True)

    # Run the lean4lean executable with the specified environment
    print("⚪ Running lean4lean")
    env = os.environ.copy()
    env["LEAN_NUM_THREADS"] = "2"
    lean4lean_executable = (
        eq_root_directory / "lean4lean" / ".lake" / "build" / "bin" / "lean4lean"
    )
    subprocess.run(
        ["lake", "env", str(lean4lean_executable), "--verbose", "equational_theories"],
        env=env,
        check=True,
    )

    print("🟢 Verification succeeded")


if __name__ == "__main__":
    try:
        main()
    except subprocess.CalledProcessError as e:
        print(f"ERROR. Command '{' '.join(e.cmd)}' exited with code {e.returncode}")
        sys.exit(e.returncode)
