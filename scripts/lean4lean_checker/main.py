import os
import sys
from pathlib import Path
import git
import shutil
import subprocess
# configuration options

l4l_repo_url = "git@github.com:digama0/lean4lean.git"
toolchain_filename = Path('lean-toolchain')
l4l_relpath = "./lean4lean"
l4l_binpath = "./.lake/build/bin/lean4lean"
lakePath = Path().home().joinpath(Path(".elan/bin/lake"))
project_name = "equational_theories"

def main():
  print("hello")
  ## construct absolute file paths
  pwd = Path(os.getcwd())
  mainToolchainPath = pwd.joinpath(toolchain_filename)
  l4lPath = pwd.joinpath(l4l_relpath)
  l4ltoolchainPath = l4lPath.joinpath(toolchain_filename)
  l4lBinPath = l4lPath.joinpath(l4l_binpath)

  ## Delete any existing copy of lean4lean first
  if l4lPath.exists():
    shutil.rmtree(l4lPath)

  ## Get a fresh clone of lean4lean
  repo = git.Repo.clone_from(l4l_repo_url, l4lPath)

  ##Compare toolchains
  localtoolchain = pwd.read_text()
  l4l_toolchain = l4ltoolchainPath.read_text()

  ## If toolchains don't match, exit without error, but message to contact maintainers
  if localtoolchain != l4l_toolchain:
    print("The local toolchain doesn't match the lean4lean toolchain")
    print("Contact the maintainers")
    exit(0)

  ## Otherwise build lean4lean
  os.chdir(l4lPath)
  buildret = subprocess.run([lakePath.as_posix(), "build", "lean4lean"]).returncode

  ## If build doesn't work, quit without error but contact maintainers
  if buildret != 0:
    print("lean4lean cannot build currently. Contact the maintainers")
    exit(0)

  ## check if build is successful and run lean4lean on the project
  if Path.exists(l4lBinPath):
    print("Successfully built lean4lean CLI")
    print("Starting lean4lean check on the project")
    os.chdir(pwd)
    ret = subprocess.run(["env", "LEAN_NUM_THREADS=2",lakePath, "env", l4lBinPath.as_posix(), project_name]).returncode
    print("lean4lean process returned ", ret)
    if ret == 0:
      print("The project is fine")
    shutil.rmtree(l4lPath)
    sys.exit(ret)
  else:
    print("lean4lean build unsuccessful")
    sys.exit(1)
  #Delete lean4lean


if __name__ == "__main__":
  main()
