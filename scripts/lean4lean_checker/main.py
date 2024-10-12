import os
import sys
from pathlib import Path
import shutil
import subprocess


class Lean4LeanChecker():
  def __init__(self) -> None:
    self.project_name = "equational_theories"
    self.l4l_repo_url = "https://github.com/digama0/lean4lean.git"
    self.toolchain_filename = Path('lean-toolchain')
    self.topPath = Path(os.getcwd())
    self.l4lSubPath = self.topPath.joinpath("./lean4lean")
    self.l4lBinPath = self.l4lSubPath.joinpath("./.lake/build/bin/lean4lean")
    self.lakePath = Path().home().joinpath(Path(".elan/bin/lake"))
    self.l4lBuildPath = self.l4lSubPath.joinpath('./.lake')
    self.l4lManifest = self.l4lSubPath.joinpath('./lake-manifest.json')
    self.repoToolchainPath = self.topPath.joinpath(self.toolchain_filename)
    self.l4lToolchainPath = self.l4lSubPath.joinpath(self.toolchain_filename)

  # Check if the toolchains of the project and lean4lean clone match
  def checkToolchainMatch(self):
    try:
      if not self.l4lSubPath.exists():
          raise Exception("lean4lean path does not exist")
      l4lToolchain = self.l4lToolchainPath.read_text()
      projectToolchain = self.repoToolchainPath.read_text()
      return l4lToolchain == projectToolchain
    except:
      print("lean4lean is not available yet")

  def try_update_l4l_toolchain(self):
    try:
      if not self.l4lSubPath.exists():
        raise Exception("lean4lean path not found")
      if self.checkToolchainMatch():
        print("The project's lean toolchain matches the toolchain of lean4lean")
        return
      else:
        print("The project's toolchain and lean toolchain are different\n")
        print("An attempt to update lean4lean to a matching toolchain will now begin")
        # switch to lean4lean directory
        os.chdir(self.l4lSubPath)

        # remove lake-manifest.json and ./.lake for lean4lean
        if self.l4lManifest.exists():
          os.remove(self.l4lManifest)
        if self.l4lBuildPath.exists():
          shutil.rmtree(self.l4lBuildPath)

        #get the project toolchain
        projectToolchain = self.repoToolchainPath.read_text()

        #write it to the lean-toolchain file of lean4lean
        self.l4lToolchainPath.write_text(projectToolchain)

        #run lake update
        val = subprocess.run([self.lakePath.as_posix(), "update"]).returncode
        if val == 0:
          print("Lean4lean's toolchain has been successfully updated")
          return
        else:
          print("There is a toolchain mismatch and lake cannot update lean4lean")

    except Exception as e:
      print(f"Failed to upgrade lean4lean.\n Cause: {e.args}\nCancelling lean4lean check and exiting")
      sys.exit(0)

  def remove_old_l4l(self):
    try:
      print("Removing any existing lean4lean clones\n")
      os.chdir(self.topPath)
      if self.l4lSubPath.exists():
        shutil.rmtree(self.l4lSubPath)
    except:
      print("Failed to remove old copies of lean4lean. The checker will not be run")
      sys.exit(0)

  def clone_l4l(self):
    try:
      subprocess.run(["git","clone", self.l4l_repo_url, self.l4lSubPath])
    except:
      print("Failed to clone lean4lean. The checker will not be run")
      sys.exit(0)

  def build_l4l(self):
    try:
      print("Building lean4lean CLI")
      os.chdir(self.l4lSubPath)
      build_ret = subprocess.run([self.lakePath.as_posix(), "build", "lean4lean"]).returncode
      if build_ret == 0:
        print("Lean4lean was successfully built\n")
      else:
        print("Lean4lean build was not successful. Lean4lean check will not be run. Exiting gracefully")
        raise Exception("lake build failure")

    except Exception:
      print("Lean4lean check will exit gracefully")
      sys.exit(0)

  def run(self):
    print("Lean4lean check action begins:\n")
    os.chdir(self.topPath)
    self.remove_old_l4l()
    self.clone_l4l()
    self.try_update_l4l_toolchain()
    self.build_l4l()

    os.chdir(self.topPath)
    print("Lean4lean check begins!\n")
    check_ret = subprocess.run([
      "env",
      "LEAN_NUM_THREADS=2",
      self.lakePath,
      "env",
      self.l4lBinPath.as_posix(),
      "--verbose",
      self.project_name
      ]).returncode
    if check_ret == 0:
      print("Lean4lean check was successful!!\n")
      self.remove_old_l4l()
      sys.exit(0)
    else:
      self.remove_old_l4l()
      sys.exit(1)

if __name__ == "__main__":
  checker = Lean4LeanChecker()
  checker.run()
