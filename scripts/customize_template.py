#!/usr/bin/env python3

import os
import shutil
import sys

def replace_text_in_file(filepath, old_text, new_text):
    """
    Replace all occurrences of old_text with new_text in the specified file.

    Arguments:
        filepath (str): The path to the file where text needs to be replaced.
        old_text (str): The text to be replaced.
        new_text (str): The text to replace with.
    """
    with open(filepath, 'r') as file:
        filedata = file.read()

    filedata = filedata.replace(old_text, new_text)

    with open(filepath, 'w') as file:
        file.write(filedata)

def rename_directory(old_name, new_name):
    """
    Rename a directory from old_name to new_name.

    Arguments:
        old_name (str): The current name of the directory.
        new_name (str): The new name for the directory.
    """
    if os.path.exists(old_name):
        os.rename(old_name, new_name)

# def remove_file(filepath):
#     """
#     Remove the specified file.

#     Arguments:
#         filepath (str): The path to the file to be removed.
#     """
#     if os.path.exists(filepath):
#         os.remove(filepath)

def main(project_name):
    """
    Perform all the customization steps for the template.

    Arguments:
        project_name (str): The name of the new project.
    """
    # Define paths to the files and directories to be modified
    lint_yml_path = '.github/workflows/lint.yml'
    project_folder = 'Project'
    example_file = os.path.join(project_folder, 'Example.lean')
    contributing_md = 'CONTRIBUTING.md'
    lakefile_toml = 'lakefile.toml'
    project_lean = 'Project.lean'

    # Replace 'Project' with the actual project name in the necessary files
    replace_text_in_file(lint_yml_path, 'Project', project_name)
    replace_text_in_file(lakefile_toml, 'Project', project_name)

    # Rename 'Project' folder to match the project name
    rename_directory(project_folder, project_name)

    # Notify the user to customize 'CONTRIBUTING.md' manually
    print(f"Please customize {contributing_md} manually to set up the contribution guidelines for your project.")

    # Rename 'Project.lean' to match the project name and update imports
    if os.path.exists(project_lean):
        new_project_lean = f"{project_name}.lean"
        os.rename(project_lean, new_project_lean)
        replace_text_in_file(new_project_lean, 'Project', project_name)

if __name__ == "__main__":
    # Check if the script is executed with the correct number of command-line arguments
    if len(sys.argv) != 2:
        print("Usage: python customize_template.py <ProjectName>")
        sys.exit(1)

    # Get the project name from the command-line arguments
    project_name = sys.argv[1]
    # Call the main function to perform the customization
    main(project_name)
