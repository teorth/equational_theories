import os
import subprocess

# Function to read commit IDs from a file
def load_commit_ids(file_path):
    commits = []
    with open(file_path, 'r') as file:
        for line in file:
            # Extract the first part of the line (the commit ID)
            commit_id = line.split()[0]
            commits.append(commit_id)
    return commits

# Function to run a command and capture its output
def run_command(command):
    result = subprocess.run(command, shell=True, capture_output=True, text=True)
    return result.stdout, result.stderr

# Load commits from the file 'commits.txt'
commit_file = 'order2'
commits = load_commit_ids(commit_file)

# Loop through each commit
for commit in commits:
    # Checkout to the specific commit
    print(f"Checking out commit {commit}...")
    checkout_cmd = f"git checkout --force {commit}"
    stdout, stderr = run_command(checkout_cmd)
    
    # Run the lake build command
    print("Running 'lake build'...")
    build_cmd = "lake build"
    stdout, stderr = run_command(build_cmd)
    
    if stderr:
        print(f"Error during 'lake build' for commit {commit}: {stderr}")
        continue

    # Run the lake exe command and save the output
    print("Running 'lake exe extract_implications outcomes --hist'...")
    exe_cmd = "lake exe extract_implications outcomes --hist"
    stdout, stderr = run_command(exe_cmd)
    
    if stderr:
        print(f"Error during 'lake exe extract_implications outcomes --hist' for commit {commit}: {stderr}")
        continue

    # Save the output to a file named after the commit
    output_file = f"{commit}.txt"
    with open(output_file, 'w') as f:
        f.write(stdout)

    print(f"Output saved to {output_file}")

print("All commits processed.")
