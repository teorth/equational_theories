#!/usr/bin/env python3

# This script generates data that is graph-invariant, e.g. it is the same in the finite and general graphs.

import json
import os
import markdown
import time
import subprocess


eqs = []
N = 0
for file in ["1_999", "1000_1999", "2000_2999", "3000_3999", "4000_4694"]:
    for line in open(f"equational_theories/Equations/Eqns{file}.lean"):
        if ":=" in line:
            N += 1
            assert str(N) in line
            eqs.append("Equation" + str(N) + "[" + line.split(":=")[1].strip() + "]")
print("var equations = ", eqs)

print("var duals = ", open("data/duals.json").read())

def get_git_commit_hash():
    try:
        return (
            subprocess.check_output(["git", "rev-parse", "HEAD"])
            .decode("ascii")
            .strip()
        )
    except:
        return "Unable to retrieve Git hash"


# Get current UTC time as a timestamp
utc_timestamp = int(time.time())

# Get the current Git commit hash
commit_hash = get_git_commit_hash()

# Create a dictionary with the information
update_info = {"timestamp": utc_timestamp, "commit_hash": commit_hash}

print("var last_updated = ", json.dumps(update_info))


commentary = {}

for eq in os.listdir("commentary/"):
    if eq.startswith("Equation") and eq.endswith(".md"):
        commentary[eq.split(".")[0].replace("Equation", "")] = markdown.markdown(
            open("commentary/" + eq).read()
        )


print("var commentary = ", json.dumps(commentary))

smallest_magma_examples = {}
with open("data/smallest_magma_examples.txt") as f:
    for line in f:
        line = line.strip()
        if line:
            eq, table = line.split(maxsplit=1)
            smallest_magma_examples[int(eq)] = json.loads(table)

print("var smallest_magma_data = ", json.dumps(smallest_magma_examples))
