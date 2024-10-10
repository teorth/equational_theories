#!/usr/bin/env python3

import os
import json
import re
smallest_magma_examples_filename = "data/smallest_magma.txt"
small_magma_examples_filename = "data/small_magma.txt"
data_folders = [
  "equational_theories/Generated/All4x4Tables/data",
  "equational_theories/Generated/VampireProven",
  ]

def read_existing_small_magmas(filename, is_smallest_size):
  with open(filename) as f:
    for line in f:
      line = line.strip()
      if line:
        eq_id, table = line.split(maxsplit=1)
        yield (int(eq_id), json.loads(table), is_smallest_size)

def get_data_files():
  for data_folder in data_folders:
    for root, _, files in os.walk(data_folder):
      for file in files:
        if file.endswith(".txt") or file.endswith(".lean"):
          yield os.path.join(root, file)

def read_data_file(data_file):
  table = None
  proves = None
  with open(data_file) as f:
    for line in f:
      if data_file.endswith(".txt"):
        line = line.strip()
        if line.startswith("Table "):
          table = json.loads(line[len("Table "):])
        elif line.startswith("Proves "):
          proves = json.loads(line[len("Proves "):])
          for eq_id in proves:
            yield (eq_id, table)
          table = None
          proves = None
      elif data_file.endswith(".lean"):
        match = re.search(r"theorem Equation(\d+)_not_implies_Equation(\d+)", line)
        if match:
          proves = int(match.group(1))
        match = re.search(r"\[\s*\[(.*?)\]\s*\]", line)
        if match:
          table = json.loads(match.group(0))
          yield proves, table
          table = None
          proves = None

results = {}
for filename, is_smallest_size in ((smallest_magma_examples_filename, True), (small_magma_examples_filename, False)):
  for (eq_id, table, is_smallest_size) in read_existing_small_magmas(filename, is_smallest_size):
    if eq_id not in results:
      results[eq_id] = (table, is_smallest_size)

for data_file in get_data_files():
  print(data_file)
  found = 0
  for (eq_id, table) in read_data_file(data_file):
    found += 1
    if eq_id in results:
      existing_table, is_smallest_size = results[eq_id]
      if len(existing_table) > len(table):
        assert not is_smallest_size
        results[eq_id] = (table, len(table) == 6 and eq_id <= 4694 or len(table) == 2)
    else:
      results[eq_id] = (table, len(table) == 6 and eq_id <= 4694 or len(table) == 2)
  print(f"   found {found} entries")


with open(smallest_magma_examples_filename, "w") as smallest_magma_examples:
  with open(small_magma_examples_filename, "w") as small_magma_examples:
    for eq_id in sorted(results):
      table, is_smallest_size = results[eq_id]
      line = f"{eq_id} {table}\n"
      if is_smallest_size:
        smallest_magma_examples.write(line)
      else:
        small_magma_examples.write(line)
