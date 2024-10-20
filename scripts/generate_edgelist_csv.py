#!/usr/bin/env python3

"""
This script processes the JSON dataset containing equations and their implication outcomes
to generate an edge list, which is then saved to a CSV file.

The user is prompted to provide:
1. The path to the JSON input file containing the equations and outcomes.
2. The path to the CSV output file where the generated edge list will be saved.

The script performs the following steps:
1. Loads the JSON file containing the dataset.
2. Generates an edge list of (source, target, outcome) tuples.
3. Saves the edge list to the specified CSV file.

Usage:
    Run the script and provide the required file paths when prompted.

Example:
    $ scripts/generate_edgelist_csv.py
    Please enter the path to the JSON data file: data/tmp/outcomes.json
    Please enter the path to save the CSV file: data/tmp/edge_list.csv
    Edge list successfully saved to data/tmp/edge_list.csv
"""

import json
import csv


def load_json_file(file_path):
    """Load a JSON file from the specified path."""
    print(f"Loading JSON data from: {file_path}")
    try:
        with open(file_path, "r", encoding="utf-8") as file:
            data = json.load(file)
        print("JSON file loaded successfully.")
        return data
    except FileNotFoundError:
        print(f"Error: The file at {file_path} was not found.")
        raise
    except json.JSONDecodeError:
        print(f"Error: The file at {file_path} is not valid JSON.")
        raise


def generate_edge_list(data):
    """Generate an edge list from the given dataset."""
    print("Generating edge list from equations and outcomes...")
    edge_list = []

    for i, equation_x in enumerate(data["equations"]):
        for j, outcome in enumerate(data["outcomes"][i]):
            equation_y = data["equations"][j]
            edge_list.append((equation_x, equation_y, outcome))

    print(f"Edge list generated with {len(edge_list)} entries.")
    return edge_list


def save_edge_list_to_csv(edge_list, output_file_path):
    """Save the edge list to a CSV file."""
    print(f"Saving edge list to CSV file: {output_file_path}")
    try:
        with open(output_file_path, mode="w", newline="", encoding="utf-8") as file:
            writer = csv.writer(file)
            writer.writerow(["Source", "Target", "Outcome"])
            writer.writerows(edge_list)
        print(f"Edge list successfully saved to {output_file_path}")
    except Exception as e:
        print(f"Error while saving to CSV: {e}")
        raise


def main():
    """Main function to load data, generate the edge list, and save it to a CSV file."""
    # Ask user for input and output file paths
    input_data_path = input("Please enter the path to the JSON data file: ")
    output_data_path = input("Please enter the path to save the CSV file: ")

    # Load data, generate edge list, and save it to CSV
    data = load_json_file(input_data_path)
    edge_list = generate_edge_list(data)
    save_edge_list_to_csv(edge_list, output_data_path)


if __name__ == "__main__":
    # Execute the script
    main()
