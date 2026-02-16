from predictor2 import predict_implication_probability
from hard_triples import generated_triples
import math
import pandas as pd
import random
import os
from typing import Dict, Any

def log_loss(p: float, is_implication: bool) -> float:
    """
    Computes the log loss for a single prediction.

    p: The predicted probability that law_1 implies law_2.
    is_implication: The actual label (True if law_1 implies law_2, False otherwise).
    """
    epsilon = 1e-9
    p = max(epsilon, min(1.0 - epsilon, p))

    if is_implication:
        return math.log(p)
    else:
        return math.log(1.0 - p)

def evaluate( law1:str, law2:str, is_implication:bool, predictor) -> tuple[float, float]:
    """
    Evaluates the `predict_implication_probability` function against a single test case.

    The score is the log-likelihood (negated log loss) for this test case, which we aim
    to maximize. This rewards confident correct predictions and penalizes
    confident incorrect ones.
    """
    try:
        p = predictor(law1, law2)
        epsilon = 1e-9
        p = max(epsilon, min(1.0 - epsilon, p))

        log_loss_value = log_loss(p, is_implication)
        return log_loss_value, p
    except Exception as e:
        print(f"Error evaluating laws: {e}")
        return -20.0, 0.5

def print_evaluation( law1:str, law2:str, is_implication:bool, predictor):
    log_loss_value, p = evaluate(law1, law2, is_implication, predictor)
    print(f"Does {law1} imply {law2}? Predicted Probability: {p:.4f}, Actual: {is_implication}, Log Loss: {log_loss_value:.4f}")

def load_data(equations_file, implications_file):
    """
    Loads the equations list and the implications matrix.
    """
    print(f"Loading equations from {equations_file}...")
    with open(equations_file, 'r', encoding='utf-8') as f:
        # Read lines and strip whitespace
        equations = [line.strip() for line in f if line.strip()]

    print(f"Loading implications from {implications_file}...")
    # Load the CSV file without a header.
    # The file contains a dense matrix of integers.
    # We use pandas for efficient reading of large CSVs.
    try:
        df = pd.read_csv(implications_file, header=None)
        implications_matrix = df.values
    except Exception as e:
        print(f"Error loading CSV: {e}")
        return [], []

    return equations, implications_matrix

def generate_random_triple(equations, implications_matrix):
    """
    Generates a random triple [law_1, law_2, is_implication].

    law_1: String representation of the first law (premise).
    law_2: String representation of the second law (conclusion).
    is_implication: Boolean, True if law_1 implies law_2, False otherwise.
    """
    n_laws = len(equations)

    # Pick two random indices
    # Note: The matrix is 0-indexed.
    # Row i corresponds to Law i+1 (as the premise)
    # Column j corresponds to Law j+1 (as the conclusion)
    i = random.randint(0, n_laws - 1)
    j = random.randint(0, n_laws - 1)

    law_1 = equations[i]
    law_2 = equations[j]

    # Check the implication value in the matrix
    # A positive entry means law_1 implies law_2
    val = implications_matrix[i, j]
    is_implication = (val > 0)

    return [law_1, law_2, bool(is_implication)]

def load_files():
    # File paths (assumed to be in the current directory)
    EQUATIONS_FILE = 'equations.txt'
    IMPLICATIONS_FILE = 'raw_implications.csv'

    # Check if files exist
    if not os.path.exists(EQUATIONS_FILE) or not os.path.exists(IMPLICATIONS_FILE):
        print("Error: Please make sure 'equations.txt' and 'raw_implications.csv' are in the current directory.")
    else:
        # Load the data once
        equations, matrix = load_data(EQUATIONS_FILE, IMPLICATIONS_FILE)

        if len(equations) > 0 and matrix.shape[0] > 0:
            print(f"\nSuccessfully loaded {len(equations)} equations and implications matrix of shape {matrix.shape}.")
        return equations, matrix



def test_random():
    equations, matrix = load_files()

    for _ in range(100):
        [law_1, law_2, is_implication] = generate_random_triple(equations, matrix)
        print_evaluation(law_1, law_2, is_implication, predict_implication_probability)

def test_list(triples):
    for law_1, law_2, is_implication in triples:
        print_evaluation(law_1, law_2, is_implication, predict_implication_probability)

test_list(generated_triples)