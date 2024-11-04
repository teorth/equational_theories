#!/usr/bin/env python3

"""Generates a plotly scatter plot to visualize equivalence class statistics.

Example usage:

$ lake exe extract_implications outcomes > /tmp/out.json
$ python scripts/implication_stats.py /tmp/out.json --outfile stats.html
"""
from __future__ import annotations

import argparse
import enum
import json
import logging
import sys
from pathlib import Path
from typing import Final

import numpy as np
import numpy.typing as npt
import pandas as pd
import plotly.express as px
import plotly.graph_objects as go
from scipy.sparse.csgraph import connected_components

LOGGER: Final = logging.getLogger(__name__)


@enum.unique
class EquationDataColumn(enum.Enum):
    """Known columns for the equation DataFrame."""

    EQUATION_NUMBER = "Equation Number"
    STATEMENT = "Statement"
    DISTINCT_VARIABLE_COUNT = "Distinct Variable Count"
    OPERATION_COUNT = "Operation Count"
    IMBALANCE = "Imbalance"
    EQUIVALENCE_CLASS = "Equivalence Class"
    IMPLICATION_COUNT = "Implication Count"
    IMPLIED_BY_COUNT = "Implied By Count"
    OUTCOMES_INDEX = "_outcomes_index"


@enum.unique
class EquivalenceClassDataColumn(enum.Enum):
    """Known columns for the equivalence class DataFrame."""

    CLASS_NUMBER = "Class Number"
    STATEMENT = "Statement"
    CLASS_SIZE = "Class Size"
    MINIMUM_DISTINCT_VARIABLE_COUNT = "Minimum Distinct Variable Count"
    MINIMUM_OPERATION_COUNT = "Minimum Operation Count"
    MINIMUM_IMBALANCE = "Minimum Imbalance"
    OUTCOMES_INDEX = "_outcomes_index"
    IMPLICATION_COUNT = "Implication Count"
    IMPLIED_BY_COUNT = "Implied By Count"


def parse_args() -> argparse.Namespace:
    """Parse command line arguments."""
    parser = argparse.ArgumentParser(
        prog="ImplicationStats",
        description="Render implication statistics using plotly.",
    )
    parser.add_argument(
        "file",
        type=Path,
        help="json file containing output of `lake exe extract_implications outcomes",
    )
    parser.add_argument(
        "--outfile",
        type=Path,
        default=None,
        help="Name of output file",
    )

    return parser.parse_args()


def load_equation_strings() -> list[str]:
    """Load equation strings from file."""
    equations_path = Path(__file__).parent.parent / "data" / "equations.txt"

    LOGGER.info("Attempting to load equation strings from %s", equations_path)
    with equations_path.open(encoding="UTF-8") as file:
        equation_strings = [line.rstrip("\n") for line in file if line.strip()]
    LOGGER.info("Successfully loaded equation strings.")

    return equation_strings


def equation_implies(proof_state: str) -> bool:
    """Determine whether an equation implies another equation.

    Uses the proof state of the potential implication to answer whether an equation
    implies another equation. Assumes no unknown implications are true.
    """
    return proof_state in {
        "explicit_proof_true",
        "implicit_proof_true",
        "explicit_conjecture_true",
        "implicit_conjecture_true",
    }


def load_outcomes(
    outcomes_path: Path,
) -> tuple[npt.NDArray[np.bool], npt.NDArray[np.int64]]:
    """Load outcomes from file."""
    LOGGER.info("Attempting to load outcomes from %s", outcomes_path)
    with outcomes_path.open(encoding="UTF-8") as file:
        data = json.load(file)
    LOGGER.info("Successfully loaded outcomes.")

    outcomes: list[list[str]] = data["outcomes"]
    outcomes_binary = [
        [equation_implies(proof_state) for proof_state in equation_proof_states]
        for equation_proof_states in outcomes
    ]

    equations: list[str] = data["equations"]
    equation_ids = list(map(name_to_id, equations))

    return np.array(
        outcomes_binary,
        dtype=np.bool,
    ), np.array(
        equation_ids,
        dtype=np.int64,
    )


def name_to_id(name: str) -> int:
    """Extract the canonical equation number from the equation name."""
    return int(name.removeprefix("Equation"))


def equivalence_classes(outcomes: npt.NDArray[np.bool]) -> npt.NDArray[np.int32]:
    """Assign each equation to an equivalence class, based on outcomes."""
    mutual_implications = outcomes & outcomes.T
    _, equivalence_class_indices = connected_components(
        csgraph=mutual_implications,
        directed=False,
        connection="strong",
    )

    return equivalence_class_indices


def operations_imbalance(statement: str) -> int:
    """Calculate measure of how imbalanced the equation is."""
    sides = statement.split("=")
    count1 = sides[0].count("◇")
    count2 = sides[1].count("◇")

    return max(count1, count2) - min(count1, count2)


def construct_equivalence_class_data(
    outcomes: npt.NDArray[np.bool],
    equation_ids: npt.NDArray[np.int64],
    equation_strings: list[str],
) -> pd.DataFrame:
    """Construct a dataframe with interesting data on each equivalence class."""
    LOGGER.info("Processing data for %s equations...", len(outcomes))

    equation_strings = [equation_strings[eid - 1] for eid in equation_ids]
    distinct_variable_counts = [
        len({c for c in equation_string if c.isalpha()})
        for equation_string in equation_strings
    ]
    operations_count = [
        equation_string.count("◇") for equation_string in equation_strings
    ]

    imbalance = [
        operations_imbalance(equation_string) for equation_string in equation_strings
    ]

    eqc = equivalence_classes(outcomes)

    equation_data = pd.DataFrame(
        data={
            EquationDataColumn.EQUATION_NUMBER.value: equation_ids,
            EquationDataColumn.STATEMENT.value: pd.Series(
                equation_strings,
                dtype="string",
            ),
            EquationDataColumn.DISTINCT_VARIABLE_COUNT.value: distinct_variable_counts,
            EquationDataColumn.OPERATION_COUNT.value: operations_count,
            EquationDataColumn.IMBALANCE.value: imbalance,
            EquationDataColumn.EQUIVALENCE_CLASS.value: eqc,
            EquationDataColumn.IMPLICATION_COUNT.value: np.sum(outcomes, axis=1),
            EquationDataColumn.IMPLIED_BY_COUNT.value: np.sum(outcomes, axis=0),
            EquationDataColumn.OUTCOMES_INDEX.value: range(len(outcomes)),
        },
    )

    equivalence_class_data = equation_data.groupby(
        EquationDataColumn.EQUIVALENCE_CLASS.value,
    ).agg(
        **{
            EquivalenceClassDataColumn.CLASS_NUMBER.value: pd.NamedAgg(
                column=EquationDataColumn.EQUATION_NUMBER.value,
                aggfunc="first",
            ),
            EquivalenceClassDataColumn.STATEMENT.value: pd.NamedAgg(
                column=EquationDataColumn.STATEMENT.value,
                aggfunc="first",
            ),
            EquivalenceClassDataColumn.MINIMUM_DISTINCT_VARIABLE_COUNT.value: pd.NamedAgg(
                column=EquationDataColumn.DISTINCT_VARIABLE_COUNT.value,
                aggfunc="min",
            ),
            EquivalenceClassDataColumn.MINIMUM_OPERATION_COUNT.value: pd.NamedAgg(
                column=EquationDataColumn.OPERATION_COUNT.value,
                aggfunc="min",
            ),
            EquivalenceClassDataColumn.MINIMUM_IMBALANCE.value: pd.NamedAgg(
                column=EquationDataColumn.IMBALANCE.value,
                aggfunc="min",
            ),
            EquivalenceClassDataColumn.OUTCOMES_INDEX.value: pd.NamedAgg(
                column=EquationDataColumn.OUTCOMES_INDEX.value,
                aggfunc="first",
            ),
        },
    )

    # Filter outcomes by equivalence class
    needed_indices = equivalence_class_data[
        EquivalenceClassDataColumn.OUTCOMES_INDEX.value
    ]
    outcomes = outcomes[needed_indices, :]
    outcomes = outcomes[:, needed_indices]

    equivalence_class_data[EquivalenceClassDataColumn.IMPLICATION_COUNT.value] = np.sum(
        outcomes,
        axis=1,
    )
    equivalence_class_data[EquivalenceClassDataColumn.IMPLIED_BY_COUNT.value] = np.sum(
        outcomes,
        axis=0,
    )

    LOGGER.info("Data processed.")

    return equivalence_class_data


def make_scatter(equivalence_class_data: pd.DataFrame) -> go.Figure:
    """Construct a scatter plot from the equivalence class data."""
    LOGGER.info("Creating scatter plot...")

    color_col = EquivalenceClassDataColumn.MINIMUM_DISTINCT_VARIABLE_COUNT.value
    equivalence_class_data[color_col] = equivalence_class_data[color_col].astype(
        "string",
    )

    figure = px.scatter(
        data_frame=equivalence_class_data,
        x=EquivalenceClassDataColumn.IMPLICATION_COUNT.value,
        y=EquivalenceClassDataColumn.IMPLIED_BY_COUNT.value,
        color=color_col,
        hover_name=EquivalenceClassDataColumn.STATEMENT.value,
        title="Implication Statistics",
        log_y=True,
        log_x=True,
    )

    LOGGER.info("Scatter plot created.")

    return figure


def main() -> None:
    """Execute script."""
    logging.basicConfig(
        level=logging.INFO,
        handlers=[logging.StreamHandler(sys.stdout)],
    )
    args = parse_args()

    outcomes, equation_ids = load_outcomes(args.file)
    equation_strings = load_equation_strings()

    equivalence_class_data = construct_equivalence_class_data(
        outcomes=outcomes,
        equation_ids=equation_ids,
        equation_strings=equation_strings,
    )

    fig = make_scatter(equivalence_class_data)

    LOGGER.info("Saving scatter plot to %s...", args.outfile)
    fig.write_html(file=args.outfile)
    LOGGER.info("Scatter plot saved.")


if __name__ == "__main__":
    main()
