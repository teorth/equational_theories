#!/usr/bin/env python3

import argparse
import itertools
import json
import math
import os
import random
import re
import sys

ALLOWED_SYMBOL_NAMES = "xyzuvw"
EQUATIONS_FILENAMES = [f"../equational_theories/Equations/Eqns{file}.lean"
                        for file in ["1_999", "1000_1999", "2000_2999", "3000_3999", "4000_4694"]]
EXAMPLE_MAGMA_TABLE = "[[2, 2, 0, 3], [2, 2, 1, 0], [2, 2, 0, 3], [2, 3, 1, 0]]"


def is_expected_equation_format(equation_string):
    if not equation_string:
        return False
    if equation_string.count("(") != equation_string.count(")"):
        return False
    if equation_string.count(" ◇ ") != equation_string.count("◇"):
        return False
    if equation_string.count(" = ") != equation_string.count("="):
        return False
    if equation_string.count(" = ") != 1:
        return False
    if not re.match(
        f"^([{ALLOWED_SYMBOL_NAMES}] ◇ )+$",
        equation_string.replace("(", "").replace("= ", "◇ ").replace(")", "") + " ◇ ",
    ):
        return False
    return True


def read_equations_map():
    equations_map = {}
    for file in EQUATIONS_FILENAMES:
        filename = os.path.join(
            os.path.dirname(os.path.abspath(__file__)),
            file,
        )
        assert filename
        with open(filename, "r", encoding="utf-8") as equations_file:
            for line in equations_file:
                line = line.rstrip("\n")
                equation_match = re.search(r"equation (\d+) := (.+?)$", line)
                if equation_match:
                    equation_id, equation = equation_match.groups()
                    assert is_expected_equation_format(equation)
                    equations_map[int(equation_id)] = equation
    assert min(equations_map.keys()) == 1
    assert max(equations_map.keys()) == len(equations_map)
    return equations_map


def get_binary_operation_map(parsed_magma_table):
    assert parsed_magma_table
    binary_operation_map = {}
    for left, row in enumerate(parsed_magma_table):
        for right, mapped_to in enumerate(row):
            binary_operation_map[(left, right)] = mapped_to
    assert len(binary_operation_map) == len(parsed_magma_table) ** 2
    return binary_operation_map


def remove_redundant_parentheses(string):
    assert string
    return re.sub(r"\(([0-9])\)", "\\1", string)


def test_equation_with_values(equation, variable_value_map, binary_operation_map):
    assert equation and variable_value_map and binary_operation_map
    assert is_expected_equation_format(equation)
    transformations = []
    transformations.append(equation)
    readable_value_map = ""
    for var, value in variable_value_map.items():
        equation = equation.replace(var, str(value))
        readable_value_map += f"{var}={value}, "
    distinct_values = len(set(list(variable_value_map.values())[:4]))
    transformations.append(
        f"{equation} # example with {readable_value_map.rstrip(', ')}"
    )
    assert equation.count(" ◇ ") == equation.count("◇")
    for _ in range(equation.count(" ◇ ") + 1):
        for (left, right), value in binary_operation_map.items():
            reduced_equation = remove_redundant_parentheses(
                equation.replace(f"{left} ◇ {right}", str(value))
            )
            if reduced_equation != equation:
                transformations.append(reduced_equation)
                equation = reduced_equation
            if "◇" not in equation:
                assert len(equation) == 5 and " = " in equation
                lhs, rhs = equation.split(" = ", 1)
                return lhs == rhs, transformations, distinct_values
    assert False


def get_symbols(binary_operation_map):
    return set(range(0, int(math.sqrt(len(binary_operation_map)))))


def test_equation(equation, binary_operation_map):
    assert equation and binary_operation_map
    assert is_expected_equation_format(equation)
    max_distinct_values = 0
    sample_transformations = []
    symbols_in_equation = sorted(
        list(set(re.sub(f"[^{ALLOWED_SYMBOL_NAMES}]", "", equation)))
    )
    for values in itertools.product(
        get_symbols(binary_operation_map), repeat=len(symbols_in_equation)
    ):
        variable_value_map = dict(zip(symbols_in_equation, list(values)))
        passed, transformations, distinct_values = test_equation_with_values(
            equation, variable_value_map, binary_operation_map
        )
        if not passed:
            return False, transformations
        if distinct_values >= max_distinct_values:
            if distinct_values > max_distinct_values:
                sample_transformations = []
            sample_transformations.append(transformations)
            max_distinct_values = distinct_values
    return True, random.Random(22_028_942).choice(sample_transformations)


def test_equation_ids(equation_ids, binary_operation_map):
    results = []
    equations_map = read_equations_map()
    for equation_id in equation_ids:
        equation_string = equations_map[equation_id]
        passed, transformations = test_equation(equation_string, binary_operation_map)
        results.append((equation_id, equation_string, passed, transformations))
    return results


def text_to_magma_table(text):
    non_whitespace_tokens = re.sub(r"\W+", " ", text).strip().split(" ")
    try:
        entries = [int(token) for token in non_whitespace_tokens]
    except ValueError:
        return None
    row_length = int(math.sqrt(len(entries)))
    if len(entries) != row_length**2:
        return None
    table = []
    for i in range(len(entries) // row_length):
        row = entries[(i * row_length) : (i + 1) * row_length]
        table.append(row)
    return table


def json_magma_table_to_short_text(json_magma_table):
    return re.sub(r"[\[\],]", "", json_magma_table).replace(" ", ",")


def parse_magma_table_string(magma_table_string):
    if not magma_table_string:
        return None, None
    parsed_magma_table = None
    try:
        parsed_magma_table = json.loads(magma_table_string.strip("'\""))
    except json.decoder.JSONDecodeError:
        pass
    if not parsed_magma_table:
        parsed_magma_table = text_to_magma_table(magma_table_string)
    if not parsed_magma_table:
        return None, None
    if not isinstance(parsed_magma_table, list):
        return None, None
    if len(parsed_magma_table) == 0:
        return None, None
    if not isinstance(parsed_magma_table[0], list):
        return None, None
    n_rows = len(parsed_magma_table)
    n_cols = len(parsed_magma_table[0])
    if n_rows != n_cols:
        return None, None
    if not 1 <= n_rows <= 10:
        return None, None
    for row in parsed_magma_table:
        for mapped_to in row:
            if not isinstance(mapped_to, int):
                return None, None
            if not 0 <= mapped_to <= n_rows - 1:
                return None, None
    binary_operation_map = get_binary_operation_map(parsed_magma_table)
    assert len(get_symbols(binary_operation_map)) == len(parsed_magma_table)
    return parsed_magma_table, binary_operation_map


def print_magma_as_table(parsed_magma_table):
    assert parsed_magma_table
    print("|       |", end="")
    for right in range(len(parsed_magma_table)):
        print(f" **{right}** |", end="")
    print("")

    print("|-------|", end="")
    for _ in range(len(parsed_magma_table)):
        print("-------|", end="")
    print("")

    for left, row in enumerate(parsed_magma_table):
        print(f"| **{left}** |", end="")
        for right, mapped_to in enumerate(row):
            print(f"   {mapped_to}   |", end="")
        print("")


def print_binary_operation_map(binary_operation_map):
    assert binary_operation_map
    print("```")
    n_symbols = len(get_symbols(binary_operation_map))
    for i, ((left, right), value) in enumerate(binary_operation_map.items()):
        print(
            f"{left} ◇ {right} = {value}",
            end=("\n" if (i + 1) % n_symbols == 0 else "     "),
        )
    print("```")


def main():
    parser = argparse.ArgumentParser(
        description="Test a given magma table against all or a subset of the predefined equations in `Equations/All.lean`."
    )
    parser.add_argument(
        "magma_table",
        type=str,
        help=f'A JSON-like 2D list representing a magma operation table. Each entry represents the result of a binary operation ◇ between two elements. Example format: "{EXAMPLE_MAGMA_TABLE}"',
    )
    parser.add_argument(
        "--ids",
        type=lambda s: [int(item) for item in s.split(",")],
        help="A comma-separated list of equation IDs to test the magma table against. If omitted, all equations in `Equations/All.lean` will be tested by default.",
    )
    parser.add_argument(
        "--print-only",
        action="store_true",
        help="Only print the number of equations passed and tested, without displaying detailed results.",
    )
    parser.add_argument(
        "--json",
        action="store_true",
        help='Output results in JSON format. Uses the magma JSON format: {"size": […], "table": […], "satisfies": […], "tested_up_to": […]}',
    )
    parser.add_argument(
        "--verbose",
        action="store_true",
        help="Enable detailed output. This includes specific counterexamples for any failures when checking against specific equation ids (specified using --ids).",
    )
    args = parser.parse_args()

    parsed_magma_table, binary_operation_map = parse_magma_table_string(
        args.magma_table
    )
    if not parsed_magma_table:
        print(f'ERROR: Unable to parse magma table "{args.magma_table}"')
        print("")
        print(
            "Expecting an n×n table (where 1 ≤ n ≤ 10) and symbols in the range [0, n-1]."
        )
        print("")
        print("Examples:")
        print(f'  "{EXAMPLE_MAGMA_TABLE}"')
        print(f'  "{json_magma_table_to_short_text(EXAMPLE_MAGMA_TABLE)}"')
        sys.exit(1)

    equations_map = read_equations_map()
    equation_ids = sorted(list(set(args.ids)) if args.ids else equations_map.keys())
    assert equation_ids

    if args.json:
        satisfies = []
        for equation_id, _, passed, _ in test_equation_ids(
            equation_ids, binary_operation_map
        ):
            if passed:
                satisfies.append(equation_id)
        result_object = {
            "size": len(get_symbols(binary_operation_map)),
            "table": parsed_magma_table,
            "satisfies": satisfies,
        }
        if len(equation_ids) == len(equations_map):
            # Set tested_up_to only if we've tested all equations.
            result_object["tested_up_to"] = max(equations_map.keys())
        else:
            result_object["tested_up_to"] = None
        print(json.dumps(result_object))
        sys.exit(0)

    for equation_id in equation_ids:
        if equation_id not in equations_map:
            print(f"ERROR: Unknown equation id {equation_id}")
            sys.exit(1)

    if args.print_only:
        n_passed, n_failed = 0, 0
        for _, _, passed, _ in test_equation_ids(equation_ids, binary_operation_map):
            if passed:
                n_passed += 1
            else:
                n_failed += 1
        print(f"{n_passed}/{n_passed + n_failed}")
        sys.exit(0)

    print(f"Magma table: {parsed_magma_table}")
    print("")
    print_magma_as_table(parsed_magma_table)
    print("")
    print_binary_operation_map(binary_operation_map)
    print("")
    print("```")
    n_passed, n_failed = 0, 0
    for equation_id, equation_string, passed, transformations in test_equation_ids(
        equation_ids, binary_operation_map
    ):
        print_transformations = False
        if passed:
            n_passed += 1
            print(f"{equation_id: 5d}. {equation_string} ✅")
            if args.verbose:
                print_transformations = True
        else:
            n_failed += 1
            if args.ids:
                print(f"{equation_id: 5d}. {equation_string} ❌")
                if args.verbose:
                    print_transformations = True
        assert transformations and transformations[0] == equation_string
        assert "◇" not in transformations[-1]
        if print_transformations:
            for transformation in transformations[1:]:
                if not passed:
                    transformation = transformation.replace(" = ", " ≠ ")
                    transformation = transformation.replace(
                        "# example ", "# counterexample "
                    )
                print(f"       {transformation}")
            print("")
    print("```")
    print("")
    print(f"Magma tested against {n_passed + n_failed} equations:")
    print(f"* {n_passed} passed ({100.0 * n_passed / (n_passed + n_failed):.1f}%)")
    print(f"* {n_failed} failed ({100.0 * n_failed / (n_passed + n_failed):.1f}%)")


if __name__ == "__main__":
    main()
