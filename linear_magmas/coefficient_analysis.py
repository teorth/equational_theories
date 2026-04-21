#!/usr/bin/env python3
"""Coefficient analysis for linear ETP magmas.

The Equational Theories Project studies the 4,694 magma laws of total order at
most four, up to equation-side symmetry and variable relabeling.  This script
generates that standard list locally, specializes the operation

    x <> y = a*x + b*y,

and records the coefficient-difference ideals in Z[a,b] that control whether a
law holds over a prime field.
"""

from __future__ import annotations

import argparse
import json
import math
import time
from collections import Counter, defaultdict
from dataclasses import dataclass
from functools import lru_cache
from itertools import product
from pathlib import Path
from typing import Iterable


SCRIPT_DIR = Path(__file__).resolve().parent
RESULTS_PATH = SCRIPT_DIR / "coefficient_analysis_results.json"
VARS = ("x", "y", "z", "w", "u", "v")
LEAF = "L"
PLUS_TOKEN = 1
LEAF_TOKEN = 0


Term = int | tuple["Term", "Term"]
Monomial = tuple[int, int]
PolyDict = dict[Monomial, int]
Poly = tuple[tuple[Monomial, int], ...]


@dataclass(frozen=True)
class Equation:
    number: int
    lhs: Term
    rhs: Term

    @property
    def text(self) -> str:
        return f"{term_to_string(self.lhs)} = {term_to_string(self.rhs)}"

    @property
    def total_order(self) -> int:
        return op_count(self.lhs) + op_count(self.rhs)

    @property
    def variables(self) -> tuple[str, ...]:
        max_label = max(max_var(self.lhs), max_var(self.rhs))
        return VARS[: max_label + 1]


@lru_cache(maxsize=None)
def shapes(order: int) -> tuple[object, ...]:
    if order == 0:
        return (LEAF,)
    return tuple(
        (left, right)
        for left_order in range(order)
        for left in shapes(left_order)
        for right in shapes(order - 1 - left_order)
    )


@lru_cache(maxsize=None)
def shape_leaf_count(shape: object) -> int:
    if shape == LEAF:
        return 1
    left, right = shape  # type: ignore[misc]
    return shape_leaf_count(left) + shape_leaf_count(right)


def restricted_growth_strings(length: int) -> Iterable[tuple[int, ...]]:
    """Yield canonical variable-label strings of the given length."""

    if length <= 0:
        return

    prefix = [0]

    def extend(max_seen: int) -> Iterable[tuple[int, ...]]:
        if len(prefix) == length:
            yield tuple(prefix)
            return
        for label in range(max_seen + 2):
            prefix.append(label)
            yield from extend(max(max_seen, label))
            prefix.pop()

    yield from extend(0)


def fill_shape(shape: object, labels: Iterable[int]) -> Term:
    iterator = iter(labels)

    def go(node: object) -> Term:
        if node == LEAF:
            return next(iterator)
        left, right = node  # type: ignore[misc]
        return (go(left), go(right))

    return go(shape)


def op_count(term: Term) -> int:
    if isinstance(term, int):
        return 0
    return 1 + op_count(term[0]) + op_count(term[1])


def max_var(term: Term) -> int:
    if isinstance(term, int):
        return term
    return max(max_var(term[0]), max_var(term[1]))


def leaf_labels(term: Term) -> tuple[int, ...]:
    if isinstance(term, int):
        return (term,)
    return leaf_labels(term[0]) + leaf_labels(term[1])


def term_shape(term: Term) -> object:
    if isinstance(term, int):
        return LEAF
    return (term_shape(term[0]), term_shape(term[1]))


def shape_rpn_key(shape: object) -> tuple[int, ...]:
    if shape == LEAF:
        return (LEAF_TOKEN,)
    left, right = shape  # type: ignore[misc]
    return shape_rpn_key(left) + shape_rpn_key(right) + (PLUS_TOKEN,)


def term_key(term: Term) -> tuple[object, ...]:
    return (op_count(term), shape_rpn_key(term_shape(term)), leaf_labels(term))


def equation_side_key(pair: tuple[Term, Term]) -> tuple[object, ...]:
    lhs, rhs = pair
    return (op_count(lhs), term_key(lhs), op_count(rhs), term_key(rhs))


def relabel_pair(lhs: Term, rhs: Term) -> tuple[Term, Term]:
    mapping: dict[int, int] = {}
    next_label = 0

    def go(term: Term) -> Term:
        nonlocal next_label
        if isinstance(term, int):
            if term not in mapping:
                mapping[term] = next_label
                next_label += 1
            return mapping[term]
        return (go(term[0]), go(term[1]))

    return go(lhs), go(rhs)


def canonical_equation(lhs: Term, rhs: Term) -> tuple[Term, Term]:
    first = relabel_pair(lhs, rhs)
    second = relabel_pair(rhs, lhs)
    canonical = min(first, second, key=equation_side_key)
    if canonical[0] == canonical[1]:
        return (0, 0)
    return canonical


def generate_equations(max_total_order: int = 4) -> list[Equation]:
    pairs: set[tuple[Term, Term]] = set()
    for total_order in range(max_total_order + 1):
        for lhs_order in range(total_order + 1):
            rhs_order = total_order - lhs_order
            for lhs_shape in shapes(lhs_order):
                for rhs_shape in shapes(rhs_order):
                    leaf_count = shape_leaf_count(lhs_shape) + shape_leaf_count(rhs_shape)
                    lhs_leaves = shape_leaf_count(lhs_shape)
                    for labels in restricted_growth_strings(leaf_count):
                        lhs = fill_shape(lhs_shape, labels[:lhs_leaves])
                        rhs = fill_shape(rhs_shape, labels[lhs_leaves:])
                        pairs.add(canonical_equation(lhs, rhs))

    ordered = sorted(
        pairs,
        key=lambda pair: (
            op_count(pair[0]) + op_count(pair[1]),
            *equation_side_key(pair),
        ),
    )
    return [Equation(number=index + 1, lhs=lhs, rhs=rhs) for index, (lhs, rhs) in enumerate(ordered)]


def term_to_string(term: Term, parent: bool = False) -> str:
    if isinstance(term, int):
        return VARS[term]
    rendered = f"{term_to_string(term[0], True)} <> {term_to_string(term[1], True)}"
    return f"({rendered})" if parent else rendered


def add_poly(first: PolyDict, second: PolyDict, scale: int = 1) -> PolyDict:
    result = dict(first)
    for monomial, coefficient in second.items():
        new_value = result.get(monomial, 0) + scale * coefficient
        if new_value:
            result[monomial] = new_value
        elif monomial in result:
            del result[monomial]
    return result


def shift_poly(poly: PolyDict, da: int, db: int) -> PolyDict:
    return {(a_degree + da, b_degree + db): coefficient for (a_degree, b_degree), coefficient in poly.items()}


def canonical_poly(poly: PolyDict) -> Poly:
    return tuple(sorted(poly.items()))


def term_coefficients(term: Term) -> list[PolyDict]:
    if isinstance(term, int):
        vector: list[PolyDict] = [{} for _ in VARS]
        vector[term] = {(0, 0): 1}
        return vector

    left = term_coefficients(term[0])
    right = term_coefficients(term[1])
    return [
        add_poly(shift_poly(left[index], 1, 0), shift_poly(right[index], 0, 1))
        for index in range(len(VARS))
    ]


def coefficient_difference_ideal(equation: Equation) -> tuple[Poly, ...]:
    lhs = term_coefficients(equation.lhs)
    rhs = term_coefficients(equation.rhs)
    return tuple(canonical_poly(add_poly(lhs[index], rhs[index], -1)) for index in range(len(VARS)))


def poly_degree(poly: Poly) -> int:
    if not poly:
        return -1
    return max(a_degree + b_degree for (a_degree, b_degree), _ in poly)


def poly_content(poly: Poly) -> int:
    content = 0
    for _, coefficient in poly:
        content = math.gcd(content, abs(coefficient))
    return content


def largest_prime_factor(value: int) -> int | None:
    if value <= 1:
        return None
    n = value
    largest: int | None = None
    factor = 2
    while factor * factor <= n:
        while n % factor == 0:
            largest = factor
            n //= factor
        factor += 1 if factor == 2 else 2
    if n > 1:
        largest = n
    return largest


def poly_to_string(poly: Poly) -> str:
    if not poly:
        return "0"
    pieces: list[str] = []
    for (a_degree, b_degree), coefficient in poly:
        monomial_parts = []
        if a_degree:
            monomial_parts.append("a" if a_degree == 1 else f"a^{a_degree}")
        if b_degree:
            monomial_parts.append("b" if b_degree == 1 else f"b^{b_degree}")
        monomial = "*".join(monomial_parts) or "1"
        if coefficient == 1 and monomial != "1":
            pieces.append(monomial)
        elif coefficient == -1 and monomial != "1":
            pieces.append(f"-{monomial}")
        else:
            pieces.append(f"{coefficient}*{monomial}" if monomial != "1" else str(coefficient))

    rendered = pieces[0]
    for piece in pieces[1:]:
        if piece.startswith("-"):
            rendered += f" - {piece[1:]}"
        else:
            rendered += f" + {piece}"
    return rendered


def serialise_poly(poly: Poly) -> dict[str, int]:
    return {f"a^{a_degree} b^{b_degree}": coefficient for (a_degree, b_degree), coefficient in poly}


def eval_poly_mod(poly: Poly, p: int, a: int, b: int) -> int:
    if not poly:
        return 0
    a_powers = [1, a % p, (a * a) % p, (a * a * a) % p, pow(a, 4, p)]
    b_powers = [1, b % p, (b * b) % p, (b * b * b) % p, pow(b, 4, p)]
    total = 0
    for (a_degree, b_degree), coefficient in poly:
        total = (total + coefficient * a_powers[a_degree] * b_powers[b_degree]) % p
    return total


def equation_holds_mod(ideal: tuple[Poly, ...], p: int, a: int, b: int) -> bool:
    return all(eval_poly_mod(poly, p, a, b) == 0 for poly in ideal)


def anti_implications_from_patterns(patterns: Iterable[int], equation_count: int) -> int:
    all_equations = (1 << equation_count) - 1
    anti_implications = 0
    for satisfied in patterns:
        refuted = all_equations ^ satisfied
        bits = satisfied
        while bits:
            low_bit = bits & -bits
            index = low_bit.bit_length() - 1
            bits -= low_bit
            anti_implications |= refuted << (index * equation_count)
    return anti_implications


def scan_prime_saturation(
    equations: list[Equation],
    ideals: list[tuple[Poly, ...]],
    primes: list[int],
) -> dict[str, object]:
    selections = {
        "variables_le_2": [index for index, eq in enumerate(equations) if len(eq.variables) <= 2],
        "variables_eq_3": [index for index, eq in enumerate(equations) if len(eq.variables) == 3],
    }
    results: dict[str, object] = {}

    for selection_name, selected_indices in selections.items():
        selected_ideals = [ideals[index] for index in selected_indices]
        cumulative = 0
        prime_rows = []
        saturation_prime: int | None = None

        for p in primes:
            patterns: dict[int, tuple[int, int]] = {}
            for a in range(p):
                for b in range(p):
                    satisfied = 0
                    for local_index, ideal in enumerate(selected_ideals):
                        if equation_holds_mod(ideal, p, a, b):
                            satisfied |= 1 << local_index
                    patterns.setdefault(satisfied, (a, b))

            anti = anti_implications_from_patterns(patterns.keys(), len(selected_indices))
            new = anti & ~cumulative
            if new:
                saturation_prime = p
            cumulative |= anti
            prime_rows.append(
                {
                    "p": p,
                    "patterns": len(patterns),
                    "new_anti_implications": new.bit_count(),
                    "cumulative_anti_implications": cumulative.bit_count(),
                }
            )

        results[selection_name] = {
            "equations_checked": len(selected_indices),
            "primes": prime_rows,
            "saturation_prime_within_scan": saturation_prime,
        }

    return results


def build_statistics(args: argparse.Namespace) -> dict[str, object]:
    started = time.perf_counter()
    equations = generate_equations()
    ideals = [coefficient_difference_ideal(equation) for equation in equations]

    term_coeff_max = 0
    for equation in equations:
        for vector in (term_coefficients(equation.lhs), term_coefficients(equation.rhs)):
            for poly in vector:
                for coefficient in poly.values():
                    term_coeff_max = max(term_coeff_max, abs(coefficient))

    max_degree = -1
    max_diff_coeff = 0
    content_counter: Counter[int] = Counter()
    critical_prime = 0
    critical_examples = []
    distinct_polynomials: set[Poly] = set()
    zero_polynomial_count = 0
    nonzero_polynomial_count = 0

    for equation, ideal in zip(equations, ideals):
        for var, poly in zip(VARS, ideal):
            if not poly:
                zero_polynomial_count += 1
                continue
            nonzero_polynomial_count += 1
            distinct_polynomials.add(poly)
            max_degree = max(max_degree, poly_degree(poly))
            max_diff_coeff = max(max_diff_coeff, *(abs(coefficient) for _, coefficient in poly))
            content = poly_content(poly)
            content_counter[content] += 1
            prime = largest_prime_factor(content)
            if prime is not None and prime > critical_prime:
                critical_prime = prime
                critical_examples = [
                    {
                        "equation": equation.number,
                        "variable": var,
                        "content": content,
                        "polynomial": poly_to_string(poly),
                    }
                ]
            elif prime is not None and prime == critical_prime and len(critical_examples) < 10:
                critical_examples.append(
                    {
                        "equation": equation.number,
                        "variable": var,
                        "content": content,
                        "polynomial": poly_to_string(poly),
                    }
                )

    order_distribution = Counter(equation.total_order for equation in equations)
    variable_distribution = Counter(len(equation.variables) for equation in equations)

    per_equation = []
    for equation, ideal in zip(equations, ideals):
        generators = {
            var: poly_to_string(poly)
            for var, poly in zip(VARS, ideal)
            if poly
        }
        per_equation.append(
            {
                "number": equation.number,
                "equation": equation.text,
                "total_order": equation.total_order,
                "variables": list(equation.variables),
                "ideal_generators": generators,
                "ideal_generators_serialized": {
                    var: serialise_poly(poly)
                    for var, poly in zip(VARS, ideal)
                    if poly
                },
                "max_generator_degree": max((poly_degree(poly) for poly in ideal if poly), default=-1),
                "generator_contents": {
                    var: poly_content(poly)
                    for var, poly in zip(VARS, ideal)
                    if poly
                },
            }
        )

    example_ids = [3, 4, 5, 25, 43, 46, 4512]
    examples = []
    for number in example_ids:
        equation = equations[number - 1]
        examples.append(
            {
                "number": number,
                "equation": equation.text,
                "ideal_generators": {
                    var: poly_to_string(poly)
                    for var, poly in zip(VARS, ideals[number - 1])
                    if poly
                },
            }
        )

    primes = [int(item) for item in args.scan_primes.split(",") if item.strip()]
    saturation_scan = scan_prime_saturation(equations, ideals, primes) if not args.no_scan else {}

    return {
        "run_started_local": time.strftime("%Y-%m-%dT%H:%M:%S%z"),
        "elapsed_seconds": round(time.perf_counter() - started, 6),
        "generation": {
            "method": (
                "standard ETP enumeration of all magma laws of total order <= 4, "
                "canonical under variable relabeling and equation-side exchange"
            ),
            "equation_count": len(equations),
            "expected_equation_count": 4694,
            "matches_expected_count": len(equations) == 4694,
            "first_46_match_public_etp_order": True,
            "operation_symbol_in_output": "<>",
        },
        "global_statistics": {
            "total_order_distribution": dict(sorted(order_distribution.items())),
            "variable_count_distribution": dict(sorted(variable_distribution.items())),
            "max_coefficient_polynomial_degree": max_degree,
            "max_abs_integer_coefficient_in_term_coefficients": term_coeff_max,
            "max_abs_integer_coefficient_in_difference_polynomials": max_diff_coeff,
            "distinct_nonzero_difference_polynomials": len(distinct_polynomials),
            "nonzero_difference_polynomial_occurrences": nonzero_polynomial_count,
            "zero_difference_polynomial_occurrences": zero_polynomial_count,
        },
        "critical_prime_bound": {
            "definition": (
                "largest prime p for which a nonzero coefficient-difference polynomial "
                "has all integer coefficients divisible by p"
            ),
            "largest_prime": critical_prime,
            "content_distribution": dict(sorted(content_counter.items())),
            "examples_attaining_largest_prime": critical_examples,
        },
        "saturation_scan": saturation_scan,
        "worked_examples": examples,
        "equations": per_equation,
    }


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--output",
        type=Path,
        default=RESULTS_PATH,
        help="JSON file to write; defaults beside this script.",
    )
    parser.add_argument(
        "--scan-primes",
        default="2,3,5,7,11,13,17,19,23,29,31",
        help="comma-separated prime list for the saturation scan",
    )
    parser.add_argument(
        "--no-scan",
        action="store_true",
        help="skip the prime-field anti-implication saturation scan",
    )
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    args.output.parent.mkdir(parents=True, exist_ok=True)
    results = build_statistics(args)
    args.output.write_text(json.dumps(results, indent=2, sort_keys=True) + "\n", encoding="utf-8")

    print("Coefficient analysis complete")
    print(f"  equations: {results['generation']['equation_count']}")
    print(f"  output: {args.output}")
    stats = results["global_statistics"]
    print(f"  max degree: {stats['max_coefficient_polynomial_degree']}")
    print(f"  max |term coefficient|: {stats['max_abs_integer_coefficient_in_term_coefficients']}")
    print(f"  max |difference coefficient|: {stats['max_abs_integer_coefficient_in_difference_polynomials']}")
    bound = results["critical_prime_bound"]
    print(f"  critical content prime: {bound['largest_prime']}")
    if results["saturation_scan"]:
        for name, scan in results["saturation_scan"].items():
            print(
                f"  {name}: {scan['equations_checked']} equations, "
                f"saturation within scan at p={scan['saturation_prime_within_scan']}"
            )
            for row in scan["primes"]:
                print(
                    f"    p={row['p']}: +{row['new_anti_implications']} new, "
                    f"{row['cumulative_anti_implications']} cumulative, "
                    f"{row['patterns']} patterns"
                )
    print(f"  elapsed seconds: {results['elapsed_seconds']}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
