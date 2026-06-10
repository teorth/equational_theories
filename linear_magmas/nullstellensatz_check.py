#!/usr/bin/env python3
"""Nullstellensatz containment checks for the ETP linear coefficient ideals.

This script checks the at-most-two-variable ETP laws from
``coefficient_analysis.py``.  It recomputes the prime-field anti-implication
scan through 31, then checks every ordered pair not separated by that scan.

The check is exact over Q[a,b].  Sympy is not required: the file contains a
small Buchberger implementation for bivariate rational polynomials.  For the
degree-four two-generator ideals in this target, the Bezout length bound gives
the radical-membership search exponent 16: if a generator q vanishes on the
variety of I, then q^16 lies in I.  A zero Groebner normal form for q^n is the
computed Nullstellensatz certificate used here.
"""

from __future__ import annotations

import argparse
import importlib.util
import json
import math
import time
from collections import Counter
from dataclasses import dataclass
from fractions import Fraction
from itertools import combinations
from pathlib import Path
from typing import Iterable


SCRIPT_DIR = Path(__file__).resolve().parent
COEFFICIENT_ANALYSIS = SCRIPT_DIR / "coefficient_analysis.py"
COEFFICIENT_RESULTS = SCRIPT_DIR / "coefficient_analysis_results.json"
RESULTS_PATH = SCRIPT_DIR / "nullstellensatz_results.md"

SCAN_PRIMES = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31]
BEZOUT_EXPONENT_BOUND = 16
VARS = ("x", "y", "z", "w", "u", "v")

Monomial = tuple[int, int]
RawPoly = tuple[tuple[Monomial, int], ...]
Poly = dict[Monomial, Fraction]
PolyKey = tuple[tuple[int, int, int, int], ...]


@dataclass(frozen=True)
class EquationRecord:
    number: int
    text: str
    variables: tuple[str, ...]
    ideal: tuple[RawPoly, ...]


@dataclass
class MembershipResult:
    contained: bool
    exponent: int | None
    obstruction_degree: int
    obstruction_terms: int


@dataclass
class PairResult:
    antecedent: int
    consequent: int
    failed_generators: list[str]
    obstruction_degree: int
    witness_primes: list[int]


@dataclass
class ArithmeticAudit:
    inverted_prime_counts: Counter[int]
    basis_denominator_prime_counts: Counter[int]
    max_inverted_prime: int
    max_basis_denominator_prime: int
    max_inverted_abs_numerator: int
    max_inverted_denominator: int

    @classmethod
    def empty(cls) -> "ArithmeticAudit":
        return cls(Counter(), Counter(), 0, 0, 1, 1)

    @property
    def max_arithmetic_prime(self) -> int:
        return max(self.max_inverted_prime, self.max_basis_denominator_prime)

    def record_inverted_coefficient(self, coefficient: Fraction) -> None:
        self.max_inverted_abs_numerator = max(self.max_inverted_abs_numerator, abs(coefficient.numerator))
        self.max_inverted_denominator = max(self.max_inverted_denominator, coefficient.denominator)
        for prime in prime_factors(abs(coefficient.numerator)):
            self.inverted_prime_counts[prime] += 1
            self.max_inverted_prime = max(self.max_inverted_prime, prime)
        for prime in prime_factors(coefficient.denominator):
            self.inverted_prime_counts[prime] += 1
            self.max_inverted_prime = max(self.max_inverted_prime, prime)

    def record_basis(self, basis: list[Poly]) -> None:
        for poly in basis:
            for coefficient in poly.values():
                for prime in prime_factors(coefficient.denominator):
                    self.basis_denominator_prime_counts[prime] += 1
                    self.max_basis_denominator_prime = max(self.max_basis_denominator_prime, prime)


def load_coefficient_module():
    spec = importlib.util.spec_from_file_location("coefficient_analysis", COEFFICIENT_ANALYSIS)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot load {COEFFICIENT_ANALYSIS}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def parse_serialized_poly(serialized: dict[str, int]) -> RawPoly:
    terms: list[tuple[Monomial, int]] = []
    for monomial, coefficient in serialized.items():
        a_degree = 0
        b_degree = 0
        pieces = monomial.split()
        for piece in pieces:
            if piece.startswith("a^"):
                a_degree = int(piece[2:])
            elif piece.startswith("b^"):
                b_degree = int(piece[2:])
            else:
                raise ValueError(f"unexpected monomial piece {piece!r}")
        if coefficient:
            terms.append(((a_degree, b_degree), int(coefficient)))
    return tuple(sorted(terms))


def records_from_json(path: Path) -> list[EquationRecord]:
    data = json.loads(path.read_text(encoding="utf-8"))
    records: list[EquationRecord] = []
    for row in data["equations"]:
        generators_by_var = row["ideal_generators_serialized"]
        ideal = []
        for var in VARS:
            serialized = generators_by_var.get(var, {})
            ideal.append(parse_serialized_poly(serialized))
        records.append(
            EquationRecord(
                number=int(row["number"]),
                text=str(row["equation"]),
                variables=tuple(row["variables"]),
                ideal=tuple(ideal),
            )
        )
    return records


def records_from_generator() -> list[EquationRecord]:
    ca = load_coefficient_module()
    equations = ca.generate_equations()
    records: list[EquationRecord] = []
    for equation in equations:
        records.append(
            EquationRecord(
                number=equation.number,
                text=equation.text,
                variables=equation.variables,
                ideal=ca.coefficient_difference_ideal(equation),
            )
        )
    return records


def load_equation_records() -> tuple[list[EquationRecord], str]:
    if COEFFICIENT_RESULTS.exists():
        return records_from_json(COEFFICIENT_RESULTS), f"read {COEFFICIENT_RESULTS.name}"
    return records_from_generator(), f"regenerated from {COEFFICIENT_ANALYSIS.name}"


def raw_to_poly(poly: RawPoly) -> Poly:
    return {monomial: Fraction(coefficient) for monomial, coefficient in poly if coefficient}


def poly_to_key(poly: Poly) -> PolyKey:
    return tuple(
        sorted(
            (a_degree, b_degree, coefficient.numerator, coefficient.denominator)
            for (a_degree, b_degree), coefficient in poly.items()
            if coefficient
        )
    )


def raw_poly_to_key(poly: RawPoly) -> PolyKey:
    return poly_to_key(raw_to_poly(poly))


def key_to_poly(key: PolyKey) -> Poly:
    return {
        (a_degree, b_degree): Fraction(numerator, denominator)
        for a_degree, b_degree, numerator, denominator in key
    }


def prime_factors(value: int) -> list[int]:
    if value <= 1:
        return []
    factors: list[int] = []
    remaining = value
    divisor = 2
    while divisor * divisor <= remaining:
        while remaining % divisor == 0:
            factors.append(divisor)
            remaining //= divisor
        divisor += 1 if divisor == 2 else 2
    if remaining > 1:
        factors.append(remaining)
    return factors


def clean(poly: Poly) -> Poly:
    return {monomial: coefficient for monomial, coefficient in poly.items() if coefficient}


def poly_degree(poly: Poly) -> int:
    if not poly:
        return -1
    return max(a_degree + b_degree for a_degree, b_degree in poly)


def monomial_order_key(monomial: Monomial) -> tuple[int, int]:
    a_degree, b_degree = monomial
    return (a_degree + b_degree, a_degree)


def leading_monomial(poly: Poly) -> Monomial:
    return max(poly, key=monomial_order_key)


def leading_coefficient(poly: Poly) -> Fraction:
    return poly[leading_monomial(poly)]


def divides(first: Monomial, second: Monomial) -> bool:
    return first[0] <= second[0] and first[1] <= second[1]


def monomial_lcm(first: Monomial, second: Monomial) -> Monomial:
    return (max(first[0], second[0]), max(first[1], second[1]))


def monomial_gcd(first: Monomial, second: Monomial) -> Monomial:
    return (min(first[0], second[0]), min(first[1], second[1]))


def poly_add(first: Poly, second: Poly, scale: Fraction = Fraction(1)) -> Poly:
    result = dict(first)
    for monomial, coefficient in second.items():
        value = result.get(monomial, Fraction(0)) + scale * coefficient
        if value:
            result[monomial] = value
        elif monomial in result:
            del result[monomial]
    return result


def poly_mul(first: Poly, second: Poly) -> Poly:
    if not first or not second:
        return {}
    result: Poly = {}
    for (a1, b1), c1 in first.items():
        for (a2, b2), c2 in second.items():
            monomial = (a1 + a2, b1 + b2)
            result[monomial] = result.get(monomial, Fraction(0)) + c1 * c2
    return clean(result)


def multiply_by_monomial(poly: Poly, monomial: Monomial, scale: Fraction) -> Poly:
    if not poly or not scale:
        return {}
    da, db = monomial
    return {
        (a_degree + da, b_degree + db): coefficient * scale
        for (a_degree, b_degree), coefficient in poly.items()
        if coefficient * scale
    }


def monic(poly: Poly, audit: ArithmeticAudit | None = None) -> Poly:
    coefficient = leading_coefficient(poly)
    if audit is not None:
        audit.record_inverted_coefficient(coefficient)
    return {monomial: value / coefficient for monomial, value in poly.items()}


def is_constant_nonzero(poly: Poly) -> bool:
    return bool(poly) and all(monomial == (0, 0) for monomial in poly)


def one_poly() -> Poly:
    return {(0, 0): Fraction(1)}


def reduce_poly(poly: Poly, basis: list[Poly]) -> Poly:
    working = clean(dict(poly))
    remainder: Poly = {}
    basis_lms = [(leading_monomial(g), leading_coefficient(g), g) for g in basis if g]

    while working:
        lm = leading_monomial(working)
        lc = working[lm]
        reduced = False
        for basis_lm, basis_lc, basis_poly in basis_lms:
            if divides(basis_lm, lm):
                delta = (lm[0] - basis_lm[0], lm[1] - basis_lm[1])
                subtraction = multiply_by_monomial(basis_poly, delta, lc / basis_lc)
                working = poly_add(working, subtraction, Fraction(-1))
                reduced = True
                break
        if not reduced:
            remainder[lm] = remainder.get(lm, Fraction(0)) + lc
            del working[lm]

    return clean(remainder)


def s_polynomial(first: Poly, second: Poly) -> Poly:
    first_lm = leading_monomial(first)
    second_lm = leading_monomial(second)
    lcm = monomial_lcm(first_lm, second_lm)
    first_delta = (lcm[0] - first_lm[0], lcm[1] - first_lm[1])
    second_delta = (lcm[0] - second_lm[0], lcm[1] - second_lm[1])
    first_part = multiply_by_monomial(first, first_delta, Fraction(1, 1) / leading_coefficient(first))
    second_part = multiply_by_monomial(second, second_delta, Fraction(1, 1) / leading_coefficient(second))
    return poly_add(first_part, second_part, Fraction(-1))


def interreduce_basis(basis: list[Poly], audit: ArithmeticAudit | None = None) -> list[Poly]:
    current = [monic(g, audit) for g in basis if g]
    changed = True
    while changed:
        changed = False
        next_basis: list[Poly] = []
        for index, poly in enumerate(current):
            others = current[:index] + current[index + 1 :]
            reduced = reduce_poly(poly, others)
            if not reduced:
                changed = True
                continue
            reduced = monic(reduced, audit)
            if poly_to_key(reduced) != poly_to_key(poly):
                changed = True
            next_basis.append(reduced)
        dedup: dict[PolyKey, Poly] = {}
        for poly in next_basis:
            dedup[poly_to_key(poly)] = poly
        current = sorted(dedup.values(), key=lambda p: monomial_order_key(leading_monomial(p)), reverse=True)
    return current


def groebner_basis(generators: Iterable[Poly], audit: ArithmeticAudit | None = None) -> list[Poly]:
    basis: list[Poly] = []
    for generator in generators:
        poly = clean(dict(generator))
        if not poly:
            continue
        if is_constant_nonzero(poly):
            return [one_poly()]
        reduced = reduce_poly(poly, basis)
        if not reduced:
            continue
        if is_constant_nonzero(reduced):
            return [one_poly()]
        basis.append(monic(reduced, audit))

    if not basis:
        return []

    basis = interreduce_basis(basis, audit)
    pairs = set(combinations(range(len(basis)), 2))

    while pairs:
        i, j = pairs.pop()
        first_lm = leading_monomial(basis[i])
        second_lm = leading_monomial(basis[j])
        if monomial_gcd(first_lm, second_lm) == (0, 0):
            continue
        remainder = reduce_poly(s_polynomial(basis[i], basis[j]), basis)
        if not remainder:
            continue
        if is_constant_nonzero(remainder):
            return [one_poly()]
        remainder = monic(remainder, audit)
        new_index = len(basis)
        basis.append(remainder)
        for old_index in range(new_index):
            pairs.add((old_index, new_index))

    final_basis = interreduce_basis(basis, audit)
    if audit is not None:
        audit.record_basis(final_basis)
    return final_basis


def groebner_key(basis: list[Poly]) -> tuple[PolyKey, ...]:
    return tuple(poly_to_key(poly) for poly in basis)


def eval_raw_poly_mod(poly: RawPoly, p: int, a_value: int, b_value: int) -> int:
    total = 0
    for (a_degree, b_degree), coefficient in poly:
        total = (total + coefficient * pow(a_value, a_degree, p) * pow(b_value, b_degree, p)) % p
    return total


def equation_holds_mod(ideal: tuple[RawPoly, ...], p: int, a_value: int, b_value: int) -> bool:
    return all(eval_raw_poly_mod(poly, p, a_value, b_value) == 0 for poly in ideal)


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


def saturation_scan(selected: list[EquationRecord]) -> tuple[int, list[dict[str, int]]]:
    cumulative = 0
    rows: list[dict[str, int]] = []
    for p in SCAN_PRIMES:
        patterns: dict[int, tuple[int, int]] = {}
        for a_value in range(p):
            for b_value in range(p):
                satisfied = 0
                for index, record in enumerate(selected):
                    if equation_holds_mod(record.ideal, p, a_value, b_value):
                        satisfied |= 1 << index
                patterns.setdefault(satisfied, (a_value, b_value))

        anti = anti_implications_from_patterns(patterns.keys(), len(selected))
        new = anti & ~cumulative
        cumulative |= anti
        rows.append(
            {
                "p": p,
                "patterns": len(patterns),
                "new_anti_implications": new.bit_count(),
                "cumulative_anti_implications": cumulative.bit_count(),
            }
        )
    return cumulative, rows


def ideal_signature(record: EquationRecord) -> tuple[PolyKey, ...]:
    return tuple(raw_poly_to_key(poly) for poly in record.ideal if poly)


def ideal_generators(record: EquationRecord) -> list[Poly]:
    return [raw_to_poly(poly) for poly in record.ideal if poly]


def raw_poly_to_string(poly: RawPoly) -> str:
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


def radical_membership_by_powers(
    generator_key: PolyKey,
    basis_key: tuple[PolyKey, ...],
    max_exponent: int,
) -> MembershipResult:
    generator = key_to_poly(generator_key)
    if not generator:
        return MembershipResult(True, 0, -1, 0)

    basis = [key_to_poly(key) for key in basis_key]
    if len(basis) == 1 and basis[0] == one_poly():
        return MembershipResult(True, 1, -1, 0)
    if not basis:
        return MembershipResult(False, None, poly_degree(generator), len(generator))

    current: Poly | None = None
    for exponent in range(1, max_exponent + 1):
        current = generator if current is None else poly_mul(current, generator)
        current = reduce_poly(current, basis)
        if not current:
            return MembershipResult(True, exponent, -1, 0)

    assert current is not None
    return MembershipResult(False, None, poly_degree(current), len(current))


def find_witness_primes(
    antecedent: EquationRecord,
    consequent: EquationRecord,
    start_after: int,
    limit: int,
    max_witnesses: int,
) -> list[int]:
    witnesses: list[int] = []
    for p in primes_up_to(limit):
        if p <= start_after:
            continue
        found = False
        for a_value in range(p):
            for b_value in range(p):
                if equation_holds_mod(antecedent.ideal, p, a_value, b_value) and not equation_holds_mod(
                    consequent.ideal, p, a_value, b_value
                ):
                    witnesses.append(p)
                    found = True
                    break
            if found:
                break
        if len(witnesses) >= max_witnesses:
            break
    return witnesses


def primes_up_to(limit: int) -> list[int]:
    if limit < 2:
        return []
    sieve = [True] * (limit + 1)
    sieve[0] = sieve[1] = False
    for value in range(2, int(math.isqrt(limit)) + 1):
        if sieve[value]:
            step = value
            start = value * value
            sieve[start : limit + 1 : step] = [False] * (((limit - start) // step) + 1)
    return [value for value in range(2, limit + 1) if sieve[value]]


def check_containments(
    selected: list[EquationRecord],
    separated_bitset: int,
    max_exponent: int,
    witness_prime_limit: int,
) -> dict[str, object]:
    total_pairs = len(selected) * len(selected)
    unseparated_pairs = total_pairs - separated_bitset.bit_count()

    basis_cache: dict[tuple[PolyKey, ...], tuple[PolyKey, ...]] = {}
    membership_cache: dict[tuple[tuple[PolyKey, ...], PolyKey], MembershipResult] = {}
    audit = ArithmeticAudit.empty()

    certified_pairs = 0
    open_pairs: list[PairResult] = []
    max_certificate_exponent = 0
    certificate_exponent_counts: dict[int, int] = {}
    checked_pairs = 0

    for antecedent_index, antecedent in enumerate(selected):
        antecedent_signature = ideal_signature(antecedent)
        if antecedent_signature not in basis_cache:
            basis = groebner_basis(ideal_generators(antecedent), audit)
            basis_cache[antecedent_signature] = groebner_key(basis)
        basis_key = basis_cache[antecedent_signature]

        for consequent_index, consequent in enumerate(selected):
            bit_index = antecedent_index * len(selected) + consequent_index
            if (separated_bitset >> bit_index) & 1:
                continue

            checked_pairs += 1
            pair_certified = True
            failed_generators: list[str] = []
            pair_obstruction_degree = -1

            for raw_generator in consequent.ideal:
                if not raw_generator:
                    continue
                generator_key = raw_poly_to_key(raw_generator)
                cache_key = (basis_key, generator_key)
                if cache_key not in membership_cache:
                    membership_cache[cache_key] = radical_membership_by_powers(
                        generator_key, basis_key, max_exponent
                    )
                membership = membership_cache[cache_key]
                if membership.contained:
                    if membership.exponent is not None:
                        max_certificate_exponent = max(max_certificate_exponent, membership.exponent)
                        certificate_exponent_counts[membership.exponent] = (
                            certificate_exponent_counts.get(membership.exponent, 0) + 1
                        )
                else:
                    pair_certified = False
                    failed_generators.append(raw_poly_to_string(raw_generator))
                    pair_obstruction_degree = max(pair_obstruction_degree, membership.obstruction_degree)

            if pair_certified:
                certified_pairs += 1
            else:
                witnesses = find_witness_primes(
                    antecedent,
                    consequent,
                    start_after=max(SCAN_PRIMES),
                    limit=witness_prime_limit,
                    max_witnesses=5,
                )
                open_pairs.append(
                    PairResult(
                        antecedent=antecedent.number,
                        consequent=consequent.number,
                        failed_generators=failed_generators,
                        obstruction_degree=pair_obstruction_degree,
                        witness_primes=witnesses,
                    )
                )

    if checked_pairs != unseparated_pairs:
        raise RuntimeError(f"checked {checked_pairs} unseparated pairs, expected {unseparated_pairs}")
    if certified_pairs + len(open_pairs) != unseparated_pairs:
        raise RuntimeError("certified/open pair counts do not add up")

    return {
        "total_pairs": total_pairs,
        "separated_pairs": separated_bitset.bit_count(),
        "unseparated_pairs": unseparated_pairs,
        "checked_pairs": checked_pairs,
        "certified_pairs": certified_pairs,
        "open_pairs": open_pairs,
        "unique_antecedent_ideals": len(basis_cache),
        "unique_membership_checks": len(membership_cache),
        "max_certificate_exponent": max_certificate_exponent,
        "certificate_exponent_counts": dict(sorted(certificate_exponent_counts.items())),
        "max_open_obstruction_degree": max((pair.obstruction_degree for pair in open_pairs), default=-1),
        "arithmetic_audit": audit,
    }


def cross_checks(selected: list[EquationRecord], separated_bitset: int) -> list[str]:
    index_by_number = {record.number: index for index, record in enumerate(selected)}
    checks: list[str] = []

    def status(antecedent_number: int, consequent_number: int) -> str:
        antecedent_index = index_by_number[antecedent_number]
        consequent_index = index_by_number[consequent_number]
        bit_index = antecedent_index * len(selected) + consequent_index
        return "separated" if ((separated_bitset >> bit_index) & 1) else "unseparated"

    for antecedent_number, consequent_number, expected in [
        (1, 1, "unseparated"),
        (1, 3, "separated"),
        (2, 3, "unseparated"),
        (4, 3, "unseparated"),
        (3, 4, "separated"),
    ]:
        actual = status(antecedent_number, consequent_number)
        marker = "ok" if actual == expected else "MISMATCH"
        checks.append(f"E{antecedent_number} -> E{consequent_number}: {actual} ({marker})")
    return checks


def write_results(
    path: Path,
    source: str,
    selected: list[EquationRecord],
    scan_rows: list[dict[str, int]],
    containment: dict[str, object],
    checks: list[str],
    elapsed: float,
    max_exponent: int,
    witness_prime_limit: int,
) -> None:
    open_pairs: list[PairResult] = containment["open_pairs"]  # type: ignore[assignment]
    lines: list[str] = []
    lines.append("# Nullstellensatz Saturation Check")
    lines.append("")
    lines.append(f"Run timestamp: {time.strftime('%Y-%m-%dT%H:%M:%S%z')}")
    lines.append(f"Input source: `{source}`")
    lines.append("Scope: ETP laws with at most two variables.")
    lines.append(f"Equations in scope: {len(selected)}")
    lines.append(f"Groebner engine: internal exact Buchberger over `Q[a,b]`")
    lines.append(f"Radical-membership exponent bound: {max_exponent}")
    lines.append("")
    lines.append("## Prime-Field Scan Through 31")
    lines.append("")
    lines.append("| p | patterns | new anti-implications | cumulative anti-implications |")
    lines.append("|---:|---:|---:|---:|")
    for row in scan_rows:
        lines.append(
            f"| {row['p']} | {row['patterns']} | {row['new_anti_implications']} | "
            f"{row['cumulative_anti_implications']} |"
        )
    lines.append("")
    lines.append("## Containment Results")
    lines.append("")
    lines.append(f"Total ordered pairs: {containment['total_pairs']}")
    lines.append(f"Separated by tested primes: {containment['separated_pairs']}")
    lines.append(f"Unseparated ordered pairs checked: {containment['checked_pairs']}")
    lines.append(f"Certified radical containments: {containment['certified_pairs']}")
    lines.append(f"Open pairs: {len(open_pairs)}")
    lines.append(f"Unique antecedent ideals with Groebner bases: {containment['unique_antecedent_ideals']}")
    lines.append(f"Unique generator membership checks: {containment['unique_membership_checks']}")
    lines.append(f"Maximum certificate exponent used: {containment['max_certificate_exponent']}")
    lines.append("")
    audit: ArithmeticAudit = containment["arithmetic_audit"]  # type: ignore[assignment]
    lines.append("Arithmetic audit:")
    lines.append(
        f"- Prime factors encountered in leading coefficients during Groebner normalization: "
        f"{dict(sorted(audit.inverted_prime_counts.items()))}"
    )
    lines.append(
        f"- Prime factors appearing in final Groebner-basis denominators: "
        f"{dict(sorted(audit.basis_denominator_prime_counts.items()))}"
    )
    lines.append(f"- Largest arithmetic prime introduced by the certificates: {audit.max_arithmetic_prime}")
    lines.append(
        f"- Largest normalized leading coefficient numerator/denominator: "
        f"{audit.max_inverted_abs_numerator}/{audit.max_inverted_denominator}"
    )
    lines.append("")
    lines.append("Generator certificate exponent counts:")
    exponent_counts = containment["certificate_exponent_counts"]
    if exponent_counts:
        for exponent, count in exponent_counts.items():  # type: ignore[union-attr]
            lines.append(f"- n={exponent}: {count}")
    else:
        lines.append("- none")
    lines.append("")
    if open_pairs:
        lines.append("## Open Pairs")
        lines.append("")
        lines.append(f"Maximum obstruction normal-form degree: {containment['max_open_obstruction_degree']}")
        lines.append(f"Witness prime search limit for open pairs: {witness_prime_limit}")
        lines.append("")
        lines.append("| antecedent | consequent | obstruction degree | witness primes > 31 | failed generators |")
        lines.append("|---:|---:|---:|---|---|")
        for pair in open_pairs[:500]:
            witnesses = ", ".join(str(p) for p in pair.witness_primes) or "none found"
            failed = "; ".join(f"`{item}`" for item in pair.failed_generators)
            lines.append(
                f"| E{pair.antecedent} | E{pair.consequent} | {pair.obstruction_degree} | "
                f"{witnesses} | {failed} |"
            )
        if len(open_pairs) > 500:
            lines.append("")
            lines.append(f"Only the first 500 open pairs are displayed out of {len(open_pairs)}.")
    else:
        lines.append("## Open Pairs")
        lines.append("")
        lines.append("None. The effective prime bound is therefore 31 for this two-variable scope.")
        lines.append(
            "Every ordered pair not separated by primes <= 31 has a radical-containment certificate whose "
            "arithmetic primes are also <= 31."
        )
    lines.append("")
    lines.append("## Sanity Checks")
    lines.append("")
    for check in checks:
        lines.append(f"- {check}")
    lines.append("")
    lines.append("## Consistency")
    lines.append("")
    lines.append(
        f"`certified + open = {containment['certified_pairs']} + {len(open_pairs)} = "
        f"{containment['unseparated_pairs']}`"
    )
    lines.append(
        f"`separated + unseparated = {containment['separated_pairs']} + "
        f"{containment['unseparated_pairs']} = {containment['total_pairs']}`"
    )
    lines.append(f"Elapsed seconds: {elapsed:.3f}")
    lines.append("")
    path.write_text("\n".join(lines), encoding="utf-8")


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=RESULTS_PATH)
    parser.add_argument("--max-exponent", type=int, default=BEZOUT_EXPONENT_BOUND)
    parser.add_argument(
        "--witness-prime-limit",
        type=int,
        default=257,
        help="prime search limit used only if radical containment fails",
    )
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    started = time.perf_counter()
    records, source = load_equation_records()
    selected = [record for record in records if len(record.variables) <= 2]

    separated_bitset, scan_rows = saturation_scan(selected)
    containment = check_containments(
        selected=selected,
        separated_bitset=separated_bitset,
        max_exponent=args.max_exponent,
        witness_prime_limit=args.witness_prime_limit,
    )
    checks = cross_checks(selected, separated_bitset)
    elapsed = time.perf_counter() - started
    write_results(
        path=args.output,
        source=source,
        selected=selected,
        scan_rows=scan_rows,
        containment=containment,
        checks=checks,
        elapsed=elapsed,
        max_exponent=args.max_exponent,
        witness_prime_limit=args.witness_prime_limit,
    )

    print("Nullstellensatz check complete")
    print(f"  equations in scope: {len(selected)}")
    print(f"  total ordered pairs: {containment['total_pairs']}")
    print(f"  separated by tested primes: {containment['separated_pairs']}")
    print(f"  unseparated checked: {containment['checked_pairs']}")
    print(f"  certified radical containments: {containment['certified_pairs']}")
    print(f"  open pairs: {len(containment['open_pairs'])}")
    print(f"  max certificate exponent: {containment['max_certificate_exponent']}")
    print(f"  output: {args.output}")
    print(f"  elapsed seconds: {elapsed:.3f}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
