#!/usr/bin/env python3
"""Nullstellensatz containment checks for exactly-three-variable ETP laws.

This is the three-variable analogue of ``nullstellensatz_check.py``.  The
coefficient ideals still live in Q[a,b], but each selected law has coefficient
generators for x, y, and z.  The script recomputes the prime-field
anti-implication scan through 31 and then checks every ordered pair not
separated by that scan.

The expensive pass is grouped by coefficient ideal.  Equations with identical
raw coefficient ideals share one representative for modular separation checks,
and radical-membership tests are cached by the reduced Groebner basis over
Q[a,b].  This keeps the exact containment pass at the ideal-class level while
still reporting equation-pair counts.
"""

from __future__ import annotations

import argparse
import time
from collections import Counter, OrderedDict
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable

import nullstellensatz_check as base


SCRIPT_DIR = Path(__file__).resolve().parent
RESULTS_PATH = SCRIPT_DIR / "nullstellensatz_3var_results.md"
BEZOUT_EXPONENT_BOUND = base.BEZOUT_EXPONENT_BOUND


@dataclass
class IdealClass:
    signature: tuple[base.PolyKey, ...]
    representative_index: int
    representative: base.EquationRecord
    numbers: list[int]
    basis_key: tuple[base.PolyKey, ...] | None = None

    @property
    def size(self) -> int:
        return len(self.numbers)

    @property
    def generator_keys(self) -> tuple[base.PolyKey, ...]:
        return tuple(base.raw_poly_to_key(poly) for poly in self.representative.ideal if poly)

    @property
    def generator_strings(self) -> tuple[str, ...]:
        return tuple(base.raw_poly_to_string(poly) for poly in self.representative.ideal if poly)


@dataclass
class OpenClassPair:
    antecedent_numbers: tuple[int, ...]
    consequent_numbers: tuple[int, ...]
    multiplicity: int
    failed_generators: tuple[str, ...]
    obstruction_degree: int
    witness_primes: tuple[int, ...]


def load_three_variable_records() -> tuple[list[base.EquationRecord], str]:
    records, source = base.load_equation_records()
    selected = [record for record in records if len(record.variables) == 3]
    validate_three_variable_scope(selected)
    return selected, source


def validate_three_variable_scope(selected: Iterable[base.EquationRecord]) -> None:
    for record in selected:
        if record.variables != ("x", "y", "z"):
            raise ValueError(
                f"E{record.number} has unexpected variables {record.variables}; "
                "the 3-variable checker expects canonical x,y,z laws"
            )
        for variable, raw_poly in zip(base.VARS, record.ideal, strict=True):
            if raw_poly and variable not in record.variables:
                raise ValueError(f"E{record.number} has a nonzero {variable}-coefficient generator")


def build_ideal_classes(selected: list[base.EquationRecord]) -> list[IdealClass]:
    classes_by_signature: OrderedDict[tuple[base.PolyKey, ...], IdealClass] = OrderedDict()
    for index, record in enumerate(selected):
        signature = base.ideal_signature(record)
        ideal_class = classes_by_signature.get(signature)
        if ideal_class is None:
            classes_by_signature[signature] = IdealClass(
                signature=signature,
                representative_index=index,
                representative=record,
                numbers=[record.number],
            )
        else:
            ideal_class.numbers.append(record.number)
    return list(classes_by_signature.values())


def compute_class_groebner_bases(
    classes: list[IdealClass],
    audit: base.ArithmeticAudit,
) -> Counter[tuple[base.PolyKey, ...]]:
    basis_counts: Counter[tuple[base.PolyKey, ...]] = Counter()
    for ideal_class in classes:
        basis = base.groebner_basis(base.ideal_generators(ideal_class.representative), audit)
        ideal_class.basis_key = base.groebner_key(basis)
        basis_counts[ideal_class.basis_key] += ideal_class.size
    return basis_counts


def class_pair_is_separated(
    row_bits: int,
    consequent: IdealClass,
) -> bool:
    return bool((row_bits >> consequent.representative_index) & 1)


def find_witness_primes_for_class_pair(
    antecedent: IdealClass,
    consequent: IdealClass,
    witness_prime_limit: int,
) -> tuple[int, ...]:
    witnesses = base.find_witness_primes(
        antecedent=antecedent.representative,
        consequent=consequent.representative,
        start_after=max(base.SCAN_PRIMES),
        limit=witness_prime_limit,
        max_witnesses=5,
    )
    return tuple(witnesses)


def check_containments_by_ideal_class(
    selected: list[base.EquationRecord],
    classes: list[IdealClass],
    separated_bitset: int,
    max_exponent: int,
    witness_prime_limit: int,
    progress_interval: float,
) -> dict[str, object]:
    total_pairs = len(selected) * len(selected)
    separated_pairs = separated_bitset.bit_count()
    expected_unseparated_pairs = total_pairs - separated_pairs
    row_mask = (1 << len(selected)) - 1

    audit = base.ArithmeticAudit.empty()
    basis_counts = compute_class_groebner_bases(classes, audit)
    membership_cache: dict[tuple[tuple[base.PolyKey, ...], base.PolyKey], base.MembershipResult] = {}

    checked_pairs = 0
    checked_class_pairs = 0
    certified_pairs = 0
    open_pairs = 0
    open_class_pairs: list[OpenClassPair] = []
    class_separated_pairs = 0
    max_certificate_exponent = 0
    certificate_exponent_counts: Counter[int] = Counter()
    last_progress = time.perf_counter()

    for antecedent_class_index, antecedent in enumerate(classes, start=1):
        if antecedent.basis_key is None:
            raise RuntimeError("Groebner basis cache was not initialized")
        basis_key = antecedent.basis_key
        row_bits = (separated_bitset >> (antecedent.representative_index * len(selected))) & row_mask

        for consequent in classes:
            multiplicity = antecedent.size * consequent.size
            if class_pair_is_separated(row_bits, consequent):
                class_separated_pairs += multiplicity
                continue

            checked_class_pairs += 1
            checked_pairs += multiplicity
            pair_certified = True
            failed_generators: list[str] = []
            pair_obstruction_degree = -1

            for generator_key, generator_string in zip(
                consequent.generator_keys,
                consequent.generator_strings,
                strict=True,
            ):
                cache_key = (basis_key, generator_key)
                membership = membership_cache.get(cache_key)
                if membership is None:
                    membership = base.radical_membership_by_powers(
                        generator_key=generator_key,
                        basis_key=basis_key,
                        max_exponent=max_exponent,
                    )
                    membership_cache[cache_key] = membership

                if membership.contained:
                    if membership.exponent is not None:
                        max_certificate_exponent = max(max_certificate_exponent, membership.exponent)
                        certificate_exponent_counts[membership.exponent] += multiplicity
                else:
                    pair_certified = False
                    failed_generators.append(generator_string)
                    pair_obstruction_degree = max(pair_obstruction_degree, membership.obstruction_degree)

            if pair_certified:
                certified_pairs += multiplicity
            else:
                open_pairs += multiplicity
                open_class_pairs.append(
                    OpenClassPair(
                        antecedent_numbers=tuple(antecedent.numbers),
                        consequent_numbers=tuple(consequent.numbers),
                        multiplicity=multiplicity,
                        failed_generators=tuple(failed_generators),
                        obstruction_degree=pair_obstruction_degree,
                        witness_primes=find_witness_primes_for_class_pair(
                            antecedent,
                            consequent,
                            witness_prime_limit,
                        ),
                    )
                )

        now = time.perf_counter()
        if progress_interval > 0 and now - last_progress >= progress_interval:
            print(
                "  containment progress: "
                f"{antecedent_class_index}/{len(classes)} ideal classes, "
                f"{checked_pairs} unseparated equation pairs checked, "
                f"{len(membership_cache)} unique memberships",
                flush=True,
            )
            last_progress = now

    if class_separated_pairs != separated_pairs:
        raise RuntimeError(
            f"class-level separated count {class_separated_pairs} does not match bitset count {separated_pairs}"
        )
    if checked_pairs != expected_unseparated_pairs:
        raise RuntimeError(f"checked {checked_pairs} unseparated pairs, expected {expected_unseparated_pairs}")
    if separated_pairs + certified_pairs + open_pairs != total_pairs:
        raise RuntimeError("separated/certified/open pair counts do not add up")

    return {
        "total_pairs": total_pairs,
        "separated_pairs": separated_pairs,
        "unseparated_pairs": expected_unseparated_pairs,
        "checked_pairs": checked_pairs,
        "checked_class_pairs": checked_class_pairs,
        "certified_pairs": certified_pairs,
        "open_pairs": open_pairs,
        "open_class_pairs": open_class_pairs,
        "raw_ideal_classes": len(classes),
        "reduced_groebner_ideals": len(basis_counts),
        "largest_raw_ideal_class": max((ideal_class.size for ideal_class in classes), default=0),
        "largest_reduced_groebner_class": max(basis_counts.values(), default=0),
        "unique_membership_checks": len(membership_cache),
        "max_certificate_exponent": max_certificate_exponent,
        "certificate_exponent_counts": dict(sorted(certificate_exponent_counts.items())),
        "max_open_obstruction_degree": max(
            (pair.obstruction_degree for pair in open_class_pairs),
            default=-1,
        ),
        "arithmetic_audit": audit,
    }


def saturation_prime(scan_rows: list[dict[str, int]]) -> int | None:
    last_new_prime: int | None = None
    for row in scan_rows:
        if row["new_anti_implications"]:
            last_new_prime = row["p"]
    return last_new_prime


def arithmetic_primes(audit: base.ArithmeticAudit) -> list[int]:
    return sorted(set(audit.inverted_prime_counts) | set(audit.basis_denominator_prime_counts))


def write_results(
    path: Path,
    source: str,
    selected: list[base.EquationRecord],
    classes: list[IdealClass],
    scan_rows: list[dict[str, int]],
    containment: dict[str, object],
    elapsed: float,
    max_exponent: int,
    witness_prime_limit: int,
) -> None:
    audit: base.ArithmeticAudit = containment["arithmetic_audit"]  # type: ignore[assignment]
    open_class_pairs: list[OpenClassPair] = containment["open_class_pairs"]  # type: ignore[assignment]
    open_pair_count = int(containment["open_pairs"])

    lines: list[str] = []
    lines.append("# Nullstellensatz Saturation Check for 3-Variable ETP Laws")
    lines.append("")
    lines.append(f"Run timestamp: {time.strftime('%Y-%m-%dT%H:%M:%S%z')}")
    lines.append(f"Input source: `{source}`")
    lines.append("Scope: ETP laws with exactly three variables.")
    lines.append(f"Equations in scope: {len(selected)}")
    lines.append("Coefficient ring: `Q[a,b]`; nonzero coefficient generators are for `x,y,z`.")
    lines.append("Groebner engine: internal exact Buchberger over `Q[a,b]`")
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
    lines.append(f"Saturation prime within the scan: {saturation_prime(scan_rows)}")
    lines.append("")
    lines.append("## Ideal Grouping")
    lines.append("")
    lines.append(f"Raw coefficient ideal classes: {containment['raw_ideal_classes']}")
    lines.append(f"Distinct reduced Groebner ideals over `Q[a,b]`: {containment['reduced_groebner_ideals']}")
    lines.append(f"Largest raw ideal class: {containment['largest_raw_ideal_class']} equations")
    lines.append(f"Largest reduced Groebner ideal class: {containment['largest_reduced_groebner_class']} equations")
    lines.append(f"Unseparated raw ideal-class pairs checked: {containment['checked_class_pairs']}")
    lines.append(f"Unique generator membership checks: {containment['unique_membership_checks']}")
    lines.append("")
    lines.append("## Containment Results")
    lines.append("")
    lines.append(f"Total 3-var ordered pairs: {containment['total_pairs']}")
    lines.append(f"Separated by primes <= 31: {containment['separated_pairs']}")
    lines.append(f"Unseparated ordered pairs checked: {containment['checked_pairs']}")
    lines.append(f"Certified radical containments: {containment['certified_pairs']}")
    lines.append(f"Open pairs: {open_pair_count}")
    lines.append(f"Maximum certificate exponent: {containment['max_certificate_exponent']}")
    lines.append("")
    lines.append("Arithmetic primes encountered:")
    lines.append(f"- All arithmetic primes: {arithmetic_primes(audit)}")
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
    lines.append("## Open Pairs")
    lines.append("")
    if open_class_pairs:
        lines.append(f"Maximum obstruction normal-form degree: {containment['max_open_obstruction_degree']}")
        lines.append(f"Witness prime search limit for open pairs: {witness_prime_limit}")
        lines.append("")
        lines.append("| antecedent | consequent | obstruction degree | witness primes > 31 | failed generators |")
        lines.append("|---:|---:|---:|---|---|")
        for class_pair in open_class_pairs:
            witnesses = ", ".join(str(prime) for prime in class_pair.witness_primes) or "none found"
            failed = "; ".join(f"`{item}`" for item in class_pair.failed_generators)
            for antecedent_number in class_pair.antecedent_numbers:
                for consequent_number in class_pair.consequent_numbers:
                    lines.append(
                        f"| E{antecedent_number} | E{consequent_number} | "
                        f"{class_pair.obstruction_degree} | {witnesses} | {failed} |"
                    )
    else:
        lines.append("None.")
    lines.append("")
    lines.append("## Consistency")
    lines.append("")
    lines.append(
        f"`separated + certified + open = {containment['separated_pairs']} + "
        f"{containment['certified_pairs']} + {open_pair_count} = {containment['total_pairs']}`"
    )
    lines.append(
        f"`checked unseparated = certified + open = {containment['certified_pairs']} + "
        f"{open_pair_count} = {containment['checked_pairs']}`"
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
    parser.add_argument(
        "--progress-interval",
        type=float,
        default=30.0,
        help="seconds between containment progress messages; use 0 to disable",
    )
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    started = time.perf_counter()

    selected, source = load_three_variable_records()
    classes = build_ideal_classes(selected)
    print(f"Loaded {len(selected)} exactly-three-variable equations from {source}")
    print(f"Grouped into {len(classes)} raw coefficient ideal classes")

    separated_bitset, scan_rows = base.saturation_scan(selected)
    print(f"Prime scan through 31 separated {separated_bitset.bit_count()} ordered pairs")

    containment = check_containments_by_ideal_class(
        selected=selected,
        classes=classes,
        separated_bitset=separated_bitset,
        max_exponent=args.max_exponent,
        witness_prime_limit=args.witness_prime_limit,
        progress_interval=args.progress_interval,
    )

    elapsed = time.perf_counter() - started
    write_results(
        path=args.output,
        source=source,
        selected=selected,
        classes=classes,
        scan_rows=scan_rows,
        containment=containment,
        elapsed=elapsed,
        max_exponent=args.max_exponent,
        witness_prime_limit=args.witness_prime_limit,
    )

    print("3-variable Nullstellensatz check complete")
    print(f"  equations in scope: {len(selected)}")
    print(f"  total ordered pairs: {containment['total_pairs']}")
    print(f"  separated by primes <= 31: {containment['separated_pairs']}")
    print(f"  unseparated checked: {containment['checked_pairs']}")
    print(f"  certified radical containments: {containment['certified_pairs']}")
    print(f"  open pairs: {containment['open_pairs']}")
    print(f"  max certificate exponent: {containment['max_certificate_exponent']}")
    print(f"  arithmetic primes: {arithmetic_primes(containment['arithmetic_audit'])}")  # type: ignore[arg-type]
    print(f"  output: {args.output}")
    print(f"  elapsed seconds: {elapsed:.3f}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
