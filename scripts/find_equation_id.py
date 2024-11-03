#!/usr/bin/env python3

import argparse
import itertools
from typing import List, NamedTuple, Tuple, Union, Iterator

VAR_NAMES = "xyzwuvrst"

ExprType = Union[str, Tuple["ExprType", str, "ExprType"]]
ShapeType = Union[None, Tuple["ShapeType", "ShapeType"]]


class Equation(NamedTuple):
    lhs_shape: ShapeType
    rhs_shape: ShapeType
    leaves: List[int]

    @classmethod
    def from_trees(cls, lhs_tree: ExprType, rhs_tree: ExprType) -> "Equation":
        lhs_shape, lhs_leaves = cls._deconstruct_tree(lhs_tree)
        rhs_shape, rhs_leaves = cls._deconstruct_tree(rhs_tree)
        return cls(lhs_shape, rhs_shape, lhs_leaves + rhs_leaves)

    @classmethod
    def _deconstruct_tree(cls, tree: ExprType) -> Tuple[ShapeType, List[int]]:
        if isinstance(tree, str):
            return (None, [VAR_NAMES.index(tree)])
        left, _op, right = tree
        left_shape, left_leaves = cls._deconstruct_tree(left)
        right_shape, right_leaves = cls._deconstruct_tree(right)
        return ((left_shape, right_shape), left_leaves + right_leaves)

    def __str__(self) -> str:
        leaves_iter = iter(self.leaves)
        lhs_str = Equation._expr_str(self.lhs_shape, leaves_iter, False)
        rhs_str = Equation._expr_str(self.rhs_shape, leaves_iter, False)
        return f"{lhs_str} = {rhs_str}"

    @classmethod
    def _expr_str(cls, shape: ShapeType, leaves_iter: Iterator[int], parenthesize: bool) -> str:
        if shape is None:
            return VAR_NAMES[next(leaves_iter)]
        left_str = cls._expr_str(shape[0], leaves_iter, True)
        right_str = cls._expr_str(shape[1], leaves_iter, True)
        if parenthesize:
            return f"({left_str} ◇ {right_str})"
        return f"{left_str} ◇ {right_str}"


def shape_order(shape: ShapeType) -> int:
    if shape is None:
        return 0
    return 1 + shape_order(shape[0]) + shape_order(shape[1])


def shape_treecmp(shape1: ShapeType, shape2: ShapeType) -> int:
    if shape1 is None and shape2 is None:
        return 0
    if shape1 is None and isinstance(shape2, tuple):
        return -1
    if isinstance(shape1, tuple) and shape2 is None:
        return 1
    left_cmp = shape_treecmp(shape1[0], shape2[0])
    if left_cmp != 0:
        return left_cmp
    return shape_treecmp(shape1[1], shape2[1])


def shape_lt(shape1: ShapeType, shape2: ShapeType) -> bool:
    shape1_order = shape_order(shape1)
    shape2_order = shape_order(shape2)
    if shape1_order < shape2_order:
        return True
    if shape1_order > shape2_order:
        return False
    if shape_treecmp(shape1, shape2) < 0:
        return True
    return False


def tokenize(expr: str) -> List[str]:
    """Convert an expression string into a list of tokens."""
    expr = (
        expr.replace(".", "◇")
        .replace("*", "◇")
        .replace("(", " ( ")
        .replace(")", " ) ")
        .replace("◇", " ◇ ")
    )
    return [token for token in expr.split() if token]


def parse_expr(tokens: List[str]) -> ExprType:
    """Parse a list of tokens into an expression tree."""

    def parse_element() -> ExprType:
        if not tokens:
            raise ValueError("Unexpected end of expression")
        if tokens[0] in VAR_NAMES:
            return tokens.pop(0)
        if tokens[0] == "(":
            tokens.pop(0)  # Remove opening parenthesis
            left = parse_element()
            if not tokens or tokens[0] != "◇":
                raise ValueError("Expected '◇' after element in parentheses")
            tokens.pop(0)  # Remove '◇'
            right = parse_element()
            if not tokens or tokens[0] != ")":
                raise ValueError("Missing closing parenthesis")
            tokens.pop(0)  # Remove closing parenthesis
            return (left, "◇", right)
        raise ValueError(f"Unexpected token: {tokens[0]}")

    result = parse_element()
    if tokens:
        if tokens[0] != "◇":
            raise ValueError(f"Unexpected token after main element: {tokens[0]}")
        tokens.pop(0)  # Remove '◇'
        right = parse_element()
        if tokens:
            raise ValueError(
                f"Unexpected tokens at the end of expression: {' '.join(tokens)}"
            )
        result = (result, "◇", right)
    return result


def canonicalize_partition(partition: List[int]) -> List[int]:
    """Canonicalize the partition to increasing order."""
    result, elts = [], []
    for x in partition:
        if x not in elts:
            elts.append(x)
        result.append(elts.index(x))
    return result


def canonicalize_equation(eq_str: str) -> Equation:
    """Canonicalize an equation string."""
    try:
        lhs, rhs = eq_str.split("=")
    except ValueError:
        raise ValueError("No '=' found in the equation.")

    lhs = parse_expr(tokenize(lhs))
    rhs = parse_expr(tokenize(rhs))

    eq = Equation.from_trees(lhs, rhs)

    if shape_lt(eq.rhs_shape, eq.lhs_shape):
        eq = Equation.from_trees(rhs, lhs)

    leaves = canonicalize_partition(eq.leaves)

    return Equation(eq.lhs_shape, eq.rhs_shape, leaves)


def generate_shapes(order: int) -> Iterator[ShapeType]:
    """Generate all possible shapes for expressions with a given number of forks."""
    if order == 0:
        yield None
    for i in range(order):
        for left in generate_shapes(i):
            for right in generate_shapes(order - 1 - i):
                yield (left, right)


def _partitions_help(n: int, max_used: int) -> Iterator[List[int]]:
    if n == 0:
        yield []
        return
    for x in range(max_used + 2):
        for next in _partitions_help(n - 1, max(max_used, x)):
            yield [x] + next


def partitions(n: int) -> Iterator[List[int]]:
    """Generate all partitions of a given number."""
    if n == 0:
        yield []
        return
    for next in _partitions_help(n, 0):
        yield [0] + next


def generate_all_eqs() -> Iterator[Equation]:
    """Generate all unique equations up to symmetry."""
    for order in itertools.count():
        half = order // 2 + 1
        for lhs_order in range(half):
            for lhs_shape in generate_shapes(lhs_order):
                for rhs_shape in generate_shapes(order - lhs_order):
                    if order == lhs_order * 2 and shape_lt(rhs_shape, lhs_shape):
                        continue
                    symmetric_shape = lhs_shape == rhs_shape
                    for leaves in partitions(order + 1):
                        if symmetric_shape:
                            flipped = leaves[half:] + leaves[:half]
                            if canonicalize_partition(flipped) < leaves:
                                continue
                            if leaves == flipped and order > 0:
                                continue
                        yield Equation(lhs_shape, rhs_shape, leaves)


def wrap_tqdm(iterable):
    try:
        from tqdm import tqdm
    except ImportError:
        return iterable
    return tqdm(iterable, delay=2, unit=" eqs", leave=False)


def find_equation_id(input_eq: Equation) -> Tuple[int, Equation]:
    for eq_num, eq in enumerate(wrap_tqdm(generate_all_eqs()), 1):
        if eq == input_eq:
            return eq_num, eq


def get_equation_by_id(input_eq: int) -> Equation:
    for eq_num, eq in enumerate(wrap_tqdm(generate_all_eqs()), 1):
        if eq_num == input_eq:
            return eq


def process_equation(eq_str: str) -> None:
    """Process a given equation, finding its number and canonical form."""
    try:
        input_eq = int(eq_str)
    except ValueError:
        input_eq = canonicalize_equation(eq_str)

    if isinstance(input_eq, Equation):
        eq_num, eq = find_equation_id(input_eq)
        print(f"The equation '{eq_str}' is Equation {eq_num}: {eq}")
    if isinstance(input_eq, int):
        eq = get_equation_by_id(input_eq)
        print(f"Equation {input_eq}: {eq}")


def main():
    """Main function to run the program."""
    parser = argparse.ArgumentParser(
        description="Canonicalize equations and find their numbers."
    )
    parser.add_argument(
        "equation",
        nargs="?",
        help="The equation to canonicalize (if not in interactive mode)",
    )
    parser.add_argument(
        "--interactive", "-i", action="store_true", help="Run in interactive mode"
    )

    args = parser.parse_args()

    if args.interactive:
        print("Welcome to the interactive equation canonicalizer!")
        print("Type 'exit' or 'quit' to end the session.")
        while True:
            eq = input("Enter an equation: ").strip()
            if eq.lower() in ["exit", "quit"]:
                print("Goodbye!")
                break
            process_equation(eq)
    elif args.equation:
        process_equation(args.equation)
    else:
        parser.print_help()


if __name__ == "__main__":
    main()
