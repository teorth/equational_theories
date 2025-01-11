#!/usr/bin/env python3

"""This module maps magma equations from/to their id

It can be used a script, with a (space-separated) list of ids or of
equations (in which the operation can be ".", "*", or "◇"), optionally
preceeded by "*" to dualize the equation, or used in interactive mode:

    python find_equation_id.py 1234 "(w*u)=t*(u*x)" 4567 "*89" "*67" "0=(1*2)*(0*1)"

    python find_equation_id.py -i

When used as a module imported in python code, one can use
- eq = Equation.from_id(integer id)
- eq = Equation.from_str(string)
- eq.id()
- all_eqs(integer order)
- eq.dual()

The theory of magma operations and their labeling is explained in
https://teorth.github.io/equational_theories/blueprint/basic-theory-chapter.html

"""

import argparse
import itertools
import typing
import functools
from sympy.functions.combinatorial.numbers import bell, binomial, catalan
import math
import string

VAR_NAMES = "xyzwuvrst"

ExprType = typing.Union[str, int, typing.Tuple["ExprType", str, "ExprType"]]
ShapeType = typing.Union[None, typing.Tuple["ShapeType", "ShapeType"]]


class Equation(typing.NamedTuple):
    """Equation(lhs_shape, rhs_shape, rhyme) denotes an equation

    lhs_shape and rhs_shape are nested pairs (tuples) of None giving how
    the operation is nested, and rhyme a list of int (starting with 0)
    giving the rhyme scheme (variable names, as numbers).  For instance,
    Equation(None, ((None, None), None), [0, 1, 0, 2]) is x=(y*x)*z.
    """
    lhs_shape: ShapeType
    rhs_shape: ShapeType
    rhyme: typing.List[int]

    @classmethod
    def from_id(cls, eq_id: int) -> "Equation":
        """Construct an equation given its id."""
        return _equation_from_id(eq_id)

    @property
    def id(self) -> int:
        """Evaluate the id of the equation."""
        return _equation_id(self)

    @classmethod
    def from_str(cls, eq_str: str) -> "Equation":
        """Parse and canonicalize an equation given as a string."""
        return _equation_from_str(eq_str)

    def __str__(self) -> str:
        rhyme_iter = iter(self.rhyme)
        lhs_str = Equation._expr_str(self.lhs_shape, rhyme_iter, False)
        rhs_str = Equation._expr_str(self.rhs_shape, rhyme_iter, False)
        return f"{lhs_str} = {rhs_str}"

    @classmethod
    def _expr_str(cls, shape: ShapeType, rhyme_iter: typing.Iterator[int], parenthesize: bool) -> str:
        if shape is None:
            i, j = divmod(next(rhyme_iter), len(VAR_NAMES))
            if i == 0:
                return VAR_NAMES[j]
            return VAR_NAMES[j] + str(i)
        left_str = cls._expr_str(shape[0], rhyme_iter, True)
        right_str = cls._expr_str(shape[1], rhyme_iter, True)
        if parenthesize:
            return f"({left_str} ◇ {right_str})"
        return f"{left_str} ◇ {right_str}"

    def orders(self) -> typing.Tuple[int, int]:
        """Number of operations on the lhs and rhs as a tuple."""
        return (shape_order(self.lhs_shape), shape_order(self.rhs_shape))

    def num_vars(self) -> int:
        """Number of distinct variables in the equation."""
        return max(self.rhyme) + 1

    def dual(self) -> "Equation":
        """Swap all left and right operands, swap lhs and rhs if needed."""
        lhs_shape = shape_dual(self.lhs_shape)
        rhs_shape = shape_dual(self.rhs_shape)
        lhs_order = shape_order(self.lhs_shape)
        lhs_rhyme = list(reversed(self.rhyme[:lhs_order + 1]))
        rhs_rhyme = list(reversed(self.rhyme[lhs_order + 1:]))
        if shape_lt(rhs_shape, lhs_shape):
            lhs_shape, rhs_shape = rhs_shape, lhs_shape
            lhs_rhyme, rhs_rhyme = rhs_rhyme, lhs_rhyme
        rhyme = canonicalize_rhyme(lhs_rhyme + rhs_rhyme)
        if lhs_shape == rhs_shape:
            rhyme = min(rhyme, canonicalize_rhyme(rhs_rhyme + lhs_rhyme))
        return Equation(lhs_shape, rhs_shape, rhyme)

##### Parsing an equation string

def _tokenize(expr: str) -> typing.List[str]:
    """Convert an expression string into a list of tokens."""
    expr = (
        expr.replace(".", "◇")
        .replace("*", "◇")
        .replace("(", " ( ")
        .replace(")", " ) ")
        .replace("◇", " ◇ ")
    )
    return [token for token in expr.split() if token]


def _parse_expr(tokens: typing.List[str]) -> ExprType:
    """Parse a list of tokens into an expression tree.

    Return nested triplets (left, "◇", right) with variables as str or int."""

    def parse_element() -> ExprType:
        if not tokens:
            raise ValueError("Unexpected end of expression")
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
        if (tokens[0].isidentifier() or tokens[0] == "0" or
            (tokens[0][0] in "123456789" and
             all(c in "0123456789" for c in tokens[0][1:]))):
            return tokens.pop(0)
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


def _deconstruct_tree(tree: ExprType) -> typing.Tuple[ShapeType, typing.List[str]]:
    if isinstance(tree, str):
        return (None, [tree])
    left, _op, right = tree
    left_shape, left_rhyme = _deconstruct_tree(left)
    right_shape, right_rhyme = _deconstruct_tree(right)
    return ((left_shape, right_shape), left_rhyme + right_rhyme)


def _equation_from_str(eq_str: str) -> Equation:
    try:
        lhs, rhs = eq_str.split("=")
    except ValueError:
        raise ValueError("No '=' or two '=' found in the equation.")
    lhs = _parse_expr(_tokenize(lhs))
    rhs = _parse_expr(_tokenize(rhs))
    lhs_shape, lhs_rhyme = _deconstruct_tree(lhs)
    rhs_shape, rhs_rhyme = _deconstruct_tree(rhs)
    if shape_lt(rhs_shape, lhs_shape):
        lhs_shape, rhs_shape = rhs_shape, lhs_shape
        lhs_rhyme, rhs_rhyme = rhs_rhyme, lhs_rhyme
    rhyme = canonicalize_rhyme(lhs_rhyme + rhs_rhyme)
    if lhs_shape == rhs_shape:
        rhyme = min(rhyme, canonicalize_rhyme(rhs_rhyme + lhs_rhyme))
    return Equation(lhs_shape, rhs_shape, rhyme)


##### On shapes

def shape_dual(shape: ShapeType) -> ShapeType:
    if shape is None:
        return None
    return (shape_dual(shape[1]), shape_dual(shape[0]))

def shape_order(shape: ShapeType) -> int:
    if shape is None:
        return 0
    return 1 + shape_order(shape[0]) + shape_order(shape[1])


def shape_cmp(shape1: ShapeType, shape2: ShapeType) -> int:
    shape1_order = shape_order(shape1)
    shape2_order = shape_order(shape2)
    if shape1_order < shape2_order:
        return -1
    if shape1_order > shape2_order:
        return 1
    if shape1 is None and shape2 is None:
        return 0
    left_cmp = shape_cmp(shape1[0], shape2[0])
    if left_cmp != 0:
        return left_cmp
    return shape_cmp(shape1[1], shape2[1])


def shape_lt(shape1: ShapeType, shape2: ShapeType) -> bool:
    return shape_cmp(shape1, shape2) < 0


##### Generating all rhymes, all shapes, all equations

def canonicalize_rhyme(rhyme: typing.List[int]) -> typing.List[int]:
    """Canonicalize the rhyme to increasing order."""
    variables = {}
    for x in rhyme:
        if x not in variables:
            variables[x] = len(variables)
    return [variables[x] for x in rhyme]


def all_rhymes(n: int) -> typing.Iterator[typing.List[int]]:
    """Generate all rhymes of a given length."""
    if n == 0:
        yield []
        return
    for next in _all_rhymes_help(n, 0):
        yield [0] + next


def _all_rhymes_help(n: int, max_used: int) -> typing.Iterator[typing.List[int]]:
    """Generates all rhymes whose minimum is at most max_used + 1"""
    if n == 0:
        yield []
        return
    for x in range(max_used + 2):
        for next in _all_rhymes_help(n - 1, max(max_used, x)):
            yield [x] + next


def all_shapes(order: int) -> typing.Iterator[ShapeType]:
    """Generate all possible shapes for expressions with a given number of operations."""
    if order == 0:
        yield None
    for i in range(order):
        for left in all_shapes(i):
            for right in all_shapes(order - 1 - i):
                yield (left, right)


def all_eqs(order: int) -> typing.Iterator[Equation]:
    """Generate all unique equations of some order up to symmetry.

    To generate unique equations of all orders, use
    (eq for n in itertools.count() for eq in all_eqs(n)).
    """
    half = order // 2 + 1
    for lhs_order in range(half):
        for lhs_shape in all_shapes(lhs_order):
            for rhs_shape in all_shapes(order - lhs_order):
                if order == lhs_order * 2 and shape_lt(rhs_shape, lhs_shape):
                    continue
                symmetric_shape = lhs_shape == rhs_shape
                for rhyme in all_rhymes(order + 1):
                    if symmetric_shape:
                        flipped = rhyme[half:] + rhyme[:half]
                        if canonicalize_rhyme(flipped) < rhyme:
                            continue
                        if rhyme == flipped and order > 0:
                            continue
                    yield Equation(lhs_shape, rhs_shape, rhyme)


##### Recursive approach to mapping from equation number to id and vice-versa

# Counting equations of some order, based on https://oeis.org/A103293, refactored to access intermediate results.

@functools.lru_cache(maxsize=None)
def num_eqs(n: int) -> int:
    """Sequence https://oeis.org/A376640 of the number of magma equations"""
    if n % 2 == 1:
        return catalan(n + 1) * bell(n + 2) // 2
    else:
        if n == 0: return 2
        return ((catalan(n + 1) - catalan(n // 2)) * bell(n + 2) // 2
                + catalan(n // 2) * bell_same_shape(n))


@functools.lru_cache(maxsize=None)
def bell_same_shape(n: int) -> int:
    """Number of rhymes when lhs and rhs have the same (n//2)-operations shape"""
    if n == 0:
        return 2
    return (bell(n + 2) + sum(stirling_sym(n + 2, k) for k in range(n + 3))
            - 2 * bell(1 + n // 2)) // 2


@functools.lru_cache(maxsize=None)
def stirling_sym(n: int, k: int) -> int:
    """Number of symmetric k-partitions of range(n), see https://oeis.org/A103293"""
    if n < 2:
        return k == n
    return k * stirling_sym(n - 2, k) + stirling_sym(n - 2, k - 1) + stirling_sym(n - 2, k - 2)


# Map from shape to id and back

def shape_id(shape: ShapeType) -> int:
    """Gives the shape id (zero-based) among shapes of a given order"""
    return _shape_id_help(shape, shape_order(shape))


def _shape_id_help(shape: ShapeType, n: int) -> int:
    if n == 0:
        return 0
    lhs_shape, rhs_shape = shape
    lhs_n = shape_order(lhs_shape)
    rhs_n = n - 1 - lhs_n
    return (sum(catalan(n1) * catalan(n - n1 - 1) for n1 in range(lhs_n))
            + _shape_id_help(lhs_shape, lhs_n) * catalan(rhs_n)
            + _shape_id_help(rhs_shape, rhs_n))


def shape_from_id(nodes: int, tree_num: int) -> ShapeType:
    if nodes == 0:
        if tree_num != 0:
            raise ValueError
        return None
    for n1 in range(nodes):
        test_num = catalan(n1) * catalan(nodes - n1 - 1)
        if tree_num >= test_num:
            tree_num -= test_num
            continue
        tree_num_1, tree_num_2 = divmod(tree_num, catalan(nodes - n1 - 1))
        return (shape_from_id(n1, tree_num_1),
                shape_from_id(nodes - n1 - 1, tree_num_2))



# Map from rhyme to id and back

@functools.lru_cache(maxsize=None)
def _num_rhyme_help(n: int, max_used: int) -> int:
    """Number of rhymes of n slots whose minimum number is at most max_used + 1"""
    if n==0:
        return 1
    return (max_used + 1) * _num_rhyme_help(n - 1, max_used) + _num_rhyme_help(n - 1, max_used + 1)


def find_rhyme_id(p: typing.List[int]) -> int:
    """Gives the rhyme id (zero-based) among rhymes with a given number of variables"""
    if (not p) or p[0]:
        raise ValueError(f"Argument of find_rhyme_id should be [0,...] not {p}")
    return _find_rhyme_id_help(p[1:], 0)


def _find_rhyme_id_help(p: typing.List[int], max_used: int) -> int:
    return p[0] * _num_rhyme_help(len(p)-1, max_used) + _find_rhyme_id_help(p[1:], max(p[0], max_used)) if p else 0


def get_rhyme_by_id(n: int, rhyme_num: int, max_used: int = 0) -> typing.List[int]:
    """Find a rhyme scheme for n slots by its number (zero-indexed)."""
    result = [0]
    while n > 0:
        var1 = min(max_used + 1, rhyme_num // _num_rhyme_help(n - 1, max_used))
        result += [var1]
        rhyme_num -= var1 * _num_rhyme_help(n - 1, max_used)
        max_used = max(max_used, var1)
        n -= 1
    return result


# Map from equation to id and back.

@functools.lru_cache(maxsize=None)
def _num_eqs_unbalanced(n: int) -> int:
    """Counts magma equations that have strictly fewer operations on the left than on the right"""
    return ((catalan(n + 1) - (0 if n % 2 == 1 else catalan(n // 2) ** 2))
            * bell(n + 2)) // 2


def _num_eqs_balanced(n: int, l: int, r: int) -> int:
    """Number of balanced equations before lhs/rhs shapes number l, r"""
    return (bell(n + 2) * (catalan(n // 2) * l - l * (l + 1) // 2
                           + r - l - (1 if r > l else 0))
            + bell_same_shape(n) * (l + (1 if r > l else 0)))


def _equation_id(input_eq: Equation) -> typing.Tuple[int, Equation]:
    """Equation id from a processed Equation"""
    lhs_shape = input_eq.lhs_shape
    rhs_shape = input_eq.rhs_shape
    n_lhs = shape_order(lhs_shape)
    n_rhs = shape_order(rhs_shape)
    n = n_lhs + n_rhs
    if n_lhs != n_rhs:
        return (1 + sum(num_eqs(i) for i in range(n))
                + bell(n + 2) * shape_id((lhs_shape, rhs_shape))
                + find_rhyme_id(input_eq.rhyme))
    # For n_lhs == n_rhs the ordering halves the equations.  For
    # different tree shapes get bell(n + 2) rhymes, otherwise
    # bell_same_shape(n).
    m = catalan(n_lhs) # number of tree shapes on each side
    l = shape_id(lhs_shape)
    r = shape_id(rhs_shape)
    if l != r:
        pid = find_rhyme_id(input_eq.rhyme)
    else:
        # Slow code here
        pid = 0
        for rhyme in all_rhymes(n + 1):
            if rhyme == input_eq.rhyme:
                break
            flipped = rhyme[n_lhs + 1:] + rhyme[:n_lhs + 1]
            if canonicalize_rhyme(flipped) < rhyme:
                continue
            if rhyme == flipped and n > 0:
                continue
            pid += 1
    return (1 + sum(num_eqs(i) for i in range(n))
            + _num_eqs_unbalanced(n) + _num_eqs_balanced(n, l, r)
            + pid)


def _equation_from_id(input_eq: int) -> Equation:
    n = 0
    eq_num = input_eq - 1
    while eq_num >= (max_eq_num := num_eqs(n)):
        eq_num -= max_eq_num
        n += 1
    if eq_num < _num_eqs_unbalanced(n):
        tree_num, rhyme_num = divmod(eq_num, bell(n + 2))
        lhs_shape, rhs_shape = shape_from_id(n + 1, tree_num)
        rhyme = get_rhyme_by_id(n + 1, rhyme_num)
        return Equation(lhs_shape, rhs_shape, rhyme)
    eq_num -= _num_eqs_unbalanced(n)
    m = catalan(n // 2)
    l = ((2*m - 1) * bell(n + 2) + 2 * bell_same_shape(n)
         - math.isqrt(((2 * m - 1) * bell(n + 2) + 2 * bell_same_shape(n)) ** 2
                 - 8 * bell(n + 2) * eq_num - 1)
         - 1) // (2*bell(n + 2))
    lhs_shape = shape_from_id(n // 2, l)
    eq_num -= _num_eqs_balanced(n, l, l)
    if eq_num < bell_same_shape(n):
        rhs_shape = lhs_shape
        # Slow code here
        for rhyme in all_rhymes(n + 1):
            flipped = rhyme[(n // 2) + 1:] + rhyme[:(n // 2) + 1]
            if canonicalize_rhyme(flipped) < rhyme:
                continue
            if rhyme == flipped and n > 0:
                continue
            if eq_num == 0:
                break
            eq_num -= 1
    else:
        eq_num -= bell_same_shape(n)
        shape_diff, pid = divmod(eq_num, bell(n + 2))
        rhs_shape = shape_from_id(n // 2, l + 1 + shape_diff)
        rhyme = get_rhyme_by_id(n + 1, pid)
    return Equation(lhs_shape, rhs_shape, rhyme)





##### Code used when the module is used as a script


def process_equation(eq_str: str) -> None:
    """Process a given equation, printing its id and canonical form."""
    eq_str = eq_str.strip("[,]")
    if eq_str.startswith("*"):
        dual = True
        eq_str = eq_str[1:]
    else:
        dual = False
    try:
        input_eq = int(eq_str)
    except ValueError:
        input_eq = None
    if isinstance(input_eq, int):
        eq = Equation.from_id(input_eq)
        if dual:
            eq = eq.dual()
            eq_num = eq.id
            print(f"The dual of Equation {input_eq} is Equation {eq_num}: {eq}")
        else:
            print(f"Equation {input_eq}: {eq}")
    else:
        input_eq = Equation.from_str(eq_str)
        if dual:
            dual_eq = input_eq.dual()
            dual_num = dual_eq.id
            print(f"The dual of '{eq_str}' is Equation {dual_num}: {dual_eq}")
        else:
            eq_num = input_eq.id
            print(f"The equation '{eq_str}' is Equation {eq_num}: {input_eq}")

def main():
    """Main function to run the program."""
    parser = argparse.ArgumentParser(
        description="Canonicalize equations and find their numbers."
    )
    parser.add_argument(
        "equations",
        nargs="*",
        help="The equations to canonicalize (if not in interactive mode)",
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
    elif args.equations:
        for eq in args.equations:
            process_equation(eq)
    else:
        parser.print_help()


if __name__ == "__main__":
    main()
