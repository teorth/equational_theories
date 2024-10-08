#!/usr/bin/env python3

import argparse
import itertools
from typing import List, Tuple, Union, Iterator

EQ_SIZE = 4
VAR_NAMES = 'xyzwuv'

ExprType = Union[str, Tuple['ExprType', str, 'ExprType']]

def tokenize(expr: str) -> List[str]:
    """Convert an expression string into a list of tokens."""
    expr = expr.replace(".", "◇").replace("(", " ( ").replace(")", " ) ").replace("◇", " ◇ ")
    return [token for token in expr.split() if token]

def parse_expr(tokens: List[str]) -> ExprType:
    """Parse a list of tokens into an expression tree."""
    def parse_element() -> ExprType:
        if not tokens:
            raise ValueError("Unexpected end of expression")
        if tokens[0] in VAR_NAMES:
            return tokens.pop(0)
        if tokens[0] == '(':
            tokens.pop(0)  # Remove opening parenthesis
            left = parse_element()
            if not tokens or tokens[0] != '◇':
                raise ValueError("Expected '◇' after element in parentheses")
            tokens.pop(0)  # Remove '◇'
            right = parse_element()
            if not tokens or tokens[0] != ')':
                raise ValueError("Missing closing parenthesis")
            tokens.pop(0)  # Remove closing parenthesis
            return (left, '◇', right)
        raise ValueError(f"Unexpected token: {tokens[0]}")

    result = parse_element()
    if tokens:
        if tokens[0] != '◇':
            raise ValueError(f"Unexpected token after main element: {tokens[0]}")
        tokens.pop(0)  # Remove '◇'
        right = parse_element()
        if tokens:
            raise ValueError(f"Unexpected tokens at the end of expression: {' '.join(tokens)}")
        result = (result, '◇', right)
    return result

def canonicalize_equation(eq_str: str) -> str:
    """Canonicalize an equation string."""
    eq_str = _canonicalize_equation_help(eq_str)
    left, right = eq_str.split('=')
    eq_str_flip = _canonicalize_equation_help(right + '=' + left)

    if len(left) == len(right) and _reorder(eq_str_flip) < _reorder(eq_str):
        return eq_str_flip
    return eq_str

def _canonicalize_equation_help(eq_str: str) -> str:
    """Helper function for canonicalize_equation."""
    try:
        lhs, rhs = eq_str.split('=')
    except ValueError:
        raise ValueError("No '=' found in the equation.")
    lhs, rhs = lhs.strip(), rhs.strip()
    
    lhs_tokens = tokenize(lhs)
    rhs_tokens = tokenize(rhs)
    lhs_parsed = parse_expr(lhs_tokens)
    rhs_parsed = parse_expr(rhs_tokens)
    
    var_map = {}
    next_var = iter(VAR_NAMES)
    
    def rewrite_expr(expr: ExprType) -> ExprType:
        if isinstance(expr, str):
            if expr == '◇':
                return expr
            if expr not in var_map:
                var_map[expr] = next(next_var)
            return var_map[expr]
        left, op, right = expr
        return (rewrite_expr(left), op, rewrite_expr(right))
    
    canon_lhs = rewrite_expr(lhs_parsed)
    canon_rhs = rewrite_expr(rhs_parsed)

    def expr_to_str(expr: ExprType) -> str:
        if isinstance(expr, str):
            return expr
        left, op, right = expr
        return f"({expr_to_str(left)} {op} {expr_to_str(right)})"

    if len(expr_to_str(canon_lhs)) > len(expr_to_str(canon_rhs)):
        canon_lhs, canon_rhs = canon_rhs, canon_lhs
    
    return f"{expr_to_str(canon_lhs)} = {expr_to_str(canon_rhs)}"

def _reorder(expr: str) -> str:
    """Replace variables with their index in VAR_NAMES."""
    for i, x in enumerate(VAR_NAMES):
        expr = expr.replace(x, str(i))
    return expr

def generate_shapes(size: int) -> Iterator[Union[str, Tuple]]:
    """Generate all possible shapes for expressions of a given size."""
    if size == 0:
        yield '.'
    for i in range(size):
        for left in generate_shapes(i):
            for right in generate_shapes(size - 1 - i):
                yield (left, right)

def exprs_with_shape(shape: Union[str, Tuple], used_vars: int) -> Iterator[Tuple[Union[int, Tuple], int]]:
    """Generate all expressions with a given shape."""
    if shape == '.':
        for var in range(used_vars + 1):
            yield var, max(var + 1, used_vars)
    else:
        left, right = shape
        for left_expr, used_vars in exprs_with_shape(left, used_vars):
            for right_expr, used_vars in exprs_with_shape(right, used_vars):
                yield (left_expr, right_expr), used_vars

def rename_vars(expr: Union[int, Tuple], perm: List[int]) -> Union[int, Tuple]:
    """Rename variables in an expression according to a permutation."""
    if isinstance(expr, int):
        return perm[expr]
    left, right = expr
    return (rename_vars(left, perm), rename_vars(right, perm))

def eq_symmetries(lhs: Union[int, Tuple], rhs: Union[int, Tuple], n_vars: int) -> Iterator[Tuple[Union[int, Tuple], Union[int, Tuple]]]:
    """Generate all symmetries of an equation."""
    for renaming in itertools.permutations(range(n_vars)):
        yield rename_vars(lhs, renaming), rename_vars(rhs, renaming)
    for renaming in itertools.permutations(range(n_vars)):
        yield rename_vars(rhs, renaming), rename_vars(lhs, renaming)

def generate_all_eqs() -> Iterator[Tuple[Union[int, Tuple], Union[int, Tuple]]]:
    """Generate all unique equations up to symmetry."""
    all_eqs = set()
    for size in range(EQ_SIZE + 1):
        for lhs_size in range(size + 1):
            for lhs_shape in generate_shapes(lhs_size):
                for rhs_shape in generate_shapes(size - lhs_size):
                    for lhs, used_vars in exprs_with_shape(lhs_shape, 0):
                        for rhs, all_used_vars in exprs_with_shape(rhs_shape, used_vars):
                            if all(symmetry not in all_eqs for symmetry in eq_symmetries(lhs, rhs, all_used_vars)):
                                if lhs == rhs and not isinstance(lhs, int):
                                    continue
                                all_eqs.add((lhs, rhs))
                                yield lhs, rhs

def format_expr(expr: Union[int, Tuple], outermost: bool = True) -> str:
    """Format an expression as a string."""
    if isinstance(expr, int):
        return VAR_NAMES[expr]
    s = f'{format_expr(expr[0], outermost=False)} ◇ {format_expr(expr[1], outermost=False)}'
    if not outermost:
        return f'({s})'
    return s

def find_equation_number(input_eq: str) -> Union[int, None]:
    """Find the number of a given equation in the generated list."""
    canonical_input = canonicalize_equation(input_eq)
    for eq_num, (lhs, rhs) in enumerate(generate_all_eqs(), 1):
        eq_str = f"{format_expr(lhs)} = {format_expr(rhs)}"
        if canonicalize_equation(eq_str) == canonical_input:
            return eq_num
    return None

def process_equation(eq: str) -> None:
    """Process a given equation, finding its number and canonical form."""
    eq_num = find_equation_number(eq)
    if eq_num:
        print(f"The equation '{eq}' is Equation {eq_num}: {canonicalize_equation(eq)}")
    else:
        print(f"The equation '{eq}' (canonicalized as '{canonicalize_equation(eq)}') was not found in the generated list")

def main():
    """Main function to run the program."""
    parser = argparse.ArgumentParser(description="Canonicalize equations and find their numbers.")
    parser.add_argument("equation", nargs="?", help="The equation to canonicalize (if not in interactive mode)")
    parser.add_argument("--interactive", "-i", action="store_true", help="Run in interactive mode")
    
    args = parser.parse_args()

    if args.interactive:
        print("Welcome to the interactive equation canonicalizer!")
        print("Type 'exit' or 'quit' to end the session.")
        while True:
            eq = input("Enter an equation: ").strip()
            if eq.lower() in ['exit', 'quit']:
                print("Goodbye!")
                break
            process_equation(eq)
    elif args.equation:
        process_equation(args.equation)
    else:
        parser.print_help()

if __name__ == "__main__":
    main()
