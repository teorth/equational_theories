#!/usr/bin/env python3

# Generate a list of equations on magmas

from itertools import permutations
from sys import argv, stderr


EQ_SIZE = 4
VAR_NAMES = 'xyzwuv'

def generate_shapes(size):
    if size == 0:
        yield '.'
    for i in range(size):
        for left in generate_shapes(i):
            for right in generate_shapes(size - 1 - i):
                yield (left, right)

def format_shape(shape, outermost=True):
    if shape == '.':
        return '_'
    left, right = shape
    s = f'{format_shape(left, outermost=False)} ◇ {format_shape(right, outermost=False)}'
    if not outermost:
        return f'({s})'
    return s

def exprs_with_shape(shape, used_vars):
    if shape == '.':
        for var in range(used_vars + 1):
            yield var, max(var + 1, used_vars)
    else:
        left, right = shape
        for left_expr, used_vars in exprs_with_shape(left, used_vars):
            for right_expr, used_vars in exprs_with_shape(right, used_vars):
                yield (left_expr, right_expr), used_vars

def rename_vars(expr, perm):
    if isinstance(expr, int):
        return perm[expr]
    left, right = expr
    return (rename_vars(left, perm), rename_vars(right, perm))

def eq_symmetries_1(lhs, rhs, n_vars):
    for renaming in permutations(range(n_vars)):
        yield rename_vars(lhs, renaming), rename_vars(rhs, renaming)

def eq_symmetries(lhs, rhs, n_vars):
    yield from eq_symmetries_1(lhs, rhs, n_vars)
    yield from eq_symmetries_1(rhs, lhs, n_vars)

def generate_all_eqs():
    all_eqs = set()
    for size in range(EQ_SIZE + 1):
        for lhs_size in range(size + 1):
            for lhs_shape in generate_shapes(lhs_size):
                for rhs_shape in generate_shapes(size - lhs_size):
                    for lhs, used_vars in exprs_with_shape(lhs_shape, 0):
                        for rhs, all_used_vars in exprs_with_shape(rhs_shape, used_vars):
                            if all(symmetry not in all_eqs for symmetry in eq_symmetries(lhs, rhs, all_used_vars)):
                                if lhs == rhs:
                                    if not isinstance(lhs, int):
                                        continue
                                all_eqs.add((lhs, rhs))
                                yield lhs, rhs

def format_expr(expr, outermost=True):
    if isinstance(expr, int):
        return VAR_NAMES[expr]
    s = f'{format_expr(expr[0], outermost=False)} ◇ {format_expr(expr[1], outermost=False)}'
    if not outermost:
        return f'({s})'
    return s

def expr_shape(expr):
    if isinstance(expr, int):
        return '.'
    left, right = expr
    return (expr_shape(left), expr_shape(right))

def count_vars(expr):
    if isinstance(expr, int):
        return expr + 1
    left, right = expr
    return max(count_vars(left), count_vars(right))


eqs = list(generate_all_eqs())

if __name__ == "__main__":
    if len(argv) > 1 and argv[1] in {'-h', '/h', '/?', '--help', '/help'}:
        print(f'Usage: python {argv[0]} [--shapes | --lean]')
        print(f'    Generates all equations up to {EQ_SIZE} operations and sends them to the standard output.')
        print(f'    To output to a file use the > operator of your shell.')
        print(f'    If the --shapes option is present, the shapes of the equations are printed instead.')
        print(f'    If the --lean option is present, the equations are printed in the format of https://github.com/teorth/equational')
        exit(1)

    print(f'Generated {len(eqs)} equations', file=stderr)
    if len(argv) > 1 and argv[1] == '--shapes':
        shapes = set()
        for lhs, rhs in eqs:
            shape = (expr_shape(lhs), expr_shape(rhs))
            if shape not in shapes:
                shapes.add(shape)
                print(format_shape(shape[0]), '=', format_shape(shape[1]))
        exit(0)

    if len(argv) > 1 and argv[1] == '--lean':
        for i, (lhs, rhs) in enumerate(eqs):
            vars = ' '.join(VAR_NAMES[i] for i in range(max(count_vars(lhs), count_vars(rhs))))
            print(f'def Equation{i + 1} (G: Type*) [Magma G] := ∀ {vars} : G, {format_expr(lhs)} = {format_expr(rhs)}')
        exit(0)

    for lhs, rhs in generate_all_eqs():
        print(format_expr(lhs), '=', format_expr(rhs))
