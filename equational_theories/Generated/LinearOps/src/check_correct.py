#!/usr/bin/env python3

import collections
from itertools import product

import re


DEBUG = True


# Define the expression node
class ExprNode:
    def __init__(self, value, left=None, right=None):
        self.value = value  # Operator or operand
        self.left = left
        self.right = right

    def __repr__(self):
        if self.left and self.right:
            return f"({self.left} {self.value} {self.right})"
        return self.value


# Parser implementation
class Parser:
    def __init__(self, expression):
        self.expression = expression.replace(" ", "")
        self.index = 0
        self.length = len(self.expression)

    def parse(self):
        return self.parse_expression()

    def parse_expression(self):
        nodes = [self.parse_term()]

        while self.current_char() == "◇":
            op = self.current_char()
            self.advance()
            right = self.parse_term()
            nodes.append(op)
            nodes.append(right)

        # Build the tree (left-associative)
        node = nodes[0]
        for i in range(1, len(nodes), 2):
            node = ExprNode(nodes[i], left=node, right=nodes[i + 1])

        return node

    def parse_term(self):
        char = self.current_char()
        if char == "(":
            self.advance()
            node = self.parse_expression()
            if self.current_char() != ")":
                raise ValueError("Mismatched parentheses")
            self.advance()
            return node
        else:
            return self.parse_variable()

    def parse_variable(self):
        match = re.match(r"[a-zA-Z_]\w*", self.expression[self.index :])
        if not match:
            raise ValueError(f"Invalid character at index {self.index}")
        var = match.group(0)
        self.index += len(var)
        return ExprNode(var)

    def current_char(self):
        if self.index < self.length:
            return self.expression[self.index]
        return None

    def advance(self):
        self.index += 1


# Function to convert expression tree to prefix notation
def expr_to_prefix(node):
    if node.value == "◇":
        left = expr_to_prefix(node.left)
        right = expr_to_prefix(node.right)
        return f"f({left}, {right})"
    else:
        return node.value


# Function to convert equations to lambdas
ctr = 0


def convert(vars_list, equation):
    global ctr
    if True:
        lhs_expr, rhs_expr = equation.split("=")

        # Parse LHS
        parser_lhs = Parser(lhs_expr)
        tree_lhs = parser_lhs.parse()
        prefix_lhs = expr_to_prefix(tree_lhs)

        # Parse RHS
        parser_rhs = Parser(rhs_expr)
        tree_rhs = parser_rhs.parse()
        prefix_rhs = expr_to_prefix(tree_rhs)

        # Create lambda string
        lambda_str = f"lambda f,{', '.join(vars_list)}: {prefix_lhs} == {prefix_rhs}"

        # Compile the lambda function
        try:
            lambda_func = eval(lambda_str)
        except Exception as e:
            print(f"Error compiling lambda{idx}: {e}")
            lambda_func = None

        # print(ctr, lambda_str)
        ctr += 1

        return lambda_func


def get_fns():
    equations = open("equations.txt", "r").read().split("\n")[:-1]
    fns = []
    for eq in equations:
        oeq = eq
        eq = eq.split("∀")[1]
        variables, eq = eq.split(":")
        variables = variables.strip().split()
        rule = eq.split(",")[1]
        fns.append((oeq, len(variables), convert(variables, rule)))

    return fns


fns = get_fns()


def check_rule(nvar, check, S, op):
    for args in product(S, repeat=nvar):
        if DEBUG:
            VARS = "xyzwuv"
            print(
                "Checking equation on assignments",
                ", ".join([f"{VARS[i]}={args[i]}" for i in range(nvar)]),
            )
        if not check(op, *args):
            return False
    return True


"""
S = list(range(4))

for row in open("../data/refutations4x4.txt").readlines():
    if 'Table' in row:
        table = np.array(eval(row.split("Table")[1]))
    elif 'Proves' in row:
        proves = eval(row.split("Proves")[1])

        ok = []
        for x in proves:
            if DEBUG:
                print(f"Showing that {fns[x-1][0]}")
                print(f"is correct on Magma\n{table}")
            string, nvar, fn = fns[x-1]
            def op(x, y):
                if DEBUG:
                    print(f"table[{x}, {y}] = {table[x, y]}")
                return table[x, y]

            this = check_rule(nvar, fn, S, op)
            assert this

            ok.append(this)
        print(collections.Counter(ok))
"""

lines = """
Variables 11 4 6
Satisfied equations: 1075
""".split(
    "\n"
)

# for row in open("h4").readlines():
for row in lines:
    print()
    print()
    if "Variables" in row:
        pk, a, b = map(int, (row.split("Variables")[1].split()))
        S = list(range(pk))
    elif "Satisfied" in row:
        proves = list(map(int, row.split(":")[1].split(", ")))

        ok = []
        for x in proves:
            if DEBUG:
                print(f"Showing that {fns[x][0]}")
                print(f"is correct on Magma\n{[pk, a, b]}")
            string, nvar, fn = fns[x]

            def op(x, y):
                if DEBUG:
                    print(f"{a}*{x}+{b}*{y}={(a*x + b*y)%pk}")
                return (a * x + b * y) % pk

            this = check_rule(nvar, fn, S, op)
            assert this

            ok.append(this)
        print(collections.Counter(ok))
