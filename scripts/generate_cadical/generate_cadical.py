#!/usr/bin/env python3
from __future__ import annotations
from typing import Optional
import re
from eznf import modeler, utils, constants
import argparse
import json

# Usage:
#   ./generate_cadical.py -s 6 37 42      Attempt to disprove 37 -> 42 using finite model of size 6
#   ./generate_cadical.py -i -s 6 37 42   Attempt to disprove 37 -> 42 using finite models up to size 6
#   ./generate_cadical.py -i -s 6         Attempt to disprove all unknowns using models up to size 6


class ExprNode:
    """Represents a node in an expression tree."""

    def __init__(
        self,
        value: str,
        left: Optional[ExprNode] = None,
        right: Optional[ExprNode] = None,
    ):
        self.value = value
        self.left = left
        self.right = right
        self.max = 1 + max(left.max if left else 0, right.max if right else 0)

    def __repr__(self) -> str:
        """Return a string representation of the node."""
        if self.left and self.right:
            return f"({self.left} {self.value} {self.right})"
        return self.value

    def get_leafs(self) -> set[str]:
        """Collect and return all leaf node values in the tree."""

        def traverse(node, leaves):
            if not node.left and not node.right:
                leaves.add(node.value)
            else:
                traverse(node.left, leaves)
                traverse(node.right, leaves)

        leaf_set = set()
        traverse(self, leaf_set)
        return leaf_set


class Parser:
    """A simple parser for mathematical expressions."""

    def __init__(self, expression: str):
        self.expression = expression.replace(" ", "")
        self.index = 0
        self.length = len(self.expression)

    def parse(self):
        """Parse the entire expression."""
        return self.parse_expression()

    def parse_expression(self):
        """Parse an expression, handling composition operators."""
        nodes = [self.parse_term()]

        while self.current_char() in ["◇", "."]:
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
        """Parse a term (variable or parenthesized expression)."""
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
        """Parse a variable."""
        match = re.match(r"[a-zA-Z_]\w*", self.expression[self.index :])
        if not match:
            raise ValueError(f"Invalid character at index {self.index}")
        var = match.group(0)
        self.index += len(var)
        return ExprNode(var)

    def current_char(self):
        """Return the current character or None if at the end."""
        return self.expression[self.index] if self.index < self.length else None

    def advance(self):
        """Move to the next character."""
        self.index += 1


def expr_to_prefix(node: ExprNode):
    """Convert an expression tree to prefix notation."""
    if node.value == "◇":
        left = expr_to_prefix(node.left)
        right = expr_to_prefix(node.right)
        return f"f({left}, {right})"
    else:
        return node.value


def make_tree(equation: str):
    """Create an expression tree from an equation string."""
    lhs_expr, rhs_expr = equation.split("=")
    parser_lhs = Parser(lhs_expr)
    tree_lhs = parser_lhs.parse()

    parser_rhs = Parser(rhs_expr)
    tree_rhs = parser_rhs.parse()

    return ExprNode("=", left=tree_lhs, right=tree_rhs)


def flip_top_most(node: ExprNode):
    """Flip the left and right children of the root node."""
    return ExprNode(node.value, left=node.right, right=node.left)


def run(n: int, first_tree: ExprNode, second_tree: ExprNode):
    encoding = modeler.Modeler()
    print("encoding...")

    def var(i, j, k):
        return f"{i}*{j}={k}"

    def neg(s):
        return f"-{s}"

    for i in range(n):
        for j in range(n):
            for k in range(n):
                encoding.add_var(var(i, j, k))
            encoding.exactly_one(var(i, j, k) for k in range(n))

    def allocate(self):
        if self.value == "=":
            print(self)
            allocate(self.left)
            allocate(self.right)
        elif self.value == "◇":
            print(self)
            allocate(self.left)
            allocate(self.right)
        else:
            print(self.value)

    negative_law = []

    def go(vars: set[str], assn: dict[str, int] = {}):
        if vars:
            x = vars.pop()
            for i in range(n):
                assn[x] = i
                go(vars, assn)
            vars.add(x)
        else:
            assn_name = str(assn)
            processed: dict[str, list[str]] = {}

            def process(tree: ExprNode) -> str:
                name = str(tree)
                if name not in processed:
                    names = [f"{assn_name} |- {name} = {k}" for k in range(n)]
                    processed[name] = names
                    if tree.left and tree.right:
                        encoding.exactly_one(names)
                        l = processed[process(tree.left)]
                        r = processed[process(tree.right)]
                        for i in range(n):
                            for j in range(n):
                                for k in range(n):
                                    # if left = i and right = j then (i*j = k <-> left*right = k)
                                    encoding.add_clause(
                                        [
                                            neg(l[i]),
                                            neg(r[j]),
                                            neg(var(i, j, k)),
                                            names[k],
                                        ]
                                    )
                                    encoding.add_clause(
                                        [
                                            neg(l[i]),
                                            neg(r[j]),
                                            neg(names[k]),
                                            var(i, j, k),
                                        ]
                                    )

                    else:
                        for k in range(n):
                            if assn[tree.value] == k:
                                encoding.add_clause([names[k]])
                            else:
                                encoding.add_clause([neg(names[k])])
                return name

            def process_tree(tree: ExprNode) -> str:
                l = process(tree.left)
                r = process(tree.right)
                vname = f"{assn_name} |- {l} == {r}"
                for k in range(n):
                    # if left = k and right = k then left == right
                    encoding.add_clause(
                        [neg(processed[l][k]), neg(processed[r][k]), vname]
                    )
                    # if left == right then (left = k <-> right = k)
                    encoding.add_clause(
                        [neg(vname), neg(processed[l][k]), processed[r][k]]
                    )
                    encoding.add_clause(
                        [neg(vname), neg(processed[r][k]), processed[l][k]]
                    )
                return vname

            encoding.add_clause([process_tree(first_tree)])
            negative_law.append(neg(process_tree(second_tree)))

    go(first_tree.get_leafs().union(second_tree.get_leafs()))
    encoding.add_clause(negative_law)

    print("running cadical...")
    lit_valuation = {}
    encoding.serialize(constants.TMP_FILENAME)
    output, return_code = utils.system_call(["cadical", constants.TMP_FILENAME])
    if return_code != 10:
        print(f"failed at size {n}")
        return False
    for line in output.split("\n"):
        if len(line) > 0 and line[0] == "v":
            tokens = line.split(" ")  # skip newline
            relevant_tokens = tokens[1:]
            for token in relevant_tokens:
                int_token = int(token)
                if int_token == 0:
                    continue
                lit_valuation[abs(int_token)] = int_token > 0
    sem_valuation = {}
    for lit_name, (lit, _) in encoding._varmap.items():
        sem_valuation[lit_name] = lit_valuation[lit]
    print("success!")
    print(
        [
            [next(k for k in range(n) if sem_valuation[var(i, j, k)]) for j in range(n)]
            for i in range(n)
        ]
    )
    return True


def main():
    argparser = argparse.ArgumentParser()
    argparser.add_argument("-s", "--size", required=True, type=int, help="Magma size")
    argparser.add_argument(
        "-i", "--incremental", action="store_true", help="Incremental up to size"
    )
    argparser.add_argument("args", nargs="*", type=int, help="Law to assume/refute")

    args = argparser.parse_args()

    def load_trees(first, second):
        first_tree = None
        second_tree = None
        for file in ["1_999", "1000_1999", "2000_2999", "3000_3999", "4000_4694"]:
            for line in open(f"../../equational_theories/Equations/Eqns{file}.lean"):
                if "equation" in line and ":=" in line:
                    equation_number = int(line.split("equation")[1].split()[0])
                    if equation_number == first:
                        first_tree = make_tree(line.split(":=")[1].strip())
                    if equation_number == second:
                        second_tree = make_tree(line.split(":=")[1].strip())
        assert first_tree is not None and second_tree is not None
        return first_tree, second_tree

    if len(args.args) == 2:
        first_tree, second_tree = load_trees(args.args[0], args.args[1])
        if args.incremental:
            for i in range(2, args.size + 1):
                if run(i, first_tree, second_tree):
                    return
        else:
            run(args.size, first_tree, second_tree)
    else:
        with open("../../home_page/fme/unknowns.json", "r") as file:
            data = json.load(file)
        if args.incremental:
            for i in range(2, args.size + 1):
                for impl in data:
                    first = int(impl["lhs"].removeprefix("Equation"))
                    second = int(impl["rhs"].removeprefix("Equation"))
                    first_tree, second_tree = load_trees(first, second)
                    print(f"attempting {first} -> {second}")
                    if run(i, first_tree, second_tree):
                        return
        else:
            for impl in data:
                first = int(impl["lhs"].removeprefix("Equation"))
                second = int(impl["rhs"].removeprefix("Equation"))
                first_tree, second_tree = load_trees(first, second)
                print(f"attempting {first} -> {second}")
                run(args.size, first_tree, second_tree)


if __name__ == "__main__":
    main()
