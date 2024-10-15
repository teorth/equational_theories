from itertools import product
import re
from typing import List, Callable

import re


# Define the expression node
class ExprNode:
    def __init__(self, value, left=None, right=None):
        self.value = value  # Operator or operand
        self.left = left
        self.right = right

    def __repr__(self):
        if self.left and self.right:
            return f"({self.left} {self.value} {self.right})"
        return "(" + self.value + ")"

    def get_leafs(root):
        def traverse(node, leaves):
            if not node:
                return

            if not node.left and not node.right:  # Leaf node
                leaves.add(node.value)
            else:
                traverse(node.left, leaves)
                traverse(node.right, leaves)

        leaf_set = set()
        traverse(root, leaf_set)
        return leaf_set

    def rename(root, rename_map):
        def traverse(node):
            if not node:
                return None

            if not node.left and not node.right:  # Leaf node
                new_value = rename_map.get(node.value, node.value)
                return ExprNode(new_value)

            new_left = traverse(node.left)
            new_right = traverse(node.right)
            return ExprNode(node.value, new_left, new_right)

        return traverse(root)


def is_same_under_rewriting(left, right):
    def traverse(node, mapping):
        if not node.left and not node.right:  # Leaf node
            if node.value not in mapping:
                if node.value in mapping.values():
                    return False  # This value is already mapped to another variable
                mapping[node.value] = len(mapping)
            return mapping[node.value]

        if not node.left or not node.right:
            return None  # Invalid expression tree

        left_result = traverse(node.left, mapping)
        right_result = traverse(node.right, mapping)

        if left_result is None or right_result is None:
            return None

        return (node.value, left_result, right_result)

    mapping1 = {}
    left_structure = traverse(left, mapping1)
    mapping2 = {}
    right_structure = traverse(right, mapping2)

    if left_structure == right_structure:
        return {v: k for k, v in mapping1.items()}, {v: k for k, v in mapping2.items()}
    return None


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

        while self.current_char() == "◇" or self.current_char() == ".":
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


def make_tree(equation):
    lhs_expr, rhs_expr = equation.split("=")
    parser_lhs = Parser(lhs_expr)
    tree_lhs = parser_lhs.parse()

    # Parse RHS
    parser_rhs = Parser(rhs_expr)
    tree_rhs = parser_rhs.parse()

    return ExprNode("=", left=tree_lhs, right=tree_rhs)
