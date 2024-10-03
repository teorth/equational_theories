from __future__ import annotations
from typing import Optional, Set, Tuple, Dict, List
import re

class ExprNode:
    """Represents a node in an expression tree."""

    def __init__(self, value: str, left: Optional[ExprNode] = None, right: Optional[ExprNode] = None):
        self.value = value
        self.left = left
        self.right = right
        self.node_count = 1 + (left.node_count if left else 0) + (right.node_count if right else 0)

    def __repr__(self) -> str:
        """Return a string representation of the node."""
        if self.left and self.right:
            return f"({self.left} {self.value} {self.right})"
        return self.value

    def get_leafs(self) -> Set[str]:
        """Collect and return all leaf node values in the tree."""
        def traverse(node, leaves):
            if not node:
                return
            if not node.left and not node.right:
                leaves.add(node.value)
            else:
                traverse(node.left, leaves)
                traverse(node.right, leaves)

        leaf_set = set()
        traverse(self, leaf_set)
        return leaf_set

    def reverse(self):
        """Create a new ExprNode with reversed structure and adjusted operators."""
        if not self.left and not self.right:
            return ExprNode(self.value)
        else:
            new_left = self.right.reverse() if self.right else None
            new_right = self.left.reverse() if self.left else None
            return ExprNode(self.value, new_left, new_right)

def is_same_under_rewriting(left: ExprNode, right: ExprNode):
    """
    Check if two expression trees are equivalent under variable renaming.
    Returns mappings for left and right trees if they're the same, else None.
    """
    if left.node_count != right.node_count:
        return None

    def traverse(node, mapping):
        if not node.left and not node.right:
            if node.value not in mapping:
                if node.value in mapping.values():
                    return None
                mapping[node.value] = len(mapping)
            return mapping[node.value]

        if not node.left or not node.right:
            return None

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

class Parser:
    """A simple parser for mathematical expressions."""

    def __init__(self, expression: str):
        self.expression = expression.replace(' ', '')
        self.index = 0
        self.length = len(self.expression)

    def parse(self):
        """Parse the entire expression."""
        return self.parse_expression()

    def parse_expression(self):
        """Parse an expression, handling composition operators."""
        nodes = [self.parse_term()]

        while self.current_char() in ['◇', '.']:
            op = self.current_char()
            self.advance()
            right = self.parse_term()
            nodes.append(op)
            nodes.append(right)

        # Build the tree (left-associative)
        node = nodes[0]
        for i in range(1, len(nodes), 2):
            node = ExprNode(nodes[i], left=node, right=nodes[i+1])

        return node

    def parse_term(self):
        """Parse a term (variable or parenthesized expression)."""
        char = self.current_char()
        if char == '(':
            self.advance()
            node = self.parse_expression()
            if self.current_char() != ')':
                raise ValueError("Mismatched parentheses")
            self.advance()
            return node
        else:
            return self.parse_variable()

    def parse_variable(self):
        """Parse a variable."""
        match = re.match(r'[a-zA-Z_]\w*', self.expression[self.index:])
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
    if node.value == '◇':
        left = expr_to_prefix(node.left)
        right = expr_to_prefix(node.right)
        return f"f({left}, {right})"
    else:
        return node.value

def make_tree(equation: str):
    """Create an expression tree from an equation string."""
    lhs_expr, rhs_expr = equation.split('=')
    parser_lhs = Parser(lhs_expr)
    tree_lhs = parser_lhs.parse()

    parser_rhs = Parser(rhs_expr)
    tree_rhs = parser_rhs.parse()

    return ExprNode("=", left=tree_lhs, right=tree_rhs)

def flip_top_most(node: ExprNode):
    """Flip the left and right children of the root node."""
    return ExprNode(node.value, left=node.right, right=node.left)

def main():
    trees = []
    for line in open("../equational_theories/AllEquations.lean"):
        if "equation" in line and ":=" in line:
            equation_number = line.split("equation")[1].split()[0]
            trees.append((int(equation_number), make_tree(line.split(":=")[1].strip())))

    seen = {}
    
    for eq_num1, tree1 in trees:
        reversed_tree1 = tree1.reverse()
        for eq_num2, tree2 in trees:
            if eq_num1 >= eq_num2:
                continue
            if is_same_under_rewriting(reversed_tree1, tree2) or is_same_under_rewriting(reversed_tree1, flip_top_most(tree2)):
                print(f"| Equation{eq_num1}[{tree1}] | Equation{eq_num2}[{tree2}] |")
                seen[eq_num1] = True
                seen[eq_num2] = True

    print("Unseen:")
    for eq_num, tree in trees:
        if eq_num not in seen:
            print(f"* Equation{eq_num}[{tree}]")

if __name__ == "__main__":
    main()
