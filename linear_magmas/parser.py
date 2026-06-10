#!/usr/bin/env python3

import re
import os
from dataclasses import dataclass
from typing import List, Union

class UnknownTransition(Exception):
    def __init__(self, x, y):
        self.x = x
        self.y = y

@dataclass
class Node:
    value: str
    left: Union['Node', None] = None
    right: Union['Node', None] = None

    @property
    def is_op(self):
        return bool(self.left)

    def __str__(self):
        if self.left and self.right:
            return f"({self.left} {self.value} {self.right})"
        elif not self.left and not self.right:
            return self.value
        else:
            assert False

    def eval(self, assignment, op):
        if self.left and self.right:
            lvalue = self.left.eval(assignment, op)
            rvalue = self.right.eval(assignment, op)
            ret = op(lvalue, rvalue)
            if ret == -1:
                raise UnknownTransition(lvalue, rvalue)
            return ret
        elif not self.left and not self.right:
            return assignment.get(self.value, self.value)
        else:
            assert False
        
    def eval_hold(self, assignment, op):
        if self.left and self.right:
            lvalue = self.left.eval_hold(assignment, op)
            rvalue = self.right.eval_hold(assignment, op)

            try:
                ret = op(lvalue, rvalue)
                if ret != -1:
                    return ret
            except:
                pass
            return (lvalue, rvalue)
        elif not self.left and not self.right:
            return assignment.get(self.value, self.value)
        else:
            assert False


class Equation:
    op_symbols = ('∘','*', '◇')

    def __init__(self, equation_str: str):
        self.equation_str = equation_str
        self._parse_equation(equation_str)

    def _parse_equation(self, equation_str: str):
        # Extract equation number
        equation_number = re.search(r'Equation(\d+)', equation_str)
        if equation_number:
            full_definition = True
            self.equation_number = int(equation_number.group(1))
        else:
            full_definition = False
            self.equation_number = -1

        if full_definition:
            variables_match = re.search(r'∀\s+([^:]+)\s*:', equation_str)
            if variables_match:
                self.free_variables = tuple(var.strip() for var in variables_match.group(1).split())
            else:
                raise ValueError("Free variables not found")
        else:
            self.free_variables = sorted(set(m for m in re.findall(r'[a-z]', equation_str)))

        # Extract the equation part
        if full_definition:
            equation_parts = equation_str.split(",")[-1].split('=') 
        else:
            equation_parts = equation_str.split('=')

        # Parse the equation into an expression tree
        def parse_expression(expr: str) -> Node:
            expr = expr.strip()
            if all(x not in expr for x in self.op_symbols):
                return Node(expr)

            # Find the outermost ∘ operator
            bracket_count = 0
            for i, char in enumerate(expr):
                if char == '(':
                    bracket_count += 1
                elif char == ')':
                    bracket_count -= 1
                elif char in self.op_symbols and bracket_count == 0:
                    left = parse_expression(expr[:i])
                    right = parse_expression(expr[i+1:])
                    return Node(char, left, right)

            # If we get here, the expression is wrapped in brackets
            return parse_expression(expr[1:-1])

        self.lhs = parse_expression(equation_parts[0])
        self.rhs = parse_expression(equation_parts[1])

    def __repr__(self):
        return str(self)

    def __str__(self):
        return f"Eq({self.equation_number}|{','.join(self.free_variables)}|{self.lhs} = {self.rhs})"
    
    @property
    def equation(self):
        return f"{self.lhs} = {self.rhs}"

    def eval(self, assignment, op):
        return self.lhs.eval(assignment, op) == self.rhs.eval(assignment, op)
    
    def implication(self, assignment, op):
        lhs = self.lhs.eval_hold(assignment, op)
        rhs = self.rhs.eval_hold(assignment, op)

        if isinstance(lhs, int) and isinstance(rhs[0], int) and isinstance(rhs[1], int):
            return (*rhs, lhs)

def read_eqs():
    for line in open(os.path.join(os.path.dirname(__file__), "data/equations.txt")):
        yield Equation(line)

if __name__ == "__main__":
    for result in read_eqs():
        print(f"Equation number: {result.equation_number}")
        print(f"Free variables: {result.free_variables}")
        print("Expression tree:")

        print(f"{result.equation_str} -> {result}")
