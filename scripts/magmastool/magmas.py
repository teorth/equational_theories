import json
import sys
import re
from itertools import product

def read_operation_table(filename):
    with open(filename, 'r') as file:
        lines = [line.strip() for line in file if line.strip()]
        table = [list(map(int, line.split())) for line in lines]

        size = len(table)
        if not all(len(row) == size for row in table):
            raise ValueError("Operation table must be square")
        return table

def read_equations(filename):
    equations = []
    with open(filename, 'r') as file:
        for line in file:
            if line.strip():
                parts = line.strip().split(maxsplit=1)
                if len(parts) == 2:
                    name, expression = parts
                    equations.append((name, expression))
    return equations

def shunting_yard(expression):
    output, stack = [], []
    tokens = re.findall(r'[a-z]+|[◇*()]', expression)
    precedence = {'◇': 1, '*': 1}

    for token in tokens:
        if token.isalpha():
            output.append(token)
        elif token in precedence:
            while (stack and stack[-1] in precedence and
                   precedence[token] <= precedence[stack[-1]]):
                output.append(stack.pop())
            stack.append(token)
        elif token == '(':
            stack.append(token)
        elif token == ')':
            while stack and stack[-1] != '(':
                output.append(stack.pop())
            if stack:
                stack.pop()

    while stack:
        if stack[-1] != '(':
            output.append(stack.pop())
        else:
            stack.pop()

    return output

def evaluate_rpn(rpn, op_table, variables):
    stack = []
    for token in rpn:
        if token.isalpha():
            if token not in variables:
                return None
            stack.append(variables[token])
        elif token == '◇':
            if len(stack) < 2:
                return None
            b, a = stack.pop(), stack.pop()
            stack.append(op_table[a][b])
    return stack[0] if stack else None

def get_variables(expression):
    return set(re.findall(r'[a-z]', expression))

def check_equation_satisfaction(equation, op_table):
    try:
        lhs_expr, rhs_expr = equation.split('=')
        lhs_rpn = shunting_yard(lhs_expr.strip())
        rhs_rpn = shunting_yard(rhs_expr.strip())

        variables = get_variables(equation)
        table_size = len(op_table)

        value_combinations = product(range(table_size), repeat=len(variables))

        for values in value_combinations:
            var_assignment = dict(zip(sorted(variables), values))

            lhs_result = evaluate_rpn(lhs_rpn, op_table, var_assignment)
            rhs_result = evaluate_rpn(rhs_rpn, op_table, var_assignment)

            if lhs_result is None or rhs_result is None:
                continue

            if lhs_result != rhs_result:
                return 0

        return 1

    except Exception as e:
        print(f"Error processing equation: {equation}")
        print(f"Error details: {str(e)}")
        return 0

def generate_results(operation_table_file, equations_file):
    try:
        operation_table = read_operation_table(operation_table_file)
        equations = read_equations(equations_file)

        results = {}
        for name, equation in equations:
            results[name] = check_equation_satisfaction(equation, operation_table)

        print(json.dumps(results, indent=2))
    except Exception as e:
        print(f"Error: {str(e)}")
        sys.exit(1)

if __name__ == "__main__":
    if len(sys.argv) != 3:
        print("Usage: python magmas.py <operation_table_file> <equations_file>")
        sys.exit(1)

    operation_table_file = sys.argv[1]
    equations_file = sys.argv[2]
    generate_results(operation_table_file, equations_file)
