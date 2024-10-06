import re

import re

class Expr:
    pass

class Var(Expr):
    def __init__(self, name):
        self.name = name

class Op(Expr):
    def __init__(self, op, left, right):
        self.op = op
        self.left = left
        self.right = right

def tokenize(expr_str):
    tokens = []
    i = 0
    while i < len(expr_str):
        if expr_str[i].isspace():
            i += 1
        elif expr_str[i].isalnum() or expr_str[i] in ("'", "_"):
            # Read variable name
            var = ''
            while i < len(expr_str) and (expr_str[i].isalnum() or expr_str[i] in ("'", "_")):
                var += expr_str[i]
                i += 1
            tokens.append(('VAR', var))
        elif expr_str[i] == '◇':
            tokens.append(('OP', '◇'))
            i += 1
        elif expr_str[i] == '(':
            tokens.append(('LPAREN', '('))
            i += 1
        elif expr_str[i] == ')':
            tokens.append(('RPAREN', ')'))
            i += 1
        elif expr_str[i] == '=':
            tokens.append(('EQUALS', '='))
            i += 1
        else:
            # Skip unknown characters
            i += 1
    return tokens

def parse_expr(tokens, pos=0):
    def parse_factor(tokens, pos):
        if pos >= len(tokens):
            raise Exception('Unexpected end of tokens')
        token = tokens[pos]
        if token[0] == 'VAR':
            return Var(token[1]), pos + 1
        elif token[0] == 'LPAREN':
            expr, pos = parse_expr(tokens, pos + 1)
            if pos >= len(tokens) or tokens[pos][0] != 'RPAREN':
                raise Exception('Expected ) at position {}'.format(pos))
            return expr, pos + 1
        else:
            raise Exception('Unexpected token: {}'.format(token))

    left, pos = parse_factor(tokens, pos)
    while pos < len(tokens) and tokens[pos][0] == 'OP':
        op = tokens[pos][1]
        pos += 1
        right, pos = parse_factor(tokens, pos)
        left = Op(op, left, right)
    return left, pos

def parse_equation_line(line):
    # First, extract the equation name
    match = re.match(r'def\s+(\w+)\s*\(.*?\)\s*(?:\[.*?\])?\s*:=\s*∀(.*)', line)
    if not match:
        return None
    equation_name = match.group(1)
    rest = match.group(2).strip()
    # Now, split the rest into variables declaration and equation
    var_equation = rest.split(',', 1)
    if len(var_equation) != 2:
        return None
    var_decl = var_equation[0].strip()
    equation = var_equation[1].strip()
    # Extract variables
    vars_and_types = var_decl.split(':', 1)
    vars_str = vars_and_types[0].strip()
    variables = vars_str.replace(',', ' ').split()
    # Now, split the equation at '='
    equation_match = re.match(r'(.*)=(.*)', equation)
    if not equation_match:
        return None
    lhs = equation_match.group(1).strip()
    rhs = equation_match.group(2).strip()
    return {
        'equation_name': equation_name,
        'variables': variables,
        'lhs': lhs,
        'rhs': rhs
    }

def process_equation_line(line, equation_index):
    eq = parse_equation_line(line)
    if eq is None:
        print(f"Failed to parse line: {line}")
        return None
    variables = eq['variables']
    lhs_expr_str = eq['lhs']
    rhs_expr_str = eq['rhs']
    # Assign indices to variables
    variable_indices = {var: idx for idx, var in enumerate(variables)}
    # Tokenize and parse lhs and rhs expressions
    lhs_tokens = tokenize(lhs_expr_str)
    rhs_tokens = tokenize(rhs_expr_str)
    try:
        lhs_expr, lhs_pos = parse_expr(lhs_tokens)
        rhs_expr, rhs_pos = parse_expr(rhs_tokens)
    except Exception as e:
        print(f"Error parsing expression: {e}")
        return None
    if lhs_pos != len(lhs_tokens):
        print(f"Unparsed tokens remain in LHS expression '{lhs_expr_str}'")
        return None
    if rhs_pos != len(rhs_tokens):
        print(f"Unparsed tokens remain in RHS expression '{rhs_expr_str}'")
        return None
    # Generate c code for lhs and rhs
    lhs_c_code = generate_c_code(lhs_expr, variable_indices)
    rhs_c_code = generate_c_code(rhs_expr, variable_indices)
    # Generate c code for function
    nvar = len(variables)
    func_code = f'bool fn{equation_index}(int* table, uint64_t arg) {{ return {lhs_c_code} == {rhs_c_code}; }} int nvar_{equation_index} = {nvar};'
    return func_code

def generate_c_code(expr, variable_indices):
    if isinstance(expr, Var):
        if expr.name in variable_indices:
            idx = variable_indices[expr.name]
            # Use expressions involving K and variable index
            code = f'GET_VAR(arg, {idx})'
            return code
        else:
            # Handle constants or variables not in variable_positions
            return expr.name
    elif isinstance(expr, Op):
        if expr.op == '◇':
            # For '◇' operation, we need to generate table[...]
            left_code = generate_c_code(expr.left, variable_indices)
            right_code = generate_c_code(expr.right, variable_indices)
            return f'table[{left_code}*N+{right_code}]'
        else:
            # Unknown operator
            raise Exception(f'Unknown operator: {expr.op}')
    else:
        raise Exception('Unknown expression type')



def generate_c_preprocessor_macros():
    macros = '''
#define GET_VAR(arg, idx) (((arg) >> ((idx) * K)) & ((1 << K) - 1))
'''
    return macros

# Generate the C preprocessor macros
macros = generate_c_preprocessor_macros()
print(macros)

for idx,line in enumerate(open("equations.txt")):
    func_code = process_equation_line(line, idx)
    if func_code:
        print(func_code)
    else:
        print(f"Failed to process equation at line {idx}: {line}")
