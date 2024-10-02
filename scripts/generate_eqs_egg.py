import subprocess
import os.path
import re

subgraph_equations = [1, 2, 3, 4, 5, 6, 7, 8, 14, 23, 29, 38, 39, 40, 41, 42,
                      43, 45, 46, 168, 381, 387, 1689, 3722, 3744, 4512, 4513,
                      4522, 4564, 4579, 4582, 5105, 28393, 374794]


def generate_equation_statement(lhs : int, rhs : int):
  return f"theorem Equation{lhs}_implies_Equation{rhs} (G: Type _) [Magma G] (h: Equation{lhs} G) : Equation{rhs} G := by egg [*]\n"

def generate_file(eqs_list : list[int], name : str):
    preamble = f"""import equational_theories.{name}
import Egg

set_option egg.explosion true
set_option egg.timeLimit 1

"""
    path = os.path.join('equational_theories', 'Generated', f"{name}Egg.lean")
    with open(path, 'w') as f:
        f.write(preamble)
        for lhs in subgraph_equations:
            for rhs in subgraph_equations:
                f.write(generate_equation_statement(lhs,rhs))

def prune_file(name : str):
    path = os.path.join('equational_theories', 'Generated', f"{name}Egg.lean")
    res = subprocess.run(['lake', 'lean', path], capture_output=True, encoding='UTF-8')


    err = re.compile(f"{path}:([0-9]+):[0-9]+: (error|egg failed)")
    warn = re.compile(f"{path}:([0-9]+):[0-9]+: warning: unused variable")
    variable = re.compile("h: Equation")

    err_matches = err.finditer(res.stdout)
    warn_matches = warn.finditer(res.stdout)
    error_lines = [int(m.group(1)) for m in err_matches]
    warn_lines = [int(m.group(1)) for m in warn_matches]
    print(f" removing {len(error_lines)} lines with errors, and {len(warn_lines)} unused variable warnings.")

    with open(path,'r') as f:
        lines = f.readlines()
    with open(path,'w') as f:
        for n, line in enumerate(lines):
            # python counts from 0
            if (n + 1) not in error_lines:
                if (n + 1) in warn_lines:
                    line_no_unused_var = variable.sub("_ : Equation", line)
                    f.write(line_no_unused_var)
                else:
                    f.write(line)


if __name__  == "__main__":
    generate_file(subgraph_equations, "Equations")
    prune_file("Equations")
