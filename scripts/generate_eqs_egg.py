subgraph_equations = [1, 2, 3, 4, 5, 6, 7, 8, 14, 23, 29, 38, 39, 40, 41, 42,
                      43, 45, 46, 168, 381, 387, 1689, 3722, 3744, 4512, 4513,
                      4522, 4564, 4579, 4582, 5105, 28393, 374794]

preamble = """import equational_theories.Equations
import Egg

set_option egg.explosion true
set_option egg.timeLimit 1

"""

def generate_equation_statement(lhs : int, rhs : int):
  return f"theorem Equation{lhs}_implies_Equation{rhs} (G: Type _) [Magma G] (h: Equation{lhs} G) : Equation{rhs} G := by egg [*]\n"

if __name__  == "__main__":
    with open("equational_theories/Generated/SubgraphEgg.lean", 'w') as f:
        f.write(preamble)
        for lhs in subgraph_equations:
            for rhs in subgraph_equations:
                f.write(generate_equation_statement(lhs,rhs))
