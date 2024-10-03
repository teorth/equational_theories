import random
from parser import Equation

def enumerate_assignments(num_elements, vars):
    N = len(vars)
    M = num_elements
    current = [0] * N
    while True:
        yield {v:x for v,x in zip(vars, current)}

        for i in range(N - 1, -1, -1):
            if current[i] < M - 1:
                current[i] += 1
                break
            else:
                current[i] = 0
        else:
            break

class FiniteMagma:
    def __init__(self, num_elements: int, table):
        self.num_elements = num_elements
        self.table = table

    def op(self, x: int, y: int):
        return self.table[x + self.num_elements*y]

    def __str__(self):
        ret = "x | y | x ◇ y"
        for x in range(self.num_elements):
            for y in range(self.num_elements):
                ret += f"\n{x} | {y} |   {self.op(x,y)}"
        return ret

    @property
    def matrix(self):
        #[ #[2,1,1,2], #[2,1,1,2], #[3,0,0,3], #[3,0,0,3] ]
        return "#[ " + ", ".join("#[" + ",".join(str(self.op(i,j)) for j in range(self.num_elements)) + "]" for i in range(self.num_elements)) + " ]"

    def to_data(self, all_equations: list[Equation]):
        #Table [[2, 3, 2, 3], [3, 2, 3, 2], [1, 0, 1, 0], [0, 1, 0, 1]]
        ret = "Table [" + ", ".join("[" + ",".join(str(self.op(i,j)) for j in range(self.num_elements)) + "]" for i in range(self.num_elements)) + "]\n"
        ret += "Proves " + str(sorted(eq.equation_number for eq in all_equations if self.proves(eq)))
        return ret

    @property
    def id(self):
        return f"{self.num_elements}_{self.number}"

    @property
    def number(self):
        factor = 1
        ret = 0
        for i in range(self.num_elements):
            for j in range(self.num_elements):
                ret += factor*self.op(i,j)
                factor *= self.num_elements
        return ret

    def proves(self, eq: Equation):
        return all(eq.eval(a, self.op) for a in enumerate_assignments(self.num_elements, eq.free_variables))


def enumerate_finite_magmas(num_elements):
    N = num_elements**2
    M = num_elements

    current = [0] * N
    while True:
        yield FiniteMagma(num_elements, current.copy())

        for i in range(N - 1, -1, -1):
            if current[i] < M - 1:
                current[i] += 1
                break
            else:
                current[i] = 0
        else:
            break

def random_finite_magma(num_elements):
    return FiniteMagma(num_elements, [random.randint(0,num_elements-1) for _ in range(num_elements**2)])



class Theorem:
    def __init__(self, magma: FiniteMagma, sat: list[Equation], unsat: list[Equation]):
        self.magma = magma
        self.sat = sat
        self.unsat = unsat

    def to_lean(self):
        m = self.magma
        N = m.num_elements

        ret = f"def Magma{m.id} : Magma (Fin {N}) where op := memoFinOp (ofMatrix {m.matrix})\n\n"

        unsat_groups = [(self.unsat[:2000], "")]
        if len(self.unsat) > 2000:
            unsat_groups.append((self.unsat[2000:], "_2"))

        for unsat_group, prefix in unsat_groups:
            ret += f"""
@[equational_result]
theorem Magma{m.id}{prefix}.Facts : ∃ (G : Type) (_ : Magma G), Facts G [{','.join(str(x.equation_number) for x in self.sat)}][{','.join(str(x.equation_number) for x in unsat_group)}]:= ⟨Fin {N}, Magma{m.id}, by decideFin!⟩
"""
        return ret
