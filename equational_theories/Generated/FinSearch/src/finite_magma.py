import random

class FiniteMagma:
    def __init__(self, num_elements: int, table):
        self.num_elements = num_elements
        self.table = table
    
    def op(self, x: int, y: int):
        return self.table[x + self.num_elements*y]

    def __str__(self):
        ret = "x | y | x ∘ y"
        for x in range(self.num_elements):
            for y in range(self.num_elements):
                ret += f"\n{x} | {y} |   {self.op(x,y)}"
        return ret


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