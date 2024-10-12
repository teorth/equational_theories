from PySingular import RunSingularCommand, InitializeSingular
from pexpect import which
import json
import re

InitializeSingular(which( "Singular"))

def parse_basis(result):
    def fix_exponents(expr):
        return re.sub(r"([a-z])(\d+)", lambda m: f"{m.group(1)}**{m.group(2)}", expr)
    result = [fix_exponents(x.split("=")[1]) for x in result.split()]
    return result

for commute in (True,):
    if commute:
        RunSingularCommand( "ring R = 0, (a, b), dp;" )
    else:
        RunSingularCommand( "ring R = 0, (a, b), dp; option(redSB);" )

    with open("data/linear_magma_restrictions.txt") as input:
        with open(f"data/linear_magma_reduced_restrictions_{'' if commute else 'non_'}commutative.txt", "w") as out:
            for line in input:
                line = line.strip()
                if not line:
                    continue
                eq_id, restrictons = line.split(maxsplit=1)
                eq_id, restrictons = int(eq_id), restrictons.lstrip("[").rstrip("]").replace("**", "^")
                if restrictons:
                    error, result = RunSingularCommand(f"ideal I{eq_id} = {restrictons}; ideal G{eq_id} = groebner(I{eq_id}); G{eq_id};")
                    assert not error
                    restriction_str = "[" + ", ".join(parse_basis(result)) + "]"
                    print(eq_id, restrictons, restriction_str)
                    out.write(f"{eq_id} {restriction_str}\n")
                else:
                    print(eq_id, restrictons, [])
                    out.write(f"{eq_id} []\n")
