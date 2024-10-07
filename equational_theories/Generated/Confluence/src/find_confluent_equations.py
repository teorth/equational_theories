from scripts.generate_eqs_list import eqs, format_expr


def leafs(x):
    if isinstance(x, int):
        yield x
    else:
        yield from leafs(x[0])
        yield from leafs(x[1])


def subexprs(expr, strict=False):
    if not strict:
        yield expr
    if isinstance(expr, tuple):
        yield from subexprs(expr[0])
        yield from subexprs(expr[1])


def u(expr):
    if isinstance(expr, int):
        return expr + 10
    else:
        return (u(expr[0]), u(expr[1]))


def subst(expr, v, term):
    if isinstance(expr, int):
        if expr == v:
            return term
        else:
            return expr
    else:
        return (subst(expr[0], v, term), subst(expr[1], v, term))


def unify(expr1, expr2):
    components = {}
    def equate(e1, e2):
        if e1 not in components:
            components[e1] = {e1}
        if e2 not in components:
            components[e2] = {e2}
        e1_comp = components[e1]
        e2_comp = components[e2]
        if e1_comp is not e2_comp:
            joint = e1_comp | e2_comp
            for x in joint:
                components[x] = joint
            for a in e1_comp:
                if isinstance(a, tuple):
                    for b in e2_comp:
                        if isinstance(b, tuple):
                            equate(a[0], b[0])
                            equate(a[1], b[1])
    equate(expr1, u(expr2))
    for c in set(map(frozenset, components.values())):
        for a in c:
            for b in c:
                if a in subexprs(b, strict=True):
                    return False
    return True


def is_confluent(expr):
    return not any(unify(expr, sub) for sub in subexprs(expr, strict=True) if isinstance(sub, tuple))


for i, eq in enumerate(eqs):
    if isinstance(eq[0], int) and isinstance(eq[1], tuple):
        if is_confluent(eq[1]):
            print(format_expr(eq[0]), '=', format_expr(eq[1]), f'     ({i+1})')
