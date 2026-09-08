#!/usr/bin/env python3
from find_dual import iter_equation_decls


def test_skips_commented_equations():
    lines = [
        "-- equation 1 := x = x\n",
        "equation 9 := x = x ◇ (x ◇ y)\n",
        "  -- equation 10 := x = y\n",
    ]
    got = list(iter_equation_decls(lines))
    assert got == [(9, "x = x ◇ (x ◇ y)")]


def test_ignores_non_decl_mentions():
    lines = [
        "/-! Equations list -/\n",
        "equation 42 := x ◇ y = x ◇ z\n",
    ]
    got = list(iter_equation_decls(lines))
    assert got == [(42, "x ◇ y = x ◇ z")]


if __name__ == "__main__":
    test_skips_commented_equations()
    test_ignores_non_decl_mentions()
    print("ok - find_dual parse")
