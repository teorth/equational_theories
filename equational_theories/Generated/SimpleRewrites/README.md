Auto-generate all proofs that can be solved by substitution and variable re-naming. Specifically, all theorems are of the form

```
theorem Equation2237_implies_Equation2235 := λ x y z w u => h x y z w u w
```

Running `src/find_simple_rewrites.py` will automatically generate this list.

This scripts finds simple rewrites by first syntactically checking if it looks like there might be a possible rewrite rule that matches, and if so, runs a very simple (but slower) inference check to make sure it works.