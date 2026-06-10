# Linear Magma Implication Graph (Coefficient Ideal Method)

Complete determination of the linear magma implication graph for ETP laws,
using coefficient ideals and Nullstellensatz certificates.

## Method

For a prime field F_p, the linear magma x ◇ y = ax + by satisfies an ETP
equation E iff every coefficient difference c_i(lhs; a,b) - c_i(rhs; a,b)
vanishes at (a,b) mod p. This reduces the finite-model search to algebraic
geometry in the affine (a,b)-plane.

Each equation defines a coefficient ideal I_E ⊂ Z[a,b]. An anti-implication
E_i ≠> E_j over F_p is a rational point in X_{E_i} \ X_{E_j}. An implication
E_i => E_j for ALL prime fields holds iff I_j ⊆ √{I_i} (radical containment),
which is decidable by Groebner bases over Q.

## Results

### 2-variable laws (810 equations)

| Metric | Value |
|--------|-------|
| Total ordered pairs | 656,100 |
| Anti-implications (separated by p ≤ 31) | 608,948 |
| Implications (certified by Groebner) | 47,152 |
| Open pairs | **0** |
| Saturation prime | p = 13 |

### 3-variable laws (2,090 equations)

| Metric | Value |
|--------|-------|
| Total ordered pairs | 4,368,100 |
| Anti-implications (separated by p ≤ 31) | 2,692,333 |
| Implications (certified by Groebner) | 1,675,767 |
| Open pairs | **0** |
| Saturation prime | p = 7 |

Every ordered pair is either separated by a witness prime or certified as a
radical containment. Zero open pairs remain. The anti-implication relation
saturates at p ≤ 13 (2-var) and p ≤ 7 (3-var) for all primes.

## Scripts

All scripts are self-contained (no external dependencies beyond Python stdlib).

- `coefficient_analysis.py` — generates all 4,694 ETP laws, computes coefficient
  ideals, runs prime-field scan through p = 31. Output: JSON with per-equation
  ideal data and scan statistics.

- `nullstellensatz_check.py` — for the 810 two-variable laws, checks radical
  containment for all unseparated pairs using exact Buchberger over Q[a,b].
  Contains a built-in Groebner basis implementation (no sympy needed).

- `nullstellensatz_3var_check.py` — same for the 2,090 three-variable laws.

### Usage

```bash
# Step 1: coefficient analysis + prime scan (~8 seconds)
python3 coefficient_analysis.py

# Step 2: Nullstellensatz certification, 2-var (~6 seconds)
python3 nullstellensatz_check.py

# Step 3: Nullstellensatz certification, 3-var (~15 seconds)
python3 nullstellensatz_3var_check.py
```

## Reference

This work comes from the [Omega project](https://github.com/the-omega-institute/automath),
which studies the mathematical structures forced by x² = x + 1 (the golden mean shift).
The coefficient ideal framework arises naturally from this constraint.

See also: [Issue #418 discussion](https://github.com/teorth/equational_theories/issues/418)
