# Higman-Neumann data

This note describes the file [`Higman-Neumann.json`](Higman-Neumann.json), which records the results of the "Higman–Neumann laws" section of the Equational Theories Project paper.

## Background

A *Ward quasigroup* is a group equipped with the division operation `x ◇ y = x * y⁻¹`. Higman and Neumann showed that Ward quasigroups are characterized among magmas by a single law of order 8, Equation 42323216, referred to below as E_HN:

```
x = y ◇ ((((y ◇ y) ◇ x) ◇ z) ◇ (((y ◇ y) ◇ y) ◇ z))
```

The paper's search for all laws of order at most 8 with this property eliminated all but 213 candidates, each of order exactly 8. This file lists those 213 laws and records how far each has been resolved.

## File format

The file is a JSON array with one object per law, sorted by increasing `id` and written one per line:

```
{"id" : 42323216, "law" : "x = y ◇ ((((y ◇ y) ◇ x) ◇ z) ◇ (((y ◇ y) ◇ y) ◇ z))", "parent" : 42359357, "class" : "HN-equivalent"},
```

It can be read with any JSON parser, for example `json.load` in Python.

## Fields

| Field | Meaning |
|---|---|
| `id` | The number of the law in the project's numbering system, described in the appendix of the paper. `scripts/find_equation_id.py` converts between numbers and laws. |
| `law` | The law itself, with `◇` as the magma operation. |
| `parent` | The number of the 5-variable law in this law's family (see below). A parent law is listed as its own parent. |
| `class` | The status of the law (see below). |

## Classes

| `class` | Number of laws | Meaning |
|---|---|---|
| `HN-equivalent` | 179 | The law is equivalent to E_HN, so its models are exactly the Ward quasigroups. |
| `finite-equivalent` | 21 | The law is equivalent to E_HN among finite magmas, so its finite models are exactly the finite Ward quasigroups. Whether it has infinite models that are not Ward quasigroups is unresolved. |
| `unknown-candidate` | 13 | No proof that the law implies E_HN and no countermodel is known, even for finite magmas. |

## Families

The 213 laws fall into 31 families, of 3 to 12 laws each. Each family consists of one 5-variable parent law together with the specializations obtained from it by identifying variables, so a parent law implies every law in its family. For example, E_HN is obtained from its parent, Equation 42359357,

```
x = y ◇ ((((z ◇ z) ◇ x) ◇ w) ◇ (((u ◇ u) ◇ y) ◇ w))
```

by replacing `z` and `u` with `y`, and by then renaming `w` to `z`.

All 31 parent laws have class `HN-equivalent`. The other laws in the file have 3 or 4 variables (30 and 152 laws, respectively).

## Scope

The file records conclusions only. It does not contain the proofs, which were obtained with automated theorem provers, or the countermodels used to eliminate other laws. These results have not been formalized in Lean.
