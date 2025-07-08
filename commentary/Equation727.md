This law implies that all left multiplications are bijective.  Composing any two right multiplications gives a constant map (namely `(z◇x)◇y` is independent of `z`).  The squaring map `S: x ↦ x◇x` and cubing maps `B: x ↦ (x◇x)◇x` and `C: x ↦ x◇(x◇x)` are bijections of order 9 with `C(x) = B(B(x))` and `S(x) = C(C(x))` and `x = B(S(S(x)))`.

The left division operation defined by `x ◇ (x : y) = y` obeys law 10577, `x = y : ((z : y) : ((z : y) : x))`.

Left multiplication by any expression is equal to left multiplication by its right-most variable, namely `(z1◇y)◇x`, `(z1◇(z2◇y))◇x`, `(z1◇(z2◇(z3◇y)))◇x` etc only depend on `y` and `x` and not on `z1,z2,z3` etc.  Additionally, one has `(z1◇(z2◇(z3◇y)))◇x = y◇x`.

This law cannot hold in a (non-trivial) commutative magma or (quasi)group.

The free magma on some set `S` of generators for this law is the set of finite non-empty lists of elements of `S×{0,1,2}` whose last element has the form `(s,0)`, and which have no sublist of the form `(t,0),(t,0),(t,1)` or `(t,1),(t,1),(t,2)` or `(t,2),(t,2),(t,0)` (for `t∈S`) except possibly as the last three elements.  The operation is generally defined by `[(s1,i1), …, (sk,0)] ◇ [(t1,j1), …, (tl,0)] = [(sk, k-1 mod 3), (t1,j1), …, (tl,0)]` for `s1,…,sk,t1,…,tl∈S` and `i1,i2,…,j1,j2,…∈{0,1,2}`, except in the case where this introduces one of the forbidden sublists, namely when `l≥3` and `sk=t1=t2` and `k-1≡j1≡j2+1 mod 3`, in which case this three-element sublist is simply deleted.
