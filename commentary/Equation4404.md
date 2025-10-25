This law is equivalent to stating that `x ◇ (x ◇ _)` and `(x ◇ _) ◇ _` only depend on `x` and are equal.  The set of cubes `x◇(x◇x) = (x◇x)◇x`, and the set of squares `x◇x`, are submagmas.  The squaring map `S: x ↦ x◇x`  `S(S(S(x))) = S(S(x))`.  Any idempotent element (such as `S(S(x))`) is a left zero.

This law cannot hold in a non-trivial quasigroup.

The free magma on some set `Σ` of generators for this law consists of finite non-empty lists of elements of `Σ` whose consecutive elements are generally distinct, except that the last two or last three are allowed to be equal, and with the operation defined by `[s] ◇ [t] = [s, t]` and `[s] ◇ [t, …, u] = [s, t, …, u]` when `s≠t` and `[s] ◇ [s, …, t] = [s, s, s]` when the second operand has at least two entries, and `[s, …, t] ◇ _ = [s, s, s]` when the first operand has at least two entries.
