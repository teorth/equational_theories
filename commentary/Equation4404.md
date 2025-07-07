This law is equivalent to stating that `x ◇ (x ◇ _)` and `(x ◇ _) ◇ _` only depend on `x` and are equal.

This law implies that the squaring map `S: x ↦ x◇x` obeys `S(S(S(x))) = S(S(x))`.

The free magma on some set `S` of generators for this law consists of finite non-empty lists of elements of `S` whose consecutive elements are generally distinct, except that the last two or last three are allowed to be equal, and with the operation defined by `[s] ◇ [t] = [s, t]` and `[s] ◇ [t, …, u] = [s, t, …, u]` when `s≠t` and `[s] ◇ [s, …, t] = [s, s, s]` when the second operand has at least two entries, and `[s, …, t] ◇ _ = [s, s, s]` when the first operand has at least two entries.
