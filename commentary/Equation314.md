This law is equivalent to stating that all squares and all three-fold products of the form `\_ ◇ (\_ ◇ \_)` are equal to the same element.

See also [law 4526](https://teorth.github.io/equational_theories/implications/?4526) which implies associativity and that three-fold products are all equal.

The free magma on some set `S` of generators for this law is the set of finite lists of elements of `S` (including the empty list `[]`), where all products are `[]` unless the second operand has length one, and generally `[s1, ..., sn] ◇ [s] = [s1, ..., sn, s]` except for two special cases `[] ◇ [s] = [s, s]` and `[s] ◇ [s] = []`.
