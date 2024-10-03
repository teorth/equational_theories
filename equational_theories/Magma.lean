/- This file contains the API for Magmas.
The `Magma α` class is very similar to the `Mul α` class.  However, we avoid using
`Mul α` here because sometimes we wish to place a Magma structure on a type, such as `ℕ`, in which
the Magma operation `∘` differs from the usual multiplication operation `*`
(or the addition operation `+`) on that type.  To avoid instance diamonds, we use `∘` instead.
(Also, there is a psychological reason for avoiding `*` and `+`, which is that these operations
suggest associativity, whereas most of the Magmas in our application will not be anywhere close to
associative.) -/

class Magma (α : Type _) where
  /-- `a ∘ b` computes a binary operation of `a` and `b`. -/
  op : α → α → α

@[inherit_doc] infix:65 " ∘ " => Magma.op
