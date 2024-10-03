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

/-- `a ∘ b` computes a binary operation of `a` and `b`.

We ensure that this notation has priority over function composition. This means that
*function composition notation is not available in this repository*.
Reason for this choice: the overloading caused huge slowdowns when compiling some definitions
Zulip thread: https://leanprover.zulipchat.com/#narrow/stream/458659-Equational/topic/Symbol.20for.20.60Magma.2Eop.60 -/
infix:65 (priority := high) " ∘ " => Magma.op


/-! Test that the function composition notation now fails. -/

/--
error: failed to synthesize
  Magma (Nat → Nat)
Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#guard_msgs(error) in
example (g f : Nat → Nat) : g ∘ f = id := rfl

/-- This instance is (only) available after writing `open MagmaToMul` -/
scoped instance MagmaToMul.inst {α : Type _} [Magma α] : Mul α where
  mul := Magma.op

/-- This instance is (only) available after writing `open MagmaToAdd` -/
scoped instance MagmaToAdd.inst {α : Type _} [Magma α] : Add α where
  add := Magma.op

/-- This instance is (only) available after writing `open MulToMagma` -/
scoped instance MulToMagma.inst {α : Type _} [Mul α] : Magma α where
  op := (· * ·)

/-- This instance is (only) available after writing `open AddToMagma` -/
scoped instance AddToMagma.inst {α : Type _} [Add α] : Magma α where
  op := (· + ·)
