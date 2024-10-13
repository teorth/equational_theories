/- This file contains the API for Magmas.
The `Magma α` class is very similar to the `Mul α` class.  However, we avoid using
`Mul α` here because sometimes we wish to place a Magma structure on a type, such as `ℕ`, in which
the Magma operation `◇` differs from the usual multiplication operation `*`
(or the addition operation `+`) on that type.  To avoid instance diamonds, we use `◇` instead.
(Also, there is a psychological reason for avoiding `*` and `+`, which is that these operations
suggest associativity, whereas most of the Magmas in our application will not be anywhere close to
associative.) -/

import Mathlib.Algebra.Opposites

class Magma (α : Type _) where
  /-- `a ◇ b` computes a binary operation of `a` and `b`. -/
  op : α → α → α

@[inherit_doc] infix:65 " ◇ " => Magma.op

namespace MulOpposite

instance magma {α : Type _} [Magma α] : Magma αᵐᵒᵖ where
  op x y := op (unop y ◇ unop x)

theorem unop_diw {α : Type _} [Magma α] (x y : αᵐᵒᵖ) : unop (x ◇ y) = unop y ◇ unop x := rfl

end MulOpposite

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
