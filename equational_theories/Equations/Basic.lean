import equational_theories.Magma
import equational_theories.Equations.Command

/-! List of equational laws being studied -/

/-
This files contains a small list of selected Equations. This way this file can be conveniently
viewed and edited, without having to open a very large file.

See `Equations/All.lean` for the remaining ones. Feel free to move individual equations here if
you do manual proofs about them and you want to import just this file. But don't forget to comment
out the corresponding copy of the equations in `Equations/All.lean` if you do so!

The equations are marked as `abbrev` so that tactics like `decide` will look through the definition.
-/

/-- The reflexive law -/
equation 1  :=  x = x

/-- The singleton law -/
equation 2  :=  x = y

/-- The idempotence law -/
equation 3  :=  x = x ◇ x

/-- The left absorption law -/
equation 4  :=  x = x ◇ y

/-- The right absorption law -/
equation 5  :=  x = y ◇ x

@[inherit_doc Equation2]
equation 6  :=  x = y ◇ y

@[inherit_doc Equation2]
equation 7  :=  x = y ◇ z

/-- dual of 23 -/
equation 8  :=  x = x ◇ (x ◇ x)

/-- Appears in Problem A1 from Putnam 2001 -/
equation 14  :=  x = y ◇ (x ◇ y)

equation 16  :=  x = y ◇ (y ◇ x)

/-- dual of 8 -/
equation 23  :=  x = (x ◇ x) ◇ x

/-- Appears in Problem A1 from Putnam 2001.  Dual of 14 -/
equation 29  :=  x = (y ◇ x) ◇ y

/-- value of multiplication is independent of right argument -/
equation 38  :=  x ◇ x = x ◇ y

/-- value of multiplication is independent of left argument; dual of 38 -/
equation 39  :=  x ◇ x = y ◇ x

/-- all squares are the same -/
equation 40  :=  x ◇ x = y ◇ y

/-- all products are the same -/
equation 41  := x ◇ x = y ◇ z

@[inherit_doc Equation38]
equation 42  :=  x ◇ y = x ◇ z

/-- The commutative law -/
equation 43  :=  x ◇ y = y ◇ x

@[inherit_doc Equation39]
equation 45  :=  x ◇ y = z ◇ y

/-- The constant law -/
equation 46  :=  x ◇ y = z ◇ w

/-- The ``Asterix law''.  -/
equation 65  :=  x = y ◇ (x ◇ (y ◇ x))

/-- The central groupoid law -/
equation 168  :=  x = (y ◇ x) ◇ (x ◇ z)

/-- From Putnam 1978, Problem A4, part (b) -/
equation 381  :=  x ◇ y = (x ◇ z) ◇ y

/-- from the mathoverflow post by paste bee -/
equation 387  :=  x ◇ y = (y ◇ y) ◇ x

/-- A hard to prove non-consequence of the ``Asterix law``. -/
equation 614 := x = x ◇ (x ◇ ((x ◇ x) ◇ x))

/-- A hard to prove non-consequence of the ``Asterix law``. -/
equation 817 := x = x ◇ ((x ◇ x) ◇ (x ◇ x))

equation 953  :=  x = y ◇ ((z ◇ x) ◇ (z ◇ z))

/-- A hard to prove non-consequence of the ``Asterix law``. -/
equation 1426 := x = (x ◇ x) ◇ (x ◇ (x ◇ x))

/-- The ``Obelix law'' -/
equation 1491  :=  x = (y ◇ x) ◇ (y ◇ (y ◇ x))

/-- From a paper of Mendelsohn & Padmanabhan, this law axiomatizes abelian groups of exponent 2 -/
equation 1571  :=  x = (y ◇ z) ◇ (y ◇ (x ◇ z))

/-- From a paper of Kisielewicz -/
equation 1689  :=  x = (y ◇ x) ◇ ((x ◇ z) ◇ z)

/-- From a paper of Mendelsohn & Padmanabhan -/
equation 2662  :=  x = ((x ◇ y) ◇ (x ◇ y)) ◇ x

equation 3167  :=  x = (((y ◇ y) ◇ z) ◇ z) ◇ x

/-- Part of an Austin pair. -/
equation 3588  :=  x ◇ y = z ◇ ((x ◇ y) ◇ z)

/-- From Putnam 1978, Problem A4, part (a) -/
equation 3722  :=  x ◇ y = (x ◇ y) ◇ (x ◇ y)

/-- Putnam 1978, Problem A4 calls this a "bypass operation" -/
equation 3744  :=  x ◇ y = (x ◇ z) ◇ (w ◇ y)

/-- A hard to prove non-consequence of the ``Asterix law``. -/
equation 3862 := x ◇ x = (x ◇ (x ◇ x)) ◇ x

/-- Part of an Austin pair. -/
equation 3994 := x ◇ y = (z ◇ (x ◇ y)) ◇ z

/-- A hard to prove non-consequence of the ``Asterix law``. -/
equation 4065 := x ◇ x = ((x ◇ x) ◇ x) ◇ x

/-- The associative law -/
equation 4512  :=  x ◇ (y ◇ z) = (x ◇ y) ◇ z

/-- dual of 4564 -/
equation 4513  :=  x ◇ (y ◇ z) = (x ◇ y) ◇ w

/-- dual of 4579 -/
equation 4522  :=  x ◇ (y ◇ z) = (x ◇ w) ◇ u

/-- dual of 4513 -/
equation 4564  :=  x ◇ (y ◇ z) = (w ◇ y) ◇ z

/-- dual of 4522 -/
equation 4579  :=  x ◇ (y ◇ z) = (w ◇ u) ◇ z

/-- all products of three values are the same, regardless bracketing -/
equation 4582  :=  x ◇ (y ◇ z) = (w ◇ u) ◇ v

equation 4656  :=  (x ◇ y) ◇ y = (x ◇ z) ◇ z

/- Some order 5 laws -/

/-- Mentioned in a paper of Kisielewicz as a conjectural Austin law -/
equation 5105  :=  x = y ◇ (y ◇ (y ◇ (x ◇ (z ◇ y))))

/-- The natural central groupoid law. -/
equation 26302  :=  x = (y ◇ ((z ◇ x) ◇ w)) ◇ (x ◇ w)

/-- Kisielewicz's second Austin law -/
equation 28770  :=  x = (((y ◇ y) ◇ y) ◇ x) ◇ (y ◇ z)

/- Some order 6 laws -/

/-- The Sheffer stroke law. -/
equation 345169  :=  x = (y ◇ ((x ◇ y) ◇ y)) ◇ (x ◇ (z ◇ y))

/-- Kisielewicz's first Austin law -/
equation 374794  :=  x = (((y ◇ y) ◇ y) ◇ x) ◇ ((y ◇ y) ◇ z)
