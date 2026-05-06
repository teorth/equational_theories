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

/-- The reflexive law. -/
equation 1  :=  x = x

/-- The singleton law. -/
equation 2  :=  x = y

/-- The idempotence law. -/
equation 3  :=  x = x ◇ x

/-- The left absorption law. -/
equation 4  :=  x = x ◇ y

/-- The right absorption law. -/
equation 5  :=  x = y ◇ x

/-- Equivalent to the singleton law, `Equation2`. -/
equation 6  :=  x = y ◇ y

/-- Equivalent to the singleton law, `Equation2`. -/
equation 7  :=  x = y ◇ z

/-- Dual of `Equation23`. -/
equation 8  :=  x = x ◇ (x ◇ x)

/-- Appears in Problem A1 from Putnam 2001 -/
equation 14  :=  x = y ◇ (x ◇ y)

equation 16  :=  x = y ◇ (y ◇ x)

/-- Dual of `Equation8`. -/
equation 23  :=  x = (x ◇ x) ◇ x

/-- Appears in Problem A1 from Putnam 2001. Dual of `Equation14`. -/
equation 29  :=  x = (y ◇ x) ◇ y

/-- Value of multiplication is independent of right argument. Dual of `Equation39`. -/
equation 38  :=  x ◇ x = x ◇ y

/-- Value of multiplication is independent of left argument. Dual of `Equation38`. -/
equation 39  :=  x ◇ x = y ◇ x

/-- All squares are the same. -/
equation 40  :=  x ◇ x = y ◇ y

/-- All products are the same. -/
equation 41  := x ◇ x = y ◇ z

@[inherit_doc Equation38]
equation 42  :=  x ◇ y = x ◇ z

/-- The commutative law. -/
equation 43  :=  x ◇ y = y ◇ x

@[inherit_doc Equation39]
equation 45  :=  x ◇ y = z ◇ y

/-- The constant law. -/
equation 46  :=  x ◇ y = z ◇ w

/-- The "Asterix law". -/
equation 65  :=  x = y ◇ (x ◇ (y ◇ x))

/-- The central groupoid law. -/
equation 168  :=  x = (y ◇ x) ◇ (x ◇ z)

/-- Part of an Austin pair. -/
equation 203 := x = (x ◇ (x ◇ x)) ◇ x

/-- From Putnam 1978, Problem A4, part (b) -/
equation 381  :=  x ◇ y = (x ◇ z) ◇ y

/-- from the [MathOverflow Post](https://mathoverflow.net/a/450905/97603) by user "paste bee". -/
equation 387  :=  x ◇ y = (y ◇ y) ◇ x

/-- A hard to prove non-consequence of the "Asterix law", `Equation65`. -/
equation 614  :=  x = x ◇ (x ◇ ((x ◇ x) ◇ x))

/-- A hard to prove non-consequence of the "Asterix law", `Equation65`. -/
equation 817  :=  x = x ◇ ((x ◇ x) ◇ (x ◇ x))

equation 953  :=  x = y ◇ ((z ◇ x) ◇ (z ◇ z))

/-- A hard to prove non-consequence of the "Asterix law", `Equation65`. -/
equation 1426  :=  x = (x ◇ x) ◇ (x ◇ (x ◇ x))

/-- The weak central groupoid law. -/
equation 1485 := x = (y ◇ x) ◇ (x ◇ (z ◇ y))

/-- The "Obelix law". -/
equation 1491  :=  x = (y ◇ x) ◇ (y ◇ (y ◇ x))

/-- From [a paper of Mendelsohn & Padmanabhan](https://doi.org/10.1016/0021-8693(75)90169-6), this law axiomatizes abelian groups of exponent 2. -/
equation 1571  :=  x = (y ◇ z) ◇ (y ◇ (x ◇ z))

/-- A law with a modified translation-invariant model. -/
equation 1659  :=  x = (x ◇ y) ◇ ((y ◇ y) ◇ z)

/-- A law with a modified translation-invariant model. -/
equation 1661  :=  x = (x ◇ y) ◇ ((y ◇ z) ◇ y)

/-- From [a paper of Kisielewicz](https://doi.org/10.1007/s000120050057), equivalent to the sigleton law `Equation2` but only by a fairly nontrivial proof. -/
equation 1689  :=  x = (y ◇ x) ◇ ((x ◇ z) ◇ z)

/-- A law with a modified translation-invariant model. -/
equation 1701 := x = (y ◇ x) ◇ ((z ◇ x) ◇ x)

/-- The dual weak central groupoid law -/
equation 2162  :=  x = ((y ◇ z) ◇ x) ◇ (x ◇ y)

/-- From [a paper of Mendelsohn & Padmanabhan](https://doi.org/10.1016/0021-8693(75)90169-6). -/
equation 2662  :=  x = ((x ◇ y) ◇ (x ◇ y)) ◇ x

/-- Part of an Austin pair. -/
equation 3588  :=  x ◇ y = z ◇ ((x ◇ y) ◇ z)

/-- From Putnam 1978, Problem A4, part (a). -/
equation 3722  :=  x ◇ y = (x ◇ y) ◇ (x ◇ y)

/-- Putnam 1978, Problem A4 calls this a "bypass operation". -/
equation 3744  :=  x ◇ y = (x ◇ z) ◇ (w ◇ y)

/-- A hard to prove non-consequence of the "Asterix law", `Equation65`. -/
equation 3862  :=  x ◇ x = (x ◇ (x ◇ x)) ◇ x

/-- Part of an Austin pair. -/
equation 3994  :=  x ◇ y = (z ◇ (x ◇ y)) ◇ z

/-- A hard to prove non-consequence of the "Asterix law", `Equation65` -/
equation 4065  :=  x ◇ x = ((x ◇ x) ◇ x) ◇ x

/-- A hard to prove consequence of several laws. -/
equation 4315  :=  x ◇ (y ◇ x) = x ◇ (y ◇ z)

/-- The associative law. -/
equation 4512  :=  x ◇ (y ◇ z) = (x ◇ y) ◇ z

/-- dual of `Equation4564` -/
equation 4513  :=  x ◇ (y ◇ z) = (x ◇ y) ◇ w

/-- dual of `Equation4579` -/
equation 4522  :=  x ◇ (y ◇ z) = (x ◇ w) ◇ u

/-- dual of `Equation4513` -/
equation 4564  :=  x ◇ (y ◇ z) = (w ◇ y) ◇ z

/-- dual of `Equation4522` -/
equation 4579  :=  x ◇ (y ◇ z) = (w ◇ u) ◇ z

/-- States that all products of three values are the same, regardless bracketing. -/
equation 4582  :=  x ◇ (y ◇ z) = (w ◇ u) ◇ v

/- Some order 5 laws -/

/-- Mentioned in [a paper of Kisielewicz](https://doi.org/10.1007/s000120050057) as a conjectural Austin law. -/
equation 5093  :=  x = y ◇ (y ◇ (y ◇ (x ◇ (z ◇ y))))

/-- The natural central groupoid law. -/
equation 26302  :=  x = (y ◇ ((z ◇ x) ◇ w)) ◇ (x ◇ w)

/-- Kisielewicz's second Austin law, see `Equation374794` for the first. -/
equation 28770  :=  x = (((y ◇ y) ◇ y) ◇ x) ◇ (y ◇ z)

/-- The left self-distributive law, as in shelves, racks and quandles. See `Equation60491` for the right one. -/
equation 56085  :=  x ◇ (y ◇ z) = (x ◇ y) ◇ (x ◇ z)

/-- The right self-distributive law, as in shelves, racks and quandles, See `Equation56085` for the left one. -/
equation 60491  :=  (x ◇ y) ◇ z = (x ◇ z) ◇ (y ◇ z)

/- Some order 6 laws -/

/-- An equation [characterizing](https://leanprover.zulipchat.com/#narrow/channel/458659-Equational/topic/The.20.22modules.20over.20Gaussian.20integers.22.20law/near/519928430) `x ◇ y = x + √-1 y` on modules over the ring `ℤ[√-1]`, the Gaussian integers. -/
equation 86082  :=  x = y ◇ (z ◇ ((y ◇ z) ◇ (w ◇ (x ◇ w))))

/-- One of the four order-six laws that characterize the Sheffer stroke. Dual to `Equation361729`. -/
equation 321577  :=  x = ((y ◇ z) ◇ x) ◇ (y ◇ ((y ◇ x) ◇ y))

/-- One of the four order-six laws that characterize the Sheffer stroke. This is referred to as `BA-1` in [McCune et al.](https://doi.org/10.2172/764209). Dual to `Equation345169`. -/
equation 329857  :=  x = ((y ◇ z) ◇ x) ◇ ((y ◇ (y ◇ x)) ◇ y)

/-- One of the four order-six laws that characterize the Sheffer stroke, what [McCune et al.](https://doi.org/10.1023/A:1020542009983) call `Sh₁`, or [in another work](https://doi.org/10.2172/764209) instead `BA-2`. Dual to `Equation329857`. -/
equation 345169  :=  x = (y ◇ ((x ◇ y) ◇ y)) ◇ (x ◇ (z ◇ y))

/-- One of the four order-six laws that characterize the Sheffer stroke, what [McCune et al.](link) call `Sh₂`. Dual to `Equation321577`. -/
equation 361729  :=  x = ((y ◇ (x ◇ y)) ◇ y) ◇ (x ◇ (z ◇ y))

/-- Kisielewicz's first Austin law, see `Equation28770` for the second. -/
equation 374794  := x = (((y ◇ y) ◇ y) ◇ x) ◇ ((y ◇ y) ◇ z)

/-- The second Jordan law, which together with the commutative `Equation43` defines Jordan algebras. -/
equation 906021  :=  x ◇ (y ◇ (x ◇ x)) = (x ◇ y) ◇ (x ◇ x)

/-- The left Bol loop law, see `Equation930594` for the right one. -/
equation 910472  :=  x ◇ (y ◇ (x ◇ z)) = (x ◇ (y ◇ x)) ◇ z

/-- The first Moufang law (of four, which are equivalent for loops). -/
equation 914612  := x ◇ (y ◇ (x ◇ z)) = ((x ◇ y) ◇ x) ◇ z

/-- The second Moufang law, -/
equation 916037  :=  x ◇ (y ◇ (z ◇ y)) = ((x ◇ y) ◇ z) ◇ y

/-- The right Bol loop law, see `Equation910472` for the left one. -/
equation 930594  :=  x ◇ ((y ◇ z) ◇ y) = ((x ◇ y) ◇ z) ◇ y

/-- The third Moufang law. -/
equation 936498  :=  (x ◇ y) ◇ (z ◇ x) = (x ◇ (y ◇ z)) ◇ x

/-- The fourth Moufang law. -/
equation 921941  :=  x ◇ ((y ◇ z) ◇ x) = (x ◇ y) ◇ (z ◇ x)

/-- The Higman-Neumann axiom, which characterized (not necessarily Abelian) groups, as [proved by Higman and Neuman](https://doi.org/10.5486/pmd.1952.2.3-4.10) in 1956. -/
equation 42323216 :=  x = y ◇ ((((y ◇ y) ◇ x) ◇ z) ◇ (((y ◇ y) ◇ y) ◇ z))

/-- A. K. Austin's law that permits infinite models, but no finite ones. -/
equation 1875916474  :=  x = (((y ◇ y) ◇ y) ◇ x) ◇ (((y ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ z)
