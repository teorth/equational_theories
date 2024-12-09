import equational_theories.Equations.All


namespace Eq467

/- Proof sketch:
* From 467 the $$L_y$$ are surjective, hence invertible.
* From 467 again one has $$Sy = y (Sy . S^2 y)$$, hence by left cancellability $$y = Sy . S^2 y$$.  Hence squaring is injective, hence invertible, and $$S^{-1} y = y . Sy$$.
* From 467 we have $$Sx = Sx . Cx$$ where $$Cx = Sx.x$$.
* From 467 again we have $$Sx = S^{-1} x . L_{Sx}^2 x = S^{-1} x . Sx = (x . Sx) . Sx$$, hence by invertibility of $$S$$, $$x = (S^{-1} x . x) . x$$, which gives 2847.
 -/

@[equational_result]
conjecture Equation467_implies_Equation2847 (G : Type) [Magma G] [Finite G] (_ : Equation467 G) : Equation2847 G


end Eq467
