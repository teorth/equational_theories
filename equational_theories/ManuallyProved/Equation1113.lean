import equational_theories.Equations.All


/- Proves the implications clustered around the equation 1113.
 -/

namespace Eq1113

/- Proof can be found at https://teorth.github.io/equational_theories/blueprint/infinite-model-chapter.html#1167-1096
 -/

@[equational_result]
conjecture Equation1133_implies_Equation1167 (G : Type) [Magma G] [Finite G] (_ : Equation1133 G) : Equation1167 G

/- Proof can be found at https://teorth.github.io/equational_theories/blueprint/infinite-model-chapter.html#1167-1096
 -/

@[equational_result]
conjecture Finite.Equation1167_implies_Equation1096 (G : Type) [Magma G] [Finite G] (_ : Equation1167 G) : Equation1096 G


end Eq1113
