import Mathlib.Data.Set.Finite.Basic

import equational_theories.EquationalResult
import equational_theories.Equations.All

/- Proves the implications clustered around the equation 1441.

When the proof is done, update the blueprint with \lean and \leanok tags as appropriate.
-/

namespace Eq1441

/- Proof can be found at https://teorth.github.io/equational_theories/blueprint/infinite-model-chapter.html#1441-4067-1443-3055 -/

@[equational_result]
conjecture Finite.Equation1441_implies_Equation4067 (G : Type) [Magma G] [Finite G] (_ : Equation1441 G) : Equation4067 G



/- Proof can be found at https://teorth.github.io/equational_theories/blueprint/infinite-model-chapter.html#1441-4067-1443-3055 -/

@[equational_result]
conjecture Finite.Equation1443_implies_Equation3055 (G : Type) [Magma G] [Finite G] (_ : Equation1443 G) : Equation3055 G


/- Proof can be found at https://teorth.github.io/equational_theories/blueprint/infinite-model-chapter.html#1681-3877-1701-1035 -/

@[equational_result]
conjecture Finite.Equation1681_implies_Equation3877 (G : Type) [Magma G] [Finite G] (_ : Equation1681 G) : Equation3877 G



/- Proof can be found at https://teorth.github.io/equational_theories/blueprint/infinite-model-chapter.html#1681-3877-1701-1035 -/

@[equational_result]
conjecture Finite.Equation1701_implies_Equation1035 (G : Type) [Magma G] [Finite G] (_ : Equation1701 G) : Equation1035 G


end Eq1441
