import equational_theories.Equations.All
import equational_theories.Subgraph

namespace Equation1571
open Subgraph

theorem ProveEquation1571Consequence {n : Nat} {G : Type _} [Magma G] (eq1571 : Equation1571 G)
    (law : Law.MagmaLaw (Fin (n+1))) (eq : equation1571Reducer law.lhs = equation1571Reducer law.rhs) :
    G ⊧ law :=
  fun _ ↦ (AbGrpPow2ImpliesEquation1571ReducerFaithful law.lhs _
    (Equation1571_implies_Equation4512 G eq1571) (Equation1571_implies_Equation43 G eq1571)
      (Equation1571_implies_Equation16 G eq1571)).trans ((congrArg (evalInSgr _) eq).trans
        (AbGrpPow2ImpliesEquation1571ReducerFaithful law.rhs _
          (Equation1571_implies_Equation4512 G eq1571) (Equation1571_implies_Equation43 G eq1571)
            (Equation1571_implies_Equation16 G eq1571)).symm)

/- Example usage of the general-purpose prover ProveEquation1571Consequence -/
theorem Equation1571_implies_Equation3167 {G : Type} [Magma G] (h : Equation1571 G) : Equation3167 G :=
  fun x y z ↦ ProveEquation1571Consequence (n := 2) h
    {lhs := Lf 0, rhs := (((Lf 1 ⋆ Lf 1) ⋆ Lf 2) ⋆ Lf 2) ⋆ Lf 0} rfl fun | 0 => x | 1 => y | 2 => z

/- Example usage of the general-purpose prover ProveEquation1571Consequence -/
theorem Equation1571_implies_Equation4656 {G : Type} [Magma G] (h : Equation1571 G) : Equation4656 G :=
  fun x y z ↦ ProveEquation1571Consequence (n := 2) h
    {lhs := (Lf 0 ⋆ Lf 1) ⋆ Lf 1, rhs := (Lf 0 ⋆ Lf 2) ⋆ Lf 2} rfl fun | 0 => x | 1 => y | 2 => z

end Equation1571
