import equational_theories.Equations
import equational_theories.FreeMagma
import equational_theories.MagmaLaw

open FreeMagma
open Law

def treeConcat {α : Type _} (t : FreeMagma α) : List α :=
  match t with
    | Lf a      => [a]
    | (tl ⋆ tr) => treeConcat tl ++ treeConcat tr

def rightJoinTrees {α : Type _} (t1 t2 : FreeMagma α) : FreeMagma α :=
  match t1 with
    | Lf a      =>  Lf a ⋆ t2
    | (tl ⋆ tr) => tl ⋆ (rightJoinTrees tr t2)

def rightAssociateTree {α : Type _} (t : FreeMagma α) : FreeMagma α :=
  match t with
    | Lf a      => Lf a
    | (tl ⋆ tr) => rightJoinTrees (rightAssociateTree tl) (rightAssociateTree tr)

theorem AssocImpliesForkEquivRightJoin {α : Type _} {G : Type _} [Magma G]
  (assoc : Equation4512 G) (f : α → G) (tl tr : FreeMagma α)
  : evalInMagma f (tl ⋆ tr) = evalInMagma f (rightJoinTrees tl tr) :=
  match tl with
    | Lf _        => Eq.refl _
    | (tl1 ⋆ tl2) => Eq.trans
      (Eq.symm $ assoc (evalInMagma f tl1) (evalInMagma f tl2) (evalInMagma f tr))
      (congrArg (fun t ↦ (evalInMagma f tl1) ◇ t) (AssocImpliesForkEquivRightJoin assoc f tl2 tr))

theorem AssocFullyRightAssociate {α : Type _} {G : Type _} [Magma G]
  (assoc : Equation4512 G) (f : α → G) (t : FreeMagma α)
  : evalInMagma f t = evalInMagma f (rightAssociateTree t) :=
  match t with
    | Lf _      => Eq.refl _
    | (tl ⋆ tr) => Eq.trans
      (congrArg (fun s ↦ s ◇ (evalInMagma f tr)) (AssocFullyRightAssociate assoc f tl)) $ Eq.trans
      (congrArg (fun s ↦ (evalInMagma f (rightAssociateTree tl)) ◇ s) (AssocFullyRightAssociate assoc f tr))
      (AssocImpliesForkEquivRightJoin assoc f (rightAssociateTree tl) (rightAssociateTree tr))

/-- Example usage of AssocFullyRightAssociate -/
theorem Assoc4 {G : Type _} [Magma G] (assoc : Equation4512 G)
  : ∀ x y z w : G, ((x ◇ y) ◇ z) ◇ w = x ◇ (y ◇ (z ◇ w)) :=
  fun x y z w ↦ AssocFullyRightAssociate
    assoc
    (fun | 0 => x | 1 => y | 2 => z | 3 => w : Fin 4 → G)
    (((Lf 0 ⋆ Lf 1) ⋆ Lf 2) ⋆ Lf 3)

inductive FreeSemigroup (α : Type _)
  | Singleton : α → FreeSemigroup α
  | Cons : α → FreeSemigroup α → FreeSemigroup α

def semigroupConcat {α : Type _} (s1 s2 : FreeSemigroup α) : FreeSemigroup α :=
  match s1 with
    | FreeSemigroup.Singleton a   => FreeSemigroup.Cons a s2
    | FreeSemigroup.Cons a s1tail => FreeSemigroup.Cons a (semigroupConcat s1tail s2)

instance (α : Type _) : Magma (FreeSemigroup α) where
  op := semigroupConcat
