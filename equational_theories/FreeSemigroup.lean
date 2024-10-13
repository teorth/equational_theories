import Mathlib.Logic.Basic

import equational_theories.Equations.Basic
import equational_theories.FreeMagma
import equational_theories.Homomorphisms
import equational_theories.MagmaLaw

open FreeMagma
open Law

def treeConcat {α : Type _} (t : FreeMagma α) : List α :=
  match t with
    | Lf a      => [a]
    | (tl ⋆ tr) => treeConcat tl ++ treeConcat tr

def rightJoinTrees {α : Type _} (t1 t2 : FreeMagma α) : FreeMagma α :=
  match t1 with
    | Lf a      => Lf a ⋆ t2
    | (tl ⋆ tr) => tl ⋆ (rightJoinTrees tr t2)

def rightAssociateTree {α : Type _} (t : FreeMagma α) : FreeMagma α :=
  match t with
    | Lf a      => Lf a
    | (tl ⋆ tr) => rightJoinTrees (rightAssociateTree tl) (rightAssociateTree tr)

theorem AssocImpliesForkEquivRightJoin {α : Type _} {G : Type _} [Magma G]
    (assoc : Equation4512 G) (f : α → G) (tl tr : FreeMagma α) :
    evalInMagma f (tl ⋆ tr) = evalInMagma f (rightJoinTrees tl tr) :=
  match tl with
    | Lf _        => rfl
    | (tl1 ⋆ tl2) =>
      (assoc (evalInMagma f tl1) (evalInMagma f tl2) (evalInMagma f tr)).symm.trans
      (congrArg (evalInMagma f tl1 ◇ ·) (AssocImpliesForkEquivRightJoin assoc f tl2 tr))

/- Associativity allows us to fully right-associate an entire operation tree -/
theorem AssocFullyRightAssociate {α : Type _} {G : Type _} [Magma G]
    (assoc : Equation4512 G) (f : α → G) (t : FreeMagma α) :
    evalInMagma f t = evalInMagma f (rightAssociateTree t) :=
  match t with
    | Lf _      => rfl
    | (tl ⋆ tr) => Eq.trans
      (congrArg (· ◇ (evalInMagma f tr)) (AssocFullyRightAssociate assoc f tl)) $ Eq.trans
      (congrArg (evalInMagma f (rightAssociateTree tl) ◇ ·) (AssocFullyRightAssociate assoc f tr))
      (AssocImpliesForkEquivRightJoin assoc f (rightAssociateTree tl) (rightAssociateTree tr))

/-- Example usage of AssocFullyRightAssociate -/
theorem Assoc4 {G : Type _} [Magma G] (assoc : Equation4512 G) :
    ∀ x y z w : G, ((x ◇ y) ◇ z) ◇ w = x ◇ (y ◇ (z ◇ w)) :=
  fun x y z w ↦ AssocFullyRightAssociate
    assoc
    (fun | 0 => x | 1 => y | 2 => z | 3 => w : Fin 4 → G)
    (((Lf 0 ⋆ Lf 1) ⋆ Lf 2) ⋆ Lf 3)

inductive FreeSemigroup (α : Type _)
  | Singleton : α → FreeSemigroup α
  | Cons : α → FreeSemigroup α → FreeSemigroup α

local postfix:61 ".+" => FreeSemigroup.Singleton
local infixr:60 " ,+ " => FreeSemigroup.Cons

def semigroupConcat {α : Type _} (s1 s2 : FreeSemigroup α) : FreeSemigroup α :=
  match s1 with
    | a .+        => a ,+ s2
    | a ,+ s1tail => a ,+ (semigroupConcat s1tail s2)

instance (α : Type _) : Magma (FreeSemigroup α) where
  op := semigroupConcat

theorem FreeSgrAssoc {α : Type} : Equation4512 (FreeSemigroup α) :=
  fun ls1 ls2 ls3 ↦ match ls1 with
    | _ .+      => rfl
    | a ,+ ls1' => congrArg (fun ls ↦ a ,+ ls) (FreeSgrAssoc ls1' ls2 ls3)

/- "Flatten" a FreeMagma tree expression into its semigroup representation -/
def freeMagmaToFreeSgr {α : Type _} : MagmaHom (FreeMagma α) (FreeSemigroup α) where
  toFun := fun t ↦ evalInMagma FreeSemigroup.Singleton t
  map_op' := fun s _ ↦ match s with
    | Lf _ => rfl
    | _ ⋆ _ => rfl

local postfix:70 " ↠Sgr " => freeMagmaToFreeSgr.toFun

def evalInSgr {α : Type _} {G : Type _} [Magma G] (f : α → G) (ls : FreeSemigroup α) : G :=
  match ls with
    | a .+ => f a
    | a ,+ lstail => f a ◇ evalInSgr f lstail

def evalInSgrHom {α : Type _} {G : Type _} [Magma G] (assoc : Equation4512 G) (f : α → G) :
    MagmaHom (FreeSemigroup α) G where
  toFun := evalInSgr f
  map_op' := let rec mapper :
    ∀ ls1 ls2 : FreeSemigroup α,
      evalInSgr f (ls1 ◇ ls2) = evalInSgr f ls1 ◇ evalInSgr f ls2 :=
    fun ls1 ls2 ↦ match ls1 with
      | _ .+      => rfl
      | a ,+ ls1' =>
        (congrArg (f a ◇ ·) (mapper ls1' ls2)).trans
        (assoc (f a) (evalInSgr f ls1') (evalInSgr f ls2))
    mapper

def foldFreeSemigroup {G : Type _} [Magma G] (ls : FreeSemigroup G) : G :=
  match ls with
    | a .+        => a
    | a ,+ lstail => a ◇ (foldFreeSemigroup lstail)

/- When evaluating in an associative structure, we may reduce a FreeMagma tree to a FreeSemigroup list -/
theorem AssocImpliesSgrProjFaithful {α : Type _} {G : Type _} [Magma G]
    (assoc : Equation4512 G) (f : α → G) (t : FreeMagma α) :
    evalInMagma f t = evalInSgr f (freeMagmaToFreeSgr t) :=
  match t with
    | Lf a => rfl
    | Lf a ⋆ tr => congrArg (f a ◇ ·) (AssocImpliesSgrProjFaithful assoc f tr)
    | (tl1 ⋆ tl2) ⋆ tr => by
      symm
      trans evalInSgr f (freeMagmaToFreeSgr.toFun (tl1 ⋆ tl2) ◇ freeMagmaToFreeSgr.toFun tr)
      · exact congrArg _ $ freeMagmaToFreeSgr.map_op' _ tr
      trans evalInSgr f ((freeMagmaToFreeSgr.toFun tl1 ◇ freeMagmaToFreeSgr.toFun tl2) ◇ freeMagmaToFreeSgr.toFun tr)
      · exact congrArg (fun s ↦ evalInSgr f (s ◇ tr ↠Sgr)) $ freeMagmaToFreeSgr.map_op' tl1 tl2
      trans
        (evalInSgrHom assoc f).toFun (freeMagmaToFreeSgr.toFun tl1 ◇ freeMagmaToFreeSgr.toFun tl2) ◇
          (evalInSgrHom assoc f).toFun (freeMagmaToFreeSgr.toFun tr)
      · apply (evalInSgrHom assoc f).map_op'
      trans
         ((evalInSgrHom assoc f).toFun (freeMagmaToFreeSgr.toFun tl1) ◇
          (evalInSgrHom assoc f).toFun (freeMagmaToFreeSgr.toFun tl2)) ◇
          evalInSgr f (freeMagmaToFreeSgr.toFun tr)
      · exact congrArg (· ◇ _) $ (evalInSgrHom assoc f).map_op' (tl1 ↠Sgr) (tl2 ↠Sgr)
      symm
      trans (tl1 ⋆ tl2 ⬝ f) ◇ evalInSgr f (freeMagmaToFreeSgr tr)
      · exact congrArg _ (AssocImpliesSgrProjFaithful assoc f tr)
      trans (evalInSgr f (freeMagmaToFreeSgr tl1) ◇ (tl2 ⬝ f)) ◇ evalInSgr f (freeMagmaToFreeSgr tr)
      · exact congrArg (fun s ↦ (s ◇ _) ◇ _) (AssocImpliesSgrProjFaithful assoc f tl1)
      · exact congrArg (fun s ↦ (_ ◇ s) ◇ _) (AssocImpliesSgrProjFaithful assoc f tl2)


def insertSgrSorted {n : Nat} (i : Fin n) (ls : FreeSemigroup (Fin n)) : FreeSemigroup (Fin n) :=
  match ls with
    | j .+        => if i ≤ j then i ,+ j .+ else j ,+ i .+
    | j ,+ lstail => if i ≤ j then i ,+ j ,+ lstail else j ,+ i ,+ lstail

def insertionSortSgr {n : Nat} (ls : FreeSemigroup (Fin n)) : FreeSemigroup (Fin n) :=
  match ls with
    | i .+ => i .+
    | i ,+ lstail => insertSgrSorted i (insertionSortSgr lstail)

theorem CommSgrImpliesInsertSortedFaithful {n : Nat} {G : Type _} [Magma G]
    (assoc : Equation4512 G) (comm : Equation43 G) (f : Fin n → G) :
    ∀ i : Fin n, ∀ ls : FreeSemigroup (Fin n),
      evalInSgr f (insertSgrSorted i ls) = f i ◇ evalInSgr f ls :=
  fun i ls ↦ match ls with
  | j .+ => by
    have eqor := ite_eq_or_eq (i ≤ j) (i ,+ j .+) (j ,+ i .+)
    cases eqor with
    | inl eq1 => exact (congrArg (evalInSgr f) eq1).trans rfl
    | inr eq2 => exact (congrArg (evalInSgr f) eq2).trans (comm _ _)
  | j ,+ lstail => by
    have eqor := ite_eq_or_eq (i ≤ j) (i ,+ j ,+ lstail) (j ,+ i ,+ lstail)
    cases eqor with
    | inl eq1 =>
      exact (congrArg (evalInSgr f) eq1).trans rfl
    | inr eq2 =>
      exact (congrArg (evalInSgr f) eq2).trans ((assoc (f j) (f i) _).trans
        (comm (f j) (f i) ▸ (assoc (f i) (f j) _).symm))

theorem CommSgrImpliesInsertionSortFaithful {n : Nat} {G : Type _} [Magma G]
    (assoc : Equation4512 G) (comm : Equation43 G) (f : Fin n → G) :
    ∀ ls : FreeSemigroup (Fin n), evalInSgr f ls = evalInSgr f (insertionSortSgr ls)
  | _ .+        => rfl
  | i ,+ lstail =>
    (congrArg (f i ◇ ·) (CommSgrImpliesInsertionSortFaithful assoc comm f lstail)).trans
    (CommSgrImpliesInsertSortedFaithful assoc comm f i (insertionSortSgr lstail)).symm

def involutionReduce {α : Type _} [DecidableEq α] (ls : FreeSemigroup α) : FreeSemigroup α :=
  match ls with
  | a .+             => a .+
  | a ,+ b .+        => a ,+ b .+
  | a ,+ b ,+ lstail => if a = b then involutionReduce lstail else a ,+ involutionReduce (b ,+ lstail)

def InvolutiveImpliesInvolutionReduceFaithful {α : Type _} [DecidableEq α] {G : Type _} [Magma G]
    (ls : FreeSemigroup α) (invol : Equation16 G) (f : α → G) :
    evalInSgr f ls = evalInSgr f (involutionReduce ls) :=
  match ls with
  | a .+              => rfl
  | a ,+ b .+         => rfl
  | a ,+ b ,+ lstail  => by
    have eqor := dite_eq_or_eq (P := a = b) (A := fun _ ↦ involutionReduce lstail) (B := fun _ ↦ a ,+ involutionReduce (b ,+ lstail))
    cases eqor with
    | inl eqcase =>
      exact (congrArg (fun s ↦ (f s) ◇ (f b ◇ (evalInSgr f lstail))) eqcase.1).trans
        ((invol (evalInSgr f lstail) (f b)).symm.trans ((InvolutiveImpliesInvolutionReduceFaithful
          lstail invol f).trans (congrArg (evalInSgr f) eqcase.2).symm))
    | inr neqcase =>
      exact ((congrArg (evalInSgr f) neqcase.2).trans
        (congrArg (f a ◇ ·)
          (InvolutiveImpliesInvolutionReduceFaithful (b ,+ lstail) invol f).symm)).symm

def equation1571Reducer {n : Nat} (t : FreeMagma (Fin (n+1))) : FreeSemigroup (Fin (n+1)) :=
  involutionReduce $ insertionSortSgr $ freeMagmaToFreeSgr (t ⋆ (Lf (Fin.last n) ⋆ Lf (Fin.last n)))

theorem AbGrpPow2ImpliesEquation1571ReducerFaithful {n : Nat} {G : Type _} [Magma G]
    (t : FreeMagma (Fin (n+1))) (f : Fin (n+1) → G)
    (assoc : Equation4512 G) (comm : Equation43 G) (invol : Equation16 G) :
    evalInMagma f t = evalInSgr f (equation1571Reducer t) :=
  (((InvolutiveImpliesInvolutionReduceFaithful _ invol f).symm).trans
    (((CommSgrImpliesInsertionSortFaithful assoc comm f _).symm).trans
      (((AssocImpliesSgrProjFaithful assoc f _).symm).trans
        ((comm _ _).trans (((assoc _ _ _).symm).trans ((invol _ (f _)).symm)))))).symm
