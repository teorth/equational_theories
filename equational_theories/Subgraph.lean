import Mathlib.Tactic
import Mathlib.Data.Nat.Defs
import equational_theories.EquationalResult
import equational_theories.Equations.Basic
import equational_theories.FactsSyntax
import equational_theories.FreeSemigroup
import equational_theories.MagmaLaw

/- This is a subproject of the main project to completely describe a small subgraph of the entire
implication graph. The list of equations under consideration can be found at
https://teorth.github.io/equational_theories/blueprint/subgraph-eq.html

Implications here should be placed inside the "Subgraph" namespace.

-/
namespace Subgraph

/- Positive implications -/

@[equational_result]
theorem Equation1_true (G: Type*) [Magma G] : Equation1 G :=
  fun _ ↦ rfl

@[equational_result]
theorem Equation2_implies_Equation3 (G: Type*) [Magma G] (h: Equation2 G) : Equation3 G :=
  fun _ ↦ h ..

@[equational_result]
theorem Equation2_implies_Equation4 (G: Type*) [Magma G] (h: Equation2 G) : Equation4 G :=
  fun _ _ ↦ h ..

@[equational_result]
theorem Equation2_implies_Equation5 (G: Type*) [Magma G] (h: Equation2 G) : Equation5 G :=
  fun _ _ ↦ h ..

@[equational_result]
theorem Equation2_implies_Equation6 (G: Type*) [Magma G] (h: Equation2 G) : Equation6 G :=
  fun _ _ ↦ h ..

@[equational_result]
theorem Equation2_implies_Equation7 (G: Type*) [Magma G] (h: Equation2 G) : Equation7 G :=
  fun _ _ _ ↦ h ..

@[equational_result]
theorem Equation2_implies_Equation8 (G: Type*) [Magma G] (h: Equation2 G) : Equation8 G :=
  fun _ ↦ h ..

@[equational_result]
theorem Equation2_implies_Equation23 (G: Type*) [Magma G] (h: Equation2 G) : Equation23 G :=
  fun _ ↦ h ..

@[equational_result]
theorem Equation2_implies_Equation38 (G: Type*) [Magma G] (h: Equation2 G) : Equation38 G :=
  fun _ _ ↦ h ..

@[equational_result]
theorem Equation2_implies_Equation39 (G: Type*) [Magma G] (h: Equation2 G) : Equation39 G :=
  fun _ _ ↦ h ..

@[equational_result]
theorem Equation2_implies_Equation40 (G: Type*) [Magma G] (h: Equation2 G) : Equation40 G :=
  fun _ _ ↦ h ..

@[equational_result]
theorem Equation2_implies_Equation41 (G: Type*) [Magma G] (h: Equation2 G) : Equation41 G :=
  fun _ _ _ ↦ h ..

@[equational_result]
theorem Equation2_implies_Equation42 (G: Type*) [Magma G] (h: Equation2 G) : Equation42 G :=
  fun _ _ _ ↦ h ..

@[equational_result]
theorem Equation2_implies_Equation43 (G: Type*) [Magma G] (h: Equation2 G) : Equation43 G :=
  fun _ _ ↦ h ..

@[equational_result]
theorem Equation2_implies_Equation46 (G: Type*) [Magma G] (h: Equation2 G) : Equation46 G :=
  fun _ _ _ _ ↦ h ..

@[equational_result]
theorem Equation2_implies_Equation168 (G: Type*) [Magma G] (h: Equation2 G) : Equation168 G :=
  fun _ _ _ ↦ h ..

@[equational_result]
theorem Equation2_implies_Equation387 (G: Type*) [Magma G] (h: Equation2 G) : Equation387 G :=
  fun _ _ ↦ h ..

theorem Equation2_implies_Equation1689 (G: Type*) [Magma G] (h: Equation2 G) : Equation1689 G:=
  fun _ _ _ ↦ h ..

@[equational_result]
theorem Equation2_implies_Equation4512 (G: Type*) [Magma G] (h: Equation2 G) : Equation4512 G :=
  fun _ _ _ ↦ h ..

@[equational_result]
theorem Equation2_implies_Equation4513 (G: Type*) [Magma G] (h: Equation2 G) : Equation4513 G :=
  fun _ _ _ _ ↦ h ..

@[equational_result]
theorem Equation2_implies_Equation4522 (G: Type*) [Magma G] (h: Equation2 G) : Equation4522 G :=
  fun _ _ _ _ _ ↦ h ..

@[equational_result]
theorem Equation2_implies_Equation4582 (G: Type*) [Magma G] (h: Equation2 G) : Equation4582 G :=
  fun _ _ _ _ _ _ ↦ h ..

@[equational_result]
theorem Equation3_implies_Equation8 (G: Type*) [Magma G] (h: Equation3 G) : Equation8 G :=
  fun x ↦ by repeat rw [← h]

@[equational_result]
theorem Equation3_implies_Equation23 (G: Type*) [Magma G] (h: Equation3 G) : Equation23 G :=
  fun x ↦ by repeat rw [← h]

@[equational_result]
theorem Equation4_implies_Equation3 (G: Type*) [Magma G] (h: Equation4 G) : Equation3 G :=
  fun _ ↦ by rw [← h]

@[equational_result]
theorem Equation4_implies_Equation8 (G: Type*) [Magma G] (h: Equation4 G) : Equation8 G :=
  fun _ ↦ h ..

@[equational_result]
theorem Equation4_implies_Equation23 (G: Type*) [Magma G] (h: Equation4 G) : Equation23 G :=
  Equation3_implies_Equation23 G fun _ ↦ h ..

@[equational_result]
theorem Equation4_implies_Equation42 (G: Type*) [Magma G] (h: Equation4 G) : Equation42 G :=
  fun _ _ _ ↦ by repeat rw [← h]

@[equational_result]
theorem Equation4_implies_Equation4522 (G: Type*) [Magma G] (h: Equation4 G) : Equation4522 G :=
  fun _ _ _ _ _ ↦ by repeat rw [← h]

@[equational_result]
theorem Equation5_implies_Equation3 (G: Type*) [Magma G] (h: Equation5 G) : Equation3 G :=
  fun _ ↦ h ..

@[equational_result]
theorem Equation5_implies_Equation8 (G: Type*) [Magma G] (h: Equation5 G) : Equation8 G :=
  fun _  ↦ by repeat rw [← h]

@[equational_result]
theorem Equation5_implies_Equation23 (G: Type*) [Magma G] (h: Equation5 G) : Equation23 G :=
  fun _  ↦ by repeat rw [← h]

@[equational_result]
theorem Equation5_implies_Equation39 (G: Type*) [Magma G] (h: Equation5 G) : Equation39 G :=
  fun _ _ ↦ by repeat rw [← h]

@[equational_result]
theorem Equation5_implies_Equation4512 (G: Type*) [Magma G] (h: Equation5 G) : Equation4512 G :=
  fun _ _ _  ↦ by repeat rw [← h]

@[equational_result]
theorem Equation6_implies_Equation2 (G: Type*) [Magma G] (h: Equation6 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a, ← h]

@[equational_result]
theorem Equation6_implies_Equation3 (G: Type*) [Magma G] (h: Equation6 G) : Equation3 G :=
  fun _ ↦ h ..

@[equational_result]
theorem Equation7_implies_Equation2 (G: Type*) [Magma G] (h: Equation7 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

@[equational_result]
theorem Equation7_implies_Equation3 (G: Type*) [Magma G] (h: Equation7 G) : Equation3 G :=
  fun _ ↦ h ..

@[equational_result]
theorem Equation7_implies_Equation41 (G: Type*) [Magma G] (h: Equation7 G) : Equation41 G :=
  fun _ _ _ ↦ h ..

/-- Dual to Problem A1 from Putnam 2001 -/
@[equational_result]
theorem Equation14_implies_Equation29 (G: Type*) [Magma G] (h: Equation14 G) : Equation29 G :=
  fun x y ↦ (h x (y ◇ x)).trans (congrArg ((y ◇ x) ◇ ·) (h y x).symm)

/-- This implication is Problem A1 from Putnam 2001 -/
@[equational_result]
theorem Equation29_implies_Equation14 (G: Type*) [Magma G] (h: Equation29 G) : Equation14 G :=
  fun x y ↦ (h x (x ◇ y)).trans (congrArg (· ◇ (x ◇ y)) (h y x).symm)

@[equational_result]
theorem Equation38_implies_Equation42 (G: Type*) [Magma G] (h: Equation38 G) : Equation42 G :=
  fun _ _ _ ↦ by rw [← h, h]

@[equational_result]
theorem Equation39_implies_Equation45 (G: Type*) [Magma G] (h: Equation39 G) : Equation45 G :=
  fun _ _ _ ↦ by rw [← h, h]

@[equational_result]
theorem Equation41_implies_Equation39 (G: Type*) [Magma G] (h: Equation41 G) : Equation39 G :=
  fun _ _ ↦ h ..

@[equational_result]
theorem Equation41_implies_Equation40 (G: Type*) [Magma G] (h: Equation41 G) : Equation40 G :=
  fun _ _ ↦ h ..

@[equational_result]
theorem Equation41_implies_Equation46 (G: Type*) [Magma G] (h: Equation41 G) : Equation46 G :=
  fun _ _ _ _ ↦ by rwa [← h, h]

@[equational_result]
theorem Equation42_implies_Equation38 (G: Type*) [Magma G] (h: Equation42 G) : Equation38 G :=
  fun _ _ ↦ h ..

@[equational_result]
theorem Equation45_implies_Equation39 (G: Type*) [Magma G] (h: Equation45 G) : Equation39 G :=
  fun _ _ ↦ h ..

@[equational_result]
theorem Equation46_implies_Equation39 (G: Type*) [Magma G] (h: Equation46 G) : Equation39 G :=
  fun _ _ ↦ h ..

@[equational_result]
theorem Equation46_implies_Equation40 (G: Type*) [Magma G] (h: Equation46 G) : Equation40 G :=
  fun _ _ ↦ h ..

@[equational_result]
theorem Equation46_implies_Equation41 (G: Type*) [Magma G] (h: Equation46 G) : Equation41 G :=
  fun _ _ _ ↦ h ..

@[equational_result]
theorem Equation46_implies_Equation42 (G: Type*) [Magma G] (h: Equation46 G) : Equation42 G :=
  fun _ _ _ ↦ h ..

@[equational_result]
theorem Equation46_implies_Equation387 (G: Type*) [Magma G] (h: Equation46 G) : Equation387 G :=
  fun _ _ ↦ h ..

@[equational_result]
theorem Equation46_implies_Equation4582 (G: Type*) [Magma G] (h: Equation46 G) : Equation4582 G :=
  fun _ _ _ _ _ _ ↦ h ..

/-- This proof is from https://mathoverflow.net/a/450905/766 -/
@[equational_result]
theorem Equation387_implies_Equation43 (G: Type*) [Magma G] (h: Equation387 G) : Equation43 G := by
  have idem (x : G) : (x ◇ x) ◇ (x ◇ x) = (x ◇ x) := by repeat rw [← h]
  have comm (x y : G) : (x ◇ x) ◇ y = y ◇ (x ◇ x) := by rw [← idem, ← h, idem]
  have op_idem (x y : G) : (x ◇ x) ◇ (y ◇ y) = x ◇ y := by repeat rw [← h]
  exact fun _ _ ↦ by rw [← op_idem, comm, op_idem]

/-- The below results for Equation1571 are out of order because early ones are lemmas for later ones -/
@[equational_result]
theorem Equation1571_implies_Equation2662 (G: Type _) [Magma G] (h: Equation1571 G) : Equation2662 G :=
  fun x y ↦ (h x (x ◇ y) (x ◇ y)).trans (congrArg (((x ◇ y) ◇ (x ◇ y)) ◇ ·) (h x x y).symm)

@[equational_result]
theorem Equation1571_implies_Equation40 (G: Type _) [Magma G] (h: Equation1571 G) : Equation40 G := by
  have sqRotate : ∀ x y z : G, (x ◇ y) ◇ (x ◇ y) = (y ◇ z) ◇ (y ◇ z) :=
    fun x y z ↦
      (congrArg (fun w ↦ (x ◇ y) ◇ (x ◇ w)) (Equation1571_implies_Equation2662 G h y z)).trans
        (h ((y ◇ z) ◇ (y ◇ z)) x y).symm
  have sqConstInImage : ∀ x y z w : G, (x ◇ y) ◇ (x ◇ y) = (z ◇ w) ◇ (z ◇ w) :=
    fun x y z w ↦ (sqRotate x y z).trans (sqRotate y z w)
  exact fun x y ↦ h x x x ▸ h y y y ▸ sqConstInImage (x ◇ x) (x ◇ (x ◇ x)) (y ◇ y) (y ◇ (y ◇ y))

@[equational_result]
theorem Equation1571_implies_Equation23 (G: Type _) [Magma G] (h: Equation1571 G) : Equation23 G := by
  refine fun x ↦ (h x (x ◇ x) (x ◇ x)).trans ?_
  rw [← h x x x, ← Equation1571_implies_Equation40 G h x (x ◇ x)]

@[equational_result]
theorem Equation1571_implies_Equation8 (G: Type _) [Magma G] (h: Equation1571 G) : Equation8 G :=
  fun x ↦ (h x x x).trans (((congrArg (· ◇ (x ◇ (x ◇ x))))
    (Equation1571_implies_Equation40 G h x (x ◇ (x ◇ x)))).trans
      (((Equation1571_implies_Equation23 G h (x ◇ (x ◇ x))).symm).trans rfl))

@[equational_result]
theorem Equation1571_implies_Equation16 (G: Type _) [Magma G] (h: Equation1571 G) : Equation16 G :=
  fun x y ↦ ((congrArg (fun w ↦ y ◇ (y ◇ w)) (Equation1571_implies_Equation8 G h x)).trans
    ((Equation1571_implies_Equation40 G h x y ▸ ((congrArg (· ◇ (y ◇ (x ◇ (y ◇ y)))))
      (Equation1571_implies_Equation8 G h y)).trans (h x y (y ◇ y)).symm))).symm

@[equational_result]
theorem Equation1571_implies_Equation43 (G: Type _) [Magma G] (h: Equation1571 G) : Equation43 G := by
  refine fun x y ↦ (h _ (x ◇ x) (x ◇ (x ◇ y))).trans ?_
  rw [← h x x y, ← Equation1571_implies_Equation23 G h x, ← Equation1571_implies_Equation16 G h y x,
    Equation1571_implies_Equation40 G h x y, ← Equation1571_implies_Equation23 G h y]

@[equational_result]
theorem Equation1571_implies_Equation4512 (G: Type _) [Magma G] (h: Equation1571 G) : Equation4512 G := by
  refine fun x y z ↦ (h (x ◇ (y ◇ z)) y x).trans ?_
  rw [Equation1571_implies_Equation43 G h (x ◇ (y ◇ z)) x,
    ← Equation1571_implies_Equation16 G h (y ◇ z) x, ← Equation1571_implies_Equation16 G h z y,
    Equation1571_implies_Equation43 G h y x]

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


namespace Eq1689
abbrev pow3 {G: Type*} [Magma G] (a : G) : G := (a ◇ a) ◇ a
abbrev pow5 {G: Type*} [Magma G] (a : G) : G := ((pow3 a) ◇ a) ◇ a
abbrev f {G: Type*} [Magma G] (a b : G) : G := (a ◇ b) ◇ b
abbrev g {G: Type*} [Magma G] (a b : G) : G := a ◇ ((a ◇ b) ◇ b)

-- Assuming there always exist b such that f a b = a, finish the proof
lemma lem_fixf_implies_eq2 {G: Type*} [Magma G] (h: Equation1689 G)
    (hfixf: ∀ b : G, ∃ c : G, f b c = b) : Equation2 G := by
  have fproj (a b : G) : f a b = b := by
    obtain ⟨c, hfbc⟩ := hfixf b
    unfold f at hfbc
    exact (hfbc ▸ (h b a c)).symm
  have eq30 (a b c : G) : a = (b ◇ a) ◇ c := by rw [← fproj a c, ← h]
  have eq6 (a b : G) : a = b ◇ b := by rw [eq30 a, ← eq30 b a]
  intro a b ; rw [eq6 a b, ← eq6]

lemma lem_1 {G: Type*} [Magma G] (h: Equation1689 G) :
    ∀ a b c : G, a ◇ (f (f a b) c) = f a b := by
  intro a b c
  nth_rewrite 1 [h a a]
  exact (h ..).symm

lemma lem_2 {G: Type*} [Magma G] (h: Equation1689 G) :
    ∀ a b c : G, a ◇ (g b c) = f a b := by
  intro a b c
  nth_rewrite 1 [g, h b]
  exact lem_1 h ..

lemma lem_fixf {G: Type*} [Magma G] (h: Equation1689 G) :
    ∀ a : G, ∃ b : G, f a b = a := by
  intro a
  have h1 : pow3 a = a ◇ pow5 a := (lem_1 h ..).symm
  have h2 : g (pow3 a) a = f a (pow5 a) := congrArg (· ◇ _) h1
  have h3 : g a (pow5 a) = f a (pow3 a) := by rw [← lem_2 h, h2]
  have h4 : a ◇ (g a (pow5 a)) = pow3 a := by rw [lem_2 h]
  use (g a (pow5 a))
  rw [f, h4, h3, ← h]

end Eq1689

/-- This result was first obtained by Kisielewicz in 1997 via computer assistance. -/
@[equational_result]
theorem Equation1689_implies_Equation2 (G: Type*) [Magma G] (h: Equation1689 G) : Equation2 G :=
  Eq1689.lem_fixf_implies_eq2 h (Eq1689.lem_fixf h)

/-- Putnam 1978, problem A4, part (b) -/
@[equational_result]
theorem Equation3744_implies_Equation381 (G : Type*) [Magma G] (h: Equation3744 G) : Equation381 G :=
  fun x y z ↦
    (h x y z y).trans $
    (congrArg (· ◇ (y ◇ y)) (h x z z x)).trans
    (h (x ◇ z) y (x ◇ z) y).symm

/-- Putnam 1978, problem A4, part (a) -/
@[equational_result]
theorem Equation3744_implies_Equation3722 (G: Type*) [Magma G] (h: Equation3744 G) : Equation3722 G :=
  fun _ _ ↦ h ..

@[equational_result]
theorem Equation4513_implies_Equation4512 (G: Type*) [Magma G] (h: Equation4513 G) : Equation4512 G :=
  fun _ _ _ ↦ h ..

@[equational_result]
theorem Equation4522_implies_Equation4513 (G: Type*) [Magma G] (h: Equation4522 G) : Equation4513 G :=
  fun _ _ _ _ ↦ h ..

@[equational_result]
theorem Equation4582_implies_Equation4522 (G: Type*) [Magma G] (h: Equation4582 G) : Equation4522 G :=
  fun _ _ _ _ _ ↦ h ..

@[equational_result]
theorem Equation4582_implies_Equation4564 (G: Type*) [Magma G] (h: Equation4582 G) : Equation4564 G :=
  fun _ _ _ _ ↦ h ..

@[equational_result]
theorem Equation4582_implies_Equation4579 (G: Type*) [Magma G] (h: Equation4582 G) : Equation4579 G :=
  fun _ _ _ _ _ ↦ h ..

@[equational_result]
theorem Equation953_implies_Equation2 (G : Type _) [Magma G] (h: Equation953 G) : Equation2 G := by
  intro x y
  have znx (z : G) : z ◇ ((x ◇ x) ◇ (x ◇ x)) = x := (h x z x).symm
  have hzzi := h x x (x ◇ x)
  have hyzi := h y x (x ◇ x)
  rw [znx] at hzzi hyzi
  exact hzzi.trans hyzi.symm

/- Obtained with lean-egg -/
@[equational_result]
theorem Equation14_implies_Equation23 (G: Type*) [Magma G] (h: Equation14 G) : Equation23 G :=
  fun x ↦
    calc x
     _ = (x ◇ x) ◇ (x ◇ (x ◇ x)) := h x (x ◇ x)
     _ = (x ◇ x) ◇ x := by rw [← h x x]

@[equational_result]
theorem Equation14_implies_Equation8 (G: Type*) [Magma G] (h: Equation14 G) : Equation8 G :=
  fun _ ↦ h ..

@[equational_result]
theorem Equation2_implies_Equation14 (G: Type*) [Magma G] (h: Equation2 G) : Equation14 G :=
  fun _ _ ↦ h ..

@[equational_result]
theorem Equation2_implies_Equation381 (G: Type _) [Magma G] (h: Equation2 G) : Equation381 G :=
  fun _ _ _ ↦ h ..

@[equational_result]
theorem Equation2_implies_Equation3722 (G: Type _) [Magma G] (h: Equation2 G) : Equation3722 G :=
  fun _ _ ↦ h ..

@[equational_result]
theorem Equation2_implies_Equation3744 (G: Type _) [Magma G] (h: Equation2 G) : Equation3744 G :=
  fun _ _ _ _ ↦ h ..

@[equational_result]
theorem Equation2_implies_Equation5093 (G: Type _) [Magma G] (h: Equation2 G) : Equation5093 G :=
  fun _ _ _ ↦ h ..

@[equational_result]
theorem Equation2_implies_Equation374794 (G: Type _) [Magma G] (h: Equation2 G) : Equation374794 G :=
  fun _ _ _ ↦ h ..

@[equational_result]
theorem Equation3_implies_Equation3722 (G: Type _) [Magma G] (h: Equation3 G) : Equation3722 G :=
  fun _ _ ↦ h _

@[equational_result]
theorem Equation4_implies_Equation381 (G: Type _) [Magma G] (h: Equation4 G) : Equation381 G :=
  fun x y z ↦ by nth_rw 1 [h x z]

@[equational_result]
theorem Equation4_implies_Equation3722 (G: Type _) [Magma G] (h: Equation4 G) : Equation3722 G :=
  fun _ _ ↦ h ..

@[equational_result]
theorem Equation4_implies_Equation3744 (G: Type _) [Magma G] (h: Equation4 G) : Equation3744 G :=
  fun x y z w ↦
    calc x ◇ y
    _ = (x ◇ z) ◇ y := by nth_rw 1 [h x z]
    _ = x ◇ z := (h ..).symm
    _ = (x ◇ z) ◇ (w ◇ y) := h ..

@[equational_result]
theorem Equation5_implies_Equation381 (G: Type _) [Magma G] (h: Equation5 G) : Equation381 G :=
  fun x y z ↦
    calc x ◇ y
    _ = y := (h y x).symm
    _ = (x ◇ z) ◇ y := h y (x ◇ z)

@[equational_result]
theorem Equation5_implies_Equation3722 (G: Type _) [Magma G] (h: Equation5 G) : Equation3722 G :=
  fun _ _ ↦ h ..

@[equational_result]
theorem Equation5_implies_Equation3744 (G: Type _) [Magma G] (h: Equation5 G) : Equation3744 G :=
  fun x y z w ↦
    calc x ◇ y
    _ = y := (h y x).symm
    _ = (x ◇ z) ◇ y := (h y (x ◇ z))
    _ = (x ◇ z) ◇ (w ◇ y) := by nth_rw 1 [h y w]

@[equational_result]
theorem Equation5_implies_Equation4564 (G: Type _) [Magma G] (h: Equation5 G) : Equation4564 G :=
  fun x y z w ↦
    calc x ◇ (y ◇ z)
    _ = y ◇ (x ◇ (y ◇ z)) := (h ..)
    _ = (w ◇ y) ◇ (x ◇ (y ◇ z)) := by nth_rw 1 [h y w]
    _ = (w ◇ y) ◇ (x ◇ z) := by nth_rw 2 [h z y]
    _ = (w ◇ y) ◇ z := by rw [← h z x]

@[equational_result]
theorem Equation5_implies_Equation4579 (G: Type _) [Magma G] (h: Equation5 G) : Equation4579 G :=
  fun x y z w u ↦
    calc x ◇ (y ◇ z)
    _ = z := h z y ▸ (h z x).symm
    _ = (w ◇ u) ◇ z := h ..

@[equational_result]
theorem Equation39_implies_Equation381 (G: Type _) [Magma G] (h: Equation39 G) : Equation381 G :=
  fun x y z ↦ (h y x).symm ▸ h y (x ◇ z)

@[equational_result]
theorem Equation41_implies_Equation381 (G: Type _) [Magma G] (h: Equation41 G) : Equation381 G :=
  fun x y z ↦ (h x x y).symm ▸ h x (x ◇ z) y

@[equational_result]
theorem Equation41_implies_Equation3722 (G: Type _) [Magma G] (h: Equation41 G) : Equation3722 G :=
  fun _ _ ↦ (h ..).symm

@[equational_result]
theorem Equation41_implies_Equation3744 (G: Type _) [Magma G] (h: Equation41 G) : Equation3744 G :=
  fun x y z w ↦ (h x x y).symm ▸ h x (x ◇ z) (w ◇ y)

@[equational_result]
theorem Equation45_implies_Equation381 (G: Type _) [Magma G] (h: Equation45 G) : Equation381 G :=
  fun _ _ _ ↦ (h ..).symm

@[equational_result]
theorem Equation46_implies_Equation381 (G: Type _) [Magma G] (h: Equation46 G) : Equation381 G :=
  fun _ _ _ ↦ (h ..).symm

@[equational_result]
theorem Equation46_implies_Equation3722 (G: Type _) [Magma G] (h: Equation46 G) : Equation3722 G :=
  fun _ _ ↦ (h ..).symm

@[equational_result]
theorem Equation46_implies_Equation3744 (G: Type _) [Magma G] (h: Equation46 G) : Equation3744 G :=
  fun _ _ _ _ ↦ (h ..).symm

@[equational_result]
theorem Equation3744_implies_Equation4512 (G: Type _) [Magma G] (h: Equation3744 G) : Equation4512 G :=
  fun x y z ↦
    calc x ◇ (y ◇ z)
    _ = (x ◇ y) ◇ (x ◇ (y ◇ z)) := h ..
    _ = ((x ◇ y) ◇ (x ◇ y)) ◇ (x ◇ (y ◇ z)) := by nth_rw 1 [h x y y x]
    _ = (x ◇ y) ◇ (y ◇ z) := (h ..).symm
    _ = ((x ◇ y) ◇ x) ◇ ((y ◇ x) ◇ (y ◇ z)) := h ..
    _ = ((x ◇ y) ◇ x) ◇ (y ◇ z) := by nth_rw 1 [← h y z x y]
    _ = (x ◇ y) ◇ z := (h ..).symm

@[equational_result]
theorem Equation4564_implies_Equation4512 (G: Type _) [Magma G] (h: Equation4564 G) : Equation4512 G :=
  fun _ _ _ ↦ h ..

@[equational_result]
theorem Equation4579_implies_Equation4512 (G: Type _) [Magma G] (h: Equation4579 G) : Equation4512 G :=
  fun _ _ _ ↦ h ..

@[equational_result]
theorem Equation4579_implies_Equation4564 (G: Type _) [Magma G] (h: Equation4579 G) : Equation4564 G :=
  fun _ _ _ _ ↦ h ..

/-- The Bol loop and Moufang loop identities are all weakenings of t-/
@[equational_result]
theorem Equation4512_implies_Equation910472 (G: Type _) [Magma G] (h: Equation4512 G) : Equation910472 G :=
  fun _ _ _ ↦ by simp only [h]

@[equational_result]
theorem Equation4512_implies_Equation930594 (G: Type _) [Magma G] (h: Equation4512 G) : Equation930594 G :=
  fun _ _ _ ↦ by simp only [h]

@[equational_result]
theorem Equation4512_implies_Equation914612 (G: Type _) [Magma G] (h: Equation4512 G) : Equation914612 G :=
  fun _ _ _ ↦ by simp only [h]

@[equational_result]
theorem Equation4512_implies_Equation916037 (G: Type _) [Magma G] (h: Equation4512 G) : Equation916037 G :=
  fun _ _ _ ↦ by simp only [h]

@[equational_result]
theorem Equation4512_implies_Equation936498 (G: Type _) [Magma G] (h: Equation4512 G) : Equation936498 G :=
  fun _ _ _ ↦ by simp only [h]

@[equational_result]
theorem Equation4512_implies_Equation921941 (G: Type _) [Magma G] (h: Equation4512 G) : Equation921941 G :=
  fun _ _ _ ↦ by simp only [h]

/- Counterexamples -/

@[equational_result]
theorem Equation3_not_implies_Equation39 : ∃ (G: Type) (_: Magma G), Equation3 G ∧ ¬ Equation39 G :=
  ⟨Fin 3, ⟨fun x y ↦ 2 * x - y⟩, by decide⟩

@[equational_result]
theorem Equation3_not_implies_Equation42 : ∃ (G: Type) (_: Magma G), Equation3 G ∧ ¬ Equation42 G :=
  ⟨ℕ, ⟨fun _ y ↦ y⟩, fun _ ↦ rfl, fun h ↦ by simpa using h 0 1 2⟩

@[equational_result]
theorem Equation3_not_implies_Equation4512 : ∃ (G: Type) (_: Magma G), Equation3 G ∧ ¬ Equation4512 G :=
  ⟨ℕ, ⟨fun x y ↦ if x = y then x else x + 1⟩, fun _ ↦ by simp, fun h ↦ by simpa using h 1 2 3⟩

@[equational_result]
theorem Equation4_not_implies_Equation39 : ∃ (G: Type) (_: Magma G), Equation4 G ∧ ¬ Equation39 G :=
  ⟨Fin 2, ⟨fun x _ ↦ x⟩, by decide⟩

-- The 2 element magma that satisfies 4 does not satisfy 40.
@[equational_result]
theorem Equation4_not_implies_Equation40 : ∃ (G: Type) (_: Magma G), Equation4 G ∧ ¬ Equation40 G :=
  ⟨Fin 2, ⟨fun x _ ↦ x⟩, by decide⟩

@[equational_result]
theorem Equation4_not_implies_Equation43 : ∃ (G: Type) (_: Magma G), Equation4 G ∧ ¬ Equation43 G :=
  ⟨ℕ, ⟨fun x _ ↦ x⟩, fun _ _ ↦ rfl, fun h ↦ by simpa using h 1 0⟩

@[equational_result]
theorem Equation4_not_implies_Equation4582 : ∃ (G: Type) (_: Magma G), Equation4 G ∧ ¬ Equation4582 G :=
  ⟨ℕ, ⟨fun x _ ↦ x⟩, fun _ _ ↦ rfl, fun h ↦ by simpa using h 0 0 0 1 0 0⟩

-- The magma with 2 elements a and b which satisfies equation 5 serves as counterexamples here. For
-- 43, a * b = b, but b * a = a. For 4513, a * (a * a) = a, but (a * a) * b = b.
--
-- We can use the `Facts` syntax to state multiple anti-implications from the same magma in one theorem

@[equational_result]
theorem Equation5_not_implies_Equation42 : ∃ (G: Type) (_: Magma G), Facts G [5] [42, 43, 4513] := by
  refine ⟨Fin 2, ⟨fun _ x ↦ x⟩, fun _ ↦ ?_, fun h ↦ ?_, fun h ↦ ?_, fun h ↦ ?_⟩
  · simp [Equation5]
  · simpa using h 0 1 0
  · simpa using h 0 1
  · simpa using h 0 0 0 1

@[equational_result]
theorem Equation8_not_implies_Equation3 : ∃ (G : Type) (_ : Magma G), Equation8 G ∧ ¬ Equation3 G := by
  simp only [not_forall]
  exact ⟨Fin 2, ⟨(· + ·)⟩, by decide, 1, one_ne_zero⟩

@[equational_result]
theorem Equation23_not_implies_Equation3 : ∃ (G : Type) (_ : Magma G), Equation23 G ∧ ¬ Equation3 G := by
  simp only [not_forall]
  exact ⟨Fin 2, ⟨(· + ·)⟩, by decide, 1, one_ne_zero⟩

@[equational_result]
theorem Equation23_not_implies_Equation14 : ∃ (G: Type) (_ : Magma G), Equation23 G ∧ ¬ Equation14 G :=
  ⟨Fin 2, { op := fun x y ↦ x * y }, by decide⟩

@[equational_result]
theorem Equation38_not_implies_Equation23 : ∃ (G : Type) (_ : Magma G), Equation38 G ∧ ¬ Equation23 G := by
  simp only [not_forall]
  exact ⟨ℕ, ⟨fun x _ ↦ x + 1⟩, fun _ _ ↦ rfl, 0, Nat.zero_ne_add_one _⟩

@[equational_result]
theorem Equation23_not_implies_Equation39 : ∃ (G: Type) (_: Magma G), Equation23 G ∧ ¬ Equation39 G :=
  ⟨Fin 2, ⟨fun x _ ↦ x⟩, by decide⟩

@[equational_result]
theorem Equation39_not_implies_Equation8 : ∃ (G : Type) (_ : Magma G), Equation39 G ∧ ¬ Equation8 G := by
  simp only [not_forall]
  refine ⟨ℕ, ⟨fun _ y ↦ y + 1⟩, fun _ _ ↦ rfl, 0, ?_⟩
  simp only [zero_add, Nat.reduceAdd, OfNat.zero_ne_ofNat, not_false_eq_true]

@[equational_result]
theorem Equation39_not_implies_Equation23 : ∃ (G : Type) (_ : Magma G), Equation39 G ∧ ¬ Equation23 G := by
  simp only [not_forall]
  exact ⟨ℕ, ⟨fun _ _ ↦ _ + 1⟩, fun _ _ ↦ rfl, 0, Nat.zero_ne_add_one 0⟩

@[equational_result]
theorem Equation39_not_implies_Equation40 : ∃ (G: Type) (_: Magma G), Equation39 G ∧ ¬ Equation40 G :=
  ⟨Fin 2, ⟨fun _ ↦ (· + 1)⟩, by decide⟩

@[equational_result]
theorem Equation39_not_implies_Equation168 : ∃ (G : Type) (_ : Magma G), Equation39 G ∧ ¬ Equation168 G := by
  simp only [not_forall]
  exact ⟨ℕ, ⟨fun _ y ↦ y⟩, (fun _ _ ↦ rfl), 0, 0, 1, nofun⟩

@[equational_result]
theorem Equation39_not_implies_Equation4512 : ∃ (G: Type) (_: Magma G), Equation39 G ∧ ¬ Equation4512 G :=
  ⟨Fin 2, ⟨fun _ ↦ (· + 1)⟩, by decide⟩

@[equational_result]
theorem Equation39_not_implies_Equation4513 : ∃ (G: Type) (_: Magma G), Equation39 G ∧ ¬ Equation4513 G :=
  ⟨Fin 2, ⟨fun _ ↦ (· + 1)⟩, by decide⟩

@[equational_result]
theorem Equation39_not_implies_Equation4522 : ∃ (G: Type) (_: Magma G), Equation39 G ∧ ¬ Equation4522 G :=
  ⟨Fin 2, ⟨fun _ ↦ (· + 1)⟩, by decide⟩

@[equational_result]
theorem Equation39_not_implies_Equation4564 : ∃ (G: Type) (_: Magma G), Equation39 G ∧ ¬ Equation4564 G :=
  ⟨Fin 2, ⟨fun _ ↦ (· + 1)⟩, by decide⟩

@[equational_result]
theorem Equation39_not_implies_Equation4579 : ∃ (G: Type) (_: Magma G), Equation39 G ∧ ¬ Equation4579 G :=
  ⟨Fin 2, ⟨fun _ ↦ (· + 1)⟩, by decide⟩

@[equational_result]
theorem Equation39_not_implies_Equation4582 : ∃ (G: Type) (_: Magma G), Equation39 G ∧ ¬ Equation4582 G :=
  ⟨Fin 2, ⟨fun _ ↦ (· + 1)⟩, by decide⟩

@[equational_result]
theorem Equation40_not_implies_Equation3 : ∃ (G: Type) (_: Magma G), Equation40 G ∧ ¬ Equation3 G := by
  exact ⟨Bool, ⟨fun x y ↦ ¬ x ∨ y⟩, by decide⟩

@[equational_result]
theorem Equation40_not_implies_Equation39 : ∃ (G: Type) (_: Magma G), Equation40 G ∧ ¬ Equation39 G :=
  ⟨Fin 2, ⟨fun x y ↦ x - y⟩, by decide⟩

@[equational_result]
theorem Equation40_not_implies_Equation42 : ∃ (G: Type) (_: Magma G), Equation40 G ∧ ¬ Equation42 G := by
  exact ⟨Bool, ⟨fun x y ↦ ¬ x ∨ y⟩, by decide⟩

@[equational_result]
theorem Equation40_not_implies_Equation43 : ∃ (G: Type) (_: Magma G), Equation40 G ∧ ¬ Equation43 G := by
  exact ⟨Bool, ⟨fun x y ↦ ¬ x ∨ y⟩, by decide⟩

@[equational_result]
theorem Equation40_not_implies_Equation4512 : ∃ (G: Type) (_: Magma G), Equation40 G ∧ ¬ Equation4512 G := by
  exact ⟨Bool, ⟨fun x y ↦ ¬ x ∨ y⟩, by decide⟩

@[equational_result]
theorem Equation42_not_implies_Equation43 : ∃ (G: Type) (_: Magma G), Equation42 G ∧ ¬ Equation43 G :=
  ⟨ℕ, ⟨fun x _ ↦ x⟩, fun _ _ _ ↦ rfl, fun h ↦ by simpa using h 0 1⟩

@[equational_result]
theorem Equation42_not_implies_Equation4512 : ∃ (G: Type) (_: Magma G), Equation42 G ∧ ¬ Equation4512 G :=
  ⟨ℕ, ⟨fun x _ ↦ x + 1⟩, fun _ _ _ ↦ rfl, fun h ↦ by simpa using h 0 0 0⟩

@[equational_result]
theorem Equation43_not_implies_Equation3 : ∃ (G: Type) (_: Magma G), Equation43 G ∧ ¬ Equation3 G :=
  ⟨ℕ, ⟨fun x y ↦ x + y⟩, fun _ _ ↦ Nat.add_comm _ _, fun h ↦ by simpa using h 1⟩

@[equational_result]
theorem Equation43_not_implies_Equation39 : ∃ (G: Type) (_: Magma G), Equation43 G ∧ ¬ Equation3 G :=
  ⟨ℕ, ⟨fun x y ↦ x + y⟩, fun _ _ ↦ Nat.add_comm _ _, fun h ↦ by simpa using h 1⟩

@[equational_result]
theorem Equation43_not_implies_Equation42 : ∃ (G: Type) (_: Magma G), Equation43 G ∧ ¬ Equation42 G :=
  ⟨ℕ, ⟨fun x y ↦ x + y⟩, fun _ _ ↦ Nat.add_comm _ _, fun h ↦ by simpa using h 0 0 1⟩

@[equational_result]
theorem Equation43_not_implies_Equation387 : ∃ (G: Type) (_: Magma G), Equation43 G ∧ ¬ Equation387 G :=
  ⟨ℕ, ⟨fun x y ↦ x + y⟩, fun _ _ ↦ Nat.add_comm _ _, fun h ↦ by simpa using h 0 1⟩

@[equational_result]
theorem Equation43_not_implies_Equation4512 : ∃ (G: Type) (_: Magma G), Equation43 G ∧ ¬ Equation4512 G :=
  ⟨ℕ, ⟨fun x y ↦ x * y + 1⟩, fun _ _ ↦ by ring_nf, fun h ↦ by simpa using h 0 0 1⟩

@[equational_result]
theorem Equation46_not_implies_Equation3 : ∃ (G: Type) (_: Magma G), Equation46 G ∧ ¬ Equation3 G :=
  ⟨ℕ, ⟨0⟩, fun _ _ _ _ ↦ rfl, fun h ↦ by simpa using h 1⟩

@[equational_result]
theorem Equation46_not_implies_Equation4 : ∃ (G: Type) (_: Magma G), Equation46 G ∧ ¬ Equation4 G :=
  ⟨ℕ, ⟨0⟩, fun _ _ _ _ ↦ rfl, fun h ↦ by simpa using h 1⟩

@[equational_result]
theorem Equation168_not_implies_Equation8 : ∃ (G : Type) (_ : Magma G), Equation168 G ∧ ¬ Equation8 G :=
  ⟨Bool × Bool, ⟨fun x y ↦ ⟨x.snd, y.fst⟩⟩, fun _ _ _ ↦ rfl, of_decide_eq_false rfl⟩

@[equational_result]
theorem Equation168_not_implies_Equation23 : ∃ (G : Type) (_ : Magma G), Equation168 G ∧ ¬ Equation23 G :=
  ⟨Bool × Bool, ⟨fun x y ↦ ⟨x.snd, y.fst⟩⟩, fun _ _ _ ↦ rfl, of_decide_eq_false rfl⟩

@[equational_result]
theorem Equation168_not_implies_Equation39 : ∃ (G : Type) (_ : Magma G), Equation168 G ∧ ¬ Equation39 G :=
  ⟨Bool × Bool, ⟨fun x y ↦ ⟨x.snd, y.fst⟩⟩, by decide⟩

@[equational_result]
theorem Equation387_not_implies_Equation39 : ∃ (G: Type) (_: Magma G), Equation387 G ∧ ¬ Equation39 G :=
  ⟨Bool, ⟨fun x y ↦ x && y⟩, by decide⟩

-- The "and" magma on the two element set of booleans satisfies 387, but does not satisfy 40.
@[equational_result]
theorem Equation387_not_implies_Equation40 : ∃ (G: Type) (_: Magma G), Equation387 G ∧ ¬ Equation40 G := by
  exact ⟨Bool, ⟨fun x y ↦ x && y⟩, fun _ _ ↦ by simp [Bool.and_comm], of_decide_eq_false rfl⟩

@[equational_result]
theorem Equation387_not_implies_Equation42 : ∃ (G: Type) (_: Magma G), Equation387 G ∧ ¬ Equation42 G := by
  exact ⟨Bool, ⟨fun x y ↦ x || y⟩, fun _ _ ↦ by simp [Bool.or_comm], of_decide_eq_false rfl⟩

@[equational_result]
theorem Equation387_not_implies_Equation4512 : ∃ (G: Type) (_: Magma G), Equation387 G ∧ ¬ Equation4512 G :=
  ⟨ℝ, ⟨fun x y ↦ (x + y) / 2⟩, fun _ _ ↦ by ring_nf, fun h ↦ by specialize h 0 0 1; field_simp at h⟩

@[equational_result]
theorem Equation4512_not_implies_Equation42 : ∃ (G: Type) (_: Magma G), Equation4512 G ∧ ¬ Equation42 G :=
  ⟨ℕ, ⟨fun x y ↦ x + y⟩, fun _ _ _ ↦ by abel_nf, fun h ↦ by simpa using h 0 0 1⟩

@[equational_result]
theorem Equation4512_not_implies_Equation4513 : ∃ (G: Type) (_: Magma G), Equation4512 G ∧ ¬ Equation4513 G :=
  ⟨ℕ, ⟨fun x y ↦ x + y⟩, fun _ _ _ ↦ by abel_nf, fun h ↦ by simpa using h 0 0 0 1⟩

@[equational_result]
theorem Equation4513_not_implies_Equation4522 : ∃ (G: Type) (_: Magma G), Equation4513 G ∧ ¬ Equation4522 G := by
  refine ⟨ℕ, ⟨fun x y ↦ if x = 0 then (if y ≤ 2 then 1 else 2) else x⟩, fun _ _ _ _ ↦ ?_, fun h ↦ ?_⟩
  · dsimp; split_ifs <;> simp_all
  · simpa using h 0 0 0 3 3

-- use "saturating addition" on the set {1, 2, 3}, where we add in the normal way but cap the result at 3 (x*y = min(3, x+y)).

inductive Th
  | t1 : Th
  | t2 : Th
  | t3 : Th

def add : Th → Th → Th
| Th.t1, Th.t1 => Th.t2
| Th.t1, Th.t2 => Th.t3
| Th.t1, Th.t3 => Th.t3
| Th.t2, Th.t1 => Th.t3
| Th.t2, Th.t2 => Th.t3
| Th.t2, Th.t3 => Th.t3
| Th.t3, _ => Th.t3

theorem add3 (a b c : Th) : add (add a b) c = Th.t3 := by
  cases a <;> cases b <;> cases c <;> trivial

theorem add3_ (a b c : Th) : add a (add b c) = Th.t3 := by
  cases a <;> cases b <;> cases c <;> trivial

@[equational_result]
theorem Equation4582_not_implies_Equation39 : ∃ (G: Type) (_: Magma G), Equation4582 G ∧ ¬ Equation39 G := by
  refine ⟨ℕ, ⟨fun x y ↦ if x = 1 ∧ y = 2 then 3 else 4⟩, fun _ _ _ _ _ _ ↦ ?_, fun h ↦ ?_⟩
  · dsimp; split_ifs <;> simp_all
  · simpa using h 2 1

@[equational_result]
theorem Equation4582_not_implies_Equation40 : ∃ (G: Type) (_: Magma G), Equation4582 G ∧ ¬ Equation40 G := by
  let hG : Magma Th := { op := fun x y ↦ add x y}
  have hh : Equation4582 Th := fun x y z w u v ↦
    calc
      add x (add y z) = Th.t3 := by rw [add3_ x y z];
      _ = add (add w u) v := by rw [add3 w u v]
  exact ⟨Th, hG, hh, fun h ↦ absurd (h Th.t1 Th.t2) (fun hh ↦ by cases hh)⟩

@[equational_result]
theorem Equation4582_not_implies_Equation42 : ∃ (G: Type) (_: Magma G), Equation4582 G ∧ ¬ Equation42 G := by
  refine ⟨ℕ, ⟨fun x y ↦ if x = 0 ∧ y = 0 then 1 else 2⟩, fun _ _ _ _ _ _ ↦ ?_, fun h ↦ ?_⟩
  · dsimp; split_ifs <;> simp_all
  · simpa using h 0 0 1

@[equational_result]
theorem Equation4582_not_implies_Equation43 : ∃ (G: Type) (_: Magma G), Equation4582 G ∧ ¬ Equation43 G := by
  refine ⟨ℕ, ⟨fun x y ↦ if x = 1 ∧ y = 2 then 3 else 4⟩, fun _ _ _ _ _ _ ↦ ?_, fun h ↦ ?_⟩
  · dsimp; split_ifs <;> simp_all
  · simpa using h 1 2

@[equational_result]
theorem Equation4582_not_implies_Equation46 : ∃ (G: Type) (_: Magma G), Equation4582 G ∧ ¬ Equation46 G := by
  refine ⟨Fin 3, ⟨fun x y ↦ if x = 2 ∧ y = 2 then 1 else 0⟩, fun _ _ _ _ _ _ ↦ ?_, fun h ↦ ?_⟩
  · dsimp; split_ifs <;> simp_all
  · simpa using h 0 0 2 2

@[equational_result]
theorem Equation43_not_implies_Equation910472 : ∃ (G: Type) (_: Magma G), Equation43 G ∧ ¬ Equation910472 G :=
  ⟨Fin 3, ⟨fun x y ↦ 2 * x - y⟩, by decide⟩

@[equational_result]
theorem Equation3_not_implies_Equation910472 : ∃ (G: Type) (_: Magma G), Equation3 G ∧ ¬ Equation910472 G :=
  ⟨Fin 3, ⟨fun x y ↦ 2 * x - y⟩, by decide⟩

@[equational_result]
theorem Equation43_not_implies_Equation930594 : ∃ (G: Type) (_: Magma G), Equation43 G ∧ ¬ Equation930594 G :=
  ⟨Fin 3, ⟨fun x y ↦ 2 * x - y⟩, by decide⟩

@[equational_result]
theorem Equation3_not_implies_Equation930594 : ∃ (G: Type) (_: Magma G), Equation3 G ∧ ¬ Equation930594 G :=
  ⟨Fin 3, ⟨fun x y ↦ 2 * x - y⟩, by decide⟩

@[equational_result]
theorem Equation43_not_implies_Equation914612 : ∃ (G: Type) (_: Magma G), Equation43 G ∧ ¬ Equation914612 G :=
  ⟨Fin 3, ⟨fun x y ↦ 2 * x - y⟩, by decide⟩

@[equational_result]
theorem Equation3_not_implies_Equation914612 : ∃ (G: Type) (_: Magma G), Equation3 G ∧ ¬ Equation914612 G :=
  ⟨Fin 3, ⟨fun x y ↦ 2 * x - y⟩, by decide⟩

@[equational_result]
theorem Equation43_not_implies_Equation916037 : ∃ (G: Type) (_: Magma G), Equation43 G ∧ ¬ Equation916037 G :=
  ⟨Fin 3, ⟨fun x y ↦ 2 * x - y⟩, by decide⟩

@[equational_result]
theorem Equation3_not_implies_Equation916037 : ∃ (G: Type) (_: Magma G), Equation3 G ∧ ¬ Equation916037 G :=
  ⟨Fin 3, ⟨fun x y ↦ 2 * x - y⟩, by decide⟩

@[equational_result]
theorem Equation43_not_implies_Equation936498 : ∃ (G: Type) (_: Magma G), Equation43 G ∧ ¬ Equation936498 G :=
  ⟨Fin 3, ⟨fun x y ↦ 2 * x - y⟩, by decide⟩

@[equational_result]
theorem Equation3_not_implies_Equation936498 : ∃ (G: Type) (_: Magma G), Equation3 G ∧ ¬ Equation936498 G :=
  ⟨Fin 3, ⟨fun x y ↦ 2 * x - y⟩, by decide⟩

@[equational_result]
theorem Equation3_not_implies_Equation921941 : ∃ (G: Type) (_: Magma G), Equation3 G ∧ ¬ Equation921941 G :=
  ⟨Fin 3, ⟨fun x y ↦ 2 * x - y⟩, by decide⟩

@[equational_result]
theorem Equation43_not_implies_Equation921941 : ∃ (G: Type) (_: Magma G), Equation43 G ∧ ¬ Equation921941 G :=
  ⟨Fin 3, ⟨fun x y ↦ 2 * x - y⟩, by decide⟩

end Subgraph
