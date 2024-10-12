/-
  Give a streamlined construction of Knuth's nonnatural central groupoid
  A2 and prove it isomorphic to a FinOp table.

  Settle a bunch of anti-implications of the form 168=>X using the latter.

  Construction based on Section 5 of
    Donald E. Knuth, Notes on central groupoids,
    Journal of Combinatorial Theory, Volume 8, Issue 4, 1970,
    https://doi.org/10.1016/S0021-9800(70)80032-1

  There is a construction of other central groupoids in progress, which
  will eventually resolve all remaining implications from 168.
-/

import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang
import equational_theories.Homomorphisms
import equational_theories.SmallMagmas

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

private def ofMatrix {n : Nat} [Inhabited (Fin n)]
  (table : Array (Array (Fin n))) (x y : Fin n) : Fin n :=
  table[x.val]![y.val]!

/-- A 3x3 helper magma, A21, which streamlines the full construction. -/
private def MagmaA21 : Magma (Fin 3) where
  op := memoFinOp (ofMatrix #[ #[0, 1, 2], #[0, 2, 1], #[0, 2, 1] ])

/-- We define Knuth's A2 here in terms of A21. -/
def MagmaA2 : Magma (Fin 3 × Fin 3) where
  op (p1 p2 : Fin 3 × Fin 3) : Fin 3 × Fin 3 :=
  match p1, p2 with
  | (a, b), (⟨0, _⟩, _) => (MagmaA21.op a b, ⟨0, by decide⟩)
  | (_, b), (c, ⟨0, _⟩) => (b, MagmaA21.op b c)
  | (_, b), (c, _)     => (b, c)

/-- A magma isomorphic to A2, given as an optable. -/
def MagmaA2T : Magma (Fin 9) where
  op := memoFinOp (ofMatrix #[ #[0, 0, 0, 1, 1, 1, 2, 2, 2], #[3, 3, 3, 5, 4, 4, 4, 5, 5], #[6, 6, 6, 8, 7, 7, 7, 8, 8], #[0, 0, 0, 1, 1, 1, 2, 2, 2], #[6, 6, 6, 5, 4, 4, 4, 5, 5], #[3, 3, 3, 8, 7, 7, 7, 8, 8], #[0, 0, 0, 1, 1, 1, 2, 2, 2], #[6, 6, 6, 5, 4, 4, 4, 5, 5], #[3, 3, 3, 8, 7, 7, 7, 8, 8]])

/-- Fin 3 × Fin 3 is isomorphic to Fin 9 as a set. -/
def equiv_F3xF3_F9 : (Fin 3 × Fin 3) ≃ (Fin 9) where
  toFun := fun (p : Fin 3 × Fin 3) =>
    let a := p.1.val
    let b := p.2.val
    have ha : a < 3 := p.1.isLt
    have hb : b < 3 := p.2.isLt
    have h2a : b + 3 * a < 9 := by linarith
    Fin.mk (b + 3 * a) h2a

  invFun := fun (n : Fin 9) =>
    let a := n.val / 3
    let b := n.val % 3
    have ha : a < 3 := Nat.div_lt_of_lt_mul (Fin.is_lt n)
    have hb : b < 3 := Nat.mod_lt n.val (by norm_num)
    (Fin.mk a ha, Fin.mk b hb)

  left_inv := fun (n : Fin 3 × Fin 3) => by
    match n with
    | (⟨0, _⟩, ⟨0, _⟩) | (⟨0, _⟩, ⟨1, _⟩) | (⟨0, _⟩, ⟨2, _⟩) |
      (⟨1, _⟩, ⟨0, _⟩) | (⟨1, _⟩, ⟨1, _⟩) | (⟨1, _⟩, ⟨2, _⟩) |
      (⟨2, _⟩, ⟨0, _⟩) | (⟨2, _⟩, ⟨1, _⟩) | (⟨2, _⟩, ⟨2, _⟩) =>
        simp_all only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, Fin.reduceFinMk, Nat.reduceMod, Fin.isValue]
  right_inv := fun (n : Fin 9) => by
    match n with
    | ⟨0, _⟩ | ⟨1, _⟩ | ⟨2, _⟩ |
      ⟨3, _⟩ | ⟨4, _⟩ | ⟨5, _⟩ |
      ⟨6, _⟩ | ⟨7, _⟩ | ⟨8, _⟩ =>
        simp_all only [Nat.reduceMod, Nat.reduceDiv, Nat.reduceMul, Nat.reduceAdd, Fin.reduceFinMk]

local instance : Magma (Fin 3 × Fin 3) := MagmaA2
local instance : Magma (Fin 9) := MagmaA2T

def equiv_MagmaA2_MagmaA2T : (Fin 3 × Fin 3) ≃◇ (Fin 9) where
  toEquiv := equiv_F3xF3_F9
  map_op' := by
    intros x y
    match x with
    | (⟨n, _⟩, ⟨m, _⟩) =>
      match y with
      | (⟨k, _⟩, ⟨l, _⟩) =>
        match n, m, k, l with
        | 0, 0, 0, 0 | 0, 0, 0, 1 | 0, 0, 0, 2
        | 0, 0, 1, 0 | 0, 0, 1, 1 | 0, 0, 1, 2
        | 0, 0, 2, 0 | 0, 0, 2, 1 | 0, 0, 2, 2
        | 0, 1, 0, 0 | 0, 1, 0, 1 | 0, 1, 0, 2
        | 0, 1, 1, 0 | 0, 1, 1, 1 | 0, 1, 1, 2
        | 0, 1, 2, 0 | 0, 1, 2, 1 | 0, 1, 2, 2
        | 0, 2, 0, 0 | 0, 2, 0, 1 | 0, 2, 0, 2
        | 0, 2, 1, 0 | 0, 2, 1, 1 | 0, 2, 1, 2
        | 0, 2, 2, 0 | 0, 2, 2, 1 | 0, 2, 2, 2
        | 1, 0, 0, 0 | 1, 0, 0, 1 | 1, 0, 0, 2
        | 1, 0, 1, 0 | 1, 0, 1, 1 | 1, 0, 1, 2
        | 1, 0, 2, 0 | 1, 0, 2, 1 | 1, 0, 2, 2
        | 1, 1, 0, 0 | 1, 1, 0, 1 | 1, 1, 0, 2
        | 1, 1, 1, 0 | 1, 1, 1, 1 | 1, 1, 1, 2
        | 1, 1, 2, 0 | 1, 1, 2, 1 | 1, 1, 2, 2
        | 1, 2, 0, 0 | 1, 2, 0, 1 | 1, 2, 0, 2
        | 1, 2, 1, 0 | 1, 2, 1, 1 | 1, 2, 1, 2
        | 1, 2, 2, 0 | 1, 2, 2, 1 | 1, 2, 2, 2
        | 2, 0, 0, 0 | 2, 0, 0, 1 | 2, 0, 0, 2
        | 2, 0, 1, 0 | 2, 0, 1, 1 | 2, 0, 1, 2
        | 2, 0, 2, 0 | 2, 0, 2, 1 | 2, 0, 2, 2
        | 2, 1, 0, 0 | 2, 1, 0, 1 | 2, 1, 0, 2
        | 2, 1, 1, 0 | 2, 1, 1, 1 | 2, 1, 1, 2
        | 2, 1, 2, 0 | 2, 1, 2, 1 | 2, 1, 2, 2
        | 2, 2, 0, 0 | 2, 2, 0, 1 | 2, 2, 0, 2
        | 2, 2, 1, 0 | 2, 2, 1, 1 | 2, 2, 1, 2
        | 2, 2, 2, 0 | 2, 2, 2, 1 | 2, 2, 2, 2 =>
          simp [equiv_F3xF3_F9]
          simp_all only [Nat.ofNat_pos, Nat.one_lt_ofNat, Fin.isValue]
          obtain ⟨_, _⟩ := x
          obtain ⟨_, _⟩ := y
          rfl

@[equational_result]
theorem MagmaA2T.Facts : ∃ (G : Type) (_ : Magma G), Facts G
  [168, 1480, 1483, 1484, 1485, 1486, 1487, 2052, 2089, 2126, 2162, 2163, 2164]
  [3461, 3462, 3463, 3521, 3522, 3523, 3532, 3533, 3534, 3535, 3864, 3880, 3883, 3915, 3921, 3952, 3958, 3989, 3997, 4001, 4268, 4282, 4314, 4315, 4339, 4357, 4587, 4606, 4615, 4645, 4666, 4689]
  := ⟨Fin 9, MagmaA2T, by decideFin!⟩
