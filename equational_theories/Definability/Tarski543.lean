import equational_theories.Definability.Basic
import equational_theories.Equations.All
import equational_theories.Generated.MagmaEgg.small

/-!
Tarski proved that if an operation obeys `x = y ◇ (z ◇ (x ◇ (y ◇ z)))`, then there is a natural
abelian group structure given by
```
0 := x ◇ x (for any, or all, x)
-x := 0 ◇ x
x + y := x ◇ (0 ◇ y)
```
so that `◇` is the "minus" operation in the group. In particular, the resulting `+` operation is
cancelative, commutative, and associative. We show this in terms of the `TermDefinable` predicate.

References: https://math.stackexchange.com/a/1225476/127777, http://matwbn.icm.edu.pl/ksiazki/fm/fm30/fm30132.pdf
-/

variable {M : Type*}

--Not tagging these as equational_result because they're just transitive closures anyway

theorem Equation543_implies_Equation16 [Magma M] : Equation543 M → Equation16 M :=
  Equation914_implies_Equation16 M ∘
  Equation952_implies_Equation914 M ∘
  Equation2552_implies_Equation952 M ∘
  Equation1774_implies_Equation2552 M ∘
  Equation1964_implies_Equation1774 M ∘
  Equation543_implies_Equation1964 M

theorem Equation543_implies_Equation4369 [Magma M] : Equation543 M → Equation4369 M :=
  Equation3810_implies_Equation4369 M ∘
  Equation1774_implies_Equation3810 M ∘
  Equation1964_implies_Equation1774 M ∘
  Equation543_implies_Equation1964 M

/--
We define the commutative semigroup structure first, instead of the commutative *group* structure,
because the identity is not actually definable (in first-order logic, nor is it computable in Lean).

We could prove it is also `IsCancelMul` later, and give the noncomputable CommGroup structure that
extends this.
-/
def CommSemigroupOf543 [Magma M] (h : Equation543 M) : CommSemigroup M :=
  let i : Mul M := ⟨fun x y ↦ x ◇ ((x ◇ x) ◇ y)⟩
  have h16 : ∀_,_ := Equation543_implies_Equation16 h -- (1.2)
  have h4369 : ∀_,_ := Equation543_implies_Equation4369 h -- (1.3)
  have h11 (x y : M) : x = x ◇ (y ◇ y) := by
    rw [h4369, ← h16 x y]
  have h40 (x y : M) : x ◇ x = y ◇ y := by
    simpa only [← h11] using h16 (x ◇ x) y
  have hcomm' (x y : M) : x ◇ ((x ◇ x) ◇ y) = y ◇ ((y ◇ y) ◇ x) := by
    rw [← h4369, h40]
  have hcomm (x y : M) : x * y = y * x :=
    hcomm' x y
  {
    mul := fun x y ↦ x ◇ ((x ◇ x) ◇ y)
    mul_comm := hcomm
    mul_assoc := fun x y z ↦ by
      have h22 (x y z : M) : (x ◇ x) ◇ (y ◇ z) = z ◇ y := by
        simp only [← h11, h4369 (x ◇ x) y z]
      have h23 (x y z : M) : x * (y ◇ z) = x ◇ (z ◇ y) := by
        simp only [HMul.hMul, Mul.mul, h4369 (x ◇ x) y z, ← h11]
      have h26 (x y z : M) : x * (y ◇ z) = y * (x ◇ z) :=
        (h23 _ _ _).trans <| (h4369 _ _ _).trans (h23 _ _ _).symm
      have h28 (x y z : M) : x * (y ◇ ((y ◇ y) ◇ z)) = y * (x ◇ ((x ◇ x) ◇ z)) := by
        simpa [h40 x y] using h26 x y ((y ◇ y) ◇ z)
      have h32 (x y z : M) : x * (y * z) = y * (z * x) := by
        simpa [hcomm z x] using h28 _ _ _
      have h34 (x y z : M) : y * (z * x) = z * (x * y) := by
        simpa [hcomm x z, hcomm x y] using (h28 z y x).symm
      symm
      exact (h32 x y z).trans ((h34 x y z).trans (hcomm _ _))
  }

open FirstOrder.Language

private lemma termDef {M : Type*} [op : Magma M] (h : Equation543 M) :
    (∅:Set M).TermDefinable MagmaLanguage (inst := op.FOStructure)
    (⟨(CommSemigroupOf543 h).mul⟩ : Magma M).FinArityOp := by
  use (
    let f := Functions.apply₂ (L := (MagmaLanguage.withConstants (∅:Set M))) (α := Fin 2) (Sum.inl ());
    f (Term.var 0) (f (f (Term.var 0) (Term.var 0)) (Term.var 1))
  )
  funext v
  simp only [Magma.FinArityOp, Fin.isValue, constantsOn_Functions, constantsOnFunc,
    Term.realize_functions_apply₂, Term.realize_var, Magma.FOStructure_funMap',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  rfl

/-- Associative structure, Equation 4512, is given by a term from any magma obeying Tarski's
one-equation abelian group subtraction law, Equation 543. -/
theorem Equation4512_termDefinableFrom_Equation543 : Law4512.TermDefinableFrom Law543 := by
  intro M op hl543
  have he543 : Equation543 M := Law543.models_iff.mp hl543
  use ⟨(CommSemigroupOf543 he543).mul⟩
  constructor
  · --The defined operation is associative
    rw [@Law4512.models_iff]
    exact fun x y z ↦ ((CommSemigroupOf543 he543).mul_assoc x y z).symm
  · --The group operation is term definable
    exact termDef he543

/-- Commuative structure, Equation 43, is given by a term from any magma obeying Tarski's
one-equation abelian group subtraction law, Equation 543. -/
theorem Equation4512_termDefinableFrom_Equation43 : Law43.TermDefinableFrom Law543 := by
  intro M op hl543
  have he543 : Equation543 M := Law543.models_iff.mp hl543
  use ⟨(CommSemigroupOf543 he543).mul⟩
  constructor
  · --The defined operation is associative
    rw [@Law43.models_iff]
    exact fun x y ↦ (CommSemigroupOf543 he543).mul_comm x y
  · --The group operation is term definable
    exact termDef he543

/-- Associative structure, Equation 4512, is a structural definition from any magma obeying Tarski's
one-equation abelian group subtraction law, Equation 543. -/
theorem Equation4512_StructuralFrom_Equation543 : Law4512.StructuralFrom Law543 := by
  intro M op hl543
  have he543 : Equation543 M := Law543.models_iff.mp hl543
  use ⟨(CommSemigroupOf543 he543).mul⟩
  constructor
  · --The defined operation is associative
    rw [@Law4512.models_iff]
    exact fun x y z ↦ ((CommSemigroupOf543 he543).mul_assoc x y z).symm
  constructor
  · --The group operation is definable
    exact (termDef he543).Definable (inst := op.FOStructure)
  · --The subtraction operation can be recovered from the group operation, in FO logic
    sorry

/-- Commutative structure, Equation 4512, is a structural definition from any magma obeying Tarski's
one-equation abelian group subtraction law, Equation 543. -/
theorem Equation43_StructuralFrom_Equation543 : Law43.StructuralFrom Law543 := by
  intro M op hl543
  have he543 : Equation543 M := Law543.models_iff.mp hl543
  use ⟨(CommSemigroupOf543 he543).mul⟩
  constructor
  · --The defined operation is associative
    rw [@Law43.models_iff]
    exact fun x y ↦ (CommSemigroupOf543 he543).mul_comm x y
  constructor
  · --The group operation is definable
    exact (termDef he543).Definable (inst := op.FOStructure)
  · --The subtraction operation can be recovered from the group operation, in FO logic
    sorry
