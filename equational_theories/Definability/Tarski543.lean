import equational_theories.Definability.Basic
import equational_theories.Equations.All
import equational_theories.Generated.MagmaEgg.small
import Mathlib.Algebra.Group.MinimalAxioms

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

References: https://math.stackexchange.com/a/1225476/127777,
  http://matwbn.icm.edu.pl/ksiazki/fm/fm30/fm30132.pdf
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

theorem Equation543_implies_Equation11 [Magma M] : Equation543 M → Equation11 M := by
  intro h x y
  rw [Equation543_implies_Equation4369 h, ← Equation543_implies_Equation16 h x y]

theorem Equation543_implies_Equation40 [Magma M] : Equation543 M → Equation40 M := by
  intro h x y
  simpa only [← Equation543_implies_Equation11 h] using Equation543_implies_Equation16 h (x ◇ x) y

theorem Equation543_implies_Equation3823 [Magma M] : Equation543 M → Equation3823 M := by
  intro h x y z
  simp only [Equation543_implies_Equation4369 h (z ◇ z) y x, ← Equation543_implies_Equation11 h]

/--
We define the commutative semigroup structure first, instead of the commutative *group* structure,
because the identity is not actually definable (in first-order logic, nor is it computable in Lean).
Also, in general magmas may be Empty, in which case we have a CommSemigroup structure but not an
identity.

We'll prove it is also `IsCancelMul` later, and give the noncomputable CommGroup structure that
extends this when it's nonempty.
-/
def CommSemigroupOf543 [Magma M] (h : Equation543 M) : CommSemigroup M :=
  let i : Mul M := ⟨fun x y ↦ x ◇ ((x ◇ x) ◇ y)⟩
  have h4369 : ∀_,_ := Equation543_implies_Equation4369 h -- (1.3)
  have h11 : ∀_,_ := Equation543_implies_Equation11 h
  have h40 : ∀_,_ := Equation543_implies_Equation40 h
  have hcomm' (x y : M) : x ◇ ((x ◇ x) ◇ y) = y ◇ ((y ◇ y) ◇ x) := by rw [← h4369, h40]
  have hcomm (x y : M) : x * y = y * x :=
    hcomm' x y
  {
    mul := fun x y ↦ x ◇ ((x ◇ x) ◇ y)
    mul_comm := hcomm
    mul_assoc := fun x y z ↦ by
      have h23 (x y z : M) : x * (y ◇ z) = x ◇ (z ◇ y) := by
        simp only [HMul.hMul, Mul.mul]
        apply congrArg (fun t ↦ x ◇ t)
        rw [h4369 (x ◇ x) y z, ← h11 y x]
      have h26 (x y z : M) : x * (y ◇ z) = y * (x ◇ z) :=
        (h23 _ _ _).trans <| (h4369 _ _ _).trans (h23 _ _ _).symm
      have h28 (x y z : M) : x * (y ◇ ((y ◇ y) ◇ z)) = y * (x ◇ ((x ◇ x) ◇ z)) := by
        simpa [h40 x y] using h26 x y ((y ◇ y) ◇ z)
      have h32 (x y z : M) : x * (y * z) = y * (z * x) := by
        simpa [hcomm z x] using h28 _ _ _
      have h34 (x y z : M) : y * (z * x) = z * (x * y) := by
        simpa [hcomm x z, hcomm x y] using (h28 z y x).symm
      symm
      exact (h32 x y z).trans <| (h34 x y z).trans (hcomm _ _)
  }

noncomputable def CommGroupOf543 [Magma M] [hn : Nonempty M] (h : Equation543 M) : CommGroup M :=
  let iInv : Inv M := ⟨fun x ↦ (x ◇ x) ◇ x⟩
  let iOne : One M := ⟨Classical.choice hn ◇ Classical.choice hn⟩
  let iCS := CommSemigroupOf543 h
  let iG : Group M :=
    Group.ofLeftAxioms iCS.mul_assoc (by
      intro x
      change (_ ◇ _) ◇ ((1 ◇ 1) ◇ _) = x
      have h40 : ∀_,_ := Equation543_implies_Equation40 h
      rw [Equation543_implies_Equation4369 h, h40 (Classical.choice _) 1, h40 _ x]
      exact (Equation543_implies_Equation16 h x x).symm
    ) (by
      intro x
      rw [iCS.mul_comm]
      change _ ◇ (_ ◇ (_ ◇ _)) = _ ◇ _
      rw [Equation543_implies_Equation4369 h]
      simp [Equation543_implies_Equation40 h _ x]
    )
  CommGroup.mk iCS.mul_comm

theorem CommGroupOf543_eq_CommSemigroupOf543 [Magma M] [hn : Nonempty M] (h : Equation543 M) :
    (CommGroupOf543 h).toCommSemigroup = CommSemigroupOf543 h :=
  rfl

open FirstOrder.Language

--A term defining the group operation from subtraction
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

--A formula defining subtraction from the group operation.
-- { (x,y,z) } is in the graph of the subtraction operation, -, if and only if
-- x-y = z, so, if x=y+z.
private lemma groupDef {M : Type*} [op : Magma M] (h : Equation543 M) :
    @Set.Definable _ (∅:Set M) MagmaLanguage (Magma.FOStructure ⟨(CommSemigroupOf543 h).mul⟩)
    _ op.Graph := by
  -- x = y + z
  use Term.equal
    (Term.var (Sum.inl 0))
    (Functions.apply₂ (Sum.inl ()) (Term.var (Sum.inl 1)) (Term.var (Sum.inr ())))
  ext v
  simp [Magma.Graph, Function.arityGraph, Magma.FinArityOp, CommSemigroupOf543]
  set x := v (Sum.inl 0)
  set y := v (Sum.inl 1)
  set z := v (Sum.inr ())
  -- Prove that  x ◇ y = z ↔ x = y ◇ ((y ◇ y) ◇ z)  where ◇ is the subtraction operation
  have h11 : ∀_,_ := Equation543_implies_Equation11 h
  have h16 : ∀_,_ := Equation543_implies_Equation16 h
  have h3823 : ∀_,_ := Equation543_implies_Equation3823 h
  have h4369 : ∀_,_ := Equation543_implies_Equation4369 h
  constructor <;> intro h1
  · rw [← h1, ← h3823, ← h16]
  · rw [h16 y (z ◇ z), h1, h4369, ← h3823, h4369, h4369 _ _ y, ← h16, ← h3823, ← h11]

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
  · rw [@Law4512.models_iff]
    exact fun x y z ↦ ((CommSemigroupOf543 he543).mul_assoc x y z).symm
  constructor
  · exact (termDef he543).Definable (inst := op.FOStructure) --The group operation is definable
  · exact groupDef he543 --The subtraction operation can be recovered from the group operation

/-- Commutative structure, Equation 4512, is a structural definition from any magma obeying Tarski's
one-equation abelian group subtraction law, Equation 543. -/
theorem Equation43_StructuralFrom_Equation543 : Law43.StructuralFrom Law543 := by
  intro M op hl543
  have he543 : Equation543 M := Law543.models_iff.mp hl543
  use ⟨(CommSemigroupOf543 he543).mul⟩
  constructor
  · rw [@Law43.models_iff]
    exact fun x y ↦ (CommSemigroupOf543 he543).mul_comm x y
  constructor
  · exact (termDef he543).Definable (inst := op.FOStructure) --The group operation is definable
  · exact groupDef he543 --The subtraction operation can be recovered from the group operation
