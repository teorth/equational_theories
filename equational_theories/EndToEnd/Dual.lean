import equational_theories.EndToEnd.Basic
import equational_theories.MagmaOp

/-!
# Dual model witnesses

If a magma `G` satisfies `l` and refutes `l'`, then the opposite magma `Op G` satisfies and
refutes the duals of those laws. That doubles the supply of `NegFact`s.

This is needed on the negative side and only there: the directly proven implications already
generate the full positive graph, but without dual witnesses 51 SCCs have non-implications that
nothing refutes.
-/

namespace EndToEnd

open Law

variable {G : Type} [Magma G] {l l' : Law.NatMagmaLaw}

/-- `Op G` satisfies the dual of anything `G` satisfies. -/
theorem satisfies_op_of_isDual (hd : MagmaLaw.IsDual l l') (h : G ⊧ l) : (Op G) ⊧ l' := by
  have h' : G ⊧ l'.dual := (hd G).mp h
  have := models.Op (G := G) (w₁ := l'.lhs.dual) (w₂ := l'.rhs.dual) h'
  simpa [MagmaLaw.dual] using this

/-- `Op G` refutes the dual of anything `G` refutes. -/
theorem not_satisfies_op_of_isDual (hd : MagmaLaw.IsDual l l') (h : ¬ (G ⊧ l)) :
    ¬ ((Op G) ⊧ l') := by
  intro hop
  exact h ((hd G).mpr (MagmaLaw.satisfies_dual_dual hop))

/-- Lists of laws, paired up by duality. -/
theorem satisfiesAll_op {ls ls' : List Law.NatMagmaLaw}
    (hd : List.Forall₂ MagmaLaw.IsDual ls ls') (h : SatisfiesAll G ls) :
    SatisfiesAll (Op G) ls' := by
  induction hd with
  | nil => trivial
  | cons hx _ ih => exact ⟨satisfies_op_of_isDual hx h.1, ih h.2⟩

theorem refutesAll_op {ls ls' : List Law.NatMagmaLaw}
    (hd : List.Forall₂ MagmaLaw.IsDual ls ls') (h : RefutesAll G ls) :
    RefutesAll (Op G) ls' := by
  induction hd with
  | nil => trivial
  | cons hx _ ih => exact ⟨not_satisfies_op_of_isDual hx h.1, ih h.2⟩

/-- The dual of a model witness, given the two laws-are-dual relations pointwise. -/
theorem negFact_dual {sat ref sat' ref' : List Nat}
    (hS : List.Forall₂ MagmaLaw.IsDual (sat.map lawOf) (sat'.map lawOf))
    (hR : List.Forall₂ MagmaLaw.IsDual (ref.map lawOf) (ref'.map lawOf))
    (h : ∃ (G : Type) (_ : Magma G),
          SatisfiesAll G (sat.map lawOf) ∧ RefutesAll G (ref.map lawOf)) :
    ∃ (G : Type) (_ : Magma G),
      SatisfiesAll G (sat'.map lawOf) ∧ RefutesAll G (ref'.map lawOf) := by
  obtain ⟨G, inst, hs, hr⟩ := h
  exact ⟨Op G, opMagma, satisfiesAll_op hS hs, refutesAll_op hR hr⟩

/-!
## A global duality table

The duality facts live once in a table rather than per witness, and the `List.Forall₂` a dual
witness needs is derived from it by `forall2_dualIdx` rather than written out, so its length
never appears in the generated data.
-/

/-- One entry of the duality table: `law` and `dual` are dual to each other. -/
structure DualFact where
  law : Nat
  dual : Nat
  proof : MagmaLaw.IsDual (lawOf law) (lawOf dual)

/-- The dual of law index `n`, according to the table. -/
def dualIdx (dt : RArray DualFact) (n : Nat) : Nat := (dt.get n).dual

/-- The table is indexed by the law it talks about, and stays in range. -/
def checkDualTable (dt : RArray DualFact) (numEq : Nat) : Bool :=
  (List.range numEq).all fun n => ((dt.get n).law == n) && Nat.blt (dt.get n).dual numEq

theorem isDual_of_table {dt : RArray DualFact} {numEq : Nat}
    (h : checkDualTable dt numEq = true) {n : Nat} (hn : n < numEq) :
    MagmaLaw.IsDual (lawOf n) (lawOf (dualIdx dt n)) := by
  have := (List.all_eq_true.mp h) n (by simpa using hn)
  simp only [Bool.and_eq_true, beq_iff_eq] at this
  have e : (dt.get n).law = n := this.1
  simpa [dualIdx, e] using (dt.get n).proof

/-- The pointwise `Forall₂` a dual witness needs, built by induction rather than written out. -/
theorem forall2_dualIdx {dt : RArray DualFact} {numEq : Nat}
    (h : checkDualTable dt numEq = true) :
    ∀ l : List Nat, l.all (fun n => Nat.blt n numEq) = true →
      List.Forall₂ MagmaLaw.IsDual (l.map lawOf) ((l.map (dualIdx dt)).map lawOf) := by
  intro l
  induction l with
  | nil => intro _; exact List.Forall₂.nil
  | cons a as ih =>
      intro hb
      simp only [List.all_cons, Bool.and_eq_true, Nat.blt_eq] at hb
      exact List.Forall₂.cons (isDual_of_table h hb.1) (ih hb.2)

/-- The dual of a model witness, with the duality supplied by the table.

`hs`/`hr` say the stored dual index lists really are the pointwise duals. They are discharged
by kernel computation, so they cost a constant-size proof term. -/
theorem negFact_dual_table {dt : RArray DualFact} {numEq : Nat}
    (hdt : checkDualTable dt numEq = true) (sat ref sat' ref' : List Nat)
    (hsb : sat.all (fun n => Nat.blt n numEq) = true)
    (hrb : ref.all (fun n => Nat.blt n numEq) = true)
    (hs : sat.map (dualIdx dt) = sat') (hr : ref.map (dualIdx dt) = ref')
    (h : ∃ (G : Type) (_ : Magma G),
          SatisfiesAll G (sat.map lawOf) ∧ RefutesAll G (ref.map lawOf)) :
    ∃ (G : Type) (_ : Magma G),
      SatisfiesAll G (sat'.map lawOf) ∧ RefutesAll G (ref'.map lawOf) := by
  subst hs; subst hr
  exact negFact_dual (forall2_dualIdx hdt sat hsb) (forall2_dualIdx hdt ref hrb) h

end EndToEnd
