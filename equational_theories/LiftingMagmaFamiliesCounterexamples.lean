import equational_theories.LiftingMagmaFamilies
import equational_theories.EquationsCommand
import equational_theories.Closure

open Law
open Lean Elab Command Term

-- TODO: Automatically generate these structures when a lifting magma family is defined
structure LiftingMagmaFamilyInstance where
  G : (α : Type) → [DecidableEq α] → Type
  instDecidableEq : ∀ α [DecidableEq α], Magma (G α)
  instLiftingMagmaFamily : LiftingMagmaFamily G
  instName : Name

def liftingMagmaFamilyInstances : Array LiftingMagmaFamilyInstance := #[
  ⟨(List ·), _, inferInstance, ``instLiftingMagmaFamilyList⟩,
  ⟨(Multiset ·), _, inferInstance, ``instLiftingMagmaFamilyMultiset⟩,
  ⟨(Id ·), _, instLiftingMagmaFamilyLeftProj, ``instLiftingMagmaFamilyLeftProj⟩,
  ⟨(Id ·), _, instLiftingMagmaFamilyRightProj, ``instLiftingMagmaFamilyRightProj⟩
]

def generateNonimplications (inst : LiftingMagmaFamilyInstance) : MetaM Unit := do
  let laws ← getMagmaLaws
  let mut positives : Array (Name × NatMagmaLaw) := #[]
  let mut negatives : Array (Name × NatMagmaLaw) := #[]
  for (lawName, law) in laws do
    let result := @decide _ <| @instDecidableSatisfies Nat inst.G inst.instDecidableEq inst.instLiftingMagmaFamily _ law
    if result then
      positives := positives.push (lawName, law)
    else
      negatives := negatives.push (lawName, law)
  let eqnThms ← Result.extractEquationalResults
  let closure ← Closure.closure <| eqnThms.map Entry.variant
  for (posLawName, posLaw) in positives do
    for (negLawName, negLaw) in negatives do
      let thm := Closure.Edge.nonimplication {
        lhs := magmaLawNameToEquationName posLawName.toString,
        rhs := magmaLawNameToEquationName negLawName.toString
      }
      unless closure.contains thm do
        sorry
