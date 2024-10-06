import equational_theories.LiftingMagmaFamilies
-- import equational_theories.AllEquations

open Lean Elab Meta Term Qq

partial def Lean.Meta.DiscrTree.Trie.collectChildren {α} : DiscrTree.Trie α → Array α
  | .node vs children => vs ++ children.concatMap fun ⟨_, t⟩ => t.collectChildren

def getLiftingFamilies : MetaM (Array Name) := do
  let globalInstances ← getGlobalInstancesIndex
  let .some resultsTrie := globalInstances.root.find? (.const ``LiftingMagmaFamily 2) |
    throwError "Failed to find instances of `LiftingMagmaFamily`."
  return resultsTrie.collectChildren.filterMap InstanceEntry.globalName?

def getLaws : MetaM (Array Name) := do
  let env ← getEnv
  env.constants.foldM (init := #[]) fun results decl cInfo => do
    if env.isSafeDefinition decl && cInfo.type.isAppOf ``Law.MagmaLaw then
      return results.push decl
    else
      return results
