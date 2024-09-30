import equational_theories.EquationalResult
import equational_theories.Subgraph
import ProofWidgets

open Lean Core Elab Command ProofWidgets Server


@[widget_module]
def ImplicationDiagram : ProofWidgets.Component Result.Output where
  javascript := include_str "../widget/dist/HasseDiagram.js"

syntax (name := implication_visualization) "#display_implications" : command

@[command_elab implication_visualization]
unsafe def displayImplications : CommandElab := fun stx => do
  let output ← Result.collectResults
  runTermElabM fun _ => do
    Widget.savePanelWidgetInfo (stx := stx) (hash := ImplicationDiagram.javascriptHash.val) do
      return toJson output
