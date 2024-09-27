import equational_theories.ParseImplications
import ProofWidgets

open Lean Core Elab Command ProofWidgets Server


@[widget_module]
def ImplicationDiagram : ProofWidgets.Component Output where
  javascript := include_str "../widget/dist/HasseDiagram.js"

syntax (name := implication_visualization) "#display_implications" : command

@[command_elab implication_visualization]
unsafe def displayImplications : CommandElab := fun stx => do
  let output ← generateOutput
  runTermElabM fun _ => do
    Widget.savePanelWidgetInfo (stx := stx) (hash := ImplicationDiagram.javascriptHash.val) do
      return toJson output

#display_implications
