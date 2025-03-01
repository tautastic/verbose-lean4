import Verbose.Tactics.Widget
import Verbose.German.Help

namespace Verbose.German
open Lean Meta Server

open ProofWidgets

implement_endpoint (lang := de) mkReformulateHypTacStx (hyp : Ident) (new : Term) : MetaM (TSyntax `tactic) :=
`(tactic|Wir formulieren $hyp um zu $new)

implement_endpoint (lang := de) mkShowTacStx (new : Term) : MetaM (TSyntax `tactic) :=
`(tactic|Wir beweisen dass $new)

implement_endpoint (lang := de) mkConcludeTacStx (args : List Term) : MetaM (TSyntax `tactic) := do
let concl ← listTermToMaybeAppliedDE args
`(tactic|Wir beenden den Beweis durch $concl)

implement_endpoint (lang := de) mkObtainTacStx (args : List Term) (news : List MaybeTypedIdent) :
  MetaM (TSyntax `tactic) := do
let maybeApp ← listTermToMaybeAppliedDE args
let newStuff ← listMaybeTypedIdentToNewStuffSuchThatDE news
`(tactic|Durch $maybeApp erhalten wir $newStuff)

implement_endpoint (lang := de) mkUseTacStx (wit : Term) : Option Term → MetaM (TSyntax `tactic)
| some goal => `(tactic|Wir beweisen dass $wit funktioniert : $goal)
| none => `(tactic|Wir beweisen dass $wit funktioniert)

implement_endpoint (lang := de) mkSinceTacStx (facts : Array Term) (concl : Term) :
    MetaM (TSyntax `tactic) := do
  let factsS ← arrayToFactsDE facts
  `(tactic|Da $factsS folgt das Ziel durch $concl)

@[server_rpc_method]
def suggestionsPanel.rpc := mkPanelRPC makeSuggestions
  "Wählen Sie Unterausdrücke mit Shift-Klick aus."
  "Vorschläge"
  "vorschläge"

@[widget_module]
def suggestionsPanel : Component SuggestionsParams :=
  mk_rpc_widget% suggestionsPanel.rpc

syntax (name := withSuggestions) "with_suggestions" tacticSeq : tactic

@[tactic withSuggestions]
def withPanelWidgets : Lean.Elab.Tactic.Tactic
  | stx@`(tactic| with_suggestions $seq) => do
    Lean.Widget.savePanelWidgetInfo suggestionsPanel.javascriptHash (pure .null) stx
    Lean.Elab.Tactic.evalTacticSeq seq
  | _ => Lean.Elab.throwUnsupportedSyntax
