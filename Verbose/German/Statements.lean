import Verbose.Tactics.Statements
import Verbose.Tactics.Common
import Verbose.German.Widget

open Lean Meta Elab Command Parser Tactic

open Lean.Parser.Term (bracketedBinder)

implement_endpoint (lang := de) mkWidgetProof (prf : TSyntax ``tacticSeq) : CoreM (TSyntax `tactic) :=
Lean.TSyntax.mkInfoCanonical <$> `(tactic| with_suggestions $prf)

implement_endpoint (lang := de) victoryMessage : CoreM String := return "Gewonnen 🎉"
implement_endpoint (lang := de) noVictoryMessage : CoreM String := return "Die Übung ist nicht erledigt."

/- **TODO**  Allow omitting Gegeben or Annahmen. -/

elab ("Aufgabe"<|>"Beispiel") str
    "Gegeben:" objs:bracketedBinder*
    "Annahmen:" hyps:bracketedBinder*
    "Konklusion:" concl:term
    tkp:"Beweis:" prf?:(tacticSeq)? tkq:"QED" : command => do
  mkExercise none objs hyps concl prf? tkp tkq

elab ("Aufgabe-lemma"<|>"Lemma") name:ident str
    "Gegeben:" objs:bracketedBinder*
    "Annahmen:" hyps:bracketedBinder*
    "Konklusion:" concl:term
    tkp:"Beweis:" prf?:(tacticSeq)? tkq:"QED" : command => do
  mkExercise (some name) objs hyps concl prf? tkp tkq
