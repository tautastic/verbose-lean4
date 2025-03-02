import Verbose.Tactics.Calc
import Verbose.German.Common
import Verbose.German.We

section widget

open ProofWidgets
open Lean Meta

implement_endpoint (lang := de) getSince? : MetaM String := pure "durch?"
implement_endpoint (lang := de) createOneStepMsg : MetaM String := pure "Erstelle einen neuen Schritt"
implement_endpoint (lang := de) createTwoStepsMsg : MetaM String := pure "Erstelle zwei neue Schritte"

/-- Rpc function for the calc widget. -/
@[server_rpc_method]
def VerboseCalcPanelDE.rpc := mkSelectionPanelRPC' verboseSuggestSteps
  "Bitte wählen Sie Unterausdrücke im Ziel mit Shift-Klick aus."
  "Erstellen eines neuen Rechenschritts"
  (extraCss := some "#suggestions {display:none}")

/-- The calc widget. -/
@[widget_module]
def WidgetCalcPanelDE : Component CalcParams :=
  mk_rpc_widget% VerboseCalcPanelDE.rpc

implement_endpoint (lang := de) mkComputeCalcTac : MetaM String := pure "durch berechnung"
implement_endpoint (lang := de) mkComputeCalcDescr : MetaM String := pure "Begründe durch berechnung"
implement_endpoint (lang := de) mkComputeAssptTac : MetaM String := pure "durch annahme"
implement_endpoint (lang := de) mkComputeAssptDescr : MetaM String := pure "Begründe durch annahme"
implement_endpoint (lang := de) mkSinceCalcTac : MetaM String := pure "da"
implement_endpoint (lang := de) mkSinceCalcHeader : MetaM String := pure "Begründe durch"
implement_endpoint (lang := de) mkSinceCalcArgs (args : Array Format) : MetaM String := do
  return match args with
  | #[] => ""
  | #[x] => s!"{x}"
  | a => ", ".intercalate ((a[:a.size-1]).toArray.toList.map (toString)) ++ s!" und {a[a.size-1]!}"

configureCalcSuggestionProvider verboseSelectSince

implement_endpoint (lang := de) theSelectedSubExpr : MetaM String :=
  pure "Der ausgewählte Unterausdruck"
implement_endpoint (lang := de) allSelectedSubExpr : MetaM String :=
  pure "Alle ausgewählten Unterausdrücke"
implement_endpoint (lang := de) inMainGoal : MetaM String :=
  pure "im Hauptziel."
implement_endpoint (lang := de) inMainGoalOrCtx : MetaM String :=
  pure "im Hauptziel oder seinem Kontext."
implement_endpoint (lang := de) shouldBe : MetaM String :=
  pure "sollte sein"
implement_endpoint (lang := de) shouldBePl : MetaM String :=
  pure "sollten sein"
implement_endpoint (lang := de) selectOnlyOne : MetaM String :=
  pure "Sie sollten nur einen Unterausdruck auswählen."

/-- Rpc function for the calc justification widget. -/
@[server_rpc_method]
def VerboseCalcSincePanelDE.rpc := mkSelectionPanelRPC' (onlyGoal := false) getCalcSuggestion
  "Sie können eine oder mehrere Hypothesen auswählen, die Sie verwenden möchten."
  "Begründung"
  verboseGetDefaultCalcSuggestions
  (extraCss := some "#suggestions {display:none}")

/-- The calc justification widget. -/
@[widget_module]
def WidgetCalcSincePanelDE : Component CalcParams :=
  mk_rpc_widget% VerboseCalcSincePanelDE.rpc
end widget

namespace Lean.Elab.Tactic
open Meta Verbose German

declare_syntax_cat CalcFirstStepDE
syntax ppIndent(colGe term (" durch " sepBy(maybeAppliedDE, " und durch "))?) : CalcFirstStepDE
syntax ppIndent(colGe term (" durch berechnung")?) : CalcFirstStepDE
syntax ppIndent(colGe term (" da " factsDE)?) : CalcFirstStepDE
syntax ppIndent(colGe term (" denn " tacticSeq)?) : CalcFirstStepDE
syntax ppIndent(colGe term (" durch?")?) : CalcFirstStepDE

-- enforce indentation of calc steps so we know when to stop parsing them
declare_syntax_cat CalcStepDE
syntax ppIndent(colGe term " durch " sepBy(maybeAppliedDE, " und durch ")) : CalcStepDE
syntax ppIndent(colGe term " durch berechnung") : CalcStepDE
syntax ppIndent(colGe term " da " factsDE) : CalcStepDE
syntax ppIndent(colGe term " denn " tacticSeq) : CalcStepDE
syntax ppIndent(colGe term " durch?") : CalcStepDE
syntax CalcStepDEs := ppLine withPosition(CalcFirstStepDE) withPosition((ppLine linebreak CalcStepDE)*)

syntax (name := calcTacticDE) "Calc" CalcStepDEs : tactic

elab tk:"sinceCalcTacDE" facts:factsDE : tactic => withRef tk <| sinceCalcTac (factsDEToArray facts)

def convertFirstCalcStepDE (step : TSyntax `CalcFirstStepDE) : TermElabM (TSyntax ``calcFirstStep × Option Syntax) := do
  match step with
  | `(CalcFirstStepDE|$t:term) => pure (← `(calcFirstStep|$t:term), none)
  | `(CalcFirstStepDE|$t:term durch%$btk berechnung%$ctk) =>
    pure (← run t btk ctk `(tacticSeq| Wir berechnen), none)
  | `(CalcFirstStepDE|$t:term durch%$tk $prfs und durch*) => do
    let prfTs ← liftMetaM <| prfs.getElems.mapM maybeAppliedDEToTerm
    pure (← run t tk none `(tacticSeq| fromCalcTac $prfTs,*), none)
  | `(CalcFirstStepDE|$t:term da%$tk $facts:factsDE) =>
    pure (← run t tk none `(tacticSeq|sinceCalcTacDE%$tk $facts), none)
  | `(CalcFirstStepDE|$t:term durch?%$tk) =>
    pure (← run t tk none `(tacticSeq|sorry%$tk), some tk)
  | `(CalcFirstStepDE|$t:term denn%$tk $prf:tacticSeq) =>
    pure (← run t tk none `(tacticSeq|$prf), none)
  | _ => throwUnsupportedSyntax
where
  run (t : Term) (btk : Syntax) (ctk? : Option Syntax)
      (tac : TermElabM (TSyntax `Lean.Parser.Tactic.tacticSeq)) :
      TermElabM (TSyntax `Lean.calcFirstStep) := do
    let ctk := ctk?.getD btk
    let tacs ← withRef ctk tac
    let pf ← withRef step.raw[1] `(term| by%$btk $tacs)
    let pf := pf.mkInfoCanonical
    withRef step <| `(calcFirstStep|$t:term := $pf)

def convertCalcStepDE (step : TSyntax `CalcStepDE) : TermElabM (TSyntax ``calcStep × Option Syntax) := do
  match step with
  | `(CalcStepDE|$t:term durch%$btk berechnung%$ctk) =>
    pure (← run t btk ctk `(tacticSeq| Wir berechnen), none)
  | `(CalcStepDE|$t:term durch%$tk $prfs und durch*) => do
    let prfTs ← liftMetaM <| prfs.getElems.mapM maybeAppliedDEToTerm
    pure (← run t tk none `(tacticSeq| fromCalcTac $prfTs,*), none)
  | `(CalcStepDE|$t:term da%$tk $facts:factsDE) =>
    pure (← run t tk none `(tacticSeq|sinceCalcTacDE%$tk $facts), none)
  | `(CalcStepDE|$t:term durch?%$tk) =>
    pure (← run t tk none `(tacticSeq|sorry%$tk), some tk)
  | `(CalcStepDE|$t:term denn%$tk $prf:tacticSeq) =>
    pure (← run t tk none `(tacticSeq|$prf), none)
  | _ => throwUnsupportedSyntax
where
  run (t : Term) (btk : Syntax) (ctk? : Option Syntax)
      (tac : TermElabM (TSyntax `Lean.Parser.Tactic.tacticSeq)) :
      TermElabM (TSyntax `Lean.calcStep) := do
    let ctk := ctk?.getD btk
    let tacs ← withRef ctk tac
    let pf ← withRef step.raw[1] `(term| by%$btk $tacs)
    let pf := pf.mkInfoCanonical
    withRef step <| `(calcStep|$t:term := $pf)

def convertCalcStepsDE (steps : TSyntax ``CalcStepDEs) : TermElabM (TSyntax ``calcSteps × Array (Option Syntax)) := do
  match steps with
  | `(CalcStepDEs| $first:CalcFirstStepDE
       $steps:CalcStepDE*) => do
         let (first, tk?) ← convertFirstCalcStepDE first
         let mut newsteps := #[]
         let mut tks? := #[tk?]
         for step in steps do
           let (newstep, tk?) ← convertCalcStepDE step
           newsteps := newsteps.push newstep
           tks? := tks?.push tk?
         pure (← `(calcSteps|$first
           $newsteps*), tks?)
  | _ => throwUnsupportedSyntax

elab_rules : tactic
| `(tactic|Calc%$calcstx $stx) => do
  let steps : TSyntax ``CalcStepDEs := ⟨stx⟩
  let (steps, tks?) ← convertCalcStepsDE steps
  let views ← Lean.Elab.Term.mkCalcStepViews steps
  if (← verboseConfigurationExt.get).useCalcWidget then
    if let some calcRange := (← getFileMap).rangeOfStx? calcstx then
    let indent := calcRange.start.character + 2
    let mut isFirst := true
    for (step, tk?) in views.zip tks? do
      if let some replaceRange := (← getFileMap).rangeOfStx? step.ref then
        let json := json% {"replaceRange": $(replaceRange),
                           "isFirst": $(isFirst),
                           "indent": $(indent)}
        Lean.Widget.savePanelWidgetInfo WidgetCalcPanelDE.javascriptHash (pure json) step.proof
      if let some tk := tk? then
        if let some replaceRange := (← getFileMap).rangeOfStx? tk then
          let json := json% {"replaceRange": $(replaceRange),
                             "isFirst": $(isFirst),
                             "indent": $(indent)}
          Lean.Widget.savePanelWidgetInfo WidgetCalcSincePanelDE.javascriptHash (pure json) tk
      isFirst := false
  evalVerboseCalc (← `(tactic|calc%$calcstx $steps))

syntax (name := Calc?DE) "Calc?" : tactic

elab "Calc?" : tactic =>
  mkCalc?Tac "Calc erstellen" "Calc" "durch?"

setLang de

example (a b : ℕ) : (a + b)^ 2 = 2*a*b + (a^2 + b^2) := by
  Calc (a+b)^2 = a^2 + b^2 + 2*a*b durch berechnung
  _ = 2*a*b + (a^2 + b^2) durch berechnung

example (a b c d : ℕ) (h : a ≤ b) (h' : c ≤ d) : a + 0 + c ≤ b + d := by
  Calc a + c    ≤ b + c durch h
   _            ≤ b + d durch h'

example (a b c d : ℕ) (h : a ≤ b) (h' : c ≤ d) : a + 0 + c ≤ b + d := by
  Calc a + 0 + c = a + c durch berechnung
  _              ≤ b + c durch h
  _              ≤ b + d durch h'

example (a b c d : ℕ) (h : a ≤ b) (h' : c ≤ d) : a + 0 + c ≤ b + d := by
  Calc a + 0 + c = a + c durch berechnung
  _              ≤ b + c da a ≤ b
  _              ≤ b + d da c ≤ d

example (a b c d : ℕ) (h : a ≤ b) (h' : c ≤ d) : a + 0 + c ≤ b + d := by
  Calc a + 0 + c = a + c durch berechnung
  _              ≤ b + d da a ≤ b und c ≤ d

example (a b c d : ℕ) (h : a ≤ b) (h' : c ≤ d) : a + 0 + c ≤ b + d := by
  Calc a + 0 + c = a + c durch berechnung
  _              ≤ b + d durch h und durch h'

example (a b c d : ℕ) (h : a ≤ b) (h' : c ≤ d) : a + 0 + c ≤ b + d := by
  Calc a + 0 + c = a + c durch berechnung
  _              ≤ b + d durch h und durch h'

def paire_fun  (f : ℝ → ℝ) := ∀ x, f (-x) = f x

example (f g : ℝ → ℝ) : paire_fun f → paire_fun g →  paire_fun (f + g) := by
  intro hf hg
  show ∀ x, (f+g) (-x) = (f+g) x
  intro x₀
  Calc (f + g) (-x₀) = f (-x₀) + g (-x₀) durch berechnung
  _                  = f x₀ + g (-x₀)    da f (-x₀) = f x₀
  _                  = f x₀ + g x₀       da g (-x₀) = g x₀
  _                  = (f + g) x₀        durch berechnung

example (f g : ℝ → ℝ) : paire_fun f →  paire_fun (g ∘ f) := by
  intro hf x
  Calc (g ∘ f) (-x) = g (f (-x)) durch berechnung
                _   = g (f x)    da f (-x) = f x

example (f : ℝ → ℝ) (x : ℝ) (hx : f (-x) = f x ∧ 1 = 1) : f (-x) + 0 = f x := by
  Calc f (-x) + 0 = f (-x) durch berechnung
                _   = f x  da f (-x) = f x

example (f g : ℝ → ℝ) (hf : paire_fun f) (hg : paire_fun g) (x) :  (f+g) (-x) = (f+g) x := by
  Calc (f + g) (-x) = f (-x) + g (-x) durch berechnung
  _                 = f x + g (-x)    da paire_fun f
  _                 = f x + g x       da paire_fun g
  _                 = (f + g) x       durch berechnung


example (ε : ℝ) (h : ε > 1) : 0 ≤ ε := by
  Calc
    (0 : ℝ) ≤ 1 denn norm_num
    _       < ε durch h

example (ε : ℝ) (h : ε > 1) : ε ≥ 0 := by
  Calc
    (0 : ℝ) ≤ 1 denn norm_num
    _       < ε durch h

example (ε : ℝ) (h : ε = 1) : ε+1 ≥ 2 := by
  Calc
    ε + 1 = 1 + 1 denn rw [h]
    _     = 2 durch norm_num

example (ε : ℝ) (h : ε = 1) : ε+1 ≤ 2 := by
  Calc
    ε + 1 = 1 + 1 denn rw [h]
    _     = 2 durch norm_num
