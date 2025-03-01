import Verbose.Tactics.Lets
import DiffEins.German.Common
import DiffEins.German.We
import DiffEins.German.Since

open Lean Verbose.German

macro ("Fakt" <|> "Behauptung") name:ident ":" stmt:term "denn" colGt prf:tacticSeq: tactic =>
  `(tactic|(checkName $name; have $name : $stmt := by $prf))

open Lean Elab Tactic

elab ("Fakt" <|> "Behauptung") name:ident ":" stmt:term "durch" prf:maybeAppliedDE : tactic => do
  evalTactic (← `(tactic|(checkName $name; have $name : $stmt := by Wir beenden den Beweis durch $prf)))

elab ("Fakt" <|> "Behauptung") name:ident ":" stmt:term "durch berechnung" : tactic => do
  evalTactic (← `(tactic|(checkName $name; have $name : $stmt := by Wir berechnen)))

macro ("Fakt" <|> "Behauptung") name:ident ":" stmt:term "da" facts:factsDE : tactic =>
  `(tactic|(checkName $name; have $name : $stmt := by Da $facts folgt das Ziel durch $stmt))

example : 1 = 1 := by
  Behauptung H : 1 = 1 denn
    rfl
  exact H

example : 1 + 1 = 2 := by
  Fakt H : 1 + 1 = 2 durch berechnung
  exact H

example (ε : ℝ) (ε_pos : 0 < ε) : 1 = 1 := by
  Behauptung H : ε ≥ 0 durch ε_pos
  rfl

example (ε : ℝ) (ε_pos : 0 < ε) : 1 = 1 := by
  Fakt H : ε ≥ 0 da ε > 0
  rfl

set_option linter.unusedVariables false

example (n : ℕ) : n + n + n = 3*n := by
  Fakt key : n + n = 2*n denn
    ring
  ring

example (n : ℤ) (h : 0 < n) : True := by
  Fakt key : 0 < 2*n denn
    linarith only [h]
  Fakt keybis : 0 < 2*n durch mul_pos angewendet auf zero_lt_two und h
  trivial
