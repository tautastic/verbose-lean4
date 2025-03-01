import Verbose.Tactics.We
import DiffEins.German.Common

open Lean Elab Parser Tactic Verbose.German

syntax locationDE := withPosition(" in der Annahme " (locationWildcard <|> locationHyp))

def locationDE_to_location : TSyntax `locationDE → TacticM (TSyntax `Lean.Parser.Tactic.location)
| `(locationDE|in der Annahme $x) => `(location|at $x)
| _ => `(location|at *) -- should not happen

declare_syntax_cat becomesDE
syntax colGt " which becomes " term : becomesDE

def extractBecomesDE (e : Lean.TSyntax `becomesDE) : Lean.Term := ⟨e.raw[1]!⟩

elab rw:"Wir" " umschreiben mit " s:myRwRuleSeq l:(locationDE)? new:(becomesDE)? : tactic => do
  rewriteTac rw s (l.map expandLocation) (new.map extractBecomesDE)

elab rw:"Wir" " umschreiben mit " s:myRwRuleSeq " überall" : tactic => do
  rewriteTac rw s (some Location.wildcard) none

elab "Wir" " betrachten mit " exp:term : tactic =>
  discussOr exp

elab "Wir" " unterscheiden ob " exp:term : tactic =>
  discussEm exp

implement_endpoint (lang := de) cannotConclude : CoreM String :=
pure "Das reicht nicht für die Schlussfolgerung."

elab "Wir" " beenden den Beweis durch " e:maybeAppliedDE : tactic => do
  concludeTac (← maybeAppliedDEToTerm e)

elab "Wir" " kombinieren " prfs:sepBy(term, " und ") : tactic => do
  combineTac prfs.getElems

implement_endpoint (lang := de) computeFailed (goal : MessageData) : TacticM MessageData :=
  pure m!"Das Ziel {goal} scheint nicht ohne weiteres aus einer Berechnung zu folgen."

elab "Wir" " berechnen " loc:(locationDE)? : tactic => do
  let loc ← loc.mapM locationDE_to_location
  computeTac loc

elab "Wir" " verwenden " exp:term : tactic => do
  evalApply (← `(tactic|apply $exp))

-- elab "Wir" " apply " exp:term " at " h:ident: tactic => do
--   let loc ← ident_to_location h
--   evalTactic (← `(tactic|apply_fun $exp $loc:location))

elab "Wir" " verwenden " exp:term " auf " e:term : tactic => do
  evalTactic (← `(tactic|specialize $exp $e))

macro "Wir" " vergessen " args:(ppSpace colGt term:max)+ : tactic => `(tactic|clear $args*)

macro "Wir" " formulieren " h:ident " um zu " new:term : tactic => `(tactic|change $new at $h:ident)

implement_endpoint (lang := de) renameResultSeveralLoc : CoreM String :=
pure "Man kann das Ergebnis der Umbenennung nur angeben, wenn man an einer einzigen Stelle umbenennt."

elab "Wir" " benennen" old:ident " um zu " new:ident loc:(locationDE)? become?:(becomesDE)? : tactic => do
  let loc? ← loc.mapM locationDE_to_location
  renameTac old new loc? (become?.map extractBecomesDE)

implement_endpoint (lang := de) unfoldResultSeveralLoc : CoreM String :=
pure "Man kann das Ergebnis der Entfaltung nur angeben, wenn die Entfaltung an einer einzigen Stelle erfolgt."

elab "Wir" " entfalten " tgt:ident loc:(locationDE)? new:(becomesDE)? : tactic => do
  let loc? ← loc.mapM locationDE_to_location
  let new? := new.map extractBecomesDE
  unfoldTac tgt loc? new?

elab "Wir" " kontraponieren" : tactic => contraposeTac true

elab "Wir" " kontraponieren" " einfach": tactic => contraposeTac false

elab "Wir " " schieben die Negation " l:(locationDE)? new:(becomesDE)? : tactic => do
  pushNegTac (l.map expandLocation) (new.map extractBecomesDE)

implement_endpoint (lang := de) rwResultWithoutGoal : CoreM String :=
pure "Man kann das Ergebnis der Umschreibung nur angeben, wenn noch etwas zu beweisen ist."

implement_endpoint (lang := de) rwResultSeveralLoc : CoreM String :=
pure "Man kann das Ergebnis der Umschreibung nur angeben, wenn man an einer einzigen Stelle umschreibt."

implement_endpoint (lang := de) cannotContrapose : CoreM String :=
pure "Kontraponieren nicht möglich: Das Hauptziel ist keine Implikation."

setLang de

example (P Q : Prop) (h : P ∨ Q) : True := by
  Wir betrachten mit h
  . intro _hP
    trivial
  . intro _hQ
    trivial


example (P : Prop) : True := by
  Wir unterscheiden ob P
  . intro _hP
    trivial
  . intro _hnP
    trivial

set_option linter.unusedVariables false in
example (P Q R : Prop) (hRP : R → P) (hR : R) (hQ : Q) : P := by
  success_if_fail_with_msg "application type mismatch
  hRP hQ
argument
  hQ
has type
  Q : Prop
but is expected to have type
  R : Prop"
    Wir beenden den Beweis durch hRP angewendet auf hQ
  Wir beenden den Beweis durch hRP angewendet auf hR

example (P : ℕ → Prop) (h : ∀ n, P n) : P 0 := by
  Wir beenden den Beweis durch h angewendet auf _

example (P : ℕ → Prop) (h : ∀ n, P n) : P 0 := by
  Wir beenden den Beweis durch h

example {a b : ℕ}: a + b = b + a := by
  Wir berechnen

example {a b : ℕ} (h : a + b - a = 0) : b = 0 := by
  Wir berechnen in der Annahme h
  Wir beenden den Beweis durch h

addAnonymousComputeLemma abs_sub_le
addAnonymousComputeLemma abs_sub_comm

example {x y : ℝ} : |x - y| = |y - x| := by
  Wir berechnen

example {x y z : ℝ} : |x - y| ≤ |x - z| + |z - y| := by
  Wir berechnen

example {x y z : ℝ} : 2*|x - y| + 3 ≤ 2*(|x - z| + |z - y|) + 3 := by
  Wir berechnen

example (a : ℝ) (h : a ≤ 3) : a + 5 ≤ 3 + 5 := by
  success_if_fail_with_msg "Das Ziel a + 5 ≤ 3 + 5 scheint nicht ohne weiteres aus einer Berechnung zu folgen."
    Wir berechnen
  rel [h]

variable (k : Nat)

example (h : True) : True := by
  Wir beenden den Beweis durch h

example (h : ∀ _n : ℕ, True) : True := by
  Wir beenden den Beweis durch h angewendet auf 0

example (h : True → True) : True := by
  Wir verwenden h
  trivial

example (h : ∀ _n _k : ℕ, True) : True := by
  Wir beenden den Beweis durch h angewendet auf 0 und 1

example (a b : ℕ) (h : a < b) : a ≤ b := by
  Wir beenden den Beweis durch h

example (a b c : ℕ) (h : a < b ∧ a < c) : a ≤ b := by
  Wir beenden den Beweis durch h

example (a b c : ℕ) (h : a ≤ b) (h' : b ≤ c) : a ≤ c := by
  Wir kombinieren h und h'

example (a b c : ℤ) (h : a = b + c) (h' : b - a = c) : c = 0 := by
  Wir kombinieren h und h'

example (a b c : ℕ) (h : a ≤ b) (h' : b ≤ c ∧ a+b ≤ a+c) : a ≤ c := by
  Wir kombinieren h und h'

example (a b c : ℕ) (h : a = b) (h' : a = c) : b = c := by
  Wir umschreiben mit ← h
  Wir beenden den Beweis durch h'

example (a b c : ℕ) (h : a = b) (h' : a = c) : b = c := by
  Wir umschreiben mit h in der Annahme h'
  Wir beenden den Beweis durch h'

example (a b : Nat) (h : a = b) (h' : b = 0): a = 0 := by
  Wir umschreiben mit ← h in der Annahme h' which becomes a = 0
  exact h'

example (a b : Nat) (h : a = b) (h' : b = 0): a = 0 := by
  Wir umschreiben mit ← h in der Annahme h'
  clear h
  exact h'

example (f : ℕ → ℕ) (n : ℕ) (h : n > 0 → f n = 0) (hn : n > 0): f n = 0 := by
  Wir umschreiben mit h
  exact hn

example (f : ℕ → ℕ) (h : ∀ n > 0, f n = 0) : f 1 = 0 := by
  Wir umschreiben mit h
  norm_num

example (a b c : ℕ) (h : a = b) (h' : a = c) : b = c := by
  success_if_fail_with_msg "Der gegebene Term
  a = 0
ist definitionsgemäß nicht gleich dem erwarteten
  b = c"
    Wir umschreiben mit [h] in der Annahme h' which becomes a = 0
  Wir umschreiben mit [h] in der Annahme h' which becomes b = c
  Wir beenden den Beweis durch h'

example (a b c : ℕ) (h : a = b) (h' : a = c) : a = c := by
  Wir umschreiben mit h überall
  Wir beenden den Beweis durch h'

example (P Q : Prop) (h : P → Q) (h' : P) : Q := by
  Wir verwenden h auf h'
  Wir beenden den Beweis durch h

example (P Q R : Prop) (h : P → Q → R) (hP : P) (hQ : Q) : R := by
  Wir beenden den Beweis durch h angewendet auf hP und hQ

-- example (f : ℕ → ℕ) (a b : ℕ) (h : a = b) : f a = f b := by
--   Wir apply f at h
--   Wir beenden den Beweis durch h

example (P : ℕ → Prop) (h : ∀ n, P n) : P 0 := by
  Wir verwenden h auf 0
  Wir beenden den Beweis durch h


example (x : ℝ) : (∀ ε > 0, x ≤ ε) → x ≤ 0 := by
  Wir kontraponieren
  intro h
  use x/2
  constructor
  Wir beenden den Beweis durch h
  Wir beenden den Beweis durch h

example (ε : ℝ) (h : ε > 0) : ε ≥ 0 := by Wir beenden den Beweis durch h
example (ε : ℝ) (h : ε > 0) : ε/2 > 0 := by Wir beenden den Beweis durch h
example (ε : ℝ) (h : ε > 0) : ε ≥ -1 := by Wir beenden den Beweis durch h
example (ε : ℝ) (h : ε > 0) : ε/2 ≥ -3 := by Wir beenden den Beweis durch h

example (x : ℝ) (h : x = 3) : 2*x = 6 := by Wir beenden den Beweis durch h

example (x : ℝ) : (∀ ε > 0, x ≤ ε) → x ≤ 0 := by
  Wir kontraponieren einfach
  intro h
  Wir schieben die Negation
  Wir schieben die Negation in der Annahme h
  use x/2
  constructor
  · Wir beenden den Beweis durch h
  · Wir beenden den Beweis durch h

example (x : ℝ) : (∀ ε > 0, x ≤ ε) → x ≤ 0 := by
  Wir kontraponieren einfach
  intro h
  success_if_fail_with_msg "Der gegebene Term
  0 < x
ist definitionsgemäß nicht gleich dem erwarteten
  ∃ ε > 0, ε < x"
    Wir schieben die Negation which becomes 0 < x
  Wir schieben die Negation which becomes ∃ ε > 0, ε < x
  success_if_fail_with_msg "Der gegebene Term
  ∃ ε > 0, ε < x
ist definitionsgemäß nicht gleich dem erwarteten
  0 < x"
    Wir schieben die Negation in der Annahme h which becomes ∃ ε > 0, ε < x
  Wir schieben die Negation in der Annahme h which becomes 0 < x
  use x/2
  constructor
  · Wir beenden den Beweis durch h
  · Wir beenden den Beweis durch h

def test_ub (A : Set ℝ) (x : ℝ) := ∀ a ∈ A, a ≤ x
def test_sup (A : Set ℝ) (x : ℝ) := test_ub A x ∧ ∀ y, test_ub A y → x ≤ y

example {A : Set ℝ} {x : ℝ} (hx : test_sup A x) :
∀ y, y < x → ∃ a ∈ A, y < a := by
  intro y
  Wir kontraponieren
  rcases hx with ⟨hx₁, hx₂⟩
  exact hx₂ y

set_option linter.unusedVariables false in
example : (∀ n : ℕ, False) → 0 = 1 := by
  Wir kontraponieren
  intro h
  use 1
  Wir berechnen

example (P Q : Prop) (h : P ∨ Q) : True := by
  Wir betrachten mit h
  all_goals
    intro
    trivial

example (P : Prop) (hP₁ : P → True) (hP₂ : ¬ P → True): True := by
  Wir unterscheiden ob P
  intro h
  exact hP₁ h
  intro h
  exact hP₂ h

set_option linter.unusedVariables false

namespace Verbose.German

def f (n : ℕ) := 2*n

example : f 2 = 4 := by
  Wir entfalten f
  rfl

example (h : f 2 = 4) : True → True := by
  Wir entfalten f in der Annahme h
  guard_hyp h :ₛ 2*2 = 4
  exact id

example (h : f 2 = 4) : True → True := by
  success_if_fail_with_msg "hypothesis h has type
  2 * 2 = 4
not
  2 * 2 = 5"
    Wir entfalten f in der Annahme h which becomes 2*2 = 5
  success_if_fail_with_msg "hypothesis h has type
  2 * 2 = 4
not
  Verbose.German.f 2 = 4"
    Wir entfalten f in der Annahme h which becomes f 2 = 4
  Wir entfalten f in der Annahme h which becomes 2*2 = 4
  exact id

set_option linter.unusedTactic false

example (P : ℕ → ℕ → Prop) (h : ∀ n : ℕ, ∃ k, P n k) : True := by
  Wir benennen n um zu p in der Annahme h
  Wir benennen k um zu l in der Annahme h
  guard_hyp_strict h : ∀ p, ∃ l, P p l
  trivial

example (P : ℕ → ℕ → Prop) (h : ∀ n : ℕ, ∃ k, P n k) : True := by
  Wir benennen n um zu p in der Annahme h which becomes ∀ p, ∃ k, P p k
  success_if_fail_with_msg "hypothesis h has type
  ∀ (p : ℕ), ∃ l, P p l
not
  ∀ (p : ℕ), ∃ j, P p j"
    Wir benennen k um zu l in der Annahme h which becomes ∀ p, ∃ j, P p j
  Wir benennen k um zu l in der Annahme h which becomes ∀ p, ∃ l, P p l
  guard_hyp_strict h :  ∀ p, ∃ l, P p l
  trivial

example (P : ℕ → ℕ → Prop) : (∀ n : ℕ, ∃ k, P n k) ∨ True := by
  Wir benennen n um zu p
  Wir benennen k um zu l
  guard_target_strict (∀ p, ∃ l, P p l) ∨ True
  right
  trivial

example (a b c : ℤ) (h1 : a ∣ b) (h2 : b ∣ c) : a ∣ c := by
  rcases h1 with ⟨k, hk⟩
  rcases h2 with ⟨l, hl⟩
  show ∃ k, c = a * k
  Wir benennen k um zu m
  guard_target_strict ∃ m, c = a * m
  use k*l
  rw [hl, hk]
  ring

example (a b c : ℕ) : True := by
  Wir vergessen a
  Wir vergessen b c
  trivial

example (h : 1 + 1 = 2) : True := by
  success_if_fail_with_msg "
'change' tactic failed, pattern
  2 = 3
is not definitionally equal to target
  1 + 1 = 2"
    Wir formulieren h um zu 2 = 3
  Wir formulieren h um zu 2 = 2
  trivial
