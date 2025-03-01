import Verbose.Tactics.Lets
import Mathlib.Tactic.Linarith

elab "Wir beweisen" " mit Induktion" name:ident ":" stmt:term : tactic =>
letsInduct name.getId stmt

open Lean Elab Tactic in

macro "Wir beweisen" " dass " stmt:term :tactic =>
`(tactic| first | show $stmt | apply Or.inl; show $stmt | apply Or.inr; show $stmt | fail "Das ist nicht das, was bewiesen werden muss. Meinten Sie: “Wir beweisen zunächst dass”?")

declare_syntax_cat explicitStmtDE
syntax ": " term : explicitStmtDE

def toStmt (e : Lean.TSyntax `explicitStmtDE) : Lean.Term := ⟨e.raw[1]!⟩

elab "Wir beweisen" " dass " witness:term " funktioniert" stmt:(explicitStmtDE)?: tactic => do
  useTac witness (stmt.map toStmt)

elab "Wir beweisen" " zunächst dass " stmt:term : tactic =>
  anonymousSplitLemmaTac stmt

elab "Wir beweisen" " jetzt dass " stmt:term : tactic =>
  unblockTac stmt

syntax "Sie müssen ankündigen: Wir zeigen jetzt dass " term : term

open Lean Parser Term PrettyPrinter Delaborator in
@[delab app.goalBlocker]
def goalBlocker_delab : Delab := whenPPOption Lean.getPPNotation do
  let stx ← SubExpr.withAppArg delab
  `(Sie müssen ankündigen: Wir zeigen jetzt dass $stx)

macro "Wir beweisen" " dass es ein Widerspruch ist" : tactic => `(tactic|exfalso)

open Lean

implement_endpoint (lang := de) inductionError : CoreM String :=
pure "Die Aussage muss mit einem Allquantor auf eine natürliche Zahl beginnen."

implement_endpoint (lang := de) notWhatIsNeeded : CoreM String :=
pure "Dies ist nicht das, was zu beweisen ist."

implement_endpoint (lang := de) notWhatIsRequired : CoreM String :=
pure "Das ist nicht das, was jetzt gebraucht wird."

setLang de

example : 1 + 1 = 2 := by
  Wir beweisen dass 2 = 2
  rfl

example : ∃ k : ℕ, 4 = 2*k := by
  Wir beweisen dass 2 funktioniert
  rfl

example : ∃ k : ℕ, 4 = 2*k := by
  Wir beweisen dass 2 funktioniert: 4 = 2*2
  rfl

example : True ∧ True := by
  Wir beweisen zunächst dass True
  trivial
  Wir beweisen jetzt dass True
  trivial

example (P Q : Prop) (h : P) : P ∨ Q := by
  Wir beweisen dass P
  exact h

example (P Q : Prop) (h : Q) : P ∨ Q := by
  Wir beweisen dass Q
  exact h

example : 0 = 0 ∧ 1 = 1 := by
  Wir beweisen zunächst dass 0 = 0
  trivial
  Wir beweisen jetzt dass 1 = 1
  trivial

example : (0 : ℤ) = 0 ∧ 1 = 1 := by
  Wir beweisen zunächst dass 0 = 0
  trivial
  Wir beweisen jetzt dass 1 = 1
  trivial

example : 0 = 0 ∧ 1 = 1 := by
  Wir beweisen zunächst dass 1 = 1
  trivial
  Wir beweisen jetzt dass 0 = 0
  trivial

example : True ↔ True := by
  Wir beweisen zunächst dass True → True
  exact id
  Wir beweisen jetzt dass True → True
  exact id

example (h : False) : 2 = 1 := by
  Wir beweisen dass es ein Widerspruch ist
  exact h

example (P : Nat → Prop) (h₀ : P 0) (h : ∀ n, P n → P (n+1)) : P 4 := by
  Wir beweisen mit Induktion H : ∀ k, P k
  . exact h₀
  . intro k hyp_rec
    exact h k hyp_rec

example (P : Nat → Prop) (h₀ : P 0) (h : ∀ n, P n → P (n+1)) : ∀ k, P k := by
  Wir beweisen mit Induktion H : ∀ k, P k
  . exact h₀
  . intro k hyp_rec
    exact h k hyp_rec

example (P : ℕ → Prop) (h₀ : P 0) (h : ∀ n, P n → P (n+1)) : P 3 := by
  success_if_fail_with_msg "Die Aussage muss mit einem Allquantor auf eine natürliche Zahl beginnen."
    Wir beweisen mit Induktion H : true
  Wir beweisen mit Induktion H : ∀ n, P n
  exact h₀
  exact h

set_option linter.unusedVariables false in
example (P : ℕ → Prop) (h₀ : P 0) (h : ∀ n, P n → P (n+1)) : True := by
  Wir beweisen mit Induktion H : ∀ k, P k
  exacts [h₀, h, trivial]

example : True := by
  Wir beweisen mit Induktion H : ∀ l, l < l + 1
  decide
  intro l
  intros hl
  linarith
  trivial

set_option linter.unusedVariables false in
example : True := by
  success_if_fail_with_msg "Die Aussage muss mit einem Allquantor auf eine natürliche Zahl beginnen."
    Wir beweisen mit Induktion H : true
  success_if_fail_with_msg "Die Aussage muss mit einem Allquantor auf eine natürliche Zahl beginnen."
    Wir beweisen mit Induktion H : ∀ n : ℤ, true
  trivial

example (P Q : Prop) (h : P ∧ Q) : P ∧ Q := by
  constructor
  Wir beweisen zunächst dass P
  exact h.1
  Wir beweisen jetzt dass Q
  exact h.2
