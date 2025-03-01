import Verbose.German.Fix

open Lean Elab Tactic

syntax "Angenommen₁ " colGt assumeDecl : tactic
syntax "Angenommen " "dass"? (colGt assumeDecl)+ : tactic
syntax "Nehmen wir an " "dass"? (colGt assumeDecl)+ : tactic
syntax "Nehmen wir für einen Widerspruch an" (colGt assumeDecl) : tactic

elab_rules : tactic
  | `(tactic| Angenommen₁ $x:ident) => Assume1 (introduced.bare x x.getId)

elab_rules : tactic
  | `(tactic| Angenommen₁ $x:ident : $type) =>
    Assume1 (introduced.typed (mkNullNode #[x, type]) x.getId type)


elab_rules : tactic
  | `(tactic| Angenommen₁ ( $decl:assumeDecl )) => do evalTactic (← `(tactic| Angenommen₁ $decl:assumeDecl))

macro_rules
  | `(tactic| Angenommen $[dass]? $decl:assumeDecl) => `(tactic| Angenommen₁ $decl)
  | `(tactic| Angenommen $[dass]? $decl:assumeDecl $decls:assumeDecl*) => `(tactic| Angenommen₁ $decl; Angenommen $decls:assumeDecl*)

macro_rules
  | `(tactic| Nehmen wir an $[dass]? $decl:assumeDecl) => `(tactic| Angenommen₁ $decl)
  | `(tactic| Nehmen wir an $[dass]? $decl:assumeDecl $decls:assumeDecl*) => `(tactic| Angenommen₁ $decl; Angenommen $decls:assumeDecl*)

elab_rules : tactic
  | `(tactic| Nehmen wir für einen Widerspruch an $x:ident : $type) => forContradiction x.getId type


setLang de

example (P Q : Prop) : P → Q → True := by
  Angenommen hP (hQ : Q)
  trivial

example (P Q : Prop) : P → Q → True := by
  Angenommen dass hP (hQ : Q)
  trivial

example (n : Nat) : 0 < n → True := by
  Angenommen dass hn
  trivial

example : ∀ n > 0, true := by
  success_if_fail_with_msg "Es gibt hier keine Annahme, die man einführen könnte."
    Angenommen n
  intro n
  Angenommen H : n > 0
  trivial


example (P Q : Prop) (h : ¬ Q → ¬ P) : P → Q := by
  Angenommen hP
  Nehmen wir für einen Widerspruch an hnQ :¬ Q
  exact h hnQ hP


example (P Q : Prop) (h : ¬ Q → ¬ P) : P → Q := by
  Angenommen hP
  Nehmen wir für einen Widerspruch an hnQ : ¬ Q
  exact h hnQ hP

example : 0 ≠ 1 := by
  success_if_fail_with_msg
    "Das Ziel ist eine Negation, es hat keinen Sinn, es durch Widerspruch zu beweisen. Sie können direkt annehmen, dass 0 = 1."
    Nehmen wir für einen Widerspruch an h : 0 = 1
  norm_num

example : 0 ≠ 1 := by
  Angenommen h : 0 = 1
  norm_num at h

allowProvingNegationsByContradiction

example : 0 ≠ 1 := by
  Nehmen wir für einen Widerspruch an h : 0 = 1
  norm_num at h
