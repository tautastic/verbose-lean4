import Verbose.Tactics.Fix

open Lean Elab Tactic

syntax "Sei₁ " colGt fixDecl : tactic
syntax "Sei " (colGt fixDecl)+ : tactic

elab_rules : tactic
  | `(tactic| Sei₁ $x:ident) => Fix1 (introduced.bare x x.getId)

elab_rules : tactic
  | `(tactic| Sei₁ $x:ident : $type) =>
    Fix1 (introduced.typed (mkNullNode #[x, type]) x.getId type)

elab_rules : tactic
  | `(tactic| Sei₁ $x:ident < $bound) =>
    Fix1 (introduced.related (mkNullNode #[x, bound]) x.getId intro_rel.lt bound)

elab_rules : tactic
  | `(tactic| Sei₁ $x:ident > $bound) =>
    Fix1 (introduced.related (mkNullNode #[x, bound]) x.getId intro_rel.gt bound)

elab_rules : tactic
  | `(tactic| Sei₁ $x:ident ≤ $bound) =>
    Fix1 (introduced.related (mkNullNode #[x, bound]) x.getId intro_rel.le bound)

elab_rules : tactic
  | `(tactic| Sei₁ $x:ident ≥ $bound) =>
    Fix1 (introduced.related (mkNullNode #[x, bound]) x.getId intro_rel.ge bound)


elab_rules : tactic
  | `(tactic| Sei₁ $x:ident ∈ $set) =>
    Fix1 (introduced.related (mkNullNode #[x, set]) x.getId intro_rel.mem set)

elab_rules : tactic
  | `(tactic| Sei₁ ( $decl:fixDecl )) => do evalTactic (← `(tactic| Sei₁ $decl:fixDecl))


macro_rules
  | `(tactic| Sei $decl:fixDecl) => `(tactic| Sei₁ $decl)

macro_rules
  | `(tactic| Sei $decl:fixDecl $decls:fixDecl*) => `(tactic| Sei₁ $decl; Sei $decls:fixDecl*)

implement_endpoint (lang := de) noObjectIntro : CoreM String :=
pure "Es gibt hier kein Objekt, das man einführen könnte."

implement_endpoint (lang := de) noHypIntro : CoreM String :=
pure "Es gibt hier keine Annahme, die man einführen könnte."

implement_endpoint (lang := de) negationByContra (hyp : Format) : CoreM String :=
pure s!"Das Ziel ist eine Negation, es hat keinen Sinn, es durch Widerspruch zu beweisen. \
 Sie können direkt annehmen, dass {hyp}."

implement_endpoint (lang := de) wrongNegation : CoreM String :=
pure "Das ist nicht das, was man bei einem Widerspruch annehmen sollte."

macro_rules
| `(ℕ) => `(Nat)

setLang de

example : ∀ b : ℕ, ∀ a : Nat, a ≥ 2 → a = a ∧ b = b := by
  Sei b (a ≥ 2)
  trivial

set_option linter.unusedVariables false in
example : ∀ n > 0, ∀ k : ℕ, ∀ l ∈ (Set.univ : Set ℕ), true := by
  Sei (n > 0) k (l ∈ (Set.univ : Set ℕ))
  trivial

-- FIXME: The next example shows an elaboration issue
/- example : ∀ n > 0, ∀ k : ℕ, ∀ l ∈ (Set.univ : Set ℕ), true := by
  Sei (n > 0) k (l ∈ Set.univ)
  trivial

-- while the following works
example : ∀ n > 0, ∀ k : ℕ, ∀ l ∈ (Set.univ : Set ℕ), true := by
  intro n n_pos k l (hl : l ∈ Set.univ)
  trivial
  -/

set_option linter.unusedVariables false in
example : ∀ n > 0, ∀ k : ℕ, ∀ l ∈ (Set.univ : Set ℕ), true := by
  Sei n
  success_if_fail_with_msg "Es gibt hier kein Objekt, das man einführen könnte."
    Sei h
  intro hn
  Sei k (l ∈ (Set.univ : Set ℕ)) -- same elaboration issue here
  trivial

/-
The next examples show that name shadowing detection does not work.

example : ∀ n > 0, ∀ k : ℕ, true := by
  Sei (n > 0)
  success_if_fail_with_msg ""
    Sei n
  Sei k
  trivial


example : ∀ n > 0, ∀ k : ℕ, true := by
  Sei n > 0
  success_if_fail_with_msg ""
    Sei n
  Sei k
  trivial
 -/

example (k l : ℕ) : ∀ n ≤ k + l, true := by
  Sei n ≤ k + l
  trivial


example (A : Set ℕ) : ∀ n ∈ A, true := by
  Sei n ∈ A
  trivial
