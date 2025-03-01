import Verbose.Tactics.By
import Verbose.German.Common

open Lean Verbose.German


elab "Durch " e:maybeAppliedDE " erhalten wir " colGt news:newStuffDE : tactic => do
obtainTac (← maybeAppliedDEToTerm e) (newStuffDEToArray news)

elab "Durch " e:maybeAppliedDE " wählen wir " colGt news:newStuffDE : tactic => do
chooseTac (← maybeAppliedDEToTerm e) (newStuffDEToArray news)

elab "Durch " e:maybeAppliedDE " genügt es zu beweisen " "dass "? colGt arg:term : tactic => do
bySufficesTac (← maybeAppliedDEToTerm e) #[arg]

elab "Durch " e:maybeAppliedDE " genügt es zu beweisen " "dass "? colGt args:sepBy(term, " und ") : tactic => do
bySufficesTac (← maybeAppliedDEToTerm e) args.getElems

elab "assumption'" : tactic => assumption'

macro "annahme" : term => `(by assumption')

lemma le_le_of_abs_le {α : Type*} [LinearOrderedAddCommGroup α] {a b : α} : |a| ≤ b → -b ≤ a ∧ a ≤ b := abs_le.1

lemma le_le_of_max_le {α : Type*} [LinearOrder α] {a b c : α} : max a b ≤ c → a ≤ c ∧ b ≤ c :=
max_le_iff.1

implement_endpoint (lang := de) cannotGet : CoreM String := pure "Das lässt sich nicht ableiten."

implement_endpoint (lang := de) theName : CoreM String := pure "Der Name"

implement_endpoint (lang := de) needName : CoreM String :=
pure "Sie müssen einen Namen für das ausgewählte Objekt angeben."

implement_endpoint (lang := de) wrongNbGoals : CoreM String :=
pure s!"Es gibt nicht so viele Behauptungen zu prüfen."

implement_endpoint (lang := de) doesNotApply (fact : Format) : CoreM String :=
pure s!"Kann {fact} nicht anwenden."

implement_endpoint (lang := de) couldNotInferImplVal (val : Name) : CoreM String :=
pure s!"Konnte keinen impliziten Wert für {val} ableiten."

implement_endpoint (lang := de) alsoNeedCheck (fact : Format) : CoreM String :=
pure s!"Sie müssen auch {fact} prüfen"

configureAnonymousFactSplittingLemmas le_le_of_abs_le le_le_of_max_le

setLang de

example (P : Nat → Prop) (h : ∀ n, P n) : P 0 := by
  Durch h angewendet auf 0 erhalten wir h₀
  exact h₀

example (P : Nat → Nat → Prop) (h : ∀ n k, P n (k+1)) : P 0 1 := by
  Durch h angewendet auf 0 und 0 erhalten wir (h₀ : P 0 1)
  exact h₀

example (n : Nat) (h : ∃ k, n = 2*k) : True := by
  Durch h erhalten wir k sodass (H : n = 2*k)
  trivial

example (n : Nat) (h : ∃ k, n = 2*k) : True := by
  Durch h erhalten wir k sodass H
  trivial

example (P Q : Prop) (h : P ∧ Q)  : Q := by
  Durch h erhalten wir (hP : P) (hQ : Q)
  exact hQ

example (x : ℝ) (h : |x| ≤ 3) : True := by
  Durch h erhalten wir (h₁ : -3 ≤ x) (h₂ : x ≤ 3)
  trivial

example (n p q : ℕ) (h : n ≥ max p q) : True := by
  Durch h erhalten wir (h₁ : n ≥ p) (h₂ : n ≥ q)
  trivial

noncomputable example (f : ℕ → ℕ) (h : ∀ y, ∃ x, f x = y) : ℕ → ℕ := by
  Durch h wählen wir g sodass (H : ∀ (y : ℕ), f (g y) = y)
  exact g

noncomputable example (f : ℕ → ℕ) (A : Set ℕ) (h : ∀ y, ∃ x ∈ A, f x = y) : ℕ → ℕ := by
  Durch h wählen wir g sodass (H : ∀ (y : ℕ), g y ∈ A) und (H' : ∀ (y : ℕ), f (g y) = y)
  exact g

noncomputable example (f : ℕ → ℕ) (A : Set ℕ) (h : ∀ y, ∃ x ∈ A, f x = y) : ℕ → ℕ := by
  Durch h wählen wir g sodass (H : ∀ (y : ℕ), g y + 0 ∈ A) und (H' : ∀ (y : ℕ), f (g y) = y)
  exact g

example (P Q : Prop) (h : P → Q) (h' : P) : Q := by
  Durch h genügt es zu beweisen dass P
  exact h'

example (P Q : Prop) (h : P → Q) (h' : P) : Q := by
  Durch h genügt es zu beweisen P
  exact h'

example (P Q : Prop) (h : P → Q) (h' : P) : Q := by
  Durch h genügt es zu beweisen P
  exact annahme

example (P Q R : Prop) (h : P → R → Q) (hP : P) (hR : R) : Q := by
  Durch h genügt es zu beweisen P und R
  exact hP
  exact hR

set_option linter.unusedVariables false in
example (P Q : Prop) (h : ∀ n : ℕ, P → Q) (h' : P) : Q := by
  success_if_fail_with_msg "Kann h 0 1 nicht anwenden."
    Durch h angewendet auf 0 und 1 genügt es zu beweisen P
  Durch h angewendet auf 0 genügt es zu beweisen P
  exact h'

example (Q : Prop) (h : ∀ n : ℤ, n > 0 → Q)  : Q := by
  Durch h angewendet auf 1 genügt es zu beweisen 1 > 0
  norm_num

example (Q : Prop) (h : ∀ n : ℤ, n > 0 → Q)  : Q := by
  Durch h genügt es zu beweisen 1 > 0
  norm_num

example {P Q R : ℕ → Prop} {n k l : ℕ} (h : ∀ k l, P k → Q l → R n) (hk : P k) (hl : Q l) :
    R n := by
  success_if_fail_with_msg "Sie müssen auch Q ?l prüfen"
    Durch h genügt es zu beweisen P k
  Durch h genügt es zu beweisen P k und Q l
  exact hk
  exact hl

set_option linter.unusedVariables false in
example (n : Nat) (h : ∃ n : Nat, n = n) : True := by
  success_if_fail_with_msg "Der Name n wird bereits genutzt"
    Durch h erhalten wir n sodass H
  trivial
