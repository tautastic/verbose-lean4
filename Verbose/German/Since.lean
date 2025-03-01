import Verbose.Tactics.Since
import DiffEins.German.Common
import Lean

namespace Verbose.German

open Lean Elab Tactic

elab "Da " facts:factsDE " erhalten wir " news:newObjectDE : tactic => do
  let newsT ← newObjectDEToTerm news
  let news_patt := newObjectDEToRCasesPatt news
  let factsT := factsDEToArray facts
  sinceObtainTac newsT news_patt factsT

elab "Da " facts:factsDE " erhalten wir " news:newFactsDE : tactic => do
  let newsT ← newFactsDEToTypeTerm news
  let news_patt := newFactsDEToRCasesPatt news
  let factsT := factsDEToArray facts
  sinceObtainTac newsT news_patt factsT

elab "Da " facts:factsDE " folgt das Ziel durch " "dass "? concl:term : tactic => do
  let factsT := factsDEToArray facts
  -- dbg_trace "factsT {factsT}"
  sinceConcludeTac concl factsT

elab "Da " facts:factsDE " genügt es zu beweisen dass " newGoals:factsDE : tactic => do
  let factsT := factsDEToArray facts
  let newGoalsT := factsDEToArray newGoals
  sinceSufficesTac factsT newGoalsT

elab "Es genügt zu beweisen dass " newGoals:factsDE : tactic => do
  let newGoalsT := factsDEToArray newGoals
  sinceSufficesTac #[] newGoalsT

elab "Wir unterscheiden ob " factL:term " oder " factR:term : tactic => do
  -- dbg_trace s!"factL {factL}"
  -- dbg_trace s!"factR {factR}"
  sinceDiscussTac factL factR

setLang de

implement_endpoint (lang := de) unusedFact (fact : String) : TacticM String :=
  pure s!"Wir brauchen hier nicht, dass {fact} gilt."

set_option linter.unusedVariables false

example (f : ℝ → ℝ) (hf : ∀ x y, f x = f y → x = y) (x y : ℝ) (hxy : f x = f y) : x = y := by
  Da ∀ x y, f x = f y → x = y und f x = f y folgt das Ziel durch x = y

example (n : Nat) (h : ∃ k, n = 2*k) : True := by
  success_if_fail_with_msg "Der Name h wird bereits genutzt"
    Da ∃ k, n = 2*k erhalten wir k sodass h : n = 2*k
  Da ∃ k, n = 2*k erhalten wir k sodass H : n = 2*k
  trivial

example (n N : Nat) (hn : n ≥ N) (h : ∀ n ≥ N, ∃ k, n = 2*k) : True := by
  success_if_fail_with_msg "Wir brauchen hier nicht, dass n ≥ n gilt."
    Da ∀ n ≥ N, ∃ k, n = 2*k, n ≥ N und n ≥ n erhalten wir k sodass H : n = 2*k
  Da ∀ n ≥ N, ∃ k, n = 2*k und n ≥ N erhalten wir k sodass H : n = 2*k
  trivial

example (P Q : Prop) (h : P ∧ Q)  : Q := by
  Da P ∧ Q erhalten wir (hP : P) und (hQ : Q)
  exact hQ

example (P Q R S : Prop) (h : P ↔ R) (h' : (Q → R) → S) : (Q → P) → S := by
  Da P ↔ R und (Q → R) → S folgt das Ziel durch (Q → P) → S

example (P Q R S : Prop) (h : P ↔ R) (h' : (Q → R) → S) : (Q → P) → S := by
  Da R ↔ P und (Q → R) → S folgt das Ziel durch (Q → P) → S

example (n : Nat) (P : Nat → Prop) (Q : ℕ → ℕ → Prop) (h : P n ∧ ∀ m, Q n m) : Q n n := by
  Da P n ∧ ∀ m, Q n m erhalten wir (hQ : ∀ m, Q n m)
  apply hQ

example (n : ℕ) (hn : n > 2) (P : ℕ → Prop) (h : ∀ n ≥ 3, P n) : True := by
  Da ∀ n ≥ 3, P n und n ≥ 3 erhalten wir H : P n
  trivial

example (n : ℕ) (hn : n > 2) (P Q : ℕ → Prop) (h : ∀ n ≥ 3, P n ∧ Q n) : True := by
  Da ∀ n ≥ 3, P n ∧ Q n und n ≥ 3 erhalten wir H : P n und H' : Q n
  trivial

example (n : ℕ) (hn : n > 2) (P : ℕ → Prop) (h : ∀ n ≥ 3, P n) : P n := by
  Da ∀ n ≥ 3, P n und n ≥ 3 folgt das Ziel durch P n

example (n : ℕ) (hn : n > 2) (P Q : ℕ → Prop) (h : ∀ n ≥ 3, P n ∧ Q n) : P n := by
  Da ∀ n ≥ 3, P n ∧ Q n und n ≥ 3 folgt das Ziel durch P n

example (n : ℕ) (hn : n > 2) (P Q : ℕ → Prop) (h : ∀ n ≥ 3, P n ∧ Q n) : True := by
  Da ∀ n ≥ 3, P n ∧ Q n und n ≥ 3 erhalten wir H : P n
  trivial

example (n : ℕ) (hn : n > 2) (P Q : ℕ → Prop) (h : ∀ n ≥ 3, P n) (h' : ∀ n ≥ 3, Q n) : True := by
  Da ∀ n ≥ 3, P n, ∀ n ≥ 3, Q n und n ≥ 3 erhalten wir H : P n und H' : Q n
  trivial

example (P Q : Prop) (h : P → Q) (h' : P) : Q := by
  Da P → Q genügt es zu beweisen dass P
  exact h'

example (P Q R : Prop) (h : P → R → Q) (hP : P) (hR : R) : Q := by
  Da P → R → Q genügt es zu beweisen dass P und R
  exact hP
  exact hR

example (P Q R S : Prop) (h : P → R → Q → S) (hP : P) (hR : R) (hQ : Q) : S := by
  Da P → R → Q → S genügt es zu beweisen dass P, R und Q
  exact hP
  exact hR
  exact hQ

example (P Q : Prop) (h : P ↔ Q) (hP : P) : Q := by
  Da P ↔ Q genügt es zu beweisen dass P
  exact hP

example (P Q : Prop) (h : P ↔ Q) (hP : P) : Q ∧ True:= by
  constructor
  Da P ↔ Q genügt es zu beweisen dass P
  exact hP
  trivial

example (P : ℕ → Prop) (x y : ℕ) (h : x = y) (h' : P x) : P y := by
  success_if_fail_with_msg "
Konnte nicht beweisen:
P : ℕ → Prop
x y : ℕ
GivenFact_0 : x = y
⊢ P y"
    Da x = y erhalten wir H : P y
  Da x = y und P x erhalten wir H : P y
  exact H

example (P : ℕ → Prop) (x y : ℕ) (h : x = y) (h' : P x) : P y := by
  Da x = y und P x folgt das Ziel durch P y

example (P : ℕ → Prop) (x y : ℕ) (h : x = y) (h' : P x) : P y := by
  Da x = y genügt es zu beweisen dass P x
  exact h'

-- example (n : ℤ) : Even (n^2) → Even n := by
--   contrapose
--   have := @Int.not_even_iff_odd
--   Da (¬ Even n ↔ Odd n) und (¬ Even (n^2) ↔ Odd (n^2)) genügt es zu beweisen dass Odd n → Odd (n^2)
--   rintro ⟨k, rfl⟩
--   use 2*k*(k+1)
--   ring

example (ε : ℝ) (ε_pos : ε > 0) : ε ≥ 0 := by
  Da ε > 0 folgt das Ziel durch ε ≥ 0

example (f : ℕ → ℕ) (x y : ℕ) (h : x = y) : f x ≤ f y := by
  Da x = y folgt das Ziel durch f x ≤ f y

configureAnonymousCaseSplittingLemmas le_or_gt lt_or_gt_of_ne lt_or_eq_of_le eq_or_lt_of_le Classical.em

example (P Q : Prop) (h : P ∨ Q) : True := by
  Wir unterscheiden ob P oder Q
  all_goals tauto

example (P Q : Prop) (h : P ∨ Q) : True := by
  Wir unterscheiden ob Q oder P
  all_goals tauto

example (P : Prop) : True := by
  Wir unterscheiden ob P oder ¬ P
  all_goals tauto

example (x y : ℕ) : True := by
  Wir unterscheiden ob x ≤ y oder x > y
  all_goals tauto

example (x y : ℕ) : True := by
  Wir unterscheiden ob x = y oder x ≠ y
  all_goals tauto

example (x y : ℕ) (h : x ≠ y) : True := by
  Wir unterscheiden ob x < y oder x > y
  all_goals tauto

example (ε : ℝ) (h : ε > 0) : ε ≥ 0 := by
  success_if_fail_with_msg "Konnte nicht beweisen:
ε : ℝ
SufficientFact_0 : ε < 0
⊢ ε ≥ 0"
    Es genügt zu beweisen dass ε < 0
  Es genügt zu beweisen dass ε > 0
  exact h

lemma le_le_of_max_le' {α : Type*} [LinearOrder α] {a b c : α} : max a b ≤ c → a ≤ c ∧ b ≤ c :=
max_le_iff.1

configureAnonymousFactSplittingLemmas le_max_left le_max_right le_le_of_max_le' le_of_max_le_left le_of_max_le_right

example (n a b : ℕ) (h : n ≥ max a b) : True := by
  Da n ≥ max a b erhalten wir H : n ≥ a und H' : n ≥ b
  trivial

example (n a b : ℕ) (h : n ≥ max a b) : True := by
  Da n ≥ max a b erhalten wir H : n ≥ a
  trivial

example (n a b : ℕ) (h : n ≥ max a b) (P : ℕ → Prop) (hP : ∀ n ≥ a, P n) : P n := by
  Da ∀ n ≥ a, P n und n ≥ a folgt das Ziel durch P n

set_option linter.unusedVariables false in
example (a b : ℕ) (P : ℕ → Prop) (h : ∀ n ≥ a, P n) : True := by
  Da ∀ n ≥ a, P n und max a b ≥ a erhalten wir H : P (max a b)
  trivial

example (a b : ℝ) (h : a + b ≤ 3) (h' : b ≥ 0) : b*(a + b) ≤ b*3 := by
  success_if_fail_with_msg "
Konnte nicht beweisen:
a b : ℝ
GivenFact_0 : a + b ≤ 3
⊢ b * (a + b) ≤ b * 3"
    Da a + b ≤ 3 folgt das Ziel durch b*(a + b) ≤ b*3
  Da a + b ≤ 3 und b ≥ 0 folgt das Ziel durch b*(a + b) ≤ b*3

example (a b : ℝ) (hb : b = 2) : a + a*b = a + a*2 := by
  Da b = 2 folgt das Ziel durch a + a*b = a + a*2

example (P Q R S T : Prop) (hPR : P ↔ R) : ((Q → R) → S) ↔ ((Q → P) → S) := by
  -- simp only [hPR]
  Da P ↔ R folgt das Ziel durch ((Q → R) → S) ↔ ((Q → P) → S)

example (a k : ℤ) (h : a = 0*k) : a = 0 := by
  Da a = 0*k folgt das Ziel durch a = 0

local macro_rules | `($x ∣ $y)   => `(@Dvd.dvd ℤ Int.instDvd ($x : ℤ) ($y : ℤ))

example (a : ℤ) (h : a = 0) : a ∣ 0 := by
  success_if_fail_with_msg "
Konnte nicht beweisen:
a : ℤ
GivenFact_0 : a = 0
⊢ a ∣ 0"
    Da a = 0 folgt das Ziel durch a ∣ 0
  Da a = 0 genügt es zu beweisen dass 0 ∣ 0
  use 0
  rfl

example (P Q : Prop) (hP : P) (hQ : Q) : P ∧ Q := by
  Da P und Q folgt das Ziel durch P ∧ Q

example (P Q : Prop) (hPQ : P → Q) (hQP : Q → P) : P ↔ Q := by
  Da P → Q und Q → P folgt das Ziel durch P ↔ Q

example (P Q : Prop) (hPQ : P ↔ Q) : True := by
  Da P ↔ Q erhalten wir h : P → Q und h' : Q → P
  trivial

private lemma test_abs_le_of_le_le {α : Type*} [LinearOrderedAddCommGroup α] {a b : α}
    (h : -b ≤ a) (h' : a ≤ b) : |a| ≤ b := abs_le.2 ⟨h, h'⟩

private lemma test_abs_le_of_le_le' {α : Type*} [LinearOrderedAddCommGroup α] {a b : α}
    (h' : a ≤ b) (h : -b ≤ a) : |a| ≤ b := abs_le.2 ⟨h, h'⟩

private lemma test_abs_le_of_le_and_le {α : Type*} [LinearOrderedAddCommGroup α] {a b : α}
    (h : -b ≤ a ∧ a ≤ b) : |a| ≤ b := abs_le.2 h

configureAnonymousGoalSplittingLemmas test_abs_le_of_le_le test_abs_le_of_le_le' test_abs_le_of_le_and_le

example (a b : ℝ) (h : a - b ≥ -1) (h' : a - b ≤ 1) : |a - b| ≤ 1 := by
  Da (-1 ≤ a - b ∧ a - b ≤ 1) → |a - b| ≤ 1 genügt es zu beweisen dass -1 ≤ a - b ∧ a - b ≤ 1
  exact ⟨h, h'⟩

example (a b : ℝ) (h : a - b ≥ -1) (h' : a - b ≤ 1) : |a - b| ≤ 1 := by
  Da (-1 ≤ a - b ∧ a - b ≤ 1) → |a - b| ≤ 1 genügt es zu beweisen dass -1 ≤ a - b und a - b ≤ 1
  all_goals assumption

example (a b : ℝ) (h : a - b ≥ -1) (h' : a - b ≤ 1) : |a - b| ≤ 1 := by
  Da -1 ≤ a - b → a - b ≤ 1 → |a - b| ≤ 1 genügt es zu beweisen dass -1 ≤ a - b und a - b ≤ 1
  all_goals assumption

example (u v : ℕ → ℝ) (h : ∀ n, u n ≤ v n) : u 0 - 2 ≤ v 0 - 2 := by
  Da ∀ n, u n ≤ v n folgt das Ziel durch u 0 - 2 ≤ v 0 - 2
