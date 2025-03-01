import Verbose.Tactics.Set
import DiffEins.German.Common

elab "Setze " n:maybeTypedIdent " := " val:term : tactic => do
  let (n, ty) := match n with
  | `(maybeTypedIdent| $N:ident) => (N, none)
  | `(maybeTypedIdent|($N : $TY)) => (N, some TY)
  | _ => (default, none)
  setTac n ty val


setLang de

example (a b : ℕ) : ℕ := by
  Setze n := max a b
  success_if_fail_with_msg "Der Name n wird bereits genutzt"
    Setze n := 1
  exact n

example (a b : ℕ) : ℕ := by
  Setze (n : ℕ) := max a b
  exact n

example : ℤ := by
  Setze (n : ℤ) := max 0 1
  exact n
