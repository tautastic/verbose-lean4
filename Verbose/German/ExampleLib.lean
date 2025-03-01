import Mathlib.Topology.MetricSpace.Basic
import Verbose.German.All

def stetige_funktion_bei (f : ℝ → ℝ) (x₀ : ℝ) :=
∀ ε > 0, ∃ δ > 0, ∀ x, |x - x₀| ≤ δ → |f x - f x₀| ≤ ε

def folge_konvergiert_gegen (u : ℕ → ℝ) (l : ℝ) :=
∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - l| ≤ ε

notation:50 f:80 " ist stetig bei " x₀ => stetige_funktion_bei f x₀
notation:50 u:80 " konvergiert gegen " l => folge_konvergiert_gegen u l

def wachsende_folge (u : ℕ → ℝ) := ∀ n m, n ≤ m → u n ≤ u m

notation u " ist wachsend" => wachsende_folge u

def ist_supremum (M : ℝ) (u : ℕ → ℝ) :=
(∀ n, u n ≤ M) ∧ ∀ ε > 0, ∃ n₀, u n₀ ≥ M - ε

notation M " ist ein Supremum von " u => ist_supremum M u

configureUnfoldableDefs stetige_funktion_bei folge_konvergiert_gegen wachsende_folge ist_supremum

section Subset
variable {α : Type*}

/- The Mathlib definition of `Set.Subset` uses a strict-implicit
argument which confuses Verbose Lean. So let us replace it. -/

protected def Verbose.German.Subset (s₁ s₂ : Set α) :=
  ∀ x, x ∈ s₁ → x ∈ s₂

instance (priority := high) Verbose.German.hasSubset : HasSubset (Set α) :=
  ⟨Verbose.German.Subset⟩

end Subset

open Verbose.German

configureAnonymousFactSplittingLemmas le_le_of_abs_le le_le_of_max_le

configureAnonymousGoalSplittingLemmas LogicIntros AbsIntros Set.Subset.antisymm

useDefaultDataProviders

useDefaultSuggestionProviders
