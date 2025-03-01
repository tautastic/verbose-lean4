import DiffEins.Folgen.Skript

Aufgabe "Stetigkeit impliziert sequenzielle Stetigkeit"
  Gegeben: (f : ℝ → ℝ) (u : ℕ → ℝ) (x₀ : ℝ)
  Annahmen: (hu : u konvergiert gegen x₀) (hf : f ist stetig bei x₀)
  Konklusion: (f ∘ u) konvergiert gegen f x₀
Beweis:
  Sei ε > 0
  Durch hf angewendet auf ε mit ε_pos erhalten wir δ sodass
    (δ_pos : δ > 0) und (Hf : ∀ x, |x - x₀| ≤ δ ⇒ |f x - f x₀| ≤ ε)

  Durch hu angewendet auf δ mit δ_pos erhalten wir N sodass
    Hu : ∀ n ≥ N, |u n - x₀| ≤ δ

  Wir beweisen dass N funktioniert
  Sei n ≥ N
  Durch Hf angewendet auf u n genügt es zu beweisen dass |u n - x₀| ≤ δ
  Wir beenden den Beweis durch Hu angewendet auf n mit n_ge
QED

-- Variation without referring to any assumption label
Aufgabe "Stetigkeit impliziert sequenzielle Stetigkeit"
  Gegeben: (f : ℝ → ℝ) (u : ℕ → ℝ) (x₀ : ℝ)
  Annahmen: (hu : u konvergiert gegen x₀) (hf : f ist stetig bei x₀)
  Konklusion: (f ∘ u) konvergiert gegen f x₀
Beweis:
  Sei ε > 0
  Da f ist stetig bei x₀ und ε > 0 erhalten wir δ sodass
    (δ_pos : δ > 0) und (Hf : ∀ x, |x - x₀| ≤ δ ⇒ |f x - f x₀| ≤ ε)
  Da u konvergiert gegen x₀ und δ > 0 erhalten wir N sodass Hu : ∀ n ≥ N, |u n - x₀| ≤ δ
  Wir beweisen dass N funktioniert : ∀ n ≥ N, |f (u n) - f x₀| ≤ ε
  Sei n ≥ N
  Da ∀ x, |x - x₀| ≤ δ → |f x - f x₀| ≤ ε genügt es zu beweisen dass |u n - x₀| ≤ δ
  Da ∀ n ≥ N, |u n - x₀| ≤ δ und n ≥ N folgt das Ziel durch |u n - x₀| ≤ δ
QED

Beispiel "Konstante Folgen konvergieren."
  Gegeben: (u : ℕ → ℝ) (l : ℝ)
  Annahmen: (h : ∀ n, u n = l)
  Konklusion: u konvergiert gegen l
Beweis:
  Sei ε > 0
  Wir beweisen dass ∃ N, ∀ n ≥ N, |u n - l| ≤ ε
  Wir beweisen dass 0 funktioniert
  Sei n ≥ 0
  Berechnung |u n - l| = |l - l| durch h
   _             = 0       durch berechnung
   _             ≤ ε       durch ε_pos
QED

Beispiel "Eine Folge, die auf einen strikt positiven Grenzwert konvergiert, ist strikt positiv."
  Gegeben: (u : ℕ → ℝ) (l : ℝ)
  Annahmen: (hl : l > 0) (h :u konvergiert gegen l)
  Konklusion: ∃ N, ∀ n ≥ N, u n ≥ l/2
Beweis:
  Durch h angewendet auf l/2 mit der Tatsache dass l/2 > 0
    erhalten wir N sodass hN : ∀ n ≥ N, |u n - l| ≤ l/2
  Wir beweisen dass N funktioniert
  Sei n ≥ N
  Durch hN angewendet auf n mit der Tatsache dass n ≥ N
    erhalten wir hN' : |u n - l| ≤ l/2
  Durch hN' erhalten wir (h₁ : -(l/2) ≤ u n - l) (h₂ : u n - l ≤ l/2)
  Wir beenden den Beweis durch h₁
QED


Beispiel "Addition of convergent Folgen."
  Gegeben: (u v : ℕ → ℝ) (l l' : ℝ)
  Annahmen: (hu : u konvergiert gegen l) (hv : v konvergiert gegen l')
  Konklusion: (u + v) konvergiert gegen (l + l')
Beweis:
  Sei ε > 0
  Durch hu angewendet auf ε/2 mit der Tatsache dass ε/2 > 0 erhalten wir N₁
      sodass (hN₁ : ∀ n ≥ N₁, |u n - l| ≤ ε / 2)
  Durch hv angewendet auf ε/2 mit der Tatsache dass ε/2 > 0 erhalten wir N₂
      sodass (hN₂ : ∀ n ≥ N₂, |v n - l'| ≤ ε / 2)
  Wir beweisen dass max N₁ N₂ funktioniert
  Sei n ≥ max N₁ N₂
  Durch n_ge erhalten wir (hn₁ : N₁ ≤ n) (hn₂ : N₂ ≤ n)
  Fakt fact₁ : |u n - l| ≤ ε/2
    durch hN₁ angewendet auf n mit hn₁
  Fakt fact₂ : |v n - l'| ≤ ε/2
    durch hN₂ angewendet auf n mit hn₂
  Berechnung
  |(u + v) n - (l + l')| = |(u n - l) + (v n - l')| durch berechnung
                     _ ≤ |u n - l| + |v n - l'|     durch abs_add
                     _ ≤  ε/2 + ε/2                 durch fact₁ und durch fact₂
                     _ =  ε                         durch berechnung
QED

Beispiel "Das Sandwich Lemma"
  Gegeben: (u v w : ℕ → ℝ) (l : ℝ)
  Annahmen: (hu : u konvergiert gegen l) (hw : w konvergiert gegen l)
    (h : ∀ n, u n ≤ v n)
    (h' : ∀ n, v n ≤ w n)
  Konklusion: v konvergiert gegen l
Beweis:
  Wir beweisen dass ∀ ε > 0, ∃ N, ∀ n ≥ N, |v n - l| ≤ ε
  Sei ε > 0
  Da u konvergiert gegen l und ε > 0
    erhalten wir N sodass hN : ∀ n ≥ N, |u n - l| ≤ ε
  Da w konvergiert gegen l und ε > 0
    erhalten wir N' sodass hN' : ∀ n ≥ N', |w n - l| ≤ ε
  Wir beweisen dass max N N' funktioniert : ∀ n ≥ max N N', |v n - l| ≤ ε
  Sei n ≥ max N N'
  Da n ≥ max N N' erhalten wir (hn : n ≥ N) und (hn' : n ≥ N')
  Da ∀ n ≥ N, |u n - l| ≤ ε und n ≥ N erhalten wir
   (hNl : -ε ≤ u n - l) und (hNd : u n - l ≤ ε)
  Da ∀ n ≥ N', |w n - l| ≤ ε und n ≥ N' erhalten wir
    (hN'l : -ε ≤ w n - l) und (hN'd : w n - l ≤ ε)
  Wir beweisen dass |v n - l| ≤ ε
  Wir beweisen zunächst dass -ε ≤ v n - l
  Berechnung -ε ≤ u n - l durch annahme
      _   ≤ v n - l da u n ≤ v n
  Wir beweisen jetzt dass v n - l ≤ ε
  Berechnung v n - l ≤ w n - l  da v n ≤ w n
      _        ≤ ε        durch annahme
QED

Beispiel "Eine Reformulierung der Definition von Konvergenz."
  Gegeben: (u : ℕ → ℝ) (l : ℝ)
  Annahmen:
  Konklusion: (u konvergiert gegen l) ⇔ ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - l| < ε
Beweis:
  Wir beweisen zunächst dass (u konvergiert gegen l) ⇒ ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - l| < ε
  Angenommen hyp : u konvergiert gegen l
  Sei ε > 0
  Durch hyp angewendet auf ε/2 mit der Tatsache dass ε/2 > 0 erhalten wir N
      sodass hN : ∀ n ≥ N, |u n - l| ≤ ε / 2
  Wir beweisen dass N funktioniert
  Sei n ≥ N
  Berechnung |u n - l| ≤ ε/2  durch hN angewendet auf n mit der Tatsache dass n ≥ N
       _         < ε    da ε > 0
  Wir beweisen jetzt dass (∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - l| < ε) ⇒ u konvergiert gegen l
  Angenommen hyp : ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - l| < ε
  Sei ε > 0
  Durch hyp angewendet auf ε mit ε_pos
    erhalten wir N sodass hN : ∀ n ≥ N, |u n - l| < ε
  Wir beweisen dass N funktioniert
  Sei n ≥ N
  Wir beenden den Beweis durch hN angewendet auf n mit der Tatsache dass n ≥ N
QED


Beispiel "Eindeutigkeit von Grenzwerte."
  Gegeben: (u : ℕ → ℝ) (l l' : ℝ)
  Annahmen: (h : u konvergiert gegen l) (h': u konvergiert gegen l')
  Konklusion: l = l'
Beweis:
  Durch eq_of_forall_dist_le genügt es zu beweisen dass ∀ ε > 0, |l - l'| ≤ ε
  Sei ε > 0
  Durch h angewendet auf ε/2 mit der Tatsache dass ε/2 > 0 erhalten wir N
      sodass hN : ∀ n ≥ N, |u n - l| ≤ ε / 2
  Durch h' angewendet auf  ε/2 mit der Tatsache dass ε/2 > 0 erhalten wir N'
      sodass hN' : ∀ n ≥ N', |u n - l'| ≤ ε / 2
  Durch hN angewendet auf max N N' mit le_max_left _ _
     erhalten wir hN₁ : |u (max N N') - l| ≤ ε / 2
  Durch hN' angewendet auf max N N' mit le_max_right _ _
    erhalten wir hN'₁ : |u (max N N') - l'| ≤ ε / 2
  Berechnung |l - l'| = |(l-u (max N N')) + (u (max N N') -l')|  durch berechnung
  _             ≤ |l - u (max N N')| + |u (max N N') - l'| durch abs_add
  _             = |u (max N N') - l| + |u (max N N') - l'| durch abs_sub_comm
  _             ≤  ε/2 + ε/2                               durch hN₁ und durch hN'₁
  _             = ε                                        durch berechnung
QED

Beispiel "Eine steigende Folge mit einem endlichen Supremum konvergiert gegen dieses."
  Gegeben: (u : ℕ → ℝ) (M : ℝ)
  Annahmen: (h : M ist ein Supremum von u) (h' : u ist steigend)
  Konklusion: u konvergiert gegen M
Beweis:
  Sei ε > 0
  Durch h erhalten wir (inf_M : ∀ (n : ℕ), u n ≤ M)
                   (sup_M_ep : ∀ ε > 0, ∃ (n₀ : ℕ), u n₀ ≥ M - ε)
  Durch sup_M_ep angewendet auf ε mit ε_pos erhalten wir n₀ sodass (hn₀ : u n₀ ≥ M - ε)
  Wir beweisen dass n₀ funktioniert : ∀ n ≥ n₀, |u n - M| ≤ ε
  Sei n ≥ n₀
  Durch inf_M angewendet auf n erhalten wir (inf_M' : u n ≤ M)
  Wir beweisen zunächst dass -ε ≤ u n - M
  · Durch h' angewendet auf n₀ und n mit n_ge erhalten wir h'' : u n₀ ≤ u n
    Berechnung
      -ε ≤ u n₀ - M durch hn₀
      _  ≤ u n - M durch h''
  Wir beweisen jetzt dass u n - M ≤ ε
  · Berechnung
     u n - M ≤ M - M durch inf_M'
     _       = 0     durch berechnung
     _       ≤ ε     durch ε_pos
QED
