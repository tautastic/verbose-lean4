import Verbose.Tactics.Help
import Verbose.Tactics.Notations
import DiffEins.German.Tactics

open Lean Meta Elab Tactic Term Verbose

namespace Verbose.German

open Lean.Parser.Tactic in
elab "hilfe" h:(colGt ident)? : tactic => do
match h with
| some h => do
        let (s, msg) ← gatherSuggestions (helpAtHyp (← getMainGoal) h.getId)
        if s.isEmpty then
          logInfo (msg.getD "Kein Vorschlag")
        else
          Lean.Meta.Tactic.TryThis.addSuggestions (← getRef) s (header := "Hilfe")
| none => do
   let (s, msg) ← gatherSuggestions (helpAtGoal (← getMainGoal))
   if s.isEmpty then
          logInfo (msg.getD "Kein Vorschlag")
    else
      Lean.Meta.Tactic.TryThis.addSuggestions (← getRef) s (header := "Hilfe")

def describe (t : Format) : String :=
match toString t with
| "ℝ" => "eine reelle Zahl"
| "ℕ" => "eine natürliche Zahl"
| "ℤ" => "eine ganze Zahl"
| t => "ein Ausdruck vom Typ " ++ t

def describe_pl (t : Format) : String :=
match toString t with
| "ℝ" => "reelle Zahlen"
| "ℕ" => "natürliche Zahlen"
| "ℤ" => "ganze Zahlen"
| t => "Ausdrücke vom Typ " ++ t

def libre (s : Ident) : String := s!"Der Name {s.getId} kann frei aus den verfügbaren Namen gewählt werden."

def printIdentList (l : List Ident) : String := commaSep (l.toArray.map (toString ·.getId)) "und"

def libres (ls : List Ident) : String :=
s!"Die Namen {printIdentList ls} können frei aus den verfügbaren Namen gewählt werden."

def describeHypShape (hyp : Name) (headDescr : String) : SuggestionM Unit :=
  pushCom "Die Annahme {hyp} hat die Form «{headDescr}»"

def describeHypStart (hyp : Name) (headDescr : String) : SuggestionM Unit :=
  pushCom "Die Annahme {hyp} beginnt mit «{headDescr}»"

implement_endpoint (lang := de) helpExistRelSuggestion (hyp : Name) (headDescr : String)
    (nameS ineqIdent hS : Ident) (ineqS pS : Term) : SuggestionM Unit := do
  describeHypShape hyp headDescr
  pushCom "Man kann es verwenden mit:"
  pushTac `(tactic|Durch $hyp.ident:term erhalten wir $nameS:ident sodass ($ineqIdent : $ineqS) und ($hS : $pS))
  pushComment <| libres [nameS, ineqIdent, hS]

implement_endpoint (lang := de) helpConjunctionSuggestion (hyp : Name) (h₁I h₂I : Ident) (p₁S p₂S : Term) :
    SuggestionM Unit := do
  let headDescr := "... und ..."
  describeHypShape hyp headDescr
  pushCom "Man kann es verwenden mit:"
  pushTac `(tactic|Durch $hyp.ident:term erhalten wir ($h₁I : $p₁S) ($h₂I : $p₂S))
  pushComment <| libres [h₁I, h₂I]

implement_endpoint (lang := de) helpSinceConjunctionSuggestion (hyp : Name) (h₁I h₂I : Ident) (p₁S p₂S : Term) :
    SuggestionM Unit := do
  let headDescr := "... und ..."
  describeHypShape hyp headDescr
  pushCom "Man kann es verwenden mit:"
  pushTac `(tactic|Da $p₁S:term und $p₂S erhalten wir ($h₁I : $p₁S) und ($h₂I : $p₂S))
  pushComment <| libres [h₁I, h₂I]

implement_endpoint (lang := de) helpDisjunctionSuggestion (hyp : Name) : SuggestionM Unit := do
  describeHypShape hyp "... oder ..."
  pushCom "Man kann es verwenden mit:"
  pushTac `(tactic|Wir betrachten mit $hyp.ident:term)

implement_endpoint (lang := de) helpSinceDisjunctionSuggestion (hyp : Name) (p₁S p₂S : Term) : SuggestionM Unit := do
  describeHypShape hyp "... oder ..."
  pushCom "Man kann es verwenden mit:"
  pushTac `(tactic|Wir unterscheiden ob $p₁S:term oder $p₂S)

implement_endpoint (lang := de) helpImplicationSuggestion (hyp HN H'N : Name) (closes : Bool)
    (le re : Expr) : SuggestionM Unit := do
  pushCom "L'hypothèse {hyp} est une implication"
  if closes then do
    pushCom "La conclusion de cette implication est le but courant"
    pushCom "Wir peut donc utiliser cette hypothèse avec :"
    pushTac `(tactic|Durch $hyp.ident:term genügt es zu beweisen $(← le.stx))
    flush
    pushCom "Si vous disposez déjà d'une preuve {HN} de {← le.fmt} alors on peut utiliser :"
    pushTac `(tactic|Wir beenden den Beweis durch $hyp.ident:term angewendet auf $HN.ident)
  else do
    pushCom "La prémisse de cette implication est {← le.fmt}"
    pushCom "Si vous avez une démonstration {HN} de {← le.fmt}"
    pushCom "vous pouvez donc utiliser cette hypothèse avec :"
    pushTac `(tactic|Durch $hyp.ident:term angewendet auf $HN.ident:term erhalten wir $H'N.ident:ident : $(← re.stx):term)
    pushComment <| libre H'N.ident


implement_endpoint (lang := de) helpEquivalenceSuggestion (hyp hyp'N : Name) (l r : Expr) : SuggestionM Unit := do
  pushCom "L'hypothèse {hyp} est une équivalence"
  pushCom "Wir peut s'en servir pour remplacer le membre de gauche (c'est auf dire {← l.fmt}) par le membre de droite  (c'est auf dire {← r.fmt}) dans le but par :"
  pushTac `(tactic|Wir umschreiben mit $hyp.ident:term)
  flush
  pushCom "Wir peut s'en servir pour remplacer le membre de droite dans par le membre de gauche dans le but par :"
  pushTac `(tactic|Wir umschreiben mit ← $hyp.ident)
  flush
  pushCom "Wir peut aussi effectuer de tels remplacements dans une hypothèse {hyp'N} par"
  pushTac `(tactic|Wir umschreiben mit $hyp.ident:term in der Annahme $hyp'N.ident:ident)
  flush
  pushCom " oder "
  pushTac `(tactic|Wir umschreiben mit ← $hyp.ident:term in der Annahme $hyp'N.ident:ident)

implement_endpoint (lang := de) helpEqualSuggestion (hyp hyp' : Name) (closes : Bool) (l r : Expr) :
    SuggestionM Unit := do
  pushCom "L'hypothèse {hyp} est une égalité"
  if closes then
    pushComment <| s!"Le but courant en découle immédiatement"
    pushComment   "Man kann es verwenden mit :"
    pushTac `(tactic|Wir beenden den Beweis durch $hyp.ident:ident)
  else do
    pushCom "Wir peut s'en servir pour remplacer le membre de gauche (c'est auf dire {l}) par le membre de droite  (c'est auf dire {r}) dans le but par :"
    pushTac `(tactic|Wir umschreiben mit $hyp.ident:ident)
    flush
    pushCom "Wir peut s'en servir pour remplacer le membre de droite dans par le membre de gauche dans le but par :"
    pushTac `(tactic|Wir umschreiben mit ← $hyp.ident:ident)
    flush
    pushCom "Wir peut aussi effectuer de tels remplacements dans une hypothèse {hyp'} par"
    pushTac `(tactic|Wir umschreiben mit $hyp.ident:ident in der Annahme $hyp'.ident:ident)
    flush
    pushCom " oder "
    pushTac `(tactic|Wir umschreiben mit ← $hyp.ident:ident in der Annahme $hyp'.ident:ident)
    flush
    pushCom "Wir peut aussi s'en servir comme étape dans un calcul, oder bien combinée linéairement auf d'autres par :"
    pushTac `(tactic|Wir kombinieren [$hyp.ident:term, ?_])
    pushCom "en remplaçant le point d'interrogation par un oder plusieurs termes prouvant des égalités."

implement_endpoint (lang := de) helpSinceEqualSuggestion (hyp hyp' : Name)
    (closes : Bool) (l r : Expr) (leS reS goalS : Term) : SuggestionM Unit := do
  pushCom "L'hypothèse {hyp} est une égalité"
  if closes then
    pushComment <| s!"Le but courant en découle immédiatement"
    pushComment   "Man kann es verwenden mit :"
    let eq ← `($leS = $reS)
    pushTac `(tactic|Da $eq:term folgt das Ziel durch $goalS)
  else do
    pushCom "Wir peut s'en servir pour remplacer le membre de gauche (c'est auf dire {l}) par le membre de droite  (c'est auf dire {r}) dans le but par :"
    pushTac `(tactic|Wir umschreiben mit $hyp.ident:ident)
    flush
    pushCom "Wir peut s'en servir pour remplacer le membre de droite dans par le membre de gauche dans le but par :"
    pushTac `(tactic|Wir umschreiben mit ← $hyp.ident:ident)
    flush
    pushCom "Wir peut aussi effectuer de tels remplacements dans une hypothèse {hyp'} par"
    pushTac `(tactic|Wir umschreiben mit $hyp.ident:ident in der Annahme $hyp'.ident:ident)
    flush
    pushCom "oder"
    pushTac `(tactic|Wir umschreiben mit ← $hyp.ident:ident in der Annahme $hyp'.ident:ident)
    flush
    pushCom "Wir peut aussi s'en servir comme étape dans un calcul, oder bien combinée linéairement auf d'autres par :"
    pushTac `(tactic|Wir kombinieren [$hyp.ident:term, ?_])
    pushCom "en remplaçant le point d'interrogation par un oder plusieurs termes prouvant des égalités."

implement_endpoint (lang := de) helpIneqSuggestion (hyp : Name) (closes : Bool) : SuggestionM Unit := do
  pushCom "L'hypothèse {hyp} est une inégalité"
  if closes then
    flush
    pushCom "Le but courant en découle immédiatement"
    pushCom "Man kann es verwenden mit :"
    pushTac `(tactic|Wir beenden den Beweis durch $hyp.ident:ident)
  else do
    flush
    pushCom "Wir peut s'en servir comme étape dans un calcul, oder bien combinée linéairement auf d'autres par :"
    pushTac `(tactic|Wir kombinieren [$hyp.ident:term, ?_])
    pushCom "en remplaçant le point d'interrogation par un oder plusieurs termes prouvant des égalités oder inégalités."

implement_endpoint (lang := de) helpMemInterSuggestion (hyp h₁ h₂ : Name) (elemS p₁S p₂S : Term) :
    SuggestionM Unit := do
  pushCom "L'hypothèse {hyp} est une appartenance auf une intersection"
  pushCom "Man kann es verwenden mit :"
  pushTac `(tactic|Durch $hyp.ident:term erhalten wir ($h₁.ident : $elemS ∈ $p₁S) ($h₂.ident : $elemS ∈ $p₂S))
  pushComment <| libres [h₁.ident, h₂.ident]

implement_endpoint (lang := de) helpMemUnionSuggestion (hyp : Name) :
    SuggestionM Unit := do
  pushCom "L'hypothèse {hyp} est une appartenance auf une réunion"
  pushCom "Man kann es verwenden mit :"
  pushTac `(tactic|Wir betrachten mit $hyp.ident)

implement_endpoint (lang := de) helpGenericMemSuggestion (hyp : Name) : SuggestionM Unit := do
  pushCom "L'hypothèse {hyp} est une appartenance"

implement_endpoint (lang := de) helpContradictionSuggestion (hypId : Ident) : SuggestionM Unit := do
  pushComment <| "Cette hypothèse est une contradiction."
  pushCom "Wir peut en déduire tout ce qu'on veut par :"
  pushTac `(tactic|(Wir beweisen dass es ein Widerspruch ist
                    Wir beenden den Beweis durch $hypId:ident))

implement_endpoint (lang := de) helpSubsetSuggestion (hyp x hx hx' : Name)
    (r : Expr) (l ambientTypePP : Format) : SuggestionM Unit := do
  pushCom "L'hypothèse {hyp} affirme l'inclusion de {l} dans {← r.fmt}."
  pushCom "Wir peut s'en servir avec :"
  pushTac `(tactic|Durch $hyp.ident:ident angewendet auf $x.ident mit $hx.ident erhalten wir $hx'.ident:ident : $x.ident ∈ $(← r.stx))
  pushCom "où {x} est {describe ambientTypePP} und {hx} est une démonstration du fait que {x} ∈ {l}"
  pushComment <| libre hx'.ident

implement_endpoint (lang := de) assumptionClosesSuggestion (hypId : Ident) : SuggestionM Unit := do
  pushCom "Cette hypothèse est exactement ce qu'il faut démontrer"
  pushCom "Man kann es verwenden mit :"
  pushTac `(tactic|Wir beenden den Beweis durch $hypId:ident)

implement_endpoint (lang := de) assumptionUnfoldingSuggestion (hypId : Ident) (expandedHypTypeS : Term) :
    SuggestionM Unit := do
  pushCom "Cette hypothèse commence par l'application d'une définition."
  pushCom "Wir peut l'expliciter avec :"
  pushTac `(tactic|Wir formulieren $hypId:ident um zu $expandedHypTypeS)
  flush

implement_endpoint (lang := de) helpForAllRelExistsRelSuggestion (hyp var_name' n₀ hn₀ : Name)
    (headDescr hypDescr : String) (t : Format) (hn'S ineqIdent : Ident) (ineqS p'S : Term) :
    SuggestionM Unit := do
  describeHypStart hyp headDescr
  pushCom "Man kann es verwenden mit:"
  pushTac `(tactic|Durch $hyp.ident:term angewendet auf $n₀.ident mit $hn₀.ident erhalten wir $var_name'.ident:ident sodass ($ineqIdent : $ineqS) und ($hn'S : $p'S))
  pushCom "où {n₀} est {describe t} und {hn₀} est une démonstration du fait que {hypDescr}."
  pushComment <| libres [var_name'.ident, ineqIdent, hn'S]

implement_endpoint (lang := de) helpForAllRelExistsSimpleSuggestion (hyp n' hn' n₀ hn₀ : Name)
    (headDescr n₀rel : String) (t : Format) (p'S : Term) : SuggestionM Unit := do
  describeHypStart hyp headDescr
  pushCom "Man kann es verwenden mit:"
  pushTac `(tactic|Durch $hyp.ident:term angewendet auf $n₀.ident mit $hn₀.ident erhalten wir $n'.ident:ident sodass ($hn'.ident : $p'S))
  pushCom "où {n₀} est {describe t} und h{n₀} est une démonstration du fait que {n₀rel}"
  pushComment <| libres [n'.ident, hn'.ident]

implement_endpoint (lang := de) helpForAllRelGenericSuggestion (hyp n₀ hn₀ : Name)
    (headDescr n₀rel : String) (t : Format) (newsI : Ident) (pS : Term) : SuggestionM Unit := do
  describeHypStart hyp headDescr
  pushCom "Man kann es verwenden mit:"
  pushTac `(tactic|Durch $hyp.ident:term angewendet auf $n₀.ident mit $hn₀.ident erhalten wir ($newsI : $pS))
  pushCom "où {n₀} est {describe t} und {hn₀} est une démonstration du fait que {n₀rel}"
  pushComment <| libre newsI

implement_endpoint (lang := de) helpForAllSimpleExistsRelSuggestion (hyp var_name' nn₀ : Name)
    (headDescr : String) (t : Format) (hn'S ineqIdent : Ident) (ineqS p'S : Term) :
    SuggestionM Unit := do
  describeHypStart hyp headDescr
  pushCom "Man kann es verwenden mit:"
  pushTac `(tactic|Durch $hyp.ident:term angewendet auf $nn₀.ident erhalten wir $var_name'.ident:ident sodass (ineqIdent : $ineqS) und ($hn'S : $p'S))
  pushCom "où {nn₀} est {describe t}"
  pushComment <| libres [var_name'.ident, ineqIdent, hn'S]

implement_endpoint (lang := de) helpForAllSimpleExistsSimpleSuggestion (hyp var_name' hn' nn₀  : Name)
    (headDescr : String) (t : Format) (p'S : Term) : SuggestionM Unit := do
  describeHypStart hyp headDescr
  pushCom "Man kann es verwenden mit:"
  pushTac `(tactic|Durch $hyp.ident:term angewendet auf $nn₀.ident erhalten wir $var_name'.ident:ident sodass ($hn'.ident : $p'S))
  pushCom "où {nn₀} est {describe t}"
  pushComment <| libres [var_name'.ident, hn'.ident]

implement_endpoint (lang := de) helpForAllSimpleForAllRelSuggestion (hyp nn₀ var_name'₀ H h : Name)
    (headDescr rel₀ : String) (t : Format) (p'S : Term) : SuggestionM Unit := do
  describeHypStart hyp headDescr
  pushCom "Man kann es verwenden mit:"
  pushTac `(tactic|Durch $hyp.ident:term angewendet auf $nn₀.ident und $var_name'₀.ident mit $H.ident erhalten wir ($h.ident : $p'S))
  pushCom "où {nn₀} und {var_name'₀} sont {describe_pl t} und {H} est une démonstration de {rel₀}"
  pushComment <| libre h.ident

implement_endpoint (lang := de) helpForAllSimpleGenericSuggestion (hyp nn₀ hn₀ : Name) (headDescr : String)
    (t : Format) (pS : Term) : SuggestionM Unit := do
  describeHypStart hyp headDescr
  pushCom "Man kann es verwenden mit:"
  pushTac `(tactic|Durch $hyp.ident:term angewendet auf $nn₀.ident erhalten wir ($hn₀.ident : $pS))
  pushCom "où {nn₀} est {describe t}"
  pushComment <| libre hn₀.ident
  flush
  pushCom "Si cette hypothèse ne servira plus dans sa forme générale, on peut aussi spécialiser {hyp} par"
  pushTac `(tactic|Wir verwenden $hyp.ident:ident auf $nn₀.ident)

implement_endpoint (lang := de) helpForAllSimpleGenericApplySuggestion (prf : Expr) (but : Format) :
    SuggestionM Unit := do
  let prfS ← prf.toMaybeAppliedDE
  pushCom "Da le but est {but}, on peut utiliser :"
  pushTac `(tactic|Wir beenden den Beweis durch $prfS)

implement_endpoint (lang := de) helpExistsSimpleSuggestion (hyp n hn : Name) (headDescr : String)
    (pS : Term) : SuggestionM Unit := do
  describeHypShape hyp headDescr
  pushCom "Man kann es verwenden mit:"
  pushTac `(tactic| Durch $hyp.ident:term erhalten wir $n.ident:ident sodass ($hn.ident : $pS))
  pushComment <| libres [n.ident, hn.ident]

implement_endpoint (lang := de) helpDataSuggestion (hyp : Name) (t : Format) : SuggestionM Unit := do
  pushComment <| s!"L'objet {hyp}" ++ match t with
          | "ℝ" => " est un nombre réel fixé."
          | "ℕ" => " est un nombre entier naturel fixé."
          | "ℤ" => " est un nombre entier relatif fixé."
          | s => s!" : {s} est fixé."

implement_endpoint (lang := de) helpNothingSuggestion : SuggestionM Unit := do
  pushCom "Je n'ai rien auf déclarer auf propos de cette hypothèse."
  flush

implement_endpoint (lang := de) helpNothingGoalSuggestion : SuggestionM Unit := do
  pushCom "Je n'ai rien auf déclarer auf propos de ce but."
  flush

def descrGoalHead (headDescr : String) : SuggestionM Unit :=
 pushCom "Le but commence par «{headDescr}»"

def descrGoalShape (headDescr : String) : SuggestionM Unit :=
 pushCom "Le but est de la forme «{headDescr}»"

def descrDirectProof : SuggestionM Unit :=
 pushCom "Une démonstration directe commence donc par:"

implement_endpoint (lang := de) helpUnfoldableGoalSuggestion (expandedGoalTypeS : Term) :
    SuggestionM Unit := do
  pushCom "Le but commence par l’application d’une définition."
  pushCom "Wir peut l’expliciter par:"
  pushTac `(tactic|Wir beweisen dass $expandedGoalTypeS)
  flush

implement_endpoint (lang := de) helpAnnounceGoalSuggestion (actualGoalS : Term) : SuggestionM Unit := do
  pushCom "L’étape suivante est d'annoncer:"
  pushTac `(tactic|Wir beweisen jetzt dass $actualGoalS)

implement_endpoint (lang := de) helpFixSuggestion (headDescr : String) (ineqS : TSyntax `fixDecl) :
    SuggestionM Unit := do
  descrGoalHead headDescr
  descrDirectProof
  pushTac `(tactic|Sei $ineqS)

implement_endpoint (lang := de) helpExistsRelGoalSuggestion (headDescr : String) (n₀ : Name) (t : Format)
    (fullTgtS : Term) : SuggestionM Unit := do
  descrGoalHead headDescr
  descrDirectProof
  pushTac `(tactic|Wir beweisen dass $n₀.ident funktioniert: $fullTgtS)
  pushCom "où {n₀} est {describe t}"

implement_endpoint (lang := de) helpExistsGoalSuggestion (headDescr : String) (nn₀ : Name) (t : Format)
    (tgt : Term) : SuggestionM Unit := do
  descrGoalHead headDescr
  descrDirectProof
  pushTac `(tactic|Wir beweisen dass $nn₀.ident funktioniert: $tgt)
  pushCom "où {nn₀} est {describe t}"

implement_endpoint (lang := de) helpConjunctionGoalSuggestion (p p' : Term) : SuggestionM Unit := do
  descrGoalShape "... und ..."
  descrDirectProof
  pushTac `(tactic|Wir beweisen zunächst dass $p)
  pushCom "Une fois cette première démonstration achevée, il restera auf montrer que {← p'.fmt}"
  flush
  pushCom "Wir peut aussi commencer par"
  pushTac `(tactic|Wir beweisen zunächst dass $p')
  pushCom "puis, une fois cette première démonstration achevée, il restera auf montrer que {← p.fmt}"

implement_endpoint (lang := de) helpDisjunctionGoalSuggestion (p p' : Term) : SuggestionM Unit := do
  descrGoalShape "... oder ..."
  pushCom "Une démonstration directe commence donc par annoncer quelle alternative va être démontrée :"
  pushTac `(tactic|Wir beweisen dass $p)
  flush
  pushCom "oder bien :"
  pushTac `(tactic|Wir beweisen dass $p')

implement_endpoint (lang := de) helpImplicationGoalSuggestion (headDescr : String) (Hyp : Name)
    (leStx : Term) : SuggestionM Unit := do
  descrGoalHead headDescr
  descrDirectProof
  pushTac `(tactic|Angenommen $Hyp.ident:ident : $leStx)
  pushComment <| libre Hyp.ident

implement_endpoint (lang := de) helpEquivalenceGoalSuggestion (r l : Format) (rS lS : Term) :
    SuggestionM Unit := do
  pushCom "Le but est une équivalence. Wir peut annoncer la démonstration de l'implication de la gauche vers la droite par :"
  pushTac `(tactic|Wir beweisen dass $lS → $rS)
  pushCom "Une fois cette première démonstration achevée, il restera auf montrer que {r} → {l}"
  flush
  pushCom "Wir peut aussi commencer par"
  pushTac `(tactic|Wir beweisen dass $rS → $lS)
  pushCom "puis, une fois cette première démonstration achevée, il restera auf montrer que {l} → {r}"

implement_endpoint (lang := de) helpSetEqSuggestion (l r : Format) (lS rS : Term) : SuggestionM Unit := do
  -- **FIXME** this discussion isn't easy to do using tactics.
  pushCom "Le but est une égalité entre ensembles"
  pushCom "Wir peut la démontrer par réécriture avec la commande `Wir umschreiben mit`"
  pushCom "oder bien commencer un calcul par"
  pushCom "  calc {l} = sorry := by sorry"
  pushCom "  ... = {r} := by sorry"
  pushCom "Wir peut bien sûr utiliser plus de lignes intermédiaires."
  pushCom "Wir peut aussi la démontrer par double inclusion."
  pushCom "Dans ce cas la démonstration commence par :"
  pushTac `(tactic|Wir beweisen zunächst dass $lS ⊆ $rS)

implement_endpoint (lang := de) helpEqGoalSuggestion (l r : Format) : SuggestionM Unit := do
  -- **FIXME** this discussion isn't easy to do using tactics.
  pushCom "Le but est une égalité"
  pushCom "Wir peut la démontrer par réécriture avec la commande `Wir umschreiben mit`"
  pushCom "oder bien commencer un calcul par"
  pushCom "  calc {l} = sorry := by sorry"
  pushCom "  ... = {r} := by sorry"
  pushCom "Wir peut bien sûr utiliser plus de lignes intermédiaires."
  pushCom "Wir peut aussi tenter des combinaisons linéaires d'hypothèses hyp₁ hyp₂... avec"
  pushCom " Wir kombinieren [hyp₁, hyp₂]"

implement_endpoint (lang := de) helpIneqGoalSuggestion (l r : Format) (rel : String) : SuggestionM Unit := do
  -- **FIXME** this discussion isn't easy to do using tactics.
  pushCom "Le but est une inégalité"
  pushCom "Wir peut commencer un calcul par"
  pushCom "  calc {l}{rel}sorry := by sorry "
  pushCom "  ... = {r} := by sorry "
  pushCom "Wir peut bien sûr utiliser plus de lignes intermédiaires."
  pushCom "La dernière ligne du calcul n'est pas forcément une égalité, cela peut être une inégalité."
  pushCom "De même la première ligne peut être une égalité. Au total les symboles de relations"
  pushCom "doivent s'enchaîner pour donner {rel}"
  pushCom "Wir peut aussi tenter des combinaisons linéaires d'hypothèses hyp₁ hyp₂... avec"
  pushCom " Wir kombinieren [hyp₁, hyp₂]"

implement_endpoint (lang := de) helpMemInterGoalSuggestion (elem le : Expr) : SuggestionM Unit := do
  pushCom "Le but est l'appartenance de {← elem.fmt} auf l'intersection de {← le.fmt} avec un autre ensemble."
  pushCom "Une démonstration directe commence donc par :"
  pushTac `(tactic|Wir beweisen zunächst dass $(← elem.stx) ∈ $(← le.stx))

implement_endpoint (lang := de) helpMemUnionGoalSuggestion (elem le re : Expr) : SuggestionM Unit := do
  pushCom "Le but est l'appartenance de {← elem.fmt} auf la réunion de {← le.fmt} und {← re.fmt}."
  pushCom "Une démonstration directe commence donc par :"
  pushTac `(tactic|Wir beweisen dass $(← elem.stx) ∈ $(← le.stx))
  flush
  pushCom "oder bien par"
  pushTac `(tactic|Wir beweisen dass $(← elem.stx) ∈ $(← re.stx))

implement_endpoint (lang := de) helpNoIdeaGoalSuggestion : SuggestionM Unit := do
  pushCom "Pas d’idée."

implement_endpoint (lang := de) helpSubsetGoalSuggestion (l r : Format) (xN : Name) (lT : Term) :
    SuggestionM Unit := do
  pushCom "Le but est l’inclusion {l} ⊆ {r}"
  pushCom "Une démonstration directe commence donc par:"
  pushTac `(tactic|Sei $xN.ident:ident ∈ $lT)
  pushComment <| libre xN.ident

implement_endpoint (lang := de) helpFalseGoalSuggestion : SuggestionM Unit := do
  pushCom "Le but est de montrer une contradiction."
  pushCom "Wir peut par exemple appliquer une hypothèse qui est une négation"
  pushCom "c'est auf dire, par définition, de la forme P ⇒ False."

implement_endpoint (lang := de) helpContraposeGoalSuggestion : SuggestionM Unit := do
  pushCom "Le but est une implication."
  pushCom "Wir peut débuter une démonstration par contraposition par:"
  pushTac `(tactic|Wir kontraponieren)

implement_endpoint (lang := de) helpByContradictionSuggestion (hyp : Ident) (assum : Term) : SuggestionM Unit := do
  pushCom "Wir peut débuter une démonstration par l’absurde par:"
  pushTac `(tactic|Nehmen wir für einen Widerspruch an $hyp:ident : $assum)

implement_endpoint (lang := de) helpNegationGoalSuggestion (hyp : Ident) (p : Format) (assum : Term) :
    SuggestionM Unit := do
  pushCom "Le but est de montrer la négation de {p}, c’est auf dire montrer que {p} implique une contradiction."
  pushCom "Une démonstration directe commence donc par :"
  pushTac `(tactic|Angenommen $hyp:ident : $assum)
  pushCom "Il restera auf montrer une contradiction."

implement_endpoint (lang := de) helpNeGoalSuggestion (l r : Format) (lS rS : Term) (Hyp : Ident):
    SuggestionM Unit := do
  pushCom "Le but est de montrer la négation de {l} = {r}, c’est auf dire montrer que {l} = {r} implique une contradiction."
  pushCom "Une démonstration directe commence donc par :"
  pushTac `(tactic|Angenommen $Hyp:ident : $lS = $rS)
  pushCom "Il restera auf montrer une contradiction."

set_option linter.unusedVariables false

setLang de

configureAnonymousGoalSplittingLemmas Iff.intro Iff.intro' And.intro And.intro' abs_le_of_le_le abs_le_of_le_le'

configureHelpProviders DefaultHypHelp DefaultGoalHelp

set_option linter.unusedTactic false

/--
info: Hilfe
• Durch h angewendet auf n₀ mit hn₀ erhalten wir (hyp : P n₀)
-/
#guard_msgs in
example {P : ℕ → Prop} (h : ∀ n > 0, P n) : P 2 := by
  hilfe h
  apply h
  norm_num

/--
info: Hilfe
• Durch h erhalten wir n sodass (n_pos : n > 0) und (hn : P n)
-/
#guard_msgs in
example {P : ℕ → Prop} (h : ∃ n > 0, P n) : True := by
  hilfe h
  trivial

/--
info: Hilfe
• Durch h erhalten wir ε sodass (ε_pos : ε > 0) und (hε : P ε)
-/
#guard_msgs in
example {P : ℝ → Prop} (h : ∃ ε > 0, P ε) : True := by
  hilfe h
  trivial

/--
info: Hilfe
• Durch h angewendet auf n₀ erhalten wir (hn₀ : P n₀ ⇒ Q n₀)
• Wir verwenden h auf n₀
-/
#guard_msgs in
example (P Q : ℕ → Prop) (h : ∀ n, P n → Q n) (h' : P 2) : Q 2 := by
  hilfe h
  exact h 2 h'

/--
info: Hilfe
• Durch h angewendet auf n₀ erhalten wir (hn₀ : P n₀)
• Wir verwenden h auf n₀
• Wir beenden den Beweis durch h angewendet auf 2
-/
#guard_msgs in
example (P : ℕ → Prop) (h : ∀ n, P n) : P 2 := by
  hilfe h
  exact h 2

/--
info: Hilfe
• Durch h genügt es zu beweisen P 1
• Wir beenden den Beweis durch h angewendet auf H
-/
#guard_msgs in
example (P Q : ℕ → Prop) (h : P 1 → Q 2) (h' : P 1) : Q 2 := by
  hilfe h
  exact h h'

/--
info: Hilfe
• Durch h angewendet auf H erhalten wir H' : Q 2
-/
#guard_msgs in
example (P Q : ℕ → Prop) (h : P 1 → Q 2) : True := by
  hilfe h
  trivial

/--
info: Hilfe
• Durch h erhalten wir (h_1 : P 1) (h' : Q 2)
-/
#guard_msgs in
example (P Q : ℕ → Prop) (h : P 1 ∧ Q 2) : True := by
  hilfe h
  trivial

/--
info: Hilfe
• Wir umschreiben mit h
• Wir umschreiben mit ← h
• Wir umschreiben mit h in der Annahme hyp
• Wir umschreiben mit ← h in der Annahme hyp
-/
#guard_msgs in
example (P Q : ℕ → Prop) (h : (∀ n ≥ 2, P n) ↔  ∀ l, Q l) : True := by
  hilfe h
  trivial

/--
info: Hilfe
• Wir beweisen zunächst dass True
• Wir beweisen zunächst dass 1 = 1
-/
#guard_msgs in
example : True ∧ 1 = 1 := by
  hilfe
  exact ⟨trivial, rfl⟩

/--
info: Hilfe
• Wir betrachten mit h
-/
#guard_msgs in
example (P Q : ℕ → Prop) (h : P 1 ∨ Q 2) : True := by
  hilfe h
  trivial

/--
info: Hilfe
• Wir beweisen dass True
• Wir beweisen dass False
-/
#guard_msgs in
example : True ∨ False := by
  hilfe
  left
  trivial

/-- info: Je n'ai rien auf déclarer auf propos de cette hypothèse. -/
#guard_msgs in
example (P : Prop) (h : P) : True := by
  hilfe h
  trivial

-- TODO: Improve this help message (low priority since it is very rare)
/--
info: Hilfe
• (
  Wir beweisen dass es ein Widerspruch ist
  Wir beenden den Beweis durch h)
-/
#guard_msgs in
example (h : False) : 0 = 1 := by
  hilfe h
  trivial

/--
info: Hilfe
• Durch h angewendet auf H erhalten wir H' : P l k
-/
#guard_msgs in
example (P : ℕ → ℕ → Prop) (k l n : ℕ) (h : l - n = 0 → P l k) : True := by
  hilfe h
  trivial

/--
info: Hilfe
• Durch h angewendet auf k₀ mit hk₀ erhalten wir n sodass (n_sup : n ≥ 3) und (hn : ∀ (l : ℕ), l - n = 0 ⇒ P l k₀)
-/
#guard_msgs in
example (P : ℕ → ℕ → Prop) (h : ∀ k ≥ 2, ∃ n ≥ 3, ∀ l, l - n = 0 → P l k) : True := by
  hilfe h
  Durch h angewendet auf 2 mit le_rfl erhalten wir n sodass (n_sup : n ≥ 3) und (hn : ∀ (l : ℕ), l - n = 0 → P l 2)
  trivial

/--
info: Hilfe
• Durch h angewendet auf k₀ und n₀ mit H erhalten wir (h_1 : ∀ (l : ℕ), l - n₀ = 0 ⇒ P l k₀)
-/
#guard_msgs in
example (P : ℕ → ℕ → Prop) (h : ∀ k, ∀ n ≥ 3, ∀ l, l - n = 0 → P l k) : True := by
  hilfe h
  trivial

/--
info: Hilfe
• Durch h angewendet auf k₀ mit hk₀ erhalten wir
  n_1 sodass (n_1_sup : n_1 ≥ 3) und (hn_1 : ∀ (l : ℕ), l - n = 0 ⇒ P l k₀)
-/
#guard_msgs in
example (P : ℕ → ℕ → Prop) (n : ℕ) (h : ∀ k ≥ 2, ∃ n ≥ 3, ∀ l, l - n = 0 → P l k) : True := by
  hilfe h
  Durch h angewendet auf 2 mit le_rfl erhalten wir n' sodass (n_sup : n' ≥ 3) und (hn : ∀ (l : ℕ), l - n' = 0 → P l 2)
  trivial

/--
info: Hilfe
• Durch h erhalten wir n sodass (n_sup : n ≥ 5) und (hn : P n)
-/
#guard_msgs in
example (P : ℕ → Prop) (h : ∃ n ≥ 5, P n) : True := by
  hilfe h
  trivial

/--
info: Hilfe
• Durch h angewendet auf k₀ mit hk₀ erhalten wir n sodass (n_sup : n ≥ 3) und (hn : P n k₀)
-/
#guard_msgs in
example (P : ℕ → ℕ → Prop) (h : ∀ k ≥ 2, ∃ n ≥ 3, P n k) : True := by
  hilfe h
  trivial

/--
info: Hilfe
• Durch h erhalten wir n sodass (hn : P n)
-/
#guard_msgs in
example (P : ℕ → Prop) (h : ∃ n : ℕ, P n) : True := by
  hilfe h
  trivial

/--
info: Hilfe
• Durch h angewendet auf k₀ erhalten wir n sodass (hn : P n k₀)
-/
#guard_msgs in
example (P : ℕ → ℕ → Prop) (h : ∀ k, ∃ n : ℕ, P n k) : True := by
  hilfe h
  trivial

/--
info: Hilfe
• Durch h angewendet auf k₀ mit hk₀ erhalten wir n sodass (hn : P n k₀)
-/
#guard_msgs in
example (P : ℕ → ℕ → Prop) (h : ∀ k ≥ 2, ∃ n : ℕ, P n k) : True := by
  hilfe h
  trivial

/--
info: Hilfe
• Wir beweisen dass n₀ funktioniert: P n₀ ⇒ True
-/
#guard_msgs in
example (P : ℕ → Prop): ∃ n : ℕ, P n → True := by
  hilfe
  use 0
  tauto

/--
info: Hilfe
• Angenommen hyp : P
-/
#guard_msgs in
example (P Q : Prop) (h : Q) : P → Q := by
  hilfe
  exact fun _ ↦ h

/--
info: Hilfe
• Sei n ≥ 0
-/
#guard_msgs in
example : ∀ n ≥ 0, True := by
  hilfe
  intros
  trivial

/--
info: Hilfe
• Sei n : ℕ
-/
#guard_msgs in
example : ∀ n : ℕ, 0 ≤ n := by
  hilfe
  exact Nat.zero_le

/--
info: Hilfe
• Wir beweisen dass n₀ funktioniert: 0 ≤ n₀
-/
#guard_msgs in
example : ∃ n : ℕ, 0 ≤ n := by
  hilfe
  use 1
  exact Nat.zero_le 1

/--
info: Hilfe
• Wir beweisen dass n₀ funktioniert: n₀ ≥ 1 ∧ True
-/
#guard_msgs in
example : ∃ n ≥ 1, True := by
  hilfe
  use 1

/-- info: Je n'ai rien auf déclarer auf propos de cette hypothèse. -/
#guard_msgs in
example (h : Odd 3) : True := by
  hilfe h
  trivial

/--
info: Hilfe
• Sei x ∈ s
---
info: Hilfe
• Durch h angewendet auf x_1 mit hx erhalten wir hx' : x_1 ∈ t
-/
#guard_msgs in
example (s t : Set ℕ) (h : s ⊆ t) : s ⊆ t := by
  hilfe
  Sei x ∈ s
  hilfe h
  exact h x_mem

/--
info: Hilfe
• Durch h erhalten wir (h_1 : x ∈ s) (h' : x ∈ t)
-/
#guard_msgs in
example (s t : Set ℕ) (x : ℕ) (h : x ∈ s ∩ t) : x ∈ s := by
  hilfe h
  Durch h erhalten wir (h_1 : x ∈ s) (h' : x ∈ t)
  exact h_1

/--
info: Hilfe
• Durch h erhalten wir (h_1 : x ∈ s) (h' : x ∈ t)
---
info: Hilfe
• Wir beweisen zunächst dass x ∈ t
---
info: Hilfe
• Wir beweisen jetzt dass x ∈ s
-/
#guard_msgs in
example (s t : Set ℕ) (x : ℕ) (h : x ∈ s ∩ t) : x ∈ t ∩ s := by
  hilfe h
  Durch h erhalten wir (h_1 : x ∈ s) (h' : x ∈ t)
  hilfe
  Wir beweisen zunächst dass x ∈ t
  exact h'
  hilfe
  Wir beweisen jetzt dass x ∈ s
  exact h_1

/--
info: Hilfe
• Wir betrachten mit h
---
info: Hilfe
• Wir beweisen dass x ∈ t
• Wir beweisen dass x ∈ s
-/
#guard_msgs in
example (s t : Set ℕ) (x : ℕ) (h : x ∈ s ∪ t) : x ∈ t ∪ s := by
  hilfe h
  Wir betrachten mit h
  Angenommen hyp : x ∈ s
  hilfe
  Wir beweisen dass x ∈ s
  exact hyp
  Angenommen hyp : x ∈ t
  Wir beweisen dass x ∈ t
  exact  hyp

/--
info: Hilfe
• Angenommen hyp : False
-/
#guard_msgs in
example : False → True := by
  hilfe
  simp

/-- info: Je n'ai rien auf déclarer auf propos de ce but. -/
#guard_msgs in
example : True := by
  hilfe
  trivial

configureHelpProviders DefaultHypHelp DefaultGoalHelp helpContraposeGoal

/--
info: Hilfe
• Angenommen hyp : False
• Wir kontraponieren
-/
#guard_msgs in
example : False → True := by
  hilfe
  Wir kontraponieren
  simp

/-- info: Je n'ai rien auf déclarer auf propos de ce but. -/
#guard_msgs in
example : True := by
  hilfe
  trivial

configureHelpProviders DefaultHypHelp DefaultGoalHelp helpByContradictionGoal

/--
info: Hilfe
• Nehmen wir für einen Widerspruch an hyp : ¬True
-/
#guard_msgs in
example : True := by
  hilfe
  trivial

/--
info: Hilfe
• Durch h erhalten wir x_1 sodass (hx_1 : f x_1 = y)
-/
#guard_msgs in
example {X Y} (f : X → Y) (x : X) (y : Y) (h : ∃ x, f x = y) : True := by
  hilfe h
  trivial

/--
info: Hilfe
• Durch h erhalten wir x_1 sodass (x_1_dans : x_1 ∈ s) und (hx_1 : f x_1 = y)
-/
#guard_msgs in
example {X Y} (f : X → Y) (s : Set X) (x : X) (y : Y) (h : ∃ x ∈ s, f x = y) : True := by
  hilfe h
  trivial

/--
info: Hilfe
• Angenommen hyp : P
-/
#guard_msgs in
example (P : Prop) (h : ¬ P) : ¬ P := by
  hilfe
  exact h

/--
info: Hilfe
• Angenommen hyp : x = y
-/
#guard_msgs in
example (x y : ℕ) (h : x ≠ y) : x ≠ y := by
  hilfe
  exact h

allowProvingNegationsByContradiction

/--
info: Hilfe
• Nehmen wir für einen Widerspruch an hyp : P
• Angenommen hyp : P
-/
#guard_msgs in
example (P : Prop) (h : ¬ P) : ¬ P := by
  hilfe
  exact h

/--
info: Hilfe
• Nehmen wir für einen Widerspruch an hyp : x = y
• Angenommen hyp : x = y
-/
#guard_msgs in
example (x y : ℕ) (h : x ≠ y) : x ≠ y := by
  hilfe
  exact h
