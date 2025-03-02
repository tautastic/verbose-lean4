import Verbose.Tactics.Common

open Lean

namespace Verbose.German

declare_syntax_cat appliedToDE
syntax "angewendet auf " sepBy(term, " und ") : appliedToDE

def appliedToDETerm : TSyntax `appliedToDE → Array Term
| `(appliedToDE| angewendet auf $[$args]und*) => args
| _ => default -- This will never happen as long as nobody extends appliedToDE

declare_syntax_cat usingStuffDE
syntax " mit " sepBy(term, " und ") : usingStuffDE
syntax " mittels " term : usingStuffDE

def usingStuffDEToTerm : TSyntax `usingStuffDE → Array Term
| `(usingStuffDE| mit $[$args]und*) => args
| `(usingStuffDE| mittels $x) => #[Unhygienic.run `(strongAssumption% $x)]
| _ => default -- This will never happen as long as nobody extends appliedToDE

declare_syntax_cat maybeAppliedDE
syntax term (appliedToDE)? (usingStuffDE)? : maybeAppliedDE

def maybeAppliedDEToTerm : TSyntax `maybeAppliedDE → MetaM Term
| `(maybeAppliedDE| $e:term) => pure e
| `(maybeAppliedDE| $e:term $args:appliedToDE) => `($e $(appliedToDETerm args)*)
| `(maybeAppliedDE| $e:term $args:usingStuffDE) => `($e $(usingStuffDEToTerm args)*)
| `(maybeAppliedDE| $e:term $args:appliedToDE $extras:usingStuffDE) =>
  `($e $(appliedToDETerm args)* $(usingStuffDEToTerm extras)*)
| _ => pure default -- This will never happen as long as nobody extends maybeAppliedDE

/-- Build a maybe applied syntax from a list of term.
When the list has at least two elements, the first one is a function
and the second one is its main arguments.When there is a third element, it is assumed
to be the type of a prop argument. -/
def listTermToMaybeAppliedDE : List Term → MetaM (TSyntax `maybeAppliedDE)
| [x] => `(maybeAppliedDE|$x:term)
| [x, y] => `(maybeAppliedDE|$x:term angewendet auf $y)
| [x, y, z] => `(maybeAppliedDE|$x:term angewendet auf $y mittels $z)
| x::y::l => `(maybeAppliedDE|$x:term angewendet auf $y:term mit [$(.ofElems l.toArray),*])
| _ => pure ⟨Syntax.missing⟩ -- This should never happen

declare_syntax_cat newStuffDE
syntax (ppSpace colGt maybeTypedIdent)* : newStuffDE
syntax maybeTypedIdent "sodass" ppSpace colGt maybeTypedIdent : newStuffDE
syntax maybeTypedIdent "sodass" ppSpace colGt maybeTypedIdent " und "
       ppSpace colGt maybeTypedIdent : newStuffDE

def newStuffDEToArray : TSyntax `newStuffDE → Array MaybeTypedIdent
| `(newStuffDE| $news:maybeTypedIdent*) => Array.map toMaybeTypedIdent news
| `(newStuffDE| $x:maybeTypedIdent sodass $news:maybeTypedIdent) =>
    Array.map toMaybeTypedIdent #[x, news]
| `(newStuffDE| $x:maybeTypedIdent sodass $y:maybeTypedIdent und $z) =>
    Array.map toMaybeTypedIdent #[x, y, z]
| _ => #[]

def listMaybeTypedIdentToNewStuffSuchThatDE : List MaybeTypedIdent → MetaM (TSyntax `newStuffDE)
| [x] => do `(newStuffDE| $(← x.stx):maybeTypedIdent)
| [x, y] => do `(newStuffDE| $(← x.stx):maybeTypedIdent sodass $(← y.stx'))
| [x, y, z] => do `(newStuffDE| $(← x.stx):maybeTypedIdent sodass $(← y.stx) und $(← z.stx))
| _ => pure default

declare_syntax_cat newFactsDE
syntax colGt namedType : newFactsDE
syntax colGt namedType " und "  colGt namedType : newFactsDE
syntax colGt namedType ", "  colGt namedType " und "  colGt namedType : newFactsDE

def newFactsDEToArray : TSyntax `newFactsDE → Array NamedType
| `(newFactsDE| $x:namedType) => #[toNamedType x]
| `(newFactsDE| $x:namedType und $y:namedType) =>
    #[toNamedType x, toNamedType y]
| `(newFactsDE| $x:namedType, $y:namedType und $z:namedType) =>
    #[toNamedType x, toNamedType y, toNamedType z]
| _ => #[]

def newFactsDEToTypeTerm : TSyntax `newFactsDE → MetaM Term
| `(newFactsDE| $x:namedType) => do
    namedTypeToTypeTerm x
| `(newFactsDE| $x:namedType und $y) => do
    let xT ← namedTypeToTypeTerm x
    let yT ← namedTypeToTypeTerm y
    `($xT ∧ $yT)
| `(newFactsDE| $x:namedType, $y:namedType und $z) => do
    let xT ← namedTypeToTypeTerm x
    let yT ← namedTypeToTypeTerm y
    let zT ← namedTypeToTypeTerm z
    `($xT ∧ $yT ∧ $zT)
| _ => throwError "Die Beschreibung der neuen Fakten konnte nicht in einen Term umgewandelt werden."

open Tactic Lean.Elab.Tactic.RCases in
def newFactsDEToRCasesPatt : TSyntax `newFactsDE → RCasesPatt
| `(newFactsDE| $x:namedType) => namedTypeListToRCasesPatt [x]
| `(newFactsDE| $x:namedType und $y:namedType) => namedTypeListToRCasesPatt [x, y]
| `(newFactsDE|  $x:namedType, $y:namedType und $z:namedType) => namedTypeListToRCasesPatt [x, y, z]
| _ => default

declare_syntax_cat newObjectDE
syntax maybeTypedIdent "sodass" maybeTypedIdent : newObjectDE
syntax maybeTypedIdent "sodass" maybeTypedIdent colGt " und " maybeTypedIdent : newObjectDE

def newObjectDEToTerm : TSyntax `newObjectDE → MetaM Term
| `(newObjectDE| $x:maybeTypedIdent sodass $new) => do
    let x' ← maybeTypedIdentToExplicitBinder x
    -- TODOBetter error handling
    let newT := (toMaybeTypedIdent new).2.get!
    `(∃ $(.mk x'), $newT)
| `(newObjectDE| $x:maybeTypedIdent sodass $new₁ und $new₂) => do
    let x' ← maybeTypedIdentToExplicitBinder x
    let new₁T := (toMaybeTypedIdent new₁).2.get!
    let new₂T := (toMaybeTypedIdent new₂).2.get!
    `(∃ $(.mk x'), $new₁T ∧ $new₂T)
| _ => throwError "Die neue Objektbeschreibung konnte nicht in einen Term umgewandelt werden."

-- TODO: create helper functions for the values below
open Tactic Lean.Elab.Tactic.RCases in
def newObjectDEToRCasesPatt : TSyntax `newObjectDE → RCasesPatt
| `(newObjectDE| $x:maybeTypedIdent sodass $new) => maybeTypedIdentListToRCasesPatt [x, new]
| `(newObjectDE| $x:maybeTypedIdent sodass $new₁ und $new₂) => maybeTypedIdentListToRCasesPatt [x, new₁, new₂]
| _ => default

declare_syntax_cat factsDE
syntax term : factsDE
syntax term " und " term : factsDE
syntax term ", " term " und " term : factsDE

def factsDEToArray : TSyntax `factsDE → Array Term
| `(factsDE| $x:term) => #[x]
| `(factsDE| $x:term und $y:term) => #[x, y]
| `(factsDE| $x:term, $y:term und $z:term) => #[x, y, z]
| _ => #[]

def arrayToFactsDE : Array Term → CoreM (TSyntax `factsDE)
| #[x] => `(factsDE| $x:term)
| #[x, y] => `(factsDE| $x:term und $y:term)
| #[x, y, z] => `(factsDE| $x:term, $y:term und $z:term)
| _ => default

end Verbose.German

/-- Convert an expression to a `maybeAppliedDE` syntax object, in `MetaM`. -/
def Lean.Expr.toMaybeAppliedDE (e : Expr) : MetaM (TSyntax `maybeAppliedDE) := do
  let fn := e.getAppFn
  let fnS ← PrettyPrinter.delab fn
  match e.getAppArgs.toList with
  | [] => `(maybeAppliedDE|$fnS:term)
  | [x] => do
      let xS ← PrettyPrinter.delab x
      `(maybeAppliedDE|$fnS:term angewendet auf $xS:term)
  | s => do
      let mut arr : Syntax.TSepArray `term "," := ∅
      for x in s do
        arr := arr.push (← PrettyPrinter.delab x)
      `(maybeAppliedDE|$fnS:term angewendet auf [$arr:term,*])

implement_endpoint (lang := de) nameAlreadyUsed (n : Name) : CoreM String :=
pure s!"Der Name {n} wird bereits genutzt"

implement_endpoint (lang := de) notDefEq (e val : MessageData) : CoreM MessageData :=
pure m!"Der gegebene Term{e}\nist definitionsgemäß nicht gleich dem erwarteten{val}"

implement_endpoint (lang := de) notAppConst : CoreM String :=
pure "Keine Anwendung einer Definition."

implement_endpoint (lang := de) cannotExpand : CoreM String :=
pure "Konnte die Definition des Leitsymbols nicht entfalten."

implement_endpoint (lang := de) doesntFollow (tgt : MessageData) : CoreM MessageData :=
pure m!"Das Folgende scheint nicht unmittelbar aus höchstens einer lokalen Annahme zu folgen: {tgt}"

implement_endpoint (lang := de) couldNotProve (goal : Format) : CoreM String :=
pure s!"Konnte nicht beweisen:\n{goal}"

implement_endpoint (lang := de) failedProofUsing (goal : Format) : CoreM String :=
pure s!"Dies konnte anhand der angegebenen Fakten nicht bewiesen werden.\n{goal}"
