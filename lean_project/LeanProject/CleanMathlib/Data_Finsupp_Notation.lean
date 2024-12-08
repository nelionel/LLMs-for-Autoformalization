import Mathlib.Data.Finsupp.Defs
namespace Finsupp
open Lean Parser Term
@[nolint docBlame] 
def fun₀.matchAlts : Parser :=
  leading_parser withPosition <| ppRealGroup <| many1Indent (ppSpace >> ppGroup matchAlt)
@[term_parser]
def fun₀ := leading_parser:maxPrec
  ppAllowUngrouped >> unicodeSymbol "λ₀" "fun₀" >> fun₀.matchAlts
local syntax:lead (name := stxSingle₀) "single₀" term:arg term:arg : term
local syntax:lead (name := stxUpdate₀) "update₀" term:arg term:arg term:arg : term
@[term_elab stxSingle₀]
def elabSingle₀ : Elab.Term.TermElab
  | `(term| single₀ $i $x) => fun ty => do Elab.Term.elabTerm (← `(Finsupp.single $i $x)) ty
  | _ => fun _ => Elab.throwUnsupportedSyntax
@[term_elab stxUpdate₀]
def elabUpdate₀ : Elab.Term.TermElab
  | `(term| update₀ $f $i $x) => fun ty => do Elab.Term.elabTerm (← `(Finsupp.update $f $i $x)) ty
  | _ => fun _ => Elab.throwUnsupportedSyntax
macro_rules
  | `(term| fun₀ $x:matchAlt*) => do
    let mut stx : Term ← `(0)
    let mut fst : Bool := true
    for xi in x do
      for xii in (← Elab.Term.expandMatchAlt xi) do
        match xii with
        | `(matchAltExpr| | $pat => $val) =>
          if fst then
            stx ← `(single₀ $pat $val)
          else
            stx ← `(update₀ $stx $pat $val)
          fst := false
        | _ => Macro.throwUnsupported
    pure stx
@[app_unexpander Finsupp.single]
def singleUnexpander : Lean.PrettyPrinter.Unexpander
  | `($_ $pat $val) => `(fun₀ | $pat => $val)
  | _ => throw ()
@[app_unexpander Finsupp.update]
def updateUnexpander : Lean.PrettyPrinter.Unexpander
  | `($_ $f $pat $val) => match f with
    | `(fun₀ $xs:matchAlt*) => `(fun₀ $xs:matchAlt* | $pat => $val)
    | _ => throw ()
  | _ => throw ()
unsafe instance instRepr {α β} [Repr α] [Repr β] [Zero β] : Repr (α →₀ β) where
  reprPrec f p :=
    if f.support.card = 0 then
      "0"
    else
      let ret : Std.Format := f!"fun₀" ++ .nest 2 (
        .group (.join <| f.support.val.unquot.map fun a =>
          .line ++ .group (f!"| {repr a} =>" ++ .line ++ repr (f a))))
      if p ≥ leadPrec then Format.paren ret else ret
extend_docs Finsupp.fun₀ after
  "If the expected type is `Π₀ i, α i` (`DFinsupp`)
  and `Mathlib.Data.DFinsupp.Notation` is imported,
  then this is notation for `DFinsupp.single` and  `Dfinsupp.update` instead."
end Finsupp