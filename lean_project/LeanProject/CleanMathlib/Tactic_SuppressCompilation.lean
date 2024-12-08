import Mathlib.Init
import Lean.Elab.Declaration
import Lean.Elab.Notation
open Lean Parser Elab Command
def elabSuppressCompilationDecl : CommandElab := fun
| `($[$doc?:docComment]? $(attrs?)? $(vis?)? $[noncomputable]? $(unsafe?)?
    $(recKind?)? def $id $sig:optDeclSig $val:declVal) => do
  elabDeclaration <| ← `($[$doc?:docComment]? $(attrs?)? $(vis?)? noncomputable $(unsafe?)?
    $(recKind?)? def $id $sig:optDeclSig $val:declVal)
| `($[$doc?:docComment]? $(attrs?)? $(vis?)? $[noncomputable]? $(unsafe?)?
    $(recKind?)? def $id $sig:optDeclSig $val:declVal deriving $derivs,*) => do
  elabDeclaration <| ← `($[$doc?:docComment]? $(attrs?)? $(vis?)? noncomputable $(unsafe?)?
    $(recKind?)? def $id $sig:optDeclSig $val:declVal deriving $derivs,*)
| `($[$doc?:docComment]? $(attrs?)? $(vis?)? $[noncomputable]? $(unsafe?)?
    $(recKind?)? $(attrKind?)? instance $(prio?)? $(id?)? $sig:declSig $val:declVal) => do
  elabDeclaration <| ← `($[$doc?:docComment]? $(attrs?)? $(vis?)? noncomputable $(unsafe?)?
    $(recKind?)? $(attrKind?)? instance $(prio?)? $(id?)? $sig:declSig $val:declVal)
| `($[$doc?:docComment]? $(attrs?)? $(vis?)? $[noncomputable]? $(unsafe?)?
    $(recKind?)? example $sig:optDeclSig $val:declVal) => do
  elabDeclaration <| ← `($[$doc?:docComment]? $(attrs?)? $(vis?)? noncomputable $(unsafe?)?
    $(recKind?)? example $sig:optDeclSig $val:declVal)
| `($[$doc?:docComment]? $(attrs?)? $(vis?)? $[noncomputable]? $(unsafe?)?
    $(recKind?)? abbrev $id $sig:optDeclSig $val:declVal) => do
  elabDeclaration <| ← `($[$doc?:docComment]? $(attrs?)? $(vis?)? noncomputable $(unsafe?)?
    $(recKind?)? abbrev $id $sig:optDeclSig $val:declVal)
| _ => throwUnsupportedSyntax
syntax "unsuppress_compilation" (" in " command)? : command
def expandSuppressCompilationNotation : Macro := fun
| `($[$doc?:docComment]? $(attrs?)? $(attrKind)? notation
    $(prec?)? $(name?)? $(prio?)? $items* => $v) => do
  let defn ← expandNotation <| ← `($[$doc?:docComment]? $(attrs?)? $(attrKind)? notation
    $(prec?)? $(name?)? $(prio?)? $items* => $v)
  `(unsuppress_compilation in $(⟨defn⟩):command)
| _ => Macro.throwUnsupported
macro "suppress_compilation" : command => do
  let declKind := mkIdent ``declaration
  let notaKind := mkIdent ``«notation»
  let declElab := mkCIdent ``elabSuppressCompilationDecl
  let notaMacro := mkCIdent ``expandSuppressCompilationNotation
  `(
  attribute [local command_elab $declKind] $declElab
  attribute [local macro $notaKind] $notaMacro
  )
macro_rules
| `(unsuppress_compilation $[in $cmd?]?) => do
  let declElab := mkCIdent ``elabSuppressCompilationDecl
  let notaMacro := mkCIdent ``expandSuppressCompilationNotation
  let attrCmds ← `(
    attribute [-command_elab] $declElab
    attribute [-macro] $notaMacro
  )
  if let some cmd := cmd? then
    `($attrCmds:command $cmd:command suppress_compilation)
  else
    return attrCmds