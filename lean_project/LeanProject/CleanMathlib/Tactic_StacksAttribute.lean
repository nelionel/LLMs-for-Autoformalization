import Lean.Elab.Command
import Mathlib.Init
open Lean Elab
namespace Mathlib.StacksTag
inductive Database where
  | kerodon
  | stacks
  deriving BEq, Hashable
structure Tag where
  declName : Name
  database : Database
  tag : String
  comment : String
  deriving BEq, Hashable
initialize tagExt : SimplePersistentEnvExtension Tag (Std.HashSet Tag) ←
  registerSimplePersistentEnvExtension {
    addImportedFn := fun as => as.foldl Std.HashSet.insertMany {}
    addEntryFn := .insert
  }
def addTagEntry {m : Type → Type} [MonadEnv m]
    (declName : Name) (db : Database) (tag comment : String) : m Unit :=
  modifyEnv (tagExt.addEntry ·
    { declName := declName, database := db, tag := tag, comment := comment })
open Parser
abbrev stacksTagKind : SyntaxNodeKind := `stacksTag
def stacksTagFn : ParserFn := fun c s =>
  let i := s.pos
  let s := takeWhileFn (fun c => c.isAlphanum) c s
  if s.hasError then
    s
  else if s.pos == i then
    ParserState.mkError s "stacks tag"
  else
    let tag := Substring.mk c.input i s.pos |>.toString
    if !tag.all fun c => c.isDigit || c.isUpper then
      ParserState.mkUnexpectedError s
        "Stacks tags must consist only of digits and uppercase letters."
    else if tag.length != 4 then
      ParserState.mkUnexpectedError s "Stacks tags must be exactly 4 characters"
    else
      mkNodeToken stacksTagKind i c s
@[inherit_doc stacksTagFn]
def stacksTagNoAntiquot : Parser := {
  fn   := stacksTagFn
  info := mkAtomicInfo "stacksTag"
}
@[inherit_doc stacksTagFn]
def stacksTagParser : Parser :=
  withAntiquot (mkAntiquot "stacksTag" stacksTagKind) stacksTagNoAntiquot
end Mathlib.StacksTag
open Mathlib.StacksTag
def Lean.TSyntax.getStacksTag (stx : TSyntax stacksTagKind) : CoreM String := do
  let some val := Syntax.isLit? stacksTagKind stx | throwError "Malformed Stacks tag"
  return val
namespace Lean.PrettyPrinter
namespace Formatter
@[combinator_formatter stacksTagNoAntiquot] def stacksTagNoAntiquot.formatter :=
  visitAtom stacksTagKind
end Formatter
namespace Parenthesizer
@[combinator_parenthesizer stacksTagNoAntiquot] def stacksTagAntiquot.parenthesizer := visitToken
end Lean.PrettyPrinter.Parenthesizer
namespace Mathlib.StacksTag
declare_syntax_cat stacksTagDB
syntax "kerodon" : stacksTagDB
syntax "stacks" : stacksTagDB
syntax (name := stacksTag) stacksTagDB stacksTagParser (ppSpace str)? : attr
initialize Lean.registerBuiltinAttribute {
  name := `stacksTag
  descr := "Apply a Stacks or Kerodon project tag to a theorem."
  add := fun decl stx _attrKind => do
    let oldDoc := (← findDocString? (← getEnv) decl).getD ""
    let (SorK, database, url, tag, comment) := ← match stx with
      | `(attr| stacks $tag $[$comment]?) =>
        return ("Stacks", Database.stacks, "https://stacks.math.columbia.edu/tag", tag, comment)
      | `(attr| kerodon $tag $[$comment]?) =>
        return ("Kerodon", Database.kerodon, "https://kerodon.net/tag", tag, comment)
      | _ => throwUnsupportedSyntax
    let tagStr ← tag.getStacksTag
    let comment := (comment.map (·.getString)).getD ""
    let commentInDoc := if comment = "" then "" else s!" ({comment})"
    let newDoc := [oldDoc, s!"[{SorK} Tag {tagStr}]({url}/{tagStr}){commentInDoc}"]
    addDocString decl <| "\n\n".intercalate (newDoc.filter (· != ""))
    addTagEntry decl database tagStr <| comment
}
end Mathlib.StacksTag
private def Lean.Environment.getSortedStackProjectTags (env : Environment) : Array Tag :=
  tagExt.getState env |>.toArray.qsort (·.tag < ·.tag)
private def Lean.Environment.getSortedStackProjectDeclNames (env : Environment) (tag : String) :
    Array Name :=
  let tags := env.getSortedStackProjectTags
  tags.filterMap fun d => if d.tag == tag then some d.declName else none
namespace Mathlib.StacksTag
private def databaseURL (db : Database) : String :=
  match db with
  | .kerodon => "https://kerodon.net/tag/"
  | .stacks => "https://stacks.math.columbia.edu/tag/"
def traceStacksTags (db : Database) (verbose : Bool := false) :
    Command.CommandElabM Unit := do
  let env ← getEnv
  let entries := env.getSortedStackProjectTags |>.filter (·.database == db)
  if entries.isEmpty then logInfo "No tags found." else
  let mut msgs := #[m!""]
  for d in entries do
    let (parL, parR) := if d.comment.isEmpty then ("", "") else (" (", ")")
    let cmt := parL ++ d.comment ++ parR
    msgs := msgs.push
      m!"[Stacks Tag {d.tag}]({databaseURL db ++ d.tag}) \
        corresponds to declaration '{.ofConstName d.declName}'.{cmt}"
    if verbose then
      let dType := ((env.find? d.declName).getD default).type
      msgs := (msgs.push m!"{dType}").push ""
  let msg := MessageData.joinSep msgs.toList "\n"
  logInfo msg
elab (name := stacksTags) "#stacks_tags" tk:("!")?: command =>
  traceStacksTags .stacks (tk.isSome)
elab (name := kerodonTags) "#kerodon_tags" tk:("!")?: command =>
  traceStacksTags .kerodon (tk.isSome)
end Mathlib.StacksTag