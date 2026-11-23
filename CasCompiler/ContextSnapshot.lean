module

public import CasCompiler.Context
public import CasTools.NativeExpression

@[expose] public section

namespace CasCompiler.ContextSnapshot

open Lean CasTools

/-- Stable source identity, shared by the closed telescope and its selected instances. -/
def bindingJson (id : BindingId) : Json :=
  Json.mkObj [("session", toJson id.session), ("serial", toJson id.serial)]

def instancesJson (context : ContextTelescope) : Json :=
  toJson <| context.instances.map fun selected => Json.mkObj [
    ("class", toJson (selected.className.toString (escape := false))),
    ("nativeClass", NativeExpression.nameJson selected.className),
    ("binding", bindingJson selected.binding)]

/-- Preserve the existing question-export schema and each ordered native context entry.
Expression indices belong to the caller's shared NativeExpression builder. -/
def contextJson (context : ContextTelescope) : StateM NativeExpression.Builder Json := do
  let entries ← context.entries.mapM fun entry => do
    let type ← NativeExpression.Builder.add entry.type
    let value ← entry.value.mapM NativeExpression.Builder.add
    return Json.mkObj [
      ("id", bindingJson entry.id), ("name", toJson (entry.userName.toString (escape := false))),
      ("nativeName", NativeExpression.nameJson entry.userName),
      ("role", toJson <| match entry.role with
        | .parameter => "parameter" | .definition => "definition" | .hypothesis => "hypothesis"
        | .instance => "instance" | .selectedStructure => "selectedStructure"
        | .result => "result"),
      ("binderInfo", toJson (reprStr entry.binderInfo)),
      ("nativeBinderInfo", toJson entry.binderInfo),
      ("kind", toJson (reprStr entry.kind)), ("type", toJson type),
      ("value", toJson value), ("nondep", toJson entry.nondep)]
  return toJson entries

/-- Assemble the exact term document from its already encoded context and native roots. -/
def termJson (term : ClosedTerm) (context : Json) (expression type : Nat) : Json :=
  Json.mkObj [
    ("context", context), ("instances", instancesJson term.context),
    ("universeParams", Json.arr (term.universeParams.map NativeExpression.nameJson)),
    ("expression", toJson expression), ("type", toJson type)]

/-- The exact closed term, its complete type, telescope, selected instances and universes.
The ordered telescope supplies the de Bruijn scopes of all stored native expressions. -/
def closedTermJson (term : ClosedTerm) : StateM NativeExpression.Builder Json := do
  let context ← contextJson term.context
  let expression ← NativeExpression.Builder.add term.expression
  let type ← NativeExpression.Builder.add term.type
  return termJson term context expression type

end CasCompiler.ContextSnapshot
