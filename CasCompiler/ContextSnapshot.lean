module

public import CasCompiler.Context
public import CasTools.NativeExpression
import all CasTools.NativeExpression

@[expose] public section

namespace CasCompiler.ContextSnapshot

open Lean CasTools

def bindingJson (id : BindingId) : Json :=
  Json.mkObj [("session", toJson id.session), ("serial", toJson id.serial)]

def instancesJson (context : ContextTelescope) : Json :=
  toJson <| context.instances.map fun selected => Json.mkObj [
    ("class", toJson (selected.className.toString (escape := false))),
    ("nativeClass", NativeExpression.nameJson selected.className),
    ("binding", bindingJson selected.binding)]

def retainedDeclarations (terms : Array ClosedTerm) : Array ConstantInfo := Id.run do
  let mut declarations := #[]
  for term in terms do
    for declaration in term.context.nativeDeclarations.constants ++
        term.nativeDeclarations.constants do
      unless declarations.any (nativeConstantExactlyMatches declaration) do
        declarations := declarations.push declaration
  return declarations

def declarationFields [Monad m] (encode : Expr → m Nat) (terms : Array ClosedTerm) :
    m (List (String × Json)) := do
  let declarations := retainedDeclarations terms
  if declarations.isEmpty then return []
  let declarations ← declarations.mapM (NativeExpression.constantInfoJson encode)
  return [("declarations", Json.arr declarations)]

private def contextJsonReference (context : ContextTelescope) : StateM NativeExpression.Builder Json := do
  let entries ← context.entries.mapM fun entry => do
    let type ← NativeExpression.Builder.add entry.type
    let value ← entry.value.mapM NativeExpression.Builder.add
    let originalSource ← entry.originalSource.mapM NativeExpression.Builder.add
    let fields := [
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
    return Json.mkObj (fields ++ originalSource.toList.map fun original =>
      ("originalSource", toJson original))
  return toJson entries

private unsafe def contextJsonCached (context : ContextTelescope) :
    StateM NativeExpression.Builder Json := do
  letI : TypeName ContextTelescope := TypeName.mk ContextTelescope ``ContextTelescope
  NativeExpression.Builder.memoSnapshot ``contextJsonReference context (contextJsonReference context)

@[implemented_by contextJsonCached]
opaque contextJson (context : ContextTelescope) : StateM NativeExpression.Builder Json :=
  contextJsonReference context

def termJson (term : ClosedTerm) (context : Json) (expression type : Nat) : Json :=
  Json.mkObj [
    ("context", context), ("instances", instancesJson term.context),
    ("universeParams", Json.arr (term.universeParams.map NativeExpression.nameJson)),
    ("expression", toJson expression), ("type", toJson type)]

private def closedTermJsonWith
    (encodeContext : ContextTelescope → StateM NativeExpression.Builder Json)
    (term : ClosedTerm) : StateM NativeExpression.Builder Json := do
  let context ← encodeContext term.context
  let expression ← NativeExpression.Builder.add term.expression
  let type ← NativeExpression.Builder.add term.type
  let native := termJson term context expression type
  let declarations ← declarationFields NativeExpression.Builder.add #[term]
  return declarations.foldl (fun document (key, value) => document.setObjVal! key value) native

private def closedTermJsonReference (term : ClosedTerm) : StateM NativeExpression.Builder Json :=
  closedTermJsonWith contextJsonReference term

private unsafe def closedTermJsonCached (term : ClosedTerm) :
    StateM NativeExpression.Builder Json := do
  letI : TypeName ClosedTerm := TypeName.mk ClosedTerm ``ClosedTerm
  NativeExpression.Builder.memoSnapshot ``closedTermJsonReference term (closedTermJsonWith contextJson term)

@[implemented_by closedTermJsonCached]
opaque closedTermJson (term : ClosedTerm) : StateM NativeExpression.Builder Json :=
  closedTermJsonReference term

end CasCompiler.ContextSnapshot
