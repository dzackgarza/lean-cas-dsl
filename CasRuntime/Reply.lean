module

public import CasRuntime.Scope

public section

namespace CasRuntime

open Lean CasCatalogue.Backend

structure ReplyReference where
  path : Array InputPathStep
  binding : ValueBinding

structure ReplyExport where
  token : String
  owner : ConnectionGeneration
  captures : Array ValueBinding

/-- Parsed control authority; prepared-layout and lifecycle admission follow separately. -/
structure ImmediateReply where
  private mk ::
  requestId : Nat
  scopeId : RuntimeId .scope
  value : Json
  exports : Array ReplyExport
  references : Array ReplyReference

private structure ReplyScan where
  references : Array (Array InputPathStep × ScopedReference) := #[]
  tokens : Array String := #[]

/-- Walk the existing JSON packet structure, recognizing only reserved reference/envelope tags.
Reference: CasContract.Port.validateResultRefs and ComputationalValue.decode at f0431beb. -/
private partial def scanReply (value : Json) (path : Array InputPathStep) : Except String ReplyScan := do
  if let some reference ← ScopedReference.parse? value then
    return { references := #[(path, reference)] }
  let tag := (value.getObjValAs? String "ctor").toOption
  if tag == some "deferredData" then
    throw "a deferred control is not an immediate result value"
  if tag == some "opaqueData" || tag == some "valueData" then
    checkServiceFields #["ctor", "args"] value
    match ← ComputationalValue.decode value with
    | .opaque token => return { tokens := #[token] }
    | .inline _ => pure ()
  let mut found : ReplyScan := {}
  match value with
  | .arr values =>
    for index in [:values.size] do
      let child ← scanReply values[index]! (path.push (.index index))
      found := ⟨found.references ++ child.references, found.tokens ++ child.tokens⟩
  | .obj fields =>
    for (name, entry) in fields.toList do
      let child ← scanReply entry (path.push (.field name))
      found := ⟨found.references ++ child.references, found.tokens ++ child.tokens⟩
  | _ => pure ()
  return found

/-- Validate the complete immediate control record before any graph materialization.
Owner identity comes from the actual invocation; capture/reference authority comes from its scope.
Source: execution contract v2 §4.2 and the retained-capture amendment. -/
opaque ImmediateReply.parseControl (scope : RequestScope) (actual : DispatchReservation)
    (graph : ValueGraph) (wireId : String) (expectedRequestId : Nat) (frame : Json) :
    IO ImmediateReply := do
  IO.ofExcept <|
    (checkServiceFields #["request_id", "status", "value", "exports"] frame).mapError IO.userError
  let requestValue ← IO.ofExcept <| (frame.getObjVal? "request_id").mapError IO.userError
  let requestId ← IO.ofExcept <| requestValue.getNat?.mapError IO.userError
  unless requestId == expectedRequestId do
    throw <| IO.userError "the reply request identity does not match its invocation"
  let status ← IO.ofExcept <| (frame.getObjValAs? String "status").mapError IO.userError
  unless status == "ok" do throw <| IO.userError "the control is not an immediate successful reply"
  let value ← IO.ofExcept <| (frame.getObjVal? "value").mapError IO.userError
  let exportValue ← IO.ofExcept <| (frame.getObjVal? "exports").mapError IO.userError
  let declarations ← IO.ofExcept <| exportValue.getArr?.mapError IO.userError
  let mut tokens : Std.HashSet String := {}
  let mut exports : Array ReplyExport := #[]
  for declaration in declarations do
    IO.ofExcept <| (checkServiceFields #["token", "captures"] declaration).mapError IO.userError
    let token ← IO.ofExcept <| (declaration.getObjValAs? String "token").mapError IO.userError
    if token.isEmpty || tokens.contains token then
      throw <| IO.userError "the reply export table has an empty or repeated token"
    tokens := tokens.insert token
    let captureValue ← IO.ofExcept <| (declaration.getObjVal? "captures").mapError IO.userError
    let captures ← IO.ofExcept <| captureValue.getArr?.mapError IO.userError
    let references ← captures.mapM fun capture => do
      let some reference ← IO.ofExcept <| (ScopedReference.parse? capture).mapError IO.userError
        | throw <| IO.userError "an export capture is not a scoped reference"
      return reference
    let retained ← scope.capture actual graph wireId references
    exports := exports.push { token, owner := actual.connection, captures := retained }
  let found ← IO.ofExcept <| (scanReply value #[]).mapError IO.userError
  for token in found.tokens do
    unless tokens.contains token do
      throw <| IO.userError "an opaque result token has no declaration in this reply"
  let bindings ← scope.resolveMany actual graph wireId (found.references.map (·.2))
  let references := found.references.zipWith (fun position binding =>
    { path := position.1, binding : ReplyReference }) bindings
  return ⟨requestId, scope.id, value, exports, references⟩

end CasRuntime
