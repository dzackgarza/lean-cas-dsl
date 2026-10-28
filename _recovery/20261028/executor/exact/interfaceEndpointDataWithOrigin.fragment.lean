/-- Project a declared input's endpoint while retaining exact data occurrences.
This shared traversal also serves metadata-only validation: it does not invent
suppliers when the caller has no runtime table. Runtime callers validate complete
coverage before and after projection. A computed anonymous callable uses its
own endpoint reference rather than reconstructing a formal named object. -/
partial def interfaceEndpointDataWithOrigin (objects : InterfaceObjects) (formal : Expr)
    (data : DataOwnership.Data) (source : Bool) (recoverFormal : Bool := true) :
    TermElabM (Except String EndpointProjectionData) := do
  let fieldData := fun (data : DataOwnership.Data) (json : Json) (index : Nat) =>
    ({ json, ownership := DataOwnership.project #[.field "args", .index index]
        data.ownership } : DataOwnership.Data)
  if (data.json.getObjValAs? String "ctor").toOption == some "valueData" then
    let .ok (.inline child) := Backend.ComputationalValue.decode data.json
      | return .error "the input callable envelope is incomplete"
    return (← interfaceEndpointDataWithOrigin objects formal
      (fieldData data child 0) source recoverFormal).map fun endpoint =>
        { endpoint with
          position := endpoint.position.map (fun path => #[.field "args", .index 0] ++ path) }
  match envelope data.json with
  | .ok ("typedMap", #[left, right, _]) | .ok ("arrow", #[left, right, _]) =>
    return .ok {
      data := fieldData data (if source then left else right) (if source then 0 else 1)
      origin := .projection
      position := some #[.field "args", .index (if source then 0 else 1)] }
  | .ok ("identity", #[left, right]) | .ok ("zero", #[left, right]) =>
    return .ok {
      data := fieldData data (if source then left else right) (if source then 0 else 1)
      origin := .projection
      position := some #[.field "args", .index (if source then 0 else 1)] }
  | .ok ("compose", #[first, second]) =>
    let some application ← retainedApplication ``CategoryTheory.CategoryStruct.comp formal
      | return .error "the composed input has no independently retained complete components"
    let fields := application.getAppArgs
    return (← interfaceEndpointDataWithOrigin objects
      (if source then fields[fields.size - 2]! else fields.back!)
      (fieldData data (if source then first else second) (if source then 0 else 1))
      source recoverFormal).map fun endpoint =>
        { endpoint with
          position := endpoint.position.map
            (fun path => #[.field "args", .index (if source then 0 else 1)] ++ path) }
  | .ok ("map", #[action, original]) =>
    let some application ← retainedApplication ``CategoryTheory.Functor.map formal
      | return .error "the mapped input has no independently retained complete action"
    let .ok endpoint ← interfaceEndpointDataWithOrigin objects application.getAppArgs.back!
        (fieldData data original 1) source recoverFormal
      | return .error "the mapped input omitted an original complete endpoint"
    return .ok { origin := .action, data := {
      json := Json.mkObj [("ctor", "functorAction"),
        ("args", Json.arr #[action, endpoint.data.json])]
      ownership := DataOwnership.prefix #[.field "args", .index 0] (fieldData data action 0).ownership ++
        DataOwnership.prefix #[.field "args", .index 1] endpoint.data.ownership } }
  | _ =>
    let some (left, right) := Language.homEnds? (← inferType formal)
      | return .error "the construction input is not a complete callable"
    if recoverFormal then
      if let .ok endpoint ← interfaceEncoding objects (if source then left else right) then
        return .ok { data := { json := endpoint }, origin := .formal }
    return .ok { origin := .projection, data := {
      json := Backend.MorphismEndpoint.encode { callable := data.json, source }
      ownership := DataOwnership.prefix #[.field "args", .index 0] data.ownership } }
