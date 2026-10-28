/-- Whole replies keep their complete invocation endpoints. The shared public
codec reader retains the exact positions of directly projected endpoint fields,
including transparent and composed packets. Only those positions acquire these
already selected occurrences; derived endpoints and matching bytes cannot
select a new producer or typed dependency. -/
partial def endpointValidationScope (scope : ComputationalData.InterfaceScope)
    (wire : Wire) (context : CategoryContext) (formal : Expr)
    (operands : Option (IO.Ref (Array Wire)) := none) :
    TermElabM ComputationalData.InterfaceScope := do
  let some (source, target) ← validationMapEndpoints wire context | return scope
  if let some operands := operands then operands.modify (· ++ #[source, target])
  let source ← endpointValidationView source context wire.morphismFramed
  let target ← endpointValidationView target context wire.morphismFramed
  let mut bindings := scope.bindings
  for (fromSource, endpoint) in #[(true, source), (false, target)] do
    let .ok projected ← ComputationalData.interfaceEndpointDataWithOrigin #[]
        formal scope.data fromSource false | continue
    let some path := projected.position | continue
    let actual ← checkedFragment (scope.data.project path)
    unless projected.data == actual && actual == endpoint.fragment do
      throwStratum .unavailable "the map scope changed an original endpoint packet or supplier"
    let child ← wireValidationScope .object endpoint (operands := operands)
    if let some existing := ComputationalData.InterfaceScope.at? (some scope) path then
      let .ok previous ← ComputationalData.interfaceScopeBinding (some existing) endpoint.json
        | throwStratum .unavailable "the callable field lost its positioned typed producer"
      if let some previous := previous then
        unless ← withoutModifyingState (withTransparency .all <|
            isDefEq previous.expectedType (← inferType endpoint.value) <&&>
              isDefEq previous.formal endpoint.value) do
          throwStratum .unavailable "the endpoint receipt conflicts with its declared typed field"
        match previous.role with
        | .object previous | .map previous =>
          discard <| framingContext (some context) (some previous)
        | .value => pure ()
    -- This explicit endpoint receipt is current authority for this field.
    -- Deeper children stay at their own typed positions; no packet is searched.
    bindings := bindings.filter fun binding => (DataOwnership.stripPrefix? path binding.path).isNone
    bindings := bindings ++ child.bindings.map (fun binding => { binding with path := path ++ binding.path })
  let scope := { scope with bindings }
  discard <| checkedFragment (scope.validate scope.data.json)
  return scope
