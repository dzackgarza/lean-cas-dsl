module

import CasCatalogue.Realize
meta import CasCatalogue.Realize

open Lean Meta Elab Command Term
open CasCatalogue CasCatalogue.Language CasCatalogue.Realize

/- These are framing and type-preservation checks. They make no mathematical
acceptance claim about a leaf or a computed answer. -/
run_cmd liftTermElabM do
  let state ← registryState
  let some sets := state.categories.find? (·.id == CategoryId.sets)
    | throwError "the admission probe has no registered category"
  let some cardinality := state.methods.find? fun entry =>
      entry.name == "cardinality" && entry.owner.syntacticEq sets.expression
    | throwError "the admission probe has no existing generic method"
  let some object := state.objects.find? fun entry =>
      entry.category == sets.id && entry.refines.isNone
    | throwError "the admission probe has no existing object"
  let some image := state.functors.find? (·.target.syntacticEq sets.expression)
    | throwError "the admission probe has no registered object-producing action"
  let some construction := state.limits.find? (·.category == sets.id)
    | throwError "the admission probe has no complete construction"
  for form in #[Form.object object, .functorImage image sets.id, .limitApex construction] do
    let addresses := state.inputAddresses (.method cardinality) form
    unless addresses == #[form.id, sets.id.raw] do
      throwError "a complete object representation lost its category-wide generic registration"
  let addresses := state.inputAddresses (.method cardinality) (.diagrams sets)
  unless addresses == #[sets.id.raw] do
    throwError "a category-wide input address was duplicated"
  let some action := state.functors.find? (·.source.syntacticEq sets.expression)
    | throwError "the admission probe has no existing direct functor"
  unless state.accepts (.functor action) (.diagrams sets) do
    throwError "a generic functor could not register its full source category"
  let some named := state.morphisms.find? (·.category == sets.id)
    | throwError "the invocation probe has no published named callable"
  let some application := state.objects.find? fun entry =>
      entry.category == sets.id && entry.application.isSome
    | throwError "the invocation probe has no published object application"
  let some binder := state.binders.find? (·.category == sets.id)
    | throwError "the invocation probe has no published binder"
  for operation in #[Operation.morphism named, .application application, .binder binder] do
    unless state.inputAddresses operation (.diagrams sets) == #[sets.id.raw] &&
        state.pointInputAddresses operation (.diagrams sets) == #[sets.id.raw, operation.id] do
      throwError "complete point invocation lost its own request form or changed ordinary input matching"
    let some request := state.form? operation.id
      | throwError "the callable's own request form is absent from the public inventory"
    unless (state.pointInputAddresses operation request).toList.eraseDups.length ==
        (state.pointInputAddresses operation request).size do
      throwError "complete callable request matching duplicated an address"

run_cmd liftTermElabM do
  let node (tag : String) (args : Array Json) :=
    Json.mkObj [("ctor", toJson tag), ("args", Json.arr args)]
  let source := node "obj.sets.fin" #[toJson (2 : Nat)]
  let target := node "obj.sets.fin" #[toJson (3 : Nat)]
  let typedMap : Backend.TypedMap := { source, target, callable := node "opaqueData" #[toJson "map"] }
  let .ok decoded := Backend.TypedMap.decode typedMap.encode
    | throwError "the public typed map did not round trip its framing"
  unless decoded.source == source && decoded.target == target && decoded.callable == typedMap.callable do
    throwError "typed map framing changed a complete endpoint or callable"
  for bad in #[node "typedMap" #[source, target], node "typedMap" #[source, target, typedMap.callable, source]] do
    if (Backend.TypedMap.decode bad).isOk then
      throwError "typed map framing accepted missing or additional fields"
  unless (Backend.PortError.unsupported "op.probe").stratum == .noImplementation &&
      (Backend.PortError.protocol "framing").stratum == .malformed &&
      (Backend.PortError.backend "failure" "backend").stratum == .unavailable do
    throwError "port failures collapsed distinct execution strata"
  let validManifest := Json.mkObj [("backends", Json.arr #[Json.mkObj [
    ("name", toJson "public-specimen"), ("command", toJson "python3"),
    ("args", Json.arr #[toJson "backend/leaf.py"])]]),
    ("registrations", Json.arr #[Json.mkObj [("operation", toJson "meth.cardinality"),
      ("input", toJson "obj.sets.fin"), ("backend", toJson "public-specimen")]])]
  let .ok manifest := Manifest.parse validManifest
    | throwError "the published complete backend manifest did not parse"
  unless manifest.backends.size == 1 && manifest.registrations.size == 1 do
    throwError "manifest parsing dropped public program or registration data"
  for malformed in #[Json.null, Json.arr #[], toJson (2 : Nat),
      Json.mkObj [("backends", Json.null)],
      Json.mkObj [("backends", Json.arr #[Json.mkObj [
        ("name", toJson "public-specimen"), ("command", toJson "python3"),
        ("args", Json.arr #[toJson (7 : Nat)])]])]] do
    if (Manifest.parse malformed).isOk then
      throwError "the manifest accepted data outside its published JSON schema"

run_cmd liftTermElabM do
  let node (tag : String) (args : Array Json) :=
    Json.mkObj [("ctor", toJson tag), ("args", Json.arr args)]
  let degreeType ← elabTermAndSynthesize (← `(WithBot Nat)) none
  for data in #[node "none" #[], node "some" #[toJson (8 : Nat)]] do
    let .ok value ← Codec.decode degreeType data
      | throwError "the generic optional data encoding lost a bottom-valued degree"
    unless ← isTypeCorrect value do throwError "a decoded degree is not typed"
  let .error _ ← Codec.decode degreeType (node "none" #[toJson (8 : Nat)])
    | throwError "a nullary bottom constructor accepted an extra field"
  let rational ← elabTermAndSynthesize (← `((0 : Rat))) none
  let rationalType ← inferType rational
  let .ok () ← ComputationalData.validatePort rational rationalType
      (Json.arr #[toJson (-3 : Int), toJson (7 : Nat)])
    | throwError "public scalar record data were not structurally validated"
  let .error _ ← ComputationalData.validatePort rational rationalType
      (Json.arr #[toJson (-3 : Int)])
    | throwError "a scalar record omitted a required public data field"
  for malformed in #[Json.arr #[toJson (-3 : Int), toJson (0 : Nat)],
      Json.arr #[toJson (2 : Int), toJson (4 : Nat)],
      Json.arr #[toJson "numerator", toJson (7 : Nat)],
      Json.arr #[toJson (-3 : Int), toJson (-7 : Int)]] do
    let .error _ ← ComputationalData.validatePort rational rationalType malformed
      | throwError "a scalar literal violated its independently declared representation constraints"
  let rationalWithOpaque := Json.arr #[node "opaqueData" #[toJson "owned-numerator"],
    toJson (7 : Nat)]
  let .ok () ← ComputationalData.validatePort rational rationalType rationalWithOpaque
    | throwError "scalar literal checking attempted to reconstruct an owned opaque field"
  let natural ← elabTermAndSynthesize (← `((0 : Nat))) none
  let naturalType ← inferType natural
  for valid in #[toJson (9 : Nat), node "valueData" #[toJson (9 : Nat)],
      node "valueData" #[node "valueData" #[toJson (9 : Nat)]],
      node "opaqueData" #[toJson "owned-natural"]] do
    let .ok () ← ComputationalData.validateElementAt naturalType Json.null natural valid
      | throwError "the exact scalar result interface lost a permitted computational envelope"
  for malformed in #[toJson "9", Json.arr #[toJson (9 : Nat)], toJson (-1 : Int),
      node "true" #[], node "valueData" #[], node "opaqueData" #[toJson ""],
      node "valueData" #[toJson "9"],
      node "arrow" #[node "obj.sets.fin" #[toJson (1 : Nat)],
        node "obj.sets.fin" #[toJson (1 : Nat)], node "opaqueData" #[toJson "callable"]],
      node "subobject" #[node "obj.sets.fin" #[toJson (1 : Nat)],
        node "obj.sets.fin" #[toJson (1 : Nat)], node "opaqueData" #[toJson "callable"]]] do
    let .error _ ← ComputationalData.validateElementAt naturalType Json.null natural malformed
      | throwError "the exact scalar result interface accepted a wrong kind or shape"
  let matrixType ← elabTermAndSynthesize (← `(Fin 2 → Fin 2 → Int)) none
  let row := Json.arr #[Json.arr #[toJson (0 : Nat), toJson (11 : Int)],
    Json.arr #[toJson (1 : Nat), toJson (-4 : Int)]]
  let matrix := Json.arr #[Json.arr #[toJson (0 : Nat), row], Json.arr #[toJson (1 : Nat), row]]
  let .ok value ← Codec.decode matrixType matrix
    | throwError "nested finite callable data did not decode a matrix type"
  unless ← isTypeCorrect value do throwError "a decoded matrix is not typed"
  let some schema ← ComputationalData.pointSchema matrixType
    | throwError "the matrix's public function fields have no computational schema"
  let opaqueRow := node "opaqueData" #[toJson "row-in-original-session"]
  let retained := Json.arr #[Json.arr #[toJson (0 : Nat), opaqueRow],
    Json.arr #[toJson (1 : Nat), row]]
  let .ok () ← ComputationalData.validatePoint schema retained
    | throwError "a nested callable lost its permitted opaque computational representation"
  for bad in #[Json.arr #[Json.arr #[toJson (0 : Nat), row]],
      Json.arr #[Json.arr #[toJson (0 : Nat), row], Json.arr #[toJson (0 : Nat), row]],
      Json.arr #[Json.arr #[toJson (0 : Nat), node "opaqueData" #[toJson ""]],
        Json.arr #[toJson (1 : Nat), row]]] do
    let .error _ ← ComputationalData.validatePoint schema bad
      | throwError "malformed nested callable data were accepted"

run_cmd liftTermElabM do
  let node (tag : String) (args : Array Json) :=
    Json.mkObj [("ctor", toJson tag), ("args", Json.arr args)]
  let endpoint := node "obj.sets.fin" #[toJson (2 : Nat)]
  let wrong := node "obj.sets.fin" #[toJson (3 : Nat)]
  let formal ← elabTermAndSynthesize (← `(TypeCat.ofHom (fun x : Fin 2 => x))) none
  let graph := Json.arr #[Json.arr #[toJson (0 : Nat), toJson (1 : Nat)],
    Json.arr #[toJson (1 : Nat), toJson (0 : Nat)]]
  let typed := (Backend.TypedMap.mk endpoint endpoint graph).encode
  if let .error message ← ComputationalData.validateEndpointPort formal endpoint endpoint typed then
    throwError "a typed computational graph lost its actual endpoint inventories: {message}"
  let .error _ ← ComputationalData.validateEndpointPort formal endpoint endpoint
      (Backend.TypedMap.mk endpoint wrong graph).encode
    | throwError "a typed map changed its exact computational codomain"
  let .error _ ← ComputationalData.validateEndpointPort formal endpoint endpoint
      (Backend.TypedMap.mk endpoint endpoint (Json.arr #[Json.arr #[toJson (0 : Nat), toJson (0 : Nat)]])).encode
    | throwError "a typed map omitted a point of its actual computational domain"

run_cmd liftTermElabM do
  let state ← registryState
  let sets ← categoryNamed state "Sets"
  let rings ← categoryNamed state "Rings"
  let selected ← (object state "ZMod" #[.nat 5] (some rings)).run {}
  let carrier ← (carrierObject selected).run {}
  let expected ← (semanticObject carrier).run {}
  let trace ← Trace.new
  let decoders : ElementData.Decoders := {
    application := fun declaration expected parameters =>
      return (← decodeDeclaration declaration expected parameters (decodeValue trace sets)).map (·.1)
    point := fun _ _ data => decodeArrowData trace sets data }
  let node (tag : String) (args : Array Json) :=
    Json.mkObj [("ctor", toJson tag), ("args", Json.arr args)]
  let descriptor := node "obj.rings.integers_mod" #[toJson (5 : Nat)]
  let expression := node "operationExpression" #[toJson "op.rings.pow",
    Json.arr #[descriptor, toJson (3 : Nat)], Json.arr #[node "numeral" #[toJson (2 : Nat)]]]
  let decoded ← ElementData.decode selected descriptor expected
    (node "element" #[descriptor, expression]) decoders
  let point ← match decoded with
    | some (.ok point) => pure point
    | some (.error message) => throwError "operation expression decoding failed: {message}"
    | none => throwError "the public element envelope was not recognized"
  unless ← isTypeCorrect point do throwError "the operation expression produced an untyped point"
  let formalPoint ← (toElement (.nat 0) carrier).run {}
  let .element formalPoint _ := formalPoint
    | throwError "the framing probe did not retain its fixed point interface"
  let selectedObject ← (semanticObject selected).run {}
  let .ok () ← ComputationalData.validateElementAt selectedObject descriptor formalPoint
      (node "element" #[descriptor, expression])
    | throwError "the data-only element validator rejected the released expression grammar"
  for bad in #[toJson "a parameter string is not an element expression", toJson (3 : Nat),
      descriptor, node "point" #[toJson "not a callable"],
      node "point" #[descriptor], node "point" #[node "true" #[]],
      node "point" #[node "compose" #[node "opaqueData" #[toJson "owned-point"], descriptor]],
      node "add" #[node "numeral" #[toJson (2 : Nat)]]] do
    let .error _ ← ComputationalData.validateElementAt selectedObject descriptor formalPoint
        (node "element" #[descriptor, bad])
      | throwError "an element envelope accepted malformed expression data"
  let .error _ ← ComputationalData.validateElementAt selectedObject descriptor formalPoint
      (node "element" #[node "obj.rings.integers_mod" #[toJson (7 : Nat)], expression])
    | throwError "the data-only element validator changed the exact selected endpoint"
  for bad in #[node "operationExpression" #[toJson "mor.sets.divide", Json.arr #[], Json.arr #[]],
      node "operationExpression" #[toJson "op.rings.pow",
        Json.arr #[node "obj.rings.integers_mod" #[toJson (7 : Nat)], toJson (3 : Nat)],
        Json.arr #[node "numeral" #[toJson (2 : Nat)]]],
      node "operationExpression" #[toJson "op.rings.pow", Json.arr #[descriptor], Json.arr #[]]] do
    let some (.error _) ← ElementData.decode selected descriptor expected
        (node "element" #[descriptor, bad]) decoders
      | throwError "an operation expression changed its registered id, selection or declared arity"

run_cmd liftTermElabM do
  let state ← registryState
  let sets ← categoryNamed state "Sets"
  let trace ← Trace.new
  let node (tag : String) (args : Array Json) :=
    Json.mkObj [("ctor", toJson tag), ("args", Json.arr args)]
  let selectedRing := node "obj.rings.integers_mod" #[toJson (5 : Nat)]
  let reals := node "obj.sets.reals" #[]
  let point (n : Nat) := node "element" #[reals, node "numeral" #[toJson n]]
  let power := node "op.rings.pow" #[selectedRing, toJson (3 : Nat)]
  let integral := node "bind.sets.integral" #[point 2, point 5]
  let application := node "obj.sets.matrices#application" #[toJson (2 : Nat),
    node "obj.commutative_rings.rationals" #[]]
  let inclusion := node "incl.sets.reals_complexes" #[]
  for data in #[power, integral, application, inclusion] do
    let arrow ← match ← decodeArrowData trace sets data with
      | .ok arrow => pure arrow
      | .error message => throwError "callable decoding failed for {data.compress}: {message}"
    unless ← isTypeCorrect arrow do throwError "a callable descriptor did not produce a typed arrow"
    let expected ← inferType arrow
    let atExpected ← match ← decodeValue trace sets expected data with
      | .ok (atExpected, _) => pure atExpected
      | .error message => throwError "callable type checking failed for {data.compress}: {message}"
    unless ← isDefEq (← inferType atExpected) expected do
      throwError "a callable descriptor changed its complete expected type"
    let .ok () ← ComputationalData.validatePublicData data
      | throwError "the computational framing validator rejected a released callable address"
  for malformed in #[node "op.rings.pow" #[selectedRing],
      node "bind.sets.integral" #[point 2],
      node "obj.sets.matrices#application" #[toJson (2 : Nat)],
      node "incl.sets.reals_complexes" #[toJson (2 : Nat)]] do
    let .error _ ← decodeArrowData trace sets malformed
      | throwError "a callable descriptor omitted or added a declaration parameter"
  let expression := node "operationExpression" #[toJson "op.rings.pow",
    Json.arr #[selectedRing, toJson (3 : Nat)], Json.arr #[node "numeral" #[toJson (2 : Nat)]]]
  let .error _ ← decodeArrowData trace sets expression
    | throwError "an applied element expression was retyped as an unapplied callable"
  let .ok () ← ComputationalData.validatePublicData (node "pair" #[reals, reals])
    | throwError "registered diagram-constructor framing was not derived from the registry"
  let .error _ ← ComputationalData.validatePublicData (node "unregisteredShape" #[reals, reals])
    | throwError "the validator invented a diagram constructor from an unregistered shape"

/- The runtime response validator checks the declared types of symbolic points.
These are engineering fixtures: an arbitrary real constant is deliberately
accepted for a different fixed real expression. No answer equality is certified. -/
run_cmd liftTermElabM do
  let node (tag : String) (args : Array Json) :=
    Json.mkObj [("ctor", toJson tag), ("args", Json.arr args)]
  let reals := node "obj.sets.reals" #[]
  let complexes := node "obj.sets.complexes" #[]
  let domain ← Language.globalPointSource.run {}
  let trace ← Trace.new
  let harness ← Harness.empty
  discard <| Semantic.recordNamedObject domain (some trace)
  let one := (← realizeEndpoint harness trace "the fixed point domain" domain).json
  let selected ← elabTermAndSynthesize (← `(CasCatalogue.Algebra.NumberSystems.reals)) none
  let fixed ← elabTermAndSynthesize (← `((0 : ℝ))) none
  let point (n : Nat) := node "element" #[reals, node "numeral" #[toJson n]]
  let owned := node "opaqueData" #[toJson "owned-callable"]
  let answer (arrow : Json) := node "valueData" #[
    node "element" #[reals, node "point" #[arrow]]]
  let squareRoot := node "mor.sets.real_sqrt" #[]
  let valid := #[node "mor.sets.real_pi" #[],
    node "compose" #[point 11, squareRoot],
    node "typedMap" #[one, reals, owned],
    node "compose" #[owned, squareRoot],
    node "compose" #[point 11, node "identity" #[reals, reals]]]
  for arrow in valid do
    if let .error message ← ComputationalData.validateElementAt selected reals fixed (answer arrow) then
      throwError "a well-typed symbolic or opaque point was rejected: {message}"
  for malformed in #[node "mor.sets.complex_i" #[], squareRoot,
      node "compose" #[point 11, node "mor.sets.complex_re" #[]],
      node "typedMap" #[one, complexes, owned],
      node "typedMap" #[node "obj.sets.fin" #[toJson (2 : Nat)], reals, owned],
      node "compose" #[point 11, node "identity" #[complexes, complexes]],
      node "compose" #[owned, owned]] do
    let .error _ ← ComputationalData.validateElementAt selected reals fixed (answer malformed)
      | throwError "a runtime symbolic answer changed its point domain, codomain or composition endpoint"
  -- A function with a nontrivial domain cannot be replaced by a closed scalar.
  let generalized ← elabTermAndSynthesize
    (← `(TypeCat.ofHom (fun _ : Fin 2 => (0 : ℝ)))) none
  let .error _ ← ComputationalData.validateElementAt selected reals generalized
      (answer (node "mor.sets.real_pi" #[]))
    | throwError "a closed result collapsed a nonconstant generalized-point interface"
  -- Parameter checking must preserve the complete selected ring, not merely the
  -- existence and arity of a registered operation-expression address.
  let rings ← categoryNamed (← registryState) "Rings"
  let ring ← (object (← registryState) "ZMod" #[.nat 5] (some rings)).run {}
  let ringObject ← (semanticObject ring).run {}
  let carrier ← (carrierObject ring).run {}
  let .element ringPoint _ ← (toElement (.nat 0) carrier).run {}
    | throwError "the selected-ring fixture lost its fixed point interface"
  let ringData := node "obj.rings.integers_mod" #[toJson (5 : Nat)]
  let changed := node "element" #[ringData, node "operationExpression" #[
    toJson "op.rings.pow", Json.arr #[node "obj.rings.integers_mod" #[toJson (7 : Nat)],
      toJson (3 : Nat)], Json.arr #[node "numeral" #[toJson (2 : Nat)]]]]
  let .error _ ← ComputationalData.validateElementAt ringObject ringData ringPoint changed
    | throwError "a runtime element changed its selected dependent ring parameter"
