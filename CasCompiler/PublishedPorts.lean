module

public import CasCompiler.RecordAction
public import CasCatalogue.Admission
public import CasContract.Port

public section

namespace CasCompiler.PublishedPorts

open Lean Meta CasCatalogue CasCatalogue.Backend

/-- One native computational role at its original complete family. The source
path and type remain explicit even when several roles share an operation address. -/
structure Port where
  operation : String
  path : Array Name
  type : Expr

def references (state : SemanticState) : Array ComputationRef :=
  (state.operations.map (ComputationRef.operation ∘ (·.id))) ++
  (state.methods.map (ComputationRef.method ∘ (·.id))) ++
  (state.functors.map (ComputationRef.functor ∘ (·.id))) ++
  (state.constructions.map (ComputationRef.construction ∘ (·.id))) ++
  (state.morphisms.map (ComputationRef.morphism ∘ (·.id)))

/-- The released complete-input address, also used by native demand preparation. -/
def inputAddress (reference : ComputationRef) : String :=
  match reference with
  | .morphism _ => computationAddress reference
  | _ => computationAddress reference ++ "#input"

private partial def recordPorts (reference : ComputationRef) (layout : SourceLayout)
    (path : Array FieldLayout) : MetaM (Array Port) := do
  let mut ports := #[]
  for field in layout.fields do
    if field.wireIndex.isNone then continue
    let selected := path.push field
    ports := ports.push ⟨recordActionAddress reference selected,
      selected.map (·.projection), field.source.type⟩
    if field.kind == .record then
      ports := ports ++ (← recordPorts reference (← field.toLayout) selected)
  return ports

/-- Derive field addresses from the same whole checked family and native layouts
that prepare runtime record actions. No suffix, type spelling or backend adds a field. -/
opaque forReference (reference : ComputationRef) : MetaM (Array Port) := withLCtx {} #[] do
  let family ← SourceFamily.forReference reference
  let root : Port := ⟨computationAddress reference, #[], family.source.familyType⟩
  -- Routed methods expose their complete object invocation at their authored id.
  -- Their native functor record is retained in that source family's metadata.
  if reference matches .method _ then return #[root]
  forallTelescopeReducing family.source.familyType fun parameters _ => do
    let bindings := parameters.mapIdx fun index expression =>
      { id := { session := "published-family-signature", serial := index },
        role := BindingRole.parameter, expression : LocalBinding }
    let context ← ContextTelescope.capture bindings
    let source ← context.close (mkAppN family.source.family parameters)
    let layout ← SourceLayout.ofTerm source
    return #[root] ++ (← recordPorts reference layout #[])

/-- Resolve all exact native owners. A shared prefix is only a candidate filter;
the original native field address is checked before an owner is admitted. -/
opaque family? (state : SemanticState) (address : String) :
    MetaM (Option ComputationRef) := do
  let possible := (references state).filter fun reference =>
    address == computationAddress reference ||
      address.startsWith (computationAddress reference ++ "#")
  let mut selected := #[]
  for reference in possible do
    if address == computationAddress reference then
      selected := selected.push reference
      continue
    if (← forReference reference).any (·.operation == address) then
      selected := selected.push reference
  match selected with
  | #[] => return none
  | #[reference] => return some reference
  | _ => throwError "the published address has several distinct native source owners"

/-- Canonical identity from the existing component packet's address encoder. -/
def componentAddress (id : NaturalTransformationId) (constructors : Array ConstructorId) : String :=
  ConstructedCellComponent.address {
    constructors := constructors.map (·.raw)
    component := { cell := id.raw, parameters := #[], receiver := .null, inverse := false } }

/-- The complete registered comparison and ordered constructor path of an address. -/
def component? (state : SemanticState) (address : String) :
    Except String (Option (CellEntry × Array ConstructorId)) := do
  let direct := state.cells.filter (fun row => componentAddress row.id #[] == address)
  if let #[entry] := direct then return some (entry, #[])
  unless direct.isEmpty do throw "the component address has several registered cells"
  unless address.startsWith "component:" do return none
  let json ← Json.parse (address.drop 10).toString
  let #[.str id, .arr encoded] ← json.getArr?
    | throw "a component address requires its cell and ordered constructor path"
  let constructors ← encoded.mapM fun value => ConstructorId.mk <$> value.getStr?
  if constructors.isEmpty then throw "an empty constructor path uses the direct component address"
  let #[entry] := state.cells.filter (·.id.raw == id)
    | throw "the component address has no unique registered cell"
  unless entry.invertible do throw "constructor-induced components require an invertible cell"
  unless componentAddress entry.id constructors == address do
    throw "the component address changed its canonical complete constructor path"
  for id in constructors do
    let #[constructor] := state.constructors.filter (·.id == id)
      | throw "the component path has no unique registered constructor"
    unless constructor.signature == #[.category] &&
        constructor.functorialAction.isSome && constructor.comparisonAction.isSome &&
        constructor.identityComparison.isSome && constructor.compositionComparison.isSome do
      throw "the component constructor lacks its complete published comparison interface"
  return some (entry, constructors)

/-- A cartesian address is published only by the accepted reindexing action. -/
def cartesian? (state : SemanticState) (address : String) : Except String (Option FunctorEntry) := do
  let rows := state.functors.filter (fun row => row.id.raw ++ "#cartesian" == address)
  if rows.isEmpty then return none
  let #[row] := rows | throw "the cartesian address has several registered functors"
  let .familyReindex family := row.expression.registrationKind
    | throw "the cartesian address does not name a family-reindex action"
  let #[_] := state.categoryFamilies.filter (·.id == family)
    | throw "the cartesian action has no unique accepted category family"
  return some row

private partial def edgeFromIdentity (state : SemanticState) (identity : Json) :
    Except String EdgeRef := do
  checkActionIdentity identity
  let fields ← identity.getObj?
  match fields.toList with
  | [("functor", .str id)] =>
    let #[row] := state.functors.filter (·.id.raw == id)
      | throw "the action has no unique registered functor"
    return .functor row.id
  | [("classifierForget", .str id)] =>
    let #[row] := state.classifiers.filter (·.id.raw == id)
      | throw "the action has no unique registered classifier"
    return .classifierForget row.id
  | [("constructorMap", .arr #[.str id, inner])] =>
    let #[row] := state.constructors.filter (·.id.raw == id)
      | throw "the action has no unique registered constructor"
    unless row.signature == #[.category] && row.functorialAction.isSome do
      throw "the constructor has no published unary functor action"
    return .constructMap row.id (← edgeFromIdentity state inner)
  | _ => throw "the action lost its checked public identity"

/-- Resolve the released recursive derived-action grammar without a finite
inventory bound. The complete actual parameters are checked at source formation. -/
def edge? (state : SemanticState) (address : String) : Except String (Option (EdgeRef × Bool)) := do
  unless address.startsWith "action:" do return none
  let isMap := address.endsWith "#map"
  let base := if isMap then (address.dropEnd 4).toString else address
  let identity ← actionIdentity base
  return some (← edgeFromIdentity state identity, isMap)

end CasCompiler.PublishedPorts
