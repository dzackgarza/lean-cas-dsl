/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Catalogue.Registry.Entry
public import CasCatalogue.Resolve
public import Std.Data.HashMap
public import Std.Data.HashSet

@[expose] public section

/-!
# The operation tree of a semantic reading (`specs/leaf-registration.md`, "The realized reading")

The realized reading evaluates the same term the semantic reading elaborates; there is no second
traversal of the statement. The semantic reading records, as it forms each value, the catalogue
operation that formed it, keyed by the value it produced: a named object at its parameters, a
method or property after its structural route, a registered limit at its diagram. The realized
reading walks these records bottom-up. Nothing is reverse-engineered from a printed term.
-/

open Lean

namespace CasCatalogue

/-- A local category context derived from accepted actions. The complete selected
bundle is retained even when the expression has no separately named registry row. -/
structure CategoryContext where
  expression : CategoryExpr
  bundle : Expr
  deriving Repr

/-- Record identity is syntactic, including the complete retained dictionary. -/
instance : BEq CategoryContext where
  beq left right := left.expression.syntacticEq right.expression && left.bundle == right.bundle

/-- Accepted source presentations of one definitionally identical complete structured value.
The identity is a kernel-checkable conversion proof of the full image, never its carrier. -/
structure ParameterPresentation where
  source : ObjectId
  sourceCategory : CategoryId
  targetCategory : CategoryId
  params : Array Expr
  route : Array EdgeRef
  applications : Array Expr
  carrierRoute : Array EdgeRef
  identifications : Array Name
  object : Expr
  image : Expr
  identity : Expr
  deriving BEq, Repr

/-- One complete selected source of a routed operation. Accepted route comparisons
retain their exact constructor and whiskering contexts and the checked typed witnesses. -/
structure OperationSource where
  context : CategoryContext
  receiver : Expr
  route : Array EdgeRef
  applications : Array Expr
  comparisons : Array RouteComparison := #[]
  comparisonWitnesses : Array Expr := #[]
  deriving BEq, Repr

/-- One surviving registered binding, before any equivalence-class representative is
chosen. The complete declaration application precedes its actual supplied operands. -/
structure OperationCandidate where
  operation : OperationId
  application : Expr
  result : Expr
  sources : Array OperationSource
  deriving BEq, Repr

/-- A checked equality of universally abstracted complete routed operation families.
The indices refer to the retained candidates and their complete source witnesses.
`parameters` instantiates that shared dependent context only after the identity is checked. -/
structure OperationFamilyComparison where
  left : Nat
  right : Nat
  leftSource : Nat
  rightSource : Nat
  parameters : Array Expr
  leftFamily : Expr
  rightFamily : Expr
  leftType : Expr
  rightType : Expr
  identity : Expr
  deriving BEq, Repr

/-- One prescribed stage, selected on the formal side before execution. Its
evidence and complete underlying action fix all public computational projections;
the input is the preceding complete subobject, not a later returned packet. -/
structure MethodLiftApplication where
  id : LiftId
  evidence : Expr
  action : Expr
  receiver : Expr
  input : Expr
  result : Expr
  deriving BEq, Repr

/-- The complete typed invocation selected by a method reading. Runtime execution
consumes these very applications and endpoints instead of resolving the method
again or inferring its parameters from a result. Lifts have the route's order. -/
structure MethodApplication where
  sourceContext : CategoryContext
  routeApplications : Array Expr
  routeReceivers : Array Expr
  image : Expr
  application : Expr
  input : Expr
  baseResult : Expr
  baseContext : CategoryContext
  result : Expr
  resultContext : CategoryContext
  lifts : Array MethodLiftApplication := #[]
  deriving BEq, Repr

/-- Traverse every retained typed field without changing its selected metadata or order. -/
def MethodApplication.mapTermsM {m : Type → Type} [Monad m]
    (f : Expr → m Expr) (application : MethodApplication) : m MethodApplication := do
  let context (value : CategoryContext) : m CategoryContext := do
    return { value with bundle := (← f value.bundle) }
  let lifts ← application.lifts.mapM fun lift => do
    return { lift with
      evidence := (← f lift.evidence)
      action := (← f lift.action)
      receiver := (← f lift.receiver)
      input := (← f lift.input)
      result := (← f lift.result) }
  return { application with
    sourceContext := (← context application.sourceContext)
    routeApplications := (← application.routeApplications.mapM f)
    routeReceivers := (← application.routeReceivers.mapM f)
    image := (← f application.image)
    application := (← f application.application)
    input := (← f application.input)
    baseResult := (← f application.baseResult)
    baseContext := (← context application.baseContext)
    result := (← f application.result)
    resultContext := (← context application.resultContext)
    lifts }

/-- Instantiate every retained mathematical field, including the full selected
category dictionaries and the evidence of each prescribed stage. -/
def MethodApplication.instantiateMVars (application : MethodApplication) :
    Meta.MetaM MethodApplication := application.mapTermsM Lean.instantiateMVars

/-- How the semantic reading formed a value. -/
inductive Node
  /-- The registered object `id` at its explicit parameters (numerals, or other values). -/
  | object (id : ObjectId) (params : Array Expr)
  /-- A typed constructor parameter obtained along an accepted structural route. -/
  | parameterTransport (source : ObjectId) (sourceCategory targetCategory : CategoryId)
      (route : Array EdgeRef) (receiver : Expr)
  /-- Structural transport of an anonymous selected object, with exact source provenance. -/
  | structureTransport (sourceCategory targetCategory : CategoryId)
      (route : Array EdgeRef) (receiver : Expr)
  /-- A structural route retaining the exact full edge applications formed by the reading. -/
  | retainedRoute (sourceCategory targetCategory : CategoryId) (route : Array EdgeRef)
      (applications : Array Expr) (receiver : Expr)
  /-- Proof-only construction in an actual classifier total, retaining the complete
  original object, registered forgetful action and full-image identification. -/
  | proofRefinement (classifier : ClassifierId) (sourceCategory targetCategory : CategoryId)
      (source action identity : Expr)
  | parameterEquivalence (expectedType representative : Expr)
      (sources : Array ParameterPresentation)
  /-- A registered named morphism at its ordered explicit declaration arguments. -/
  | namedMorphism (id : MorphismId) (params : Array Expr)
  /-- A registered inclusion at its complete declared parameters and exact endpoints. -/
  | namedInclusion (id : InclusionId) (category : CategoryId) (params : Array Expr)
      (source target : Expr)
  /-- A map the object row `object` registers as its field `field` (`inclusion`: the admission
  inclusion `Mˣ ↪ M`; `constants`: `R → R[[t]]`), at its explicit parameters. -/
  | objectField (object : ObjectId) (field : String) (category : CategoryId) (params : Array Expr)
  /-- A map of the registered power object `powerObject`, its field `field` (`member`, `truth`)
  at its explicit parameters. -/
  | powerObjectMap (powerObject : PowerObjectId) (field : String) (params : Array Expr)
  /-- A callable published as a typed field of a registered owner. -/
  | namedCallable (address : String) (category : CategoryId) (params : Array Expr)
  /-- A typed callable body in its exact generalized-element domain context. -/
  | callableRecipe (category : CategoryId) (domain target body : Expr)
  /-- A formally admitted point retaining its original computational datum and endpoints. -/
  | admittedPoint (object : ObjectId) (category : CategoryId) (params : Array Expr)
      (original : Expr) (originalCategory : CategoryId) (originalSource originalTarget : Expr)
  /-- The actual checked one-data-field constructor, retaining the original point map. -/
  | constrainedPoint (constructor : Name) (category : CategoryId)
      (domain source target original : Expr)
  /-- An accepted presentation comparison, retaining declaration arguments and orientation. -/
  | presentation (id : NaturalTransformationId) (params : Array Expr) (inverse : Bool)
  | generator (id : ObjectId) (params : Array Expr)
  | presentationApply (id : NaturalTransformationId) (params : Array Expr) (inverse : Bool)
      (source target argument : Expr)
  /-- A closed selected element formed by an accepted operation, retaining all typed inputs. -/
  | operationApply (id : OperationId) (params operands : Array Expr) (target selected : Expr)
  | operationPoint (id : OperationId) (params : Array Expr)
      (comparison operation target selected : Expr)
  /-- The entire checked class of inherited operations. `chosen` is a deterministic
  serialization representative inside that class, never an operation-priority rule. -/
  | operationEquivalence (representative : Expr) (chosen : Nat)
      (candidates : Array OperationCandidate) (comparisons : Array OperationFamilyComparison)
  | elementNumeral (value : Nat) (target selected : Expr)
  /-- The value of a closed point at the registered terminal point, used as a dependent
  declaration parameter while retaining its complete selected computational source. -/
  | elementValue (point target selected : Expr)
  /-- The product mediator of independently fixed points at a retained formal product. -/
  | productMediator (category : CategoryId) (presentation domain left right : Expr)
  | morphismComposition (category : CategoryId) (first second source middle target : Expr)
  | morphismIdentity (category : CategoryId) (object : Expr)
  | contextualRoute (source target : CategoryContext) (route : Array EdgeRef)
      (applications : Array Expr) (receiver : Expr) (morphism : Bool)
  | contextualComposition (context : CategoryContext)
      (first second source middle target : Expr)
  | contextualIdentity (context : CategoryContext) (object : Expr)
  | contextualArrow (context : CategoryContext) (hom source target : Expr)
  /-- One endpoint occurrence of a complete selected callable. The parent is formed
  first; neither equal formal endpoints nor independent object actions choose its data. -/
  | callableEndpoint (context : CategoryContext) (receiver : Expr) (source : Bool)
  /-- The stored map of an object of the registered arrow-category construction. -/
  | arrowProjection (receiver : Expr)
  /-- A defining leg of the exact retained universal construction. -/
  | limitProjection (receiver index : Expr)
  /-- A field of the complete accepted Arrow/subobject or universal-construction schema.
  An optional index is an actual registered data-constructor port, never a value lookup. -/
  | structuredProjection (receiver : Expr) (field : String) (index : Option Nat)
  /-- The canonical cartesian map and its endpoints, fixed by a registered family
  reindexing, its complete parameters, original base map and selected fibre object. -/
  | cartesian (id : FunctorId) (params : Array Expr) (baseMorphism receiver : Expr)
      (field : String)
  /-- Forward point identification along a checked carrier-preserving structural view. -/
  | pointView (source target : Expr) (route : Array EdgeRef)
      (applications : Array Expr) (argument : Expr)
  /-- The exact map action of an accepted structural route. -/
  | morphismTransport (sourceCategory targetCategory : CategoryId)
      (route : Array EdgeRef) (receiver : Expr)
  /-- A registered functor's object action at its typed parameters and exact receiver. -/
  | functor (id : FunctorId) (params : Array Expr) (receiver : Expr)
  /-- A directly selected registered construction, with every declaration parameter. -/
  | construction (id : ConstructionId) (params : Array Expr) (receiver : Expr)
  | constructionMap (id : ConstructionId) (params : Array Expr)
      (source target morphism : Expr)
  | categoryParameter (id : CategoryId) (params : Array Expr)
  | functorParameter (id : FunctorId) (params : Array Expr)
  /-- The actual registered core construction retains its underlying complete object. -/
  | coreObject (context : CategoryContext) (object : Expr)
  | coreIso (context : CategoryContext) (source target forward backward : Expr)
  /-- An explicitly selected lift's four fields share this exact retained application. -/
  | selectedLift (id : LiftId) (params : Array Expr) (source inclusion monic : Expr)
  | liftProjection (receiver : Expr) (field : String)
  | liftFactor (receiver baseMap cone proof : Expr)
  /-- A component of a registered cell, after its declared constructor actions. -/
  | cellComponent (id : NaturalTransformationId) (params : Array Expr)
      (constructors : Array ConstructorId) (inverse : Bool) (receiver : Expr)
  | cellEndpoint (id : NaturalTransformationId) (params : Array Expr)
      (constructors : Array ConstructorId) (inverse right : Bool) (receiver : Expr)
  /-- A binder's exact parameters, domain map and independently admitted map. -/
  | binder (id : BinderId) (params : Array Expr) (domain body admitted : Expr)
  /-- A registered arrow-category object, with its defining map and both endpoints. -/
  | arrow (category : CategoryId) (morphism source target : Expr)
  /-- The denotation of the literal `literal` of the registered literal form `form` (a morphism
  of its graph, a finite subset of its elements). -/
  | literal (form : LiteralId) (literal : Expr)
  /-- The method `id` after its selected route, retaining every checked comparison
  with its complete constructor and whiskering context. -/
  | method (id : MethodId) (route : Array EdgeRef) (receiver : Expr)
      (comparisons : Array (RouteComparison × Expr)) (application : MethodApplication)
  /-- A method whose result has prescribed lifts back along its route. -/
  | methodWithLifts (id : MethodId) (route : Array EdgeRef) (lifts : Array LiftId)
      (receiver : Expr) (comparisons : Array (RouteComparison × Expr))
      (application : MethodApplication)
  /-- The property `id`, decided of `receiver` after the structural route `route`. -/
  | property (id : PropertyId) (route : Array EdgeRef) (receiver : Expr)
      (comparisons : Array (RouteComparison × Expr))
  /-- The registered limit `id` at the diagram `diagram`, returned along the registered creation
  lift `lift` when it is computed in another category. -/
  | limit (id : LimitId) (diagram : Expr) (lift : Option LiftId)
  deriving BEq, Repr

/-- A total traversal of the selected typed fields. Metadata, array boundaries and
all declaration positions are preserved; this never unfolds a mathematical value. -/
def Node.mapTermsM {m : Type → Type} [Monad m] (f : Expr → m Expr) (node : Node) : m Node := do
  let mapContext (context : CategoryContext) : m CategoryContext := do
    return { context with bundle := ← f context.bundle }
  let mapComparisons (comparisons : Array (RouteComparison × Expr)) :=
    comparisons.mapM fun (context, value) => do pure (context, ← f value)
  match node with
  | .object id parameters => pure (.object id (← parameters.mapM f))
  | .parameterTransport source sourceCategory targetCategory route receiver =>
      pure (.parameterTransport source sourceCategory targetCategory route (← f receiver))
  | .structureTransport sourceCategory targetCategory route receiver =>
      pure (.structureTransport sourceCategory targetCategory route (← f receiver))
  | .proofRefinement classifier sourceCategory targetCategory source action identity =>
      pure (.proofRefinement classifier sourceCategory targetCategory
        (← f source) (← f action) (← f identity))
  | .parameterEquivalence expected representative sources => do
      let sources ← sources.mapM fun source => do
        pure { source with
          params := ← source.params.mapM f
          applications := ← source.applications.mapM f
          object := ← f source.object
          image := ← f source.image
          identity := ← f source.identity }
      pure (.parameterEquivalence (← f expected)
        (← f representative) sources)
  | .operationEquivalence representative chosen candidates comparisons => do
      let candidates ← candidates.mapM fun candidate => do
        let sources ← candidate.sources.mapM fun source => do
          return { source with
            context := ← mapContext source.context
            receiver := ← f source.receiver
            applications := ← source.applications.mapM f
            comparisonWitnesses := ← source.comparisonWitnesses.mapM f }
        return { candidate with
          application := ← f candidate.application
          result := ← f candidate.result
          sources }
      let comparisons ← comparisons.mapM fun comparison => do
        return { comparison with
          parameters := ← comparison.parameters.mapM f
          leftFamily := ← f comparison.leftFamily
          rightFamily := ← f comparison.rightFamily
          leftType := ← f comparison.leftType
          rightType := ← f comparison.rightType
          identity := ← f comparison.identity }
      pure (.operationEquivalence (← f representative) chosen candidates comparisons)
  | .retainedRoute source target route applications receiver =>
      pure (.retainedRoute source target route (← applications.mapM f)
        (← f receiver))
  | .namedMorphism id params => pure (.namedMorphism id (← params.mapM f))
  | .powerObjectMap id field params =>
      pure (.powerObjectMap id field (← params.mapM f))
  | .objectField id field category params =>
      pure (.objectField id field category (← params.mapM f))
  | .namedInclusion id category params source target =>
      pure (.namedInclusion id category (← params.mapM f)
        (← f source) (← f target))
  | .callableRecipe category domain target body =>
      pure (.callableRecipe category (← f domain)
        (← f target) (← f body))
  | .namedCallable address category params =>
      pure (.namedCallable address category (← params.mapM f))
  | .admittedPoint id category params original originalCategory source target =>
      pure (.admittedPoint id category (← params.mapM f)
        (← f original) originalCategory
        (← f source) (← f target))
  | .constrainedPoint constructor category domain source target original =>
      pure (.constrainedPoint constructor category (← f domain)
        (← f source) (← f target) (← f original))
  | .presentation id params inverse =>
      pure (.presentation id (← params.mapM f) inverse)
  | .generator id params => pure (.generator id (← params.mapM f))
  | .elementNumeral value target selected =>
      pure (.elementNumeral value (← f target) (← f selected))
  | .elementValue point target selected =>
      pure (.elementValue (← f point) (← f target)
        (← f selected))
  | .productMediator category productPresentation domain left right =>
      pure (.productMediator category (← f productPresentation)
        (← f domain) (← f left) (← f right))
  | .morphismComposition category first second source middle target =>
      pure (.morphismComposition category (← f first)
        (← f second) (← f source)
        (← f middle) (← f target))
  | .morphismIdentity category objectValue =>
      pure (.morphismIdentity category (← f objectValue))
  | .contextualRoute source target route applications receiver morphism =>
      pure (.contextualRoute (← mapContext source) (← mapContext target)
        route (← applications.mapM f) (← f receiver) morphism)
  | .contextualComposition context first second source middle target =>
      pure (.contextualComposition (← mapContext context)
        (← f first) (← f second)
        (← f source) (← f middle) (← f target))
  | .contextualIdentity context objectValue =>
      pure (.contextualIdentity (← mapContext context) (← f objectValue))
  | .contextualArrow context hom source target =>
      pure (.contextualArrow (← mapContext context) (← f hom)
        (← f source) (← f target))
  | .callableEndpoint context receiver source =>
      pure (.callableEndpoint (← mapContext context) (← f receiver) source)
  | .arrowProjection receiver =>
      pure (.arrowProjection (← f receiver))
  | .limitProjection receiver index =>
      pure (.limitProjection (← f receiver) (← f index))
  | .structuredProjection receiver field index =>
      pure (.structuredProjection (← f receiver) field index)
  | .cartesian id params baseMorphism receiver field =>
      pure (.cartesian id (← params.mapM f)
        (← f baseMorphism) (← f receiver) field)
  | .pointView source target route applications argument =>
      pure (.pointView (← f source) (← f target) route
        (← applications.mapM f) (← f argument))
  | .operationPoint id params comparison operation target selected =>
      pure (.operationPoint id (← params.mapM f)
        (← f comparison) (← f operation)
        (← f target) (← f selected))
  | .operationApply id params operands target selected =>
      pure (.operationApply id (← params.mapM f)
        (← operands.mapM f) (← f target)
        (← f selected))
  | .presentationApply id params inverse source target argument =>
      pure (.presentationApply id (← params.mapM f) inverse
        (← f source) (← f target) (← f argument))
  | .morphismTransport sourceCategory targetCategory route receiver =>
      pure (.morphismTransport sourceCategory targetCategory route (← f receiver))
  | .functor id params receiver =>
      pure (.functor id (← params.mapM f) (← f receiver))
  | .categoryParameter id params =>
      pure (.categoryParameter id (← params.mapM f))
  | .functorParameter id params =>
      pure (.functorParameter id (← params.mapM f))
  | .construction id params receiver =>
      pure (.construction id (← params.mapM f) (← f receiver))
  | .constructionMap id params source target morphism =>
      pure (.constructionMap id (← params.mapM f)
        (← f source) (← f target) (← f morphism))
  | .coreObject context objectValue =>
      pure (.coreObject (← mapContext context) (← f objectValue))
  | .coreIso category source target forward backward =>
      pure (.coreIso (← mapContext category) (← f source) (← f target)
        (← f forward) (← f backward))
  | .selectedLift id params source inclusion monic =>
      pure (.selectedLift id (← params.mapM f) (← f source)
        (← f inclusion) (← f monic))
  | .liftProjection receiver field => pure (.liftProjection (← f receiver) field)
  | .liftFactor receiver baseMap cone proof =>
      pure (.liftFactor (← f receiver) (← f baseMap)
        (← f cone) (← f proof))
  | .cellComponent id params constructors inverse receiver =>
      pure (.cellComponent id (← params.mapM f) constructors inverse
        (← f receiver))
  | .cellEndpoint id params constructors inverse right receiver =>
      pure (.cellEndpoint id (← params.mapM f) constructors inverse right
        (← f receiver))
  | .binder id params domain body admitted =>
      pure (.binder id (← params.mapM f) (← f domain)
        (← f body) (← f admitted))
  | .arrow category morphism source target =>
      pure (.arrow category (← f morphism) (← f source)
        (← f target))
  | .literal form literalValue => pure (.literal form (← f literalValue))
  | .method id route receiver recordedComparisons interpreted =>
      pure (.method id route (← f receiver)
        (← mapComparisons recordedComparisons) (← interpreted.mapTermsM f))
  | .methodWithLifts id route lifts receiver recordedComparisons interpreted =>
      pure (.methodWithLifts id route lifts (← f receiver)
        (← mapComparisons recordedComparisons) (← interpreted.mapTermsM f))
  | .property id route receiver recordedComparisons =>
      pure (.property id route (← f receiver)
        (← mapComparisons recordedComparisons))
  | .limit id diagram lift => pure (.limit id (← f diagram) lift)

/-- An administrative description retains the complete node skeleton and each typed
field at its original ordinal. Expressions remain shared immutable Lean subterms; the
skeleton contains positions, never printed mathematical terms or their hashes. -/
def Node.producerDescription (node : Node) : String × Array Expr := Id.run do
  let position (term : Expr) : StateM (Array Expr) Expr := do
    let fields ← get
    set (fields.push term)
    pure (mkRawNatLit fields.size)
  let (skeleton, fields) := (node.mapTermsM position).run #[]
  return (reprStr skeleton, fields)

/-- The records of one statement's semantic reading. -/
abbrev Trace := IO.Ref (Std.HashMap Expr Node)

/-- A binding keeps its own trace key even when another accepted registry row uses
the same declaration and produces the same map. The tag is retained syntax only;
the whole value and its type are unchanged by this transparent definition. -/
def Trace.operationResult (_binding : String) {α : Sort u} (value : α) : α := value

/-- A producer retains every selected typed input even when its mathematical result
does not mention that input. This is an administrative identity, not an operation. -/
def Trace.producerArgument {α : Sort u} (_argument : α) {β : Sort v} (value : β) : β := value

/-- Distinct interpreted producers have distinct execution keys. Only `occurrence` is
administrative: the complete selected description and its typed arguments remain part
of the interpreted question. The whole term still has exactly the original value. -/
def Trace.producerResult (_occurrence : Nat) (_description : String)
    {α : Sort u} (value : α) : α := value

/-- Allocation is outside elaborator rollback and outside copied trace maps. A speculative
branch may abandon an ordinal, but no subsequently merged branch can reuse it. -/
initialize nextProducerOccurrence : IO.Ref Nat ← IO.mkRef 0

structure ProducerAnchor where
  occurrence : Nat
  description : String
  fields : Array Expr
  type : Expr
  formal : Expr

/-- Read only the complete administrative wrapper. No mathematical unfolding or
interpretation of a printed expression participates. -/
def Trace.producerAnchor? (value : Expr) : Option ProducerAnchor := Id.run do
  let value := value.consumeMData
  unless value.isAppOfArity ``Trace.producerResult 4 do return none
  let arguments := value.getAppArgs
  let .lit (.natVal occurrence) := arguments[0]! | return none
  let .lit (.strVal description) := arguments[1]! | return none
  let mut formal := arguments[3]!
  let mut fields := #[]
  while formal.isAppOfArity ``Trace.producerArgument 4 do
    fields := fields.push formal.getAppArgs[1]!
    formal := formal.appArg!
  return some { occurrence, description, fields, type := arguments[2]!, formal }

/-- Inspect a selected mathematical head while retaining the original anchored term
as the value used for execution. Meaningful operation-binding markers are not erased. -/
partial def Trace.unanchor (value : Expr) : Expr :=
  let selected := value.consumeMData
  let arguments := selected.getAppArgs
  if arguments.size < 4 then value
  else
    match Trace.producerAnchor? (mkAppN selected.getAppFn (arguments.extract 0 4)) with
    | some anchor =>
        Trace.unanchor (mkAppN anchor.formal (arguments.extract 4 arguments.size))
    | none => value

/-- Erase only allocation ordinals in an identity view. Matching the first application
of the marker leaves traversal of every type, selected field and formal result intact. -/
def Trace.withoutOccurrences (value : Expr) : Expr :=
  value.replace fun term =>
    if term.isAppOfArity ``Trace.producerResult 1 then
      some (mkApp term.appFn! (mkRawNatLit 0))
    else none

def Trace.new : IO Trace := IO.mkRef {}

/-- Recover an existing record without changing its producer. A fresh producer must
use `recordProduced` and retain its returned handle; an equal raw value cannot replace
another selected record. Repeating the exact same recovery is idempotent. -/
def Trace.record (trace? : Option Trace) (value : Expr) (node : Node) : IO Unit := do
  match trace? with
  | some trace =>
      let conflict ← trace.modifyGet fun entries =>
        match entries[value]? with
        | some previous => (previous != node, entries)
        | none => (false, entries.insert value node)
      if conflict then
        throw <| IO.userError "distinct selected producers share one executable trace key"
  | none => pure ()

/-- Record a producer before another equal mathematical value can occupy its key.
The node is independently fixed first. Building its descriptor visits only its finite
ordered fields and shares their existing expression DAG; the new occurrence cannot
occur in any of those fields. Callers retain the returned handle, never the bare value. -/
def Trace.recordProduced (trace? : Option Trace) (value : Expr) (node : Node) : Meta.MetaM Expr := do
  let some trace := trace? | return value
  let (description, fields) := node.producerDescription
  let mut selected := value
  for field in fields.reverse do
    selected ← Meta.mkAppM ``Trace.producerArgument #[field, selected]
  let occurrence ← nextProducerOccurrence.modifyGet fun next => (next, next + 1)
  let result ← Meta.mkAppM ``Trace.producerResult
    #[mkRawNatLit occurrence, mkStrLit description, selected]
  Trace.record (some trace) result node
  return result

/-- Check the complete anchor against the actual retained semantic record. The
description string alone cannot assert a selected operation or parameter. -/
def Trace.checkProducerRecord (value : Expr) (node : Node) : Meta.MetaM Unit := do
  let value ← Lean.instantiateMVars value
  unless value.consumeMData.isAppOfArity ``Trace.producerResult 4 do return
  let some anchor := Trace.producerAnchor? value
    | throwError "the selected producer has a malformed administrative anchor"
  let node ← node.mapTermsM Lean.instantiateMVars
  let (description, fields) := node.producerDescription
  unless anchor.description == description && anchor.fields.size == fields.size do
    throwError "the producer anchor changed its complete selected record"
  for (actual, retained) in anchor.fields.zip fields do
    unless actual.equal retained do
      throwError "the producer anchor changed an ordered typed field"
  unless ← Meta.isTypeCorrect value do
    throwError "the producer anchor is outside its original complete type"

/-- Validate references from the prepared claim and every retained record against
the actual trace. The descriptor is checked at its selected node; a string cannot
substitute for that node. Exact-expression visitation shares repeated DAG subterms. -/
def Trace.checkProducedEntries (entries : Array (Expr × Node))
    (roots : Array Expr := #[]) : Meta.MetaM Unit := do
  let mut recorded : Std.HashMap Expr Node := {}
  for (value, node) in entries do
    if let some previous := recorded[value]? then
      unless previous == node do
        throwError "distinct selected producers share one executable trace key"
    recorded := recorded.insert value node
  let complete := recorded
  let visited ← IO.mkRef ({} : Std.HashSet ExprStructEq)
  let rec visit (value : Expr) : Meta.MetaM Unit := do
    let key : ExprStructEq := ⟨value⟩
    if (← visited.get).contains key then return
    visited.modify (·.insert key)
    if value.isAppOfArity ``Trace.producerResult 4 then
      let some node := complete[value]?
        | throwError "a selected producer reference is outside its complete trace"
      Trace.checkProducerRecord value node
    match value with
    | .app fn argument => visit fn *> visit argument
    | .lam _ type body _ | .forallE _ type body _ => visit type *> visit body
    | .letE _ type value body _ => visit type *> visit value *> visit body
    | .mdata _ body | .proj _ _ body => visit body
    | _ => pure ()
  for (value, node) in entries do
    Trace.checkProducerRecord value node
    visit value
    for field in node.producerDescription.2 do visit field
  for root in roots do visit root

/-- Administrative duplication does not add a mathematical operation. Coalesce only
exact term-and-record duplicates after removing occurrence ordinals, before any proof
or binder quotient. Different raw proof keys and different selected records survive. -/
def Trace.identityEntries (entries : Array (Expr × Node)) : Array (Expr × Node) := Id.run do
  let mut seen : Std.HashMap ExprStructEq (Array Node) := {}
  let mut result := #[]
  for (term, node) in entries do
    if (term.find? (·.isAppOfArity ``Trace.producerResult 4)).isNone then
      result := result.push (term, node)
      continue
    let term := Trace.withoutOccurrences term
    let node := Id.run <| node.mapTermsM fun field => pure (Trace.withoutOccurrences field)
    let key : ExprStructEq := ⟨term⟩
    let previous := seen[key]?.getD #[]
    unless previous.contains node do
      result := result.push (term, node)
      seen := seen.insert key (previous.push node)
  return result

/-- Record an operation at a key containing its exact accepted binding. Separate
rows sharing a declaration therefore survive the union of candidate traces. -/
def Trace.recordOperation (trace? : Option Trace) (value : Expr) (node : Node) : Meta.MetaM Expr := do
  let binding ← match node with
    | .operationApply id .. | .operationPoint id .. => pure id.raw
    | _ => throwError "an operation trace key requires an operation node"
  let result ← Meta.mkAppM ``Trace.operationResult #[toExpr binding, value]
  Trace.recordProduced trace? result node

/-- Exact named callable addresses have independent trace/cache keys for the same
reason as element operations: accepted aliases may share a Lean declaration. -/
def Trace.recordCallable (trace? : Option Trace) (value : Expr) (node : Node) : Meta.MetaM Expr := do
  let binding ← match node with
    | .namedMorphism id .. => pure id.raw
    | .namedCallable address .. => pure address
    | _ => throwError "a callable trace key requires an exact callable node"
  let result ← Meta.mkAppM ``Trace.operationResult #[toExpr binding, value]
  Trace.recordProduced trace? result node

/-- Record `derived` as formed the way `value` was (the apex of a recorded limit, say). -/
def Trace.alias (trace? : Option Trace) (value derived : Expr) : IO Unit := do
  let some trace := trace? | return
  if let some node := (← trace.get)[value]? then Trace.record (some trace) derived node

/-- How `value` was formed, if it was recorded. -/
partial def Trace.node? (trace : Trace) (value : Expr) : IO (Option Node) := do
  if let some node := (← trace.get)[value]? then return some node
  match value with
  | .mdata _ body => trace.node? body
  | _ =>
      -- Elaboration's expected-type `id` wrappers carry the same formal construction.
      -- Categorical identities and mathematical operations remain distinct trace nodes.
      if value.isAppOfArity ``id 2 then trace.node? value.appArg! else pure none

/-- A typed view retains its original selected producer in a fresh addressed result.
Callers use the returned handle instead of overwriting a possibly shared bare view. -/
def Trace.aliasProduced (trace? : Option Trace) (value derived : Expr) : Meta.MetaM Expr := do
  let some trace := trace? | return derived
  let some node ← trace.node? value | return derived
  Trace.recordProduced trace? derived node

end CasCatalogue
