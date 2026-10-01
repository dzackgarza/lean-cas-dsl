/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Catalogue.Registry.Semantic
public import Lean.Data.Json
public import Lean

@[expose] public section

set_option backward.privateInPublic true

/-!
# The registry: `lean-categories`' semantic registry, read by the kernel

The rows are `lean-categories`' (`LeanCategories.Catalogue.Registry.Semantic`), read here from the
pinned release; this repository writes none (`specs/architecture.md`). The kernel reads them
through `RegistryState`, and exports them as a manifest (`checkedRegistryManifest`).

A leaf contributes no row of any kind (`specs/leaf-registration.md`, "A registration is data"):
it is a manifest of registrations (`CasContract.Registration`), which the kernel admits against
these rows. Nothing a leaf supplies is recorded here.
-/

namespace CasCatalogue
open LeanCategories

open Lean
open Lean Meta
open Lean Elab Command

/-- A row of the registry: exactly a semantic row of the catalogue. -/
abbrev RegistryEntry := SemanticEntry

/-- The semantic row a registry row is. -/
def RegistryEntry.toSemantic (entry : RegistryEntry) : SemanticEntry := entry

/-- A semantic row, as a registry row. -/
def RegistryEntry.ofSemantic (entry : SemanticEntry) : RegistryEntry := entry

/-- Stable identifier of a registry row. -/
def RegistryEntry.stableId (entry : RegistryEntry) : String := SemanticEntry.stableId entry

/-- Lean declarations a row names. -/
def RegistryEntry.declarations (entry : RegistryEntry) : Array Name :=
  SemanticEntry.declarations entry

/-- The registry: the imported semantic registry, and nothing else. -/
structure RegistryState extends SemanticState
  deriving Inhabited

instance : Coe RegistryState SemanticState := ⟨RegistryState.toSemanticState⟩

/-- Every row. -/
def RegistryState.registryEntries (state : RegistryState) : List RegistryEntry :=
  state.toSemanticState.entries.map RegistryEntry.ofSemantic

/-- Whether this row's stable ID conflicts with a registered row. -/
def RegistryState.hasEntryId (state : RegistryState) (entry : RegistryEntry) : Bool :=
  state.toSemanticState.hasEntryId entry.toSemantic

/-- The registry of the current environment, read-only: `lean-categories`' semantic rows. Nothing
in this repository, the kernel or a leaf writes to it. -/
def registryState : CoreM RegistryState := do
  return { toSemanticState := ← semanticState }

/-- Inspect a row's declarations: by `lean-categories`' validators, which every row is. -/
def validateRegistryEntryDeclaration (entry : RegistryEntry) : MetaM Unit :=
  validateSemanticEntryDeclaration entry.toSemantic

/-- The notebook's roots: it registers nothing (`CasDslTests.Boundary`). -/
def notebookRoots : List Name := [`CasDsl, `CasDslTests]

/-- Every registry row, grouped by the imported module that wrote it. -/
def registryRowsByModule (env : Environment) : Array (Name × Array RegistryEntry) :=
  (semanticRowsByModule env).map fun (module, rows) =>
    (module, rows.map RegistryEntry.ofSemantic)

private def registryObject (fields : List (String × Json)) : Json := Json.mkObj fields

structure RegistryManifestParameter where
  ids : Array String
  name : String
  kind : String
  dependency : Option Nat
  deriving DecidableEq, Repr, ToJson, FromJson

inductive RegistryManifestParameterExpr
  | variable (id : String)
  | apply (operation : String) (argument : RegistryManifestParameterExpr)
  | apply2 (operation : String) (left right : RegistryManifestParameterExpr)
  | apply3 (operation : String)
      (first second third : RegistryManifestParameterExpr)
  deriving DecidableEq, Repr

private def registryManifestParameterExprJson : RegistryManifestParameterExpr → Json
  | .variable id => registryObject [("tag", "variable"), ("id", id)]
  | .apply operation argument => registryObject [
      ("tag", "apply"), ("operation", operation),
      ("argument", registryManifestParameterExprJson argument)]
  | .apply2 operation left right => registryObject [
      ("tag", "apply2"), ("operation", operation),
      ("left", registryManifestParameterExprJson left),
      ("right", registryManifestParameterExprJson right)]
  | .apply3 operation first second third => registryObject [
      ("tag", "apply3"), ("operation", operation),
      ("first", registryManifestParameterExprJson first),
      ("second", registryManifestParameterExprJson second),
      ("third", registryManifestParameterExprJson third)]

instance : ToJson RegistryManifestParameterExpr where
  toJson := registryManifestParameterExprJson

mutual

inductive RegistryManifestConstructorArg
  | category (category : RegistryManifestCategoryExpr)
  | object (id : String)
  | functor (id : String)

inductive RegistryManifestCategoryExpr
  | atom (id : String)
  | familyApp (family : String) (args : Array RegistryManifestParameterExpr)
  | classifierTotal (classifier : String)
  | refine (base : RegistryManifestCategoryExpr) (classifier : String)
  | opaque (id : String)
  | familyTotal (family : String)
  | construct (constructor : String) (args : Array RegistryManifestConstructorArg)

end

deriving instance BEq, Repr for RegistryManifestConstructorArg, RegistryManifestCategoryExpr

private def registryManifestCategoryExprJson : RegistryManifestCategoryExpr → Json
  | .atom id => registryObject [("tag", "atom"), ("id", id)]
  | .familyApp family args => registryObject [
      ("tag", "familyApp"), ("family", family), ("args", toJson args)]
  | .classifierTotal classifier => registryObject [
      ("tag", "classifierTotal"), ("classifier", classifier)]
  | .refine base classifier => registryObject [
      ("tag", "refine"), ("base", registryManifestCategoryExprJson base),
      ("classifier", classifier)]
  | .opaque id => registryObject [("tag", "opaque"), ("id", id)]
  | .familyTotal family => registryObject [("tag", "familyTotal"), ("family", family)]
  | .construct constructor args => registryObject [
      ("tag", "construct"), ("constructor", constructor),
      ("args", Json.arr (args.attach.map fun
        | ⟨.category category, h⟩ =>
            have := Array.sizeOf_lt_of_mem h
            have := RegistryManifestConstructorArg.category.sizeOf_spec category
            registryObject [
              ("tag", "category"), ("category", registryManifestCategoryExprJson category)]
        | ⟨.object id, _⟩ => registryObject [("tag", "object"), ("id", id)]
        | ⟨.functor id, _⟩ => registryObject [("tag", "functor"), ("id", id)]))]
termination_by e => sizeOf e
decreasing_by all_goals simp_wf; all_goals omega

instance : ToJson RegistryManifestCategoryExpr where
  toJson := registryManifestCategoryExprJson

instance : Inhabited RegistryManifestCategoryExpr := ⟨.atom ""⟩

inductive RegistryManifestFunctorExpr
  | identity (category : RegistryManifestCategoryExpr)
  | atomic (id : String)
  | classifierForget (classifier : String) (host : RegistryManifestCategoryExpr)
  | opaquePort (id : String)
  | familyFibreInclusion (family : String) (args : Array RegistryManifestParameterExpr)
  | familyReindex (family morphism : String)
      (source target : Array RegistryManifestParameterExpr)
  | comp (left right : RegistryManifestFunctorExpr)
  | constructMap (constructor : String) (functor : RegistryManifestFunctorExpr)
  deriving BEq, Repr

private def registryManifestFunctorExprJson : RegistryManifestFunctorExpr → Json
  | .identity category => registryObject [("tag", "identity"), ("category", toJson category)]
  | .atomic id => registryObject [("tag", "atomic"), ("id", id)]
  | .classifierForget classifier host => registryObject [
      ("tag", "classifierForget"), ("classifier", classifier), ("host", toJson host)]
  | .opaquePort id => registryObject [("tag", "opaquePort"), ("id", id)]
  | .familyFibreInclusion family args => registryObject [
      ("tag", "familyFibreInclusion"), ("family", family), ("args", toJson args)]
  | .familyReindex family morphism source target => registryObject [
      ("tag", "familyReindex"), ("family", family), ("morphism", morphism),
      ("source", toJson source), ("target", toJson target)]
  | .comp left right => registryObject [
      ("tag", "comp"), ("left", registryManifestFunctorExprJson left),
      ("right", registryManifestFunctorExprJson right)]
  | .constructMap constructor functor => registryObject [
      ("tag", "constructMap"), ("constructor", constructor),
      ("functor", registryManifestFunctorExprJson functor)]

instance : ToJson RegistryManifestFunctorExpr where
  toJson := registryManifestFunctorExprJson


structure RegistryManifestCategory where
  id : String
  declaration : String
  realization : String
  refinementRealization : String
  expression : RegistryManifestCategoryExpr
  deriving BEq, Repr, ToJson

structure RegistryManifestFamily where
  id : String
  schema : String
  realization : String
  transport : String
  parameters : Array RegistryManifestParameter
  variance : String
  deriving BEq, Repr, ToJson

structure RegistryManifestClassifier where
  id : String
  host : RegistryManifestCategoryExpr
  declaration : String
  realization : String
  deriving BEq, Repr, ToJson

structure RegistryManifestFunctor where
  id : String
  source : RegistryManifestCategoryExpr
  target : RegistryManifestCategoryExpr
  declaration : String
  realization : String
  expression : RegistryManifestFunctorExpr
  structural : Bool
  deriving BEq, Repr, ToJson

structure RegistryManifestPort where
  id : String
  source : RegistryManifestCategoryExpr
  target : RegistryManifestCategoryExpr
  declaration : String
  realization : String
  provenance : String
  deriving BEq, Repr, ToJson

structure RegistryManifestOpaque where
  id : String
  declaration : String
  realization : String
  reason : String
  ports : Array RegistryManifestPort
  deriving BEq, Repr, ToJson

structure RegistryManifestFibration where
  id : String
  projection : String
  variance : String
  evidence : String
  deriving BEq, Repr, ToJson

structure RegistryManifestConstructor where
  id : String
  signature : Array String
  semantics : String
  deriving BEq, Repr, ToJson

structure RegistryManifestMethod where
  id : String
  name : String
  owner : RegistryManifestCategoryExpr
  functor : String
  shape : String
  returnsToSource : Bool
  deriving BEq, Repr, ToJson

structure RegistryManifestCell where
  id : String
  source : RegistryManifestCategoryExpr
  target : RegistryManifestCategoryExpr
  left : Array String
  right : Array String
  declaration : String
  invertible : Bool
  deriving BEq, Repr, ToJson

structure RegistryManifestLimit where
  id : String
  category : String
  shape : String
  declaration : String
  colimit : Bool
  deriving BEq, Repr, ToJson

structure RegistryManifestObject where
  id : String
  category : String
  declaration : String
  deriving BEq, Repr, ToJson

structure RegistryManifestAdjunction where
  id : String
  left : String
  right : String
  declaration : String
  deriving BEq, Repr, ToJson

structure RegistryManifestProperty where
  id : String
  name : String
  classifier : String
  receiver : Option RegistryManifestCategoryExpr
  deriving BEq, Repr, ToJson

structure RegistryManifestLift where
  id : String
  edge : String
  evidence : String
  kind : String
  deriving BEq, Repr, ToJson

/-- The exported registry: the semantic rows of the catalogue. No row of a leaf exists to export. -/
structure RegistryManifest where
  schemaVersion : String
  categories : Array RegistryManifestCategory
  classifiers : Array RegistryManifestClassifier
  functors : Array RegistryManifestFunctor
  opaqueCategories : Array RegistryManifestOpaque
  categoryFamilies : Array RegistryManifestFamily
  fibrations : Array RegistryManifestFibration
  constructors : Array RegistryManifestConstructor
  methods : Array RegistryManifestMethod
  properties : Array RegistryManifestProperty
  lifts : Array RegistryManifestLift
  cells : Array RegistryManifestCell
  limits : Array RegistryManifestLimit
  adjunctions : Array RegistryManifestAdjunction
  objects : Array RegistryManifestObject
  source : String
  deriving BEq, Repr, ToJson

private def registryManifestParameterExpr : ParameterExpr → RegistryManifestParameterExpr
  | .variable id => .variable id.raw
  | .apply operation argument => .apply operation.raw (registryManifestParameterExpr argument)
  | .apply2 operation left right =>
      .apply2 operation.raw (registryManifestParameterExpr left) (registryManifestParameterExpr right)
  | .apply3 operation first second third =>
      .apply3 operation.raw (registryManifestParameterExpr first)
        (registryManifestParameterExpr second) (registryManifestParameterExpr third)

private def registryManifestCategoryExpr : CategoryExpr → RegistryManifestCategoryExpr
  | .atom id => .atom id.raw
  | .familyApp family args => .familyApp family.raw (args.map registryManifestParameterExpr)
  | .classifierTotal classifier => .classifierTotal classifier.raw
  | .refine base classifier => .refine (registryManifestCategoryExpr base) classifier.raw
  | .opaque id => .opaque id.raw
  | .familyTotal family => .familyTotal family.raw
  | .construct constructor args => .construct constructor.raw (args.attach.map fun
      | ⟨.category category, h⟩ =>
          have := Array.sizeOf_lt_of_mem h
          have := ConstructorArg.category.sizeOf_spec category
          .category (registryManifestCategoryExpr category)
      | ⟨.object id, _⟩ => .object id.raw
      | ⟨.functor id, _⟩ => .functor id.raw)
termination_by e => sizeOf e
decreasing_by all_goals simp_wf; all_goals omega

private def registryManifestFunctorExpr {source target : CategoryExpr} :
    FunctorExpr source target → RegistryManifestFunctorExpr
  | .identity category => .identity (registryManifestCategoryExpr category)
  | .atomic id => .atomic id.raw
  | .classifierForget classifier host =>
      .classifierForget classifier.raw (registryManifestCategoryExpr host)
  | .opaquePort id => .opaquePort id.raw
  | .familyFibreInclusion family args =>
      .familyFibreInclusion family.raw (args.map registryManifestParameterExpr)
  | .familyReindex family morphism source target =>
      .familyReindex family.raw morphism.raw (source.map registryManifestParameterExpr)
        (target.map registryManifestParameterExpr)
  | .comp left right => .comp (registryManifestFunctorExpr left) (registryManifestFunctorExpr right)
  | .constructMap constructor functor =>
      .constructMap constructor.raw (registryManifestFunctorExpr functor)

private def registryManifestSchema : CategoryFamilySchema → String
  | .ring => "ring"
  | .commRing => "commRing"
  | .commRingModule => "commRingModule"
  | .commRingNat => "commRingNat"
  | .commRingIndexType => "commRingIndexType"
  | .domain => "domain"

private def registryManifest (state : RegistryState) : RegistryManifest :=
  let cats := state.categories.qsort (fun a b => a.id.raw < b.id.raw)
  let families := state.categoryFamilies.qsort (fun a b => a.id.raw < b.id.raw)
  let clfs := state.classifiers.qsort (fun a b => a.id.raw < b.id.raw)
  let functors := state.functors.qsort (fun a b => a.id.raw < b.id.raw)
  let opaqueEntries := state.opaqueCategories.qsort (fun a b => a.id.raw < b.id.raw)
  { schemaVersion := "0.3.0-semantic"
    categories := cats.map fun e => {
      id := e.id.raw, declaration := e.declaration.toString,
      realization := e.realization.toString,
      refinementRealization := e.refinementRealization.map Lean.Name.toString |>.getD "",
      expression := registryManifestCategoryExpr e.expression }
    classifiers := clfs.map fun e => {
      id := e.id.raw,
      host := registryManifestCategoryExpr e.host, declaration := e.declaration.toString,
      realization := e.realization.toString }
    functors := functors.map fun e => {
      id := e.id.raw,
      source := registryManifestCategoryExpr e.source, target := registryManifestCategoryExpr e.target,
      declaration := e.declaration.toString, realization := e.realization.toString,
      expression := registryManifestFunctorExpr e.expression, structural := e.structural }
    opaqueCategories := opaqueEntries.map fun e => {
      id := e.id.raw, declaration := e.declaration.toString, realization := e.realization.toString,
      reason := e.reason,
      ports := e.ports.map fun p => {
        id := p.id.raw, source := registryManifestCategoryExpr p.source,
        target := registryManifestCategoryExpr p.target, declaration := p.declaration.toString,
        realization := p.realization.toString, provenance := p.provenance } }
    categoryFamilies := families.map fun e => {
      id := e.id.raw,
      schema := registryManifestSchema e.schema,
      realization := e.realization.toString, transport := e.transport.toString,
      parameters := e.schema.parameterMetadata.map fun parameter => {
        ids := parameter.ids.toArray.map (·.raw), name := parameter.name,
        kind := parameter.kind.raw, dependency := parameter.dependency },
      variance := e.transportSemantics.variance.raw }
    fibrations := (state.fibrations.qsort (fun a b => a.id.raw < b.id.raw)).map fun e => {
      id := e.id.raw, projection := e.projection.raw,
      variance := match e.variance with
        | .cartesian => "cartesian"
        | .cocartesian => "cocartesian",
      evidence := e.evidence.toString }
    constructors := (state.constructors.qsort (fun a b => a.id.raw < b.id.raw)).map fun e => {
      id := e.id.raw, semantics := e.semantics.toString,
      signature := e.signature.map fun
        | .category => "category"
        | .object => "object"
        | .functor => "functor" }
    methods := (state.methods.qsort (fun a b => a.id.raw < b.id.raw)).map fun e => {
      id := e.id.raw, name := e.name, owner := registryManifestCategoryExpr e.owner,
      functor := e.functor.raw,
      shape := match e.shape with
        | .object => "object"
        | .isoInvariant => "isoInvariant",
      returnsToSource := e.returnsToSource }
    properties := (state.properties.qsort (fun a b => a.id.raw < b.id.raw)).map fun e => {
      id := e.id.raw, name := e.name, classifier := e.classifier.raw,
      receiver := e.receiver.map registryManifestCategoryExpr }
    lifts := (state.lifts.qsort (fun a b => a.id.raw < b.id.raw)).map fun e => {
      id := e.id.raw, edge := e.edge.label, evidence := e.evidence.toString
      kind := match e.kind with
        | .subobjects => "subobjects"
        | .createsLimits shape => s!"creates_limits:{shape}" }
    cells := (state.cells.qsort (fun a b => a.id.raw < b.id.raw)).map fun e => {
      id := e.id.raw, source := registryManifestCategoryExpr e.source,
      target := registryManifestCategoryExpr e.target, left := e.left.map (·.label),
      right := e.right.map (·.label), declaration := e.declaration.toString,
      invertible := e.invertible }
    limits := (state.limits.qsort (fun a b => a.id.raw < b.id.raw)).map fun e => {
      id := e.id.raw, category := e.category.raw, shape := e.shape,
      declaration := e.declaration.toString, colimit := e.colimit }
    adjunctions := (state.adjunctions.qsort (fun a b => a.id.raw < b.id.raw)).map fun e => {
      id := e.id.raw, left := e.left.raw, right := e.right.raw,
      declaration := e.declaration.toString }
    objects := (state.objects.qsort (fun a b => a.id.raw < b.id.raw)).map fun e => {
      id := e.id.raw, category := e.category.raw, declaration := e.declaration.toString }
    source := "lean-registry" }

private def registryManifestJson (state : RegistryState) : Json := toJson (registryManifest state)

/-- The ids of `kind` that the manifest exports are exactly the ids the registry state registers:
none missing, none extra, none substituted, and each named by one row. The registry state, which
`lean-categories` alone writes, is the reference; no downstream list of its rows is kept. -/
def validateProjection (kind : String) (registered exported : Array String) :
    Except String Unit := do
  let repeated := exported.foldl (init := #[]) fun out id =>
    if (exported.filter (· == id)).size > 1 && !out.contains id then out.push id else out
  unless repeated.isEmpty do
    throw s!"exported {kind}: stable ids name several rows: {repeated}"
  let missing := registered.filter (!exported.contains ·)
  let extra := exported.filter (!registered.contains ·)
  unless missing.isEmpty && extra.isEmpty do
    throw s!"exported {kind} are not the registered ones: missing {missing}, not registered {extra}"

/-- The manifest is a faithful projection of `state`: every row kind exports exactly the rows the
state registers (`validateProjection`). -/
def validateManifestProjection (state : RegistryState) (manifest : RegistryManifest) :
    Except String Unit := do
  validateProjection "categories" (state.categories.map (·.id.raw)) (manifest.categories.map (·.id))
  validateProjection "category families" (state.categoryFamilies.map (·.id.raw))
    (manifest.categoryFamilies.map (·.id))
  validateProjection "classifiers" (state.classifiers.map (·.id.raw)) (manifest.classifiers.map (·.id))
  validateProjection "functors" (state.functors.map (·.id.raw)) (manifest.functors.map (·.id))
  validateProjection "constructors" (state.constructors.map (·.id.raw))
    (manifest.constructors.map (·.id))
  validateProjection "fibrations" (state.fibrations.map (·.id.raw)) (manifest.fibrations.map (·.id))
  validateProjection "methods" (state.methods.map (·.id.raw)) (manifest.methods.map (·.id))
  validateProjection "properties" (state.properties.map (·.id.raw)) (manifest.properties.map (·.id))
  validateProjection "lifts" (state.lifts.map (·.id.raw)) (manifest.lifts.map (·.id))
  validateProjection "cells" (state.cells.map (·.id.raw)) (manifest.cells.map (·.id))
  validateProjection "limits" (state.limits.map (·.id.raw)) (manifest.limits.map (·.id))
  validateProjection "adjunctions" (state.adjunctions.map (·.id.raw)) (manifest.adjunctions.map (·.id))
  validateProjection "objects" (state.objects.map (·.id.raw)) (manifest.objects.map (·.id))
  validateProjection "opaque categories" (state.opaqueCategories.map (·.id.raw))
    (manifest.opaqueCategories.map (·.id))
  validateProjection "opaque ports"
    (state.opaqueCategories.flatMap fun c => c.ports.map (·.id.raw))
    (manifest.opaqueCategories.flatMap fun c => c.ports.map (·.id))

/-- The stable ids of each row kind of `manifest`, opaque ports included. -/
def manifestRowIds (manifest : RegistryManifest) : Array (String × Array String) :=
  #[("categories", manifest.categories.map (·.id)),
    ("category families", manifest.categoryFamilies.map (·.id)),
    ("classifiers", manifest.classifiers.map (·.id)),
    ("functors", manifest.functors.map (·.id)),
    ("constructors", manifest.constructors.map (·.id)),
    ("fibrations", manifest.fibrations.map (·.id)),
    ("methods", manifest.methods.map (·.id)),
    ("properties", manifest.properties.map (·.id)),
    ("lifts", manifest.lifts.map (·.id)),
    ("cells", manifest.cells.map (·.id)),
    ("limits", manifest.limits.map (·.id)),
    ("adjunctions", manifest.adjunctions.map (·.id)),
    ("objects", manifest.objects.map (·.id)),
    ("opaque categories", manifest.opaqueCategories.map (·.id)),
    ("opaque ports", manifest.opaqueCategories.flatMap fun c => c.ports.map (·.id))]

/-- `read` has exactly the rows of `reference`, kind by kind (`validateProjection`): a row that
`lean-categories` registers and the reader does not see is lost, and fails. -/
def validateSameRows (reference read : RegistryManifest) : Except String Unit :=
  (manifestRowIds reference).zip (manifestRowIds read) |>.forM fun ((kind, registered), (_, seen)) =>
    validateProjection kind registered seen

/-- Return the manifest produced from the checked persistent registry state, checked to be a
faithful projection of it. -/
def checkedRegistryManifestDTO : CoreM RegistryManifest := do
  let state ← registryState
  match validatePersistedSemanticState state.toSemanticState with
  | .error message => throwError message
  | .ok () =>
    let manifest := registryManifest state
    match validateManifestProjection state manifest with
    | .error message => throwError message
    | .ok () => pure manifest

def checkedRegistryManifest : CoreM Json := do
  return toJson (← checkedRegistryManifestDTO)

end CasCatalogue
