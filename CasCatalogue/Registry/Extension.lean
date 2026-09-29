/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CasCatalogue.Registry.Entry
public import CasCatalogue.Registry.Typed
public import CasCatalogue.Action
public import CasCatalogue.Decide
public import CasCatalogue.Lift
public import Mathlib.CategoryTheory.Core
public import LeanCategories.CategoryTheory.OneCat.Classifier
public import CasCatalogue.Realization
public import CasCatalogue.FamilyFibration
public import LeanCategories.ForMathlib.Cofibered
public import Lean.Data.Json
public import Lean
public meta import CasCatalogue.Syntax

@[expose] public section

set_option backward.privateInPublic true

/-!
# Persistent registry extension

`addImportedFn` receives `Array (Array RegistryEntry)` from imported modules.
-/

namespace CasCatalogue
open LeanCategories

open Lean
open Lean Meta
open Lean Elab Command

inductive RegistryEntry
  | category (e : NamedCategoryEntry)
  | categoryFamily (e : CategoryFamilyEntry)
  | classifier (e : ClassifierEntry)
  | functor (e : FunctorEntry)
  | opaque (e : OpaqueCategoryEntry)
  | fibration (e : FibrationEntry)
  | constructor (e : ConstructorEntry)
  | action (e : FunctorActionEntry)
  | method (e : MethodEntry)
  | comparison (e : ComparisonEntry)
  | property (e : PropertyEntry)
  | decider (e : DeciderEntry)
  | lift (e : LiftEntry)
  | realizer (e : RealizerEntry)
  | implementation (e : ImplementationEntry)
  | handleIso (e : HandleIsoEntry)
  deriving Repr

/-- Stable identifier represented by a heterogeneous registry entry. -/
def RegistryEntry.stableId : RegistryEntry → String
  | .category e => e.id.raw
  | .categoryFamily e => e.id.raw
  | .classifier e => e.id.raw
  | .functor e => e.id.raw
  | .opaque e => e.id.raw
  | .fibration e => e.id.raw
  | .constructor e => e.id.raw
  | .action e => e.id.raw
  | .method e => e.id.raw
  | .comparison e => e.id.raw
  | .property e => e.id.raw
  | .decider e => e.id.raw
  | .lift e => e.id.raw
  | .realizer e => e.id.raw
  | .implementation e => e.id.raw
  | .handleIso e => e.id.raw

/-- Lean declarations that must resolve before this row can be persisted. -/
def RegistryEntry.declarations : RegistryEntry → Array Name
  | .category e => #[e.declaration, e.realization] ++ match e.refinementRealization with
      | some realization => #[realization]
      | none => #[]
  | .categoryFamily e => #[e.realization, e.transport]
  | .classifier e => #[e.declaration, e.realization]
  | .functor e => #[e.declaration, e.realization]
  | .opaque e => #[e.declaration, e.realization] ++
      e.ports.flatMap fun p => #[p.declaration, p.realization]
  | .fibration e => #[e.evidence]
  | .constructor e => #[e.semantics] ++ e.functorialAction.toArray
  | .action e => #[e.realization]
  | .method _ => #[]
  | .comparison e => #[e.evidence]
  | .property _ => #[]
  | .decider e => #[e.realization]
  | .lift e => #[e.evidence]
  | .realizer e => #[e.denotation]
  | .implementation e => #[e.realization]
  | .handleIso e => #[e.source, e.target, e.evidence]

structure RegistryState where
  categories : Array NamedCategoryEntry := #[]
  categoryFamilies : Array CategoryFamilyEntry := #[]
  classifiers : Array ClassifierEntry := #[]
  functors : Array FunctorEntry := #[]
  opaqueCategories : Array OpaqueCategoryEntry := #[]
  fibrations : Array FibrationEntry := #[]
  constructors : Array ConstructorEntry := #[]
  actions : Array FunctorActionEntry := #[]
  methods : Array MethodEntry := #[]
  comparisons : Array ComparisonEntry := #[]
  properties : Array PropertyEntry := #[]
  deciders : Array DeciderEntry := #[]
  lifts : Array LiftEntry := #[]
  realizers : Array RealizerEntry := #[]
  implementations : Array ImplementationEntry := #[]
  handleIsos : Array HandleIsoEntry := #[]
  deriving Inhabited

/-- Registered category-constructor lookup by stable ID. -/
def RegistryState.constructor? (state : RegistryState) (id : ConstructorId) :
    Option ConstructorEntry :=
  state.constructors.find? fun entry => entry.id == id

def RegistryState.opaquePortIds (state : RegistryState) : List OpaquePortId :=
  state.opaqueCategories.toList.flatMap fun category => category.ports.toList.map (·.id)

/-- Registered functor lookup by stable ID. -/
def RegistryState.functor? (state : RegistryState) (id : FunctorId) : Option FunctorEntry :=
  state.functors.find? fun entry => entry.id == id

/-- Registered category-family lookup by stable ID. -/
def RegistryState.categoryFamily? (state : RegistryState) (id : CategoryFamilyId) :
    Option CategoryFamilyEntry :=
  state.categoryFamilies.find? fun entry => entry.id == id

def RegistryState.category? (state : RegistryState) (expression : CategoryExpr) :
    Option NamedCategoryEntry :=
  let candidates := state.categories.filter fun entry => entry.expression.syntacticEq expression;
  (if candidates.size == 1 then candidates[0]? else none)

def RegistryState.classifier? (state : RegistryState) (id : ClassifierId) :
    Option ClassifierEntry :=
  state.classifiers.find? fun entry => entry.id == id

/-- Typed opaque-port lookup by stable ID. -/
def RegistryState.opaquePort? (state : RegistryState) (id : OpaquePortId) : Option StructuralPortEntry :=
  state.opaqueCategories.foldl (fun found category =>
    match found with
    | some _ => found
    | none => category.ports.find? fun port => port.id == id) none

/-- Whether a route step names registered rows (a derived `c(U)` needs `c`'s functorial action). -/
def EdgeRef.isRegisteredIn (state : RegistryState) : EdgeRef → Bool
  | .functor id => (state.functor? id).isSome
  | .classifierForget id => (state.classifier? id).isSome
  | .constructMap constructor inner =>
      (state.constructor? constructor).any (·.functorialAction.isSome) &&
        inner.isRegisteredIn state

def duplicateOpaquePortId : List OpaquePortId → Option OpaquePortId
  | [] => none
  | port :: ports =>
      if ports.any fun other => other == port then some port
      else duplicateOpaquePortId ports

def duplicateOpaqueCategoryId : List CategoryId → Option CategoryId
  | [] => none
  | category :: categories =>
      if categories.any fun other => other == category then some category
      else duplicateOpaqueCategoryId categories

def duplicateCategoryExpressionList : List NamedCategoryEntry → Option CategoryExpr
  | [] => none
  | category :: categories =>
      if categories.any fun other => other.expression.syntacticEq category.expression then
        some category.expression
      else duplicateCategoryExpressionList categories

def opaqueCategoryMatchesCategory (category : NamedCategoryEntry)
    (opaqueEntry : OpaqueCategoryEntry) : Bool :=
  category.id == opaqueEntry.id && category.declaration == opaqueEntry.declaration &&
    category.realization == opaqueEntry.realization &&
    category.expression.syntacticEq (.opaque category.id)

def categoryIdMatchesExpression (id : CategoryId) (expression : CategoryExpr) : Bool :=
  match expression with
  | .atom expressionId | .opaque expressionId => expressionId == id
  | _ => true

/-- Whether two symbolic category endpoints are syntactically identical. -/
def sameEndpoint (left right : CategoryExpr) : Bool :=
  left.syntacticEq right

def RegistryState.duplicateCategoryExpression (state : RegistryState) : Option CategoryExpr :=
  duplicateCategoryExpressionList state.categories.toList

private def duplicateCategoryExpressionProbeState : RegistryState :=
  { categories := #[
      { id := ⟨"probe.expression.first"⟩,
        declaration := ``sameEndpoint, expression := .atom ⟨"probe.expression"⟩,
        realization := ``sameEndpoint },
      { id := ⟨"probe.expression.second"⟩,
        declaration := ``sameEndpoint, expression := .atom ⟨"probe.expression"⟩,
        realization := ``sameEndpoint }] }

example : duplicateCategoryExpressionProbeState.duplicateCategoryExpression.isSome := by
  native_decide

example : duplicateCategoryExpressionProbeState.category? (.atom ⟨"probe.expression"⟩) = none := by
  native_decide

/-- Whether an expression denotes the stable category ID of an opaque port endpoint. -/
def denotesCategory (expression : CategoryExpr) (endpoint : CategoryExpr) : Bool :=
  expression.syntacticEq endpoint

def refinementDepth : CategoryExpr → Nat
  | .refine parent _ => refinementDepth parent + 1
  | _ => 0

def refinementHostInChainFuel (_state : RegistryState) (target : CategoryExpr) :
    Nat → CategoryExpr → Bool
  | 0, _ => false
  | fuel + 1, expression =>
      if sameEndpoint target expression then true
      else if _state.functors.any (fun functor =>
          functor.source.syntacticEq expression && functor.target.syntacticEq target) then
        -- A registered functor from the base to the host is a structural route.
        true
      else match expression with
        | .refine parent classifier =>
            (_state.classifier? classifier).any fun entry =>
              refinementHostInChainFuel _state entry.host fuel parent &&
                (refinementHostInChainFuel _state target fuel parent ||
                  refinementHostInChainFuel _state target fuel (.classifierTotal classifier))
        | .atom id =>
            match _state.categories.find? (·.id == id) with
            | some entry =>
                if sameEndpoint entry.expression expression then
                  false
                else
                  refinementHostInChainFuel _state target fuel entry.expression
            | none => false
        | .opaque id =>
            _state.opaqueCategories.any fun entry =>
              entry.id == id && entry.ports.any fun port => sameEndpoint port.target target
        | _ => false

/-- A refinement descends from both its parent and its classifier total. -/
def refinementHostInChain (state : RegistryState) (target : CategoryExpr)
    (expression : CategoryExpr) : Bool :=
  refinementHostInChainFuel state target
    (refinementDepth expression + state.categories.size + state.opaqueCategories.size + 1) expression

private def ancestryProbeState : RegistryState :=
  { classifiers := #[
      { id := ⟨"clf.first"⟩,
        declaration := ``sameEndpoint, host := .atom ⟨"cat.host"⟩
        realization := ``sameEndpoint,},
      { id := ⟨"clf.second"⟩,
        declaration := ``sameEndpoint, host := .atom ⟨"cat.host"⟩
        realization := ``sameEndpoint,}] }

example : refinementHostInChain ancestryProbeState (.atom ⟨"cat.host"⟩)
    (.refine (.refine (.atom ⟨"cat.host"⟩) ⟨"clf.first"⟩) ⟨"clf.second"⟩) := by
  native_decide

example : !refinementHostInChain ancestryProbeState (.atom ⟨"cat.host"⟩)
    (.refine (.atom ⟨"cat.other"⟩) ⟨"clf.latest"⟩) := by
  native_decide

example : !categoryIdMatchesExpression ⟨"cat.host"⟩ (.atom ⟨"cat.other"⟩) := by
  native_decide

example : !categoryIdMatchesExpression ⟨"cat.named"⟩ (.opaque ⟨"cat.other"⟩) := by
  native_decide

example : duplicateOpaquePortId
    [⟨"port.same"⟩, ⟨"port.same"⟩] = some ⟨"port.same"⟩ := by
  native_decide

partial def CategoryExpr.isRegistered (state : RegistryState) : CategoryExpr → Bool
  | .atom id =>
      state.categories.any (·.id == id) || state.opaqueCategories.any (·.id == id)
  | .familyApp family args =>
      (state.categoryFamily? family).any fun entry =>
        CategoryFamilySchema.parameterArgsValid args entry.schema
  | .familyTotal family => (state.categoryFamily? family).isSome
  | .classifierTotal classifier => (state.classifier? classifier).isSome
  | .refine base classifier =>
      base.isRegistered state &&
        (state.classifier? classifier).isSome
  | .opaque id => state.categories.any (·.id == id) || state.opaqueCategories.any (·.id == id)
  | .construct constructor args =>
      (state.constructor? constructor).any fun entry =>
        entry.signature.size == args.size &&
          (entry.signature.zip args).all fun (kind, arg) =>
            match kind, arg with
            | .category, .category category => category.isRegistered state
            | .object, .object _ => true
            | .functor, .functor id => (state.functor? id).isSome
            | _, _ => false

/- The schema rejects a module whose base is not the selected ring. -/
example : !CategoryFamilySchema.parameterArgsValid #[.variable ParameterId.r]
    .commRingModule := by decide

/- A ring family cannot accept a dependent module parameter. -/
example : !CategoryFamilySchema.parameterArgsValid #[.variable ParameterId.r, .variable ParameterId.w]
    .ring := by decide

/-- Validate references within a typed functor expression against prior persistent entries. -/
partial def FunctorExpr.referencesValid (state : RegistryState)
    {source target : CategoryExpr} : FunctorExpr source target → Bool
  | .identity _ => true
  | .atomic _ => true
  | .classifierForget classifier host =>
      (state.classifier? classifier).any fun entry => sameEndpoint entry.host host
  | .opaquePort id =>
      match state.opaquePort? id with
      | some entry => denotesCategory source entry.source && denotesCategory target entry.target
      | none => false
  | .familyFibreInclusion family args =>
      (state.categoryFamily? family).any fun entry =>
        CategoryFamilySchema.parameterArgsValid args entry.schema
  | .familyReindex family _ sourceArgs targetArgs =>
      (state.categoryFamily? family).any fun entry =>
        CategoryFamilySchema.parameterArgsValid sourceArgs entry.schema &&
          CategoryFamilySchema.parameterArgsValid targetArgs entry.schema
  | .comp left right => left.referencesValid state && right.referencesValid state
  | .constructMap constructor functor =>
      (state.constructor? constructor).isSome && functor.referencesValid state

/-- Validate the cospan references of a pullback category before it is persisted. -/
partial def CategoryExpr.referencesValid (state : RegistryState) : CategoryExpr → Bool
  | .atom _ => true
  | .classifierTotal classifier => (state.classifier? classifier).isSome
  | .opaque _ => true
  | .familyApp family args =>
      match state.categoryFamily? family with
      | some entry => CategoryFamilySchema.parameterArgsValid args entry.schema
      | none => false
  | .familyTotal family => (state.categoryFamily? family).isSome
  | .construct constructor args =>
      (state.constructor? constructor).isSome &&
        args.all fun arg =>
          match arg with
          | .category category => category.referencesValid state
          | _ => true
  | .refine base classifier =>
      base.referencesValid state &&
        (state.classifier? classifier).any fun entry =>
          refinementHostInChain state entry.host base && entry.host.referencesValid state

private def RegistryState.apply : RegistryState → RegistryEntry → RegistryState
  | s, .category e => { s with categories := s.categories.push e }
  | s, .categoryFamily e => { s with categoryFamilies := s.categoryFamilies.push e }
  | s, .classifier e => { s with classifiers := s.classifiers.push e }
  | s, .functor e => { s with functors := s.functors.push e }
  | s, .opaque e => { s with opaqueCategories := s.opaqueCategories.push e }
  | s, .fibration e => { s with fibrations := s.fibrations.push e }
  | s, .constructor e => { s with constructors := s.constructors.push e }
  | s, .action e => { s with actions := s.actions.push e }
  | s, .method e => { s with methods := s.methods.push e }
  | s, .comparison e => { s with comparisons := s.comparisons.push e }
  | s, .property e => { s with properties := s.properties.push e }
  | s, .decider e => { s with deciders := s.deciders.push e }
  | s, .lift e => { s with lifts := s.lifts.push e }
  | s, .realizer e => { s with realizers := s.realizers.push e }
  | s, .implementation e => { s with implementations := s.implementations.push e }
  | s, .handleIso e => { s with handleIsos := s.handleIsos.push e }

def RegistryState.registryEntries (state : RegistryState) : List RegistryEntry :=
  state.categories.toList.map RegistryEntry.category ++
    state.categoryFamilies.toList.map RegistryEntry.categoryFamily ++
    state.classifiers.toList.map RegistryEntry.classifier ++
    state.functors.toList.map RegistryEntry.functor ++
    state.opaqueCategories.toList.map RegistryEntry.opaque ++
    state.fibrations.toList.map RegistryEntry.fibration ++
    state.constructors.toList.map RegistryEntry.constructor ++
    state.actions.toList.map RegistryEntry.action ++
    state.methods.toList.map RegistryEntry.method ++
    state.comparisons.toList.map RegistryEntry.comparison ++
    state.properties.toList.map RegistryEntry.property ++
    state.deciders.toList.map RegistryEntry.decider ++
    state.lifts.toList.map RegistryEntry.lift ++
    state.realizers.toList.map RegistryEntry.realizer ++
    state.implementations.toList.map RegistryEntry.implementation ++
    state.handleIsos.toList.map RegistryEntry.handleIso

def registryEntryPairAllowed : RegistryEntry → RegistryEntry → Bool
  | .category category, right =>
      match right with
      | .opaque opaqueEntry => opaqueCategoryMatchesCategory category opaqueEntry
      | _ => false
  | .opaque opaqueEntry, right =>
      match right with
      | .category category => opaqueCategoryMatchesCategory category opaqueEntry
      | _ => false
  | _, _ => false

def duplicateRegistryEntryId : List RegistryEntry → Option String
  | [] => none
  | entry :: entries =>
      if entries.any fun other =>
          other.stableId == entry.stableId && !registryEntryPairAllowed entry other then
        some entry.stableId
      else duplicateRegistryEntryId entries

def RegistryState.duplicateEntryId (state : RegistryState) : Option String :=
  duplicateRegistryEntryId state.registryEntries

/-- Whether this entry's stable ID conflicts with a retained registry entry. -/
def RegistryState.hasEntryId : RegistryState → RegistryEntry → Bool
  | state, entry => state.registryEntries.any fun existing =>
      existing.stableId == entry.stableId && !registryEntryPairAllowed existing entry

private def duplicateImportedOpaquePortId (as : Array (Array RegistryEntry)) : Option OpaquePortId :=
  duplicateOpaquePortId
    (RegistryState.opaquePortIds (mkStateFromImportedEntries RegistryState.apply {} as))

private def duplicateImportedOpaqueCategoryId (as : Array (Array RegistryEntry)) : Option CategoryId :=
  duplicateOpaqueCategoryId
    ((mkStateFromImportedEntries RegistryState.apply {} as).opaqueCategories.toList.map (·.id))

private def importedOpaquePortProbeEntries : Array (Array RegistryEntry) := #[
  #[RegistryEntry.opaque {
    id := ⟨"cat.first"⟩, declaration := ``sameEndpoint, realization := ``sameEndpoint,
    ports := #[StructuralPortEntry.mk ⟨"port.imported"⟩ (.atom ⟨"cat.first"⟩)
      (.atom ⟨"cat.first"⟩) ``sameEndpoint ``sameEndpoint "probe"],
    reason := "probe",}],
  #[RegistryEntry.opaque {
    id := ⟨"cat.second"⟩, declaration := ``sameEndpoint, realization := ``sameEndpoint,
    ports := #[StructuralPortEntry.mk ⟨"port.imported"⟩ (.atom ⟨"cat.second"⟩)
      (.atom ⟨"cat.second"⟩) ``sameEndpoint ``sameEndpoint "probe"],
    reason := "probe",}] ]

example : duplicateImportedOpaquePortId importedOpaquePortProbeEntries =
    some ⟨"port.imported"⟩ := by
  native_decide

private def duplicateImportedStableIdProbeEntries : Array (Array RegistryEntry) := #[
  #[RegistryEntry.category {
    id := ⟨"probe.duplicate"⟩,
    declaration := ``sameEndpoint, expression := .atom ⟨"probe.duplicate"⟩,
    realization := ``sameEndpoint,}],
  #[RegistryEntry.classifier {
    id := ⟨"probe.duplicate"⟩,
    declaration := ``sameEndpoint, host := .atom ⟨"probe.duplicate"⟩,
    realization := ``sameEndpoint,}]]

example : RegistryState.duplicateEntryId
    (mkStateFromImportedEntries RegistryState.apply {} duplicateImportedStableIdProbeEntries) =
    some "probe.duplicate" := by
  native_decide

private def allRegistryKindsDuplicateProbeState : RegistryState :=
  { categories := #[{
      id := ⟨"probe.all-kinds"⟩,
      declaration := ``sameEndpoint, expression := .atom ⟨"probe.all-kinds"⟩,
      realization := ``sameEndpoint,}]
    categoryFamilies := #[{
      id := ⟨"probe.all-kinds"⟩, schema := .ring,
      realization := ``sameEndpoint, transport := ``sameEndpoint,
      transportSemantics := .restrictionOfScalars }]
    classifiers := #[{
      id := ⟨"probe.all-kinds"⟩,
      declaration := ``sameEndpoint, host := .atom ⟨"probe.all-kinds"⟩,
      realization := ``sameEndpoint,}]
    functors := #[{
      id := ⟨"probe.all-kinds"⟩,
      source := .atom ⟨"probe.all-kinds"⟩, target := .atom ⟨"probe.all-kinds"⟩,
      declaration := ``sameEndpoint, realization := ``sameEndpoint,
      expression := .atomic ⟨"probe.all-kinds"⟩ }]
    opaqueCategories := #[{
      id := ⟨"probe.all-kinds"⟩, declaration := ``sameEndpoint,
      realization := ``sameEndpoint, ports := #[], reason := "probe",}] }

example : allRegistryKindsDuplicateProbeState.duplicateEntryId = some "probe.all-kinds" := by
  decide

private def localCrossKindDuplicateProbeState : RegistryState :=
  { categories := #[{
      id := ⟨"probe.local-duplicate"⟩,
      declaration := ``sameEndpoint, expression := .atom ⟨"probe.local-duplicate"⟩,
      realization := ``sameEndpoint,}] }

private def localCrossKindDuplicateProbeEntry : RegistryEntry := .classifier {
  id := ⟨"probe.local-duplicate"⟩,
  declaration := ``sameEndpoint, host := .atom ⟨"probe.local-duplicate"⟩,
  realization := ``sameEndpoint,}

example : localCrossKindDuplicateProbeState.hasEntryId localCrossKindDuplicateProbeEntry := by
  native_decide

private def localNamedOpaqueCompanionProbeState : RegistryState :=
  { categories := #[{
      id := ⟨"probe.local-companion"⟩,
      declaration := ``sameEndpoint, expression := .opaque ⟨"probe.local-companion"⟩,
      realization := ``sameEndpoint,}] }

private def localNamedOpaqueCompanionProbeEntry : RegistryEntry := .opaque {
  id := ⟨"probe.local-companion"⟩, declaration := ``sameEndpoint,
  realization := ``sameEndpoint, ports := #[], reason := "probe",}

example : !localNamedOpaqueCompanionProbeState.hasEntryId
    localNamedOpaqueCompanionProbeEntry := by
  native_decide

example : !opaqueCategoryMatchesCategory
    { id := ⟨"cat.fake.opaque"⟩,
      declaration := ``sameEndpoint, expression := .opaque ⟨"existing"⟩,
      realization := ``sameEndpoint,}
    { id := ⟨"cat.fake.opaque"⟩, declaration := ``sameEndpoint,
      realization := ``sameEndpoint, ports := #[], reason := "probe",} := by
  have differentIds : !((.opaque ⟨"existing"⟩ : CategoryExpr).syntacticEq
      (.opaque ⟨"cat.fake.opaque"⟩)) := by
    native_decide
  simp [opaqueCategoryMatchesCategory, differentIds]

private def validatePersistedRegistryState (state : RegistryState) : Except String Unit := do
  if let some id := state.duplicateEntryId then
    throw s!"duplicate normalized-category registry ID {id}"
  if let some _ := state.duplicateCategoryExpression then
    throw "duplicate normalized-category registry expression"
  if let some id := duplicateOpaquePortId state.opaquePortIds then
    throw s!"duplicate opaque port ID {id.raw}"
  for category in state.categories do
    let isSelf := match category.expression with
      | .atom id | .opaque id => id == category.id
      | _ => false
    unless categoryIdMatchesExpression category.id category.expression do
      throw s!"category entry {category.id.raw} does not use its own category expression ID"
    unless isSelf ||
        (category.expression.isRegistered state && category.expression.referencesValid state) do
      throw s!"category entry {category.id.raw} has an unresolved registry reference"
    match category.expression with
    | .opaque _ =>
        unless (state.opaqueCategories.filter (opaqueCategoryMatchesCategory category)).size == 1 do
          throw s!"opaque category entry {category.id.raw} has no unique matching companion"
    | _ => pure ()
  for functor in state.functors do
    unless functor.source.isRegistered state && functor.target.isRegistered state &&
        functor.source.referencesValid state && functor.target.referencesValid state &&
        functor.expression.referencesValid state do
      throw s!"functor entry {functor.id.raw} has an unresolved registry reference"
  for classifier in state.classifiers do
    unless classifier.host.isRegistered state && classifier.host.referencesValid state do
      throw s!"classifier entry {classifier.id.raw} has an unresolved registry reference"
  for opaqueEntry in state.opaqueCategories do
    let some category := state.categories.find? (·.id == opaqueEntry.id)
      | throw s!"opaque category entry {opaqueEntry.id.raw} has no registered category"
    unless opaqueCategoryMatchesCategory category opaqueEntry do
      throw s!"opaque category entry {opaqueEntry.id.raw} does not match its registered category"
    unless opaqueEntry.ports.toList.all fun port =>
        port.source.syntacticEq (.opaque opaqueEntry.id) &&
          port.source.isRegistered state && port.target.isRegistered state do
      throw s!"opaque category entry {opaqueEntry.id.raw} has an invalid port source or endpoint"
  for fibration in state.fibrations do
    unless (state.functor? fibration.projection).isSome do
      throw s!"fibration entry {fibration.id.raw} has an unregistered projection"
  for action in state.actions do
    unless action.edge.isRegisteredIn state do
      throw s!"action entry {action.id.raw} realizes an unregistered functor"
  for method in state.methods do
    unless (state.functor? method.functor).isSome do
      throw s!"method entry {method.id.raw} names an unregistered functor"
  for comparison in state.comparisons do
    unless (comparison.left ++ comparison.right).all (·.isRegisteredIn state) do
      throw s!"comparison entry {comparison.id.raw} names an unregistered route step"
  for property in state.properties do
    unless (state.classifier? property.classifier).isSome do
      throw s!"property entry {property.id.raw} names an unregistered classifier"
  for decider in state.deciders do
    unless (state.classifier? decider.classifier).isSome do
      throw s!"decider entry {decider.id.raw} names an unregistered classifier"
  pure ()

private def registryValidationFailed (result : Except String Unit) : Bool :=
  match result with
  | .error _ => true
  | .ok _ => false

private def persistedOrphanOpaqueExpressionProbeState : RegistryState :=
  { categories := #[{
      id := ⟨"probe.persisted.orphan"⟩,
      declaration := ``sameEndpoint, expression := .opaque ⟨"probe.persisted.orphan"⟩,
      realization := ``sameEndpoint }] }

example : registryValidationFailed
    (validatePersistedRegistryState persistedOrphanOpaqueExpressionProbeState) := by
  decide

private def persistedWrongOpaquePortOwnerProbeState : RegistryState :=
  { categories := #[{
      id := ⟨"probe.persisted.owner"⟩,
      declaration := ``sameEndpoint, expression := .opaque ⟨"probe.persisted.owner"⟩,
      realization := ``sameEndpoint }]
    opaqueCategories := #[{
      id := ⟨"probe.persisted.owner"⟩, declaration := ``sameEndpoint,
      realization := ``sameEndpoint,
      ports := #[StructuralPortEntry.mk ⟨"probe.persisted.port"⟩
        (.atom ⟨"probe.persisted.owner"⟩) (.atom ⟨"probe.persisted.owner"⟩)
        ``sameEndpoint ``sameEndpoint "probe"],
      reason := "probe" }] }

example : registryValidationFailed
    (validatePersistedRegistryState persistedWrongOpaquePortOwnerProbeState) := by
  native_decide

private def importedWrongOpaquePortOwnerProbeEntries : Array (Array RegistryEntry) := #[
  #[RegistryEntry.category {
    id := ⟨"probe.imported.owner"⟩,
    declaration := ``sameEndpoint, expression := .opaque ⟨"probe.imported.owner"⟩,
    realization := ``sameEndpoint }],
  #[RegistryEntry.opaque {
    id := ⟨"probe.imported.owner"⟩, declaration := ``sameEndpoint,
    realization := ``sameEndpoint,
    ports := #[StructuralPortEntry.mk ⟨"probe.imported.port"⟩
      (.atom ⟨"probe.imported.owner"⟩) (.atom ⟨"probe.imported.owner"⟩)
      ``sameEndpoint ``sameEndpoint "probe"],
    reason := "probe" }]]

example : registryValidationFailed
    (validatePersistedRegistryState
      (mkStateFromImportedEntries RegistryState.apply {} importedWrongOpaquePortOwnerProbeEntries)) := by
  native_decide

private initialize registryExt : SimplePersistentEnvExtension RegistryEntry RegistryState ←
  registerSimplePersistentEnvExtension {
    addEntryFn := RegistryState.apply
    addImportedFn := fun as =>
      let state := mkStateFromImportedEntries RegistryState.apply {} as
      match validatePersistedRegistryState state with
      | .error message => panic! s!"invalid normalized-category registry in imported modules: {message}"
      | .ok () => state
}

/-- The registry state of the current environment, read-only. The only write path is
`addRegistryEntryChecked`, through the `normalized_registry` command. -/
def registryState : CoreM RegistryState :=
  return registryExt.getState (← getEnv)

/-- The result type of a declaration after exposing all of its parameters. -/
def declarationResultType (declaration : Name) : MetaM Expr := do
  let info ← getConstInfo declaration
  forallTelescopeReducing info.type fun _ result => pure result

/-- Require a declaration to return an actual category object. -/
def ensureCategoryDeclaration (declaration : Name) : MetaM Unit := do
  let result ← declarationResultType declaration
  unless result.isConstOf ``LeanCategories.ObjCat do
    throwError "registry declaration {declaration} must return ObjCat, but returns {result}"

/-- Require a category-realization declaration to have the typed witness form. -/
def ensureCategoryRealization (realization : Name) : MetaM Unit := do
  let result ← declarationResultType realization
  unless result.isAppOf ``CasCatalogue.CategoryRealization do
    throwError
      "registry realization {realization} must return CategoryRealization ..., but returns {result}"

def validateRegisteredCategoryEndpointRealization (state : RegistryState) (expression : CategoryExpr)
    (category realization : Expr) : MetaM Unit := do
  let realizationType ← withTransparency .all <| whnf (← inferType realization)
  unless realizationType.isAppOf ``CasCatalogue.CategoryRealization do
    throwError "category endpoint realization is not a CategoryRealization"
  let realizationArgs := realizationType.getAppArgs
  unless realizationArgs.size == 2 do
    throwError "category endpoint realization has malformed parameters"
  unless ← withTransparency .all <| isDefEq (Lean.toExpr expression) realizationArgs[0]! do
    throwError "category endpoint realization has the wrong expression"
  unless ← withTransparency .all <| isDefEq category realizationArgs[1]! do
    throwError "category endpoint realization has the wrong category"
  let familyFibre ← withTransparency .all do
    mkAppM ``CasCatalogue.CategoryRealization.familyFibre #[realization]
  let familyFibre ← withTransparency .all <| whnf familyFibre
  match expression with
  | .familyApp family familyArgs =>
      let familyEntry ← match state.categoryFamily? family with
        | some entry => pure entry
        | none => throwError "family endpoint has no registered family"
      unless CategoryFamilySchema.parameterArgsValid familyArgs familyEntry.schema do
        throwError "family endpoint has invalid parameter quotations"
      unless familyFibre.isAppOf ``Option.some do
        throwError "family endpoint realization has no typed fibre witness"
      let packed := familyFibre.getAppArgs.back!
      let witness := packed.getAppArgs.back!
      let witnessType ← withTransparency .all <| inferType witness
      let witnessTypeArgs := witnessType.getAppArgs
      unless witnessTypeArgs.size >= 5 do
        throwError "family endpoint realization has a malformed fibre witness"
      let witnessIdentifier := witnessTypeArgs[1]!
      let witnessRealization := witnessTypeArgs[4]!
      let familyValue ← mkAppM ``CasCatalogue.CategoryFamilyId.mk #[mkStrLit family.raw]
      unless ← withTransparency .all <| isDefEq witnessIdentifier familyValue do
        throwError "family endpoint realization has the wrong family witness"
      let registeredRealization ← mkConstWithFreshMVarLevels familyEntry.realization
      unless ← withTransparency .all <| isDefEq witnessRealization registeredRealization do
        throwError "family endpoint realization is not the exact registered family realization"
      let witnessArguments ← withTransparency .all do
        mkAppM ``CasCatalogue.CategoryFamilyFibreWitness.arguments #[witness]
      unless ← withTransparency .all <| isDefEq (Lean.toExpr familyArgs) witnessArguments do
        throwError "family endpoint realization has unrelated symbolic arguments"
      let categoryEq ← withTransparency .all do
        mkAppM ``CasCatalogue.CategoryFamilyFibreWitness.category_eq #[witness]
      let categoryEqType ← withTransparency .all <| inferType categoryEq
      unless categoryEqType.isEq do
        throwError "family endpoint realization has no category equality witness"
      unless ← withTransparency .all <| isDefEq categoryEqType.getAppArgs[1]! category do
        throwError "family endpoint realization has the wrong category witness"
  | _ =>
      let entry ← match state.category? expression with
        | some entry => pure entry
        | none => throwError "category endpoint has no registered category realization"
      let registeredRealization ← mkConstWithFreshMVarLevels entry.realization
      let registeredType ← inferType registeredRealization
      let (parameters, _, _) ← forallMetaTelescopeReducing registeredType
      let registeredValue := mkAppN registeredRealization parameters
      unless ← withTransparency .all <| isDefEq realization registeredValue do
        throwError
          "category endpoint realization is not the exact registered realization {entry.realization}"
      unless familyFibre.isAppOfArity ``Option.none 1 do
        throwError "non-family endpoint realization has a family fibre witness"

def validateClassifierTotalEndpointRealization (state : RegistryState)
    (classifier : ClassifierId) (category realization : Expr) : MetaM Unit := do
  let classifierEntry ← match state.classifier? classifier with
    | some entry => pure entry
    | none => throwError "classifier endpoint {classifier.raw} has no registered classifier"
  let realizationType ← withTransparency .all <| whnf (← inferType realization)
  unless realizationType.isAppOf ``CasCatalogue.CategoryRealization do
    throwError "classifier total realization is not a CategoryRealization"
  let realizationArgs := realizationType.getAppArgs
  unless realizationArgs.size == 2 do
    throwError "classifier total realization has malformed parameters"
  let expression : CategoryExpr := .classifierTotal classifier
  unless ← withTransparency .all <| isDefEq (Lean.toExpr expression) realizationArgs[0]! do
    throwError "classifier total realization has the wrong expression"
  unless ← withTransparency .all <| isDefEq category realizationArgs[1]! do
    throwError "classifier total realization has the wrong category"
  let registeredConstant ← mkConstWithFreshMVarLevels classifierEntry.realization
  let registeredType ← inferType registeredConstant
  let (parameters, _, _) ← forallMetaTelescopeReducing registeredType
  let registeredValue := mkAppN registeredConstant parameters
  let registeredTotal ← withTransparency .all do
    mkAppM ``CasCatalogue.ClassifierRealization.totalRealization #[registeredValue]
  unless ← withTransparency .all <| isDefEq realization registeredTotal do
    throwError "classifier total realization is not the exact registered classifier realization"
  let familyFibre ← withTransparency .all do
    mkAppM ``CasCatalogue.CategoryRealization.familyFibre #[realization]
  let familyFibre ← withTransparency .all <| whnf familyFibre
  unless familyFibre.isAppOfArity ``Option.none 1 do
    throwError "non-family classifier total realization has a family fibre witness"

def validateRefinementEndpointRealization (state : RegistryState)
    (base : CategoryExpr) (classifier : ClassifierId) : MetaM Unit := do
  let classifierEntry ← match state.classifier? classifier with
    | some entry => pure entry
    | none => throwError "refinement classifier {classifier.raw} has no registered classifier"
  unless refinementHostInChain state classifierEntry.host base do
    throwError "refinement classifier {classifier.raw} has no registered host ancestry"

/-- A constructed category `.construct c args` must be definitionally the constructor's
semantics applied to the registered denotations of its arguments: a category argument is the
registered declaration of that category expression, a functor argument the registered
declaration of that functor, and an object argument ranges over the declaration's own
parameters. -/
def validateConstructedCategory (state : RegistryState) (constructor : ConstructorId)
    (args : Array ConstructorArg) (category : Expr) : MetaM Unit := do
  let entry ← match state.constructor? constructor with
    | some entry => pure entry
    | none => throwError "constructed category uses unregistered constructor {constructor.raw}"
  unless entry.signature.size == args.size do
    throwError "constructor {constructor.raw} applied to the wrong number of arguments"
  let semanticsConstant ← mkConstWithFreshMVarLevels entry.semantics
  let (semanticsArgs, binderInfos, _) ←
    forallMetaTelescopeReducing (← inferType semanticsConstant)
  let explicitArgs := (semanticsArgs.zip binderInfos).filter (·.2.isExplicit) |>.map (·.1)
  unless explicitArgs.size == args.size do
    throwError "constructor {constructor.raw} semantics has the wrong arity"
  for (arg, target) in args.zip explicitArgs do
    match arg with
    | .category categoryExpr =>
        let categoryEntry ← match state.category? categoryExpr with
          | some e => pure e
          | none => throwError
              "constructor {constructor.raw} argument is not a registered category"
        let declarationConstant ← mkConstWithFreshMVarLevels categoryEntry.declaration
        let (declarationArgs, _, _) ←
          forallMetaTelescopeReducing (← inferType declarationConstant)
        unless ← withTransparency .all <|
            isDefEq target (mkAppN declarationConstant declarationArgs) do
          throwError "constructor {constructor.raw} category argument does not match"
    | .functor functorId =>
        let functorEntry ← match state.functor? functorId with
          | some e => pure e
          | none => throwError
              "constructor {constructor.raw} argument is not a registered functor"
        let declarationConstant ← mkConstWithFreshMVarLevels functorEntry.declaration
        let (declarationArgs, _, _) ←
          forallMetaTelescopeReducing (← inferType declarationConstant)
        let declarationValue := mkAppN declarationConstant declarationArgs
        let declarationType ← whnf (← inferType declarationValue)
        let functorValue ← if declarationType.isAppOf ``CategoryTheory.Cat.Hom then
            mkAppM ``CategoryTheory.Cat.Hom.toFunctor #[declarationValue]
          else
            pure declarationValue
        unless ← withTransparency .all <| isDefEq target functorValue do
          throwError "constructor {constructor.raw} functor argument does not match"
    | .object _ => pure ()
  unless ← withTransparency .all <|
      isDefEq category (mkAppN semanticsConstant semanticsArgs) do
    throwError
      "constructed category is not {entry.semantics} applied to its registered arguments"

/-- A family-total endpoint must be the total category of the exact registered family
realization (`CategoryFamilyRealization.totalCat`). -/
def validateFamilyTotalEndpointRealization (state : RegistryState)
    (family : CategoryFamilyId) (category realization : Expr) : MetaM Unit := do
  let familyEntry ← match state.categoryFamily? family with
    | some entry => pure entry
    | none => throwError "family total {family.raw} has no registered family"
  let realizationType ← withTransparency .all <| whnf (← inferType realization)
  unless realizationType.isAppOf ``CasCatalogue.CategoryRealization do
    throwError "family total realization is not a CategoryRealization"
  let realizationArgs := realizationType.getAppArgs
  unless realizationArgs.size == 2 do
    throwError "family total realization has malformed parameters"
  let expression : CategoryExpr := .familyTotal family
  unless ← withTransparency .all <| isDefEq (Lean.toExpr expression) realizationArgs[0]! do
    throwError "family total realization has the wrong expression"
  unless ← withTransparency .all <| isDefEq category realizationArgs[1]! do
    throwError "family total realization has the wrong category"
  let registeredRealization ← mkConstWithFreshMVarLevels familyEntry.realization
  let registeredTotal ← withTransparency .all do
    mkAppM ``CasCatalogue.CategoryFamilyRealization.totalCat #[registeredRealization]
  unless ← withTransparency .all <| isDefEq category registeredTotal do
    throwError "family total {family.raw} is not the total category of its registered realization"
  let familyFibre ← withTransparency .all do
    mkAppM ``CasCatalogue.CategoryRealization.familyFibre #[realization]
  let familyFibre ← withTransparency .all <| whnf familyFibre
  unless familyFibre.isAppOfArity ``Option.none 1 do
    throwError "family total realization has a family fibre witness"

def validateCategoryEndpointRealization (state : RegistryState) (expression : CategoryExpr)
    (category realization : Expr) : MetaM Unit :=
  match expression with
  | .classifierTotal classifier =>
      validateClassifierTotalEndpointRealization state classifier category realization
  | .familyTotal family =>
      validateFamilyTotalEndpointRealization state family category realization
  | _ => validateRegisteredCategoryEndpointRealization state expression category realization

def validateRefinementDeclarationRealization (state : RegistryState)
    (expression : CategoryExpr) (declaration refinement : Name) : MetaM Unit := do
  let (expectedBase, expectedClassifier) ← match expression with
    | .refine base classifier => pure (base, classifier)
    | _ => throwError "refinement realization is attached to a non-refinement expression"
  let refinementConstant ← mkConstWithFreshMVarLevels refinement
  let refinementType ← inferType refinementConstant
  forallTelescopeReducing refinementType fun arguments refinementResult => do
    let refinementArgs := refinementResult.getAppArgs
    unless refinementArgs.size == 2 do
      throwError "refinement realization {refinement} has malformed parameters"
    unless ← withTransparency .all <| isDefEq (Lean.toExpr expression) refinementArgs[0]! do
      throwError "refinement realization {refinement} has the wrong expression"
    let declarationValue ← mkConstWithFreshMVarLevels declaration
    let declarationValue := mkAppN declarationValue arguments
    unless ← withTransparency .all <| isDefEq declarationValue refinementArgs[1]! do
      throwError "refinement declaration {declaration} has the wrong category"
    let refinementValue := mkAppN refinementConstant arguments
    let base ← withTransparency .all do
      mkAppM ``CasCatalogue.RefinementRealization.base #[refinementValue]
    let classifierId ← withTransparency .all do
      mkAppM ``CasCatalogue.RefinementRealization.classifierId #[refinementValue]
    unless ← withTransparency .all <| isDefEq base (Lean.toExpr expectedBase) do
      throwError "refinement realization {refinement} has the wrong base"
    unless ← withTransparency .all <| isDefEq classifierId (Lean.toExpr expectedClassifier) do
      throwError "refinement realization {refinement} has the wrong classifier"
    let classifier ← withTransparency .all do
      mkAppM ``CasCatalogue.RefinementRealization.classifier #[refinementValue]
    let classifierEntry ← match state.classifier? expectedClassifier with
      | some entry => pure entry
      | none => throwError "refinement realization {refinement} has an unregistered classifier"
    let classifierRealization ← withTransparency .all do
      mkAppM ``CasCatalogue.RefinementRealization.classifierRealization #[refinementValue]
    let classifierRealizationType ← withTransparency .all <| inferType classifierRealization
    let classifierArgs := classifierRealizationType.getAppArgs
    unless classifierArgs.size == 4 do
      throwError "refinement realization {refinement} has malformed classifier data"
    unless ← withTransparency .all <| isDefEq classifierArgs[0]! (Lean.toExpr classifierEntry.host) do
      throwError "refinement realization {refinement} has the wrong classifier host"
    unless ← withTransparency .all <| isDefEq classifierArgs[1]! (Lean.toExpr expectedClassifier) do
      throwError "refinement realization {refinement} has the wrong classifier ID"
    let registeredConstant ← mkConstWithFreshMVarLevels classifierEntry.realization
    let registeredType ← inferType registeredConstant
    let (registeredParameters, _, _) ← forallMetaTelescopeReducing registeredType
    let registeredValue := mkAppN registeredConstant registeredParameters
    unless ← withTransparency .all <| isDefEq classifierRealization registeredValue do
      throwError "refinement realization {refinement} is not the exact registered classifier realization"
    let baseCategory ← withTransparency .all do
      mkAppM ``CasCatalogue.RefinementRealization.baseCategory #[refinementValue]
    let baseRealization ← withTransparency .all do
      mkAppM ``CasCatalogue.RefinementRealization.baseRealization #[refinementValue]
    validateCategoryEndpointRealization state expectedBase baseCategory baseRealization
    let hostRealization ← withTransparency .all do
      mkAppM ``CasCatalogue.ClassifierRealization.hostRealization #[classifierRealization]
    validateCategoryEndpointRealization state classifierEntry.host classifierArgs[2]!
      hostRealization
    let totalRealization ← withTransparency .all do
      mkAppM ``CasCatalogue.ClassifierRealization.totalRealization #[classifierRealization]
    -- The total endpoint is the classifier's total category, not the classifier datum.
    let classifierTotal ← withTransparency .all do
      mkAppM ``LeanCategories.Classifier.total #[classifierArgs[3]!]
    validateClassifierTotalEndpointRealization state expectedClassifier classifierTotal
      totalRealization
    let baseToHost ← withTransparency .all do
      mkAppM ``CasCatalogue.RefinementRealization.baseToHost #[refinementValue]
    let reindexed ← withTransparency .all do
      mkAppM ``CasCatalogue.RefinementRealization.reindexed #[refinementValue]
    let expectedReindexed ← withTransparency .all do
      mkAppM ``LeanCategories.Classifier.reindex #[baseToHost, classifier]
    unless ← withTransparency .all <| isDefEq reindexed expectedReindexed do
      throwError "refinement realization {refinement} does not use Classifier.reindex"
    -- Audit finding 5: the pullback must be taken along the structural route from the base to
    -- the classifier's host. When the base is the host, that route is the identity.
    if expectedBase.syntacticEq classifierEntry.host then
      let identity ← withTransparency .all do
        mkAppM ``CategoryTheory.CategoryStruct.id #[baseCategory]
      unless ← withTransparency .all <| isDefEq baseToHost identity do
        throwError
          "refinement realization {refinement} reindexes along a non-identity functor from its host"
    else
      -- Otherwise the route must be a registered functor from the base to the host: the
      -- pullback is along declared structure, never an arbitrary functor.
      let mut matched := false
      for functorEntry in state.functors do
        if !matched && functorEntry.source.syntacticEq expectedBase &&
            functorEntry.target.syntacticEq classifierEntry.host then
          let declarationConstant ← mkConstWithFreshMVarLevels functorEntry.declaration
          let (declarationArgs, _, _) ←
            forallMetaTelescopeReducing (← inferType declarationConstant)
          let declarationValue := mkAppN declarationConstant declarationArgs
          let declarationType ← whnf (← inferType declarationValue)
          let routeFunctor ← if declarationType.isAppOf ``CategoryTheory.Cat.Hom then
              mkAppM ``CategoryTheory.Cat.Hom.toFunctor #[declarationValue]
            else
              pure declarationValue
          let baseFunctor ← withTransparency .all do
            mkAppM ``CategoryTheory.Cat.Hom.toFunctor #[baseToHost]
          if ← withTransparency .all <| isDefEq baseFunctor routeFunctor then
            matched := true
      unless matched do
        throwError
          "refinement realization {refinement} reindexes along a functor that is not a registered route from its base to its host"

def validateOpaquePortRealization (state : RegistryState) (entry : StructuralPortEntry) : MetaM Unit := do
  let realizationConstant ← mkConstWithFreshMVarLevels entry.realization
  let realizationType ← inferType realizationConstant
  forallTelescopeReducing realizationType fun arguments realizationResult => do
    let realizationValue := mkAppN realizationConstant arguments
    let realizationArgs := realizationResult.getAppArgs
    unless realizationArgs.size == 6 do
      throwError "opaque port realization {entry.realization} has malformed parameters"
    let expression : FunctorExpr entry.source entry.target := .opaquePort entry.id
    unless ← withTransparency .all <| isDefEq (Lean.toExpr entry.source) realizationArgs[0]! do
      throwError "opaque port realization {entry.realization} has the wrong source"
    unless ← withTransparency .all <| isDefEq (Lean.toExpr entry.target) realizationArgs[1]! do
      throwError "opaque port realization {entry.realization} has the wrong target"
    unless ← withTransparency .all <| isDefEq (Lean.toExpr expression) realizationArgs[2]! do
      throwError "opaque port realization {entry.realization} has the wrong expression"
    let declarationValue ← mkConstWithFreshMVarLevels entry.declaration
    let declarationValue := mkAppN declarationValue arguments
    let declarationType ← whnf (← inferType declarationValue)
    let realizedDeclarationValue ← if declarationType.isAppOf ``CategoryTheory.Cat.Hom then
        mkAppM ``CategoryTheory.Cat.Hom.toFunctor #[declarationValue]
      else
        pure declarationValue
    unless ← withTransparency .all <| isDefEq realizedDeclarationValue realizationArgs[5]! do
      throwError "opaque port declaration {entry.declaration} is not its realization"
    let sourceRealization ← withTransparency .all do
      mkAppM ``CasCatalogue.FunctorRealization.sourceRealization #[realizationValue]
    let targetRealization ← withTransparency .all do
      mkAppM ``CasCatalogue.FunctorRealization.targetRealization #[realizationValue]
    let sourceType ← withTransparency .all <| whnf (← inferType sourceRealization)
    let targetType ← withTransparency .all <| whnf (← inferType targetRealization)
    let sourceArgs := sourceType.getAppArgs
    let targetArgs := targetType.getAppArgs
    unless sourceArgs.size == 2 && targetArgs.size == 2 do
      throwError "opaque port endpoint realization has malformed parameters"
    validateCategoryEndpointRealization state entry.source sourceArgs[1]! sourceRealization
    validateCategoryEndpointRealization state entry.target targetArgs[1]! targetRealization

def validateCategoryDeclarationRealization (state : RegistryState) (expression : CategoryExpr)
    (declaration realization : Name) (familyRealization : Option Name) : MetaM Unit := do
  let realizationConstant ← mkConstWithFreshMVarLevels realization
  let realizationValue := realizationConstant
  let realizationType ← inferType realizationValue
  forallTelescopeReducing realizationType fun arguments realizationResult => do
    let realizationArgs := realizationResult.getAppArgs
    unless realizationArgs.size == 2 do
      throwError "registry realization {realization} has malformed CategoryRealization parameters"
    unless ← withTransparency .all <| isDefEq (Lean.toExpr expression) realizationArgs[0]! do
      throwError
        "registry category expression does not match realization {realization}"
    let declarationValue ← mkConstWithFreshMVarLevels declaration
    let declarationValue := mkAppN declarationValue arguments
    unless ← isDefEq declarationValue realizationArgs[1]! do
      throwError
        "registry category declaration {declaration} does not match realization {realization}"
    let realizationValue := mkAppN realizationConstant arguments
    match expression with
    | .classifierTotal classifier =>
        validateClassifierTotalEndpointRealization state classifier realizationArgs[1]!
          realizationValue
    | .refine base classifier =>
        validateRefinementEndpointRealization state base classifier
    | .familyTotal family =>
        validateFamilyTotalEndpointRealization state family realizationArgs[1]!
          realizationValue
    | .construct constructor args =>
        validateConstructedCategory state constructor args realizationArgs[1]!
    | .atom _ | .familyApp .. | .opaque _ => pure ()
    let familyFibre ← withTransparency .all do
      mkAppM ``CasCatalogue.CategoryRealization.familyFibre #[mkAppN realizationConstant arguments]
    let familyFibre ← withTransparency .all <| whnf familyFibre
    match expression, familyRealization with
    | .familyApp family familyArgs, some familyRealization => do
        let realizationValue := mkAppN realizationConstant arguments
        let witnessOption ← withTransparency .all do
          let witnessOption ←
            mkAppM ``CasCatalogue.CategoryRealization.familyFibre #[realizationValue]
          whnf witnessOption
        unless witnessOption.isAppOf ``Option.some do
          throwError
            "registry family category {declaration} lacks a typed fibre witness"
        let packedArgs := witnessOption.getAppArgs
        let packed := packedArgs.back!
        let packedFields := packed.getAppArgs
        unless packedFields.size >= 2 do
          throwError "registry family category {declaration} has malformed fibre witness"
        let witness := packedFields.back!
        let witnessType ← withTransparency .all <| inferType witness
        let witnessTypeArgs := witnessType.getAppArgs
        unless witnessTypeArgs.size >= 5 do
          throwError "registry family category {declaration} has malformed realization type"
        let witnessIdentifier := witnessTypeArgs[1]!
        let witnessRealization := witnessTypeArgs[4]!
        let familyValue ← mkAppM ``CasCatalogue.CategoryFamilyId.mk #[mkStrLit family.raw]
        unless ← withTransparency .all <| isDefEq witnessIdentifier familyValue do
          throwError "registry family category {declaration} has the wrong family witness"
        let familyConstant ← mkConstWithFreshMVarLevels familyRealization
        let registeredRealization := mkAppN familyConstant #[]
        unless ← withTransparency .all <| isDefEq witnessRealization registeredRealization do
          throwError "registry family category {declaration} has a non-registered family realization"
        let witnessArguments ← withTransparency .all do
          mkAppM ``CasCatalogue.CategoryFamilyFibreWitness.arguments #[witness]
        unless ← withTransparency .all <| isDefEq (Lean.toExpr familyArgs) witnessArguments do
          throwError "registry family category {declaration} has symbolic arguments unrelated to its fibre parameter"
        let categoryEq ← withTransparency .all do
          mkAppM ``CasCatalogue.CategoryFamilyFibreWitness.category_eq #[witness]
        let categoryEqType ← withTransparency .all <| inferType categoryEq
        unless categoryEqType.isEq do
          throwError "registry family category {declaration} has no category equality witness"
        unless ← withTransparency .all <| isDefEq categoryEqType.getAppArgs[1]! realizationArgs[1]! do
          throwError "registry family category {declaration} witness has the wrong category"
        let familyValue := witnessRealization
        let parameter ← withTransparency .all do
          mkAppM ``CasCatalogue.CategoryFamilyFibreWitness.parameter #[witness]
        let fibre ← withTransparency .all do
          mkAppM ``CasCatalogue.CategoryFamilyRealization.fibre #[familyValue, parameter]
        unless ← withTransparency .all <| isDefEq categoryEqType.getAppArgs[2]! fibre do
          throwError "registry family category {declaration} is not its selected family fibre"
    | .familyApp _ _, none =>
        throwError "registry family category {declaration} has no registered family realization"
    | _, some _ =>
        throwError "non-family category {declaration} carries a family fibre witness"
    | _, none =>
        unless familyFibre.isAppOfArity ``Option.none 1 do
          throwError "non-family category {declaration} has a non-empty family fibre witness"

/-- Require a functor-realization declaration to have the typed witness form. -/
def ensureFunctorRealization (realization : Name) : MetaM Unit := do
  let result ← declarationResultType realization
  unless result.isAppOf ``CasCatalogue.FunctorRealization do
    throwError
      "registry realization {realization} must return FunctorRealization ..., but returns {result}"

def FunctorExpr.classifierForget? {source target : CategoryExpr}
    : FunctorExpr source target → Option (ClassifierId × CategoryExpr)
  | .classifierForget classifier host => some (classifier, host)
  | _ => none

def FunctorExpr.identity? {source target : CategoryExpr}
    : FunctorExpr source target → Option CategoryExpr
  | .identity category => some category
  | _ => none

inductive FunctorExpr.RegistrationKind
  | identity
  | atomic
  | classifierForget (classifier : ClassifierId) (host : CategoryExpr)
  | opaquePort (port : OpaquePortId)
  | familyFibreInclusion (family : CategoryFamilyId)
  | familyReindex (family : CategoryFamilyId)
  | comp
  | constructMap

def FunctorExpr.registrationKind {source target : CategoryExpr} :
    FunctorExpr source target → FunctorExpr.RegistrationKind
  | .identity _ => .identity
  | .atomic _ => .atomic
  | .classifierForget classifier host => .classifierForget classifier host
  | .opaquePort port => .opaquePort port
  | .familyFibreInclusion family _ => .familyFibreInclusion family
  | .familyReindex family _ _ _ => .familyReindex family
  | .comp _ _ => .comp
  | .constructMap _ _ => .constructMap

/-- Require a registered fibre inclusion or reindexing to be exactly the canonical realization
(`canonical`) built from the registered family realization. -/
def validateFamilyFunctorRealization (state : RegistryState) (family : CategoryFamilyId)
    (canonical : Name) (realizationValue : Expr) : MetaM Unit := do
  let familyEntry ← match state.categoryFamily? family with
    | some entry => pure entry
    | none => throwError "family functor {family.raw} has no registered family"
  let canonicalConstant ← mkConstWithFreshMVarLevels canonical
  let (canonicalArgs, _, _) ← forallMetaTelescopeReducing (← inferType canonicalConstant)
  unless canonicalArgs.size > 3 do
    throwError "canonical family functor realization {canonical} has malformed parameters"
  let canonicalValue := mkAppN canonicalConstant canonicalArgs
  unless ← withTransparency .all <| isDefEq realizationValue canonicalValue do
    throwError
      "family functor {family.raw} is not the canonical realization {canonical} of its family"
  let registeredRealization ← mkConstWithFreshMVarLevels familyEntry.realization
  unless ← withTransparency .all <| isDefEq canonicalArgs[3]! registeredRealization do
    throwError "family functor {family.raw} is not built from its registered family realization"

def validateFunctorDeclarationRealization (state : RegistryState) {source target : CategoryExpr}
    (expression : FunctorExpr source target)
    (declaration realization : Name) : MetaM Unit := do
  let realizationConstant ← mkConstWithFreshMVarLevels realization
  let realizationType ← inferType realizationConstant
  forallTelescopeReducing realizationType fun arguments realizationResult => do
    let realizationValue := mkAppN realizationConstant arguments
    let realizationArgs := realizationResult.getAppArgs
    unless realizationArgs.size == 6 do
      throwError "registry realization {realization} has malformed FunctorRealization parameters"
    let expressionValue := Lean.toExpr expression
    let expressionType ← inferType expressionValue
    let expressionTypeArgs := expressionType.getAppArgs
    unless expressionTypeArgs.size == 2 do
      throwError "registry functor expression has malformed endpoints"
    unless ← withTransparency .all <| isDefEq expressionTypeArgs[0]! realizationArgs[0]! do
      throwError "registry functor source does not match realization {realization}"
    unless ← withTransparency .all <| isDefEq expressionTypeArgs[1]! realizationArgs[1]! do
      throwError "registry functor target does not match realization {realization}"
    unless ← withTransparency .all <| isDefEq expressionValue realizationArgs[2]! do
      throwError "registry functor expression does not match realization {realization}"
    let declarationValue ← mkConstWithFreshMVarLevels declaration
    let declarationValue := mkAppN declarationValue arguments
    let declarationType ← whnf (← inferType declarationValue)
    let declarationIsCatHom := declarationType.isAppOf ``CategoryTheory.Cat.Hom
    let realizedDeclarationValue ← if declarationIsCatHom then
        mkAppM ``CategoryTheory.Cat.Hom.toFunctor #[declarationValue]
      else
        pure declarationValue
    unless ← withTransparency .all <| isDefEq realizedDeclarationValue realizationArgs[5]! do
      throwError
          "registry functor declaration {declaration} is not the realized functor {realization}"
    let sourceRealization ← withTransparency .all do
      mkAppM ``CasCatalogue.FunctorRealization.sourceRealization #[realizationValue]
    let targetRealization ← withTransparency .all do
      mkAppM ``CasCatalogue.FunctorRealization.targetRealization #[realizationValue]
    let sourceType ← withTransparency .all <| whnf (← inferType sourceRealization)
    let targetType ← withTransparency .all <| whnf (← inferType targetRealization)
    let sourceArgs := sourceType.getAppArgs
    let targetArgs := targetType.getAppArgs
    unless sourceArgs.size == 2 && targetArgs.size == 2 do
      throwError "registry functor endpoint realization has malformed parameters"
    match expression.registrationKind with
    | .identity => do
        unless ← withTransparency .all <| isDefEq sourceArgs[1]! targetArgs[1]! do
          throwError "identity functor has distinct realized endpoint categories"
        let expectedIdentity ← withTransparency .all do
          mkAppM ``CategoryTheory.CategoryStruct.id #[sourceArgs[1]!]
        unless ← withTransparency .all <| isDefEq declarationValue expectedIdentity do
          throwError "identity functor declaration is not the endpoint identity"
    | .atomic => pure ()
    | .comp => pure ()
    | .constructMap =>
        throwError "a constructor's action on a functor is derived from the constructor, never \
          registered"
    | .familyFibreInclusion family =>
        validateFamilyFunctorRealization state family
          ``CasCatalogue.CategoryFamilyRealization.fibreInclusionRealization realizationValue
    | .familyReindex family =>
        validateFamilyFunctorRealization state family
          ``CasCatalogue.CategoryFamilyRealization.reindexRealization realizationValue
    | .classifierForget classifier host => do
        let classifierEntry ← match state.classifier? classifier with
          | some entry => pure entry
          | none => throwError "classifier forget {classifier.raw} has no registered classifier"
        unless host.syntacticEq classifierEntry.host do
          throwError "classifier forget {classifier.raw} has the wrong symbolic host"
        let classifierConstant ← mkConstWithFreshMVarLevels classifierEntry.realization
        let classifierType ← inferType classifierConstant
        let (parameters, _, _) ← forallMetaTelescopeReducing classifierType
        let classifierValue := mkAppN classifierConstant parameters
        let registeredForgetfulRealization ← withTransparency .all do
          mkAppM ``CasCatalogue.ClassifierRealization.forgetfulRealization #[classifierValue]
        unless ← withTransparency .all <| isDefEq realizationValue registeredForgetfulRealization do
          throwError
            "classifier forget {classifier.raw} is not the exact registered classifier forgetful realization"
    | .opaquePort port => do
            let portEntry ← match state.opaquePort? port with
          | some entry => pure entry
          | none => throwError "opaque port {port.raw} has no registered port declaration"
            unless portEntry.source.syntacticEq source && portEntry.target.syntacticEq target do
              throwError "opaque port {port.raw} has the wrong symbolic endpoints"
            unless declaration == portEntry.declaration && realization == portEntry.realization do
              throwError "opaque port {port.raw} is not its exact registered declaration and realization"
            validateOpaquePortRealization state portEntry
    validateCategoryEndpointRealization state source sourceArgs[1]! sourceRealization
    validateCategoryEndpointRealization state target targetArgs[1]! targetRealization
    let realizationFunctorType ← whnf (← inferType realizationArgs[5]!)
    let realizationArgs' := realizationFunctorType.getAppArgs
    let declarationFunctorType ← whnf (← inferType realizedDeclarationValue)
    let declarationFunctorArgs := declarationFunctorType.getAppArgs
    unless declarationFunctorArgs.size >= 2 && realizationArgs'.size >= 2 do
      throwError "registry functor declaration {declaration} has malformed endpoints"
    unless ← isDefEq declarationFunctorArgs[0]! realizationArgs'[0]! do
      throwError
        "registry functor declaration {declaration} source does not match realization {realization}"
    unless ← isDefEq declarationFunctorArgs[1]! realizationArgs'[1]! do
      throwError
        "registry functor declaration {declaration} target does not match realization {realization}"

private def classifierForgetConstantProbeHost : CategoryExpr := .atom ⟨"probe.classifier.host"⟩
private def classifierForgetConstantProbeId : ClassifierId := ⟨"probe.classifier"⟩

private noncomputable def classifierForgetConstantProbeCategory : ObjCat :=
  CategoryTheory.Cat.of (CategoryTheory.Discrete Bool)

private noncomputable def classifierForgetConstantProbeHostRealization :
    CategoryRealization classifierForgetConstantProbeHost
      classifierForgetConstantProbeCategory := {}

private noncomputable def classifierForgetConstantProbeClassifier :
    Classifier classifierForgetConstantProbeCategory :=
  { total := classifierForgetConstantProbeCategory
    forget := CategoryTheory.CategoryStruct.id _ }

private noncomputable def classifierForgetConstantProbeClassifierRealization :
    ClassifierRealization classifierForgetConstantProbeHost classifierForgetConstantProbeId
      classifierForgetConstantProbeCategory classifierForgetConstantProbeClassifier :=
  { hostRealization := classifierForgetConstantProbeHostRealization
    totalRealization := {} }

private noncomputable def classifierForgetConstantProbeFunctor :
    classifierForgetConstantProbeCategory ⟶ classifierForgetConstantProbeCategory :=
  (CategoryTheory.Functor.const (CategoryTheory.Discrete Bool)).obj
    (CategoryTheory.Discrete.mk true)
    |>.toCatHom

private noncomputable def classifierForgetConstantProbeFunctorRealization :
    FunctorRealization
      (.classifierForget classifierForgetConstantProbeId classifierForgetConstantProbeHost)
      classifierForgetConstantProbeCategory classifierForgetConstantProbeCategory
      classifierForgetConstantProbeFunctor.toFunctor :=
  { sourceRealization := {}
    targetRealization := classifierForgetConstantProbeHostRealization }

private def classifierForgetConstantProbeState : RegistryState :=
  { categories := #[{
      id := ⟨"probe.classifier.host"⟩
      declaration := ``classifierForgetConstantProbeCategory
      expression := classifierForgetConstantProbeHost
      realization := ``classifierForgetConstantProbeHostRealization}]
    classifiers := #[{
      id := classifierForgetConstantProbeId
      declaration := ``classifierForgetConstantProbeClassifier
      host := classifierForgetConstantProbeHost
      realization := ``classifierForgetConstantProbeClassifierRealization}] }

run_cmd
  liftTermElabM do
    let accepted ← try
        validateFunctorDeclarationRealization classifierForgetConstantProbeState
          (.classifierForget classifierForgetConstantProbeId classifierForgetConstantProbeHost)
          ``classifierForgetConstantProbeFunctor
          ``classifierForgetConstantProbeFunctorRealization
        pure true
      catch _ => pure false
    if accepted then
      throwError "constant classifier-forget probe was accepted"

/-- Require a declaration to return a typed family realization. -/
def ensureCategoryFamilyRealization (identifier : CategoryFamilyId) (schema : CategoryFamilySchema)
    (realization : Name) : MetaM Unit := do
  let result ← declarationResultType realization
  unless result.isAppOf ``CasCatalogue.CategoryFamilyRealization do
    throwError
      "registry realization {realization} must return CategoryFamilyRealization ..., but returns {result}"
  let arguments := result.getAppArgs
  unless arguments.size == 3 do
    throwError "registry realization {realization} has malformed schema parameters"
  let registeredIdentifier := Lean.toExpr identifier
  unless ← withTransparency .all <| isDefEq registeredIdentifier arguments[0]! do
    throwError "registry realization {realization} does not use the registered family identifier"
  unless ← withTransparency .all <| isDefEq (Lean.toExpr schema) arguments[1]! do
    throwError "registry realization {realization} does not use the registered family schema"

/-- Validate a family transport against the typed realization. -/
def validateCategoryFamilyTransportDecl (_identifier : CategoryFamilyId)
    (schema : CategoryFamilySchema)
    (realization transport : Name) (semantics : CategoryFamilyTransportSemantics) :
    MetaM Unit := do
  let realizationValue ← mkConstWithFreshMVarLevels realization
  let transportValue ← mkConstWithFreshMVarLevels transport
  let realizationTransport ←
    mkAppM ``CasCatalogue.CategoryFamilyRealization.transport #[realizationValue]
  let realizationTransportType ← inferType realizationTransport
  let transportType ← inferType transportValue
  unless ← isDefEq realizationTransportType transportType do
    throwError
      "registry family transport {transport} does not have the realization's exact pseudofunctor type"
  unless ← isDefEq realizationTransport transportValue do
    throwError
      "registry family transport {transport} is not the transport used by realization {realization}"
  let realizationSemantics ←
    mkAppM ``CasCatalogue.CategoryFamilyRealization.transportSemantics #[realizationValue]
  unless ← isDefEq (Lean.toExpr semantics) realizationSemantics do
    throwError "registry family transport semantics do not match its typed realization"
  match semantics, schema with
  | .restrictionOfScalars, .ring =>
      let mathlibTransport ← mkConstWithFreshMVarLevels
        ``RingCat.moduleCatRestrictScalarsPseudofunctor
      unless ← isDefEq transportValue mathlibTransport do
        throwError "registry restriction-of-scalars transport is not Mathlib's pseudofunctor"
  | .restrictionOfScalars, _ =>
      throwError "restriction-of-scalars semantics require a RingCat family"
  | .discrete, .ring =>
      throwError "RingCat families cannot register equality-only transport semantics"
  | .discrete, .commRing => do
      let canonicalTransport ← withTransparency .all do
        mkAppM ``CasCatalogue.CategoryFamilyRealization.canonicalDiscreteCommRingTransport
          #[realizationValue]
      unless ← withTransparency .all <| isDefEq transportValue canonicalTransport do
        throwError
          "registry equality-only transport is not the canonical discrete family transport"
  | .discrete, .commRingModule => do
      let canonicalTransport ← withTransparency .all do
        mkAppM
          ``CasCatalogue.CategoryFamilyRealization.canonicalDiscreteCommRingModuleTransport
          #[realizationValue]
      unless ← withTransparency .all <| isDefEq transportValue canonicalTransport do
        throwError
          "registry equality-only transport is not the canonical discrete family transport"
  | .discrete, .commRingNat => do
      let canonicalTransport ← withTransparency .all do
        mkAppM ``CasCatalogue.CategoryFamilyRealization.canonicalDiscreteCommRingNatTransport
          #[realizationValue]
      unless ← withTransparency .all <| isDefEq transportValue canonicalTransport do
        throwError
          "registry equality-only transport is not the canonical discrete family transport"
  | .discrete, .commRingIndexType => do
      let canonicalTransport ← withTransparency .all do
        mkAppM
          ``CasCatalogue.CategoryFamilyRealization.canonicalDiscreteCommRingIndexTypeTransport
          #[realizationValue]
      unless ← withTransparency .all <| isDefEq transportValue canonicalTransport do
        throwError
          "registry equality-only transport is not the canonical discrete family transport"
  | .discrete, .domain => do
      let canonicalTransport ← withTransparency .all do
        mkAppM ``CasCatalogue.CategoryFamilyRealization.canonicalDiscreteDomainTransport
          #[realizationValue]
      unless ← withTransparency .all <| isDefEq transportValue canonicalTransport do
        throwError
          "registry equality-only transport is not the canonical discrete family transport"

/-- Require a declaration to return a typed classifier realization. -/
def ensureClassifierRealization (realization : Name) : MetaM Unit := do
  let result ← declarationResultType realization
  unless result.isAppOf ``CasCatalogue.ClassifierRealization do
    throwError
      "registry realization {realization} must return ClassifierRealization ..., but returns {result}"

/-- Require a declaration to return a classifier after its parameters are supplied. -/
def ensureClassifierDeclaration (declaration : Name) : MetaM Unit := do
  let result ← declarationResultType declaration
  unless result.isAppOfArity ``LeanCategories.Classifier 1 do
    throwError "registry declaration {declaration} must return Classifier _, but returns {result}"

def validateClassifierDeclarationRealization (_state : RegistryState) (entry : ClassifierEntry) :
    MetaM Unit := do
  let realizationConstant ← mkConstWithFreshMVarLevels entry.realization
  let realizationType ← inferType realizationConstant
  forallTelescopeReducing realizationType fun arguments realizationResult => do
    let realizationValue := mkAppN realizationConstant arguments
    let realizationArgs := realizationResult.getAppArgs
    unless realizationArgs.size == 4 do
      throwError "classifier realization {entry.realization} has malformed parameters"
    unless ← withTransparency .all <| isDefEq (Lean.toExpr entry.host) realizationArgs[0]! do
      throwError "classifier realization {entry.realization} has the wrong host"
    unless ← withTransparency .all <| isDefEq (Lean.toExpr entry.id) realizationArgs[1]! do
      throwError "classifier realization {entry.realization} has the wrong identifier"
    let declarationConstant ← mkConstWithFreshMVarLevels entry.declaration
    let declarationValue := mkAppN declarationConstant arguments
    unless ← withTransparency .all <| isDefEq declarationValue realizationArgs[3]! do
      throwError "classifier declaration {entry.declaration} is not the realized classifier"
    let hostRealization ← withTransparency .all do
      mkAppM ``CasCatalogue.ClassifierRealization.hostRealization #[realizationValue]
    let totalRealization ← withTransparency .all do
      mkAppM ``CasCatalogue.ClassifierRealization.totalRealization #[realizationValue]
    let classifierTotal ← withTransparency .all do
      mkAppM ``LeanCategories.Classifier.total #[declarationValue]
    let hostType ← withTransparency .all <| whnf (← inferType hostRealization)
    let hostArgs := hostType.getAppArgs
    unless hostArgs.size == 2 do
      throwError "classifier host realization has malformed parameters"
    let totalType ← withTransparency .all <| whnf (← inferType totalRealization)
    let totalArgs := totalType.getAppArgs
    unless totalArgs.size == 2 do
      throwError "classifier total realization has malformed parameters"
    validateCategoryEndpointRealization _state entry.host hostArgs[1]! hostRealization
    let stateWithClassifier :=
      { _state with classifiers := _state.classifiers.push entry }
    validateClassifierTotalEndpointRealization stateWithClassifier entry.id totalArgs[1]!
      totalRealization
    unless ← withTransparency .all <| isDefEq classifierTotal totalArgs[1]! do
      throwError "classifier total realization is not the registered classifier total"

/-- Require a declaration to elaborate to an actual functor between categories. -/
def ensureFunctorDeclaration (declaration : Name) : MetaM Unit := do
  let result ← whnf (← declarationResultType declaration)
  unless result.isAppOfArity ``CategoryTheory.Functor 4 ||
      result.isAppOfArity ``CategoryTheory.Cat.Hom 2 do
    throwError
      "registry declaration {declaration} must return a categorical functor, but returns {result}"

/-- A fibration's evidence must prove `IsFibered` (cartesian) or `IsCofibered` (cocartesian)
of exactly the realized functor of its registered projection. -/
def validateFibrationEvidence (state : RegistryState) (e : FibrationEntry) : MetaM Unit := do
  let projection ← match state.functor? e.projection with
    | some entry => pure entry
    | none => throwError "fibration {e.id.raw} has no registered projection {e.projection.raw}"
  let declarationConstant ← mkConstWithFreshMVarLevels projection.declaration
  let (declarationArgs, _, _) ← forallMetaTelescopeReducing (← inferType declarationConstant)
  let declarationValue := mkAppN declarationConstant declarationArgs
  let declarationType ← whnf (← inferType declarationValue)
  let projectionFunctor ← if declarationType.isAppOf ``CategoryTheory.Cat.Hom then
      mkAppM ``CategoryTheory.Cat.Hom.toFunctor #[declarationValue]
    else
      pure declarationValue
  let evidenceConstant ← mkConstWithFreshMVarLevels e.evidence
  let (_, _, evidenceType) ← forallMetaTelescopeReducing (← inferType evidenceConstant)
  let evidenceType ← whnfR evidenceType
  let expected := match e.variance with
    | .cartesian => ``CategoryTheory.Functor.IsFibered
    | .cocartesian => ``CategoryTheory.Functor.IsCofibered
  unless evidenceType.isAppOf expected do
    throwError "fibration {e.id.raw} evidence {e.evidence} does not prove {expected}"
  let provedFunctor := evidenceType.getAppArgs.back!
  unless ← withTransparency .all <| isDefEq provedFunctor projectionFunctor do
    throwError
      "fibration {e.id.raw} evidence {e.evidence} is not about its projection {e.projection.raw}"

/-- The registered functor `entry`'s declaration, applied to fresh metavariables for its
parameters, as a Mathlib functor. -/
def registeredFunctorInstance (entry : FunctorEntry) : MetaM Expr := do
  let declarationConstant ← mkConstWithFreshMVarLevels entry.declaration
  let (declarationArgs, _, _) ← forallMetaTelescopeReducing (← inferType declarationConstant)
  let declarationValue := mkAppN declarationConstant declarationArgs
  let declarationType ← whnf (← inferType declarationValue)
  if declarationType.isAppOf ``CategoryTheory.Cat.Hom then
    mkAppM ``CategoryTheory.Cat.Hom.toFunctor #[declarationValue]
  else
    pure declarationValue

/-- One structural edge of the registry. -/
structure StructuralEdge where
  source : CategoryExpr
  target : CategoryExpr
  expression : FunctorExpr source target
  ref : EdgeRef

/-- The registered functor row of an edge, if it is one. -/
def StructuralEdge.functor? (edge : StructuralEdge) : Option FunctorId :=
  match edge.ref with
  | .functor id => some id
  | _ => none

/-- A human-readable label of an edge. -/
def EdgeRef.label : EdgeRef → String
  | .functor id => id.raw
  | .classifierForget id => s!"forget[{id.raw}]"
  | .constructMap constructor inner => s!"{constructor.raw}({inner.label})"

/-- The structural edges: `structural` functor rows and classifier forgetful functors. -/
def RegistryState.structuralEdges (state : RegistryState) : Array StructuralEdge :=
  let rows := (state.functors.filter (·.structural)).map fun entry =>
    { source := entry.source, target := entry.target, expression := entry.expression,
      ref := .functor entry.id : StructuralEdge }
  let forgets := state.categories.filterMap fun category =>
    match category.expression with
    | .classifierTotal classifier =>
        (state.classifier? classifier).map fun entry =>
          { source := .classifierTotal classifier, target := entry.host
            expression := .classifierForget classifier entry.host
            ref := .classifierForget classifier }
    | _ => none
  rows ++ forgets

/-- The structural edges out of `current`: registered ones, and, when `current` is a unary
functorial constructor `c(A)`, the edges `c(U) : c(A) → c(B)` for every structural edge
`U : A → B` (CC-CLOSURE: `Arr(−)` and `Core(−)` act on the structural graph). -/
partial def RegistryState.edgesFrom (state : RegistryState) (current : CategoryExpr) :
    Array StructuralEdge :=
  let base := state.structuralEdges.filter (·.source.syntacticEq current)
  let derived := match current with
    | .construct constructor args =>
        match args.toList, state.constructor? constructor with
        | [.category inner], some entry =>
            if entry.functorialAction.isSome then
              (state.edgesFrom inner).map fun edge =>
                { source := .construct constructor #[.category edge.source]
                  target := .construct constructor #[.category edge.target]
                  expression := .constructMap constructor edge.expression
                  ref := .constructMap constructor edge.ref }
            else #[]
        | _, _ => #[]
    | _ => #[]
  base ++ derived

/-- A structural route between two categories: its steps, in order. -/
structure Route where
  source : CategoryExpr
  target : CategoryExpr
  steps : Array StructuralEdge

/-- The registered functor ids along a route. -/
def Route.functorIds (route : Route) : Array FunctorId := route.steps.filterMap (·.functor?)

/-- The steps of a route. -/
def Route.refs (route : Route) : Array EdgeRef := route.steps.map (·.ref)

/-- All simple structural routes from `source` to `target`. A route never revisits a category,
so the enumeration is finite; `fuel` bounds its length. -/
partial def RegistryState.routes (state : RegistryState) (source target : CategoryExpr)
    (fuel : Nat := 32) : Array Route :=
  let rec go (current : CategoryExpr) (visited : List CategoryExpr) (fuel : Nat) :
      Array (Array StructuralEdge) :=
    if current.syntacticEq target then #[#[]]
    else if fuel = 0 then #[]
    else
      (state.edgesFrom current).foldl (init := #[]) fun acc edge =>
        if !(visited.any (·.syntacticEq edge.target)) then
          acc ++ (go edge.target (edge.target :: visited) (fuel - 1)).map (#[edge] ++ ·)
        else acc
  (go source [source] fuel).map fun steps => { source, target, steps }

/-- The edges along `steps` if they form a structural route from `source` to `target`. -/
def RegistryState.routeEdges? (state : RegistryState) (source target : CategoryExpr)
    (steps : Array EdgeRef) : Option (Array StructuralEdge) := do
  let mut current := source
  let mut out := #[]
  for step in steps do
    let edge ← (state.edgesFrom current).find? fun edge => edge.ref == step
    out := out.push edge
    current := edge.target
  if current.syntacticEq target then some out else none

/-- The Mathlib functor of a classifier's forgetful functor `total → host`. -/
def classifierForgetInstance (entry : ClassifierEntry) : MetaM Expr := do
  let classifier ← mkConstWithFreshMVarLevels entry.declaration
  let (args, _, _) ← forallMetaTelescopeReducing (← inferType classifier)
  let mut value := mkAppN classifier args
  let type ← whnf (← inferType value)
  if type.isAppOf ``LeanCategories.PropertyClassifier then
    value ← mkAppM ``LeanCategories.PropertyClassifier.toClassifier #[value]
  else if type.isAppOf ``LeanCategories.StructureClassifier then
    value ← mkAppM ``LeanCategories.StructureClassifier.toClassifier #[value]
  mkAppM ``CategoryTheory.Cat.Hom.toFunctor #[← mkAppM ``LeanCategories.Classifier.forget #[value]]

/-- `F ⋙ G` for functor terms with metavariables: unify `F`'s target with `G`'s source at the
current depth (so the metavariables of both, including universe levels, are assigned), then apply
`Functor.comp` at the resulting levels. -/
def mkFunctorComp (F G : Expr) : MetaM Expr := do
  let fType ← whnf (← inferType F)
  let gType ← whnf (← inferType G)
  let .const ``CategoryTheory.Functor [v₁, v₂, u₁, u₂] := fType.getAppFn
    | throwError "not a functor: {F}"
  let .const ``CategoryTheory.Functor [v₂', v₃, u₂', u₃] := gType.getAppFn
    | throwError "not a functor: {G}"
  let #[C, instC, D, instD] := fType.getAppArgs | throwError "malformed functor type"
  let #[D', instD', E, instE] := gType.getAppArgs | throwError "malformed functor type"
  unless ← isLevelDefEq v₂ v₂' <&&> isLevelDefEq u₂ u₂' <&&> isDefEq D D' <&&>
      isDefEq instD instD' do
    throwError "cannot compose {F} with {G}: the middle categories differ"
  instantiateMVars <| mkAppN (mkConst ``CategoryTheory.Functor.comp [v₁, v₂, v₃, u₁, u₂, u₃])
    #[C, instC, D, instD, E, instE, F, G]

/-- Apply the constant `name` to `explicitArgs`, unifying every argument at the current
metavariable depth (unlike `mkAppM`), so metavariables of the arguments, universe levels
included, are assigned. -/
def mkAppHere (name : Name) (explicitArgs : Array Expr) : MetaM Expr := do
  let constant ← mkConstWithFreshMVarLevels name
  let (args, binders, _) ← forallMetaTelescopeReducing (← inferType constant)
  let mut k : Nat := 0
  for i in [0:args.size] do
    if binders[i]!.isExplicit then
      let some arg := explicitArgs[k]? | throwError "mkAppHere: too few arguments for {name}"
      unless ← isDefEq (← inferType args[i]!) (← inferType arg) do
        throwError "mkAppHere: argument {k} does not fit {name}"
      unless ← isDefEq args[i]! arg do
        throwError "mkAppHere: argument {k} does not fit {name}"
      k := k + 1
  instantiateMVars (mkAppN constant args)

/-- The Mathlib functor of one structural edge. -/
partial def RegistryState.edgeFunctor (state : RegistryState) : EdgeRef → MetaM Expr
  | .functor id => match state.functor? id with
      | some entry => registeredFunctorInstance entry
      | none => throwError "unregistered functor {id.raw}"
  | .classifierForget id => match state.classifier? id with
      | some entry => classifierForgetInstance entry
      | none => throwError "unregistered classifier {id.raw}"
  | .constructMap constructor inner => do
      let some action := (state.constructor? constructor).bind (·.functorialAction)
        | throwError "constructor {constructor.raw} has no registered action on functors"
      mkAppHere action #[← state.edgeFunctor inner]

/-- The Mathlib composite of a structural route. -/
def RegistryState.routeFunctor (state : RegistryState) (steps : Array EdgeRef) :
    MetaM Expr := do
  let mut acc : Option Expr := none
  for step in steps do
    let functor ← state.edgeFunctor step
    acc ← some <$> match acc with
      | none => pure functor
      | some previous => mkFunctorComp previous functor
  match acc with
  | some functor => pure functor
  | none => throwError "an empty route has no composite"

/-- A comparison's routes must be structural routes between its endpoints, and its evidence an
isomorphism between their Mathlib composites (CC-COHERE). -/
def validateComparison (state : RegistryState) (e : ComparisonEntry) : MetaM Unit := do
  unless e.source.isRegistered state && e.target.isRegistered state do
    throwError "comparison {e.id.raw} has an unregistered endpoint"
  if e.left == e.right then
    throwError "comparison {e.id.raw} compares a route with itself"
  for (side, steps) in [("left", e.left), ("right", e.right)] do
    if (state.routeEdges? e.source e.target steps).isNone then
      throwError "comparison {e.id.raw}: its {side} side is not a structural route"
  let left ← state.routeFunctor e.left
  let right ← state.routeFunctor e.right
  let evidenceConstant ← mkConstWithFreshMVarLevels e.evidence
  let (_, _, evidenceType) ← forallMetaTelescopeReducing (← inferType evidenceConstant)
  let evidenceType ← whnfR evidenceType
  unless evidenceType.isAppOfArity ``CategoryTheory.Iso 4 do
    throwError "comparison {e.id.raw} evidence {e.evidence} is not an isomorphism"
  let args := evidenceType.getAppArgs
  unless ← withTransparency .all <| isDefEq args[2]! left do
    throwError "comparison {e.id.raw} evidence is not about its left route"
  unless ← withTransparency .all <| isDefEq args[3]! right do
    throwError "comparison {e.id.raw} evidence is not about its right route"


/-- A route's steps, rendered. -/
def renderSteps (steps : Array EdgeRef) : String :=
  " ⋙ ".intercalate (steps.toList.map (·.label))

/-- CC-IMMEDIATE, functors: a structural functor that is definitionally the composite of an
existing structural route between the same endpoints adds no mathematics and is rejected, naming
that composite. A structural functor with the same endpoints but different content (a second
port) is admitted; the resulting ambiguity needs a comparison (CC-COHERE). -/
def validateImmediateFunctor (state : RegistryState) (e : FunctorEntry) : MetaM Unit := do
  unless e.structural do return
  let others := { state with functors := state.functors.filter (·.id != e.id) }
  for route in others.routes e.source e.target do
    if route.steps.isEmpty then continue
    let duplicate ← withoutModifyingState do
      let composite ← others.routeFunctor route.refs
      let declared ← registeredFunctorInstance e
      withTransparency .all <| isDefEq declared composite
    if duplicate then
      throwError "functor {e.id.raw} adds nothing: it is the existing structural composite \
        {renderSteps route.refs}"

/-- CC-IMMEDIATE, methods (#53 §5): a method whose functor is definitionally an existing method
pulled back along a structural route is declared below its lowest generating level, and is
rejected naming that method and route. -/
def validateMethodLevel (state : RegistryState) (e : MethodEntry) (functor : FunctorEntry) :
    MetaM Unit := do
  for other in state.methods do
    if other.id == e.id || other.shape != e.shape then continue
    let some otherFunctor := state.functor? other.functor | continue
    for route in state.routes e.owner other.owner do
      if route.steps.isEmpty then continue
      let pulledBack ← withoutModifyingState do
        let along ← state.routeFunctor route.refs
        let along ← match e.shape with
          | .object => pure along
          | .isoInvariant => mkAppHere ``CategoryTheory.Functor.core #[along]
        let composite ← mkFunctorComp along (← registeredFunctorInstance otherFunctor)
        let declared ← registeredFunctorInstance functor
        withTransparency .all <| isDefEq declared composite
      if pulledBack then
        throwError "method {e.id.raw} is declared below its generating level: it is \
          {other.id.raw} along {renderSteps route.refs}"

/-- An action row's realization must be a `RealizedAction F dC dD` whose functor `F` is an
instance of its edge's Mathlib functor (CC-ACTION). -/
def validateActionRealization (state : RegistryState) (e : FunctorActionEntry) : MetaM Unit := do
  let registered ← state.edgeFunctor e.edge
  let realizationConstant ← mkConstWithFreshMVarLevels e.realization
  let (_, _, realizationType) ← forallMetaTelescopeReducing (← inferType realizationConstant)
  let realizationType ← whnfR realizationType
  unless realizationType.isAppOfArity ``CasCatalogue.RealizedAction 11 do
    throwError "action {e.id.raw} realization {e.realization} is not a RealizedAction"
  let realizedFunctor := realizationType.getAppArgs[8]!
  unless ← withTransparency .all <| isDefEq realizedFunctor registered do
    throwError
      "action {e.id.raw} realization {e.realization} does not realize {e.edge.label}"

/-- The registered classifier `entry` as a `Classifier` term, with metavariables for parameters. -/
def classifierInstance (entry : ClassifierEntry) : MetaM Expr := do
  let classifier ← mkConstWithFreshMVarLevels entry.declaration
  let (args, _, _) ← forallMetaTelescopeReducing (← inferType classifier)
  let value := mkAppN classifier args
  let type ← whnf (← inferType value)
  if type.isAppOf ``LeanCategories.PropertyClassifier then
    mkAppM ``LeanCategories.PropertyClassifier.toClassifier #[value]
  else if type.isAppOf ``LeanCategories.StructureClassifier then
    mkAppM ``LeanCategories.StructureClassifier.toClassifier #[value]
  else pure value

/-- A property row names a registered classifier; an alias's receiver must reach the classifier's
host by a structural route. -/
def validateProperty (state : RegistryState) (e : PropertyEntry) : MetaM Unit := do
  let some classifier := state.classifier? e.classifier
    | throwError "property {e.id.raw} names an unregistered classifier {e.classifier.raw}"
  if let some receiver := e.receiver then
    unless receiver.isRegistered state do
      throwError "property {e.id.raw} has an unregistered receiver"
    if (state.routes receiver classifier.host).isEmpty then
      throwError "property {e.id.raw}: its receiver has no structural route to the host of \
        {e.classifier.raw}"

/-- A decider row's realization must be a `Decider c d` for exactly its registered classifier. -/
def validateDecider (state : RegistryState) (e : DeciderEntry) : MetaM Unit := do
  let some classifier := state.classifier? e.classifier
    | throwError "decider {e.id.raw} names an unregistered classifier {e.classifier.raw}"
  let expected ← classifierInstance classifier
  let realization ← mkConstWithFreshMVarLevels e.realization
  let (_, _, type) ← forallMetaTelescopeReducing (← inferType realization)
  let type ← whnfR type
  unless type.isAppOfArity ``CasCatalogue.Decider 5 do
    throwError "decider {e.id.raw}: {e.realization} is not a Decider"
  unless ← withTransparency .all <| isDefEq type.getAppArgs[1]! expected do
    throwError "decider {e.id.raw}: {e.realization} decides a different property than \
      {e.classifier.raw}"

/-- CC-PROP: a property category is owned by its classifier. An atom category whose declaration is
a registered classifier's total, or a full subcategory of a registered atom category cut out by a
property, is rejected: the property must be a classifier and the category its total or a
refinement, so that no category can be introduced as a label. -/
def validateNotPropertyAtom (state : RegistryState) (e : NamedCategoryEntry) : MetaM Unit := do
  unless e.expression matches .atom _ do return
  for classifier in state.classifiers do
    let isTotal ← withoutModifyingState do
      let c ← classifierInstance classifier
      let total ← mkAppM ``LeanCategories.Classifier.total #[c]
      let declared ← mkConstWithFreshMVarLevels e.declaration
      let (args, _, _) ← forallMetaTelescopeReducing (← inferType declared)
      withTransparency .all <| isDefEq (mkAppN declared args) total
    if isTotal then
      throwError "category {e.id.raw} is the total of classifier {classifier.id.raw}: register it \
        as its classifier total, not as an atom"
  let carrier? ← withoutModifyingState do
    let declared ← mkConstWithFreshMVarLevels e.declaration
    let (args, _, _) ← forallMetaTelescopeReducing (← inferType declared)
    let carrier ← whnf (← mkAppM ``CategoryTheory.Bundled.α #[mkAppN declared args])
    if carrier.isAppOf ``CategoryTheory.ObjectProperty.FullSubcategory then
      return some (← instantiateMVars carrier.getAppArgs[0]!)
    return none
  let some ambient := carrier? | return
  for other in state.categories do
    unless other.expression matches .atom _ do continue
    if other.id == e.id then continue
    let isAmbient ← withoutModifyingState do
      let declared ← mkConstWithFreshMVarLevels other.declaration
      let (args, _, _) ← forallMetaTelescopeReducing (← inferType declared)
      let otherCarrier ← mkAppM ``CategoryTheory.Bundled.α #[mkAppN declared args]
      withTransparency .all <| isDefEq otherCarrier ambient
    if isAmbient then
      throwError "category {e.id.raw} is a property subcategory of {other.id.raw}: register the \
        property as a classifier on {other.id.raw}"

/-- A lift row's evidence must be a `MonoLift U` and its edge the functor `U.mapArrow`. -/
def validateLift (state : RegistryState) (e : LiftEntry) : MetaM Unit := do
  let edge ← state.edgeFunctor e.edge
  let evidence ← mkConstWithFreshMVarLevels e.evidence
  let (_, _, type) ← forallMetaTelescopeReducing (← inferType evidence)
  let type ← whnfR type
  unless type.isAppOfArity ``CasCatalogue.MonoLift 5 do
    throwError "lift {e.id.raw}: {e.evidence} is not a MonoLift"
  let onArrows ← mkAppHere ``CategoryTheory.Functor.mapArrow #[type.getAppArgs[4]!]
  unless ← withTransparency .all <| isDefEq onArrows edge do
    throwError "lift {e.id.raw}: {e.evidence} lifts along a functor whose action on arrows is \
      not {e.edge.label}"

/-- The carrier type of a registered category row, with metavariables for its parameters. -/
def categoryCarrierInstance (entry : NamedCategoryEntry) : MetaM Expr := do
  let declared ← mkConstWithFreshMVarLevels entry.declaration
  let (args, _, _) ← forallMetaTelescopeReducing (← inferType declared)
  mkAppM ``CategoryTheory.Bundled.α #[mkAppN declared args]

/-- A realizer row's denotation must land in its registered category (CC-SEP). -/
def validateRealizer (state : RegistryState) (e : RealizerEntry) : MetaM Unit := do
  let some category := state.categories.find? (·.id == e.category)
    | throwError "realizer {e.id.raw} names an unregistered category {e.category.raw}"
  let denotation ← mkConstWithFreshMVarLevels e.denotation
  let (_, _, type) ← forallMetaTelescopeReducing (← inferType denotation)
  let type ← whnfR type
  unless type.isAppOfArity ``CategoryTheory.Functor 4 do
    throwError "realizer {e.id.raw}: {e.denotation} is not a denotation functor (handles ⥤ C)"
  unless ← withTransparency .all <| isDefEq type.getAppArgs[2]! (← categoryCarrierInstance category) do
    throwError "realizer {e.id.raw}: {e.denotation} does not denote into {e.category.raw}"

/-- A fused implementation must be typed by exactly the semantic composite it claims: its route
functor is the route's composite and its method functor the method's (CC-ROUTE). With no proof it
can only be a trusted assertion (CC-TRUST). -/
def validateImplementation (state : RegistryState) (e : ImplementationEntry) : MetaM Unit := do
  let some method := state.methods.find? (·.id == e.method)
    | throwError "implementation {e.id.raw} names an unregistered method {e.method.raw}"
  let some methodFunctor := state.functor? method.functor
    | throwError "implementation {e.id.raw}: its method has no registered functor"
  unless method.shape == .isoInvariant do
    throwError "implementation {e.id.raw}: fused implementations are typed for iso-invariant \
      methods"
  let realization ← mkConstWithFreshMVarLevels e.realization
  let (_, _, type) ← forallMetaTelescopeReducing (← inferType realization)
  let type ← whnfR type
  -- The status is fixed by the evidence: no proof is a trusted assertion, a checker proved sound
  -- is certificate-checked; nothing else may be claimed.
  if type.isAppOfArity ``CasCatalogue.TrustedImplementation 14 then
    unless e.trust == .trustedAssertion do
      throwError "implementation {e.id.raw}: an unproved implementation is a trusted assertion"
  else if type.isAppOfArity ``CasCatalogue.CertifiedImplementation 14 then
    unless e.trust == .certificateChecked do
      throwError "implementation {e.id.raw}: a certified implementation is certificate-checked"
  else
    throwError "implementation {e.id.raw}: {e.realization} is neither a TrustedImplementation \
      nor a CertifiedImplementation"
  let args := type.getAppArgs
  unless ← withTransparency .all <| isDefEq args[10]! (← state.routeFunctor e.route) do
    throwError "implementation {e.id.raw} does not realize its route"
  unless ← withTransparency .all <|
      isDefEq args[11]! (← registeredFunctorInstance methodFunctor) do
    throwError "implementation {e.id.raw} does not realize its method"

/-- A registered isomorphism must be an isomorphism `source ≅ target` in the handle category of
its realizer, between exactly its source and target handles (CC-CARRIER). -/
def validateHandleIso (state : RegistryState) (e : HandleIsoEntry) : MetaM Unit := do
  let some realizer := state.realizers.find? (·.id == e.realizer)
    | throwError "isomorphism {e.id.raw} names an unregistered realizer {e.realizer.raw}"
  let evidence ← mkConstWithFreshMVarLevels e.evidence
  let type ← whnfR (← inferType evidence)
  unless type.isAppOfArity ``CategoryTheory.Iso 4 do
    throwError "isomorphism {e.id.raw}: {e.evidence} is not an isomorphism of handles"
  let denotationType ← whnfR (← inferType (← mkConstWithFreshMVarLevels realizer.denotation))
  let args := type.getAppArgs
  let checks := #[(args[0]!, denotationType.getAppArgs[0]!, "realizer"),
    (args[2]!, ← mkConstWithFreshMVarLevels e.source, "source"),
    (args[3]!, ← mkConstWithFreshMVarLevels e.target, "target")]
  for (actual, expected, what) in checks do
    unless ← withTransparency .all <| isDefEq actual expected do
      throwError "isomorphism {e.id.raw}: its evidence is not about its {what}"

/-- A method row names a registered functor whose source is its owner (`.object`) or the core
of its owner (`.isoInvariant`, the registered constructor whose semantics is
`CasCatalogue.Constructors.core`). -/
def validateMethodEntry (state : RegistryState) (e : MethodEntry) : MetaM Unit := do
  let functor ← match state.functor? e.functor with
    | some entry => pure entry
    | none => throwError "method {e.id.raw} names an unregistered functor {e.functor.raw}"
  unless e.owner.isRegistered state do
    throwError "method {e.id.raw} has an unregistered owner"
  match e.shape with
  | .object =>
      unless functor.source.syntacticEq e.owner do
        throwError "method {e.id.raw}: functor {e.functor.raw} is not defined on its owner"
  | .isoInvariant =>
      let isCoreOfOwner : Bool := match functor.source with
        | .construct constructor #[.category category] =>
            category.syntacticEq e.owner &&
              (state.constructor? constructor).any
                (·.semantics == `CasCatalogue.Constructors.core)
        | _ => false
      unless isCoreOfOwner do
        throwError
          "method {e.id.raw}: functor {e.functor.raw} is not defined on the core of its owner"
  validateMethodLevel state e functor

/-- Inspect declaration types before atomically persisting a registry entry. -/
def validateRegistryEntryDeclaration (entry : RegistryEntry) : MetaM Unit := do
  let state := registryExt.getState (← getEnv)
  match entry with
  | .category e => do
      ensureCategoryDeclaration e.declaration
      ensureCategoryRealization e.realization
      match e.expression with
      | .familyApp family _ =>
          match state.categoryFamily? family with
          | some familyEntry =>
              validateCategoryDeclarationRealization state e.expression e.declaration e.realization
                (some familyEntry.realization)
          | none => throwError "category entry {e.id.raw} refers to an unregistered family"
      | _ => validateCategoryDeclarationRealization state e.expression e.declaration e.realization none
      match e.expression, e.refinementRealization with
      | .refine .., some refinement =>
          validateRefinementDeclarationRealization state e.expression e.declaration refinement
      | .refine .., none =>
          throwError "refinement category {e.id.raw} has no typed RefinementRealization"
      | _, some _ =>
          throwError "non-refinement category {e.id.raw} carries a refinement realization"
      | _, none => pure ()
      validateNotPropertyAtom state e
  | .categoryFamily e => do
      ensureCategoryFamilyRealization e.id e.schema e.realization
      validateCategoryFamilyTransportDecl e.id e.schema e.realization e.transport
        e.transportSemantics
  | .classifier e => do
      ensureClassifierDeclaration e.declaration
      ensureClassifierRealization e.realization
      validateClassifierDeclarationRealization state e
  | .functor e => do
      match e.expression with
      | .atomic id =>
          unless id == e.id do
            throwError
              "registry functor {e.id.raw} has an atomic expression for {id.raw}"
      | _ => pure ()
      ensureFunctorDeclaration e.declaration
      ensureFunctorRealization e.realization
      validateFunctorDeclarationRealization state e.expression e.declaration e.realization
      validateImmediateFunctor state e
  | .opaque e => do
      ensureCategoryDeclaration e.declaration
      ensureCategoryRealization e.realization
      validateCategoryDeclarationRealization state (.opaque e.id) e.declaration e.realization none
      for port in e.ports do
        ensureFunctorDeclaration port.declaration
        ensureFunctorRealization port.realization
        validateOpaquePortRealization state port
  | .fibration e => validateFibrationEvidence state e
  | .action e => validateActionRealization state e
  | .method e => validateMethodEntry state e
  | .comparison e => validateComparison state e
  | .property e => validateProperty state e
  | .decider e => validateDecider state e
  | .lift e => validateLift state e
  | .realizer e => validateRealizer state e
  | .implementation e => validateImplementation state e
  | .handleIso e => validateHandleIso state e
  | .constructor e => do
      let semanticsConstant ← mkConstWithFreshMVarLevels e.semantics
      let (_, binderInfos, result) ←
        forallMetaTelescopeReducing (← inferType semanticsConstant)
      unless (binderInfos.filter (·.isExplicit)).size == e.signature.size do
        throwError "constructor {e.id.raw} semantics does not have its signature's arity"
      unless (← whnfR result).isAppOf ``CategoryTheory.Cat do
        throwError "constructor {e.id.raw} semantics does not return a category"
      if let some action := e.functorialAction then
        let actionConstant ← mkConstWithFreshMVarLevels action
        let (_, _, actionResult) ← forallMetaTelescopeReducing (← inferType actionConstant)
        unless (← whnf actionResult).isAppOf ``CategoryTheory.Functor do
          throwError "constructor {e.id.raw}: its action {action} does not return a functor"

/-! ### Who may write the registry (CC-ADAPTER, CC-SEP)

Semantics — categories, functors, classifiers, methods, properties, comparisons, lifts, families,
fibrations, constructors — are registered only by the core library (`CasCatalogue`) and its
acceptance probes (`CasAcceptance`). A backend leaf (`CasLeaves`) contributes only realizers,
actions, implementations, deciders and isomorphisms of realized objects, only through
`register_leaf`, and imports only the leaf API `CasCatalogue.Leaf`, the registered semantics
(`CasCatalogue.Semantics.*`), other leaves, Mathlib and `lean-categories`. The module a row is written in is read from the environment, so the rule
holds whatever path the row takes. -/

/-- The library roots that author semantics: the core and its acceptance probes. -/
def semanticAuthorRoots : List Name := [`CasCatalogue, `CasAcceptance]

/-- The library root of backend leaves. -/
def leafRoot : Name := `CasLeaves

/-- The leaf API: the one core module a leaf imports. -/
def leafApiModule : Name := `CasCatalogue.Leaf

/-- The row kinds a backend leaf may contribute (spec §5, permitted contributions 1–4). -/
def RegistryEntry.isLeafContribution : RegistryEntry → Bool
  | .realizer _ | .action _ | .implementation _ | .decider _ | .handleIso _ => true
  | _ => false

/-- The registered semantics a leaf realizes; public to leaves. -/
def semanticsRoot : Name := `CasCatalogue.Semantics

/-- A direct import a leaf module may have: the leaf API, the registered semantics, other leaves,
and the mathematics. Every other kernel module is internal. -/
def leafImportAllowed (module : Name) : Bool :=
  module == leafApiModule ||
    [semanticsRoot, leafRoot, `Mathlib, `LeanCategories, `Init].any (·.isPrefixOf module)

/-- The direct imports of a leaf module that it may not have. -/
def leafImportViolations (imports : Array Name) : Array Name :=
  imports.filter (!leafImportAllowed ·)

/- Validate the elaborated declaration and persist exactly one registry entry. -/
private def persistRegistryEntry (entry : RegistryEntry) : MetaM Unit := do
  validateRegistryEntryDeclaration entry
  let env ← getEnv
  let state := registryExt.getState env
  if state.hasEntryId entry then
    throwError "duplicate normalized-category registry ID: {entry.stableId}"
  match entry with
  | .category e =>
      if state.categories.any fun existing =>
          existing.expression.syntacticEq e.expression then
        throwError "duplicate normalized-category registry expression"
  | _ => pure ()
  match entry with
  | .category e =>
      unless categoryIdMatchesExpression e.id e.expression do
        throwError "category entry {e.id.raw} does not use its own category expression ID"
      let isSelf := match e.expression with
        | .atom id | .opaque id => id == e.id
        | _ => false
      if (!e.expression.isRegistered state && !isSelf) || !e.expression.referencesValid state then
        throwError "category entry {e.id.raw} has an unresolved or ill-typed functor reference"
  | .functor e =>
      if !e.source.isRegistered state || !e.target.isRegistered state ||
          !e.source.referencesValid state || !e.target.referencesValid state ||
          !e.expression.referencesValid state then
        throwError "functor entry {e.id.raw} has an unresolved or unregistered endpoint"
  | .classifier e =>
      unless e.host.isRegistered state && e.host.referencesValid state do
        throwError "classifier entry {e.id.raw} has an unresolved or unregistered host"
  | .opaque e =>
      let category ← match state.categories.find? (·.id == e.id) with
        | some category => pure category
        | none => throwError "opaque category entry {e.id.raw} has no registered category"
      unless opaqueCategoryMatchesCategory category e do
        throwError "opaque category entry {e.id.raw} does not match its registered category"
      unless e.realization == category.realization do
        throwError "opaque category entry {e.id.raw} does not use its registered realization"
      for port in e.ports do
        unless port.source.syntacticEq (.opaque e.id) do
          throwError "opaque port {port.id.raw} is owned by another opaque category"
        unless port.source.isRegistered state && port.target.isRegistered state do
          throwError "opaque port {port.id.raw} has an unregistered endpoint"
      match duplicateOpaquePortId (e.ports.toList.map (·.id)) with
      | some id => throwError "duplicate opaque port ID {id.raw}"
      | none => pure ()
      for category in state.opaqueCategories do
        for port in e.ports do
          unless !category.ports.any fun registered => registered.id == port.id do
            throwError "duplicate opaque port ID {port.id.raw}"
  | _ => pure ()
  for declaration in entry.declarations do
    if declaration.isAnonymous then
      throwError "registry entry {entry.stableId} has no declaration name"
    if (env.find? declaration).isNone then
      throwError "registry entry {entry.stableId} refers to unknown declaration {declaration}"
  modifyEnv (registryExt.addEntry · entry)

/-- Register one semantic row. Only the core library and its acceptance probes may. -/
def addRegistryEntryChecked (entry : RegistryEntry) : MetaM Unit := do
  let module := (← getEnv).mainModule
  unless semanticAuthorRoots.contains module.getRoot do
    throwError "registry row {entry.stableId}: {module} is not in the core library; semantics are \
      registered only by `CasCatalogue`, and a backend leaf contributes through `register_leaf`"
  persistRegistryEntry entry

/-- Register one row of a backend leaf: a permitted contribution, written in a leaf module (or an
acceptance probe) whose direct imports are the leaf API, other leaves and the mathematics. -/
def addLeafRegistryEntryChecked (entry : RegistryEntry) : MetaM Unit := do
  let env ← getEnv
  let module := env.mainModule
  let root := module.getRoot
  unless root == leafRoot || semanticAuthorRoots.contains root do
    throwError "leaf row {entry.stableId}: {module} is neither a leaf nor a core module"
  unless entry.isLeafContribution do
    throwError "leaf row {entry.stableId}: a backend leaf contributes only realizers, actions, \
      implementations, deciders and isomorphisms (spec §5)"
  if root == leafRoot then
    let bad := leafImportViolations (env.header.imports.map (·.module))
    unless bad.isEmpty do
      throwError "leaf module {module} imports core-internal modules {bad.toList}; a leaf \
        imports only {leafApiModule}, {semanticsRoot}.*, other leaves, Mathlib and lean-categories"
  persistRegistryEntry entry

/-- Every registry row, grouped by the imported module that wrote it. -/
def registryRowsByModule (env : Environment) : Array (Name × Array RegistryEntry) :=
  env.header.moduleNames.mapIdx fun index module =>
    (module, registryExt.getModuleEntries env index)

/-- Violations of the leaf boundary among the imported modules: a leaf module with a forbidden
direct import or a non-leaf row, and a row written outside the core, its probes and the leaves. -/
def leafBoundaryViolations (env : Environment) : Array String := Id.run do
  let mut violations := #[]
  for (module, rows) in registryRowsByModule env do
    let root := module.getRoot
    if root == leafRoot then
      if let some index := env.getModuleIdx? module then
        let imports := env.header.moduleData[index.toNat]!.imports.map (·.module)
        for bad in leafImportViolations imports do
          violations := violations.push s!"{module} imports {bad}"
      for row in rows do
        unless row.isLeafContribution do
          violations := violations.push s!"{module} registers the semantic row {row.stableId}"
    else if !semanticAuthorRoots.contains root then
      for row in rows do
        violations := violations.push s!"{module} (outside the core) registers {row.stableId}"
  return violations

/--
Atomically elaborate and register one authored registry declaration.

The command is deliberately entry-by-entry: an imported module contributes its own
declarations directly to the persistent environment extension instead of assembling a
second in-memory manifest and replaying it later.
-/
syntax (name := normalizedRegistryEntry) "normalized_registry " term : command

elab_rules : command
  | `(normalized_registry $entry) => do
      let command ← `(run_cmd
        liftTermElabM do
          addRegistryEntryChecked $entry)
      elabCommand command

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

private partial def registryManifestParameterExprOfJson : Json → Except String RegistryManifestParameterExpr :=
  fun j => do
    let tag ← j.getObjValAs? String "tag"
    match tag with
    | "variable" => .variable <$> j.getObjValAs? String "id"
    | "apply" => .apply <$> j.getObjValAs? String "operation" <*> registryManifestParameterExprOfJson (← j.getObjValAs? Json "argument")
    | "apply2" => .apply2 <$> j.getObjValAs? String "operation" <*> registryManifestParameterExprOfJson (← j.getObjValAs? Json "left") <*> registryManifestParameterExprOfJson (← j.getObjValAs? Json "right")
    | "apply3" => .apply3 <$> j.getObjValAs? String "operation" <*> registryManifestParameterExprOfJson (← j.getObjValAs? Json "first") <*> registryManifestParameterExprOfJson (← j.getObjValAs? Json "second") <*> registryManifestParameterExprOfJson (← j.getObjValAs? Json "third")
    | _ => throw s!"unknown parameter expression tag: {tag}"

instance : FromJson RegistryManifestParameterExpr where
  fromJson? := registryManifestParameterExprOfJson

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

private partial def registryManifestCategoryExprJson : RegistryManifestCategoryExpr → Json
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
      ("args", Json.arr (args.map fun
        | .category category => registryObject [
            ("tag", "category"), ("category", registryManifestCategoryExprJson category)]
        | .object id => registryObject [("tag", "object"), ("id", id)]
        | .functor id => registryObject [("tag", "functor"), ("id", id)]))]

instance : ToJson RegistryManifestCategoryExpr where
  toJson := registryManifestCategoryExprJson

instance : Inhabited RegistryManifestCategoryExpr := ⟨.atom ""⟩

/-- Decode a constructor argument, given the category-expression decoder. -/
private def constructorArgOfJson
    (category : Json → Except String RegistryManifestCategoryExpr) (arg : Json) :
    Except String RegistryManifestConstructorArg := do
  match ← arg.getObjValAs? String "tag" with
  | "category" => .category <$> category (← arg.getObjValAs? Json "category")
  | "object" => .object <$> arg.getObjValAs? String "id"
  | "functor" => .functor <$> arg.getObjValAs? String "id"
  | tag => throw s!"unknown constructor argument tag: {tag}"

private partial def registryManifestCategoryExprOfJson : Json → Except String RegistryManifestCategoryExpr :=
  fun j => do
    let tag ← j.getObjValAs? String "tag"
    match tag with
    | "atom" => .atom <$> j.getObjValAs? String "id"
    | "familyApp" => .familyApp <$> j.getObjValAs? String "family" <*> j.getObjValAs? _ "args"
    | "classifierTotal" => .classifierTotal <$> j.getObjValAs? String "classifier"
    | "refine" => .refine <$> registryManifestCategoryExprOfJson (← j.getObjValAs? Json "base") <*> j.getObjValAs? String "classifier"
    | "opaque" => .opaque <$> j.getObjValAs? String "id"
    | "familyTotal" => .familyTotal <$> j.getObjValAs? String "family"
    | "construct" => do
        let constructor ← j.getObjValAs? String "constructor"
        let args ← j.getObjValAs? (Array Json) "args"
        let args ← args.mapM (constructorArgOfJson registryManifestCategoryExprOfJson)
        pure (.construct constructor args)
    | _ => throw s!"unknown category expression tag: {tag}"

instance : FromJson RegistryManifestCategoryExpr where
  fromJson? := registryManifestCategoryExprOfJson

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

private partial def registryManifestFunctorExprJson : RegistryManifestFunctorExpr → Json
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

private partial def registryManifestFunctorExprOfJson : Json → Except String RegistryManifestFunctorExpr
  | j => do
    let tag ← j.getObjValAs? String "tag"
    match tag with
    | "identity" => .identity <$> j.getObjValAs? _ "category"
    | "atomic" => .atomic <$> j.getObjValAs? String "id"
    | "classifierForget" =>
        .classifierForget <$> j.getObjValAs? String "classifier" <*> j.getObjValAs? _ "host"
    | "opaquePort" => .opaquePort <$> j.getObjValAs? String "id"
    | "familyFibreInclusion" =>
        .familyFibreInclusion <$> j.getObjValAs? String "family" <*> j.getObjValAs? _ "args"
    | "familyReindex" =>
        .familyReindex <$> j.getObjValAs? String "family" <*> j.getObjValAs? String "morphism"
          <*> j.getObjValAs? _ "source" <*> j.getObjValAs? _ "target"
    | "comp" => .comp <$> (registryManifestFunctorExprOfJson (← j.getObjValAs? _ "left")) <*>
        (registryManifestFunctorExprOfJson (← j.getObjValAs? _ "right"))
    | "constructMap" => .constructMap <$> j.getObjValAs? String "constructor" <*>
        (registryManifestFunctorExprOfJson (← j.getObjValAs? _ "functor"))
    | _ => throw s!"unknown functor expression tag: {tag}"

instance : FromJson RegistryManifestFunctorExpr where
  fromJson? := registryManifestFunctorExprOfJson

structure RegistryManifestCategory where
  id : String
  declaration : String
  realization : String
  refinementRealization : String
  expression : RegistryManifestCategoryExpr
  deriving BEq, Repr, ToJson, FromJson

structure RegistryManifestFamily where
  id : String
  schema : String
  realization : String
  transport : String
  parameters : Array RegistryManifestParameter
  variance : String
  deriving BEq, Repr, ToJson, FromJson

structure RegistryManifestClassifier where
  id : String
  host : RegistryManifestCategoryExpr
  declaration : String
  realization : String
  deriving BEq, Repr, ToJson, FromJson

structure RegistryManifestFunctor where
  id : String
  source : RegistryManifestCategoryExpr
  target : RegistryManifestCategoryExpr
  declaration : String
  realization : String
  expression : RegistryManifestFunctorExpr
  structural : Bool
  deriving BEq, Repr, ToJson, FromJson

structure RegistryManifestPort where
  id : String
  source : RegistryManifestCategoryExpr
  target : RegistryManifestCategoryExpr
  declaration : String
  realization : String
  provenance : String
  deriving BEq, Repr, ToJson, FromJson

structure RegistryManifestOpaque where
  id : String
  declaration : String
  realization : String
  reason : String
  ports : Array RegistryManifestPort
  deriving BEq, Repr, ToJson, FromJson

structure RegistryManifestFibration where
  id : String
  projection : String
  variance : String
  evidence : String
  deriving BEq, Repr, ToJson, FromJson

structure RegistryManifestConstructor where
  id : String
  signature : Array String
  semantics : String
  deriving BEq, Repr, ToJson, FromJson

structure RegistryManifestAction where
  id : String
  functor : String
  realization : String
  deriving BEq, Repr, ToJson, FromJson

structure RegistryManifestMethod where
  id : String
  name : String
  owner : RegistryManifestCategoryExpr
  functor : String
  shape : String
  returnsToSource : Bool
  deriving BEq, Repr, ToJson, FromJson

structure RegistryManifestComparison where
  id : String
  source : RegistryManifestCategoryExpr
  target : RegistryManifestCategoryExpr
  left : Array String
  right : Array String
  evidence : String
  deriving BEq, Repr, ToJson, FromJson

structure RegistryManifestProperty where
  id : String
  name : String
  classifier : String
  receiver : Option RegistryManifestCategoryExpr
  deriving BEq, Repr, ToJson, FromJson

structure RegistryManifestDecider where
  id : String
  classifier : String
  realization : String
  deriving BEq, Repr, ToJson, FromJson

structure RegistryManifestLift where
  id : String
  edge : String
  evidence : String
  deriving BEq, Repr, ToJson, FromJson

structure RegistryManifestRealizer where
  id : String
  category : String
  denotation : String
  backend : String
  deriving BEq, Repr, ToJson, FromJson

structure RegistryManifestImplementation where
  id : String
  method : String
  route : Array String
  realization : String
  backend : String
  trust : String
  deriving BEq, Repr, ToJson, FromJson

structure RegistryManifestHandleIso where
  id : String
  realizer : String
  source : String
  target : String
  evidence : String
  deriving BEq, Repr, ToJson, FromJson

structure RegistryManifest where
  schemaVersion : String
  categories : Array RegistryManifestCategory
  classifiers : Array RegistryManifestClassifier
  functors : Array RegistryManifestFunctor
  opaqueCategories : Array RegistryManifestOpaque
  categoryFamilies : Array RegistryManifestFamily
  fibrations : Array RegistryManifestFibration
  constructors : Array RegistryManifestConstructor
  actions : Array RegistryManifestAction
  methods : Array RegistryManifestMethod
  comparisons : Array RegistryManifestComparison
  properties : Array RegistryManifestProperty
  deciders : Array RegistryManifestDecider
  lifts : Array RegistryManifestLift
  realizers : Array RegistryManifestRealizer
  implementations : Array RegistryManifestImplementation
  handleIsos : Array RegistryManifestHandleIso
  source : String
  deriving BEq, Repr, ToJson, FromJson

private def registryManifestParameterExpr : ParameterExpr → RegistryManifestParameterExpr
  | .variable id => .variable id.raw
  | .apply operation argument => .apply operation.raw (registryManifestParameterExpr argument)
  | .apply2 operation left right =>
      .apply2 operation.raw (registryManifestParameterExpr left) (registryManifestParameterExpr right)
  | .apply3 operation first second third =>
      .apply3 operation.raw (registryManifestParameterExpr first)
        (registryManifestParameterExpr second) (registryManifestParameterExpr third)

private partial def registryManifestCategoryExpr : CategoryExpr → RegistryManifestCategoryExpr
  | .atom id => .atom id.raw
  | .familyApp family args => .familyApp family.raw (args.map registryManifestParameterExpr)
  | .classifierTotal classifier => .classifierTotal classifier.raw
  | .refine base classifier => .refine (registryManifestCategoryExpr base) classifier.raw
  | .opaque id => .opaque id.raw
  | .familyTotal family => .familyTotal family.raw
  | .construct constructor args => .construct constructor.raw (args.map fun
      | .category category => .category (registryManifestCategoryExpr category)
      | .object id => .object id.raw
      | .functor id => .functor id.raw)

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
  { schemaVersion := "0.2.0-ids"
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
    actions := (state.actions.qsort (fun a b => a.id.raw < b.id.raw)).map fun e => {
      id := e.id.raw, functor := e.edge.label, realization := e.realization.toString }
    methods := (state.methods.qsort (fun a b => a.id.raw < b.id.raw)).map fun e => {
      id := e.id.raw, name := e.name, owner := registryManifestCategoryExpr e.owner,
      functor := e.functor.raw,
      shape := match e.shape with
        | .object => "object"
        | .isoInvariant => "isoInvariant",
      returnsToSource := e.returnsToSource }
    comparisons := (state.comparisons.qsort (fun a b => a.id.raw < b.id.raw)).map fun e => {
      id := e.id.raw, source := registryManifestCategoryExpr e.source,
      target := registryManifestCategoryExpr e.target, left := e.left.map (·.label),
      right := e.right.map (·.label), evidence := e.evidence.toString }
    properties := (state.properties.qsort (fun a b => a.id.raw < b.id.raw)).map fun e => {
      id := e.id.raw, name := e.name, classifier := e.classifier.raw,
      receiver := e.receiver.map registryManifestCategoryExpr }
    deciders := (state.deciders.qsort (fun a b => a.id.raw < b.id.raw)).map fun e => {
      id := e.id.raw, classifier := e.classifier.raw, realization := e.realization.toString }
    lifts := (state.lifts.qsort (fun a b => a.id.raw < b.id.raw)).map fun e => {
      id := e.id.raw, edge := e.edge.label, evidence := e.evidence.toString }
    realizers := (state.realizers.qsort (fun a b => a.id.raw < b.id.raw)).map fun e => {
      id := e.id.raw, category := e.category.raw, denotation := e.denotation.toString,
      backend := e.backend }
    implementations := (state.implementations.qsort (fun a b => a.id.raw < b.id.raw)).map fun e => {
      id := e.id.raw, method := e.method.raw, route := e.route.map (·.label),
      realization := e.realization.toString, backend := e.backend, trust := e.trust.label }
    handleIsos := (state.handleIsos.qsort (fun a b => a.id.raw < b.id.raw)).map fun e => {
      id := e.id.raw, realizer := e.realizer.raw, source := e.source.toString,
      target := e.target.toString, evidence := e.evidence.toString }
    source := "lean-registry" }

private def registryManifestJson (state : RegistryState) : Json := toJson (registryManifest state)

/-- Return the manifest produced from the checked persistent registry state. -/
def checkedRegistryManifestDTO : CoreM RegistryManifest := do
  let state := registryExt.getState (← getEnv)
  match validatePersistedRegistryState state with
  | .error message => throwError message
  | .ok () => pure (registryManifest state)

def checkedRegistryManifest : CoreM Json := do
  return toJson (← checkedRegistryManifestDTO)

end CasCatalogue
