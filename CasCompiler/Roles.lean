module

public import CasCompiler.Layout
public import CasRuntime.Identity

public section

namespace CasCompiler

open Lean Meta CasRuntime

/-- Source positions remain distinct when their terms or actual values coincide. -/
inductive RoleAddress
  | context (binding : BindingId)
  | argument (position : Nat)
  | result (path : Array Name)
  | capture (position : Nat)
  deriving BEq, Hashable, Repr

/-- A retained preparation remains distinct from another build of the same source occurrence. -/
structure RoleScope where
  private mk ::
  program : RuntimeId .program
  occurrence : RuntimeId .occurrence
  preparation : RuntimeId .preparation
  deriving BEq, Hashable, Repr

structure RoleId where
  private mk ::
  scope : RoleScope
  address : RoleAddress
  deriving BEq, Hashable, Repr

/-- Checked source term, complete native family and exact source-position dependencies. -/
structure ComputationalRole where
  private mk ::
  id : RoleId
  source : ClosedTerm
  typeFamily : ClosedTerm
  dependencies : Array RoleId

structure ArgumentRole where
  private mk ::
  role : ComputationalRole
  wireIndex : Option Nat

structure CaptureRole where
  private mk ::
  role : ComputationalRole
  layout : SourceLayout

structure ResultRole where
  private mk ::
  role : ComputationalRole
  layout : SourceLayout
  wirePath : Option (Array Nat)

/-- Full semantic context and source roles; only declared inputs are demanded before a call.
Future result fields remain declarations until whole-result admission binds their actual values. -/
structure RoleTelescope where
  private mk ::
  scope : RoleScope
  source : SourceLayout
  context : Array ComputationalRole
  arguments : Array ArgumentRole
  results : Array ResultRole
  captures : Array CaptureRole

private def sourceTypeFamily (source : ClosedTerm) : MetaM ClosedTerm :=
  source.withOpen fun bindings expression => do
    let context ← ContextTelescope.capture bindings
    context.close (← inferType expression)

private def contextRoles (scope : RoleScope) (term : ClosedTerm) : MetaM (Array RoleId) :=
  term.withOpen fun bindings expression => do
    let dependencies ← localDependencies (bindings.map (·.expression)) expression
    dependencies.mapM fun index => do
      let some binding := bindings[index]?
        | throwError "a computational role dependency is outside its native context"
      return ⟨scope, .context binding.id⟩

private partial def resultRoles (scope : RoleScope) (application : Option ApplicationLayout)
    (source : SourceLayout) (family : ClosedTerm) (dependencies : Array RoleId)
    (wirePath : Option (Array Nat)) : MetaM (Array ResultRole) := do
  let root : ResultRole := ⟨⟨⟨scope, .result source.address⟩, source.source, family, dependencies⟩,
    source, wirePath⟩
  let mut results := #[root]
  if source.kind == .record then
    let record ← RecordLayout.ofSource source
    for prepared in record.fields do
      let mut fieldDependencies ← contextRoles scope prepared.field.typeFamily
      if let some application := application then
        let selected ← application.dependenciesFor prepared.layout
        fieldDependencies := fieldDependencies ++ selected.arguments.map fun index =>
          (⟨scope, .argument index⟩ : RoleId)
      for previous in prepared.field.precedingDependencies do
        let some field := record.fields[previous]?
          | throwError "a result role dependency is outside its source constructor"
        fieldDependencies := fieldDependencies.push ⟨scope, .result field.field.address⟩
      let childPath := wirePath.bind fun path => prepared.field.wireIndex.map path.push
      results := results ++ (← resultRoles scope application prepared.layout
        prepared.field.typeFamily fieldDependencies childPath)
  return results

/-- Derive identities from source binder positions, field paths and capture positions.
Reuse: checked Layout families, ContextTelescope, native dependency closure and worker identities.
Source: lean-cas-dsl#66, scoped computational-role telescope and total demanded-role map. -/
opaque RoleTelescope.ofRequest (identities : IdentitySupply)
    (program : RuntimeId .program) (occurrence : RuntimeId .occurrence)
    (context : OpenContext) (application : Option ApplicationLayout) (source : SourceLayout)
    (captures : Array SourceLayout) : MetaM RoleTelescope := do
  unless identities.worker == program.worker && program.worker == occurrence.worker do
    throwError "a computational role scope mixed worker identities"
  let scope : RoleScope := ⟨program, occurrence, ← identities.fresh .preparation⟩
  let mut contextRoles : Array ComputationalRole := #[]
  for binding in context.bindings do
    let term ← context.close binding.expression
    let family ← sourceTypeFamily term
    contextRoles := contextRoles.push ⟨⟨scope, .context binding.id⟩, term, family,
      ← CasCompiler.contextRoles scope family⟩
  let mut arguments : Array ArgumentRole := #[]
  if let some application := application then
    for argument in application.arguments, index in [:application.arguments.size] do
      unless argument.sourceIndex == index do
        throwError "an application role lost its original source binder position"
      let dependencies := (← CasCompiler.contextRoles scope argument.typeFamily) ++
        argument.precedingDependencies.map fun previous => (⟨scope, .argument previous⟩ : RoleId)
      arguments := arguments.push ⟨⟨⟨scope, .argument index⟩, argument.source.source,
        argument.typeFamily, dependencies⟩, argument.wireIndex⟩
  let family ← match application with
    | some layout => pure layout.resultTypeFamily
    | none => sourceTypeFamily source.source
  let mut rootDependencies ← CasCompiler.contextRoles scope family
  if let some application := application then
    rootDependencies := rootDependencies ++ application.resultDependencies.map fun index =>
      (⟨scope, .argument index⟩ : RoleId)
  let results ← resultRoles scope application source family rootDependencies (some #[])
  let captures ← captures.mapIdxM fun index source => do
    let family ← sourceTypeFamily source.source
    let role := ComputationalRole.mk ⟨scope, .capture index⟩ source.source family
      (← CasCompiler.contextRoles scope family)
    return CaptureRole.mk role source
  return ⟨scope, source, contextRoles, arguments, results, captures⟩

end CasCompiler
