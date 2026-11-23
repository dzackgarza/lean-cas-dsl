module

import CasCompiler.Roles
import CasContract.Failure
public meta import Lean.Elab.Command
meta import CasCompiler.Roles
meta import CasContract.Failure

open Lean Meta CasCompiler CasRuntime

/-- A hypothetical source value is sufficient to exercise schema preparation; this fixture
introduces no axiom or inhabitant. Lean permits strictly positive recursive structures.
Sources: Lean 4 reference, Inductive Types / Structures; T007's repeated-record requirement. -/
structure RecursiveLayoutFixture where
  next : RecursiveLayoutFixture

set_option maxRecDepth 64 in
run_cmd Lean.Elab.Command.liftTermElabM do
  let identities ← liftM (m := IO) IdentitySupply.new
  let program ← liftM (m := BaseIO) (identities.fresh .program)
  let occurrence ← liftM (m := BaseIO) (identities.fresh .occurrence)
  withLocalDeclD `selected (mkConst ``RecursiveLayoutFixture) fun selected => do
    let context ← ContextTelescope.capture #[{
      id := ⟨"recursive-layout", 0⟩, role := .parameter, expression := selected }]
    let source ← SourceLayout.ofTerm (← context.close selected)
    let failure ← try
      discard <| RoleTelescope.ofRequest identities program occurrence context none source #[]
      pure none
    catch error => pure (some error)
    let some error := failure
      | throwError "a recursive source record was accepted as a finite result interface"
    unless CasCatalogue.Exception.stratum? error == some .noImplementation do
      throwError "recursive source record preparation must report no implementation, got: \
        {error.toMessageData}"

/- Repeated constructors and equal sibling types are finite data, not a cycle on one path.
The complete four scalar fields must remain reachable under their original addresses. -/
run_cmd Lean.Elab.Command.liftTermElabM do
  let identities ← liftM (m := IO) IdentitySupply.new
  let program ← liftM (m := BaseIO) (identities.fresh .program)
  let occurrence ← liftM (m := BaseIO) (identities.fresh .occurrence)
  let context ← ContextTelescope.capture #[]
  let pair ← mkAppM ``Prod.mk #[mkNatLit 2, mkNatLit 3]
  let nested ← mkAppM ``Prod.mk #[pair, pair]
  let source ← SourceLayout.ofTerm (← context.close nested)
  let roles ← RoleTelescope.ofRequest identities program occurrence context none source #[]
  for left in #[``Prod.fst, ``Prod.snd] do
    for right in #[``Prod.fst, ``Prod.snd] do
      unless roles.results.any (fun role =>
          role.layout.kind == .data && role.layout.address == #[left, right]) do
        throwError "a finite nested record lost a scalar field at {left}.{right}"

/-- A callable ends a stored-record path. Demanding its result starts a new interface.
This retains the lazy recursive interface required by constitutional C8. -/
structure CallableRecursiveLayoutFixture where
  next : Unit → CallableRecursiveLayoutFixture

run_cmd Lean.Elab.Command.liftTermElabM do
  let identities ← liftM (m := IO) IdentitySupply.new
  let program ← liftM (m := BaseIO) (identities.fresh .program)
  let occurrence ← liftM (m := BaseIO) (identities.fresh .occurrence)
  withLocalDeclD `selected (mkConst ``CallableRecursiveLayoutFixture) fun selected => do
    let context ← ContextTelescope.capture #[{
      id := ⟨"callable-recursive-layout", 0⟩, role := .parameter, expression := selected }]
    let source ← SourceLayout.ofTerm (← context.close selected)
    let some field := source.fields[0]? | throwError "the callable record lost its field"
    let callable ← field.toLayout
    unless callable.kind == .function do throwError "the recursive field lost its callable role"
    let result ← callable.applyIn context #[← context.close (mkConst ``Unit.unit)]
    let roles ← RoleTelescope.ofRequest identities program occurrence context none result #[]
    unless roles.results.any (fun role => role.layout.kind == .function) do
      throwError "the demanded recursive result lost its lazy callable continuation"
