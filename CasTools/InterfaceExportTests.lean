module

import LeanCategories.Catalogue
import CasTools.InterfaceDocument
public meta import Lean.Elab.Command
meta import CasTools.InterfaceDocument

open Lean Meta Elab Command CasCatalogue CasTools

-- Compare the generated artifact against the original native environment. These
-- checks neither reconstruct semantics from JSON nor admit any backend result.
run_cmd do
  let document ← liftTermElabM InterfaceExport.prepare
  let .ok rows := document.getObjValAs? (Array Json) "registry"
    | throwError "public help omitted its registry"
  let snapshot ← liftTermElabM do RegistrySnapshot.snapshot
  let ids ← rows.mapM fun row => do
    let .ok id := row.getObjValAs? String "id"
      | throwError "a public row lost its stable identity"
    return id
  unless ids.size == snapshot.entries.size &&
      snapshot.stableIds.all ids.contains do
    throwError "public help omitted or duplicated an accepted registry entry"
  -- A category and its opaque-interface row can share a category identifier.
  -- Compare complete typed entries, never collapse them into a map keyed by ID.
  let mut counts : Std.HashMap String Nat := {}
  let mut identities : Std.HashSet (String × String) := {}
  for row in rows do
    let .ok entry := row.getObjVal? "entry"
      | throwError "a public row lost its typed record"
    let .ok kind := row.getObjValAs? String "kind"
      | throwError "a public row lost its native kind"
    let .ok id := row.getObjValAs? String "id"
      | throwError "a public row lost its identifier"
    if identities.contains (kind, id) then
      throwError "public help duplicated a typed registry identity"
    identities := identities.insert (kind, id)
    let encoded := entry.compress
    counts := counts.insert encoded (counts.getD encoded 0 + 1)
  for original in snapshot.entries do
    let encoded := (toJson original).compress
    unless counts.getD encoded 0 == 1 do
      throwError "public help lost or duplicated the complete typed row {original.stableId}"
  let .ok native := document.getObjVal? "native"
    | throwError "public help omitted the native declaration graph"
  let .ok nodes := NativeExpression.decodeNodes native
    | throwError "the complete public native graph did not decode"
  let .ok declarations := native.getObjValAs? (Array Json) "declarations"
    | throwError "public help omitted the native declaration payloads"
  let mut declared : Std.HashSet Name := {}
  for declaration in declarations do
    let .ok nameJson := declaration.getObjVal? "name"
      | throwError "a public declaration lost its native name"
    let .ok name := NativeExpression.nameFromJson nameJson
      | throwError "a public declaration changed its native name encoding"
    declared := declared.insert name
    let original ← getConstInfo name
    let .ok typeIndex := declaration.getObjValAs? Nat "type"
      | throwError "a public declaration lost its type"
    let some actualType := nodes[typeIndex]?
      | throwError "a public declaration has a dangling type reference"
    unless actualType.equal original.type do
      throwError "public declaration {name} changed its complete dependent native type"
    let .ok universes := declaration.getObjValAs? (Array Json) "universeParams"
      | throwError "a public declaration lost its universe parameters"
    let .ok universes := universes.mapM NativeExpression.nameFromJson
      | throwError "a public declaration changed a universe parameter"
    unless universes.toList == original.levelParams do
      throwError "public declaration {name} changed its ordered universe parameters"
    let value := match original with
      | .defnInfo info => some info.value
      | .thmInfo info => some info.value
      | .opaqueInfo info => some info.value
      | _ => none
    if let some value := value then
      let .ok valueIndex := declaration.getObjValAs? Nat "value"
        | throwError "public declaration {name} was replaced by an axiom"
      let some actualValue := nodes[valueIndex]?
        | throwError "a public declaration has a dangling value reference"
      unless actualValue.equal value do
        throwError "public declaration {name} changed its original native value"
  let state ← liftTermElabM do semanticState
  for object in state.objects do
    for name in object.application.toArray ++ object.generator.toArray ++
        object.admission.toArray ++ object.constants.toArray ++ object.inclusion.toArray ++
        object.refines.toArray.map (·.identification) do
      unless declared.contains name do
        throwError "public object {object.id.raw} lost an authored action or law {name}"
  for row in state.functors do
    let candidates := rows.filter fun exported =>
      exported.getObjValAs? String "id" == .ok row.id.raw &&
        exported.getObjValAs? String "kind" == .ok "functor"
    let #[exported] := candidates | throwError "a public functor has no unique row"
    let .ok tagged := exported.getObjVal? "entry"
      | throwError "a public functor lost its entry"
    let .ok wrapped := tagged.getObjVal? "functor"
      | throwError "a public functor lost its native row kind"
    let .ok payload := wrapped.getObjVal? "e"
      | throwError "a public functor lost its original record"
    let .ok expression := payload.getObjVal? "expression"
      | throwError "a public functor lost its indexed native expression"
    let .ok #[restored] := NativeExpression.decode expression
      | throwError "a public functor expression did not decode"
    unless restored.equal (toExpr row.expression) do
      throwError "public functor {row.id.raw} lost a selected or intermediate category"
  for name in InterfaceExport.dataInterfaces do
    unless declared.contains name do
      throwError "the public data-only interface omitted {name}"
  let .ok help := InterfaceExport.help document
    | throwError "the prepared public document cannot be rendered"
  unless help.startsWith "# Selected language and interfaces" do
    throwError "the public help has no language entrance"
