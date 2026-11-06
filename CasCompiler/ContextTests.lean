module

import CasCompiler.Context
public meta import Lean.Elab.Command
meta import CasCompiler.Context

open Lean Meta CasCompiler

run_cmd Lean.Elab.Command.liftTermElabM do
  let u := Level.param `u
  let saved ← withLocalDeclD `α (.sort u) fun α =>
    withLocalDecl `chosen .instImplicit (mkApp (mkConst ``Inhabited [u]) α) fun chosen =>
      withLocalDeclD `x α fun x =>
        withLetDecl `y α x fun y => do
          let context ← ContextTelescope.capture #[
            { id := ⟨"context-test", 0⟩, role := .parameter, expression := α },
            { id := ⟨"context-test", 1⟩, role := .instance, expression := chosen },
            { id := ⟨"context-test", 2⟩, role := .parameter, expression := x },
            { id := ⟨"context-test", 3⟩, role := .definition, expression := y }]
          context.close y
  if saved.expression.hasFVar || saved.expression.hasMVar then
    throwError "published context contains a local variable or metavariable"
  unless saved.universeParams.contains `u do
    throwError "published context lost its universe parameter"
  saved.withOpen fun bindings value => do
    unless bindings.size == 4 do throwError "reopened context has the wrong arity"
    unless bindings[3]!.id == ⟨"context-test", 3⟩ do
      throwError "reopened definition lost its binding identity"
    unless ← isDefEq (← inferType value) bindings[0]!.expression do
      throwError "reopened value lost its dependent type"
    unless ← isDefEq value bindings[2]!.expression do
      throwError "reopened definition lost its value"
    let dictionary ← synthInstance (mkApp (mkConst ``Inhabited [u]) bindings[0]!.expression)
    unless dictionary == bindings[1]!.expression do
      throwError "reopened context lost its selected local instance"

  saved.context.withOpen fun bindings => do
    withLocalDeclD `later bindings[0]!.expression fun later => do
      let target ← ContextTelescope.capture (bindings.push {
        id := ⟨"context-test", 4⟩, role := .parameter, expression := later })
      let imported ← saved.inContext target
      unless ← isDefEq imported bindings[3]!.expression do
        throwError "a later context lost the original definition binding"

  saved.context.withOpen fun bindings => do
    let changed := bindings.set! 3 { bindings[3]! with id := ⟨"context-test", 5⟩ }
    let target ← ContextTelescope.capture changed
    let mut rejected := false
    try
      discard <| saved.inContext target
    catch _ => rejected := true
    unless rejected do throwError "a different binding identity replaced a captured definition"

run_cmd Lean.Elab.Command.liftTermElabM do
  let context ← ContextTelescope.capture #[]
  let unresolved ← mkFreshExprMVar (mkConst ``Nat)
  let mut rejected := false
  try
    discard <| context.close unresolved
  catch _ => rejected := true
  unless rejected do throwError "publication accepted an unresolved term"

run_cmd Lean.Elab.Command.liftTermElabM do
  withLocalDeclD `x (mkConst ``Nat) fun _ => do
    let mut rejected := false
    try
      discard <| ContextTelescope.capture #[]
    catch _ => rejected := true
    unless rejected do throwError "context capture accepted an incomplete binding map"
