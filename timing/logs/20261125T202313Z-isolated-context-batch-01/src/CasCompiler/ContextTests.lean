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

  saved.context.withOpen fun bindings => do
    withLocalDeclD `later bindings[0]!.expression fun later =>
      withLetDecl `replacement bindings[0]!.expression later fun replacement => do
        let changed := bindings.set! 3 { bindings[3]! with id := ⟨"context-test", 5⟩ }
        let target ← ContextTelescope.capture <| changed.push
          { id := ⟨"context-test", 4⟩, role := .parameter, expression := later } |>.push
          { id := ⟨"context-test", 3⟩, role := .definition, expression := replacement }
        let mut rejected := false
        try
          discard <| saved.inContext target
        catch _ => rejected := true
        unless rejected do throwError "a captured definition changed under the same binding identity"

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

-- The selected instance environment can exclude or reorder class-typed declarations.
run_cmd Lean.Elab.Command.liftTermElabM do
  let saved ← withLocalDeclD `α (.sort (Level.succ Level.zero)) fun α => do
    let type ← mkAppM ``Inhabited #[α]
    withLocalDeclD `first type fun first =>
      withLocalDeclD `second type fun second => do
        let declarations ← getLCtx
        let bindings : Array LocalBinding := #[
          { id := ⟨"instance-selection", 0⟩, role := .parameter, expression := α },
          { id := ⟨"instance-selection", 1⟩, role := .instance, expression := first },
          { id := ⟨"instance-selection", 2⟩, role := .parameter, expression := second }]
        let mut saved : Array ClosedTerm := #[]
        let selections : Array LocalInstances := #[
          #[{ className := ``Inhabited, fvar := first }],
          #[{ className := ``Inhabited, fvar := second },
            { className := ``Inhabited, fvar := first }]]
        for selected in selections do
          let source ← withLCtx declarations selected do
            let context ← ContextTelescope.capture bindings
            context.close (← synthInstance (← mkAppM ``Inhabited #[α]))
          saved := saved.push source
        return saved
  for source in saved do
    source.withOpen fun bindings selected => do
      let current ← synthInstance (← mkAppM ``Inhabited #[bindings[0]!.expression])
      unless current == selected do
        throwError "context reopening changed the actual ordered local-instance selection"

-- Equal original source terms do not identify opaque runtime binders. Their exact
-- recorded sources still justify dependent mathematical types and survive complete
-- closure/import without turning the native declarations into reducible definitions.
run_cmd Lean.Elab.Command.liftTermElabM do
  let empty ← ContextTelescope.capture #[]
  let saved ← empty.withLocalBinding ⟨"opaque-context", 0⟩ .result `first (mkConst ``Nat)
    (fun context first =>
      context.withLocalBinding ⟨"opaque-context", 1⟩ .result `second (mkConst ``Nat)
        (fun context second => do
          if ← withoutModifyingState (isDefEq first.expression second.expression) then
            throwError "equal source terms collapsed two opaque binding identities"
          let sameSource ← context.withOriginalSources #[first.expression, second.expression]
            fun sources => isDefEq sources[0]! sources[1]!
          unless sameSource do
            throwError "source interpretation lost an explicitly retained original term"
          let original ← mkAppM ``Fin.last #[mkNatLit 6]
          let dependent := mkApp (mkConst ``Fin) first.expression
          context.withLocalBinding ⟨"opaque-context", 2⟩ .result `point dependent
            (fun context point => do
              check point.expression
              if (← getFVarLocalDecl point.expression).value?.isSome then
                throwError "a runtime occurrence acquired a native let definition"
              let sameType ← context.withOriginalSources #[← inferType original, dependent]
                fun types => isDefEq types[0]! types[1]!
              unless sameType do
                throwError "source interpretation lost the original dependent field type"
              context.close (← mkAppM ``Prod.mk #[first.expression, point.expression]))
            (originalSource := some original))
        (originalSource := some (mkNatLit 7)))
    (originalSource := some (mkNatLit 7))
  unless saved.context.entries.size == 3 &&
      saved.context.entries.all (fun entry => entry.value.isNone && entry.originalSource.isSome) do
    throwError "closed opaque context lost an original source or changed its declaration kind"
  saved.context.withInContext empty fun imported => do
    unless imported.telescope.exactlyMatches saved.context do
      throwError "context import changed a complete opaque source telescope"
    let expression ← saved.inContext imported
    check expression
    let repeated ← ClosedTerm.inContextMany #[saved, saved] imported
    unless repeated.size == 2 && repeated.all (·.equal expression) do
      throwError "batched context transport changed a retained original term"
    let changedBindings := imported.bindings.set! 1
      { imported.bindings[1]! with originalSource := some (mkNatLit 8) }
    let changedContext ← ContextTelescope.capture changedBindings
    let changed ← changedContext.close expression
    let changedSourceRejected ← try
        discard <| ClosedTerm.inContextMany #[saved, changed] imported
        pure false
      catch failure =>
        pure ((← failure.toMessageData.toString) ==
          "the target context changed an original source correspondence")
    unless changedSourceRejected do
      throwError "batched context transport reused a different complete original source"
    unless imported.bindings[0]!.id != imported.bindings[1]!.id &&
        imported.bindings[0]!.expression.fvarId! != imported.bindings[1]!.expression.fvarId! do
      throwError "context import identified distinct equal-source occurrences"
