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
    source.context.withOpenContext fun context => do
      unless context.telescope.exactlyMatches source.context do
        throwError "controlled opening changed the complete original telescope"
      let actual ← getLocalInstances
      unless actual.size == source.context.instances.size do
        throwError "controlled opening changed the original instance count"
      for current in actual, original in source.context.instances do
        let some binding := context.bindings.find? (·.id == original.binding)
          | throwError "controlled opening lost an original instance binding"
        unless current.className == original.className && current.fvar.equal binding.expression do
          throwError "controlled opening changed the original selected-instance order"
      let selected ← source.inContext context
      let current ← synthInstance (← inferType selected)
      unless current.equal selected do
        throwError "controlled opening changed native instance synthesis"




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


run_cmd Lean.Elab.Command.liftTermElabM do
  withLocalDeclD `x (mkConst ``Nat) fun x => do
    let context ← ContextTelescope.capture #[
      { id := ⟨"closing-occurrences", 0⟩, role := .parameter, expression := x }]
    let calls ← IO.mkRef 0
    let values ← context.withClosing (fun _ => do calls.modify (· + 1)) fun close => do
      return #[← close x, ← close x]
    unless (← calls.get) == 2 do
      throwError "repeated source fields skipped an original policy occurrence"
    let #[first, second] := values
      | throwError "closing changed the number of original source fields"
    unless first.expression.equal second.expression && first.type.equal second.type &&
        first.context.exactlyMatches context.telescope &&
        second.context.exactlyMatches context.telescope do
      throwError "repeated closing changed the complete original source"


run_cmd Lean.Elab.Command.liftTermElabM do
  let context ← ContextTelescope.capture #[]
  let calls ← IO.mkRef 0
  let rejected ← try
    context.withClosing (fun _ => do
      calls.modify (· + 1)
      if (← calls.get) == 2 then
        throwError (MessageData.tagged `CasCompiler.tests.originalClosePolicyFailure
          m!"deliberate second closing policy failure"))
      fun close => do
        discard <| close (mkNatLit 7)
        discard <| close (mkNatLit 7)
    pure false
  catch failure =>
    pure (failure.toMessageData.hasTag (· == `CasCompiler.tests.originalClosePolicyFailure))
  unless rejected && (← calls.get) == 2 do
    throwError "repeated closing swallowed or skipped the second policy failure"


run_cmd Lean.Elab.Command.liftTermElabM do
  withLocalDeclD `x (mkConst ``Nat) fun x => do
    let context ← ContextTelescope.capture #[
      { id := ⟨"closing-scope", 0⟩, role := .parameter, expression := x }]
    let calls ← IO.mkRef 0
    context.withClosing (fun _ => do calls.modify (· + 1)) fun close => do
      let original ← close x
      let rejected ← withLCtx {} #[] do
        try
          discard <| close x
          pure false
        catch _ => pure true
      unless rejected && (← calls.get) == 1 do
        throwError "closing reused a checked local after its native scope was removed"
      let restored ← close x
      unless (← calls.get) == 2 && restored.expression.equal original.expression &&
          restored.context.exactlyMatches original.context do
        throwError "closing failed to preserve the restored original native scope"



run_cmd Lean.Elab.Command.liftTermElabM do
  let originalEnvironment ← getEnv
  try
    let declaration ← mkAuxDeclName `closingEnvironment
    addDecl (.defnDecl {
      name := declaration, levelParams := [], type := mkConst ``Nat,
      value := mkNatLit 19, hints := .abbrev, safety := .safe })
    let context ← ContextTelescope.capture #[]
    let calls ← IO.mkRef 0
    context.withClosing (fun term => do
      calls.modify (· + 1)
      if (← calls.get) == 1 then
        unless term.nativeDeclarations.constants.any (·.name == declaration) do
          throwError "closing lost its original checked native declaration"
        setEnv originalEnvironment)
      fun close => do
        discard <| close (mkConst declaration)
        let rejected ← try
          discard <| close (mkConst declaration)
          pure false
        catch _ => pure true
        unless rejected && (← calls.get) == 1 do
          throwError "closing reused native evidence after the policy removed its declaration"
  finally
    setEnv originalEnvironment


run_cmd Lean.Elab.Command.liftTermElabM do
  let calls ← IO.mkRef 0
  let (escaped, original) ← withLocalDeclD `x (mkConst ``Nat) fun x => do
    let context ← ContextTelescope.capture #[
      { id := ⟨"closing-lifetime", 0⟩, role := .parameter, expression := x }]
    context.withClosing (fun _ => do calls.modify (· + 1)) fun close => do
      discard <| close x
      return (close, x)
  let rejected ← try
    discard <| escaped original
    pure false
  catch _ => pure true
  unless rejected && (← calls.get) == 1 do
    throwError "an escaped closer reused a result after its original native scope ended"


run_cmd Lean.Elab.Command.liftTermElabM do
  let originalEnvironment ← getEnv
  try
    let declaration ← mkAuxDeclName `closingBranch
    let first : DefinitionVal := {
      name := declaration, levelParams := [], type := mkConst ``Nat,
      value := mkNatLit 31, hints := .abbrev, safety := .safe }
    let second := { first with value := mkNatLit 37 }
    addDecl (.defnDecl first)
    let context ← ContextTelescope.capture #[]
    context.withClosing (fun _ => pure ()) fun close => do
      let original ← close (mkConst declaration)
      setEnv originalEnvironment
      addDecl (.defnDecl second)
      let changed ← close (mkConst declaration)
      unless original.expression.equal changed.expression && original.type.equal changed.type &&
          original.nativeDeclarations.constants.any (nativeConstantExactlyMatches (.defnInfo first)) &&
          changed.nativeDeclarations.constants.any (nativeConstantExactlyMatches (.defnInfo second)) &&
          !(original.nativeDeclarations.exactlyMatches changed.nativeDeclarations) do
        throwError "closing identified different checked native bodies at the same source name"
  finally
    setEnv originalEnvironment



run_cmd Lean.Elab.Command.liftTermElabM do
  let originalEnvironment ← getEnv
  try
    let declaration ← mkAuxDeclName `controlledContextType
    let original : DefinitionVal := {
      name := declaration, levelParams := [], type := mkSort (.succ .zero),
      value := mkConst ``Nat, hints := .regular 0, safety := .safe }
    addDecl (.defnDecl original)
    let saved ← withTransparency .all <| withLocalDeclD `value (mkConst declaration) fun value => do
      let context ← ContextTelescope.capture #[{
        id := ⟨"controlled-context", 0⟩, role := .result, expression := value,
        originalSource := some (mkNatLit 7) }]
      return context.telescope
    withTransparency .all <| saved.withOpenContext (m := MetaM) fun context => do
      unless context.telescope.exactlyMatches saved && context.bindings.size == 1 do
        throwError "controlled opening changed the original source telescope"
      let binding := context.bindings[0]!
      unless binding.id == ⟨"controlled-context", 0⟩ &&
          binding.originalSource.any (·.equal (mkNatLit 7)) &&
          (← getFVarLocalDecl binding.expression).value?.isNone do
        throwError "controlled opening replaced an opaque occurrence by its source"
    if ← withoutModifyingState <| withReducible <|
        isDefEq (mkConst ``Nat) (mkConst declaration) then
      throwError "the controlled-opening negative lost its stricter native conversion premise"
    let calls ← IO.mkRef 0
    let rejected ← withReducible do
      try
        saved.withOpenContext (m := MetaM) fun _ => do
          liftM (m := IO) <| calls.modify (· + 1)
        pure false
      catch failure => pure ((← failure.toMessageData.toString) ==
        "an opaque source binding changed its original mathematical type")
    unless rejected && (← calls.get) == 0 do
      throwError "controlled opening skipped the current original-source type check"
    setEnv originalEnvironment
    addDecl (.defnDecl { original with value := mkConst ``Bool })
    let changed ← try
      saved.withOpenContext (m := MetaM) fun _ => do
        liftM (m := IO) <| calls.modify (· + 1)
      pure false
    catch failure => pure ((← failure.toMessageData.toString).endsWith
      "has a different native meaning")
    unless changed && (← calls.get) == 0 do
      throwError "controlled opening accepted a different original native declaration"
  finally
    setEnv originalEnvironment




run_cmd Lean.Elab.Command.liftTermElabM do
  let originalEnvironment ← getEnv
  unless originalEnvironment.isImportedConst ``Nat do
    throwError "the missing-import control requires the original imported Nat declaration"
  let saved ← withLocalDeclD `x (mkConst ``Nat) fun x => do
    let context ← ContextTelescope.capture #[{
      id := ⟨"controlled-import-availability", 0⟩, role := .parameter, expression := x }]
    return context.telescope
  unless saved.entries.size == 1 && saved.instances.isEmpty &&
      saved.nativeDeclarations.constants.isEmpty &&
      saved.entries.all (fun entry => entry.value.isNone && entry.originalSource.isNone) do
    throwError "the missing-import control lost its source-free imported parameter"
  let empty ← liftM (m := IO) <| mkEmptyEnvironment
  let rawCalls ← IO.mkRef 0
  let originalCalls ← IO.mkRef 0
  let checkedCalls ← IO.mkRef 0
  try
    setEnv empty
    if (← getEnv).contains ``Nat then
      throwError "the missing-import control retained the declaration it must remove"
    saved.withOpen (m := MetaM) fun bindings => do
      unless bindings.size == 1 &&
          (← getFVarLocalDecl bindings[0]!.expression).type.equal (mkConst ``Nat) do
        throwError "the raw opener changed the original parameter type"
      liftM (m := IO) <| rawCalls.modify (· + 1)
    unless (← rawCalls.get) == 1 do
      throwError "the missing-import control did not reach the raw opener callback"
    let originalRejected ← try
      saved.withOpen (m := MetaM) fun bindings => do
        discard <| ContextTelescope.capture bindings
        liftM (m := IO) <| originalCalls.modify (· + 1)
      pure false
    catch failure => pure ((← failure.toMessageData.toString) ==
      "a retained native source refers to missing declaration Nat")
    unless originalRejected && (← originalCalls.get) == 0 do
      throwError "complete context recapture accepted the missing imported declaration"
    let checkedRejected ← try
      saved.withOpenContext (m := MetaM) fun _ => do
        liftM (m := IO) <| checkedCalls.modify (· + 1)
      pure false
    catch failure => pure ((← failure.toMessageData.toString) ==
      "a retained native source refers to missing declaration Nat")
    unless checkedRejected && (← checkedCalls.get) == 0 do
      throwError "controlled opening skipped the original imported-declaration availability gate"
  finally
    setEnv originalEnvironment



run_cmd Lean.Elab.Command.liftTermElabM do
  let originalEnvironment ← getEnv
  try
    let dName ← mkAuxDeclName `mapPolicyDomain
    let sName ← mkAuxDeclName `mapPolicySignal
    for name in #[dName, sName] do
      addDecl (.defnDecl {
        name, levelParams := [], type := mkSort (.succ .zero),
        value := mkConst ``Nat, hints := .abbrev, safety := .safe })
    let functionType ← mkArrow (mkConst sName) (mkConst ``Nat)
    let sources ← withLocalDeclD `x (mkConst ``Nat) fun x =>
      withLocalDeclD `f functionType fun f => do
        let source ← ContextTelescope.capture #[
          { id := ⟨"context-map-policy", 0⟩, role := .parameter, expression := x },
          { id := ⟨"context-map-policy", 1⟩, role := .parameter, expression := f }]
        return #[← source.close (mkApp f (mkNatLit 0)), ← source.close (mkNatLit 1)]
    let #[first, second] := sources
      | throwError "the map-policy control lost its complete common source telescope"
    unless first.context.entries.size == 2 && second.context.entries.size == 2 &&
        first.context.exactlyMatches second.context do
      throwError "the map-policy control lost its complete common source telescope"
    withLocalDeclD `x (mkConst dName) fun x =>
      withLocalDeclD `f functionType fun f => do
        let target ← ContextTelescope.capture #[
          { id := ⟨"context-map-policy", 0⟩, role := .parameter, expression := x },
          { id := ⟨"context-map-policy", 1⟩, role := .parameter, expression := f }]
        let stableDomain ← IO.mkRef 0
        let stableSignal ← IO.mkRef 0
        let stable ← withCanUnfoldPred (fun _ info => do
          if info.name == dName then stableDomain.modify (· + 1)
          if info.name == sName then stableSignal.modify (· + 1)
          return true) <| ClosedTerm.inContextMany sources target
        unless (← stableDomain.get) > 0 && (← stableSignal.get) > 0 &&
            stable.size == 2 && stable[0]!.equal (mkApp f (mkNatLit 0)) &&
            stable[1]!.equal (mkNatLit 1) do
          throwError "stable native unfolding changed the original transported terms"
        let requireChangedPolicyFailure
            (label : String) (transport : MetaM (Array Expr)) : MetaM Unit := do
          let changed ← IO.mkRef false
          let allowedDomain ← IO.mkRef 0
          let deniedDomain ← IO.mkRef 0
          let signal ← IO.mkRef 0
          let failure : Option Exception ← try
            discard <| withCanUnfoldPred (fun _ info => do
              if info.name == sName then
                signal.modify (· + 1)
                changed.set true
                return true
              if info.name == dName then
                if ← changed.get then
                  deniedDomain.modify (· + 1)
                  return false
                allowedDomain.modify (· + 1)
                return true
              return true) transport
            pure none
          catch failure => pure (some failure)
          unless (← changed.get) && (← allowedDomain.get) > 0 && (← signal.get) > 0 do
            throwError "{label}: the actual native callback transition was not reached"
          let some failure := failure
            | throwError "{label}: transport reused a context map after its unfolding policy changed"
          unless (← deniedDomain.get) > 0 &&
              (← failure.toMessageData.toString) ==
                "the target context changed a captured binding type" do
            throw failure
        requireChangedPolicyFailure "separate public transports" <|
          sources.mapM fun source => source.inContext target
        requireChangedPolicyFailure "consecutive public transport" <|
          ClosedTerm.inContextMany sources target
  finally
    setEnv originalEnvironment
