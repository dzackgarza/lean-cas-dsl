module

public import CasCompiler.Elaborate
public import CasCompiler.Syntax
public import Lean.Meta.Check

public section

namespace CasCompiler

open Lean Meta Elab Term



opaque SourceReadM.proveOriginal (sources : Array Expr)
    (originalProposition : Array Expr → TermElabM Expr)
    (prepare : Expr → Array Expr → TermElabM Expr)
    (target : SourceReadM Expr) : SourceReadM Expr := do
  let original ← get
  let formals ← original.context.bindings.filterM fun binding => do
    return binding.originalSource.isNone && (← binding.expression.fvarId!.getDecl).value?.isNone
  let declarations ← original.context.bindings.mapM fun binding =>
    binding.expression.fvarId!.getDecl
  let instances ← getLocalInstances
  let function ← liftM (m := TermElabM) <| controlAt MetaM fun run =>
    original.context.withOriginalSources sources fun expressions =>
      run do
        let expected ← originalProposition expressions
        unless ← isProp expected do
          throwError "source proof checking requires a proposition"
        let proof ← instantiateMVars (← prepare expected expressions)
        unless ← isDefEq (← inferType proof) expected do
          throwError (← mkTypeMismatchError none proof (← inferType proof) expected)
        checkWithKernel proof
        let locals := (← getLCtx).foldl
          (fun result declaration => result.push (mkFVar declaration.fvarId)) #[]
        unless locals.size == original.context.bindings.size do
          throwError "source proof preparation changed the original native telescope"



        let function ← mkLambdaFVars locals proof (usedOnly := false) (usedLetOnly := true)
        checkWithKernel function
        return function
  let proposition ← target
  let current ← get
  let sameOptionalExpression := fun (first second : Option Expr) =>
    match first, second with
    | none, none => true
    | some first, some second => first.equal second
    | _, _ => false
  let sameBinding := fun (first second : LocalBinding) =>
    first.id == second.id && first.role == second.role &&
      first.expression.equal second.expression &&
      sameOptionalExpression first.originalSource second.originalSource
  unless original.context.bindings.size ≤ current.context.bindings.size do
    liftM (m := TermElabM) <| throwError "source proof target lost an original source binding"
  for previous in original.context.bindings,
      actual in current.context.bindings.take original.context.bindings.size,
      declaration in declarations do
    unless sameBinding previous actual do
      liftM (m := TermElabM) <| throwError "source proof target changed an original source binding"
    let actual ← actual.expression.fvarId!.getDecl
    unless declaration.fvarId == actual.fvarId && declaration.index == actual.index &&
        declaration.userName == actual.userName && declaration.binderInfo == actual.binderInfo &&
        declaration.kind == actual.kind && declaration.isNondep == actual.isNondep &&
        declaration.type.equal actual.type &&
        sameOptionalExpression (declaration.value? true) (actual.value? true) do
      liftM (m := TermElabM) <| throwError "source proof target changed an original native declaration"
  let currentInstances ← getLocalInstances
  unless instances.size == currentInstances.size do
    liftM (m := TermElabM) <| throwError "source proof target changed its selected local instances"
  for previous in instances, actual in currentInstances do
    unless previous.className == actual.className && previous.fvar == actual.fvar do
      liftM (m := TermElabM) <| throwError "source proof target changed its selected local instance order"
  unless original.formals.size == current.formals.size do
    liftM (m := TermElabM) <| throwError "source proof target changed its active formal scope"
  for previous in original.formals, actual in current.formals do
    unless sameBinding previous actual do
      liftM (m := TermElabM) <| throwError "source proof target changed an active formal binding"
  let currentFormals ← current.context.bindings.filterM fun binding => do
    return binding.originalSource.isNone && (← binding.expression.fvarId!.getDecl).value?.isNone
  unless formals.map (·.id) == currentFormals.map (·.id) do
    liftM (m := TermElabM) <| throwError "source proof target changed its original formal telescope"
  let mut proof := function
  for formal in formals do
    let .forallE _ type _ _ ← whnfR (← inferType proof)
      | liftM (m := TermElabM) <| throwError "source proof closure lost an original formal position"
    let actual ← inferType formal.expression
    let nativeFits ← withoutModifyingState (isDefEq actual type)
    let value ← if nativeFits then do


        unless ← isDefEq actual type do
          liftM (m := TermElabM) <| throwError "source proof closure changed its checked formal type"
        pure formal.expression
      else do
        let selected := (← SourceReadM.selection? formal.expression).getD {
          value := formal.expression }
        SourceReadM.select { selected with value := formal.expression } (some type)
    proof := mkApp proof value


  proof := proof.headBeta
  checkWithKernel proof
  let actual ← inferType proof
  let nativeFits ← withoutModifyingState (isDefEq actual proposition)
  if nativeFits then
    unless ← isDefEq actual proposition do
      liftM (m := TermElabM) <| throwError "source proof closure changed its original proposition"
    return proof
  SourceReadM.select { value := proof } (some proposition)

opaque SourceReadM.prove (proposition : Expr)
    (prepare : Expr → Array Expr → TermElabM Expr)
    (sources : Array Expr := #[]) : SourceReadM Expr :=
  SourceReadM.proveOriginal (#[proposition] ++ sources)
    (fun expressions => pure expressions[0]!)
    (fun expected expressions => prepare expected (expressions.extract 1 expressions.size))
    (pure proposition)




opaque SourceSession.proof (session : SourceSession) (stx : TSyntax `cas_term)
    (obligation : ClosedTerm) (selections : SourceSelectionScope ClosedTerm := {}) :
    TermElabM SourceTerm := withRef stx do
  let `(cas_term| proof($evidence:term)) := stx
    | throwError "source evidence requires an explicit proof term"
  session.elaborateScoped evidence do
    let proposition ← session.readClosed evidence obligation selections
    SourceReadM.prove proposition (fun expected _ => sourceFormalProof evidence expected)

end CasCompiler
