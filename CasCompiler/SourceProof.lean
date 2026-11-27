module

public import CasCompiler.Elaborate
public import CasCompiler.Syntax
public import Lean.Meta.Check

public section

namespace CasCompiler

open Lean Meta Elab Term



opaque SourceReadM.prove (proposition : Expr)
    (prepare : Expr → Array Expr → TermElabM Expr)
    (sources : Array Expr := #[]) : SourceReadM Expr := do
  let original ← get
  let formals ← original.context.bindings.filterM fun binding => do
    return binding.originalSource.isNone && (← binding.expression.fvarId!.getDecl).value?.isNone
  let function ← liftM (m := TermElabM) <| controlAt MetaM fun run =>
    original.context.withOriginalSources (#[proposition] ++ sources) fun expressions =>
      run do
        let expected := expressions[0]!
        unless ← isProp expected do
          throwError "source proof checking requires a proposition"
        let proof ← instantiateMVars (← prepare expected (expressions.extract 1 expressions.size))
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




opaque SourceSession.proof (session : SourceSession) (stx : TSyntax `cas_term)
    (obligation : ClosedTerm) (selections : SourceSelectionScope ClosedTerm := {}) :
    TermElabM SourceTerm := withRef stx do
  let `(cas_term| proof($evidence:term)) := stx
    | throwError "source evidence requires an explicit proof term"
  session.elaborateScoped evidence do
    let proposition ← session.readClosed evidence obligation selections
    SourceReadM.prove proposition (fun expected _ => sourceFormalProof evidence expected)

end CasCompiler
