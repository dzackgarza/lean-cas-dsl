module

public import CasCompiler.ReadContext
public import CasCompiler.SourceProof
public import CasCatalogue.Decide
import CasCompiler.SourceCarrier

public section

namespace CasCompiler

open Lean Meta Elab Term

namespace ReadGraphRules

open SourceReader

def rule (context : ReadContext) : SourceReadM NativeSourceJudgement := do
  let readExpression := @ReadContext.readExpression context
  let categoryOf := context.categoryOf
  let source := context.source
  match source with
  | `(cas_term| {$pairs:cas_pair,*} : $source:cas_term → $target:cas_term) => do


    let domain ← readExpression categoryOf source none
    let codomain ← readExpression categoryOf target none
    let (domain, codomain) ← sourceCommonCategory domain codomain
    let some category := domain.category
      | liftM (m := TermElabM) <| throwError "a graph literal requires its selected category"
    unless category.role == .object && codomain.category.any (·.role == .object) do
      liftM (m := TermElabM) <| throwError "a graph literal maps between objects"
    let state ← CasCatalogue.semanticState
    let rows := state.graphLiterals.filter fun row => state.categories.any fun entry =>
      entry.id == row.category && entry.expression.syntacticEq category.expression
    let #[row] := rows
      | liftM (m := TermElabM) <| CasCatalogue.throwUnsupportedSource "the selected category has no registered graph literal"
    let sourceCarrierType := (← sourceCarrier domain).value
    let targetCarrierType := (← sourceCarrier codomain).value
    let pairType ← mkAppM ``Prod #[sourceCarrierType, targetCarrierType]
    let mut elements := #[]
    for pair in pairs.getElems do
      let `(cas_pair| $argument:cas_term ↦ $result:cas_term) := pair
        | liftM (m := TermElabM) <| throwError "a graph literal lists pairs `x ↦ y`"
      let argument ← readExpression categoryOf argument (some sourceCarrierType)
      let result ← readExpression categoryOf result (some targetCarrierType)
      elements := elements.push (← mkAppOptM ``Prod.mk
        #[some sourceCarrierType, some targetCarrierType, some argument.value, some result.value])
    let graph ← mkListLit pairType elements.toList
    discard <| checkedDeclaration row.denotation
    let constant ← mkConstWithFreshMVarLevels row.denotation
    let before ← liftM (m := MetaM) getMCtx
    let (arguments, infos, type) ← forallMetaTelescopeReducing (← inferType constant)
    let owned := (← liftM (m := MetaM) getMCtx).decls.foldl (fun result identity _ =>
      if before.decls.contains identity then result else result.push identity) #[]
    let type ← whnfR type
    unless type.isAppOfArity ``Quiver.Hom 4 do
      liftM (m := TermElabM) <| throwError "the registered graph literal does not denote a map"
    unless ← isDefEq type.getAppArgs[2]! domain.value <&&>
        isDefEq type.getAppArgs[3]! codomain.value do
      liftM (m := TermElabM) <| throwError "the registered graph literal has different endpoints"
    let explicit := (List.range arguments.size).toArray.filter (infos[·]!.isExplicit)
    let some first := explicit[0]? | liftM (m := TermElabM) <| throwError "the graph literal takes no graph"
    unless ← isDefEq arguments[first]! graph do
      liftM (m := TermElabM) <| throwError "the graph literal does not accept this list of pairs"
    for argument in arguments, info in infos do
      if info.isInstImplicit && (← liftM (m := MetaM) <| instantiateMVars argument).isMVar then
        let some instanceValue ← synthInstance? (← inferType argument)
          | liftM (m := TermElabM) <| throwError "the graph literal lacks its declared decidable equality"
        discard <| isDefEq argument instanceValue
    for index in explicit.drop 1 do
      let obligation ← liftM (m := MetaM) <| instantiateMVars (← inferType arguments[index]!)
      let proof ← SourceReadM.prove obligation fun original _ => do
        let some proof ← CasCatalogue.Decide.decisionProof original
          | CasCatalogue.throwStratum .invalid m!"the graph does not list each element once: {original}"
        return proof
      extendSourceApplicationScope owned
      discard <| isDefEq arguments[index]! proof
    let value ← liftM (m := MetaM) <| instantiateMVars (mkAppN constant arguments)
    let category := { category with role := .morphism, carrier := none, limit := none }
    let selected ← sourceReferenceAt (.graph row) value value
    let value ← selectMorphism { selected with category := some category }
      (fun selected expected => SourceReadM.select selected expected) (some category.bundle)
    return ⟨value, some category⟩
  | _ => throwReadRuleMismatch

end ReadGraphRules

end CasCompiler
