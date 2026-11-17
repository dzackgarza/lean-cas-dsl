module

public import CasCompiler.ReadContext
public import CasCatalogue.Evaluation

public section

namespace CasCompiler

open Lean Meta Elab Term

namespace ReadGraphRules

open SourceReader

def rule (context : ReadContext) : TermElabM NativeSourceJudgement := do
  let readExpression := @ReadContext.readExpression context
  let categoryOf := context.categoryOf
  let source := context.source
  match source with
  | `(cas_term| {$pairs:cas_pair,*} : $source:cas_term → $target:cas_term) => do
    -- The map with this graph, through the registered graph literal of the endpoints'
    -- category. Totality and distinct arguments are decided by the kernel on the literal.
    let domain ← readExpression categoryOf source none
    let codomain ← readExpression categoryOf target none
    let (domain, codomain) ← sourceCommonCategory domain codomain
    let some category := domain.category
      | throwError "a graph literal requires its selected category"
    unless category.role == .object && codomain.category.any (·.role == .object) do
      throwError "a graph literal maps between objects"
    let state ← CasCatalogue.semanticState
    let rows := state.graphLiterals.filter fun row => state.categories.any fun entry =>
      entry.id == row.category && entry.expression.syntacticEq category.expression
    let #[row] := rows
      | CasCatalogue.throwUnsupportedSource "the selected category has no registered graph literal"
    let sourceCarrierType := (← sourceCarrier domain).value
    let targetCarrierType := (← sourceCarrier codomain).value
    let pairType ← mkAppM ``Prod #[sourceCarrierType, targetCarrierType]
    let mut elements := #[]
    for pair in pairs.getElems do
      let `(cas_pair| $argument:cas_term ↦ $result:cas_term) := pair
        | throwError "a graph literal lists pairs `x ↦ y`"
      let argument ← readExpression categoryOf argument (some sourceCarrierType)
      let result ← readExpression categoryOf result (some targetCarrierType)
      elements := elements.push (← mkAppOptM ``Prod.mk
        #[some sourceCarrierType, some targetCarrierType, some argument.value, some result.value])
    let graph ← mkListLit pairType elements.toList
    discard <| checkedDeclaration row.denotation
    let constant ← mkConstWithFreshMVarLevels row.denotation
    let (arguments, infos, type) ← forallMetaTelescopeReducing (← inferType constant)
    let type ← whnfR type
    unless type.isAppOfArity ``Quiver.Hom 4 do
      throwError "the registered graph literal does not denote a map"
    unless ← isDefEq type.getAppArgs[2]! domain.value <&&>
        isDefEq type.getAppArgs[3]! codomain.value do
      throwError "the registered graph literal has different endpoints"
    let explicit := (List.range arguments.size).toArray.filter (infos[·]!.isExplicit)
    let some first := explicit[0]? | throwError "the graph literal takes no graph"
    unless ← isDefEq arguments[first]! graph do
      throwError "the graph literal does not accept this list of pairs"
    for argument in arguments, info in infos do
      if info.isInstImplicit && (← instantiateMVars argument).isMVar then
        let some instanceValue ← synthInstance? (← inferType argument)
          | throwError "the graph literal lacks its declared decidable equality"
        discard <| isDefEq argument instanceValue
    for index in explicit.drop 1 do
      let obligation ← instantiateMVars (← inferType arguments[index]!)
      let some proof ← CasCatalogue.Decide.decisionProof obligation
        | CasCatalogue.throwStratum .invalid m!"the graph does not list each element once: {obligation}"
      discard <| isDefEq arguments[index]! proof
    let value ← instantiateMVars (mkAppN constant arguments)
    return ⟨sourceReference ``CasCatalogue.GraphLiteralEntry row.id.raw row.denotation value,
      some { category with role := .morphism, carrier := none }⟩
  | _ => throwReadRuleMismatch

end ReadGraphRules

end CasCompiler
