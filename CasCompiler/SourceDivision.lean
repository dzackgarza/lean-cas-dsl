module

public import CasCompiler.SourceMember
public import CasCompiler.SourceAdmission
public import CasCompiler.SourceTypeOrigin
public import CasCompiler.SourceOperation
import CasCompiler.SourceCarrier

public section

namespace CasCompiler

open Lean Meta Elab Term CasCatalogue

initialize registerTraceClass `cas.division

/-- `a / b`: a registered morphism named `/` (`mor.sets.divide : M × Mˣ → M`) at the object `M` of
its parameter category that the operands' registered owner is, viewed along its structural route.
Competing routes are resolved by a declared preferred route for `/`, else by their whole-family
agreement, else the reading is ambiguous (sourceStructuralView; constitution C6). The divisor is
admitted into the second factor with that subobject's own evidence (sourceAdmission).
`owners` are the registered objects whose carrier is the operands' set; `read` reads an operand in
that set. Several applicable rows or owners are ambiguous; none is an unsupported source. -/
def sourceDivision (owners : Array NativeSourceOperationDomain) (left right : TSyntax `cas_term)
    (read : TSyntax `cas_term → TermElabM Expr) : TermElabM Expr := do
  let state ← semanticState
  let mut candidates := #[]
  for row in state.morphisms do
    unless row.name == "/" do continue
    let (_, _, parameters) ← morphismAtSource row
    let mut objects := #[]
    for (parameter, info) in parameters do
      unless info.isExplicit do continue
      if let some category ← sourceObjectCategory? (← inferType parameter) then
        objects := objects.push category
    trace[cas.division] "{row.id.raw}: object parameters {objects.map (·.id.raw)}; owners {owners.map (·.value)}"
    let #[category] := objects | continue
    for owner in owners do
      let routes ← SourceRoutes.forOwner owner.category.expression category.expression
      let some routes ← routes.finiteRoutes
        | throwUnsupportedSource "the division's monoid view requires its uniform comparison"
      trace[cas.division] "{owner.value} has {routes.size} routes to {category.id.raw}"
      unless routes.isEmpty do candidates := candidates.push (row, category, owner)
  let (row, category, owner) ← match candidates with
    | #[candidate] => pure candidate
    | #[] => throwUnsupportedSource "no registered division `/` applies to the operands' object"
    | _ => throwSemanticAmbiguity "several registered divisions `/` apply to the operands' object"
  let monoid ← sourceStructuralView ⟨owner.value, some owner.category⟩ category.expression
    (some "/")
  let (morphism, _, parameters) ← morphismAtSource row
  let some objectIndex := parameters.findIdx? fun (_, info) => info.isExplicit
    | throwError "the registered division lost its object parameter"
  let (parameter, _) := parameters[objectIndex]!
  -- The monoid is stated at the parameter's own type (`MonCat`), not at the bundled category of
  -- the view, so that the factor `Mˣ` is spelled as its admission declares it.
  let monoidAtParameter ← mkExpectedTypeHint monoid.value (← instantiateMVars (← inferType parameter))
  unless ← isDefEq parameter monoidAtParameter do
    throwError "the registered division does not take the operands' monoid"
  unless ← synthesizeDeclared parameters do
    throwError "the registered division lacks a declared instance at the operands' monoid"
  -- Native unification checks this argument but may normalize its view. The actual
  -- declaration keeps the original routed object in its complete formal position.
  let arguments ← parameters.mapM fun (parameter, _) => instantiateMVars parameter
  let morphism := mkAppN (← instantiateMVars morphism.getAppFn)
    (arguments.set! objectIndex monoidAtParameter)
  if morphism.hasMVar || morphism.hasLevelMVar then
    throwError "the registered division is not determined by the operands' monoid"
  let function ← sourceSetFunction
    (sourceReference ``MorphismEntry row.id.raw row.declaration morphism)
  let hole ← mkFreshExprMVar none
  discard <| elabAppArgs function #[] #[Arg.expr hole] none false false
  let pair ← whnfR (← instantiateMVars (← inferType hole))
  unless pair.isAppOfArity ``Prod 2 do
    throwError "the registered division does not take a pair"
  let operand := fun (source : TSyntax `cas_term) (type : Expr) => do
    let value ← read source
    let value ← match owner.comparison with
      | none => pure value
      | some comparison => do
        let inverse ← sourceSetFunction (← mkAppM ``CategoryTheory.Iso.inv #[comparison])
        elabAppArgs inverse #[] #[Arg.expr value] (some type) false false
    unless ← isDefEq (← inferType value) type do
      throwErrorAt source "the operand is not in the monoid the division acts on"
    return value
  let dividend ← operand left pair.getAppArgs[0]!
  -- The divisor's factor is a registered subobject at the monoid (`Mˣ`): the admitted object
  -- whose declaration is its head.
  let units := pair.getAppArgs[1]!
  let #[entry] := state.objects.filter fun entry =>
      entry.admission.isSome && units.getAppFn.constName? == some entry.declaration
    | throwError "the divisor's factor {units} of the registered division is not one admitted subobject"
  let divisor ← sourceAdmission entry units fun base => operand right base
  let tuple ← mkAppM ``Prod.mk #[dividend, divisor]
  let value ← elabAppArgs function #[] #[Arg.expr tuple] none false false
  let mut value ← match owner.comparison with
    | none => pure value
    | some comparison => do
      let forward ← sourceSetFunction (← mkAppM ``CategoryTheory.Iso.hom #[comparison])
      elabAppArgs forward #[] #[Arg.expr value] none false false
  for evidence in owner.originEvidence.reverse do
    let body := value
    value ← withLetDecl (← mkFreshUserName `divisionOwnerAgreement)
      (← inferType evidence) evidence fun binding =>
        mkLetFVars #[binding] body (usedLetOnly := false) (generalizeNondepLet := false)
  return value

end CasCompiler
