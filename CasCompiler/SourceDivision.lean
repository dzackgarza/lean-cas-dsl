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








def sourceDivision (owners : Array NativeSourceOperationDomain) (left right : TSyntax `cas_term)
    (read : TSyntax `cas_term → SourceReadM Expr) : SourceReadM Expr := do
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
    liftM (m := TermElabM) <| do trace[cas.division] "{row.id.raw}: object parameters {objects.map (·.id.raw)}; owners {owners.map (·.value)}"
    let #[category] := objects | continue
    for owner in owners do
      let routes ← SourceRoutes.forOwner owner.category.expression category.expression
      let some routes ← routes.finiteRoutes
        | liftM (m := TermElabM) <| throwUnsupportedSource "the division's monoid view requires its uniform comparison"
      liftM (m := TermElabM) <| do trace[cas.division] "{owner.value} has {routes.size} routes to {category.id.raw}"
      unless routes.isEmpty do candidates := candidates.push (row, category, owner)
  let (row, category, owner) ← match candidates with
    | #[candidate] => pure candidate
    | #[] => liftM (m := TermElabM) <| throwUnsupportedSource "no registered division `/` applies to the operands' object"
    | _ => liftM (m := TermElabM) <| throwSemanticAmbiguity "several registered divisions `/` apply to the operands' object"
  let monoid ← sourceStructuralView ⟨owner.value, some owner.category⟩ category.expression
    (some "/")
  let (morphism, _, parameters) ← morphismAtSource row
  let some objectIndex := parameters.findIdx? fun (_, info) => info.isExplicit
    | liftM (m := TermElabM) <| throwError "the registered division lost its object parameter"
  let (parameter, _) := parameters[objectIndex]!


  let monoidAtParameter ← mkExpectedTypeHint monoid.value (← liftM (m := MetaM) <| instantiateMVars (← inferType parameter))
  unless ← isDefEq parameter monoidAtParameter do
    liftM (m := TermElabM) <| throwError "the registered division does not take the operands' monoid"
  unless ← synthesizeDeclared parameters do
    liftM (m := TermElabM) <| throwError "the registered division lacks a declared instance at the operands' monoid"


  let arguments ← liftM (m := MetaM) <|
    parameters.mapM fun (parameter, _) => instantiateMVars parameter
  let morphism := mkAppN (← liftM (m := MetaM) <| instantiateMVars morphism.getAppFn)
    (arguments.set! objectIndex monoidAtParameter)
  if morphism.hasMVar || morphism.hasLevelMVar then
    liftM (m := TermElabM) <| throwError "the registered division is not determined by the operands' monoid"
  let #[originalCategory] := state.categories.filter (·.id == row.category)
    | liftM (m := TermElabM) <| throwError "the registered division lost its original complete category row"
  let selected ← SourceReadM.select
    (← sourceReferenceAt (.named (.registered (.inr row) originalCategory)) morphism morphism)
  let function ← sourceSetFunction selected
  let hole ← mkFreshExprMVar none
  discard <| elabAppArgs function #[] #[Arg.expr hole] none false false
  let pair ← whnfR (← liftM (m := MetaM) <| instantiateMVars (← inferType hole))
  unless pair.isAppOfArity ``Prod 2 do
    liftM (m := TermElabM) <| throwError "the registered division does not take a pair"
  let operand := fun (source : TSyntax `cas_term) (type : Expr) => do
    let value ← read source
    let value ← match owner.comparison with
      | none => pure value
      | some comparison => do
        let inverse ← sourceSetFunction (← mkAppM ``CategoryTheory.Iso.inv #[comparison])
        elabAppArgs inverse #[] #[Arg.expr value] (some type) false false
    unless ← isDefEq (← inferType value) type do
      liftM (m := TermElabM) <| throwErrorAt source "the operand is not in the monoid the division acts on"
    return value
  let dividend ← operand left pair.getAppArgs[0]!


  let units := pair.getAppArgs[1]!
  let #[entry] := state.objects.filter fun entry =>
      entry.admission.isSome && units.getAppFn.constName? == some entry.declaration
    | liftM (m := TermElabM) <| throwError "the divisor's factor {units} of the registered division is not one admitted subobject"
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
    value ← liftM (m := MetaM) <| withLetDecl (← mkFreshUserName `divisionOwnerAgreement)
      (← inferType evidence) evidence fun binding =>
        mkLetFVars #[binding] body (usedLetOnly := false) (generalizeNondepLet := false)
  return value

end CasCompiler
