/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CasCatalogue.Resolve
public import CasContract.Limits
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers

@[expose] public section

/-!
# The public surface of registered limits and colimits (CC-UNIV, CC-LIFT)

`limit% shape (D) in "cat.id"` and `colimit% shape (D) in "cat.id"`, for a diagram `D` of handles,
elaborate to the realized `LimitCone D` or `ColimitCocone D`:

1. the registered limit of `shape` in the category is resolved (`resolveLimit`): its own
   presentation, or one in the target of a registered creation lift, which the resolution names;
2. the diagram is elaborated as a diagram of handles of the unique registered realizer of the
   category that has a limit realization of that limit (along that lift);
3. the registered presentation is taken at the diagram's denotation (after the lift's functor),
   identified with the standard form of the shape by Mathlib's `diagramIsoCospan`,
   `diagramIsoPair` or `diagramIsoParallelPair`;
4. the leaf's apex handle and its identification complete the realized cone
   (`realizedLimitCone`, `realizedReturnedLimitCone`, `realizedColimitCocone`), whose legs and
   mediators are the core's.

Failures are stratified: an unregistered limit is `invalid`; no realization on the diagram's
presentation is `noImplementation`.
-/

open Lean Meta Elab Term CategoryTheory

namespace CasCatalogue

/-- Mathlib's identification of a diagram of a standard shape with its standard form. -/
def standardFormIso : String → Option Name
  | "pullback" => some ``CategoryTheory.Limits.diagramIsoCospan
  | "product" | "coproduct" => some ``CategoryTheory.Limits.diagramIsoPair
  | "kernel" | "cokernel" | "equalizer" | "coequalizer" =>
      some ``CategoryTheory.Limits.diagramIsoParallelPair
  | _ => none

/-- A declaration applied to fresh metavariables for all its arguments. -/
def instantiateFresh (declaration : Name) : MetaM Expr := do
  let constant ← mkConstWithFreshMVarLevels declaration
  let (args, _, _) ← forallMetaTelescopeReducing (← inferType constant)
  return mkAppN constant args

/-- The full and faithful structure of a lift's functor `U`: a property classifier's fields, or
Lean's instances `U.Full` and `U.Faithful`. -/
def liftFullyFaithful (state : RegistryState) (lift : LiftEntry) (U : Expr) : MetaM Expr := do
  if let .classifierForget id := lift.edge then
    if let some entry := state.classifier? id then
      let value ← instantiateFresh entry.declaration
      if (← whnf (← inferType value)).isAppOf ``LeanCategories.PropertyClassifier then
        let full ← mkAppM ``LeanCategories.PropertyClassifier.full #[value]
        let faithful ← mkAppM ``LeanCategories.PropertyClassifier.faithful #[value]
        return ← mkAppOptM ``Functor.FullyFaithful.ofFullyFaithful
          #[none, none, none, none, U, full, faithful]
  let full? ← synthInstance? (← mkAppM ``Functor.Full #[U])
  let faithful? ← synthInstance? (← mkAppM ``Functor.Faithful #[U])
  let (some full, some faithful) := (full?, faithful?)
    | throwStratum .noImplementation m!"{lift.edge.label} is not known to be full and faithful: \
        returning a limit along it needs a morphism rule"
  mkAppOptM ``Functor.FullyFaithful.ofFullyFaithful #[none, none, none, none, U, full, faithful]

/-- Elaborate `limit% shape (diagram) in "cat.id"` (or `colimit%`). -/
def elabLimitCall (colimit : Bool) (shape : String) (diagram : Term) (category : String) :
    TermElabM Expr := do
  let state ← registryState
  let some categoryEntry := state.categories.find? (·.id.raw == category)
    | throwStratum .invalid m!"no registered category {category}"
  let resolution ← match state.resolveLimit categoryEntry.id shape colimit with
    | .ok resolution => pure resolution
    | .error message => throwStratum .invalid m!"{message}"
  let some limit := state.limits.find? (·.id == resolution.limit) | unreachable!
  let J ← limitShapeIndex limit
  let some isoName := standardFormIso shape
    | throwStratum .noImplementation m!"the shape {shape} has no standard form here"
  let lift? := resolution.lift.bind fun id => state.lifts.find? (·.id == id)
  let rows := state.limitRealizations.filter fun row =>
    row.limit == resolution.limit && row.lift == resolution.lift &&
      (state.realizers.find? (·.id == row.realizer)).any (·.category == categoryEntry.id)
  -- The diagram's realizer: the unique one whose handles it is a diagram of.
  let attempt (row : LimitRealizationEntry) : TermElabM (RealizerEntry × Expr × Expr) := do
    let some realizer := state.realizers.find? (·.id == row.realizer) | unreachable!
    let d ← instantiateFresh realizer.denotation
    let handles := (← whnfR (← inferType d)).getAppArgs[0]!
    let expected ← mkAppOptM ``CategoryTheory.Functor #[J, none, handles, none]
    let D ← withoutErrToSorry <| elabTermEnsuringType diagram expected
    synthesizeSyntheticMVarsNoPostponing
    let D ← instantiateMVars D
    let type ← whnfR (← inferType D)
    unless type.isAppOfArity ``CategoryTheory.Functor 4 &&
        (← isDefEq type.getAppArgs[2]! handles) do
      throwError "not a diagram of {realizer.id.raw} handles"
    return (realizer, d, D)
  let mut accepting : Array LimitRealizationEntry := #[]
  for row in rows do
    let saved ← saveState
    try discard <| attempt row; accepting := accepting.push row
    -- not a reading fallback: realization selection: every applicable limit realization is collected, exactly one is required
    catch e => trace[Meta.debug] "{row.id.raw}: {e.toMessageData}"
    saved.restore
  let row ← match accepting with
    | #[row] => pure row
    | #[] => throwStratum .noImplementation
                m!"no registered realization of {limit.id.raw} applies to this diagram"
    | _ => throwStratum .ambiguousRealization
               m!"several registered realizations of {limit.id.raw} apply to this diagram"
  let (realizer, d, D) ← attempt row
  let some ffName := realizer.fullyFaithful
    | throwStratum .noImplementation
        m!"{realizer.id.raw} has no fully faithful denotation: its limits need a morphism rule"
  let hd ← instantiateFresh ffName
  unless ← isDefEq (← whnfR (← inferType hd)).appArg! d do
    throwError "the fully faithful witness of {realizer.id.raw} is not of its denotation"
  -- The registered presentation at the diagram's denotation (after the lift's functor).
  let mut F ← mkAppM ``Functor.comp #[D, d]
  let mut U? : Option Expr := none
  if let some lift := lift? then
    let U ← state.edgeFunctor lift.edge
    F ← withTransparency .all <| mkFunctorComp F U
    U? := some U
  let α ← mkAppM isoName #[F]
  let standard := (← whnfR (← inferType α)).getAppArgs.back!
  let family ← instantiateFresh limit.declaration
  let familyDiagram := (← whnfR (← inferType family)).appArg!
  unless ← withTransparency .all <| isDefEq familyDiagram standard do
    throwError "the registered presentation {limit.declaration} does not apply to {standard}"
  let L ← mkAppM (if colimit then ``colimitCoconeOfIso else ``limitConeOfIso) #[α, family]
  let apex ← if colimit then mkAppM ``CategoryTheory.Limits.Cocone.pt #[← mkAppM ``CategoryTheory.Limits.ColimitCocone.cocone #[L]]
    else mkAppM ``CategoryTheory.Limits.Cone.pt #[← mkAppM ``CategoryTheory.Limits.LimitCone.cone #[L]]
  -- The leaf's apex handle with its identification.
  let presentation ← instantiateFresh row.realization
  let identification ← whnfR (← inferType (← mkAppM ``Sigma.snd #[presentation]))
  unless identification.isAppOfArity ``CategoryTheory.Iso 4 &&
      (← withTransparency .all <| isDefEq identification.getAppArgs[3]! apex) do
    throwStratum .noImplementation
      m!"the realization {row.id.raw} does not present the apex of this diagram"
  let a ← mkAppM ``Sigma.fst #[presentation]
  let φ ← mkAppM ``Sigma.snd #[presentation]
  let result ← match colimit, U? with
    | true, _ => mkAppM ``realizedColimitCocone #[hd, L, a, φ]
    | false, none => mkAppM ``realizedLimitCone #[hd, L, a, φ]
    | false, some U =>
        let some lift := lift? | unreachable!
        let hU ← liftFullyFaithful state lift U
        mkAppM ``realizedReturnedLimitCone #[hd, hU, L, a, φ]
  let result ← instantiateMVars result
  if result.hasExprMVar then
    throwError "the realized limit is not determined by the diagram: {result}"
  let via := match resolution.lift with
    | some id => s!" returned along {id.raw}"
    | none => ""
  logInfo m!"resolved: {limit.id.raw}{via} ; realized by {row.id.raw}"
  return result

syntax (name := limitCall) "limit% " ident " (" term ") " "in " str : term
syntax (name := colimitCall) "colimit% " ident " (" term ") " "in " str : term

end CasCatalogue
