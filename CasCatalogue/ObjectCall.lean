/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CasCatalogue.Resolve

@[expose] public section

/-!
# The public surface of named objects (CC-CALC, CC-SEP)

`obj% "obj.id" (a₁) … (aₙ) in "cat.id"` is the value of the registered object `obj.id` of the
category `cat.id` at the typed parameters `a₁ … aₙ` (`lean-categories`' object rows), as a handle
of the realizer whose registered presentation presents it. The presentation's identification is
what makes the handle mean that value; nothing names a leaf's handle constructor. With several
presentations, `using "rz.id"` names the realizer: which presentation is used is a realization
choice, never made by order.

Failures are stratified: an unregistered object or category, or an object of another category, is
`invalid`; no presentation is `noImplementation`; several without `using` are
`ambiguousRealization`.
-/

open Lean Meta Elab Term

namespace CasCatalogue

/-- Elaborate `obj% "obj.id" (args…) in "cat.id" [using "rz.id"]`. -/
def elabObjectCall (objectId : String) (args : Array Term) (category : String)
    (realizer? : Option String) : TermElabM Expr := do
  let state ← registryState
  let some categoryEntry := state.categories.find? (·.id.raw == category)
    | throwStratum .invalid m!"no registered category {category}"
  let some object := state.objects.find? (·.id.raw == objectId)
    | throwStratum .invalid m!"no registered object {objectId}"
  unless object.category == categoryEntry.id do
    throwStratum .invalid m!"{objectId} is an object of {object.category.raw}, not of {category}"
  let rows := state.presentations.filter fun row =>
    row.object == object.id && realizer?.all (row.realizer.raw == ·)
  let row ← match rows with
    | #[row] => pure row
    | #[] => throwStratum .noImplementation m!"no registered presentation of {objectId}"
    | _ => throwStratum .ambiguousRealization m!"several registered presentations of {objectId} \
        ({rows.toList.map (·.realizer.raw)}); which realization is used must be stated \
        (`using`)"
  let presentation := mkCIdent row.presentation
  let value ← elabTerm (← `(Sigma.fst ($presentation $args*))) none
  synthesizeSyntheticMVarsNoPostponing
  instantiateMVars value

/-- Elaborate `hom% (f) : (a) ⟶ (b) in "cat.id"`: the morphism of handles `a ⟶ b` whose denotation
is `f : d a ⟶ d b`, for the unique realizer `d` of `cat.id` whose handles `a` and `b` are. It is the
preimage of `f` along `d`'s fully faithful structure, so it denotes `f` exactly. -/
def elabHomCall (f source target : Term) (category : String) : TermElabM Expr := do
  let state ← registryState
  let some categoryEntry := state.categories.find? (·.id.raw == category)
    | throwStratum .invalid m!"no registered category {category}"
  let (denotation, a) ← receiverRealization state categoryEntry.id source
  let (denotation', b) ← receiverRealization state categoryEntry.id target
  unless ← isDefEq denotation denotation' do
    throwStratum .invalid m!"the two objects are handles of different realizers"
  let some realizer ← state.realizers.findM? fun r => do
      let d ← mkConstWithFreshMVarLevels r.denotation
      let (args, _, _) ← forallMetaTelescopeReducing (← inferType d)
      withoutModifyingState (isDefEq (mkAppN d args) denotation)
    | throwStratum .invalid m!"the objects' realizer is not registered"
  let some witness := realizer.fullyFaithful
    | throwStratum .noImplementation
        m!"{realizer.id.raw} has no fully faithful denotation: its morphisms are not presented"
  let hd ← mkConstWithFreshMVarLevels witness
  let (hdArgs, _, _) ← forallMetaTelescopeReducing (← inferType hd)
  let hd := mkAppN hd hdArgs
  unless ← isDefEq (← whnfR (← inferType hd)).appArg! denotation do
    throwError "the fully faithful witness of {realizer.id.raw} is not of its denotation"
  let expected ← mkAppM ``Quiver.Hom #[← mkAppM ``Prefunctor.obj
      #[← mkAppM ``CategoryTheory.Functor.toPrefunctor #[denotation], a],
    ← mkAppM ``Prefunctor.obj #[← mkAppM ``CategoryTheory.Functor.toPrefunctor #[denotation], b]]
  let map ← elabTermEnsuringType f expected
  synthesizeSyntheticMVarsNoPostponing
  instantiateMVars (← mkAppM ``CategoryTheory.Functor.FullyFaithful.preimage #[hd, map])

syntax (name := homCall) "hom% " "(" term ")" " : " "(" term ")" " ⟶ " "(" term ")" " in " str :
  term

syntax (name := objectCall)
  "obj% " str ("(" term ")")* " in " str (&" using " str)? : term

end CasCatalogue
