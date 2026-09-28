/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CasCatalogue.Standard
public import CasCatalogue.ResolveSyntax
public import CasCatalogue.Leaves.Lattices.Valued.ActionProbes
public meta import CasCatalogue.Standard
public meta import CasCatalogue.ResolveSyntax
public meta import CasCatalogue.Leaves.Lattices.Valued.ActionProbes

@[expose] public section

/-!
# Acceptance for `cc-resolve` (CC-TRANSPORT, CC-UNIFORM, CC-RESOLVE)

* A formed module's `cardinality` resolves to the three-step structural composite
  `BilinModule → Mod_R → ∫ᶜ Mod → Sets` followed by the one registered cardinality on
  `Core(Sets)`; a lattice's to the four-step composite. No category below `Sets` declares a
  cardinality.
* The elaborated term is ordinary Lean: a `let` of the checked composite `FunctorExpr` around the
  composed `RealizedAction` applied to the receiver, with no string-keyed dispatch.
* The ring diamond: `Ring` reaches `Magma`, and hence `Sets`, along the multiplicative and the
  additive port, and the two routes are distinct. With no registered comparison, `cardinality` on
  rings is reported ambiguous with both routes; naming a port with `via` resolves it. (The
  comparison that identifies them at `Sets` is `cc-cohere`.)
-/

open Lean Meta Elab Term Command
open CasCatalogue.Lattices.Valued.ActionProbes CasCatalogue.Foundation.Cardinality

namespace CasCatalogue.ResolveProbes

/- Resolution reports its route (`#resolve` logs it; the `run_cmd` below asserts it). -/
#resolve cardinality in "cat.bilin_module"
#resolve cardinality in "cat.lattice"
#resolve cardinality in "cat.rings" via "fun.rings.multiplicative_monoid"

/- Execution receives `U(x)`: the value is computed by the composed actions. -/
#guard method% cardinality (a2.form) in "cat.bilin_module" == CardinalHandle.aleph0
#guard method% cardinality (a2) in "cat.lattice" == CardinalHandle.aleph0
#guard method% cardinality (e8) in "cat.lattice" == CardinalHandle.aleph0
/-- The zero lattice: `ℤ⁰` has one element. -/
def zeroLattice : Lattices.Valued.Actions.LatticeGramHandle := ⟨⟨0, !![]⟩, by decide⟩
#guard method% cardinality (zeroLattice) in "cat.lattice" == CardinalHandle.finite 1

/-- The value of a method call on the zero-rank Gram form, as elaborated. -/
def zeroFormCardinality := method% cardinality (zeroLattice.form) in "cat.bilin_module"

run_cmd liftTermElabM do
  let state ← registryState
  let some bilin := state.categories.find? (·.id.raw == "cat.bilin_module")
    | throwError "cat.bilin_module is not registered"
  let some lattice := state.categories.find? (·.id.raw == "cat.lattice")
    | throwError "cat.lattice is not registered"
  let some rings := state.categories.find? (·.id.raw == "cat.rings")
    | throwError "cat.rings is not registered"
  let some magmas := state.categories.find? (·.id.raw == "cat.magmas")
    | throwError "cat.magmas is not registered"
  -- CC-TRANSPORT: the formed module's route is the three-step structural composite.
  match state.resolveMethod bilin.expression "cardinality" with
  | .ok r =>
      unless r.route.functorIds.map (·.raw) ==
          #["fun.bilin_module.forget", "fun.modules.fibre_inclusion", "fun.modules.underlying"] do
        throwError "unexpected formed-module route {state.renderResolution r}"
      unless r.method.functor.raw == "fun.sets.cardinality" do
        throwError "cardinality is not the one registered on Sets"
  | .error e => throwError e.render state
  match state.resolveMethod lattice.expression "cardinality" with
  | .ok r =>
      unless r.route.functorIds.map (·.raw) == #["fun.lattice.forget_form",
          "fun.bilin_module.forget", "fun.modules.fibre_inclusion", "fun.modules.underlying"] do
        throwError "unexpected lattice route {state.renderResolution r}"
  | .error e => throwError e.render state
  -- CC-RESOLVE: the two ports of a ring are distinct routes to magmas.
  let portRoutes := state.routes rings.expression magmas.expression
  unless portRoutes.size == 2 &&
      portRoutes.any (·.functorIds.contains FunctorId.ringsMultiplicative) &&
      portRoutes.any (·.functorIds.contains FunctorId.ringsAdditive) do
    throwError "the ring's two ports are not two distinct routes to magmas"
  -- Without a comparison, `cardinality` on rings is ambiguous and names both routes.
  match state.resolveMethod rings.expression "cardinality" with
  | .error (.ambiguous _ candidates) =>
      unless candidates.size == 2 do
        throwError "expected exactly the two port routes, got {candidates.size}"
  | .ok r => throwError "ring cardinality resolved by a selection rule: {state.renderResolution r}"
  | .error e => throwError "unexpected: {e.render state}"
  -- Naming the port resolves it.
  match state.resolveMethod rings.expression "cardinality" #[FunctorId.ringsAdditive] with
  | .ok r =>
      unless r.route.functorIds.contains FunctorId.additiveGroupsToGroups do
        throwError "the additive port does not pass through the additive group"
  | .error e => throwError e.render state
  -- No route, and no method.
  let some cardinals := state.categories.find? (·.id.raw == "cat.cardinals")
    | throwError "cat.cardinals is not registered"
  match state.resolveMethod cardinals.expression "cardinality" with
  | .error (.notApplicable ..) => pure ()
  | _ => throwError "cardinality applied to cardinals, which have no structural route to Sets"
  match state.resolveMethod bilin.expression "no_such_method" with
  | .error (.unknownMethod _) => pure ()
  | _ => throwError "an unknown method resolved"
  -- Construction functors are not edges: nothing leaves a lattice by base change.
  unless (state.structuralEdges.filter fun e =>
      e.functor?.any (· == FunctorId.latticeBaseChange)).isEmpty do
    throwError "base change is an inheritance edge"
  -- The elaborated term is the composite applied, not a string-keyed call.
  let term ← `(method% cardinality (zeroLattice.form) in "cat.bilin_module")
  let e ← instantiateMVars (← elabTerm term none)
  unless e.isLet do throwError "the elaborated term does not bind the composite"
  let composite := e.letValue!
  unless composite.isAppOf ``FunctorExpr.comp do
    throwError "the bound composite is not a FunctorExpr composition"
  if (e.find? fun sub => sub == .lit (.strVal "cardinality")).isSome then
    throwError "the elaborated term contains a string-keyed method call"
  unless (e.letBody!.find? (·.isConstOf ``RealizedAction.comp)).isSome do
    throwError "the value is not computed by composed actions"

end CasCatalogue.ResolveProbes
