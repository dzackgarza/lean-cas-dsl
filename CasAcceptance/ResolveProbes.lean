/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CasCatalogue.ResolveSyntax
public import CasCatalogue.Semantic
public import LeanCategories.Catalogue.Semantics
public meta import CasCatalogue.ResolveSyntax
public meta import CasCatalogue.Semantic
public meta import LeanCategories.Catalogue.Semantics

@[expose] public section

/-!
# Acceptance for `cc-resolve` (CC-TRANSPORT, CC-UNIFORM, CC-RESOLVE)

* A formed module's `cardinality` resolves to the three-step structural composite
  `BilinModule → Mod_R → ∫ᶜ Mod → Sets` followed by the one registered cardinality on
  `Core(Sets)`; a lattice's to the four-step composite. No category below `Sets` declares a
  cardinality.
* The semantic reading of a method call is the method's functor applied after the route's
  composite functor (`Semantic.method`): a term of the catalogue's mathematics, recorded as the
  method after its route, with no string-keyed dispatch and no leaf in it.
* The ring diamond: `Ring` reaches `Magma`, and hence `Sets`, along the multiplicative and the
  additive port, and the two routes are distinct. This module deliberately does not import the
  comparison row (`lean-categories` `LeanCategories/Catalogue/Semantics/Algebra/PortComparison.lean`): without it, `cardinality` on rings is
  reported ambiguous with both routes, and naming a port with `via` resolves it. With it, see
  `CohereProbes`.
-/

open Lean Meta Elab Term Command

namespace CasCatalogue.ResolveProbes

/- Resolution reports its route (`#resolve` logs it; the `run_cmd` below asserts it). -/
#resolve cardinality in "cat.bilin_module"
#resolve cardinality in "cat.lattice"
#resolve cardinality in "cat.rings" via "fun.rings.multiplicative_monoid"

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
  -- The semantic reading of a call: the method's functor after the route's composite, recorded
  -- as the method after its route; no string-keyed dispatch, and no leaf.
  let some sets := state.categories.find? (·.id == CategoryId.sets)
    | throwError "cat.sets is not registered"
  let some fin := state.objects.find? (·.id.raw == "obj.sets.fin")
    | throwError "obj.sets.fin is not registered"
  let trace ← (Trace.new : IO _)
  let three ← Semantic.object fin #[Syntax.mkNumLit "3"] (some trace)
  let (value, target) ← Semantic.method "cardinality" three sets (some trace)
  unless target.id == CategoryId.cardinals do
    throwError "the cardinality of a set is not in the cardinals"
  unless (value.find? (·.isConstOf ``Prefunctor.obj)).isSome do
    throwError "the value is not the method's functor applied"
  if (value.find? fun sub => sub == .lit (.strVal "cardinality")).isSome then
    throwError "the semantic value contains a string-keyed method call"
  let some (.method id route receiver) ← (trace.node? value : IO _)
    | throwError "the call is not recorded as the method after its route"
  unless id.raw == "meth.cardinality" && route.isEmpty && receiver == three do
    throwError "recorded as {id.raw} after {route.size} steps"
  -- An unknown method, and a method whose owner no route reaches, are invalid.
  for name in ["frobnicate", "annihilator"] do
    let stratum ← try discard <| Semantic.method name three sets; pure none
      catch e => pure (Exception.stratum? e)
    unless stratum == some .invalid do
      throwError "`{name}` on a set fails as {repr stratum}, not as invalid"

end CasCatalogue.ResolveProbes
