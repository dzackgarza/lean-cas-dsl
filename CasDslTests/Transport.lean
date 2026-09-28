/-
Receiver transport through the `CasCatalogue` registry (`cc-dsl-migration`).

`x.f` is `f(F(x))`: a method call on a semantic point resolves, by the one
resolver (`CasCatalogue.RegistryState.resolveMethod`), to a route of
registered structural functors from the point's category to the method's
owner, and execution receives the route's image, computed by the registered
actions from the realizer the presentation encodes into (CC-TRANSPORT,
CC-SEP). Each claim the name-level transport tests made is asserted here
against that resolver:

* the transported image is the underlying set, computed by actions (ℤ/4 ↦
  its four residues; ℤ/0 = ℤ ↦ ℤ, which the old object map could not present);
* the router and the executor see the image, never the module;
* a transported resolution records its route;
* direct and transported routes are one candidate pool: a call reachable
  both ways is an ambiguity naming both, never settled by which was found
  first;
* a method whose owner no structural route reaches is not applicable;
* a functor row whose declaration does not land in its declared target is
  rejected at registration, so a mislabeled transport cannot be used;
* a transported resolution with no implementation on the image is a gap
  naming the route;
* the surface: binding, method call, `#explain_route`, argument handling and
  category-bound `=`; and #53 §11: `(ℤ/2)⁴` in `Mod(ℤ/2)` has cardinality 16.
-/
import CasDsl

namespace CasDslTests.Transport

open Lean Elab Command Meta
open CasDsl CasCatalogue

private def contains (hay needle : String) : Bool := (hay.splitOn needle).length > 1

/-- The four residues of ℤ/4, spelled independently of the decoder. -/
private def modUnderlying : Obj :=
  .setObj (.finite (.mod 4) #[.mod 4 0, .mod 4 1, .mod 4 2, .mod 4 3])

/-- A call on a point of `Mod_R`. -/
private def callOn (env : Environment) (base : Domain) (pres : Obj) (m : String)
    (withArguments := false) : IO (Except String Semantic.Plan) :=
  Semantic.call env "cat.modules_r" (some base) pres m withArguments

/-! ## The transported image, computed by the registered actions -/

run_cmd do
  let env ← getEnv
  -- `contains` has no Lean-native action, so the call returns the image it must run on
  match ← callOn env .int (.domainObj (.mod 4)) "contains" (withArguments := true) with
  | .ok { value? := some _, .. } => throwError "`contains` was answered without its argument"
  | .ok { image? := some image, route, .. } =>
      unless image == modUnderlying do
        throwError s!"U(ℤ/4) is {image.presentation}, expected {modUnderlying.presentation}"
      -- the route is the transport: fibre inclusion, underlying set, the set as a subset
      for step in ["fun.modules.fibre_inclusion", "fun.modules.underlying",
          "fun.sets.whole_subset"] do
        unless contains route step do
          throwError s!"the route to `contains` does not pass through {step}: {route}"
  | .ok _ => throwError "`contains` on ℤ/4 has no decoded image"
  | .error e => throwError s!"`contains` did not resolve on ℤ/4: {e}"
  -- ℤ/0 = ℤ: the underlying set is ℤ, infinite; the functor is total
  match ← callOn env .int (.domainObj (.mod 0)) "cardinality" with
  | .ok { value? := some v, .. } =>
      unless v == .cardinal .countablyInfinite do
        throwError s!"|U(ℤ/0)| came back as {v.render}, expected ℵ₀"
  | _ => throwError "the cardinality of ℤ/0 as a ℤ-module did not run in Lean"

/-! ## The transported resolution, and its value

`cardinality` is owned by `Sets` alone; a ℤ-module reaches it through two
structural functors, and the whole composite runs in Lean. -/

run_cmd do
  let env ← getEnv
  match ← callOn env .int (.domainObj (.mod 4)) "cardinality" with
  | .ok { value? := some v, route, .. } =>
      unless v == .cardinal (.finite 4) do
        throwError s!"|ℤ/4| came back as {v.render}, expected 4"
      unless contains route "cat.modules_r --fun.modules.fibre_inclusion--> cat.modules_total \
          --fun.modules.underlying--> cat.sets ; meth.cardinality" do
        throwError s!"unexpected route for cardinality: {route}"
  | .ok _ => throwError "cardinality of ℤ/4 did not run as a Lean composite"
  | .error e => throwError s!"cardinality of ℤ/4 failed: {e}"

/-! ## One candidate pool: a call reachable directly and by transport is ambiguous

`size` is declared twice in this module's copy of the registry: on `Sets` (as
cardinality, reached by transport) and on `Mod_R` itself (as rank, reached by
the empty route). Neither is consulted first; the call is an ambiguity
carrying both routes. -/

run_cmd liftTermElabM do
  -- (`MethodEntry.mk`: in this file `{ … }` is the notebook's set literal)
  addRegistryEntryChecked (.method (MethodEntry.mk ⟨"meth.probe.size_sets"⟩ "size"
    Foundation.Sets FunctorId.setsCardinality .isoInvariant false))
  addRegistryEntryChecked (.method (MethodEntry.mk ⟨"meth.probe.size_modules"⟩ "size"
    Modules.Modules FunctorId.modulesRank .isoInvariant false))

run_cmd do
  let env ← getEnv
  match ← callOn env .int (.domainObj (.mod 4)) "size" with
  | .error e =>
      unless contains e "ambiguous" && contains e "meth.probe.size_sets" &&
          contains e "meth.probe.size_modules" do
        throwError s!"`size` did not report both candidates: {e}"
  | .ok _ => throwError "`size`, reachable directly and by transport, was resolved to one"

/-! ## A method no structural route reaches is not applicable

`kernel` is owned by the arrows of modules; a module is not an arrow, so no
route reaches it. An unknown name is reported as such. -/

run_cmd do
  let env ← getEnv
  match ← callOn env .int (.domainObj (.mod 4)) "kernel" with
  | .error e =>
      unless contains e "not available here" do
        throwError s!"`kernel` on a module was not reported inapplicable: {e}"
  | .ok _ => throwError "`kernel` resolved on a module"
  match ← callOn env .int (.domainObj (.mod 4)) "casdslNoSuchMethod" with
  | .error e =>
      unless contains e "no method is named" do
        throwError s!"an unknown method was not reported as such: {e}"
  | .ok _ => throwError "an unknown method resolved"

/-! ## A mislabeled functor cannot be registered

The name-level resolver detected, at call time, a functor whose image did not
reach its declared target. A registered functor row is typed: its declaration
must be a functor between the denotations of its endpoints, so a row claiming
that the underlying-set functor lands in rings is refused before it can be
used. -/

run_cmd liftTermElabM do
  let mislabeled : FunctorEntry := FunctorEntry.mk ⟨"fun.probe.mislabeled"⟩
    Modules.ModulesTotal Algebra.Catalogue.Rings.Rings
    `CasCatalogue.Modules.CatalogueRegistration.modulesUnderlyingDeclaration
    `CasCatalogue.Modules.CatalogueRegistration.modulesUnderlyingRealization
    (.atomic ⟨"fun.probe.mislabeled"⟩) true
  let accepted ← try validateRegistryEntryDeclaration (.functor mislabeled); pure true
    catch _ => pure false
  if accepted then throwError "a functor row landing outside its declared target was accepted"

/-! ## A transported resolution with no implementation is a gap naming the route -/

run_cmd liftTermElabM do
  addRegistryEntryChecked (.method (MethodEntry.mk ⟨"meth.probe.unrouted"⟩ "casdslUnrouted"
    Constructed.SubobjectsSets FunctorId.subsetsContains .isoInvariant false))

let F := ℤ/4 in Modules(ℤ)

run_cmd do
  let env ← getEnv
  match ← runEval env (.method (.ref `F) `casdslUnrouted #[]) with
  | .error e =>
      let text := e.render
      unless contains text "NoImplementation" && contains text "fun.modules.underlying" do
        throwError s!"the gap hides the transport: {text}"
  | .ok d => throwError s!"a method with no implementation ran: {d.render}"

/-! ## The surface path -/

#explain_route F.cardinality()

run_cmd do
  let env ← getEnv
  match ← runEval env (.method (.ref `F) `cardinality #[]) with
  | .ok d =>
      unless d.render == "4" do
        throwError s!"F.cardinality() evaluated to {d.render}, expected 4"
  | .error e => throwError s!"F.cardinality() failed: {e.render}"

-- `contains` transports, and the ARGUMENT is not transported: it is read in the
-- ambient set of the image, so `2` names the residue class 2 while `1/2` is not
-- an element of it
run_cmd do
  let env ← getEnv
  let cases : List (String × CasExpr × String) :=
    [("2", .num 2, "true"), ("1/2", .bin .div (.num 1) (.num 2), "false")]
  for (label, arg, expected) in cases do
    match ← runEval env (.method (.ref `F) `contains #[arg]) with
    | .ok d =>
        unless d.render == expected do
          throwError s!"F.contains({label}) evaluated to {d.render}, expected {expected}"
    | .error e => throwError s!"F.contains({label}) failed: {e.render}"

/-! ## Bare `=` is category-bound (design review 2026-07-30)

`U(F) = {0, 1, 2, 3}` in Sets, but `F` is a module: bare `=` never inserts a
functor, so equality across categories is trivially false. The Sets question
is the explicit method call, whose receiver transports. -/

run_cmd do
  let env ← getEnv
  let ctx : EvalCtx := { env, notes := ← IO.mkRef #[],
                         annotations := ← IO.mkRef #[] }
  let setLit : CasExpr := .finSet #[.num 0, .num 1, .num 2, .num 3]
  match ← (evalAssert ctx .eq (.ref `F) setLit).run with
  | .ok (some false) => pure ()
  | .ok r => throwError s!"F = {"{0,1,2,3}"} must be trivially FALSE across \
categories, got {repr r}"
  | .error e => throwError s!"F = {"{0,1,2,3}"} must be trivially false, not an \
error: {e.render}"
  match ← (evalAssert ctx .ne (.ref `F) setLit).run with
  | .ok (some true) => pure ()
  | _ => throwError s!"F ≠ {"{0,1,2,3}"} must be trivially true across categories"
  match ← runEval env (.method (.ref `F) `set_eq #[setLit]) with
  | .ok d =>
      unless d.render == "true" do
        throwError s!"F.set_eq({"{0,1,2,3}"}) evaluated to {d.render}, expected true"
  | .error e => throwError s!"F.set_eq({"{0,1,2,3}"}) failed: {e.render}"
  match ← (evalAssert ctx .eq setLit setLit).run with
  | .ok (some true) => pure ()
  | _ => throwError s!"{"{0,1,2,3} = {0,1,2,3}"} must remain true in Sets"

/-! ## #53 §11: cardinality of `(ℤ/2)⁴` as an `𝔽₂`-module

The receiver is a point of `Mod_{ℤ/2}`; the resolved method is the one
cardinality functor on `Core(Sets)`, reached along the module fibration's
fibre inclusion and underlying-set functor, with no module-specific
cardinality anywhere. The value is computed by the composed Lean-native
actions. `ℤ/16` also has 16 elements, but it is not an `𝔽₂`-module: its
ascription to `Mod(ℤ/2)` is refused, not reinterpreted. -/

let L := (ZZ/2)^4 in Mod(ZZ/2)

#explain_route L.cardinality()

run_cmd do
  let env ← getEnv
  match ← runEval env (.method (.ref `L) `cardinality #[]) with
  | .ok d =>
      unless d.render == "16" do
        throwError s!"L.cardinality() evaluated to {d.render}, expected 16"
  | .error e => throwError s!"L.cardinality() failed: {e.render}"
  if Semantic.realizes "cat.modules_r" (some (.mod 2)) (.domainObj (.mod 16)) then
    throwError "ℤ/16 was realized as an 𝔽₂-module"

/-! ### The same composite, realized by Sage

A fused Sage route is registered for exactly this composite (`card ∘ U ∘ ι_R`, keyed by
`meth.cardinality` and the two route steps) and runs on the module itself. Selecting the Sage
realization runs it: the answer is 16 where Sage is installed; where it is not, the failure is the
selected backend's absence — never a silent fall back to the Lean composite. -/

run_cmd do
  let env ← getEnv
  let ctx : EvalCtx := { env, realization? := some `sage, notes := ← IO.mkRef #[],
                         annotations := ← IO.mkRef #[] }
  match ← (eval ctx (.method (.ref `L) `cardinality #[])).run with
  | .ok d =>
      unless d.render == "16" do
        throwError s!"the Sage realization of L.cardinality() gave {d.render}, expected 16"
  | .error (.exec (.backendUnavailable b _)) =>
      unless b == `sage do throwError s!"the Sage realization ran on {b}"
  | .error e => throwError s!"the Sage realization of L.cardinality() failed: {e.render}"

-- a fused route must realize a registered composite: one claiming a route that does not reach
-- the method's owner is refused at registration
run_cmd do
  let bogus : CasDsl.Route := CasDsl.Route.mk `cardinality (.domainIs .anyMod) `sage "module_cardinality" 0 ""
    "" (some ("meth.cardinality", #["fun.sets.whole_subset"]))
  let refused ← try checkFusedRoute bogus; pure false catch _ => pure true
  unless refused do throwError "a fused route realizing no registered composite was accepted"

end CasDslTests.Transport
