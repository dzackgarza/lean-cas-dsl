/-
Elaboration-time tests for round two of the resolver: receiver transport
along registered functors (`CasDsl/Resolve.lean`).

The first half is `#guard` over the pure core with fixture registrations, so
every claim about *when* transport happens is checked without an
`Environment`. What has to be pinned down there is not that transport works —
it is that it happens in exactly one situation and never competes with round
one: a direct or inherited declaration wins untransported, two applicable
functors are an ambiguity rather than a pick, a functor whose source the
receiver does not reach is not applied, and a receiver whose transported image
still cannot resolve the method keeps its ORIGINAL `notApplicable` error.

The second half runs against the real standard universe and the real native
executor: `cardinality` on the ℤ/4 module fixture must resolve through the
forgetful functor, route against the IMAGE, and come back as the cardinal 4.
-/
import CasDsl

namespace CasDslTests.Transport

open Lean (Name)
open CasDsl

/-! ## Fixture registrations (plain data — no `Environment` needed) -/

private def cats : Array CatDecl := #[
  { name := `Sets },
  { name := `CountableSets, parents := #[`Sets] },
  { name := `FiniteSets, parents := #[`CountableSets] },
  { name := `Modules },
  { name := `SmallModules, parents := #[`Modules] },
  { name := `Rings }
]

private def rules : Array ProfileRule := #[
  { pattern := .cyclicMod, cat := `SmallModules, slots := #[.const (.dom .int)] },
  { pattern := .finiteSet, cat := `FiniteSets, slots := #[.setDom] }
]

/-- `size` is declared on BOTH sides of the transport step: on `Sets` (where a
transported receiver would find it) and on `Modules` (where the receiver finds
it directly). That overlap is what makes "round one wins" testable. -/
private def decls : Array MethodDecl := #[
  { id := `cardinality, receiver := `Sets },
  { id := `annihilator, receiver := `Modules },
  { id := `size, receiver := `Sets },
  { id := `size, receiver := `Modules },
  { id := `factor, receiver := `Rings }
]

private def forget : FunctorDecl :=
  { name := `forget, source := `Modules, target := `Sets, objMap := .cyclicToFiniteSet }

/-- A second forgetful functor with the same source and target: two ways to
read the same receiver as a set. -/
private def forget2 : FunctorDecl := { forget with name := `forget2 }

/-- A DEFECTIVE registration: its object map lands in the set hierarchy, but it
declares `Rings` as its target. -/
private def mislabeled : FunctorDecl :=
  { name := `mislabeled, source := `Modules, target := `Rings,
    objMap := .cyclicToFiniteSet }

/-- Its object map applies to the module fixture, but its source is a category
the fixture does not inhabit — so it must not be used. -/
private def fromRings : FunctorDecl :=
  { name := `fromRings, source := `Rings, target := `Sets,
    objMap := .cyclicToFiniteSet }

private def modFixture : Obj := .cyclicModule 4

/-- The underlying set of ℤ/4, written out: what `cyclicToFiniteSet` must
produce, spelled independently of the code that produces it. -/
private def modUnderlying : Obj :=
  .setObj (.finite (.mod 4) #[.mod 4 0, .mod 4 1, .mod 4 2, .mod 4 3])

/-! ## The object map is data, and is defined exactly where it is honest -/

#guard ObjMap.cyclicToFiniteSet.apply modFixture == some modUnderlying
-- ℤ/0 ≅ ℤ: not a finite set, so the map is undefined rather than the empty set
#guard ObjMap.cyclicToFiniteSet.apply (.cyclicModule 0) == none
#guard ObjMap.cyclicToFiniteSet.apply modUnderlying == none
#guard ObjMap.cyclicToFiniteSet.apply (.domainObj (.mod 4)) == none

/-! ## `concreteReceiver`: what the router and the executor must see -/

private def direct : Resolution :=
  { decl := { id := `annihilator, receiver := `Modules }, profileEntry := ⟨`Modules, #[]⟩,
    via := [] }

#guard direct.concreteReceiver modFixture == modFixture
#guard { direct with viaFunctor := some ⟨`forget, modUnderlying⟩ }.concreteReceiver
    modFixture == modUnderlying

/-! ## When transport happens -/

private def resolve (fs : Array FunctorDecl) (o : Obj) (m : Name)
    : Except ResolveError Resolution :=
  resolveCoreWithTransport cats decls rules fs o m

private def tag : Except ResolveError Resolution → String
  | .ok _ => "ok"
  | .error (.notApplicable ..) => "notApplicable"
  | .error (.ambiguous ..) => "ambiguous"
  | .error (.unknownMethod _) => "unknownMethod"
  | .error (.functorTargetMismatch ..) => "functorTargetMismatch"

/-- Receiver category, inheritance chain, and the transport step (as the
functor's name and the image it produced). -/
private def resolved (r : Except ResolveError Resolution)
    : Option (Name × List Name × CatRef × Option (Name × Obj)) :=
  r.toOption.map fun res =>
    (res.decl.receiver, res.via, res.profileEntry,
      res.viaFunctor.map fun s => (s.functor, s.image))

-- THE transported resolution: `cardinality` is declared on `Sets`, which the
-- module fixture does not inhabit; the functor carries the RECEIVER there, and
-- the resolution records both the image and the chain inside the image's
-- profile
#guard resolved (resolve #[forget] modFixture `cardinality) ==
  some (`Sets, [`CountableSets, `Sets], ⟨`FiniteSets, #[.dom (.mod 4)]⟩,
    some (`forget, modUnderlying))

-- ROUND ONE WINS UNCONDITIONALLY: `size` is declared on `Modules` *and* on
-- `Sets`, and `forget` applies — the direct declaration resolves untransported,
-- and the two rounds never compete (a resolver that merged them would report
-- an ambiguity here, one that preferred transport would answer `Sets`)
#guard resolved (resolve #[forget] modFixture `size) ==
  some (`Modules, [`Modules], ⟨`SmallModules, #[.dom .int]⟩, none)

-- the same declaration is still reached directly when NO functor is registered
#guard resolved (resolve #[] modFixture `size) == resolved (resolve #[forget] modFixture `size)

-- a functor whose source the receiver does not reach is not applied, even
-- though its object map is defined on this presentation
#guard tag (resolve #[fromRings] modFixture `cardinality) == "notApplicable"

-- a functor whose object map is undefined on the presentation is not applied
-- (`forget`'s source is reachable from the image's own profile, but a set has
-- no underlying-set image registered)
#guard tag (resolve #[forget] modUnderlying `annihilator) == "notApplicable"

-- with no functors registered at all, nothing changes for round one
#guard tag (resolve #[] modFixture `cardinality) == "notApplicable"

/-! ## Competing functors are an ambiguity, never a pick -/

#guard tag (resolve #[forget, forget2] modFixture `cardinality) == "ambiguous"

private def candidateFunctors : Except ResolveError Resolution → Array (Option Name)
  | .error (.ambiguous _ cs) => cs.map fun c => c.viaFunctor.map (·.functor)
  | _ => #[]

-- both candidates are carried, each naming the functor that produced it: the
-- report is what lets a developer unregister one
#guard candidateFunctors (resolve #[forget, forget2] modFixture `cardinality) ==
  #[some `forget, some `forget2]

/-! ## Zero transported candidates: the original error, unchanged

`factor` is declared on `Rings`, which neither the module nor its underlying
set reaches. The reported profile must stay the RECEIVER's — reporting the
image's profile would blame the wrong object, and continuing to search would
be the functor-composition this slice does not implement. -/

private def notApplicableAt : Except ResolveError Resolution → Option (Array CatRef × Array Name)
  | .error (.notApplicable _ profile declaredOn) => some (profile, declaredOn)
  | _ => none

#guard notApplicableAt (resolve #[forget] modFixture `factor) ==
  some (#[⟨`SmallModules, #[.dom .int]⟩], #[`Rings])
-- byte for byte the error round one produced on its own
#guard notApplicableAt (resolve #[forget] modFixture `factor) ==
  notApplicableAt (resolve #[] modFixture `factor)

/-! ## A defective functor registration is loud, and stops resolution

CEILING (one hop, and nothing past a defect): `transportCandidates` resolves
the image with round one only. There is no second hop to test with the shipped
object map — every image is a set presentation, and no registered object map
is defined on one — so what is asserted here is the other half of the same
discipline: the resolver never works *around* a candidate it cannot trust. -/

private def mismatchAt : Except ResolveError Resolution → Option (Name × Name × Array CatRef)
  | .error (.functorTargetMismatch f t prof) => some (f, t, prof)
  | _ => none

#guard mismatchAt (resolve #[mislabeled] modFixture `cardinality) ==
  some (`mislabeled, `Rings, #[⟨`FiniteSets, #[.dom (.mod 4)]⟩])

-- and a working functor alongside it does NOT paper over the defect
#guard tag (resolve #[mislabeled, forget] modFixture `cardinality) == "functorTargetMismatch"
#guard tag (resolve #[forget, mislabeled] modFixture `cardinality) == "functorTargetMismatch"

/-! ## The transport step is visible in the structured gap

A transported resolution with no route must report the functor: without it the
gap would claim a set-shaped presentation for a module and leave no trace of
how the two are related. -/

private def contains (hay needle : String) : Bool := (hay.splitOn needle).length > 1

private def transportedGap : CapabilityGap := {
  method := `nth
  receiverCategory := ⟨`FiniteSets, #[.dom (.mod 4)]⟩
  presentation := modUnderlying.presentation
  semanticVia := [`CountableSets]
  viaFunctor := some ⟨`UnderlyingSet, modUnderlying⟩
  routesConsidered := #[]
}

#guard contains (renderGap transportedGap) "NoImplementation"
#guard contains (renderGap transportedGap) "UnderlyingSet"
#guard contains (renderSemanticPath transportedGap.receiverCategory
  transportedGap.semanticVia transportedGap.viaFunctor) "transported by functor"
-- an untransported gap says nothing about functors
#guard !contains (renderGap { transportedGap with viaFunctor := none }) "transported"

/-! ## The real universe, the real route, the real executor -/

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let o : Obj := .cyclicModule 4
  let res ← match resolveMethod env o `cardinality with
    | .ok res => pure res
    | .error e =>
        throwError s!"cardinality must reach {o.presentation} by transport: {repr e}"
  let some step := res.viaFunctor
    | throwError s!"cardinality resolved on {o.presentation} without transport"
  unless step.functor == `UnderlyingSet do
    throwError s!"cardinality was transported by '{step.functor}', expected 'UnderlyingSet'"
  unless step.image == modUnderlying do
    throwError s!"UnderlyingSet(ℤ/4) is {step.image.presentation}, expected \
{modUnderlying.presentation}"
  -- the router must see the IMAGE: routing the untransported module finds
  -- nothing, which is exactly why every caller goes through `concreteReceiver`
  match routeFor env res o with
  | .gap _ => pure ()
  | _ => throwError "a set route matched the untransported module receiver"
  let route ← match routeFor env res (res.concreteReceiver o) with
    | .chosen r => pure r
    | .gap _ => throwError "the transported cardinality call has no route"
    | .ambiguousRoutes rs => throwError s!"{rs.size} routes tied for transported cardinality"
  unless route.backend == `native && route.opId == "cardinality" do
    throwError s!"transported cardinality routed to {route.backend}:{route.opId}"
  -- and it computes: |ℤ/4| = 4, through the registered executor
  match ← execute route (res.concreteReceiver o) #[] with
  | .ok v =>
      unless v == .cardinal (.finite 4) do
        throwError s!"the cardinality of ℤ/4 came back as {v.render}, expected 4"
  | .error e => throwError s!"executing transported cardinality failed: {repr e}"

/-! ## A transported resolution with no route is a gap that names the functor

The shipped universe routes every set method that reaches the module fixture,
so the transported GAP path needs a method with no route to be observable. The
declaration below is added to a local copy of the environment — it is
registration data, never committed, so the standard universe is unchanged. -/

open Lean Elab Command in
run_cmd do
  let env := addMethod (← getEnv)
    { id := `casdslTransportProbe, receiver := `Sets,
      doc := "a set method with no registered route (test fixture)" }
  let o : Obj := .cyclicModule 4
  let res ← match resolveMethod env o `casdslTransportProbe with
    | .ok res => pure res
    | .error e => throwError s!"the probe method did not transport: {repr e}"
  match routeFor env res (res.concreteReceiver o) with
  | .gap g =>
      unless (g.viaFunctor.map (·.functor)) == some `UnderlyingSet do
        throwError "the gap of a transported resolution did not record the functor"
      unless g.presentation == modUnderlying.presentation do
        throwError s!"the gap reports the presentation {g.presentation}, expected the \
transported receiver {modUnderlying.presentation}"
      -- the rendered chain must explain how a module came to be routed as a set
      unless contains (renderGap g) "UnderlyingSet" do
        throwError s!"the rendered gap hides the transport step:\n{renderGap g}"
  | .chosen r => throwError s!"a method with no route routed to {r.backend}:{r.opId}"
  | .ambiguousRoutes _ => throwError "a method with no route reported tied routes"

/-! ## The surface path: binding, method call, and the diagnostic

`callMethod` is the only remaining place the transported receiver could be
dropped, so the value is asserted through the evaluator as well. -/

let F := ℤ/4 in SmallModules(ℤ)

#explain_route F.cardinality()

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  match ← runEval env (.method (.ref `F) `cardinality #[]) with
  | .ok d =>
      unless d.render == "4" do
        throwError s!"F.cardinality() evaluated to {d.render}, expected 4"
  | .error e => throwError s!"F.cardinality() failed: {e.render}"

-- `contains` transports too, and the ARGUMENT is not transported: it is read
-- against the method's declaration, so `2` names the residue class 2 of the
-- underlying set while `1/2` is simply not an element of it
open Lean Elab Command in
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

`U(F) = {0, 1, 2, 3}` in Sets — but `F` itself is a module, there is no
unique module structure on that set, and bare `=` never inserts a functor:
equality of objects in different categories is TRIVIALLY FALSE. The Sets
question remains available as the explicit method call, whose receiver
transports like any other. A resolver change that let bare `=` transport
would flip the first two assertions; dropping transport would break the
third. -/

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let ctx : EvalCtx := { env, notes := ← IO.mkRef #[] }
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
  -- the explicit Sets question, receiver transported: U(F) = {0,1,2,3}
  match ← runEval env (.method (.ref `F) `set_eq #[setLit]) with
  | .ok d =>
      unless d.render == "true" do
        throwError s!"F.set_eq({"{0,1,2,3}"}) evaluated to {d.render}, expected true"
  | .error e => throwError s!"F.set_eq({"{0,1,2,3}"}) failed: {e.render}"
  -- and two sets still compare as sets, untransported
  match ← (evalAssert ctx .eq setLit setLit).run with
  | .ok (some true) => pure ()
  | _ => throwError s!"{"{0,1,2,3} = {0,1,2,3}"} must remain true in Sets"

end CasDslTests.Transport
