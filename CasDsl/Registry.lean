/-
The persistent registries: ALL semantic state of the DSL.

Every registry here is a `SimplePersistentEnvExtension`, so registrations
live in the `Lean.Environment` and inherit cell atomicity, rollback,
restart replay and the olean session cache from the plugin state law
(lean-jupyter-kernel `docs/plugins.md`). No semantic state may live in an
`IO.Ref`; the executor code table in `Route.lean` is the one exemption and
it holds no semantics.

Duplicate registration is a developer error, never a silent overwrite: the
`…Checked` adders are what the prelude uses.
-/
import Lean
import CasDsl.Category

namespace CasDsl

open Lean

/-- A notebook binding: the name a `let` introduced and the object it
denotes. Rebinding a name is legal notebook behaviour, so this registry has
no checked adder; lookup takes the latest entry. -/
abbrev Binding := Name × Obj

/-- A registered representative presentation: a label and a concrete object
that `#capability_gaps` crosses with the declared methods. -/
abbrev Representative := String × Obj

initialize categoryExt :
    SimplePersistentEnvExtension CatDecl (Array CatDecl) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := Array.push
    addImportedFn := fun arrs => arrs.flatten
  }

initialize methodExt :
    SimplePersistentEnvExtension MethodDecl (Array MethodDecl) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := Array.push
    addImportedFn := fun arrs => arrs.flatten
  }

initialize routeExt :
    SimplePersistentEnvExtension Route (Array Route) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := Array.push
    addImportedFn := fun arrs => arrs.flatten
  }

initialize functorExt :
    SimplePersistentEnvExtension FunctorDecl (Array FunctorDecl) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := Array.push
    addImportedFn := fun arrs => arrs.flatten
  }

initialize profileRuleExt :
    SimplePersistentEnvExtension ProfileRule (Array ProfileRule) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := Array.push
    addImportedFn := fun arrs => arrs.flatten
  }

initialize canonicalMapExt :
    SimplePersistentEnvExtension CanonicalMap (Array CanonicalMap) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := Array.push
    addImportedFn := fun arrs => arrs.flatten
  }

initialize bindingExt :
    SimplePersistentEnvExtension Binding (Array Binding) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := Array.push
    addImportedFn := fun arrs => arrs.flatten
  }

initialize representativeExt :
    SimplePersistentEnvExtension Representative (Array Representative) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := Array.push
    addImportedFn := fun arrs => arrs.flatten
  }

/-! ## Accessors -/

def categories (env : Environment) : Array CatDecl := categoryExt.getState env

def methods (env : Environment) : Array MethodDecl := methodExt.getState env

def routes (env : Environment) : Array Route := routeExt.getState env

def functors (env : Environment) : Array FunctorDecl := functorExt.getState env

def profileRules (env : Environment) : Array ProfileRule := profileRuleExt.getState env

/-- The registered preferred canonical maps — everything the surface may insert
as a coercion. An empty registry means the surface performs no coercion at
all except the engine-level cases documented in `Eval.coerceValue`. -/
def canonicalMaps (env : Environment) : Array CanonicalMap := canonicalMapExt.getState env

def bindings (env : Environment) : Array Binding := bindingExt.getState env

def representatives (env : Environment) : Array Representative :=
  representativeExt.getState env

/-! ## Adders -/

def addCategory (env : Environment) (d : CatDecl) : Environment :=
  categoryExt.addEntry env d

def addMethod (env : Environment) (d : MethodDecl) : Environment :=
  methodExt.addEntry env d

def addRoute (env : Environment) (r : Route) : Environment :=
  routeExt.addEntry env r

def addFunctor (env : Environment) (f : FunctorDecl) : Environment :=
  functorExt.addEntry env f

def addProfileRule (env : Environment) (r : ProfileRule) : Environment :=
  profileRuleExt.addEntry env r

def addCanonicalMap (env : Environment) (r : CanonicalMap) : Environment :=
  canonicalMapExt.addEntry env r

def addBinding (env : Environment) (b : Binding) : Environment :=
  bindingExt.addEntry env b

def addRepresentative (env : Environment) (r : Representative) : Environment :=
  representativeExt.addEntry env r

/-! ## Lookups -/

def catDecl? (env : Environment) (n : Name) : Option CatDecl :=
  (categories env).find? (·.name == n)

/-- The registered functor of that name — how a diagnostic recovers the
`source → target` of a transport step recorded in a `Resolution`. -/
def functorDecl? (env : Environment) (n : Name) : Option FunctorDecl :=
  (functors env).find? (·.name == n)

/-- Every declaration of `id`. The same method identity is declared on
several receiver categories in general (that is what makes specificity
resolution necessary), so this is an array, never an `Option`. -/
def methodDecls (env : Environment) (id : Name) : Array MethodDecl :=
  (methods env).filter (·.id == id)

/-- The latest binding of `n`; rebinding shadows. -/
def binding? (env : Environment) (n : Name) : Option Obj :=
  (bindings env).findSomeRev? fun (n', o) => if n' == n then some o else none

def routesFor (env : Environment) (method : Name) : Array Route :=
  (routes env).filter (·.method == method)

/-! ## Checked registration

Used by the prelude and by user-facing registration commands: a clash is
reported, never resolved by overwriting or by keeping both. -/

def addCategoryChecked (env : Environment) (d : CatDecl) : Except String Environment :=
  if (catDecl? env d.name).isSome then
    .error s!"category '{d.name}' is already registered"
  else
    .ok (addCategory env d)

def addMethodChecked (env : Environment) (d : MethodDecl) : Except String Environment :=
  if (methods env).any (fun m => m.id == d.id && m.receiver == d.receiver) then
    .error s!"method '{d.id}' is already declared on category '{d.receiver}'"
  else
    .ok (addMethod env d)

def addRouteChecked (env : Environment) (r : Route) : Except String Environment :=
  if (routes env).any
      (fun r' => r'.method == r.method && r'.pattern == r.pattern &&
                 r'.backend == r.backend && r'.opId == r.opId) then
    .error s!"route for '{r.method}' via backend '{r.backend}' op '{r.opId}' \
is already registered for this pattern"
  else
    .ok (addRoute env r)

/-- Functors are keyed by name: it is what a `Resolution` records and what a
diagnostic resolves back to a `source → target`, so two functors may not
share one. -/
def addFunctorChecked (env : Environment) (f : FunctorDecl) : Except String Environment :=
  if (functorDecl? env f.name).isSome then
    .error s!"functor '{f.name}' is already registered"
  else
    .ok (addFunctor env f)

def addProfileRuleChecked (env : Environment) (r : ProfileRule)
    : Except String Environment :=
  if (profileRules env).any (· == r) then
    .error s!"profile rule assigning category '{r.cat}' to this pattern is \
already registered"
  else
    .ok (addProfileRule env r)

/-- Embeddings are keyed by the PAIR of patterns: two rules accepting the
same `(source, target)` pair would make a coercion ambiguous, and the
coercion layer refuses to pick between them (it reports both). Catching the
clash at registration is what keeps that from ever being observed. -/
def addCanonicalMapChecked (env : Environment) (r : CanonicalMap)
    : Except String Environment :=
  if (canonicalMaps env).any (fun r' => r'.src == r.src && r'.tgt == r.tgt) then
    .error s!"a preferred canonical map of {repr r.src} into {repr r.tgt} is \
already registered"
  else
    .ok (addCanonicalMap env r)

/-- Representative presentations are keyed by their label so an audit lists
each fixture once. -/
def addRepresentativeChecked (env : Environment) (r : Representative)
    : Except String Environment :=
  if (representatives env).any (·.1 == r.1) then
    .error s!"representative presentation '{r.1}' is already registered"
  else
    .ok (addRepresentative env r)

end CasDsl
