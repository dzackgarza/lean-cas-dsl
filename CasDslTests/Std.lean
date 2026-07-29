/-
Elaboration-time tests for the standard universe, run against the IMPORTED
registry state.

That is the point of this module: `CasDsl/Std.lean` proves its claims while
its own registrations are still being elaborated, whereas everything here
sees the registries as they arrive through `addImportedFn` — i.e. after the
olean round trip that the kernel's session cache and restart replay depend
on. A registration that did not survive serialization fails the build here.
-/
import CasDsl.Std

namespace CasDslTests.Std

open Lean Elab Command
open CasDsl
open CasDsl.Std

/-! ## The six claims of the standard universe, re-asserted after import -/

run_cmd acceptanceProofs (← getEnv)

/-! ## Profiles and routes that the acceptance notebook depends on -/

run_cmd do
  let env ← getEnv
  -- matrix elements carry their instantiation data: size and entry domain
  unless profileOf env mat2Q == #[⟨`MatrixElems, #[.nat 2, .dom .rat]⟩] do
    throwError s!"Mat₂(ℚ) profile is {repr (profileOf env mat2Q)}"
  -- `{0, 2, 4, ...}` is countable and enumerable natively
  expectRouted env (.setObj (.arithProg .int (.int 0) (.int 2) none)) `nth [] `native
  -- ℤ used as an object enumerates by the registered convention
  expectRouted env (.domainObj .int) `nth [] `native
  -- the ℚ[x] element the notebook obtains by `map p to ℚ[x]` factors
  expectRouted env polyQ `factor [`FactorizationElems] `sage
  expectRouted env mat2Q `det [] `sage
  expectRouted env mat2Q `inverse [] `sage

/-! ## Re-registration is an error, never a silent overwrite -/

run_cmd do
  let env ← getEnv
  if (addCategoryChecked env { name := `Sets }).toOption.isSome then
    throwError "re-registering an imported category was not detected as a clash"
  if (addMethodChecked env { id := `factor, receiver := `FactorizationElems }).toOption.isSome then
    throwError "re-declaring an imported method was not detected as a clash"

end CasDslTests.Std
