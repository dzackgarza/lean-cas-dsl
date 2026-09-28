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

/-! ## Typings and realizations that the acceptance notebook depends on -/

run_cmd do
  let env ← getEnv
  -- a matrix is constructed as a point of square matrices over commutative rings
  match typeOf env mat2Q with
  | .ok t =>
      unless t.category == "cat.matrix_points" do
        throwError s!"Mat₂(ℚ) is typed in {t.category}"
  | .error e => throwError e
  -- `{0, 2, 4, ...}` is enumerated in its presented order, natively
  expectRealized env (.setObj (.arithProg .int (.int 0) (.int 2) none)) `nth (some `native)
  -- ℤ used as an object enumerates by the registered convention
  expectRealized env (.domainObj .int) `nth (some `native)
  -- the ℚ[x] element the notebook obtains by `map p to ℚ[x]` factors
  expectRealized env polyQ `factor (some `sage)
  expectRealized env mat2Q `det (some `sage)
  expectRealized env mat2Q `inverse (some `sage)

/-! ## Re-registration is an error, never a silent overwrite -/

private def factorDecl : MethodDecl := { id := `factor }

run_cmd do
  let env ← getEnv
  -- (positional constructors: the imported grammar owns `{ … }`)
  if (addTypingRuleChecked env (TypingRule.mk (.elemOf (.exact .int)) "cat.ring_points" none
      #[] "")).toOption.isSome then
    throwError "re-registering an imported typing rule was not detected as a clash"
  if (addMethodChecked env factorDecl).toOption.isSome then
    throwError "re-declaring an imported method was not detected as a clash"

end CasDslTests.Std
