import CasDsl

/-!
An externally CONTRIBUTED `casTerm` production — grammar plus translator
registered from outside `CasDsl/Syntax.lean`. This file is the proof that
the surface is open where the translator table says it is: a module adds a
spelling without an edit to `toExprCore`, and the spelling parses,
translates, recurses into the core grammar for its child, and evaluates.
`tripleof x` is `3 · x`.
-/

namespace CasDslTests.Extension

open Lean CasDsl

syntax (name := casTestTriple) "tripleof" casTerm : casTerm

#eval show IO Unit from
  registerTermTranslator ``casTestTriple fun rec stx => do
    return .bin .mul (.num 3) (← rec stx[1])

-- a second registration for the same kind is refused, not shadowed
#eval show IO Unit from do
  let refused ← try
    registerTermTranslator ``casTestTriple fun _ _ => Except.error "shadow"
    pure false
  catch _ => pure true
  unless refused do
    throw <| IO.userError
      "a duplicate casTerm translator registration was not refused"

let tripled := tripleof (2 + 3)

open Elab Command in
run_cmd do
  let some o := (bindings (← getEnv)).findSome? fun (n, o) =>
      if n == `tripled then some o else none
    | throwError "the contributed production did not bind"
  unless o == Obj.elem .int (.int 15) do
    throwError s!"tripleof (2 + 3) evaluated to {o.presentation}, not 15"

end CasDslTests.Extension
