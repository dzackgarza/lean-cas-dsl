module

public import CasCompiler.CategoricalPointFamily

public section

namespace CasCompiler

open Lean Meta

/-- Read a function's independently stated domain and, when nondependent, its target.
The domain remains available when the result depends on the argument. Only the native
type is inspected; no function body or finite carrier is evaluated. -/
opaque nativeFunctionEndpointTypes (type : Expr) : MetaM (Expr × Option Expr) := do
  let .forallE _ domain range _ ← whnfR type
    | throwError "the native function lost its original dependent function type"
  let source ← declaredEndpoint domain
  let target ← if range.hasLooseBVars then pure none
    else some <$> declaredEndpoint range
  return (source, target)

/-- Read endpoints from the original native Hom or a plain nondependent function type.
The latter is its canonical function interface. No function body is opened or evaluated,
and a dependent function receives no fabricated categorical Hom interpretation. -/
opaque nativeMapEndpoints (arrow : Expr) : MetaM (Expr × Expr) := do
  let original ← inferType arrow
  if original.isAppOfArity ``Quiver.Hom 4 then
    return ← categoricalPointEndpoints arrow
  let type ← whnfR original
  if type.isForall then
    let (source, some target) ← nativeFunctionEndpointTypes type
      | throwError "a dependent native function has no single categorical target endpoint"
    return (source, target)
  categoricalPointEndpoints arrow

end CasCompiler
