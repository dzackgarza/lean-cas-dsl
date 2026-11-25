module

public import CasContract.Port

public section

namespace CasRuntime

open Lean CasCatalogue.Backend

inductive ScopedReference
  | scope (slot : Nat)
  | input (path : Array InputPathStep)
  | result (index : Nat)
  deriving BEq, Repr

def ScopedReference.encode : ScopedReference → Json
  | .scope slot => Json.mkObj [("ctor", .str "scopeRef"), ("args", .arr #[toJson slot])]
  | .input path => inputRef path
  | .result index => resultRef index

/-- The existing released reference grammar, independent of live request authority.
Parsing supplies no binding; RequestScope resolves the original position separately. -/
def ScopedReference.parse? (json : Json) : Except String (Option ScopedReference) := do
  if (json.getObjValAs? String "ctor").toOption == some "scopeRef" then
    checkServiceFields #["ctor", "args"] json
    let #[slot] ← (← json.getObjVal? "args").getArr?
      | throw "a scope reference requires exactly one slot"
    return some (.scope (← slot.getNat?))
  if let some path ← inputRefPath? json then return some (.input path)
  if let some index ← resultRefIndex? json then return some (.result index)
  return none

end CasRuntime

