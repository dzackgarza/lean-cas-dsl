module

public import CasRuntime.PreparedRequest
public import CasRuntime.InputRoute

public section

namespace CasRuntime

open Lean Meta CasCompiler







opaque PreparedRequest.fixedInputFor (request : PreparedRequest) (graph : ValueGraph)
    (source : SourceLayout)
    (resolve : Option (FixedInput → MetaM (ValueGraph × ValueBinding)) := none) :
    MetaM (Option FixedInput) := do
  let _ := resolve
  let some original := request.origin.application | return none
  original.fixedInputAt graph (← request.source.projectionPathTo source)

end CasRuntime
