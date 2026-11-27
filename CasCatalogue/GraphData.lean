module

public import Lean.Data.Json.Basic

public section

namespace CasCatalogue.GraphData

/-- Framing of a supplied computational inventory; no formal carrier is enumerated. -/
def validateInventory [BEq α] (values : Array α) : Except String Unit := do
  let mut seen := #[]
  for value in values do
    if seen.contains value then throw "a callable inventory repeats a domain point"
    seen := seen.push value

/-- Complete finite-graph framing shared by the legacy public codec and prepared runtime.
Callers supply the comparison data only after selecting their actual input references. -/
def validateDomain [BEq α] (domain : Array α) (pairs : Array (α × α)) :
    Except String Unit := do
  validateInventory domain
  unless pairs.size == domain.size do
    throw "the computational graph is not total at its declared data endpoint"
  let mut seen := #[]
  for (input, _) in pairs do
    if seen.contains input then throw "the computational graph repeats a domain key"
    unless domain.contains input do
      throw "the computational graph uses a key outside its declared data endpoint"
    seen := seen.push input

def validateEndpoints [BEq α] (domain : Array α) (target : Option (Array α))
    (pairs : Array (α × α)) : Except String Unit := do
  validateDomain domain pairs
  if let some target := target then
    validateInventory target
    for (_, output) in pairs do
      unless target.contains output do
        throw "the computational graph value is outside its declared data codomain"

/-- The released pair-array framing, with no point decoding or mathematical application. -/
def pairs (value : Lean.Json) : Except String (Array (Lean.Json × Lean.Json)) := do
  (← value.getArr?).mapM fun pair => do
    let #[input, output] ← pair.getArr?
      | throw "a computational graph entry requires input and output"
    return (input, output)

end CasCatalogue.GraphData
