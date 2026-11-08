module

import CasRuntime.Owner
public meta import Lean.Elab.Command
meta import CasRuntime.Owner

open CasRuntime

run_cmd Lean.Elab.Command.liftIO do
  let owners ← OwnerRegistry.new
  let first ← owners.spawn { cmd := "/bin/cat" }
  try
    let value ← owners.identities.fresh .value
    let occurrence ← owners.identities.fresh .occurrence
    unless first.generation.worker == value.worker && value.worker == occurrence.worker do
      throw <| IO.userError "worker resources have different worker identities"
    unless first.generation.serial < value.serial && value.serial < occurrence.serial do
      throw <| IO.userError "worker identities are not monotone across resource kinds"
    let tasks ← (Array.range 32).mapM fun _ =>
      IO.asTask (owners.identities.fresh .value)
    let values ← tasks.mapM fun task => IO.ofExcept task.get
    let mut seen : Std.HashSet Nat := {}
    for identity in values do
      if seen.contains identity.serial then
        throw <| IO.userError "concurrent allocations reused a worker identity"
      unless identity.worker == occurrence.worker && identity.serial > occurrence.serial do
        throw <| IO.userError "concurrent allocation changed worker or reused an earlier identity"
      seen := seen.insert identity.serial
    let other ← OwnerRegistry.new
    let unrelated ← other.identities.fresh .value
    if unrelated.worker == value.worker then
      throw <| IO.userError "separate workers share an identity supply"
  finally owners.close first.generation
