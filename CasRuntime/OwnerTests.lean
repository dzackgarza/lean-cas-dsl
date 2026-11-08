module

import CasRuntime.Owner
public meta import Lean.Elab.Command
meta import CasRuntime.Owner

open CasRuntime

run_cmd Lean.Elab.Command.liftIO do
  let owners ← OwnerRegistry.new
  let first ← owners.spawn { cmd := "/bin/cat" }
  try
    let second ← owners.spawn { cmd := "/bin/cat" }
    try
      if first.generation == second.generation then
        throw <| IO.userError "separate connections share a generation"
      unless ← owners.allAlive #[first.generation, second.generation] do
        throw <| IO.userError "live child connections are unavailable"
      first.child.stdin.putStr "first\n"
      first.child.stdin.flush
      unless (← first.child.stdout.getLine) == "first\n" do
        throw <| IO.userError "the first generation lost its own channel"
      owners.close first.generation
      if ← owners.isLive first.generation then
        throw <| IO.userError "a closed generation remains available"
      unless ← owners.isLive second.generation do
        throw <| IO.userError "closing one generation invalidated another"
      unless ← owners.allAlive #[] do
        throw <| IO.userError "owner-free data became unavailable"
      second.child.stdin.putStr "second\n"
      second.child.stdin.flush
      unless (← second.child.stdout.getLine) == "second\n" do
        throw <| IO.userError "the surviving generation lost its own channel"
      let third ← owners.spawn { cmd := "/bin/cat" }
      try
        unless third.generation.serial > second.generation.serial do
          throw <| IO.userError "a new connection reused a generation"
      finally owners.close third.generation
    finally owners.close second.generation
  finally owners.close first.generation

run_cmd Lean.Elab.Command.liftIO do
  let owners ← OwnerRegistry.new
  let child ← owners.spawn { cmd := "/usr/bin/true" }
  discard <| IO.ofExcept child.exited.get
  if ← owners.isLive child.generation then
    throw <| IO.userError "a terminated process retains a live generation"
