module

public import Std.Async.Timer

public section

namespace CasRuntime

/-- Wait for an existing task under a native event-loop timer, then release the timer.
The task itself continues on expiry. Its owner decides cancellation and resource cleanup.
Reference: Lean v4.33.0 Std/Async/Timer.lean (Sleep) and Init/System/IO.lean (waitAny). -/
def awaitBefore (task : Task α) (timeoutMs : UInt32) : IO (Option α) := do
  if timeoutMs == 0 then return none
  let sleeper ← (Std.Async.Sleep.mk (.ofNat timeoutMs.toNat)).block
  let deadline ← sleeper.wait.toIO
  let completed : Task (Except IO.Error (Option α)) := task.map fun value => .ok (some value)
  try
    IO.ofExcept (← IO.waitAny [completed,
      Task.map (x := deadline) (fun result => result.map fun _ => none)])
  finally sleeper.stop

end CasRuntime
