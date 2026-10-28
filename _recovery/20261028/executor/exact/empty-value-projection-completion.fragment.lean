  -- A checked data-only view changes the complete result role while keeping
  -- precisely its original child's representation. Once that child is actual,
  -- the pure projection is actual too; no mathematical operation is executed.
  if let .value _ := assembly.result then
    if let .project path (.wire _ original) := actionTemplateExecution template then
      if path.isEmpty && original.completedData then
        result := { result with payload := (← scopedPayload wire.value data) }
