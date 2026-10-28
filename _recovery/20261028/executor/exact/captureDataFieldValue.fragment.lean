/-- Reinterpret only a checked public data projection as an ordinary typed
value. Its original complete object or map remains a typed child; no historical
capture, category context, or endpoint receipt is copied to the different role. -/
def captureDataFieldValue (h : Harness) (original : Wire) (formal expected : Expr) :
    TermElabM Wire := do
  let result ← retainedRecordInterface original
  if let .value _ := result then return ← forwardRetainedValue original formal
  let template := ActionDataTemplate.project #[] (.wire result.role original)
  let (data, dependencies) ← renderCapturedActionData template
  let wire : Wire := {
    form := original.form
    payload := (← if original.completedData then scopedPayload formal data
      else combinedRecipePayload formal data dependencies)
    serviceHandles := (← retainServiceOperands h dependencies) }
  retainIntrinsicResultAssembly wire (.value expected) template
