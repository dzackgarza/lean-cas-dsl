  | .valueView receiver =>
      discard <| trace.valueOrigin e
      let original ← realizeUnobserved h trace "the retained value view's original producer" receiver
      forwardRetainedValue original e
  | .constructionApexView receiver =>
      let type ← withTransparency .all <| whnf (← inferType receiver)
      let colimit ← if type.isAppOf ``CategoryTheory.Limits.ColimitCocone then pure true
        else if type.isAppOf ``CategoryTheory.Limits.LimitCone then pure false
        else do
          throwStratum .invalid
            "the retained apex has no complete universal presentation as its source"
      let cone ← mkAppM (if colimit then ``CategoryTheory.Limits.ColimitCocone.cocone
        else ``CategoryTheory.Limits.LimitCone.cone) #[receiver]
      let apex ← mkAppM (if colimit then ``CategoryTheory.Limits.Cocone.pt
        else ``CategoryTheory.Limits.Cone.pt) #[cone]
      unless ← withoutModifyingState (withTransparency .all <|
          isDefEq (← inferType apex) (← inferType e) <&&> isDefEq apex e) do
        throwStratum .invalid "the retained apex changed its original universal projection"
      let producer ← trace.valueOrigin receiver
      let original ← realizeUnobserved h trace "the retained apex's complete original construction" producer
      forwardRetainedValue original e
  | .dataFieldView receiver expected fields =>
      let path ← checkedDataFieldView receiver expected e fields
      let original ← realizeUnobserved h trace "the data field's complete original producer" receiver
      let original ← forwardRetainedValue original receiver
      let original ← match ← retainedRecordInterface original with
        | .map context => do
          if !fields.isEmpty then
            let (source, _) ← contextualMorphismEndpoints context original.value
            unless ← callableHasSetsContext context source do
              throwStratum .noImplementation
                "a structured Hom cannot be replaced by its erased carrier function"
            unless (← ComputationalData.declaredCallableType? expected).isSome do
              throwStratum .invalid "the callable data projection lost its complete function type"
          captureCompleteCallable h trace original context
        | _ => capturePublicRecordProjectionAt h original path
      captureDataFieldValue h original e expected
