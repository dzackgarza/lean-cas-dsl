structure EndpointProjectionData where
  data : DataOwnership.Data
  origin : EndpointDataOrigin
  /-- A direct codec projection retains its exact position in the original
  packet. Derived action data, formal recovery and endpoint references have no
  such position; matching their bytes cannot create one. -/
  position : Option DataOwnership.Path := none
