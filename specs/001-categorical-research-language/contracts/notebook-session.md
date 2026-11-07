# Native notebook and CAS session contract

Feature context: `001-categorical-research-language`.

Current canonical content:

1. [Base planned notebook contract](https://github.com/dzackgarza/lean-cas-dsl/issues/69#issuecomment-6664296914).
2. [Runtime/model amendment: staged/committed visibility, commit status and captured continuations](https://github.com/dzackgarza/lean-cas-dsl/issues/69#issuecomment-6684996781).
3. [Full-audit amendment: one admission per transport ID and a separate duplicate-request protocol diagnostic](https://github.com/dzackgarza/lean-cas-dsl/issues/69#issuecomment-6706802517).
4. [Amended implementation and lifecycle assignments](https://github.com/dzackgarza/lean-cas-dsl/issues/10#issuecomment-6685591815), with item 3's existing task refinements.
5. [Validation-guide alignment](https://github.com/dzackgarza/lean-cas-dsl/issues/24#issuecomment-6706903869).
6. [Repeated full-audit amendment: data-only observation without extensible printer callbacks and demand-specific liveness](https://github.com/dzackgarza/lean-cas-dsl/issues/69#issuecomment-6707359041).
7. [Observation/liveness validation alignment](https://github.com/dzackgarza/lean-cas-dsl/issues/24#issuecomment-6707377395).

Read the full texts together. Item 3 replaces the base's optional duplicate-transport join policy; internal consumers still share one actual pending CAS occurrence. Its provider capture capability is separate from the notebook's unchanged eight-feature handshake. No duplicate diagnostic may settle the original execution response or trigger replay. Item 6 replaces the proposed effectful `Query.inspect` reuse path and clarifies retained-field access; it does not relax the existing inert-query promise.

Inert inspection, checks before source transmission, atomic publication, cancellation, snapshot identity, actual owner lifetime and no-replay requirements remain binding. These documents establish no production notebook acceptance. This is a durable navigation pointer.
