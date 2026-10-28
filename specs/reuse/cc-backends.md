# Reuse record: `cc-backends`

## Selected implementation path

Reuse the existing **leaf process protocol and Python serving library**. Sage/passagemath and GAP remain opaque engines in leaf packages; the kernel does not import their algorithms, Python categories or native bindings.

| Responsibility | Existing source to import/use | Implementation destination |
| --- | --- | --- |
| Leaf manifest and process protocol | [`CasContract.Registration`](https://github.com/dzackgarza/lean-cas-dsl-leaf-contracts/blob/34bb8abbdbb49699015f63840cf86ed67f438003/CasContract/Registration.lean), [`CasContract.Port`](https://github.com/dzackgarza/lean-cas-dsl-leaf-contracts/blob/34bb8abbdbb49699015f63840cf86ed67f438003/CasContract/Port.lean) in the existing `cas_leaf_contracts` Lake dependency | The kernel's existing admission/dispatch boundary; extend the published contract only for the required complete value interface under #69. Do not restore retired `CasDsl/Port.lean` or `backends/sage_adapter.py` owners. |
| Python leaf framing | [`python/cas_port.py`](https://github.com/dzackgarza/lean-cas-dsl-leaf-contracts/blob/34bb8abbdbb49699015f63840cf86ed67f438003/python/cas_port.py), imported from the selected contract checkout through `PYTHONPATH` | Existing leaf programs call `from cas_port import serve`; framing supplies no mathematical meaning or correctness. |
| GAP realization | [`backends/gap_groups.py`](https://github.com/dzackgarza/lean-cas-dsl-leaves/blob/0030cccf6beb0dfc3a96cb5ea4d7cf569180cb6e/backends/gap_groups.py) imports `sage.libs.gap.libgap` and already calls `libgap.Units`; [`leaves.json`](https://github.com/dzackgarza/lean-cas-dsl-leaves/blob/0030cccf6beb0dfc3a96cb5ea4d7cf569180cb6e/leaves.json) launches the Python process | Extend the existing leaf and registrations for required unit-group computations under #3. No new Lean/libgap embedding or direct-GAP adapter is selected. |
| Engine interpreter | [`backends/engine_python.py`](https://github.com/dzackgarza/lean-cas-dsl-leaves/blob/0030cccf6beb0dfc3a96cb5ea4d7cf569180cb6e/backends/engine_python.py), selected `CAS_SAGE_PYTHON`/`CAS_GAP_PYTHON`, and the existing demo runner | Preserve the configured V1 launch under #24; extend explicit invocation portability in these owners under #34. The module aggregate must be the one needed by the leaf; modular Sage need not expose the full `sage.all`. |
| Research-side Python transport, after V1 | [`nbdsl_kernel.worker.client.WorkerClient`](https://github.com/dzackgarza/lean-jupyter-kernel/blob/4c6c2a77abcc717513a65ca35723ed428647e1bd/nbdsl_kernel/nbdsl_kernel/worker/client.py), prelude `CasDsl.Notebook`, and the permitted [`Worker.Output`](https://github.com/dzackgarza/lean-jupyter-kernel/blob/4c6c2a77abcc717513a65ca35723ed428647e1bd/worker/Worker/Output.lean) interface | New thin `python/cas_client/` facade over #69's released public result/reference contract under #68. Existing text/MIME replies are transport, not an already completed typed CAS API. |

The selected candidate's [Lake manifest](https://github.com/dzackgarza/lean-cas-dsl/blob/d0dfd405c6e10ec08ee68a024df4bc6b7d316e4b/lake-manifest.json) already resolves the leaf contract and notebook worker revisions above. These inspected source pins establish the reuse path, not a successful integrated build. Build and execute the actual compatible delivery tuple through #24.

The engine baseline is [passagemath-standard 10.8.13, CPython 3.12.14, Linux x86_64, with hashed wheels](https://github.com/dzackgarza/lean-cas-dsl/blob/d0dfd405c6e10ec08ee68a024df4bc6b7d316e4b/examples/kernel-v1/requirements-passagemath-py312-linux-x86_64.txt). Tag `passagemath-10.8.13` resolves to source `642d38ca1d030f742d47c0dff075b411284a3ebc`; #20 uses this matching source/runtime tuple for the next inventory while preserving the old Sage 10.9 census separately.

## GAP hazard decision

The source-based comparison in [#3](https://github.com/dzackgarza/lean-cas-dsl/issues/3) selects the existing subprocess-hosted libgap. It already supplies the units primitive and leaves the native integration with its upstream owner. Its [Cython wrapper](https://github.com/passagemath/passagemath/blob/642d38ca1d030f742d47c0dff075b411284a3ebc/src/sage/libs/gap/libgap.pyx#L161-L268) handles nonlocal C errors and interruption; [GASMAN marking/reference accounting](https://github.com/passagemath/passagemath/blob/642d38ca1d030f742d47c0dff075b411284a3ebc/src/sage/libs/gap/util.pyx#L113-L166) owns native objects inside the process. This does not assert fault-free behavior.

A direct process also isolates GAP from Lean, but needs protocol, serialization, state ownership and failure handling. The inspected [Sage process interface](https://github.com/passagemath/passagemath/blob/642d38ca1d030f742d47c0dff075b411284a3ebc/src/sage/interfaces/gap.py) illustrates synchronization/EOF handling and warns that printed GAP objects are not general serializable values. Neither topology preserves a selected result across process loss by itself.

Keep native pointers private. Public references retain their actual session/owner and selected construction; required defining maps cannot be rebound to a freshly chosen result. If ownership/data cannot be restored, report the precise stale/unavailable outcome. Worker replay and olean caching do not establish restoration of foreign objects. #3/#24/#69 retain the actual runtime and subsequent-use checks; the comparison is not a runtime acceptance claim.

## Owner

Interpret the accepted mathematical question, admit its registered realizations, and validate the complete returned interface and associations. #69 owns typed result/form indexing, selected contexts, actual defining maps, producer/output association and ownership. These obligations are not supplied merely by installing an engine or reusing framing. The required independent assertions continue to judge opaque answers; admitted formal evidence can discharge a question under the existing evidence rule before opaque computation. No engine or leaf proves its own answer, and certificate-primary evidence has not been adopted.

Keep implementation selection separate from mathematical ambiguity. The current public rule reports two admitted registrations for one operation/input form as ambiguous; #22 exercises alternatives in separate manifest configurations and preserves that combined-registration control. No backend ranking chooses a mathematical comparison.

## Queries

The September 29, 2026 corpus search used the queries `GAP computer algebra interface Lean`, `SageMath oracle certificate Lean tactic`, and `external solver certificate checking decode`. It found no applicable Lean CAS bridge in that inspected search; ACL2 release notes and evm-asm were not CAS bridges. This is a dated search result, not a proof that no bridge exists. The concrete source reuse above is the current implementation decision; no new exhaustive survey is required.
