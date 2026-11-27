"""Protocol-v2 provider for kernel lift tests.

It answers the structural views and the prescribed restriction lift of RX-LIFT
(tests/acceptance/proposals/independent-extension-reconstruction-20261024/
completion/rx-lift-prescribed-stages.cas). Each answer is provider-owned data: a
native export, whose later projections and applications reach this process
again through `$cas.invoke_export` and are answered the same way. The operation
and invocation context of each request, export requests included, are written to
the log file named by the first argument, one JSON object per line. The kernel
test reads that log.
"""

from __future__ import annotations

import json
import sys

from cas_port import serve
from cas_session import JsonValue, export

LOG = sys.argv[1]


def _answer(operation: str):
    def handler(context: JsonValue) -> JsonValue:
        with open(LOG, "a", encoding="utf-8") as log:
            log.write(json.dumps({"op": operation, "context": context}) + "\n")
        return export(_answer(f"{operation}/export"), [])

    return handler


OPERATIONS = sys.argv[2:]

serve("kernel-lift-peer", "0", {operation: _answer(operation) for operation in OPERATIONS})
