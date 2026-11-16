"""Protocol-v2 provider for kernel lift tests.

It answers the structural views and the prescribed restriction lift of RX-LIFT
(tests/acceptance/proposals/independent-extension-reconstruction-20261024/
completion/rx-lift-prescribed-stages.cas) with named descriptors, and writes the
operation and invocation context of each request to the log file named by its
first argument, one JSON object per line. The kernel test reads that log.
"""

from __future__ import annotations

import json
import sys

from cas_port import serve
from cas_session import JsonValue

LOG = sys.argv[1]


def _answer(operation: str):
    def handler(context: JsonValue) -> JsonValue:
        with open(LOG, "a", encoding="utf-8") as log:
            log.write(json.dumps({"op": operation, "context": context}) + "\n")
        return {"ctor": operation, "args": []}

    return handler


OPERATIONS = sys.argv[2:]

serve("kernel-lift-peer", "0", {operation: _answer(operation) for operation in OPERATIONS})
