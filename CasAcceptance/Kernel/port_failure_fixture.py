"""Protocol-only subprocess fixture for PortFailureProbes; no mathematical operations."""

import json
import sys


def emit(data):
    raw = json.dumps(data, separators=(",", ":")).encode()
    sys.stdout.buffer.write(str(len(raw)).encode() + b"\n" + raw)
    sys.stdout.buffer.flush()


mode = sys.argv[1]
emit({"op": "ready", "backend": "failure-fixture", "backend_version": "0", "capabilities": []})
if mode == "broken-pipe":
    sys.exit(17)
size = int(sys.stdin.buffer.readline())
request = json.loads(sys.stdin.buffer.read(size))
if mode == "closed":
    sys.exit(17)
raw = {
    "header-eof": b"17",
    "payload-eof": b"19\n{}",
    "bad-header": b"x\n",
    "bad-json": b"1\n{",
    "bad-utf8": b"1\n\xff",
}.get(mode)
if raw is not None:
    sys.stdout.buffer.write(raw)
    sys.stdout.buffer.flush()
    sys.exit(17)
if mode == "wrong-id":
    emit({"request_id": request["request_id"] + 1, "status": "ok", "value": None})
elif mode == "bad-status":
    emit({"request_id": request["request_id"], "status": "unknown"})
elif mode == "unsupported":
    emit({"request_id": request["request_id"], "status": "unsupported", "op": request["op"]})
elif mode == "engine-error":
    emit({"request_id": request["request_id"], "status": "error", "kind": "EngineError", "message": "fixture"})
else:
    raise ValueError(mode)
