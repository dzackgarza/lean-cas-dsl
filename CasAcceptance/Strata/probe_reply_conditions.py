"""Public-port execution fault conditions, independent of assertion source.

The JSON configuration selects a protocol failure, or forwards an independently
provided backend and replaces one operation's reply with supplied data. This is
engineering fault injection, not a mathematical implementation or oracle.
"""

from contextlib import contextmanager
import json
from pathlib import Path
import signal
import subprocess
import sys
from types import SimpleNamespace
import uuid

from cas_port import opaque_data, read_frame, write_frame


@contextmanager
def port_streams(input_stream=None, output_stream=None):
    original_input, original_output = sys.stdin, sys.stdout
    try:
        if input_stream is not None:
            sys.stdin = SimpleNamespace(buffer=input_stream)
        if output_stream is not None:
            sys.stdout = SimpleNamespace(buffer=output_stream)
        yield
    finally:
        sys.stdin, sys.stdout = original_input, original_output


def child_read(child):
    with port_streams(input_stream=child.stdout):
        return read_frame()


def child_write(child, frame):
    with port_streams(output_stream=child.stdin):
        write_frame(frame)


def selected(config, frame):
    operation = config.get("operation")
    if operation is not None and frame.get("op") != operation:
        return False
    constructor = config.get("requestCtor")
    if constructor is not None:
        argument = frame.get("args")
        if not isinstance(argument, dict) or argument.get("ctor") != constructor:
            return False
    return True


def main():
    config = json.loads(Path(sys.argv[1]).read_text())
    mode = config["mode"]
    child = None
    replacements = {}
    intercepted = False

    def stop(_signal, _frame):
        raise SystemExit(0)

    signal.signal(signal.SIGTERM, stop)

    def receipt(event):
        if "receipts" in config:
            with Path(config["receipts"]).open("a") as output:
                output.write(json.dumps(event, separators=(",", ":")) + "\n")

    def consume(data, used):
        if isinstance(data, dict):
            if data.get("ctor") == "opaqueData":
                args = data.get("args")
                if isinstance(args, list) and len(args) == 1 and args[0] in replacements:
                    used.append(args[0])
                    return replacements[args[0]]
            return {key: consume(value, used) for key, value in data.items()}
        if isinstance(data, list):
            return [consume(value, used) for value in data]
        return data

    try:
        if "delegate" in config:
            delegate = config["delegate"]
            child = subprocess.Popen(
                [delegate["command"], *delegate.get("args", [])],
                cwd=delegate["root"], stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                stderr=sys.stderr,
            )
            ready = child_read(child)
            if ready is None:
                return
            write_frame(ready)
        else:
            write_frame({"op": "ready", "protocol": 1,
                         "backend": config.get("backend", "condition-probe"),
                         "backend_version": "0", "adapter_version": "0.1.0",
                         "capabilities": config.get("operations", [])})
        while True:
            request = read_frame()
            if request is None:
                return
            used = []
            forwarded = consume(request, used)
            if used:
                receipt({"event": "consume", "tokens": used,
                         "request": request, "forwarded": forwarded})
            if mode == "disconnect" and selected(config, request):
                return
            if child is not None:
                child_write(child, forwarded)
                response = child_read(child)
                if response is None:
                    return
            else:
                response = {"request_id": request.get("request_id"),
                            "status": "unsupported", "op": request.get("op")}
            if selected(config, request) and not used:
                if mode == "unsupported":
                    response = {"request_id": request.get("request_id"),
                                "status": "unsupported", "op": request.get("op")}
                elif mode == "replace":
                    response = {"request_id": request.get("request_id"),
                                "status": "ok", "value": config["value"]}
                elif mode == "owned-replacement":
                    if not intercepted and response.get("status") == "ok":
                        token = "fault-owned-" + uuid.uuid4().hex
                        replacements[token] = config["backing"]
                        receipt({"event": "create", "token": token,
                                 "request": request, "backing": config["backing"]})
                        response = {"request_id": request.get("request_id"),
                                    "status": "ok", "value": opaque_data(token)}
                        intercepted = True
                elif mode != "passthrough":
                    raise ValueError("unknown execution-control condition")
            write_frame(response)
    finally:
        if child is not None:
            if child.poll() is None:
                child.kill()
            child.wait(timeout=10)


if __name__ == "__main__":
    main()
