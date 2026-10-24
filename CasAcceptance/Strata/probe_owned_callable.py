"""Actual-process ownership scaffolding, with no mathematical implementation.

Opaque tokens witness creation and consumption in the same process. The returned
point is deliberately arbitrary and is never used as mathematical correctness
evidence by SessionOwnershipProbes. All framing uses the released port contract.
"""

import itertools
import sys
import uuid

from cas_port import opaque_data, point_invocation, serve, value_data


process = uuid.uuid4().hex
serials = itertools.count()
issued = set()
materialize_invocation = "--materialize-invocation" in sys.argv[1:]
require_argument_owner = "--require-argument-owner" in sys.argv[1:]
argument_calls = 0


def fresh():
    token = f"{process}:{next(serials)}"
    issued.add(token)
    return opaque_data(token)


def tokens(data):
    if isinstance(data, dict):
        if data.get("ctor") == "opaqueData":
            args = data.get("args")
            if not isinstance(args, list) or len(args) != 1:
                raise ValueError("an owned token lost its complete framing")
            yield args[0]
        else:
            for child in data.values():
                yield from tokens(child)
    elif isinstance(data, list):
        for child in data:
            yield from tokens(child)


def implementation(operation):
    def call(argument):
        global argument_calls
        if isinstance(argument, dict) and argument.get("ctor") == "apply":
            _, _, arrow, _, _, _, supplied = point_invocation(argument, operation)
            if require_argument_owner:
                used = list(tokens(supplied))
                if argument_calls and not used:
                    raise ValueError("the subsequent operation lost its predecessor's actual result")
                if any(token not in issued for token in used):
                    raise ValueError("the operation received another session's result")
                argument_calls += 1
                return fresh()
            used = list(tokens(arrow))
            if materialize_invocation and not used:
                return fresh()
            if not used or any(token not in issued for token in used):
                raise ValueError("the request did not consume this process's returned callable")
            return value_data(0)
        if not isinstance(argument, dict) or argument.get("ctor") != operation:
            raise ValueError("a whole-callable request lost its declared operation")
        if not isinstance(argument.get("args"), list):
            raise ValueError("a whole-callable request lost its ordered parameters")
        return fresh()

    return call


if __name__ == "__main__":
    serve("session-probe", "0", "0.1.0", {
        operation: implementation(operation) for operation in sys.argv[1:]
        if not operation.startswith("--")
    })
