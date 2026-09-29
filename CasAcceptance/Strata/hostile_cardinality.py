"""A hostile backend for the stratified-failure probes (`CasAcceptance/StrataProbes.lean`): it
answers the registered operation `meth.cardinality` outside the operation's result type
(`n = 1`), and fails while computing (`n = 2`)."""

import os
import sys

sys.path.insert(0, os.path.join(os.path.dirname(__file__), "..", "..", "port", "python"))
from cas_port import serve  # noqa: E402


def op_cardinality(args):
    if int(args["n"]) == 2:
        raise ArithmeticError("the backend failed while computing")
    return {"cardinal": "seventeen"}


if __name__ == "__main__":
    serve("probe", "0", "0.1.0", {"meth.cardinality": op_cardinality})
