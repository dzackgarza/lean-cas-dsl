"""The backend program of the Sage cardinality leaf (`CasLeaves/Modules/SageCardinality.lean`),
owned by the leaf: Sage answers the registered semantic operation `meth.cardinality` on free
modules `(ℤ/n)^k` (`ℤ^k` when `n = 0`); the leaf decodes the answer into a cardinal handle.

Run with a Python that has Sage (`passagemath-modules` suffices), from the repository root:
`.venv/bin/python CasLeaves/Modules/SageCardinality/sage_cardinality.py`.
"""

import os
import sys

sys.path.insert(0, os.path.join(os.path.dirname(__file__), "..", "..", "..", "port", "python"))
from cas_port import serve  # noqa: E402

try:
    import sage.all__sagemath_modules  # noqa: F401
    from sage.all__sagemath_modules import ZZ, FreeModule, Infinity, Integers
    from sage.version import version as SAGE_VERSION
except ImportError as exc:
    sys.stderr.write("sage_cardinality: Sage is not importable: %s\n" % exc)
    sys.exit(1)

ADAPTER_VERSION = "0.1.0"


def op_cardinality(args):
    n, k = int(args["n"]), int(args["k"])
    c = FreeModule(Integers(n) if n != 0 else ZZ, k).cardinality()
    return {"cardinal": "aleph0"} if c == Infinity else {"cardinal": "finite", "n": int(c)}


serve("sage", SAGE_VERSION, ADAPTER_VERSION, {"meth.cardinality": op_cardinality})
