"""The backend program of the GAP kernels leaf (`CasLeaves/Algebra/GapKernels.lean`), owned by the
leaf: operations keyed by registered semantic operations, computed by GAP (through `libgap`),
answered as untrusted JSON that the leaf decodes into the operation's semantic result type or
rejects. It speaks the port protocol through the core's Python reference module `cas_port`.

* `lim.groups.kernel`: the kernel `K ↪ G` of a homomorphism of group tables `f : G → H`, computed
  by GAP's `Kernel` of `GroupHomomorphismByImages` between the right regular permutation
  representations; answered as the table of `K` and its inclusion.

`--hostile=MODE` reproduces backend mistakes the caller must reject: `capability` also announces an
operation that is not registered (an own subgroup notion), `forget-inclusion` answers a kernel
without its inclusion, `whole-group` answers the whole group as the kernel.

Run with a Python that has `passagemath-gap` (or Sage), from the repository root:
`.venv/bin/python CasLeaves/Algebra/GapKernels/gap_kernels.py`.
"""

import os
import sys

sys.path.insert(0, os.path.join(os.path.dirname(__file__), "..", "..", "..", "port", "python"))
from cas_port import serve  # noqa: E402

try:
    import sage.all__sagemath_gap  # noqa: F401  (initializes libgap)
    from sage.libs.gap.libgap import libgap
except ImportError as exc:
    sys.stderr.write("gap_kernels: GAP (libgap) is not importable: %s\n" % exc)
    sys.exit(1)

ADAPTER_VERSION = "0.1.0"
HOSTILE = next((a.split("=", 1)[1] for a in sys.argv[1:] if a.startswith("--hostile=")), None)


def identity(mul):
    n = len(mul)
    return next(e for e in range(n) if all(mul[e][x] == x for x in range(n)))


def regular(mul):
    """The right regular representation: `a ↦ (x ↦ x·a)`, on the points `1..n`."""
    n = len(mul)
    return [libgap.PermList([mul[x][a] + 1 for x in range(n)]) for a in range(n)]


def op_groups_kernel(args):
    source, target, fmap = args["source"]["mul"], args["target"]["mul"], args["map"]
    gens, images = regular(source), regular(target)
    G, H = libgap.Group(gens), libgap.Group(images)
    hom = libgap.GroupHomomorphismByImages(G, H, gens, [images[fmap[a]] for a in range(len(source))])
    e = identity(source)
    # An element ρ_a of the regular representation sends the identity to a.
    kernel = sorted(int(libgap.OnPoints(e + 1, k)) - 1 for k in libgap.AsList(libgap.Kernel(hom)))
    if HOSTILE == "whole-group":
        kernel = list(range(len(source)))
    pos = {a: i for i, a in enumerate(kernel)}
    inv = {a: next(b for b in kernel if source[a][b] == e) for a in kernel}
    subgroup = {"size": len(kernel),
                "mul": [[pos[source[a][b]] for b in kernel] for a in kernel],
                "one": pos[e],
                "inv": [pos[inv[a]] for a in kernel]}
    if HOSTILE == "forget-inclusion":
        return {"subgroup": subgroup}
    return {"subgroup": subgroup, "inclusion": kernel}


OPS = {"lim.groups.kernel": op_groups_kernel}
if HOSTILE == "capability":
    OPS["op.groups.orthogonal_subgroup"] = op_groups_kernel

serve("gap", str(libgap.eval("GAPInfo.Version")), ADAPTER_VERSION, OPS)
