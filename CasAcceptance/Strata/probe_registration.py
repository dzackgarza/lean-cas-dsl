"""A probe backend for the registration probes (`CasAcceptance/RegistrationProbes.lean`). It is
test scaffolding, not a leaf: it exists to show what the kernel does with a registration's
answers. It serves `meth.cardinality` on the kernel's encoding of a named object
(`{"ctor": <object id>, "args": [<parameters>]}`) and answers, by its `--answer` flag,

* `correct`: the cardinality of `Fin(n)` and of `(ℤ/n)^k`, as a value of `lit.cardinals`
  (`{"ctor": "finite", "args": [m]}` or `{"ctor": "aleph0", "args": []}`);
* `seven`: the constant `7`, a well-formed wrong answer;
* `malformed`: a value outside the result form.
"""

import sys

from cas_port import serve  # the leaf contract's reference port, on PYTHONPATH


def finite(m):
    return {"ctor": "finite", "args": [int(m)]}


def correct(value):
    ctor, args = value["ctor"], value["args"]
    if ctor in ("obj.sets.fin", "obj.finite_sets.fin"):
        return finite(args[0])
    if ctor == "obj.sets.integers_mod_power":
        n, k = int(args[0]), int(args[1])
        if k == 0:
            return finite(1)
        if n == 0:
            return {"ctor": "aleph0", "args": []}
        return finite(n ** k)
    raise ValueError("the probe computes no cardinality of %s" % ctor)


ANSWERS = {
    "correct": correct,
    "seven": lambda value: finite(7),
    "malformed": lambda value: {"cardinal": "seventeen"},
}


if __name__ == "__main__":
    flag = next((a for a in sys.argv[1:] if a.startswith("--answer=")), "--answer=correct")
    serve("probe", "0", "0.1.0", {"meth.cardinality": ANSWERS[flag.split("=", 1)[1]]})
