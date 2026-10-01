"""A probe backend for the registration probes (`CasAcceptance/RegistrationProbes.lean`). It is
test scaffolding, not a leaf: it exists to show what the kernel does with a registration's
answers. It serves, on the kernel's structural encoding,

* `meth.cardinality` on a named object (`{"ctor": <object id>, "args": [<parameters>]}`) or on
  a finite subset by its elements (`[1, 2, 3]`), as a value of `lit.cardinals`
  (`{"ctor": "finite", "args": [m]}` or `{"ctor": "aleph0", "args": []}`);
* `lim.sets.product` and `lim.sets.pullback` on a diagram of `Sets` in its standard form
  (`{"ctor": "pair", "args": [X, Y]}`, `{"ctor": "cospan", "args": [f, g]}`, an object a named
  object and a morphism its graph, a list of pairs of points), as the cone `{"ctor": "cone",
  "args": [<apex>, <leg>, <leg>]}`: the apex a named object, each leg a graph.

Its answers are chosen by its `--answer` flag:

* `correct`: the right answers;
* `seven`: the constant cardinality `7`, a well-formed wrong answer;
* `malformed`: a cardinality outside the result form;
* `missing_leg`: a product cone with one leg;
* `wrong_apex`: a product cone whose apex has one point too many, with well-formed legs.
"""

import sys

from cas_port import serve  # the leaf contract's reference port, on PYTHONPATH


def finite(m):
    return {"ctor": "finite", "args": [int(m)]}


def fin(n):
    return {"ctor": "obj.sets.fin", "args": [int(n)]}


def points(named):
    """The number of points of a finite named set the probe knows."""
    ctor, args = named["ctor"], named["args"]
    if ctor == "obj.sets.fin":
        return int(args[0])
    if ctor == "obj.sets.integers_mod" and int(args[0]) > 0:
        return int(args[0])
    raise ValueError("the probe knows no points of %s" % ctor)


def cardinality(value):
    if isinstance(value, list):  # a finite subset, by its elements
        return finite(len(set(map(str, value))))
    ctor, args = value["ctor"], value["args"]
    if ctor == "obj.sets.fin":
        return finite(args[0])
    if ctor == "obj.sets.integers_mod_power":
        n, k = int(args[0]), int(args[1])
        if k == 0:
            return finite(1)
        if n == 0:
            return {"ctor": "aleph0", "args": []}
        return finite(n ** k)
    raise ValueError("the probe computes no cardinality of %s" % ctor)


def cone(apex, *legs):
    return {"ctor": "cone", "args": [apex, *legs]}


def product(diagram):
    """`X × Y` as `Fin(|X|·|Y|)`, with `k ↦ (k div |Y|, k mod |Y|)`."""
    X, Y = diagram["args"]
    n, m = points(X), points(Y)
    fst = [[k, k // m] for k in range(n * m)]
    snd = [[k, k % m] for k in range(n * m)]
    return cone(fin(n * m), fst, snd)


def product_missing_leg(diagram):
    apex, fst, _ = product(diagram)["args"]
    return cone(apex, fst)


def product_wrong_apex(diagram):
    X, Y = diagram["args"]
    n, m = points(X), points(Y)
    size = n * m + 1
    return cone(fin(size), [[k, k % n] for k in range(size)], [[k, k % m] for k in range(size)])


def pullback(diagram):
    """`{(x, y) | f x = g y}` as `Fin(k)`, listed in order, with its two projections."""
    f, g = diagram["args"]
    f, g = dict((x, y) for x, y in f), dict((x, y) for x, y in g)
    pairs = [(x, y) for x in sorted(f) for y in sorted(g) if f[x] == g[y]]
    fst = [[i, x] for i, (x, _) in enumerate(pairs)]
    snd = [[i, y] for i, (_, y) in enumerate(pairs)]
    return cone(fin(len(pairs)), fst, snd)


ANSWERS = {
    "correct": {"meth.cardinality": cardinality, "lim.sets.product": product,
                "lim.sets.pullback": pullback},
    "seven": {"meth.cardinality": lambda value: finite(7)},
    "malformed": {"meth.cardinality": lambda value: {"cardinal": "seventeen"}},
    "missing_leg": {"meth.cardinality": cardinality, "lim.sets.product": product_missing_leg},
    "wrong_apex": {"meth.cardinality": cardinality, "lim.sets.product": product_wrong_apex},
}


if __name__ == "__main__":
    flag = next((a for a in sys.argv[1:] if a.startswith("--answer=")), "--answer=correct")
    serve("probe", "0", "0.1.0", ANSWERS[flag.split("=", 1)[1]])
