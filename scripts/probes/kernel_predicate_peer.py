"""Protocol-v2 provider for kernel predicate tests.

It answers whether a natural number is prime. The kernel decides membership in
the subset of primes from this Boolean answer.
"""

from __future__ import annotations

from cas_port import point_invocation, serve
from cas_session import JsonValue


def _natural(value: JsonValue) -> int:
    """A natural operand: a returned number, or the numeral descriptor of one."""
    if isinstance(value, int):
        return value
    assert isinstance(value, dict) and isinstance(value.get("args"), list), value
    number = value["args"][-1]
    assert isinstance(number, int), value
    return number


def is_prime(context: JsonValue) -> JsonValue:
    fields = point_invocation(context, "mor.sets.nat_is_prime")
    number = _natural(fields[6])
    return number > 1 and all(number % divisor for divisor in range(2, number))


serve("kernel-predicate-peer", "0", {"mor.sets.nat_is_prime": is_prime})
