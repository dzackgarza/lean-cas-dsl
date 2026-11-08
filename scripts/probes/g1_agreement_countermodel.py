"""Executable countermodel for G1's proposed total agreement classifier.

This is an engineering model, not the production resolver or a new acceptance
oracle. The proof and exact categorical interpretation are in issue #66.
Every selected finite route terminates; deciding agreement of *all* routes is
not implemented or claimed. No sampled prefix is called a uniqueness proof.
"""
from __future__ import annotations

from dataclasses import dataclass
from itertools import product
from typing import Callable, Iterable


@dataclass(frozen=True)
class Instruction:
    next_state: int
    write: int
    move: int

    def __post_init__(self) -> None:
        if self.next_state < 0 or self.write not in (0, 1) or self.move not in (-1, 0, 1):
            raise ValueError("invalid binary-tape instruction")


@dataclass(frozen=True)
class Machine:
    """A deterministic binary-tape machine; absent transitions halt.

    Rows are (state, scanned symbol, instruction). Duplicate keys are rejected.
    The blank input has state 0, head 0 and an all-zero two-sided tape.
    """
    rows: tuple[tuple[int, int, Instruction], ...]

    def __post_init__(self) -> None:
        keys = [(q, a) for q, a, _ in self.rows]
        if any(q < 0 or a not in (0, 1) for q, a in keys):
            raise ValueError("invalid transition key")
        if len(keys) != len(set(keys)):
            raise ValueError("duplicate transition key")

    def halts_within(self, steps: int) -> bool:
        """Decide only bounded halting, by an explicitly finite simulation."""
        if steps < 0:
            raise ValueError("steps must be nonnegative")
        transitions = {(q, a): instruction for q, a, instruction in self.rows}
        ones: set[int] = set()
        state = head = 0
        for elapsed in range(steps + 1):
            instruction = transitions.get((state, int(head in ones)))
            if instruction is None:
                return True
            if elapsed == steps:
                return False
            if instruction.write:
                ones.add(head)
            else:
                ones.discard(head)
            state, head = instruction.next_state, head + instruction.move
        raise AssertionError("finite simulation fell through")

    def marked_bit(self, n: int) -> int:
        """s_M(0)=0; s_M(n+1)=1 iff M halts in at most n transitions."""
        if n < 0:
            raise ValueError("route index must be nonnegative")
        return int(n > 0 and self.halts_within(n - 1))


@dataclass(frozen=True)
class Tower:
    """A set with two fixed points and a countable family of selected points."""
    carrier: tuple[int, ...]
    zero: int
    one: int
    points: Callable[[int], int]

    def tail(self) -> Tower:
        return Tower(self.carrier, self.zero, self.one, lambda n: self.points(n + 1))

    def head(self) -> tuple[tuple[int, ...], int, int, int]:
        return (self.carrier, self.zero, self.one, self.points(0))


def machine_tower(machine: Machine) -> Tower:
    return Tower((0, 1), 0, 1, machine.marked_bit)


@dataclass(frozen=True)
class SelectedRoute:
    """The exact first-hit route enter; tail^n; head; origin remains retained."""
    tail_count: int

    def __post_init__(self) -> None:
        if self.tail_count < 0:
            raise ValueError("tail_count must be nonnegative")

    @property
    def labels(self) -> tuple[str, ...]:
        return ("enter",) + ("tail",) * self.tail_count + ("head",)

    def whole_family(self, machine: Machine) -> tuple[int]:
        """Exact table of Unit -> Bool, not a sample of an infinite domain.

        The rigid source object ranges over the one-object classifier total;
        the nullary operand ranges over Unit. Both variables remain arbitrary.
        """
        return (machine.marked_bit(self.tail_count),)


def accepts_first_hit(labels: Iterable[str]) -> bool:
    """Finite automaton for enter . tail* . head; target is absorbing."""
    state = "source"
    for label in labels:
        if state == "source" and label == "enter":
            state = "tower"
        elif state == "tower" and label == "tail":
            pass
        elif state == "tower" and label == "head":
            state = "owner"
        else:
            return False
    return state == "owner"


@dataclass(frozen=True)
class DifferenceWitness:
    left: SelectedRoute
    right: SelectedRoute
    left_family: tuple[int]
    right_family: tuple[int]


@dataclass(frozen=True)
class Undetermined:
    checked_through: int


def inspect_prefix(machine: Machine, through: int) -> DifferenceWitness | Undetermined:
    """A finite diagnostic: never infer global agreement from a quiet prefix."""
    if through < 0:
        raise ValueError("through must be nonnegative")
    initial = SelectedRoute(0)
    for n in range(1, through + 1):
        route = SelectedRoute(n)
        if route.whole_family(machine) != initial.whole_family(machine):
            return DifferenceWitness(initial, route, initial.whole_family(machine), route.whole_family(machine))
    return Undetermined(through)


def halt_after(steps: int) -> Machine:
    """An explicit finite machine halting after exactly `steps` transitions."""
    if steps < 0:
        raise ValueError("steps must be nonnegative")
    return Machine(tuple((q, a, Instruction(q + 1, a, 0)) for q in range(steps) for a in (0, 1)))


def loop_forever() -> Machine:
    return Machine(((0, 0, Instruction(0, 0, 0)), (0, 1, Instruction(0, 1, 0))))


def all_binary_maps() -> tuple[tuple[int, int], ...]:
    return tuple(product((0, 1), repeat=2))


def apply_map(mapping: tuple[int, int], value: int) -> int:
    return mapping[value]


def preserves_base_points(mapping: tuple[int, int]) -> bool:
    return apply_map(mapping, 0) == 0 and apply_map(mapping, 1) == 1
