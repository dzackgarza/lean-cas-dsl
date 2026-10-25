"""Arbitrary protocol witnesses for action execution; no mathematical answers."""

import itertools
import sys
import uuid

from cas_port import opaque_data, point_invocation, serve, value_data


role, operation = sys.argv[1:3]
options = set(sys.argv[3:])
serials = itertools.count()
issued = set()
images = []
session = uuid.uuid4().hex


def node(tag, *args):
    return {"ctor": tag, "args": list(args)}


def tokens(data):
    if isinstance(data, dict):
        if data.get("ctor") == "opaqueData":
            yield data["args"][0]
        else:
            for child in data.values():
                yield from tokens(child)
    elif isinstance(data, list):
        for child in data:
            yield from tokens(child)


def fresh():
    token = f"{session}:{next(serials)}"
    issued.add(token)
    return opaque_data(token)


def object_action(request):
    if request.get("ctor") != operation or not isinstance(request.get("args"), list):
        raise ValueError("object action changed its selected declaration")
    if "receiver" not in request:
        raise ValueError("object action omitted its complete source")
    if any(token not in issued for token in tokens(request)):
        raise ValueError("object action received a foreign source owner")
    if "--first-opaque" in options and not images or "--opaque-objects" in options:
        result = fresh()
    else:
        result = node("obj.sets.fin", 7 + len(images))
    images.append(result)
    return value_data(result)


def map_action(request):
    _, parameters, arrow, domain, source, target, argument = point_invocation(request, operation + "#map")
    if source not in images or target not in images:
        raise ValueError("map action did not reuse both actually computed object images")
    if domain != source or argument != node("identity", source, source):
        raise ValueError("map action replaced its complete original image domain")
    if arrow.get("ctor") != "map" or len(arrow.get("args", [])) != 2:
        raise ValueError("map action lost its original source map")
    action, original = arrow["args"]
    if action != node(operation, *parameters):
        raise ValueError("map action changed its selected complete parameters")
    if original.get("ctor") != "typedMap" or len(original.get("args", [])) != 3:
        raise ValueError("map action discarded a complete source endpoint")
    if any(token not in issued for token in tokens(request)):
        raise ValueError("map action received a foreign source or image owner")
    if "--wrong-endpoint" in options:
        target = node("obj.sets.fin", 999)
    callable_data = fresh()
    if "--bare-maps" in options:
        return value_data(callable_data)
    return value_data(node("typedMap", source, target, callable_data))


def target_consumer(request):
    if request.get("ctor") != "obj.sets.fin" or len(request.get("args", [])) != 1:
        raise ValueError("target consumer received data outside its own target interface")
    if list(tokens(request)):
        raise ValueError("target consumer received a foreign opaque owner")
    return 17  # An arbitrary framing witness, never checked as a mathematical answer.


def source_callable(request):
    _, _, _, domain, source, target, argument = point_invocation(request)
    if domain != source or argument != node("identity", source, source):
        raise ValueError("the source callable lost its whole domain")
    if any(token not in issued for token in tokens(request)):
        raise ValueError("the source callable received a foreign owner")
    return value_data(node("typedMap", source, target, fresh()))


if role == "action":
    implementations = {operation: object_action, operation + "#map": map_action}
    for option in options:
        if option.startswith("--source-operation="):
            implementations[option.split("=", 1)[1]] = source_callable
elif role == "target":
    implementations = {operation: target_consumer}
else:
    raise ValueError("unknown engineering witness role")

serve("action-execution-probe", "0", "0.1.0", implementations)
