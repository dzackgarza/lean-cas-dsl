"""Arbitrary service protocol witnesses. These values assert no mathematical answers."""
import itertools
import sys
import uuid
from cas_port import serve, value_data, opaque_data, deferred_call, deferred_data, result_ref

role, mode = sys.argv[1:3]
serials = itertools.count()
issued = set()
session = uuid.uuid4().hex

def node(tag, *args):
    return {'ctor': tag, 'args': list(args)}

def request(operation, receiver):
    return {'ctor': operation, 'args': [], 'receiver': receiver}

def call(operation, receiver):
    return deferred_call(operation, operation + '#input', request(operation, receiver))

def fresh():
    token = f'{session}:{next(serials)}'
    issued.add(token)
    return opaque_data(token)

def tokens(value):
    if isinstance(value, dict):
        if value.get('ctor') == 'opaqueData':
            yield value['args'][0]
        else:
            for child in value.values():
                yield from tokens(child)
    elif isinstance(value, list):
        for child in value:
            yield from tokens(child)

def outer(arguments):
    receiver = arguments['receiver']
    if mode == 'nested-object-argument':
        actual = node('functorAction', node('fun.sets.identity'), receiver)
        return deferred_data([deferred_call('meth.cardinality', 'cat.sets', actual)],
                             value_data(node('obj.sets.fin', 19)))
    if mode == 'nested-map-argument':
        actual = node('map', node('fun.sets.identity'),
                      node('typedMap', receiver, receiver, node('mor.sets.fin_rev', 2)))
        application = node('apply', 'mor.sets.fin_rev', [2], node('mor.sets.fin_rev', 2),
                           receiver, receiver, receiver, actual)
        return deferred_data([deferred_call('mor.sets.fin_rev', 'mor.sets.fin_rev', application)],
                             value_data(node('obj.sets.fin', 19)))
    if mode in {'whole-map', 'wrong-map-endpoint'}:
        first = result_ref(0)
        second = result_ref(1)
        arrow = node('map', node('fun.sets.identity'),
                     node('typedMap', receiver, receiver, node('mor.sets.fin_rev', 2)))
        application = node('apply', 'fun.sets.identity#map', [], arrow,
                           first, first, second, node('identity', first, first))
        return deferred_data([
            call('fun.sets.identity', receiver),
            call('fun.sets.identity', first),
            deferred_call('fun.sets.identity#map', 'fun.sets.identity#input', application),
        ], first)
    if mode == 'cycle':
        return deferred_data([call('fun.sets.list', receiver)], result_ref(0))
    if mode == 'backend-selector':
        selected = call('fun.sets.identity', receiver)
        selected['backend'] = 'child-service'
        return node('deferredData', [selected], result_ref(0))
    if mode == 'forward-reference':
        return node('deferredData', [call('fun.sets.identity', result_ref(0))], result_ref(0))
    if mode == 'bad-type':
        return deferred_data([
            deferred_call('meth.cardinality', 'cat.sets', receiver),
            call('fun.sets.identity', result_ref(0)),
        ], result_ref(1))
    if mode == 'extra-reference':
        return deferred_data([call('fun.sets.identity', receiver)],
            {'ctor': 'valueData', 'args': [node('obj.sets.fin', 17)], 'ignored': result_ref(0)})
    if mode == 'opaque' or mode == 'nested':
        return deferred_data([call('fun.sets.identity', receiver)], result_ref(0))
    if mode == 'mixed-owners':
        return deferred_data([call('fun.sets.identity', receiver)],
            node('valueData', node('objectProduct', result_ref(0), fresh())))
    if mode == 'portable-from-owned' and not issued:
        return fresh()
    if mode == 'portable-from-owned':
        if any(token not in issued for token in tokens(receiver)):
            raise ValueError('the original source lost its actual session')
        receiver = node('obj.sets.fin', 2)
    return deferred_data([
        call('fun.sets.identity', receiver),
        call('fun.sets.identity', result_ref(0)),
        deferred_call('meth.cardinality', 'cat.sets', result_ref(0)),
        deferred_call('meth.cardinality', 'cat.sets', result_ref(1)),
    ], result_ref(0))

def identity(arguments):
    receiver = arguments['receiver']
    if any(token not in issued for token in tokens(receiver)):
        raise ValueError('the child received a foreign opaque token')
    index = next(serials)
    if mode == 'nested' and index == 0:
        return deferred_data([call('fun.sets.identity', node('obj.sets.fin', 19))], result_ref(0))
    if mode in {'opaque', 'mixed-owners'}:
        return value_data(fresh())
    if mode == 'nested-map-argument':
        return value_data(receiver)
    return value_data(node('obj.sets.fin', 7 + index))

def map_action(arguments):
    operation, parameters, arrow, domain, source, target, argument = arguments['args']
    if operation != 'fun.sets.identity#map' or parameters or arrow['args'][0] != node('fun.sets.identity'):
        raise ValueError('the shared service changed its exact selected map action')
    if (source == target and mode != 'nested-map-argument') or domain != source or argument != node('identity', source, source):
        raise ValueError('the whole service map changed its retained image occurrences')
    if arrow['args'][1]['args'][2] != node('mor.sets.fin_rev', 2):
        raise ValueError('the service lost its nonidentity original whole callable')
    if mode == 'nested-map-argument':
        return value_data(node('typedMap', source, target, [[0, 1], [1, 0]]))
    if mode == 'wrong-map-endpoint':
        target = node('obj.sets.fin', 999)
    return value_data(node('typedMap', source, target, fresh()))


def cardinality(arguments):
    if list(tokens(arguments)):
        raise ValueError('the independent consumer received opaque source data')
    if arguments.get('ctor') != 'obj.sets.fin':
        raise ValueError('the independent consumer received an unevaluated source action')
    return node('finite', 17 + next(serials))

def target_map(arguments):
    operation, parameters, arrow, domain, source, target, argument = arguments['args']
    if operation != 'mor.sets.fin_rev' or parameters != [2] or arrow != node('mor.sets.fin_rev', 2):
        raise ValueError('the target operation lost its published own selection')
    if argument != node('typedMap', source, source, [[0, 1], [1, 0]]):
        raise ValueError('the target consumer received an unexecuted source map action')
    return value_data(node('typedMap', domain, target, fresh()))


implementations = {'fun.sets.list': outer} if role == 'outer' else (
    {'fun.sets.identity': identity, 'fun.sets.identity#map': map_action} if role == 'child' else {'meth.cardinality': cardinality, 'mor.sets.fin_rev': target_map})
serve('deferred-service-probe', '0', '0.1.0', implementations)
