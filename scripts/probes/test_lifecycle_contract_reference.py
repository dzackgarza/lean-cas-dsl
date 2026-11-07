"""Executable finite models of the proposed contract corrections, not production tests."""
from dataclasses import dataclass
from itertools import permutations, product
import unittest

@dataclass(frozen=True)
class Binding:
    value: str
    role: str
    owners: frozenset[str]=frozenset()

@dataclass(frozen=True)
class Export:
    owner: str
    captures: tuple[Binding,...]

class Frame:
    def __init__(self, export, arguments, scope):
        self.export=export
        self.scope=scope
        self.slots=export.captures+tuple(arguments)
        self.active=True
    def capture(self, index):
        if not self.active or not (0<=index<len(self.export.captures)):
            raise ValueError('expired or undeclared capture')
        return self.slots[index]
    def required_owners(self):
        return frozenset({self.export.owner}).union(*(v.owners for v in self.slots))
    def dispatch(self, live):
        if not self.active or not self.required_owners()<=live:
            raise ValueError('unavailable before dispatch')
        return self.slots
    def close(self): self.active=False

class Admission:
    def __init__(self, nonce):
        self.nonce=nonce
        self.used=set()
        self.jobs=[]
    def receive(self, nonce, request_id, operation, payload):
        if nonce!=self.nonce:
            return 'wrong_nonce'
        if request_id in self.used:
            return 'protocol_error:duplicate_request_id'
        self.used.add(request_id)
        if operation=='execute':
            self.jobs.append((request_id,payload))
        return 'admitted'

class TransitionTests(unittest.TestCase):
    def setUp(self):
        self.a=Binding('original-map','map over R',frozenset({'foreign:1'}))
        self.b=Binding('other-map','map over S',frozenset({'foreign:2'}))
        self.exp=Export('producer:1',(self.a,self.b))
    def test_capture_prefix_cannot_be_replaced_by_arguments(self):
        for args in ((),(self.b,), (self.b,self.a)):
            f=Frame(self.exp,args,'fresh')
            self.assertEqual(tuple(f.capture(i) for i in range(2)),self.exp.captures)
            self.assertEqual(f.slots[2:],args)
    def test_equal_values_distinct_roles_retained(self):
        x=Binding('same','role-1'); y=Binding('same','role-2')
        f=Frame(Export('p',(x,y)),(),'s')
        self.assertNotEqual(f.capture(0),f.capture(1))
        self.assertEqual(len(f.slots),2)
    def test_nested_frames_do_not_mutate_shared_captures(self):
        first=Frame(self.exp,(self.a,),'s1'); second=Frame(self.exp,(self.b,),'s2')
        second.close()
        self.assertEqual(first.capture(0),self.a)
        self.assertEqual(first.slots[2],self.a)
        with self.assertRaises(ValueError): second.capture(0)
        self.assertEqual(self.exp.captures,(self.a,self.b))
    def test_suspend_rebinds_only_declared_capture_pairs(self):
        old=Frame(self.exp,(self.a,),'old')
        retained=(old.capture(1),)
        old.close()
        resume=Frame(Export(self.exp.owner,retained),(self.a,),'new')
        self.assertEqual(resume.capture(0),self.b)
        with self.assertRaises(ValueError): resume.capture(1)
        with self.assertRaises(ValueError): old.capture(0)
    def test_all_required_owners_checked_before_send(self):
        frame=Frame(self.exp,(Binding('arg','r',frozenset({'arg:1'})),),'s')
        allowners=frame.required_owners()
        self.assertEqual(allowners,frozenset({'producer:1','foreign:1','foreign:2','arg:1'}))
        for missing in allowners:
            with self.assertRaises(ValueError): frame.dispatch(allowners-{missing})
        self.assertEqual(frame.dispatch(allowners),frame.slots)
    def test_loss_after_preparation_does_not_rebind_owner(self):
        frame=Frame(self.exp,(),'s')
        replacement=frozenset({'producer:2','foreign:1','foreign:2'})
        with self.assertRaises(ValueError): frame.dispatch(replacement)
        self.assertEqual(frame.export.owner,'producer:1')
    def test_no_ambient_old_scope(self):
        frame=Frame(self.exp,(),'s')
        for i in (-1,2,7):
            with self.assertRaises(ValueError): frame.capture(i)
        frame.close()
        with self.assertRaises(ValueError): frame.capture(0)
    def test_duplicate_same_or_conflicting_payload_has_no_effect(self):
        for first,second in product(('code A','code B'),repeat=2):
            r=Admission('w')
            r.receive('w','i','execute',first)
            before=list(r.jobs)
            self.assertEqual(r.receive('w','i','execute',second),'protocol_error:duplicate_request_id')
            self.assertEqual(r.jobs,before)
    def test_request_id_shared_across_operation_kinds(self):
        for a,b in product(('execute','inspect','cancel','commit_status'),repeat=2):
            r=Admission('w'); r.receive('w','id',a,'payload')
            before=list(r.jobs)
            self.assertTrue(r.receive('w','id',b,'different').startswith('protocol_error:'))
            self.assertEqual(r.jobs,before)
    def test_no_snapshot_rollback_of_seen_identifiers(self):
        r=Admission('w'); r.receive('w','i','execute','A')
        # Snapshot selection deliberately does not mutate this live admission set.
        for snapshot in (0,1,0,9):
            self.assertTrue(r.receive('w','i','execute',f'parent={snapshot}').startswith('protocol_error:'))
        self.assertEqual(len(r.jobs),1)
    def test_explicit_rerun_fresh_id_is_not_a_duplicate(self):
        r=Admission('w')
        self.assertEqual(r.receive('w','i','execute','A'),'admitted')
        self.assertEqual(r.receive('w','j','execute','A'),'admitted')
        self.assertEqual(len(r.jobs),2)
    def test_wrong_nonce_cannot_consume_current_session_id(self):
        r=Admission('w')
        self.assertEqual(r.receive('old','i','execute','A'),'wrong_nonce')
        self.assertEqual(r.used,set())
        self.assertEqual(r.receive('w','i','execute','A'),'admitted')
    def test_serialized_competing_arrivals_allocate_once(self):
        for arrival in permutations(('A','B','C')):
            r=Admission('w')
            outcomes=[r.receive('w','same','execute',x) for x in arrival]
            self.assertEqual(outcomes.count('admitted'),1)
            self.assertEqual(len(r.jobs),1)
            self.assertEqual(r.jobs[0][1],arrival[0])
    def test_source_free_status_request_never_executes(self):
        r=Admission('w'); r.receive('w','i','execute','A')
        self.assertEqual(r.receive('w','status','commit_status','i'),'admitted')
        self.assertEqual(r.jobs,[('i','A')])

if __name__=='__main__': unittest.main(verbosity=2)
