#!/usr/bin/env python3
"""Trusted revision-bound dispatch and acceptance. No candidate imports or execution.

The launcher holds Controller; workers receive only Worker. Deployment must isolate
launcher credentials: Python object visibility is not an OS authority boundary.
"""
from dataclasses import dataclass
from pathlib import Path
import hashlib
import json
import subprocess
import os
import re


def git(repo, *args):
    return subprocess.run(['git', '-c', 'core.hooksPath=/dev/null', '-C', str(repo), *args],
                          env={'PATH':os.defpath,'LANG':'C.UTF-8','GIT_CONFIG_NOSYSTEM':'1',
                               'GIT_CONFIG_GLOBAL':'/dev/null'},
                          check=True, capture_output=True).stdout


def canonical(value):
    return json.dumps(value, sort_keys=True, separators=(',', ':')).encode()


def verify_review_signature(data,signature,public_key,fingerprint):
    import tempfile
    with tempfile.TemporaryDirectory() as tmp:
        allowed=Path(tmp)/'allowed'
        actual=subprocess.run(['ssh-keygen','-lf',str(public_key)],check=True,capture_output=True,text=True).stdout.split()[1]
        if actual!=fingerprint:raise ValueError('review authority fingerprint mismatch')
        allowed.write_text('review '+public_key.read_text().strip()+'\n')
        subprocess.run(['ssh-keygen','-Y','verify','-f',str(allowed),'-I','review',
                        '-n','lean-cas-custodian','-s',str(signature)],
                       input=Path(data).read_bytes(),check=True,capture_output=True)


@dataclass(frozen=True)
class Revision:
    repository: Path
    commit: str

    def __post_init__(self):
        actual = git(self.repository, 'rev-parse', self.commit + '^{commit}').decode().strip()
        if actual != self.commit:
            raise ValueError('full immutable commit identity required')

    def read(self, path):
        return git(self.repository, 'show', self.commit + ':' + path)

    def files(self):
        return git(self.repository, 'ls-tree', '-r', '--name-only', self.commit).decode().splitlines()


@dataclass(frozen=True)
class AcceptedArtifact:
    revision: Revision
    path: str
    sha256: str

    @property
    def repository(self): return self.revision.repository
    @property
    def commit(self): return self.revision.commit
    def files(self): return [self.path]
    def read(self,path):
        if path != self.path: raise PermissionError('outside released public metadata artifact')
        contents=self.revision.read(path)
        if hashlib.sha256(contents).hexdigest()!=self.sha256: raise ValueError('accepted artifact digest mismatch')
        return contents


@dataclass(frozen=True)
class ArtifactSource:
    repository: Path
    commit: str
    def __post_init__(self):
        if not re.fullmatch(r'[0-9a-f]{40}',self.commit):raise ValueError('full artifact source revision required')


@dataclass(frozen=True)
class ExternalArtifact:
    revision: Revision
    artifact_file: Path
    sha256: str
    provenance: tuple
    contents: bytes

    @classmethod
    def load(cls,revision,path,digest,provenance):
        contents=path.read_bytes()
        if hashlib.sha256(contents).hexdigest()!=digest:
            raise ValueError('external release artifact digest mismatch')
        if provenance.get('mathematics')!=revision.commit:
            raise ValueError('external artifact mathematical source revision mismatch')
        return cls(revision,path,digest,tuple(sorted(provenance.items())),contents)
    @property
    def repository(self):return self.revision.repository
    @property
    def commit(self):return self.revision.commit
    def files(self):return ['public_operation_metadata.json']
    def read(self,path):
        if path!='public_operation_metadata.json':raise PermissionError('outside released artifact')
        return self.contents


def configured_input(value):
    if 'artifact_file' in value:
        source=ArtifactSource(Path(value['repository']),value['commit'])
        return ExternalArtifact.load(source,Path(value['artifact_file']),value['sha256'],value['provenance'])
    revision=Revision(Path(value['repository']),value['commit'])
    if 'path' in value:
        return AcceptedArtifact(revision,value['path'],value['sha256'])
    return revision


@dataclass(frozen=True)
class Assignment:
    obligation: str
    role: str
    requirement: bytes
    inputs: tuple


class Worker:
    """Source construction capability; no dispatch, release or approval operation."""
    def __init__(self, assignment):
        self.assignment = assignment

    def operations(self):
        return ('source', 'focused_validation', 'submit')


ROLE_INPUTS = {'formalization': ('mathematics',),
               'acceptance': ('mathematics','contract'),
               'kernel': ('mathematics','contract','acceptance'),
               'leaf': ('contract','public_metadata')}


class Controller:
    def __init__(self, requirements: Revision, accepted: dict, reviewer_key: Path,
                 reviewer_fingerprint: str, assignments: dict):
        self.requirements = requirements
        self.accepted = dict(accepted)
        self.reviewer_key = reviewer_key
        self.reviewer_fingerprint = reviewer_fingerprint
        self.decisions = {}
        # Launcher-supplied protected dispatch, inaccessible through Worker.
        self.assignments = dict(assignments)

    def assign(self, obligation):
        # Role and objective are determined by the protected plan, never worker prose.
        plan = self.requirements.read('specs/computational-core-plan.md')
        if ('`' + obligation + '`').encode() not in plan:
            raise ValueError('objective absent from governing plan')
        role = self.assignments[obligation]
        if role not in ('kernel', 'formalization', 'acceptance', 'leaf'):
            raise ValueError('unknown author role')
        if role=='leaf':
            public=self.accepted.get('public_metadata')
            if public is None:raise ValueError('leaf dispatch missing released public metadata input')
            if isinstance(public,ExternalArtifact):
                provenance=dict(public.provenance)
                if provenance.get('contract')!=self.accepted['contract'].commit:
                    raise ValueError('leaf public metadata is not the released contract tuple')
                if 'mathematics' in self.accepted and provenance.get('mathematics')!=self.accepted['mathematics'].commit:
                    raise ValueError('leaf public metadata is not the accepted mathematical tuple')
        permitted = ROLE_INPUTS[role]
        return Worker(Assignment(obligation, role, plan,
                      tuple((name, self.accepted[name]) for name in permitted)))

    def request(self, obligation, base, candidate):
        # All patches and full source come from the same immutable tuple.
        if ('`' + obligation + '`').encode() not in self.requirements.read('specs/computational-core-plan.md'):
            raise ValueError('objective absent from governing plan')
        for name, revision in base.items():
            if name not in self.accepted or revision != self.accepted[name]:
                raise ValueError('base is not the supplied accepted input')
        if set(base) != set(candidate) or set(base) != set(self.accepted):
            raise ValueError('incomplete revision tuple')
        documents = {}
        for path in self.requirements.files():
            if path in ('AGENTS.md','INTENT.md','SPEC.md', 'specs/architecture.md', 'specs/computational-core-plan.md') or path.startswith('specs/owner/'):
                documents[path] = self.requirements.read(path).decode()
        required = {'INTENT.md','SPEC.md','specs/architecture.md','specs/computational-core-plan.md',
                    'specs/owner/convergence-process.md'}
        if not required.issubset(documents) or any(not documents[p].strip() for p in required):
            raise ValueError('missing authoritative review context')
        payload = {'obligation': obligation, 'requirements_revision': self.requirements.commit,
                   'requirements': documents, 'base': {}, 'candidate': {}, 'artifacts': {}, 'source': {}, 'patches': {}}
        for name in sorted(candidate):
            a, b = base[name], candidate[name]
            if a.repository.resolve() != b.repository.resolve():
                raise ValueError('tuple repository mismatch')
            payload['base'][name] = a.commit
            payload['candidate'][name] = b.commit
            if isinstance(b,AcceptedArtifact):
                payload['artifacts'][name] = {'path':b.path,'sha256':b.sha256}
            elif isinstance(b,ExternalArtifact):
                payload['artifacts'][name] = {'artifact_file':str(b.artifact_file),'sha256':b.sha256,'provenance':dict(b.provenance)}
            if isinstance(b,ExternalArtifact):
                import difflib
                before=a.read('public_operation_metadata.json').decode(errors='replace').splitlines(keepends=True) if isinstance(a,ExternalArtifact) else []
                after=b.contents.decode(errors='replace').splitlines(keepends=True)
                payload['patches'][name]=''.join(difflib.unified_diff(before,after,fromfile='accepted-public-metadata',tofile='candidate-public-metadata'))
                provenance=dict(b.provenance)
                if provenance.get('mathematics')!=candidate['mathematics'].commit or provenance.get('contract')!=candidate['contract'].commit:
                    raise ValueError('public artifact incompatible with mathematical/contract tuple')
            else:
                payload['patches'][name] = git(b.repository, 'diff', '--no-ext-diff', '--no-textconv', a.commit, b.commit).decode(errors='replace')
            payload['source'][name] = {p: b.read(p).decode(errors='replace') for p in b.files()}
        payload['request_id'] = hashlib.sha256(canonical(payload)).hexdigest()
        return payload

    def advance(self, request, decision_file, signature):
        # Existing SSH review identity is the sole source of independent approval.
        bound = dict(request)
        request_id = bound.pop('request_id')
        if hashlib.sha256(canonical(bound)).hexdigest() != request_id:
            raise ValueError('review request changed after assembly')
        if request['requirements_revision'] != self.requirements.commit:
            raise ValueError('stale requirement revision')
        # Reconstruct from the protected revisions as well as checking the envelope hash.
        # A caller cannot attach invented source/requirements to real revision identities.
        base = {name:self.accepted[name] for name in request['base']}
        candidate = {}
        for name,commit in request['candidate'].items():
            descriptor=request.get('artifacts',{}).get(name)
            revision=(ArtifactSource if descriptor and 'artifact_file' in descriptor else Revision)(self.accepted[name].repository,commit)
            if descriptor and 'artifact_file' in descriptor:
                candidate[name]=ExternalArtifact.load(revision,Path(descriptor['artifact_file']),descriptor['sha256'],descriptor['provenance'])
            else:
                candidate[name]=AcceptedArtifact(revision,descriptor['path'],descriptor['sha256']) if descriptor else revision
        if self.request(request['obligation'], base, candidate) != request:
            raise ValueError('request is not the revision-derived snapshot')
        for name, revision in request['base'].items():
            if revision != self.accepted[name].commit:
                raise ValueError('stale accepted inputs')
        verify_review_signature(decision_file,signature,self.reviewer_key,self.reviewer_fingerprint)
        decision = json.loads(Path(decision_file).read_text())
        if decision['request_id'] != request['request_id'] or decision['outcome'] != 'no_blocking_finding':
            raise ValueError('decision does not accept this snapshot')
        if decision.get('findings'):
            raise ValueError('blocking findings cannot advance inputs')
        self.decisions[request['request_id']] = decision
        advancement=dict(request['candidate'])
        for name,artifact in request.get('artifacts',{}).items():
            advancement[name]=dict(artifact,commit=request['candidate'][name])
        return advancement

    def propose_acceptance(self, worker, candidate: Revision):
        """Independent author's source channel. Proposal is data, never admission."""
        if worker.assignment.role != 'acceptance':
            raise PermissionError('acceptance proposal belongs to the acceptance author')
        base = self.accepted['acceptance']
        # Construction main can contain unrelated integrated source. Author submission
        # is this commit, while assessment still compares ALL acceptance inputs to the
        # accepted base. A merge submission needs explicit independently assembled context.
        parents = git(candidate.repository, 'rev-list', '--parents', '-n', '1', candidate.commit).decode().split()[1:]
        if len(parents) != 1:
            raise ValueError('submission requires one source parent')
        changed = git(candidate.repository, 'diff', '--name-only', parents[0],
                      candidate.commit).decode().splitlines()
        if not changed or any(not p.startswith('tests/acceptance/') for p in changed):
            raise ValueError('acceptance proposal must change only its assigned repository paths')
        tuple_candidate=dict(self.accepted)
        tuple_candidate['acceptance']=candidate
        return self.request(worker.assignment.obligation,self.accepted,tuple_candidate)


def main():
    """Public submission endpoint: emits untrusted source identity, never a decision."""
    import argparse
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest='operation', required=True)
    submit = sub.add_parser('submit-acceptance')
    submit.add_argument('--repository', type=Path, required=True)
    submit.add_argument('--candidate', required=True)
    args = parser.parse_args()
    revision = Revision(args.repository, args.candidate)
    parents = git(revision.repository, 'rev-list', '--parents', '-n', '1', revision.commit).decode().split()[1:]
    if len(parents) != 1:
        parser.error('submission requires one source parent')
    changed = git(revision.repository, 'diff', '--name-only', parents[0], revision.commit).decode().splitlines()
    if not changed or any(not p.startswith('tests/acceptance/') for p in changed):
        parser.error('acceptance source submission must change only tests/acceptance/')
    print(json.dumps({'kind': 'acceptance_source_submission', 'candidate': revision.commit,
                      'source_parent': parents[0], 'changed_paths': changed}, sort_keys=True))
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
