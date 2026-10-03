#!/usr/bin/env python3
"""Role-specific MCP transport owned by the trusted launcher.

Run only from the protected controller deployment. `--configuration` is a trusted
launch configuration, not an author-supplied tool argument. Author sessions receive
this server's tools only; deployment must separately remove all authority credentials
and other write/commission connectors. This does not restrict an ambient shell.
"""
import argparse
import json
import sys
import subprocess
from pathlib import Path
from controller import Controller, Revision, configured_input, ROLE_INPUTS, git


SCHEMA = {'type': 'object', 'properties': {'path': {'type': 'string'}},
          'required': ['path'], 'additionalProperties': False}


class RoleServer:
    def __init__(self, controller, obligation, source_repository, validation=None):
        self.controller = controller
        self.worker = controller.assign(obligation)
        self.repository = source_repository.resolve()
        self.role = self.worker.assignment.role
        self.inputs = dict(self.worker.assignment.inputs)
        self.validation = validation

    def tools(self):
        tools = [
            {'name': 'read_assigned_input', 'description': 'Read an assigned accepted revision; no candidate input.',
             'inputSchema': {'type': 'object', 'properties': {'input': {'type':'string', 'enum':list(self.inputs)}, 'path': {'type':'string'}}, 'required':['input','path'], 'additionalProperties':False}},
            {'name':'read_source','description':'Read assigned mutable source, never governing or other-role files.',
             'inputSchema':SCHEMA},
            {'name':'list_source','description':'List assigned mutable source paths.',
             'inputSchema':{'type':'object','properties':{},'additionalProperties':False}},
            {'name': 'write_source', 'description': 'Write source in the assigned repository and role paths.',
             'inputSchema': {'type':'object','properties':{'path':{'type':'string'},'content':{'type':'string'}},'required':['path','content'],'additionalProperties':False}},
            {'name': 'submit_source', 'description': 'Submit an immutable source identity for independent assessment. Never admits.',
             'inputSchema': {'type':'object','properties':{'candidate':{'type':'string'}},'additionalProperties':False}},
        ]
        if self.validation is not None:
            tools.append({'name':'validate_source','description':'Run launcher-configured focused validation without authority credentials; does not accept.',
                          'inputSchema':{'type':'object','properties':{'candidate':{'type':'string'}},'required':['candidate'],'additionalProperties':False}})
        return tools

    def permitted(self, path):
        p = Path(path)
        if p.as_posix() != path or '\\' in path:
            return False
        if p.is_absolute() or '..' in p.parts or any(part in p.parts for part in ('.git','.lake','.gitattributes','.gitmodules','.lfsconfig')):
            return False
        # These paths judge or configure authoring; no deployed author role writes them.
        # Authorized construction corrections use the orchestrator's source operation,
        # never a kernel-worker authority grant.
        if path.startswith(('custodian/', '.github/', 'specs/owner/', 'scripts/', 'CasAcceptance/')) or path in (
                'AGENTS.md', 'INTENT.md', 'SPEC.md', 'CasAcceptance.lean', 'justfile', 'lakefile.lean',
                'lakefile.toml', 'lean-toolchain', 'specs/architecture.md',
                'specs/computational-core-plan.md'):
            return False
        if self.role == 'acceptance':
            return path.startswith('tests/acceptance/')
        if self.role == 'kernel':
            return not path.startswith(('tests/acceptance/', 'LeanCategories/', 'CasLeaves/'))
        if self.role == 'formalization':
            return not path.startswith(('CasCatalogue/', 'CasAcceptance/', 'tests/acceptance/', 'CasLeaves/'))
        return not path.endswith('.lean') and not path.startswith(('LeanCategories/', 'tests/acceptance/'))

    def call(self, name, args):
        if name == 'read_assigned_input':
            if set(args) != {'input', 'path'}:
                raise ValueError('invalid read arguments')
            revision = self.inputs[args['input']]
            if args['path'] not in revision.files():
                raise ValueError('not a tracked assigned input')
            return revision.read(args['path']).decode(errors='replace')
        if name == 'list_source':
            if args: raise ValueError('list takes no author arguments')
            paths=git(self.repository,'ls-files','--cached','--others','--exclude-standard').decode().splitlines()
            return json.dumps(sorted(p for p in set(paths) if self.permitted(p)))
        if name == 'read_source':
            if set(args) != {'path'} or not self.permitted(args['path']): raise PermissionError('outside assigned source')
            target=self.repository/args['path']
            if target.resolve()!=target or not target.is_file() or target.stat().st_nlink!=1:
                raise PermissionError('source read requires one regular unlinked file')
            return target.read_text()
        if name == 'write_source':
            if set(args) != {'path', 'content'} or not self.permitted(args['path']):
                raise PermissionError('outside assigned source authority')
            target = self.repository / args['path']
            if target.resolve()!=target or (target.exists() and (not target.is_file() or target.stat().st_nlink!=1)):
                raise PermissionError('source write requires one regular unlinked path')
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_text(args['content'])
            return 'source written; no acceptance or publication'
        if name == 'validate_source' and self.validation is not None:
            if set(args) != {'candidate'}:
                raise ValueError('invalid validation arguments')
            from execution import execute
            revision = Revision(self.repository,args['candidate'])
            return json.dumps(execute(revision,self.validation['runtime'],
                                      tuple(self.validation['arguments'])),sort_keys=True)
        if name == 'submit_source':
            if set(args) not in (set(),{'candidate'}):
                raise ValueError('invalid submission arguments')
            if not args:
                candidate=self.checkpoint()
            else:
                candidate=args['candidate']
            revision = Revision(self.repository, candidate)
            parents = git(self.repository, 'rev-list', '--parents', '-n', '1', revision.commit).decode().split()[1:]
            if len(parents) != 1:
                raise ValueError('one submission source parent required')
            files = git(self.repository, 'diff', '--name-only', parents[0], revision.commit).decode().splitlines()
            if not files or any(not self.permitted(p) for p in files):
                raise PermissionError('submission changes another role source')
            return json.dumps({'kind': 'source_submission', 'role': self.role,
                              'obligation': self.worker.assignment.obligation,
                              'candidate': revision.commit, 'source_parent': parents[0],
                              'changed_paths': files}, sort_keys=True)
        raise PermissionError('operation not exposed to this author')

    def checkpoint(self):
        import os, tempfile, subprocess
        paths=set(git(self.repository,'diff','HEAD','--name-only').decode().splitlines())
        paths.update(git(self.repository,'ls-files','--others','--exclude-standard').decode().splitlines())
        if not paths or any(not self.permitted(p) for p in paths):
            raise PermissionError('checkpoint contains absent or other-role changes')
        for path in paths:
            target=self.repository/path
            if target.resolve()!=target or (target.exists() and (not target.is_file() or target.stat().st_nlink!=1)):
                raise PermissionError('linked or nonregular source checkpoint is unsupported')
        base=git(self.repository,'rev-parse','HEAD').decode().strip()
        with tempfile.TemporaryDirectory(prefix='custodian-index-') as tmp:
            env=dict(PATH=os.defpath,LANG='C.UTF-8',GIT_CONFIG_NOSYSTEM='1',
                     GIT_CONFIG_GLOBAL='/dev/null',GIT_INDEX_FILE=str(Path(tmp)/'index'),
                     GIT_AUTHOR_NAME='assigned-'+self.role,GIT_AUTHOR_EMAIL='source@example.invalid',
                     GIT_COMMITTER_NAME='custodian-source',GIT_COMMITTER_EMAIL='source@example.invalid')
            def command(*args):
                return subprocess.run(['git','-c','core.hooksPath=/dev/null','-C',str(self.repository),*args],env=env,check=True,capture_output=True,text=True).stdout.strip()
            command('read-tree',base)
            command('add','--',*sorted(paths))
            tree=command('write-tree')
            candidate=command('commit-tree',tree,'-p',base,'-m','Source checkpoint for '+self.worker.assignment.obligation)
            command('update-ref','HEAD',candidate,base)
        git(self.repository,'reset',candidate,'--',*sorted(paths))
        return candidate

    def handle(self, request):
        method = request['method']
        if method == 'initialize':
            return {'protocolVersion':'2024-11-05','capabilities':{'tools':{}},
                    'serverInfo':{'name':'custodian-role-source','version':'1'}}
        if method == 'tools/list':
            return {'tools':self.tools()}
        if method == 'tools/call':
            params = request['params']
            return {'content':[{'type':'text','text':self.call(params['name'],params.get('arguments',{}))}]}
        if method == 'ping':
            return {}
        raise ValueError('unsupported operation')


def prepare_source(config):
    """Launcher creates a mutable clone from independently supplied source revision."""
    import subprocess, os
    environment={'PATH':os.defpath,'LANG':'C.UTF-8','GIT_CONFIG_NOSYSTEM':'1','GIT_CONFIG_GLOBAL':'/dev/null'}
    destination=Path(config['source_repository'])
    source=config.get('source_base')
    if source is None:
        if not (destination/'.git').exists(): raise ValueError('assigned mutable source checkout unavailable')
        return destination
    base=Revision(Path(source['repository']),source['commit'])
    if destination.resolve()==base.repository.resolve():
        raise ValueError('mutable author checkout must be separate from immutable input storage')
    if not destination.exists():
        destination.parent.mkdir(parents=True,exist_ok=True)
        subprocess.run(['git','-c','core.hooksPath=/dev/null','clone','--quiet','--no-hardlinks','--no-checkout','--',str(base.repository),str(destination)],env=environment,check=True,capture_output=True)
        git(destination,'checkout','--quiet','--detach',base.commit)
    else:
        git(destination,'merge-base','--is-ancestor',base.commit,'HEAD')
    return destination


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--configuration', type=Path, required=True)
    args = parser.parse_args()
    config = json.loads(args.configuration.read_text())
    role=config['assignments'][config['obligation']]
    if role=='leaf' and 'public_metadata' in config['accepted']:
        public=config['accepted']['public_metadata']
        if 'artifact_file' in public and public['provenance']['mathematics']!=config['accepted']['mathematics']['commit']:
            raise ValueError('leaf dispatch mathematical metadata tuple mismatch')
    revisions = {name:configured_input(config['accepted'][name]) for name in ROLE_INPUTS[role]}
    requirements = Revision(Path(config['requirements']['repository']),config['requirements']['commit'])
    controller = Controller(requirements, revisions, Path(config['reviewer_public_key']),
                            config['reviewer_fingerprint'], config['assignments'])
    server = RoleServer(controller,config['obligation'],prepare_source(config),config.get('validation'))
    for line in sys.stdin:
        request = json.loads(line)
        if 'id' not in request:
            continue
        response = {'jsonrpc':'2.0','id':request['id']}
        try:
            response['result'] = server.handle(request)
        except (ValueError, KeyError, PermissionError, OSError, RuntimeError, TypeError, subprocess.CalledProcessError) as error:
            response['error'] = {'code':-32602,'message':str(error)}
        print(json.dumps(response), flush=True)
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
