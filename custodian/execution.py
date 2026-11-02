"""Credential-free candidate process boundary; replies remain untrusted data."""
import io
import re
import subprocess
import tarfile
import tempfile
import uuid
import os
import selectors
import time
from pathlib import Path
from controller import Revision, git


def _collect(process, chunks, deadline, output_limit, *, drain=False):
    """Retain bounded output under one absolute deadline; cleanup may discard excess."""
    count = sum(len(data) for values in chunks.values() for data in values)
    overflowed = False
    with selectors.DefaultSelector() as selector:
        for label, pipe in (('stdout',process.stdout),('stderr',process.stderr)):
            if pipe is not None:
                os.set_blocking(pipe.fileno(),False)
                selector.register(pipe,selectors.EVENT_READ,label)
        while selector.get_map():
            remaining = deadline-time.monotonic()
            if remaining <= 0:
                return 'process_timeout'
            for key, _ in selector.select(min(remaining,0.1)):
                data = os.read(key.fileobj.fileno(),65536)
                if not data:
                    selector.unregister(key.fileobj)
                    continue
                available = max(output_limit-count,0)
                if available:
                    chunks[key.data].append(data[:available])
                    count += min(len(data),available)
                if len(data)>available:
                    overflowed = True
                    if not drain:
                        return 'output_limit'
    try:
        process.wait(timeout=max(deadline-time.monotonic(),0))
    except subprocess.TimeoutExpired:
        return 'process_timeout'
    return 'output_limit' if overflowed else None


def _close_process(process, deadline):
    try:
        if process.poll() is None:
            process.kill()
        try:
            process.wait(timeout=max(deadline-time.monotonic(),0))
            return True
        except subprocess.TimeoutExpired:
            return False
    finally:
        for pipe in (process.stdout,process.stderr):
            if pipe is not None:
                pipe.close()


def _created_id(cidfile):
    """Only the trusted create client can write this unmounted acknowledgement."""
    try:
        with cidfile.open('rb') as stream:
            value = stream.read(65)
    except FileNotFoundError:
        return None
    return value.decode('ascii') if re.fullmatch(rb'[0-9a-f]{64}',value) else None


def execute(revision: Revision, image: str, arguments: tuple[str, ...], timeout=60, output_limit=16*1024*1024):
    """Trusted runner chooses immutable runtime and arguments, never an author tool field.

    Mount only the exact committed candidate tree. No Git metadata, accepted assertions,
    signing keys, credential files, Docker socket or network is available to candidate.
    """
    if not re.fullmatch(r'sha256:[0-9a-f]{64}',image):
        raise ValueError('immutable runtime image identity required')
    with tempfile.TemporaryDirectory(prefix='custodian-execution-') as tmp:
        source=Path(tmp)/'candidate';source.mkdir()
        archive=git(revision.repository,'archive','--format=tar',revision.commit)
        with tarfile.open(fileobj=io.BytesIO(archive)) as tar:
            if any(member.issym() or member.islnk() for member in tar.getmembers()):
                raise ValueError('linked candidate tree is unsupported')
            tar.extractall(source,filter='data')
        # Readability by the unprivileged container user is explicit and contains source only.
        Path(tmp).chmod(0o755)
        source.chmod(0o755)
        for path in source.rglob('*'):
            path.chmod(0o755 if path.is_dir() else 0o644)
        container = 'custodian-execution-' + uuid.uuid4().hex
        cidfile = Path(tmp)/'container.id'
        command=['docker','create','--name',container,'--cidfile',str(cidfile),
                 '--network','none','--read-only','--cap-drop','ALL',
                 '--security-opt','no-new-privileges','--user','65534:65534',
                 '--pids-limit','32','--memory','256m','--cpus','1',
                 '--mount',f'type=bind,src={source},dst=/candidate,readonly',
                 '--tmpfs','/tmp:rw,noexec,nosuid,size=16m',image,*arguments]
        chunks = {'stdout': [], 'stderr': []}
        failure = None
        process = None
        container_id = None
        # Creation cannot execute candidate code. Its ID is host control data,
        # never mixed into the candidate's bounded stdout or exposed as a mount.
        creator = subprocess.Popen(command,stdout=subprocess.DEVNULL,stderr=subprocess.PIPE)
        deadline = time.monotonic()+timeout
        cleanup = {'container_id':None, 'failure':None}
        try:
            failure = _collect(creator,chunks,deadline,output_limit)
            if failure is None and creator.returncode == 0:
                container_id = _created_id(cidfile)
                if time.monotonic() >= deadline:
                    failure = 'process_timeout'
                elif container_id is not None:
                    process = subprocess.Popen(['docker','start','--attach',container_id],
                                               stdout=subprocess.PIPE,stderr=subprocess.PIPE)
                    failure = _collect(process,chunks,deadline,output_limit)
        finally:
            process_failure = failure
            # The original five-second cleanup allowance includes late creation
            # acknowledgement, client reaping and removal; no stage resets it.
            cleanup_deadline = time.monotonic()+5
            container_id = container_id or _created_id(cidfile)
            if creator.poll() is None and container_id is None:
                # Do not kill a create request and mistake "not found" for an
                # absent container. It can finish only a stopped container here.
                _collect(creator,chunks,cleanup_deadline,output_limit,drain=True)
                container_id = _created_id(cidfile)
            cleanup['container_id'] = container_id
            for client in (process,creator):
                if client is not None and not _close_process(client,cleanup_deadline):
                    cleanup['failure'] = 'client_reap_timeout'
            if container_id is None:
                cleanup['failure'] = 'creation_unacknowledged'
            else:
                # Diagnostic output shares the remaining original byte budget;
                # it cannot truncate already retained candidate output or grow
                # an unbounded communicate() buffer. Excess is drained, not kept.
                retained = sum(len(data) for values in chunks.values() for data in values)
                cleanup_chunks = {'stdout':[], 'stderr':[]}
                removed = subprocess.Popen(['docker','rm','--force',container_id],
                                           stdout=subprocess.PIPE,stderr=subprocess.PIPE)
                try:
                    collected = _collect(removed,cleanup_chunks,cleanup_deadline,
                                         max(output_limit-retained,0),drain=True)
                finally:
                    reaped = _close_process(removed,cleanup_deadline)
                cleanup.update(returncode=removed.returncode,
                    output_truncated=collected == 'output_limit',
                    stdout=b''.join(cleanup_chunks['stdout']).decode(errors='replace'),
                    stderr=b''.join(cleanup_chunks['stderr']).decode(errors='replace'))
                if collected == 'process_timeout':
                    cleanup['failure'] = 'removal_timeout'
                elif not reaped:
                    cleanup['failure'] = 'removal_reap_timeout'
                elif removed.returncode:
                    cleanup['failure'] = 'removal_failed'
            # A timeout does not conceal a second, unresolved cleanup failure.
            if cleanup['failure'] is not None:
                failure = 'container_cleanup'
        return {'revision':revision.commit,'runtime':image,'arguments':list(arguments),
                'container':container,
                'returncode':process.returncode if process is not None else None,
                'creation_returncode':creator.returncode,
                'operation_failure':failure,'process_failure':process_failure,'cleanup':cleanup,
                'stdout':b''.join(chunks['stdout']).decode(errors='replace'),
                'stderr':b''.join(chunks['stderr']).decode(errors='replace')}
