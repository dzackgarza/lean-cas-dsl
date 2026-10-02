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
        command=['docker','run','--name',container,'--rm','--network','none','--read-only','--cap-drop','ALL',
                 '--security-opt','no-new-privileges','--user','65534:65534',
                 '--pids-limit','32','--memory','256m','--cpus','1',
                 '--mount',f'type=bind,src={source},dst=/candidate,readonly',
                 '--tmpfs','/tmp:rw,noexec,nosuid,size=16m',image,*arguments]
        chunks = {'stdout': [], 'stderr': []}
        count = 0
        failure = None
        process = subprocess.Popen(command, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        deadline = time.monotonic() + timeout
        try:
            with selectors.DefaultSelector() as selector:
                for label, pipe in (('stdout',process.stdout),('stderr',process.stderr)):
                    os.set_blocking(pipe.fileno(),False)
                    selector.register(pipe,selectors.EVENT_READ,label)
                while selector.get_map():
                    remaining = deadline-time.monotonic()
                    if remaining <= 0:
                        failure = 'process_timeout'
                        break
                    for key, _ in selector.select(min(remaining,0.1)):
                        data = os.read(key.fileobj.fileno(),65536)
                        if not data:
                            selector.unregister(key.fileobj)
                            continue
                        available = max(output_limit-count,0)
                        chunks[key.data].append(data[:available])
                        count += min(len(data),available)
                        if len(data)>available:
                            failure = 'output_limit'
                            break
                    if failure:
                        break
            if failure:
                process.kill()
            process.wait(timeout=5)
        finally:
            if process.poll() is None:
                process.kill()
                process.wait()
            process.stdout.close()
            process.stderr.close()
            subprocess.run(['docker','rm','--force',container],capture_output=True)
        return {'revision':revision.commit,'runtime':image,'arguments':list(arguments),
                'container':container,'returncode':process.returncode,'operation_failure':failure,
                'stdout':b''.join(chunks['stdout']).decode(errors='replace'),
                'stderr':b''.join(chunks['stderr']).decode(errors='replace')}
