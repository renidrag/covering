"""Atomic records and an operating-system-owned workspace lock."""
from contextlib import contextmanager
import json
import os
from pathlib import Path
import tempfile


def write_json(path, value):
    path = Path(path)
    path.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.NamedTemporaryFile(mode='w', dir=path.parent, delete=False) as stream:
        temporary = Path(stream.name)
        try:
            json.dump(value, stream, indent=2)
            stream.write('\n')
            stream.flush()
            os.fsync(stream.fileno())
        except BaseException:
            temporary.unlink(missing_ok=True)
            raise
    try:
        temporary.replace(path)
    finally:
        temporary.unlink(missing_ok=True)


@contextmanager
def workspace_lock():
    import fcntl

    path = Path('results/.workflow.lock')
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open('a+') as stream:
        try:
            fcntl.flock(stream, fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError:
            stream.seek(0)
            owner = stream.read().strip() or 'another command'
            raise ValueError(f'Workspace is busy ({owner}). Use ./covering status.') from None
        try:
            stream.seek(0)
            stream.truncate()
            stream.write(f'PID {os.getpid()}')
            stream.flush()
            yield
        finally:
            fcntl.flock(stream, fcntl.LOCK_UN)
