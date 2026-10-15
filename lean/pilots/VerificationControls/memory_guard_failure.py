"""Inject one inspection failure after a controlled child group has started."""
from pathlib import Path
import sys
import time

sys.path.insert(0, str(Path(__file__).resolve().parents[3] / 'scripts'))
import run_memory_guard as guard

state = Path(sys.argv[1])


def fail_inspection(_self, _group):
    deadline = time.monotonic() + 2
    while not state.exists() and time.monotonic() < deadline:
        time.sleep(0.01)
    raise guard.InspectionError('controlled inspection failure')


inspector = guard.make_inspector()
type(inspector).sample = fail_inspection
raise SystemExit(guard.main(sys.argv[2:]))
