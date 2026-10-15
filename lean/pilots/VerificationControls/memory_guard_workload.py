"""Small, bounded process-tree workloads for the RSS watchdog controls."""
import argparse
import json
import os
from pathlib import Path
import subprocess
import sys
import time

p = argparse.ArgumentParser()
p.add_argument('--mib', type=int, default=0)
p.add_argument('--children', type=int, default=0)
p.add_argument('--child-mib', type=int, default=0)
p.add_argument('--seconds', type=float, default=0.15)
p.add_argument('--exit-code', type=int, default=0)
p.add_argument('--churn', type=int, default=0)
p.add_argument('--detach', action='store_true')
p.add_argument('--state', type=Path)
a = p.parse_args()
assert 0 <= a.mib <= 64 and 0 <= a.child_mib <= 64 and 0 <= a.children <= 2
assert 0 <= a.seconds <= 8 and 0 <= a.churn <= 16
memory = bytearray(a.mib * 1024**2)
for offset in range(0, len(memory), 4096):
    memory[offset] = 1
children = [subprocess.Popen([sys.executable, __file__, '--mib', str(a.child_mib),
                              '--seconds', str(a.seconds)]) for _ in range(a.children)]
if a.state:
    a.state.write_text(json.dumps({'group': os.getpgrp(),
                                  'pids': [os.getpid(), *(c.pid for c in children)]}) + '\n')
if not a.detach:
    for _ in range(a.churn):
        subprocess.run([sys.executable, '-c', 'pass'], check=True)
    time.sleep(a.seconds)
    for child in children:
        child.wait()
raise SystemExit(a.exit_code)
