#!/usr/bin/env python3
"""Fresh sequential compilation of the structural GPPT proof and Stanton.

Run through `lake -d lean env python3 scripts/recheck_gppt.py`. Every project
module is recompiled in a temporary tree. Only vendored dependency caches are
reused. The larger finite completion proof has a measured 180-second allowance;
all other modules have 60 seconds. Use the outer logged RSS watchdog as usual.
"""
from recheck_stanton import recheck


if __name__ == '__main__':
    recheck(entry='CoveringDesigns.C12_6_3', audit='lean/audits/C12_6_3.lean',
            record_path='results/gppt-structural-fresh.json',
            prefix='gppt-recheck-', memory_mib=6144,
            long_checks={'CoveringDesigns.C12_6_3.Structural.CompletionChecks': 180})
