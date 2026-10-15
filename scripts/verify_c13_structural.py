#!/usr/bin/env python3
"""Verify the public C(13,7,4)=30 theorem and its prerequisites serially.

Uses the same bounded compiler, dependency checks, manifests, and fingerprints
as the whole-library audit. Dependencies must already be installed locally.
Run from the project root; --memory-mib and timeout options are supported.
"""
from audit_library import main


if __name__ == '__main__':
    main(only_c13=True)
