#!/usr/bin/env python3
"""Validate and invoke complete verification with already provisioned exact dependencies.
No automatic download, no incremental-owned mode, and no mutation of dependencies.
"""
from pathlib import Path
import os,sys
sys.dont_write_bytecode=True
from release_integrity import validated_snapshot
ROOT=Path(__file__).resolve().parents[1]
validated_snapshot(ROOT)
os.execv(sys.executable,[sys.executable,'-B',str(ROOT/'scripts/verify.py'),*sys.argv[1:]])
