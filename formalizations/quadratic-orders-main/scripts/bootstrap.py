#!/usr/bin/env python3
"""Complete fresh verification with already provisioned pinned dependencies."""
from pathlib import Path
import os,sys
sys.dont_write_bytecode=True
from release_integrity import validated_snapshot
ROOT=Path(__file__).resolve().parents[1]
validated_snapshot(ROOT)
os.execv(sys.executable,[sys.executable,'-B',str(ROOT/'scripts/verify.py'),*sys.argv[1:]])
