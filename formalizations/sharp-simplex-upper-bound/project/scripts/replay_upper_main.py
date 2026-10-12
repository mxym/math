#!/usr/bin/env python3
"""The old incremental entry is replaced by full fresh 123-module verification.
Use the arguments documented in ../../VERIFICATION.md. No cache-only owned mode.
The previous default-20 implementation is archived for historical evidence only.
"""
from pathlib import Path
import os,sys
sys.dont_write_bytecode=True
entry=Path(__file__).resolve().parents[2]/'scripts/verify.py'
os.execv(sys.executable,[sys.executable,'-B',str(entry),*sys.argv[1:]])
