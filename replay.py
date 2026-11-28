#!/usr/bin/env python3
"""Replay the isolated eight-point finite certificate using standard Python only."""
from pathlib import Path
import base64, gzip, hashlib, subprocess, sys
if not __debug__ or sys.flags.optimize: raise RuntimeError("run without -O")
P = Path(__file__).resolve().parent
for line in (P / "SHA256SUMS").read_text().splitlines():
    sha, name = line.split("  ", 1)
    if hashlib.sha256((P / name).read_bytes()).hexdigest() != sha:
        raise ValueError("manifest mismatch: " + name)
packed = base64.b64decode("".join((P / "closed-box-witnesses.gz.b64").read_text().split()), validate=True)
raw = gzip.decompress(packed)
if len(raw) != 235094 or hashlib.sha256(raw).hexdigest() != "5652e646f8cddc56e010cc04844a0bf4e27b62b7821f736992c26a280f3ef136":
    raise ValueError("wrong frozen witness")
subprocess.run([sys.executable, str(P / "independent-even-eight-boxes.py")], input=raw, check=True)
subprocess.run([sys.executable, str(P / "independent-even-eight-graphs.py")], check=True)
print("PASS: frozen exact boxes and independent graph enumeration", flush=True)
