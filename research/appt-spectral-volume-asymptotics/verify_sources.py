#!/usr/bin/env python3
from pathlib import Path
import hashlib,json
ROOT=Path(__file__).resolve().parent
pins=json.loads((ROOT/'SOURCE_HASHES.json').read_text())
for name,expected in pins.items():
 p=ROOT/name
 if not p.is_file() or hashlib.sha256(p.read_bytes()).hexdigest()!=expected:
  raise SystemExit('SOURCE_HASH_MISMATCH: '+name)
print('SOURCE_HASHES_PASS',len(pins),'files')
