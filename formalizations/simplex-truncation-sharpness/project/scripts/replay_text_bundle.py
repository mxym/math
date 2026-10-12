#!/usr/bin/env python3
"""Reconstruct exact authorized UTF-8 bundle parts downloaded from the private Page."""
from pathlib import Path
import argparse
import hashlib
import json

parser = argparse.ArgumentParser()
parser.add_argument('parts', nargs='+', type=Path)
parser.add_argument('--out', type=Path, required=True)
args = parser.parse_args()
args.out.mkdir(parents=True, exist_ok=True)
seen = set()
chunks = {}
for part in args.parts:
    for item in json.loads(part.read_text())['files']:
        relative = Path(item['path'])
        if relative.is_absolute() or '..' in relative.parts:
            raise RuntimeError('Unsafe bundle path')
        entry = chunks.setdefault(item['path'], {'record': item, 'segments': {}})
        for key in ['bytes', 'sha256', 'mode', 'chunk_count']:
            if entry['record'][key] != item[key]:
                raise RuntimeError('Inconsistent file metadata')
        if item['chunk_index'] in entry['segments']:
            raise RuntimeError('Duplicate bundle segment')
        entry['segments'][item['chunk_index']] = item['text']
for name, entry in chunks.items():
        item = entry['record']
        count = item['chunk_count']
        if set(entry['segments']) != set(range(count)):
            raise RuntimeError('Missing file segment: ' + name)
        seen.add(name)
        data = ''.join(entry['segments'][i] for i in range(count)).encode('utf-8')
        if len(data) != item['bytes'] or hashlib.sha256(data).hexdigest() != item['sha256']:
            raise RuntimeError('Part file digest mismatch: ' + item['path'])
        target = args.out / name
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(data)
        target.chmod(item['mode'])
for item in json.loads((args.out / 'SOURCE_FILES_SHA256.json').read_text()):
    target = args.out / item['path']
    if not target.is_file() or hashlib.sha256(target.read_bytes()).hexdigest() != item['sha256']:
        raise RuntimeError('Reconstructed full manifest mismatch')
print(f'EXACT_TEXT_BUNDLE_REPLAY_PASS {len(seen)} files')
