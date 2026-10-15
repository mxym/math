"""Copy the own research controls to a separate replay directory."""
from pathlib import Path
import argparse
import gzip
import hashlib
import json
import shutil


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--output', required=True, type=Path)
    args = parser.parse_args()
    source = Path(__file__).resolve().parent
    output = args.output.resolve()
    if output == source:
        raise ValueError('Use a separate replay directory')
    output.mkdir(parents=True, exist_ok=True)
    copied = 0
    for p in source.iterdir():
        if not p.is_file():
            continue
        target = output / p.name
        if target.exists() and target.read_bytes() != p.read_bytes():
            raise ValueError('Refusing to replace different replay file: ' + str(target))
        if not target.exists():
            shutil.copyfile(p, target)
        copied += 1
    entries = json.loads((source / 'ARCHIVE_MANIFEST.json').read_text())['archives']
    for entry in entries:
        packed = (source / entry['archive']).read_bytes()
        if hashlib.sha256(packed).hexdigest() != entry['archive_sha256']:
            raise ValueError('Archive hash mismatch')
        raw = gzip.decompress(packed)
        if hashlib.sha256(raw).hexdigest() != entry['raw_sha256']:
            raise ValueError('Raw hash mismatch')
        target = output / entry['raw_path']
        target.parent.mkdir(parents=True, exist_ok=True)
        if target.exists() and target.read_bytes() != raw:
            raise ValueError('Refusing to replace different raw file')
        target.write_bytes(raw)
    print(json.dumps({'copied_root_files': copied, 'verified_archives': len(entries),
                      'output': str(output), 'scope': 'Own controls; no independent review.'}))


if __name__ == '__main__':
    main()
