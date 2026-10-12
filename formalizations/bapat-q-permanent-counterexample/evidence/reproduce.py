#!/usr/bin/env python3
"""Validate the compact bundle, then configure and invoke the preserved verifier."""
import argparse
import gzip
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import sys

ROOT = Path(__file__).resolve().parent

def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def check():
    lines = (ROOT/'SHA256SUMS').read_text().splitlines()
    paths = set()
    for line in lines:
        expected, rel = line.split('  ', 1)
        path = (ROOT/rel).resolve(strict=True)
        if not path.is_relative_to(ROOT) or digest(path) != expected:
            raise RuntimeError('BUNDLE_HASH_MISMATCH: '+rel)
        paths.add(path)
    actual = {p.resolve() for p in ROOT.rglob('*') if p.is_file() and p != ROOT/'SHA256SUMS'}
    if actual != paths:
        raise RuntimeError('BUNDLE_FILE_LIST_MISMATCH')
    mappings = json.loads((ROOT/'provenance/file-map.json').read_text())
    for entry in mappings:
        if entry.get('decompressed_sha256'):
            data = gzip.decompress((ROOT/entry['target']).read_bytes())
            if hashlib.sha256(data).hexdigest() != entry['original_sha256']:
                raise RuntimeError('LOSSLESS_COMPRESSION_MISMATCH')
    case = json.loads((ROOT/'formalization/verify.json').read_text())
    if set(case['audit_modules']) != set(case['modules']):
        raise RuntimeError('OWNED_MODULE_EXCLUSION')
    for info in case['modules'].values():
        if digest(ROOT/'formalization/sources'/info['path']) != info['sha256']:
            raise RuntimeError('SOURCE_HASH_MISMATCH')
    print(json.dumps({'bundle_files_verified':len(paths),'sources_verified':len(case['modules']),
                      'compressed_evidence_lossless':True}),flush=True)

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--check-only', action='store_true')
    ap.add_argument('--doctor-only', action='store_true')
    ap.add_argument('--toolchain', type=Path)
    ap.add_argument('--packages-root', type=Path)
    ap.add_argument('--work-dir', type=Path)
    args=ap.parse_args()
    check()
    if args.check_only: return
    if not all([args.toolchain,args.packages_root,args.work_dir]):
        ap.error('Provide --toolchain, --packages-root and --work-dir, or use --check-only')
    toolchain=args.toolchain.resolve(strict=True)
    packages=args.packages_root.resolve(strict=True)
    work=args.work_dir.resolve()
    if work.is_relative_to(ROOT): ap.error('Work directory must be outside the immutable evidence bundle')
    work.mkdir(parents=True,exist_ok=False)
    verifier=work/'verifier'
    shutil.copytree(ROOT/'verifier',verifier)
    (verifier/'locks').mkdir()
    env_path=verifier/'config/environment.json'
    env=json.loads(env_path.read_text())
    env.update(toolchain_path=str(toolchain), packages_root=str(packages),cache_root=str(work/'cache'))
    env_path.write_text(json.dumps(env,indent=2)+'\n')
    case=json.loads((ROOT/'formalization/verify.json').read_text())
    case['source_dir']=str(ROOT/'formalization/sources')
    case_path=work/'verify.json'
    case_path.write_text(json.dumps(case,indent=2)+'\n')
    action=['doctor'] if args.doctor_only else ['verify',str(case_path)]
    result=subprocess.run([sys.executable,str(verifier/'bin/leanctl.py'),*action],check=False)
    raise SystemExit(result.returncode)

if __name__=='__main__': main()
