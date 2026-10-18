#!/usr/bin/env python3
"""Separate exact-format local reader; never runs or modifies the Lean producer."""
from pathlib import Path
import argparse,json,sys
ROOT=Path(__file__).resolve().parent
BASE=ROOT.parents[1]
sys.path.insert(1,str(BASE))
import reproduce as a
from audit_runtime import configure
from evidence_v2 import verify_run
SOURCE_MANIFEST_SHA256='582008527e7b22047496b0e0a462a96415575047d804d1340f11021034b46f41'


def check_reader():
    manifest=a.readj(ROOT/'READER_HASHES.json')
    actual={p.name:a.sha(p)for p in ROOT.iterdir()if p.is_file()and p.name!='READER_HASHES.json'}
    if manifest['reader_inputs']!=actual or manifest['mathematical_source_manifest_sha256']!=SOURCE_MANIFEST_SHA256 or a.sha(BASE/'SOURCE_HASHES.json')!=SOURCE_MANIFEST_SHA256:raise RuntimeError('Separate local reader/source binding changed')
    a.check_binding()
    return manifest


def verify(directory):
    a.check_execution_inputs(False);runtime=configure(False);manifest=check_reader()
    out=Path(directory).resolve()
    if not out.is_relative_to((BASE/'verification').resolve()):raise RuntimeError('Local evidence is outside owned D-backed output')
    pre=a.readj(out/'PRE_AUDIT.json')
    if pre['binaries']!=runtime['actual_executables']:raise RuntimeError('Recorded tool identities differ from current verified D-pinned executables')
    result=verify_run(out,'D_BACKED_STORAGE_VERIFIED')
    return dict(result,reader_revision='raw-resource-local-reader-v2',reader_manifest_sha256=a.sha(ROOT/'READER_HASHES.json'),original_mathematical_source_manifest_sha256=SOURCE_MANIFEST_SHA256,additional_Lean_or_kernel_execution=False)

if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('directory');args=ap.parse_args();print(json.dumps(verify(args.directory),indent=2))
