#!/usr/bin/env python3
"""Validate and repackage the completed legacy uniform component.

This is cache transport, not proof trust. Every source, imported-object hash,
object and successful bounded-build record is checked, and final theorem roots
must still be replayed from a fresh trust-zero kernel.
"""
from __future__ import annotations
import argparse
import hashlib
import json
import tarfile
from pathlib import Path, PurePosixPath
from component_cache import pack
ROOT=Path(__file__).resolve().parent.parent


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('archive',type=Path)
    args=parser.parse_args()
    if (ROOT/'.lake/build').is_symlink():
        raise RuntimeError('Refusing an external project build directory')
    seen=set()
    with tarfile.open(args.archive,'r:gz') as archive:
        for member in archive.getmembers():
            name=PurePosixPath(member.name)
            if name.is_absolute() or '..' in name.parts:
                raise RuntimeError('Unsafe legacy cache path')
            if not (name.parts[:2]==('.lake','build') or name.parts[:2]==('logs','blocks')):
                raise RuntimeError('Unexpected legacy cache prefix')
            dest=ROOT.joinpath(*name.parts)
            if not dest.resolve().is_relative_to(ROOT):
                raise RuntimeError('Legacy cache path escapes package')
            if member.isdir():
                dest.mkdir(parents=True,exist_ok=True)
            elif member.isfile():
                if member.name in seen:
                    raise RuntimeError('Duplicate legacy cache member')
                seen.add(member.name)
                payload=archive.extractfile(member)
                if payload is None:
                    raise RuntimeError('Missing legacy cache payload')
                dest.parent.mkdir(parents=True,exist_ok=True)
                dest.write_bytes(payload.read())
            else:
                raise RuntimeError('Nonregular legacy cache member')
    graph=json.loads((ROOT/'generated-UniformBuild.json').read_text())['modules']
    summary=json.loads((ROOT/'logs/blocks/SUMMARY.json').read_text())
    if summary['status']!='PASS' or summary['completed']!=len(graph) or summary['total']!=len(graph):
        raise RuntimeError('Legacy component did not complete the identical module DAG')
    if 'version 4.34.1,' not in summary['lean_version']:
        raise RuntimeError('Legacy Lean toolchain mismatch')
    objects={m:sha(ROOT/'.lake/build/lib/lean'/(m.replace('.','/')+'.olean')) for m in graph}
    for module,deps in graph.items():
        record=json.loads((ROOT/'logs/blocks'/(module+'.json')).read_text())
        source=ROOT/(module.replace('.','/')+'.lean')
        if record.get('exit_code')!=0 or record.get('timed_out') or record.get('engine')!='lake':
            raise RuntimeError('Failed or unexpected legacy build: '+module)
        if record['source_sha256']!=sha(source) or record['olean_sha256']!=objects[module]:
            raise RuntimeError('Legacy source or object hash mismatch: '+module)
        if record['dependency_oleans']!={d:objects[d] for d in deps}:
            raise RuntimeError('Legacy dependency hash mismatch: '+module)
        if record['log_sha256']!=sha(ROOT/'logs/blocks'/(module+'.log')):
            raise RuntimeError('Legacy module log mismatch: '+module)
    out=ROOT/'local-verification/complete'
    out.mkdir(parents=True,exist_ok=True)
    report={'status':'PASS','reused_not_fresh':True,'source_run':37947374801,
            'source_job':113877048106,'source_commit':'247e98e8bf13aae2924e980e4680c6f6466552ed',
            'source_artifact':11626618391,'archive_sha256':sha(args.archive),
            'module_count':len(graph),'build_summary':summary,
            'verification':'Exact source, object, imported-object and build-log hashes; final trust-zero replay still required'}
    (out/'UNIFORM_CACHE_PROVENANCE.json').write_text(json.dumps(report,indent=2)+'\n')
    pack('UniformBuild')
    print('VERIFIED_UNIFORM_COMPONENT_REPACKED',len(graph),'source-identical modules')

if __name__=='__main__':
    main()
