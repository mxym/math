#!/usr/bin/env python3
"""Transfer checked component build caches; source and object hashes are mandatory.
These caches are not proof oracles: the final roots are replayed at trust zero.
"""
from __future__ import annotations
import argparse, hashlib, io, json, tarfile
from pathlib import Path, PurePosixPath
ROOT=Path(__file__).resolve().parent.parent

def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()
def module_of(path):
    rel=path.relative_to(ROOT/'.lake/build')
    for prefix in [('lib','lean'),('ir',)]:
        if rel.parts[:len(prefix)]==prefix:
            parts=rel.parts[len(prefix):]
            return '.'.join([*parts[:-1],parts[-1].split('.')[0]])
    return None

def pack(case):
    modules=json.loads((ROOT/f'generated-{case}.json').read_text())['modules']
    sources={m.replace('.','/')+'.lean':sha(ROOT/(m.replace('.','/')+'.lean')) for m in modules}
    for name in ['lakefile.toml','lake-manifest.json','lean-toolchain']:sources[name]=sha(ROOT/name)
    files=[]
    for path in (ROOT/'.lake/build').rglob('*'):
        if path.is_file() and module_of(path) in modules:files.append(path)
    for m in modules:
        record=ROOT/'logs/blocks'/(m+'.json');r=json.loads(record.read_text())
        src=m.replace('.','/')+'.lean';obj=ROOT/'.lake/build/lib/lean'/(m.replace('.','/')+'.olean')
        if r['exit_code']!=0 or r['source_sha256']!=sources[src] or r['olean_sha256']!=sha(obj):
            raise RuntimeError('Unverified component module: '+m)
        files += [record,record.with_suffix('.log')]
    manifest={'case':case,'sources':sources,'files':{p.relative_to(ROOT).as_posix():sha(p) for p in sorted(files)}}
    payload=(json.dumps(manifest,indent=2)+'\n').encode()
    out=ROOT/'component-build.tar.gz'
    with tarfile.open(out,'w:gz',compresslevel=1) as archive:
        info=tarfile.TarInfo('component-manifest.json');info.size=len(payload);info.mode=0o644
        archive.addfile(info,io.BytesIO(payload))
        for p in sorted(files):archive.add(p,arcname=p.relative_to(ROOT).as_posix(),recursive=False)
    print('SOURCE_BOUND_COMPONENT_PACKED',case,len(modules),'modules',len(files),'files',sha(out))

def merge(directory):
    records=[]; seen={}
    archives=sorted(Path(directory).rglob('component-build.tar.gz'))
    if not archives:raise RuntimeError('No component build artifacts found')
    for filename in archives:
        with tarfile.open(filename,'r:gz') as archive:
            stream=archive.extractfile('component-manifest.json')
            if stream is None:raise RuntimeError('Missing component manifest')
            manifest=json.load(stream)
            for name,h in manifest['sources'].items():
                if sha(ROOT/name)!=h:raise RuntimeError('Component source mismatch: '+name)
            declared=manifest['files'];members={m.name:m for m in archive.getmembers()}
            if set(members)!=set(declared)|{'component-manifest.json'}:raise RuntimeError('Unexpected archive members')
            for name,h in declared.items():
                m=members[name];parts=PurePosixPath(name)
                if not m.isfile() or parts.is_absolute() or '..' in parts.parts:
                    raise RuntimeError('Invalid cache member: '+name)
                if not (name.startswith('.lake/build/') or name.startswith('logs/blocks/')):
                    raise RuntimeError('Unexpected cache location: '+name)
                src=archive.extractfile(m)
                if src is None:raise RuntimeError('Missing cache payload: '+name)
                data=src.read()
                if hashlib.sha256(data).hexdigest()!=h:raise RuntimeError('Cache content mismatch: '+name)
                # Shared proof objects must be identical across independently built components.
                if name in seen and '.olean' in name and seen[name]!=h:
                    raise RuntimeError('Conflicting proof object: '+name)
                dest=ROOT/name;dest.parent.mkdir(parents=True,exist_ok=True)
                dest.write_bytes(data);seen[name]=h
            records.append({'case':manifest['case'],'archive_sha256':sha(filename),'modules':len(manifest['sources'])-3})
    out=ROOT/'local-verification/complete';out.mkdir(parents=True,exist_ok=True)
    (out/'COMPONENTS.json').write_text(json.dumps(records,indent=2)+'\n')
    print('SOURCE_BOUND_COMPONENT_MERGE_PASS',len(records),'components')

if __name__=='__main__':
    parser=argparse.ArgumentParser();sub=parser.add_subparsers(dest='command',required=True)
    sub.add_parser('pack').add_argument('case');sub.add_parser('merge').add_argument('directory')
    args=parser.parse_args()
    if args.command=='pack':pack(args.case)
    else:merge(args.directory)
