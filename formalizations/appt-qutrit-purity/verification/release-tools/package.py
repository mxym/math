#!/usr/bin/env python3
"""Export a source-locked release only after the complete verification reports PASS."""
from __future__ import annotations
import argparse, gzip, hashlib, io, json, subprocess, tarfile
from pathlib import Path

PREFIX = 'formalizations/appt-qutrit-purity/'
NAME = 'appt-qutrit-purity-complete-v1'
ALLOWED = {'Classical.choice', 'propext', 'Quot.sound'}


def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def git_bytes(repo: Path, commit: str, name: str) -> bytes:
    return subprocess.check_output(['git', '-C', str(repo), 'show', commit+':'+name])


def export_source(repo: Path, commit: str, output: Path) -> None:
    proc = subprocess.Popen(['git', '-C', str(repo), 'archive', '--format=tar', commit, PREFIX.rstrip('/')], stdout=subprocess.PIPE)
    assert proc.stdout is not None
    with output.open('wb') as raw, gzip.GzipFile(filename='', mode='wb', fileobj=raw, mtime=0, compresslevel=9) as gz:
        with tarfile.open(fileobj=proc.stdout, mode='r|') as src, tarfile.open(fileobj=gz, mode='w|', format=tarfile.PAX_FORMAT) as dst:
            for member in src:
                if member.name.rstrip('/') == PREFIX.rstrip('/'):
                    relative = ''
                elif member.name.startswith(PREFIX):
                    relative = member.name[len(PREFIX):]
                else:
                    continue
                if not (member.isfile() or member.isdir()):
                    raise RuntimeError('Unexpected nonregular source member: '+member.name)
                payload = src.extractfile(member) if member.isfile() else None
                member.name = NAME + ('/'+relative if relative else '')
                member.uid=member.gid=member.mtime=0
                member.uname=member.gname=''
                member.pax_headers={}
                dst.addfile(member, payload)
    if proc.wait() != 0:
        raise RuntimeError('Git archive failed')


def verify_archive(path: Path, pins: dict[str,str]) -> None:
    with tarfile.open(path, 'r:gz') as archive:
        names=[m.name for m in archive.getmembers()]
        if len(names) != len(set(names)):
            raise RuntimeError('Duplicate archive member')
        for name, expected in pins.items():
            stream=archive.extractfile(NAME+'/'+name)
            if stream is None or digest(stream.read()) != expected:
                raise RuntimeError('Release source hash mismatch: '+name)


def main() -> None:
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--repo',type=Path,required=True)
    ap.add_argument('--commit',required=True)
    ap.add_argument('--evidence',type=Path,required=True)
    ap.add_argument('--output',type=Path,required=True)
    args=ap.parse_args()
    repo=args.repo.resolve(); out=args.output.resolve()
    commit=subprocess.check_output(['git','-C',str(repo),'rev-parse',args.commit+'^{commit}'],text=True).strip()
    report=json.loads((args.evidence/'RUN.json').read_text())
    run=json.loads((args.evidence/'workflow-run.json').read_text())
    if report['status']!='PASS' or run['conclusion']!='success':
        raise RuntimeError('Refusing complete release without a successful full audit')
    required={'bounded-lake','lake-build','empty-kernel','completion-formula-controls','corrupt-final-theorem'}
    passed={c['name'] for c in report['checks'] if c['passed']}
    if not required<=passed or not all(c['passed'] for c in report['checks']):
        raise RuntimeError('Missing completed verification stages')
    if not set(report['axioms'])<=ALLOWED:
        raise RuntimeError('Unapproved proof axiom')
    pins=json.loads(git_bytes(repo,commit,PREFIX+'PROOF_SOURCES.json'))
    if pins!=report['sources']:
        raise RuntimeError('Publication sources differ from the fully verified sources')
    for name,expected in pins.items():
        if digest(git_bytes(repo,commit,PREFIX+name))!=expected:
            raise RuntimeError('Git-stored source hash mismatch: '+name)
    out.mkdir(parents=True,exist_ok=True)
    source=out/(NAME+'-source.tar.gz')
    export_source(repo,commit,source)
    verify_archive(source,pins)
    evidence=out/(NAME+'-verification.tar.gz')
    with evidence.open('wb') as raw, gzip.GzipFile(filename='',mode='wb',fileobj=raw,mtime=0,compresslevel=9) as gz:
        with tarfile.open(fileobj=gz,mode='w',format=tarfile.PAX_FORMAT) as tf:
            for p in sorted(args.evidence.rglob('*')):
                if not p.is_file(): continue
                info=tf.gettarinfo(str(p),arcname='verification/'+p.relative_to(args.evidence).as_posix())
                info.uid=info.gid=info.mtime=0;info.uname=info.gname='';info.pax_headers={}
                with p.open('rb') as stream:tf.addfile(info,stream)
    manifest={'status':'COMPLETE','release_tag':NAME,'publication_commit':commit,
        'verified_source_commit':run['head_sha'],'verification_run':run['id'],
        'verification_url':run['html_url'],'scope':report['scope'],
        'theorem':'APPT.Quantum.appt_purity_maximum_formula','lean':report['lean'],
        'mathlib':report['mathlib'],'axioms':report['axioms'],
        'source_files':len(pins),'compiled_modules':report['build_summary']['completed'],
        'replayed_declarations':report['replayed_declarations'],
        'replayed_roots':report['replayed_roots'],
        'fresh_single_runner_build':report['fresh_package_build'],
        'provenance':'All components were independently source-hash-bound; the final full theorem was replayed from an empty kernel at trust zero',
        'assets':{p.name:{'sha256':digest(p.read_bytes()),'bytes':p.stat().st_size} for p in (source,evidence)}}
    (out/'RELEASE_MANIFEST.json').write_text(json.dumps(manifest,indent=2)+'\n')
    assets=[source,evidence,out/'RELEASE_MANIFEST.json']
    (out/'SHA256SUMS').write_text(''.join(digest(p.read_bytes())+'  '+p.name+'\n' for p in assets))
    print(json.dumps(manifest,indent=2))

if __name__=='__main__': main()
