#!/usr/bin/env python3
"""Validate and retain literal successful all-n verification, without rewriting its report."""
from __future__ import annotations
import argparse, gzip, hashlib, json, re, shutil, subprocess, tarfile
from pathlib import Path


def sha(p: Path) -> str:
    return hashlib.sha256(p.read_bytes()).hexdigest()


def main() -> None:
    ap=argparse.ArgumentParser()
    ap.add_argument('--repo',type=Path,required=True)
    ap.add_argument('--artifact',type=Path,required=True)
    ap.add_argument('--run',type=int,required=True)
    args=ap.parse_args()
    repo=args.repo.resolve();root=repo/'formalizations/appt-qutrit-purity';src=args.artifact.resolve()
    reports=list(src.rglob('local-verification/complete/RUN.json'))
    if len(reports)!=1:raise RuntimeError('Expected one exact final verification report')
    report_file=reports[0];details=report_file.parent;report=json.loads(report_file.read_text())
    run=json.loads(subprocess.check_output(['gh','api',f'repos/mxym/math/actions/runs/{args.run}']))
    jobs=json.loads(subprocess.check_output(['gh','api',f'repos/mxym/math/actions/runs/{args.run}/jobs']))
    if report['status']!='PASS' or run['conclusion']!='success':raise RuntimeError('Full verification did not pass')
    checks=report['checks']
    if len(checks)!=18 or not all(c['passed'] and not c['timed_out'] for c in checks):raise RuntimeError('Not all 18 checks passed')
    for c in checks:
        if sha(details/(c['name']+'.log'))!=c['log_sha256']:raise RuntimeError('Changed check log: '+c['name'])
    pins=json.loads((root/'PROOF_SOURCES.json').read_text())
    if pins!=report['sources'] or sha(root/'PROOF_SOURCES.json')!=report['source_manifest_sha256']:
        raise RuntimeError('Source manifest mismatch')
    for name,h in pins.items():
        if sha(root/name)!=h:raise RuntimeError('Publication source mismatch: '+name)
    roots_candidates=list(src.rglob('replayed-roots.txt'))
    roots=roots_candidates[0].read_text().splitlines()
    axes=roots_candidates[0].with_name('replayed-axioms.txt').read_text().splitlines()
    closure=roots_candidates[0].with_name('replayed-closure.txt').read_text().splitlines()
    if 'APPT.Quantum.appt_purity_maximum_formula' not in roots:raise RuntimeError('Maximum missing from replay')
    if len(roots)!=report['replayed_roots'] or len(closure)!=report['replayed_declarations']:
        raise RuntimeError('Wrong root/closure count')
    if set(axes)!={'Classical.choice','propext','Quot.sound'}:raise RuntimeError('Wrong axiom inventory')
    module_records=list(src.rglob('logs/blocks/APPT*.json'))
    if len(module_records)!=879:raise RuntimeError('Expected 879 unique module records')
    for p in module_records:
        r=json.loads(p.read_text());source=r['module'].replace('.','/')+'.lean'
        if r['exit_code']!=0 or r['timed_out'] or sha(root/source)!=r['source_sha256'] or sha(p.with_suffix('.log'))!=r['log_sha256']:
            raise RuntimeError('Invalid module record: '+r['module'])
    corruption=(details/'corrupt-final-theorem.log').read_text()
    if "declaration type mismatch, 'APPT.Quantum.appt_purity_maximum_formula'" not in corruption:
        raise RuntimeError('Wrong rejection reason')
    m=re.search(r'TYPE_CLOSURE_REPLAY_PASS (\d+) declarations; trust level zero',corruption)
    if not m:raise RuntimeError('Missing successful type-dependency replay')
    out=root/'verification/complete-v1';out.mkdir(exist_ok=True)
    for p in details.iterdir():
        if p.is_file() and p.suffix in {'.json','.log'}:shutil.copy2(p,out/p.name)
    for p in roots_candidates[0].parent.glob('replayed-*.txt'):
        if 'closure' not in p.name:shutil.copy2(p,out/p.name)
    for p in src.rglob('completion-replayed-*.txt'):
        if 'type-dependencies' not in p.name and 'closure' not in p.name:shutil.copy2(p,out/p.name)
    (out/'workflow-run.json').write_text(json.dumps(run,indent=2)+'\n')
    (out/'workflow-jobs.json').write_text(json.dumps(jobs,indent=2)+'\n')
    archive=out/'literal-evidence.tar.gz'
    with archive.open('wb') as raw,gzip.GzipFile(filename='',mode='wb',fileobj=raw,mtime=0,compresslevel=9) as gz:
        with tarfile.open(fileobj=gz,mode='w',format=tarfile.PAX_FORMAT) as tf:
            for p in sorted(src.rglob('*')):
                if not p.is_file():continue
                info=tf.gettarinfo(str(p),arcname=p.relative_to(src).as_posix())
                info.uid=info.gid=info.mtime=0;info.uname=info.gname='';info.pax_headers={}
                with p.open('rb') as f:tf.addfile(info,f)
    summary={'status':'COMPLETE','scope':report['scope'],'verification_run':args.run,
        'verified_source_commit':run['head_sha'],'checks_passed':len(checks),'compiled_modules':879,
        'source_files':len(pins),'replayed_declarations':len(closure),'replayed_roots':len(roots),
        'trust_level':0,'axioms':axes,'corruption_control_type_dependencies':int(m[1]),
        'corruption_control':'Original final theorem type and universe parameters; only proof replaced by True.intro; fresh trust-zero kernel rejects that exact theorem',
        'fresh_single_runner_build':report['fresh_package_build'],
        'maximum_recorded_module_seconds':max(json.loads(p.read_text())['seconds'] for p in module_records),
        'literal_evidence_sha256':sha(archive)}
    (out/'SUMMARY.json').write_text(json.dumps(summary,indent=2)+'\n')
    print(json.dumps(summary,indent=2))

if __name__=='__main__':main()
