#!/usr/bin/env python3
"""Reproduce the complete physical qutrit-qudit APPT maximum, for every n >= 3."""
from __future__ import annotations
import argparse, datetime, hashlib, json, re, shutil, subprocess, time
from pathlib import Path
ROOT=Path(__file__).resolve().parent
OUT=ROOT/'local-verification'/'complete'
ALLOWED={'propext','Classical.choice','Quot.sound'}
MATHLIB='d13f23b723b8a846827a245b89c10fc7d3f11612'

def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()

def command_text(command: list[str]) -> str:
    return subprocess.check_output(command,cwd=ROOT,text=True,timeout=120).strip()

def validate_sources(pins: dict[str,str]) -> None:
    for name,expected in pins.items():
        path=ROOT/name
        if not path.is_file() or digest(path)!=expected:
            raise RuntimeError('Source hash mismatch: '+name)
    actual={p.relative_to(ROOT).as_posix() for p in (ROOT/'APPT').rglob('*.lean')}
    if not actual<=pins.keys():raise RuntimeError('Unpinned proof source: '+repr(actual-pins.keys()))
    for name in actual:
        if re.search(r'\b(sorry|admit|axiom|native_decide)\b',(ROOT/name).read_text()):
            raise RuntimeError('Forbidden proof token: '+name)

def main() -> None:
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--fresh',action='store_true',help='Remove only this package build directory; preserve external dependencies.')
    ap.add_argument('--jobs',type=int,choices=[1,2],default=2)
    args=ap.parse_args();OUT.mkdir(parents=True,exist_ok=True)
    pins=json.loads((ROOT/'PROOF_SOURCES.json').read_text());validate_sources(pins)
    manifest_hash=digest(ROOT/'PROOF_SOURCES.json')
    version=command_text(['lake','env','lean','--version'])
    if 'version 4.34.1,' not in version:raise RuntimeError('Wrong Lean toolchain: '+version)
    manifest=json.loads((ROOT/'lake-manifest.json').read_text())
    mp=next(p for p in manifest['packages'] if p['name']=='mathlib')
    if mp['rev']!=MATHLIB:raise RuntimeError('Wrong pinned Mathlib revision')
    checkout=ROOT/'.lake/packages/mathlib'
    actual=command_text(['git','-C',str(checkout),'rev-parse','HEAD'])
    if actual!=MATHLIB:raise RuntimeError('Mathlib checkout revision mismatch')
    if command_text(['git','-C',str(checkout),'status','--porcelain','--untracked-files=no']):
        raise RuntimeError('Tracked Mathlib sources are modified')
    if args.fresh:
        build=ROOT/'.lake/build'
        if build.is_symlink():raise RuntimeError('Refusing to remove linked build directory')
        if build.exists():shutil.rmtree(build)
    steps=[
        ('source-inventory',['python3','scripts/source_manifest.py','--check'],'pass',180),
        ('regenerate-uniform',['python3','scripts/generate_uniform.py','--check'],'pass',180),
        ('regenerate-finite',['python3','scripts/generate_finite_sparse.py','--check'],'pass',180),
        ('certificate-controls',['python3','scripts/certificate_controls.py'],'pass',180),
        ('replay-controls',['lake','env','lean','-j1','ReplayControls.lean'],'pass',180),
        ('module-graph',['python3','scripts/completion_graph.py','--check'],'pass',180),
        ('bounded-lake',['lake','env','python3','scripts/build_blocks.py','--case','All','--engine','lake','--jobs',str(args.jobs),'--timeout','300']+(['--fresh'] if args.fresh else []),'pass',21600),
        ('lake-build',['lake','build'],'pass',600),
        ('positive-sparse',['lake','env','lean','-j1','-M12288','PositiveSparse.lean'],'pass',180),
        ('negative-sparse',['lake','env','lean','-j1','-M12288','RejectSparse.lean'],'decide',180),
        ('positive-corner',['lake','env','lean','-j1','-M12288','NecessityPositive.lean'],'pass',180),
        ('negative-corner',['lake','env','lean','-j1','-M12288','NecessityReject.lean'],'decide',180),
        ('positive-purity',['lake','env','lean','-j1','-M12288','PositivePurity.lean'],'pass',300),
        ('negative-purity',['lake','env','lean','-j1','-M12288','RejectPurity.lean'],'false',300),
        ('completion-formula-controls',['lake','env','lean','-j1','-M12288','CompletionFormulaControls.lean'],'pass',300),
        ('empty-kernel',['lake','env','lean','-j1','-M12288','CheckpointReplay.lean'],'pass',1200),
        ('replay-support',['lake','env','lean','-j1','-M12288','-o','.lake/build/lib/lean/Verification/ReplaySupport.olean','Verification/ReplaySupport.lean'],'pass',180),
        ('corrupt-final-theorem',['lake','env','lean','-j1','-M12288','CompletionAudit.lean'],'pass',1200),
    ]
    report={'status':'RUNNING','scope':'Complete actual-state qutrit-qudit APPT maximal purity for every integer n >= 3; universal upper bound and physical APPT attainment',
            'utc_started':datetime.datetime.now(datetime.timezone.utc).isoformat(),'fresh_package_build':args.fresh,
            'lean':version,'mathlib':actual,'jobs':args.jobs,'per_module_timeout_seconds':300,
            'source_manifest_sha256':manifest_hash,'sources':pins,'checks':[]}
    def save():
        (OUT/'RUN.json').write_text(json.dumps(report,indent=2)+'\n')
    save()
    (ROOT/'.lake/build/lib/lean/Verification').mkdir(parents=True,exist_ok=True)
    try:
        for name,cmd,expected,limit in steps:
            log=OUT/(name+'.log');started=time.monotonic();timed_out=False
            with log.open('w') as stream:
                try:
                    proc=subprocess.run(cmd,cwd=ROOT,stdout=stream,stderr=subprocess.STDOUT,timeout=limit)
                    code=proc.returncode
                except subprocess.TimeoutExpired:
                    code=124;timed_out=True
            text=log.read_text();passed=code==0 and not timed_out
            if expected!='pass':
                diagnostic=('Tactic `decide` proved that the proposition' in text and 'is false' in text) if expected=='decide' else ('unsolved goals' in text and 'False' in text)
                passed=(code!=0 and not timed_out and text.count('error:')==1 and diagnostic)
            item={'name':name,'command':cmd,'exit_code':code,'expected_rejection':expected!='pass',
                  'timed_out':timed_out,'passed':passed,'seconds':round(time.monotonic()-started,3),'log_sha256':digest(log)}
            report['checks'].append(item);save();print(json.dumps(item),flush=True)
            if not passed:raise RuntimeError('Verification failed: '+name)
        control=(OUT/'replay-controls.log').read_text()
        if 'REPLAY_POSITIVE_CONTROL_PASS' not in control or 'REPLAY_NEGATIVE_CONTROL_REJECTED' not in control:
            raise RuntimeError('Missing paired kernel control markers')
        corruption=(OUT/'corrupt-final-theorem.log').read_text()
        if 'EMPTY_KERNEL_REPLAY_PASS' not in corruption or 'CORRUPTED_PROOF_REJECTED APPT.Quantum.appt_purity_maximum_formula' not in corruption or 'declaration type mismatch' not in corruption:
            raise RuntimeError('Final theorem proof-corruption control missing')
        for p in ROOT.glob('completion-replayed-*.txt'):shutil.copy2(p,OUT/p.name)
        replay=(OUT/'empty-kernel.log').read_text()
        match=re.search(r'EMPTY_KERNEL_REPLAY_PASS (\d+) declarations; (\d+) roots; trust level zero',replay)
        if not match:raise RuntimeError('Missing trust-zero replay completion marker')
        axioms=set((ROOT/'replayed-axioms.txt').read_text().splitlines())
        if not axioms<=ALLOWED:raise RuntimeError('Unapproved axioms: '+repr(axioms))
        roots=(ROOT/'replayed-roots.txt').read_text().splitlines()
        if 'APPT.Quantum.appt_purity_maximum_formula' not in roots:raise RuntimeError('Final maximum not among replay roots')
        for p in ROOT.glob('replayed-*.txt'):shutil.copy2(p,OUT/p.name)
        summary=json.loads((ROOT/'logs/blocks/SUMMARY.json').read_text())
        if summary['status']!='PASS' or summary['completed']!=summary['total']:raise RuntimeError('Incomplete local module build')
        shutil.copy2(ROOT/'logs/blocks/SUMMARY.json',OUT/'BUILD_SUMMARY.json')
        validate_sources(pins)
        if digest(ROOT/'PROOF_SOURCES.json')!=manifest_hash:raise RuntimeError('Source manifest changed during verification')
        report.update(status='PASS',axioms=sorted(axioms),replayed_declarations=int(match[1]),
                      replayed_roots=int(match[2]),build_summary=summary,
                      utc_finished=datetime.datetime.now(datetime.timezone.utc).isoformat())
        save();print('COMPLETE_APPT_MAXIMUM_VERIFIED',flush=True)
    except Exception as exc:
        report.update(status='FAIL',failure=str(exc));save();raise

if __name__=='__main__':main()
