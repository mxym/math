#!/usr/bin/env python3
"""Check physical APPT necessity and its full proof dependency closure."""
from __future__ import annotations
import argparse, hashlib, json, re, shutil, subprocess, time
from pathlib import Path
ROOT=Path(__file__).resolve().parent
OUT=ROOT/'local-verification'/'necessity'
MATHLIB='d13f23b723b8a846827a245b89c10fc7d3f11612'
ALLOWED={'propext','Classical.choice','Quot.sound'}
def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()
def output(cmd: list[str]) -> str:
    return subprocess.check_output(cmd,cwd=ROOT,text=True,timeout=90).strip()
def main() -> None:
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--fresh',action='store_true',help='Remove this package build directory, not external dependency caches.')
    args=parser.parse_args(); OUT.mkdir(parents=True,exist_ok=True)
    pins=json.loads((ROOT/'NECESSITY_SOURCES.json').read_text())
    for name,expected in pins.items():
        if digest(ROOT/name)!=expected: raise RuntimeError('Source hash mismatch: '+name)
    version=output(['lake','env','lean','--version'])
    if 'version 4.34.1,' not in version: raise RuntimeError('Wrong Lean version: '+version)
    manifest=json.loads((ROOT/'lake-manifest.json').read_text())
    package=next(p for p in manifest['packages'] if p['name']=='mathlib')
    if package['rev']!=MATHLIB: raise RuntimeError('Wrong Mathlib manifest pin')
    revision=output(['git','-C',str(ROOT/'.lake/packages/mathlib'),'rev-parse','HEAD'])
    if revision!=MATHLIB: raise RuntimeError('Wrong Mathlib checkout: '+revision)
    for name in pins:
        if name.startswith('APPT/') and name.endswith('.lean'):
            if re.search(r'\b(sorry|admit|axiom|native_decide)\b',(ROOT/name).read_text()):
                raise RuntimeError('Forbidden proof token: '+name)
    if args.fresh:
        build=ROOT/'.lake/build'
        if build.is_symlink(): raise RuntimeError('Refusing to remove linked build directory')
        if build.exists(): shutil.rmtree(build)
    steps=[('lake-build',['lake','build','APPT.Quantum.SpectralNecessity'],False,300),
           ('positive',['lake','env','lean','-j1','NecessityPositive.lean'],False,180),
           ('negative',['lake','env','lean','-j1','NecessityReject.lean'],True,180),
           ('empty-kernel',['lake','env','lean','-j1','-M12288','NecessityReplay.lean'],False,600)]
    report={'status':'RUNNING','scope':'Actual density/APPT to sorted normalized real spectrum, trace-square purity and both necessary PSD matrices; no sufficiency or all-dimension maximum claimed',
            'fresh_package_build':args.fresh,'lean':version,'mathlib':revision,'sources':pins,'checks':[]}
    for name,cmd,negative,limit in steps:
        log=OUT/(name+'.log'); started=time.monotonic()
        with log.open('w') as stream:
            proc=subprocess.run(cmd,cwd=ROOT,stdout=stream,stderr=subprocess.STDOUT,timeout=limit)
        text=log.read_text(); passed=proc.returncode==0
        if negative:
            passed=(proc.returncode!=0 and text.count('error:')==1
                    and 'Tactic `decide` proved that the proposition' in text
                    and 'slotA (0, 0) = 7' in text and 'is false' in text)
        item={'name':name,'command':cmd,'exit_code':proc.returncode,'expected_rejection':negative,'passed':passed,
              'seconds':round(time.monotonic()-started,3),'log_sha256':digest(log)}
        report['checks'].append(item)
        (OUT/'RUN.json').write_text(json.dumps(report,indent=2)+'\n')
        print(json.dumps(item),flush=True)
        if not passed: raise RuntimeError('Verification failed: '+name)
    if 'NECESSITY_EMPTY_KERNEL_REPLAY_PASS' not in (OUT/'empty-kernel.log').read_text():
        raise RuntimeError('Missing empty-kernel completion marker')
    names=set((ROOT/'necessity-replayed-axioms.txt').read_text().splitlines())
    if not names<=ALLOWED: raise RuntimeError('Unapproved dependencies: '+repr(names))
    for path in ROOT.glob('necessity-replayed-*.txt'): shutil.copy2(path,OUT/path.name)
    for name,expected in pins.items():
        if digest(ROOT/name)!=expected: raise RuntimeError('Source changed during verification: '+name)
    report.update(status='PASS',axioms=sorted(names))
    (OUT/'RUN.json').write_text(json.dumps(report,indent=2)+'\n')
    print('PHYSICAL_APPT_NECESSITY_VERIFIED',flush=True)
if __name__=='__main__': main()
