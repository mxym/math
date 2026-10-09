#!/usr/bin/env python3
"""Replay the exported checkpoint. External dependency caches are not proof oracles."""
from pathlib import Path
import hashlib, json, re, subprocess, time

ROOT=Path(__file__).resolve().parent
OUT=ROOT/'local-verification'
ALLOWED={'propext','Classical.choice','Quot.sound'}

def digest(p): return hashlib.sha256(p.read_bytes()).hexdigest()

def main():
    OUT.mkdir(exist_ok=True)
    pins=json.loads((ROOT/'PROOF_SOURCES.json').read_text())
    for path,expected in pins.items():
        if digest(ROOT/path)!=expected: raise RuntimeError('Source hash mismatch: '+path)
    version=subprocess.check_output(['lake','env','lean','--version'],cwd=ROOT,text=True).strip()
    if 'version 4.34.1,' not in version: raise RuntimeError('Wrong Lean version: '+version)
    manifest=json.loads((ROOT/'lake-manifest.json').read_text())
    mp=next(p for p in manifest['packages'] if p['name']=='mathlib')
    if mp['rev']!='d13f23b723b8a846827a245b89c10fc7d3f11612': raise RuntimeError('Wrong Mathlib pin')
    # Lean's parser/kernel and the closure audit remain authoritative; this scan is additional.
    for p in (ROOT/'APPT').rglob('*.lean'):
        if re.search(r'\b(sorry|admit|axiom|native_decide)\b',p.read_text()):
            raise RuntimeError('Forbidden token in proof source: '+str(p))
    jobs=[('regenerate',['python3','scripts/generate_uniform.py','--check'],0,180),
          ('bounded-lake',['lake','env','python3','scripts/build_blocks.py','--case','All','--engine','lake','--jobs','2','--timeout','300'],0,21600),
          ('lake-build',['lake','build'],0,600),
          ('positive-coefficient',['lake','env','lean','-j1','-M12288','PositiveCoefficient.lean'],0,180),
          ('negative-coefficient',['lake','env','lean','-j1','-M12288','RejectCoefficient.lean'],1,180),
          ('empty-kernel',['lake','env','lean','-j1','-M12288','CheckpointReplay.lean'],0,600)]
    results=[]
    for name,cmd,expected,limit in jobs:
        start=time.time();file=OUT/(name+'.log')
        with file.open('w') as f:
            run=subprocess.run(cmd,cwd=ROOT,stdout=f,stderr=subprocess.STDOUT,timeout=limit)
        text=file.read_text()
        good=(run.returncode==0) if expected==0 else (run.returncode!=0 and 'error:' in text and 'Tactic `decide` failed' in text)
        result={'name':name,'command':cmd,'exit_code':run.returncode,'expected_rejection':bool(expected),
                'passed':good,'seconds':round(time.time()-start,3),'log_sha256':digest(file)}
        results.append(result);print(result,flush=True)
        (OUT/'RUN.json').write_text(json.dumps({'status':'RUNNING','lean':version,'sources':pins,'checks':results},indent=2)+'\n')
        if not good: raise RuntimeError('Verification check failed: '+name)
    text=(OUT/'empty-kernel.log').read_text()
    if 'EMPTY_KERNEL_REPLAY_PASS' not in text: raise RuntimeError('Missing replay completion marker')
    axioms=set((ROOT/'replayed-axioms.txt').read_text().splitlines())
    if not axioms<=ALLOWED: raise RuntimeError('Unapproved axioms: '+repr(axioms))
    for p in ROOT.glob('replayed-*.txt'): (OUT/p.name).write_bytes(p.read_bytes())
    for path,expected in pins.items():
        if digest(ROOT/path)!=expected: raise RuntimeError('Source changed during verification: '+path)
    report={'status':'PASS','scope':'uniform ordered-spectrum upper bound under A/B PSD and actual APPT attainment; final state-level upper bound pending',
            'lean':version,'mathlib':mp['rev'],'sources':pins,'checks':results,'axioms':sorted(axioms)}
    (OUT/'RUN.json').write_text(json.dumps(report,indent=2)+'\n')
    print('CHECKPOINT_VERIFICATION_PASS',flush=True)

if __name__=='__main__': main()
