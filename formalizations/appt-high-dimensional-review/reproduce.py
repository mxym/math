#!/usr/bin/env python3
"""Rebuild and trust-zero replay the finite physical APPT review, not its unproved global limits."""
from __future__ import annotations
import argparse, hashlib, json, os, re, shutil, signal, subprocess, time
from pathlib import Path
ROOT=Path(__file__).resolve().parent
OLD=ROOT.parent/'appt-qutrit-purity'
PIN='d13f23b723b8a846827a245b89c10fc7d3f11612'
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def inventory():
    paths={ROOT/'reproduce.py',ROOT/'lean-toolchain',ROOT/'lakefile.toml',ROOT/'lake-manifest.json'}
    seen=set()
    def visit(name):
        if name in seen:return
        seen.add(name)
        base=OLD if name.startswith(('APPT.','Verification.')) else ROOT
        p=base/(name.replace('.','/')+'.lean')
        if not p.is_file():raise RuntimeError('Missing local dependency '+str(p))
        paths.add(p)
        for line in re.findall(r'^import\s+([^\n]+)',p.read_text(),re.M):
            for dep in line.split():
                if dep.startswith(('APPT.','APPTReview.','Verification.')) or dep in ('APPTReview','Regression'):visit(dep)
    for name in ('APPTReview','ReviewAudit','Regression'):visit(name)
    return {('../appt-qutrit-purity/' if p.is_relative_to(OLD) else '')+p.relative_to(OLD if p.is_relative_to(OLD) else ROOT).as_posix():sha(p) for p in sorted(paths)}
def check_sources():
    if (ROOT/'lean-toolchain').read_text().strip()!='leanprover/lean4:v4.34.1':raise RuntimeError('Wrong toolchain pin')
    manifest=json.loads((ROOT/'lake-manifest.json').read_text())
    if [x.get('rev') for x in manifest['packages'] if x['name']=='mathlib']!=[PIN]:raise RuntimeError('Wrong Mathlib pin')
    if inventory()!=json.loads((ROOT/'SOURCE_HASHES.json').read_text()):raise RuntimeError('Source inventory changed')
    for p in (ROOT/'APPTReview').glob('*.lean'):
        code=re.sub(r'/\-.*?\-/|--[^\n]*','',p.read_text(),flags=re.S)
        if re.search(r'\b(sorry|admit|axiom|native_decide|unsafe)\b',code):raise RuntimeError('Forbidden proof token: '+str(p))
    print('SOURCE_BINDING_PASS',len(inventory()),flush=True)
def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--write-manifest',action='store_true')
    ap.add_argument('--check-only',action='store_true')
    ap.add_argument('--fresh',action='store_true')
    args=ap.parse_args()
    if args.write_manifest:
        (ROOT/'SOURCE_HASHES.json').write_text(json.dumps(inventory(),indent=2)+'\n')
        print('MANIFEST_WRITTEN; not proof verification');return
    check_sources()
    if args.check_only:return
    if not shutil.which('lake'):raise RuntimeError('Install pinned Lean/Lake and cache dependencies first')
    actual=subprocess.check_output(['git','-C',str(ROOT/'.lake/packages/mathlib'),'rev-parse','HEAD'],text=True).strip()
    if actual!=PIN:raise RuntimeError('Actual Mathlib checkout does not match pin')
    if args.fresh:
        p=ROOT/'.lake/build'
        if p.is_symlink():raise RuntimeError('Refusing to remove symlinked build directory')
        if p.exists():shutil.rmtree(p)
    out=ROOT/'verification/reproduction';out.mkdir(parents=True,exist_ok=True)
    records=[]
    def stage(name,cmd,limit):
        log=out/(name+'.log');start=time.monotonic()
        with log.open('w') as stream:
            process=subprocess.Popen(cmd,cwd=ROOT,stdout=stream,stderr=subprocess.STDOUT,start_new_session=True)
            try:code=process.wait(timeout=limit)
            except subprocess.TimeoutExpired:
                os.killpg(process.pid,signal.SIGKILL);process.wait();code=124
                stream.write('\nBOUNDED_PROCESS_GROUP_TIMEOUT\n')
        records.append({'stage':name,'command':cmd,'exit_code':code,'seconds':round(time.monotonic()-start,3),'log':log.name,'sha256':sha(log)})
        (out/'STAGES.json').write_text(json.dumps(records,indent=2)+'\n')
        print(json.dumps(records[-1]),flush=True)
        if code:
            print(log.read_text()[-16000:],flush=True)
            raise RuntimeError('Stage failed: '+name+'; original output retained')
        return log.read_text()
    stage('toolchain',['lake','env','lean','--version'],60)
    stage('build',['lake','build','APPTReview'],900)
    dest=ROOT/'.lake/build/lib/lean';(dest/'Verification').mkdir(parents=True,exist_ok=True)
    stage('support',['lake','env','lean','-j1','-M6000','--root='+str(OLD),'-o',str(dest/'Verification/ReplaySupport.olean'),str(OLD/'Verification/ReplaySupport.lean')],180)
    stage('regressions',['lake','env','lean','-j1','-M6000','-o',str(dest/'Regression.olean'),'Regression.lean'],180)
    audit=stage('kernel',['lake','env','lean','-j1','-M6000','ReviewAudit.lean'],480)
    for marker in ('EMPTY_KERNEL_REPLAY_PASS','CORRUPTED_PROOF_REJECTED'):
        if marker not in audit:raise RuntimeError('Missing audit marker '+marker)
    for p in ROOT.glob('review-kernel-*.txt'):shutil.copy2(p,out/p.name)
    check_sources()
    result={'status':'PASS','scope':'Complete exact rectangular APPT maximum, ordered-spectrum and actual unitary-orbit equality classification; all listed finite dependencies. NOT growing-dimensional multiscale lower limits, full entropy laws or asymptotic rigidity.','source_manifest_sha256':sha(ROOT/'SOURCE_HASHES.json'),'stages':records,'empty_kernel_trust_level':0,'source_files':len(inventory())}
    (out/'SUMMARY.json').write_text(json.dumps(result,indent=2)+'\n')
    print('REVIEW_REPRODUCTION_PASS',flush=True)
if __name__=='__main__':main()