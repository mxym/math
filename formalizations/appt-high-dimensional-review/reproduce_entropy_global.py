#!/usr/bin/env python3
"""Rebuild and replay full-entropy upper and saturation-to-flatness proofs; not entropy attainment."""
from __future__ import annotations
import argparse, hashlib, json, os, re, shutil, signal, subprocess, time
from pathlib import Path
ROOT=Path(__file__).resolve().parent
OLD=ROOT.parent/'appt-qutrit-purity'
PIN='d13f23b723b8a846827a245b89c10fc7d3f11612'
MANIFEST=ROOT/'ENTROPY_GLOBAL_HASHES.json'
SCOPE='Full physical von Neumann fixed-finite-aspect upper half, full entropy coefficient saturation implies head saturation and uniform all-eigenvalue flatness. No matching entropy-attainment construction, complete entropy minimum, fixed-local/all-regime entropy law or other Renyi order is certified.'
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def inventory():
    paths={ROOT/Path(__file__).name,ROOT/'lean-toolchain',ROOT/'lakefile.toml',ROOT/'lake-manifest.json'}
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
                if dep.startswith(('APPT.','APPTReview.','Verification.')):visit(dep)
    visit('EntropyGlobalAudit')
    return {('../appt-qutrit-purity/' if p.is_relative_to(OLD) else '')+p.relative_to(OLD if p.is_relative_to(OLD) else ROOT).as_posix():sha(p) for p in sorted(paths)}
def check_sources():
    if (ROOT/'lean-toolchain').read_text().strip()!='leanprover/lean4:v4.34.1':raise RuntimeError('Wrong Lean pin')
    manifest=json.loads((ROOT/'lake-manifest.json').read_text())
    if [x.get('rev') for x in manifest['packages'] if x['name']=='mathlib']!=[PIN]:raise RuntimeError('Wrong Mathlib pin')
    pins=inventory()
    if pins!=json.loads(MANIFEST.read_text()):raise RuntimeError('Source inventory changed')
    for n in pins:
        if not n.endswith('.lean') or n.startswith('../appt-qutrit-purity/Verification/'):continue
        if n=='EntropyGlobalAudit.lean':continue
        code=re.sub(r'/\-.*?\-/|--[^\n]*','',(ROOT/n).read_text(),flags=re.S)
        if re.search(r'\b(sorry|admit|axiom|native_decide|unsafe)\b',code):raise RuntimeError('Forbidden proof token '+n)
    print('ENTROPY_GLOBAL_SOURCE_PASS',len(pins),flush=True)
def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--write-manifest',action='store_true')
    ap.add_argument('--check-only',action='store_true')
    ap.add_argument('--fresh',action='store_true')
    args=ap.parse_args()
    if args.write_manifest:
        MANIFEST.write_text(json.dumps(inventory(),indent=2)+'\n')
        print('MANIFEST_WRITTEN; not mathematical verification');return
    check_sources()
    if args.check_only:return
    actual=subprocess.check_output(['git','-C',str(ROOT/'.lake/packages/mathlib'),'rev-parse','HEAD'],text=True).strip()
    if actual!=PIN:raise RuntimeError('Actual Mathlib checkout differs from pin')
    if args.fresh:
        p=ROOT/'.lake/build'
        if p.is_symlink():raise RuntimeError('Refusing to remove symlinked build directory')
        if p.exists():shutil.rmtree(p)
    out=ROOT/'verification/entropy-global-reproduction';out.mkdir(parents=True,exist_ok=True)
    for n in ('SUMMARY.json','STAGES.json'):
        p=out/n
        if p.exists():p.unlink()
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
            raise RuntimeError('Failed stage '+name+'; original diagnostics retained')
        return log.read_text()
    stage('toolchain',['lake','env','lean','--version'],60)
    stage('build',['lake','build','APPTReview.EntropyGlobalControls'],900)
    dest=ROOT/'.lake/build/lib/lean';(dest/'Verification').mkdir(parents=True,exist_ok=True)
    stage('support',['lake','env','lean','-j1','-M6000','--root='+str(OLD),'-o',str(dest/'Verification/ReplaySupport.olean'),str(OLD/'Verification/ReplaySupport.lean')],180)
    log=stage('kernel',['lake','env','lean','-j1','-M6000','EntropyGlobalAudit.lean'],480)
    audit=(ROOT/'EntropyGlobalAudit.lean').read_text()
    block=re.search(r'replayAndCorrupt\s*\[(.*?)\]\s*"entropy-global-kernel"',audit,re.S)
    if not block:raise RuntimeError('Cannot parse requested audit roots')
    roots=re.findall(r'``([A-Za-z0-9_.]+)',block[1])
    match=re.search(r'EMPTY_KERNEL_REPLAY_PASS (\d+) declarations; (\d+) roots; trust level zero',log)
    if not match or int(match[2])!=len(roots):raise RuntimeError('Missing complete trust-zero replay')
    if (ROOT/'entropy-global-kernel-roots.txt').read_text().splitlines()!=roots:raise RuntimeError('Root mismatch')
    if len((ROOT/'entropy-global-kernel-closure.txt').read_text().splitlines())!=int(match[1]):raise RuntimeError('Declaration count mismatch')
    if set((ROOT/'entropy-global-kernel-axioms.txt').read_text().splitlines())!={'propext','Classical.choice','Quot.sound'}:raise RuntimeError('Unexpected axioms')
    controls=[roots[0]]+re.findall(r'rejectCorruptTheorem\s*``([A-Za-z0-9_.]+)',audit)
    for name in controls:
        if 'CORRUPTED_PROOF_REJECTED '+name not in log or "declaration type mismatch, '"+name+"'" not in log:raise RuntimeError('Missing exact-type corruption rejection '+name)
    for p in ROOT.glob('entropy-global-*.txt'):shutil.copy2(p,out/p.name)
    check_sources()
    result={'status':'PASS','scope':SCOPE,'source_manifest_sha256':sha(MANIFEST),'source_files':len(inventory()),'stages':records,'kernel_declarations':int(match[1]),'roots':len(roots),'empty_kernel_trust_level':0,'corrupted_theorems':controls}
    (out/'SUMMARY.json').write_text(json.dumps(result,indent=2)+'\n')
    print('ENTROPY_GLOBAL_REPRODUCTION_PASS',flush=True)
if __name__=='__main__':main()
