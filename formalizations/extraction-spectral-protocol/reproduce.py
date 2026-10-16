#!/usr/bin/env python3
"""Source-bound rebuild and empty-kernel audit of the new finite protocols.

No old audit root set or source binding is modified. Cached pinned third-party
Mathlib outputs may be reused; every audited proof dependency is replayed in
an empty trust-zero kernel.
"""
from pathlib import Path
import argparse, datetime, hashlib, json, os, re, shutil, signal, subprocess, time
ROOT=Path(__file__).resolve().parent
REPO=ROOT.parent.parent
PIN='d13f23b723b8a846827a245b89c10fc7d3f11612'
ALLOWED_AXIOMS={'propext','Classical.choice','Quot.sound'}
PACKAGES=['extraction-spectral-protocol','spectral-extraction-core',
          'spectral-extraction-local-cap','extraction-symmetric-support',
          'appt-qutrit-purity','appt-high-dimensional-review','extraction-information-spectrum']

def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def strip_comments(s): return re.sub(r'/\-.*?\-/|--[^\n]*','',s,flags=re.S)
def math_roots():
    result=[]
    for f in sorted((ROOT/'SpectralProtocol').glob('*.lean')):
        result += ['SpectralProtocol.'+x for x in re.findall(r'^theorem\s+([A-Za-z0-9_\u0080-\uffff]+)',strip_comments(f.read_text()),flags=re.M)]
    return result

def inventory():
    selected={ROOT/f for f in ['lean-toolchain','lakefile.toml','lake-manifest.json',
      'SpectralProtocol.lean','ProtocolVerification.lean','ProtocolVerification/ReplaySupport.lean',
      'reproduce.py','README.md','ROOTS.txt','Audit.lean','Check.lean']}
    selected.update((ROOT/'SpectralProtocol').glob('*.lean'))
    pending=list(selected & set(ROOT.rglob('*.lean')))
    seen=set()
    while pending:
        f=pending.pop()
        if f in seen: continue
        seen.add(f)
        for raw in re.findall(r'^import\s+([^\n]+)',f.read_text(),flags=re.M):
            for module in raw.split():
                if module.startswith(('Mathlib.','Lean.')) or module=='Lean': continue
                candidates=[ROOT.parent/pkg/(module.replace('.','/')+'.lean') for pkg in PACKAGES]
                found=[x for x in candidates if x.is_file()]
                if len(found)!=1: raise RuntimeError('Nonunique/missing local import '+module)
                g=found[0]
                if g not in selected: selected.add(g);pending.append(g)
    for pkg in PACKAGES:
        d=ROOT.parent/pkg
        for name in ['lean-toolchain','lakefile.toml','lake-manifest.json']:
            if (d/name).exists(): selected.add(d/name)
    return {p.relative_to(REPO).as_posix():sha(p) for p in sorted(selected)}

def check():
    if inventory()!=json.loads((ROOT/'SOURCE_HASHES.json').read_text()):
        raise RuntimeError('Source binding changed')
    if (ROOT/'lean-toolchain').read_text().strip()!='leanprover/lean4:v4.34.1':
        raise RuntimeError('Wrong Lean toolchain')
    manifest=json.loads((ROOT/'lake-manifest.json').read_text())
    if [p.get('rev') for p in manifest['packages'] if p['name']=='mathlib']!=[PIN]:
        raise RuntimeError('Wrong Mathlib pin')
    for p in manifest['packages']:
        if p['type']!='git': continue
        package=ROOT/'.lake/packages'/p['name']
        if not package.exists(): continue
        actual=subprocess.check_output(['git','-C',str(package),'rev-parse','HEAD'],text=True).strip()
        if actual!=p['rev']: raise RuntimeError('Wrong dependency pin: '+p['name'])
        if subprocess.run(['git','-C',str(package),'diff','--quiet']).returncode:
            raise RuntimeError('Tracked dependency edits: '+p['name'])
    for p in (ROOT/'SpectralProtocol').glob('*.lean'):
        if re.search(r'\b(sorry|admit|axiom|native_decide|unsafe)\b',strip_comments(p.read_text())):
            raise RuntimeError('Forbidden mathematical proof token: '+str(p))
    roots=(ROOT/'ROOTS.txt').read_text().splitlines()
    if len(roots)!=len(set(roots)) or set(roots)!=set(math_roots()):
        raise RuntimeError('Root coverage differs from actual mathematical theorem declarations')
    print('SOURCE_BINDING_PASS',len(inventory()),'ROOTS',len(roots),flush=True)

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--write-manifest',action='store_true')
    ap.add_argument('--check-only',action='store_true');ap.add_argument('--fresh',action='store_true')
    args=ap.parse_args()
    if args.write_manifest:
        (ROOT/'SOURCE_HASHES.json').write_text(json.dumps(inventory(),indent=2)+'\n')
        print('MANIFEST_WRITTEN_NOT_VERIFICATION');return
    check()
    if args.check_only:return
    if args.fresh:
        output=ROOT/'.lake/build'
        if output.is_symlink() or output.name!='build' or not output.resolve().is_relative_to(ROOT.resolve()):
            raise RuntimeError('Unsafe output directory')
        if output.exists():shutil.rmtree(output)
    out=ROOT/'verification'/('reproduction-'+datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%SZ'))
    out.mkdir(parents=True,exist_ok=False);records=[]
    shutil.copy2(ROOT/'SOURCE_HASHES.json',out/'SOURCE_HASHES.json')
    def stage(name,cmd,limit):
        log=out/(name+'.log');start=time.monotonic()
        with log.open('w') as f:
            p=subprocess.Popen(cmd,cwd=ROOT,stdout=f,stderr=subprocess.STDOUT,start_new_session=True)
            try:code=p.wait(timeout=limit)
            except subprocess.TimeoutExpired:os.killpg(p.pid,signal.SIGKILL);p.wait();code=124
        record=dict(stage=name,command=cmd,exit_code=code,seconds=round(time.monotonic()-start,3),log=log.name,sha256=sha(log))
        records.append(record);(out/'STAGES.json').write_text(json.dumps(records,indent=2)+'\n');print(json.dumps(record),flush=True)
        if code: print(log.read_text()[-10000:]);raise RuntimeError('Failed stage '+name)
        return log.read_text()
    stage('toolchain',['lake','env','lean','--version'],60)
    stage('build',['lake','build','SpectralProtocol','ProtocolVerification'],900)
    stage('types-and-axioms',['lake','env','lean','-j1','-M6000','Check.lean'],120)
    audit=stage('kernel',['lake','env','lean','-j1','-M10000','Audit.lean'],1200)
    controls=len(re.findall(r'^run_cmd ProtocolVerification.rejectCorruptTheorem', (ROOT/'Audit.lean').read_text(),flags=re.M))+1
    if audit.count('EMPTY_KERNEL_REPLAY_PASS')!=1 or audit.count('CORRUPTED_PROOF_REJECTED')!=controls:
        raise RuntimeError('Incomplete audit markers')
    axioms=set((ROOT/'verification/protocol-kernel-axioms.txt').read_text().splitlines())
    if not axioms<=ALLOWED_AXIOMS: raise RuntimeError('Unexpected kernel axioms')
    for p in (ROOT/'verification').glob('protocol-*.txt'):shutil.copy2(p,out/p.name)
    check()
    result=dict(status='PASS',scope='Literal elementary Bell tensor target; actual joint multiblock unitary and complete local sector decoders with all off-diagonal blocks removed; weighted support-mass and post-unitary local-reset baseline bounds; actual finite product-PPT bridge and convention equivalence; original-space spectral prefix lower and support-mass extraction; actual pure-iid integer Bell optimum and real-floor identity; normalized pure-iid adversarial average and finite physical upper/lower bounds; local sector Kraus semantics and complete multisector protocols. No full Schur, universal mixed-state rate limits, Haar rank-s law, gate synthesis, or full paper certification.',fresh_own_output_build=args.fresh,source_files=len(inventory()),roots=len(math_roots()),kernel_declarations=int(re.search(r'EMPTY_KERNEL_REPLAY_PASS (\d+) declarations',audit).group(1)),kernel_trust=0,axioms=sorted(axioms),same_type_forged_proof_controls=controls,source_manifest_sha256=sha(ROOT/'SOURCE_HASHES.json'),stages=records)
    (out/'SUMMARY.json').write_text(json.dumps(result,indent=2)+'\n')
    (ROOT/'verification/LATEST.json').write_text(json.dumps(dict(directory=out.name,summary_sha256=sha(out/'SUMMARY.json')),indent=2)+'\n')
    print('SPECTRAL_PROTOCOL_REPRODUCTION_PASS',out,flush=True)
if __name__=='__main__':main()