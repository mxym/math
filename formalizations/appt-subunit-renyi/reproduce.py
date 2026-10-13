#!/usr/bin/env python3
"""Source-bound fresh own-module build and empty-kernel replay; scope is partial."""
from pathlib import Path
import argparse,hashlib,json,re,shutil,subprocess,os,time,signal
ROOT=Path(__file__).resolve().parent
REPO=ROOT.parent.parent
PIN='d13f23b723b8a846827a245b89c10fc7d3f11612'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def inventory():
    selected={ROOT/n for n in ['lean-toolchain','lakefile.toml','lake-manifest.json','reproduce.py','check_half_certificate.py','half_certificate.json','ROOTS.txt','Audit.lean']}
    seen=set()
    def visit(name):
        if name in seen:return
        seen.add(name)
        if name=='APPTSubunit' or name.startswith('APPTSubunit.'):base=ROOT
        elif name.startswith('APPTReview.'):base=ROOT.parent/'appt-high-dimensional-review'
        elif name.startswith(('APPT.','Verification.')):base=ROOT.parent/'appt-qutrit-purity'
        else:return
        p=base/(name.replace('.','/')+'.lean');selected.add(p)
        for line in re.findall(r'^import\s+([^\n]+)',p.read_text(),re.M):
            for dep in line.split():visit(dep)
    visit('APPTSubunit');visit('Verification.ReplaySupport')
    for pkg in ['appt-high-dimensional-review','appt-qutrit-purity']:
        for n in ['lean-toolchain','lakefile.toml','lake-manifest.json']:selected.add(ROOT.parent/pkg/n)
    selected.add(REPO/'research/appt-multilevel-counterexample/SUBUNIT_RENYI.md')
    return {p.relative_to(REPO).as_posix():sha(p) for p in sorted(selected)}
def check():
    if inventory()!=json.loads((ROOT/'SOURCE_HASHES.json').read_text()):raise RuntimeError('Source binding changed')
    if (ROOT/'lean-toolchain').read_text().strip()!='leanprover/lean4:v4.34.1':raise RuntimeError('Wrong Lean pin')
    for pkg in [ROOT,ROOT.parent/'appt-high-dimensional-review',ROOT.parent/'appt-qutrit-purity']:
        manifest=json.loads((pkg/'lake-manifest.json').read_text())
        if [p.get('rev') for p in manifest['packages'] if p['name']=='mathlib']!=[PIN]:raise RuntimeError('Wrong Mathlib manifest')
    mathlib=ROOT/'.lake/packages/mathlib'
    if mathlib.exists():
        if subprocess.check_output(['git','-C',str(mathlib),'rev-parse','HEAD'],text=True).strip()!=PIN:raise RuntimeError('Actual Mathlib pin differs')
        if subprocess.run(['git','-C',str(mathlib),'diff','--quiet'],capture_output=True).returncode:raise RuntimeError('Mathlib source has tracked edits')
        manifest=json.loads((ROOT/'lake-manifest.json').read_text())
        for p in manifest['packages']:
            if p['type']=='git':
                actual=subprocess.check_output(['git','-C',str(ROOT/'.lake/packages'/p['name']),'rev-parse','HEAD'],text=True).strip()
                if actual!=p['rev']:raise RuntimeError('Actual dependency pin differs '+p['name'])
    for p in (ROOT/'APPTSubunit').glob('*.lean'):
        code=re.sub(r'/\-.*?\-/|--[^\n]*','',p.read_text(),flags=re.S)
        if re.search(r'\b(sorry|admit|axiom|native_decide|unsafe)\b',code):raise RuntimeError('Forbidden proof token '+str(p))
    print('SOURCE_BINDING_PASS',len(inventory()),flush=True)
def main():
    ap=argparse.ArgumentParser();ap.add_argument('--write-manifest',action='store_true');ap.add_argument('--check-only',action='store_true');ap.add_argument('--fresh',action='store_true');a=ap.parse_args()
    if a.write_manifest:(ROOT/'SOURCE_HASHES.json').write_text(json.dumps(inventory(),indent=2)+'\n');print('MANIFEST_WRITTEN_NOT_VERIFICATION');return
    check()
    if a.check_only:return
    if a.fresh:
        p=ROOT/'.lake/build'
        if p.is_symlink() or not p.resolve().is_relative_to(ROOT.resolve()):raise RuntimeError('Unsafe build path')
        if p.exists():shutil.rmtree(p)
    out=ROOT/'verification/reproduction';out.mkdir(parents=True,exist_ok=True);records=[]
    def stage(name,cmd,limit):
        log=out/(name+'.log');start=time.monotonic()
        with log.open('w') as f:
            p=subprocess.Popen(cmd,cwd=ROOT,stdout=f,stderr=subprocess.STDOUT,start_new_session=True)
            try:code=p.wait(timeout=limit)
            except subprocess.TimeoutExpired:os.killpg(p.pid,signal.SIGKILL);p.wait();code=124
        record={'stage':name,'command':cmd,'exit_code':code,'seconds':round(time.monotonic()-start,3),'log':log.name,'sha256':sha(log)}
        records.append(record);(out/'STAGES.json').write_text(json.dumps(records,indent=2)+'\n');print(json.dumps(record),flush=True)
        if code:print(log.read_text()[-12000:]);raise RuntimeError('Failed stage '+name)
        return log.read_text()
    stage('toolchain',['lake','env','lean','--version'],60)
    stage('certificate',['python3','check_half_certificate.py'],60)
    stage('certificate-optimized',['python3','-O','check_half_certificate.py'],60)
    stage('build',['lake','build','APPTSubunit'],600)
    dest=ROOT/'.lake/build/lib/lean/Verification/ReplaySupport.olean';dest.parent.mkdir(parents=True,exist_ok=True)
    old=ROOT.parent/'appt-qutrit-purity'
    stage('support',['lake','env','lean','-j1','-M6000','--root='+str(old),'-o',str(dest),str(old/'Verification/ReplaySupport.lean')],90)
    audit=stage('kernel',['lake','env','lean','-j1','-M6000','Audit.lean'],600)
    if 'EMPTY_KERNEL_REPLAY_PASS' not in audit or audit.count('CORRUPTED_PROOF_REJECTED')!=6:raise RuntimeError('Incomplete audit markers')
    axioms=set((ROOT/'subunit-kernel-axioms.txt').read_text().splitlines())
    if not axioms<={'propext','Classical.choice','Quot.sound'}:raise RuntimeError('Unexpected axioms')
    for p in ROOT.glob('subunit-*.txt'):shutil.copy2(p,out/p.name)
    check();count=int(re.search(r'EMPTY_KERNEL_REPLAY_PASS (\d+) declarations',audit).group(1))
    result={'status':'PASS','scope':'Finite downward-spike all-unitary APPT density construction and exact purity; arbitrary-dimensional half-order head bound with real spectral/pivot bridge and continuum rational polynomial certificate. NOT the complete arbitrary-order sharp entropy limit or negative high-hierarchy construction.','source_files':len(inventory()),'own_modules':len(list((ROOT/'APPTSubunit').glob('*.lean'))),'roots':len((ROOT/'ROOTS.txt').read_text().splitlines()),'kernel_declarations':count,'kernel_trust':0,'axioms':sorted(axioms),'unchanged_type_corruption_controls':6,'source_manifest_sha256':sha(ROOT/'SOURCE_HASHES.json'),'stages':records}
    (out/'SUMMARY.json').write_text(json.dumps(result,indent=2)+'\n');print('SUBUNIT_REPRODUCTION_PASS',flush=True)
if __name__=='__main__':main()
