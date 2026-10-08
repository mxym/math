#!/usr/bin/env python3
"""Separate axiom-signature addendum. No rebuild of the frozen Bapat proof."""
import argparse
import datetime
import hashlib
import json
import os
from pathlib import Path
import subprocess

ROOT=Path(__file__).resolve().parent
PIN='5045d0056413266e57c625dcd7c365b10e377c52'

def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--environment-json',required=True,type=Path)
    ap.add_argument('--bapat-build',required=True,type=Path)
    ap.add_argument('--output',required=True,type=Path)
    args=ap.parse_args()
    conf=json.loads(args.environment_json.read_text())
    toolchain=Path(conf['toolchain_path']);lean=toolchain/'bin/lean'
    commit=subprocess.check_output([str(lean),'--githash'],text=True).strip()
    if commit!=PIN: raise RuntimeError('LEAN_COMMIT_MISMATCH')
    output=args.output.resolve();output.mkdir(parents=True,exist_ok=False)
    (output/'build').mkdir();(output/'audit').mkdir()
    env=os.environ.copy();env.pop('LEAN_SRC_PATH',None)
    env['LEAN_PATH']=':'.join([str(args.bapat_build.resolve()),str(output/'build')]+
      [str(Path(conf['packages_root'])/p['name']/'.lake/build/lib/lean') for p in conf['packages']]+
      [str(toolchain/'lib/lean')])
    env['STANDARD_AXIOM_OUTPUT']=str(output/'actual-standard-axioms.json')
    env['INDEPENDENT_AUDIT_OUTPUT']=str(output/'audit')
    commands=[]
    def run(label,argv):
        begin=datetime.datetime.now(datetime.timezone.utc).isoformat()
        with (output/(label+'.log')).open('w') as f:
            r=subprocess.run(argv,stdout=f,stderr=subprocess.STDOUT,env=env,cwd=ROOT,timeout=1800)
        commands.append({'label':label,'argv':list(map(str,argv)),'started_utc':begin,
          'ended_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'exit_code':r.returncode})
        (output/'commands.json').write_text(json.dumps(commands,indent=2)+'\n')
        if r.returncode: raise RuntimeError('FAILED: '+label)
    run('guard-compile',[str(lean),'-o',str(output/'build/StandardAxiomGuard.olean'),str(ROOT/'sources/StandardAxiomGuard.lean')])
    run('loaded-bapat-axioms',[str(lean),str(ROOT/'sources/CheckLoadedAxioms.lean')])
    run('smoke-compile',[str(lean),'-o',str(output/'build/SmokeOwned.olean'),str(ROOT/'sources/SmokeOwned.lean')])
    template=(ROOT/'OwnedAudit.standard-axioms-v1.template.lean').read_text()
    roots=['StandardAxiomSmoke.propext_control','StandardAxiomSmoke.choice_control','StandardAxiomSmoke.quotient_control']
    instantiated=template.replace('@@IMPORTS@@','import SmokeOwned').replace('@@MODULES@@','#[ "SmokeOwned" ]').replace('@@ROOTS@@','#[ '+', '.join('``'+r for r in roots)+' ]')
    check=output/'SmokeAudit.lean';check.write_text(instantiated)
    run('hardened-smoke-audit',[str(lean),'-j2','-M6144',str(check)])
    run('invalid-proof-kernel-control',[str(lean),str(ROOT/'sources/RejectInvalidProof.lean')])
    evidence={'status':'PASS_AXIOM_SIGNATURE_ADDENDUM','lean_commit':commit,
      'lean_version':subprocess.check_output([str(lean),'--version'],text=True).strip(),
      'lean_binary_sha256':sha(lean),'lean_runtime_sha256':sha(toolchain/'lib/lean/libleanshared.so'),
      'frozen_bapat_modules_recompiled':False,'actual_bapat_import_environment_checked':True,
      'signature_negative_controls_rejected':13,'small_hardened_replay':json.loads((output/'audit/replay-summary.json').read_text()),
      'original_invalid_proof_control':'PASS','comparison':'Structural alpha-equivalence: binder names erased, universe parameters renamed by index; full Expr.equal preserves binder visibility and all remaining syntax; no unfolding or definitional reduction.',
      'source_hashes':{str(p.relative_to(ROOT)):sha(p) for p in sorted((ROOT/'sources').glob('*.lean'))},
      'hardened_template_sha256':sha(ROOT/'OwnedAudit.standard-axioms-v1.template.lean'),
      'search_path':env['LEAN_PATH'].split(':')}
    (output/'RESULT.json').write_text(json.dumps(evidence,indent=2)+'\n')
    print(json.dumps(evidence,indent=2))

if __name__=='__main__':main()
