#!/usr/bin/env python3
"""Hosted-GitHub bootstrap, strict full-scope audit, and portable artifact sealing."""
from pathlib import Path
import argparse,hashlib,json,os,shutil,subprocess,sys
import reproduce as a
from audit_runtime import configure,hosted_context,check_ci_binaries

def source_precheck():
    s,roots,defs,controls=a.scope_lists()
    if s['state']!='READY' or s['pending_required']:raise RuntimeError('CI requires final READY source binding')
    if a.inventory()!=a.readj(a.ROOT/'SOURCE_HASHES.json') or a.old_inventory()!=a.readj(a.ROOT/'FROZEN_OLD_INPUTS.json'):
        raise RuntimeError('Bound source/protected history mismatch')
    a.validate_source_head(s,a.inventory())
    expected=a.readj(a.ROOT/'CI_EXECUTION_POLICY.json')['expected_scope']
    actual=dict(endpoint_theorems=len(roots),model_definitions=len(defs),same_type_controls=len(controls))
    if actual!=expected:raise RuntimeError('CI scope is not the fixed planned endpoint/definition/control scope')
    workflow=a.REPO/'.github/workflows/extraction-algorithm.yml'
    if workflow.read_bytes()!=(a.ROOT/'extraction-algorithm.workflow.yml').read_bytes():raise RuntimeError('Installed workflow differs from bound template')
    return s

def main():
    ap=argparse.ArgumentParser();ap.add_argument('command',choices=['environment','bootstrap','run']);args=ap.parse_args()
    runtime=configure(True);env=runtime['env'];output=runtime['output'];output.mkdir(exist_ok=True)
    if args.command=='environment':
        with open(os.environ['GITHUB_ENV'],'a') as f:
            for key in ['TMPDIR','MATHLIB_CACHE_DIR','XDG_CACHE_HOME','ELAN_HOME']:
                if '\n' in env[key]:raise RuntimeError('Invalid runtime path')
                f.write(key+'='+env[key]+'\n')
            f.write('EXTRACTION_ALGORITHM_EVIDENCE='+str(output)+'\n')
        print('EXCLUSIVE_GITHUB_RUNTIME_CONFIGURED '+str(output));return
    source_precheck();policy=a.readj(a.ROOT/'CI_EXECUTION_POLICY.json')
    if args.command=='bootstrap':
        installer=hosted_context()/'elan-init.sh'
        subprocess.run(['curl','--fail','--location','--retry','3','--connect-timeout','15','--max-time','90',policy['elan_init_url'],'--output',str(installer)],env=env,check=True)
        a.dump(output/'BOOTSTRAP.json',dict(installer_url=policy['elan_init_url'],installer_sha256=a.sha(installer)))
        subprocess.run(['sh',str(installer),'-y','--no-modify-path','--default-toolchain','none'],env=env,cwd=a.ROOT,check=True)
        subprocess.run([env['ELAN_HOME']+'/bin/elan','toolchain','install',policy['lean_toolchain']],env=env,cwd=a.ROOT,check=True)
        binaries=check_ci_binaries();a.dump(output/'BOOTSTRAP_BINARIES.json',binaries)
        subprocess.run(['lake','exe','cache','get'],env=env,cwd=a.ROOT,check=True)
        source_precheck();a.check_pins();print('PINNED_CI_BOOTSTRAP_PASS');return
    before=dict(source_manifest_sha256=a.sha(a.ROOT/'SOURCE_HASHES.json'),source_inputs=a.inventory(),binaries=check_ci_binaries())
    a.dump(output/'PRE_AUDIT.json',before)
    with (output/'driver.log').open('w') as log:
        process=subprocess.Popen([sys.executable,'reproduce.py','--github-actions','--fresh'],cwd=a.ROOT,env=env,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
        for line in process.stdout:
            log.write(line);log.flush();print(line,end='',flush=True)
        code=process.wait()
    if code:raise RuntimeError('Full CI audit failed with exit '+str(code))
    after=dict(source_manifest_sha256=a.sha(a.ROOT/'SOURCE_HASHES.json'),source_inputs=a.inventory(),binaries=check_ci_binaries())
    if before!=after:raise RuntimeError('Source/tool drift across CI audit')
    source_precheck();a.dump(output/'POST_AUDIT.json',after)
    workflow_binding=dict(path='.github/workflows/extraction-algorithm.yml',sha256=a.sha(a.REPO/'.github/workflows/extraction-algorithm.yml'),bound_template_sha256=a.sha(a.ROOT/'extraction-algorithm.workflow.yml'))
    context=dict(actual_workflow=workflow_binding,status='GITHUB_CI_AUDIT_COMPLETED_PENDING_ARTIFACT_DOWNLOAD_CHECK',source_commit=os.environ['GITHUB_SHA'],run_id=os.environ['GITHUB_RUN_ID'],run_attempt=os.environ['GITHUB_RUN_ATTEMPT'],repository=os.environ['GITHUB_REPOSITORY'],source_manifest_sha256=before['source_manifest_sha256'],latest=a.readj(output/'LATEST.json'))
    a.dump(output/'CI_CONTEXT.json',context)
    for name in ['SOURCE_HASHES.json','FROZEN_OLD_INPUTS.json','SCOPE.json','ROOTS.txt','DEFINITIONS.txt','CONTROLS.txt','CI_EXECUTION_POLICY.json']:
        shutil.copy2(a.ROOT/name,output/name)
    hashes={p.relative_to(output).as_posix():a.sha(p) for p in sorted(output.rglob('*')) if p.is_file() and p.name!='ARTIFACT_HASHES.json'}
    a.dump(output/'ARTIFACT_HASHES.json',hashes)
    print('FULL_CI_EVIDENCE_SEALED_PENDING_DOWNLOAD_CHECK '+str(output))

if __name__=='__main__':main()
