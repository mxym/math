#!/usr/bin/env python3
"""Separate actual raw-resource CI producer; one source binding from its first version."""
from pathlib import Path
import argparse,os,re,shutil,subprocess,sys
import reproduce as a
from audit_runtime import configure,hosted_context,check_ci_binaries
WORKFLOW='.github/workflows/extraction-raw-resource.yml'
TEMPLATE='extraction-raw-resource.workflow.yml'
EXPORTS=['SOURCE_HASHES.json','PROTECTED_INPUTS.json','SCOPE.json','ROOTS.txt','DEFINITIONS.txt','CONTROLS.txt','CI_EXECUTION_POLICY.json']


def workflow_binding():
    path=a.REPO/WORKFLOW
    if path.is_symlink()or not path.is_file()or a.sha(path)!=a.sha(a.ROOT/TEMPLATE):raise RuntimeError('Actual raw-resource workflow differs from source-bound template')
    return dict(path=WORKFLOW,sha256=a.sha(path),bound_template_sha256=a.sha(a.ROOT/TEMPLATE))


def check_commit(commit):
    a.check_binding(check_dependencies=False)
    if not re.fullmatch(r'[a-f0-9]{40}',commit)or a.run('git','rev-parse','HEAD')!=commit:raise RuntimeError('Checkout is not exact immutable event commit')
    workflow_binding()
    paths=[a.ROOT/'SOURCE_HASHES.json',a.ROOT/'PROTECTED_INPUTS.json',a.REPO/WORKFLOW]+[a.REPO/name for name in a.inventory()]
    for path in paths:
        name=path.relative_to(a.REPO).as_posix()
        if path.read_bytes()!=subprocess.check_output(['git','show',commit+':'+name],cwd=a.REPO):raise RuntimeError('Bound input differs from event Git blob '+name)


def identity():
    names=['GITHUB_SHA','GITHUB_RUN_ID','GITHUB_RUN_ATTEMPT','GITHUB_REPOSITORY','GITHUB_WORKFLOW_REF','GITHUB_WORKFLOW_SHA']
    v={name:os.environ[name]for name in names}
    if v['GITHUB_REPOSITORY']!='mxym/math'or v['GITHUB_WORKFLOW_SHA']!=v['GITHUB_SHA']or not v['GITHUB_WORKFLOW_REF'].startswith('mxym/math/'+WORKFLOW+'@refs/'):raise RuntimeError('Wrong actual raw-resource workflow identity')
    return dict(source_commit=v['GITHUB_SHA'],run_id=v['GITHUB_RUN_ID'],run_attempt=v['GITHUB_RUN_ATTEMPT'],repository=v['GITHUB_REPOSITORY'],workflow_ref=v['GITHUB_WORKFLOW_REF'],workflow_commit=v['GITHUB_WORKFLOW_SHA'])


def snapshot(binaries):
    return dict(source_manifest_sha256=a.sha(a.ROOT/'SOURCE_HASHES.json'),source_inputs=a.inventory(),protected_inputs=a.old_inventory(),protected_manifest_sha256=a.sha(a.ROOT/'PROTECTED_INPUTS.json'),actual_workflow=workflow_binding(),binaries=binaries)


def main():
    parser=argparse.ArgumentParser();parser.add_argument('command',choices=['environment','bootstrap','run']);args=parser.parse_args()
    runtime=configure(True);env,output=runtime['env'],runtime['output'];check_commit(os.environ['GITHUB_SHA']);who=identity();output.mkdir(exist_ok=True)
    if args.command=='environment':
        with open(os.environ['GITHUB_ENV'],'a')as handle:
            for key in ['TMPDIR','MATHLIB_CACHE_DIR','XDG_CACHE_HOME','ELAN_HOME']:
                if '\n'in env[key]:raise RuntimeError('Invalid exclusive runtime path')
                handle.write(key+'='+env[key]+'\n')
            handle.write('EXTRACTION_RAW_RESOURCE_EVIDENCE='+str(output)+'\n')
        print('RAW_RESOURCE_EXCLUSIVE_GITHUB_STORAGE_CONFIGURED');return
    policy=a.readj(a.ROOT/'CI_EXECUTION_POLICY.json')
    if args.command=='bootstrap':
        installer=hosted_context()/'elan-init.sh'
        subprocess.run(['curl','--fail','--location','--retry','3','--connect-timeout','15','--max-time','90',policy['elan_init_url'],'--output',str(installer)],env=env,check=True)
        a.dump(output/'BOOTSTRAP.json',dict(installer_url=policy['elan_init_url'],installer_sha256=a.sha(installer),github=who,actual_workflow=workflow_binding(),source_manifest_sha256=a.sha(a.ROOT/'SOURCE_HASHES.json')))
        subprocess.run(['sh',str(installer),'-y','--no-modify-path','--default-toolchain','none'],env=env,cwd=a.ROOT,check=True)
        subprocess.run([env['ELAN_HOME']+'/bin/elan','toolchain','install',policy['lean_toolchain']],env=env,cwd=a.ROOT,check=True)
        a.dump(output/'BOOTSTRAP_BINARIES.json',check_ci_binaries())
        subprocess.run(['lake','exe','cache','get'],env=env,cwd=a.ROOT,check=True)
        check_commit(who['source_commit']);a.check_pins();print('RAW_RESOURCE_PINNED_CI_BOOTSTRAP_PASS');return
    before=snapshot(check_ci_binaries());a.dump(output/'PRE_AUDIT.json',before)
    command=[sys.executable,'reproduce.py','--github-actions','--fresh']
    with (output/'driver.log').open('w')as log:
        process=subprocess.Popen(command,cwd=a.ROOT,env=env,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
        for line in process.stdout:log.write(line);log.flush();print(line,end='',flush=True)
        if process.wait():raise RuntimeError('Full raw-resource mathematical audit failed')
    after=snapshot(check_ci_binaries());check_commit(who['source_commit'])
    if before!=after:raise RuntimeError('Source/execution/workflow/tool drift across CI')
    a.dump(output/'POST_AUDIT.json',after)
    a.dump(output/'CI_CONTEXT.json',dict(who,status='GITHUB_CI_AUDIT_COMPLETED_PENDING_ARTIFACT_DOWNLOAD_CHECK',actual_workflow=workflow_binding(),source_manifest_sha256=a.sha(a.ROOT/'SOURCE_HASHES.json'),latest=a.readj(output/'LATEST.json'),actual_command=command[1:],actual_cwd=a.ROOT.relative_to(a.REPO).as_posix()))
    for name in EXPORTS:shutil.copy2(a.ROOT/name,output/name)
    recipe=output/'recipe';recipe.mkdir()
    for name in a.inventory():
        source=a.REPO/name
        if source.is_relative_to(a.ROOT):
            target=recipe/source.relative_to(a.ROOT);target.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(source,target)
    a.dump(output/'ARTIFACT_HASHES.json',{path.relative_to(output).as_posix():a.sha(path)for path in sorted(output.rglob('*'))if path.is_file()and path!=output/'ARTIFACT_HASHES.json'})
    print('RAW_RESOURCE_FULL_CI_EVIDENCE_SEALED_PENDING_DOWNLOAD_CHECK')

if __name__=='__main__':main()
