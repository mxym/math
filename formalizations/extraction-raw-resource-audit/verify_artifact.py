#!/usr/bin/env python3
"""Validate every downloaded byte, exact executed recipe, full replay and controls."""
from pathlib import Path
import argparse,json,re
import reproduce as a
import ci_driver as c
from evidence import verify_run


def verify(directory,expected_commit,run_id,run_attempt):
    c.check_commit(expected_commit)
    for value in [str(run_id),str(run_attempt)]:
        if not re.fullmatch(r'[0-9]+',value):raise RuntimeError('Invalid immutable run identity')
    base=Path(directory).resolve();hashes=a.readj(base/'ARTIFACT_HASHES.json')
    if any(path.is_symlink()for path in base.rglob('*')):raise RuntimeError('Artifact contains symlink')
    actual={path.relative_to(base).as_posix()for path in base.rglob('*')if path.is_file()and path!=base/'ARTIFACT_HASHES.json'}
    if actual!=set(hashes):raise RuntimeError('Artifact missing/extra files')
    for name,digest in hashes.items():
        path=base/name
        if not isinstance(name,str)or Path(name).is_absolute()or Path(name).as_posix()!=name or any(part in {'.','..'}for part in Path(name).parts)or not path.resolve().is_relative_to(base)or a.sha(path)!=digest:raise RuntimeError('Artifact byte hash mismatch '+name)
    context=a.readj(base/'CI_CONTEXT.json');identity=dict(source_commit=expected_commit,workflow_commit=expected_commit,run_id=str(run_id),run_attempt=str(run_attempt),repository='mxym/math')
    if any(context.get(key)!=value for key,value in identity.items())or not context.get('workflow_ref','').startswith('mxym/math/'+c.WORKFLOW+'@refs/'):raise RuntimeError('Wrong immutable workflow/run identity')
    if context.get('status')!='GITHUB_CI_AUDIT_COMPLETED_PENDING_ARTIFACT_DOWNLOAD_CHECK'or context.get('actual_workflow')!=c.workflow_binding():raise RuntimeError('Wrong actual completed workflow')
    if context.get('actual_command')!=['reproduce.py','--github-actions','--fresh']or context.get('actual_cwd')!=a.ROOT.relative_to(a.REPO).as_posix():raise RuntimeError('Wrong actual recipe command')
    for name in c.EXPORTS:
        if (base/name).read_bytes()!=(a.ROOT/name).read_bytes():raise RuntimeError('Export differs from source-bound checkout '+name)
    if context['source_manifest_sha256']!=a.sha(a.ROOT/'SOURCE_HASHES.json'):raise RuntimeError('Source manifest identity differs')
    recipe=base/'recipe';expected_recipe={}
    for name,digest in a.inventory().items():
        source=a.REPO/name
        if source.is_relative_to(a.ROOT):expected_recipe[source.relative_to(a.ROOT).as_posix()]=digest
    if {path.relative_to(recipe).as_posix():a.sha(path)for path in recipe.rglob('*')if path.is_file()}!=expected_recipe:raise RuntimeError('Actual exported execution recipe differs')
    pre=a.readj(base/'PRE_AUDIT.json');post=a.readj(base/'POST_AUDIT.json')
    policy=a.readj(a.ROOT/'CI_EXECUTION_POLICY.json');binaries=pre['binaries']
    if set(binaries)!=set(policy['binary_sha256'])or {key:value['sha256']for key,value in binaries.items()}!=policy['binary_sha256']:raise RuntimeError('Wrong toolchain binaries')
    if pre!=post or pre!=c.snapshot(binaries):raise RuntimeError('Source/protected/execution pre-post drift')
    if a.readj(base/'BOOTSTRAP_BINARIES.json')!=binaries:raise RuntimeError('Bootstrap/audit binary drift')
    bootstrap=a.readj(base/'BOOTSTRAP.json')
    if bootstrap['github']!={key:context[key]for key in identity|{'workflow_ref':None}}or bootstrap['actual_workflow']!=c.workflow_binding()or bootstrap['source_manifest_sha256']!=context['source_manifest_sha256']or bootstrap['installer_url']!=policy['elan_init_url']:raise RuntimeError('Wrong bootstrap source/workflow/run identity')
    latest=a.readj(base/'LATEST.json')
    if latest!=context['latest']or Path(latest['directory']).name!=latest['directory']:raise RuntimeError('Invalid latest pointer')
    out=base/latest['directory']
    if a.sha(out/'SUMMARY.json')!=latest['summary_sha256']:raise RuntimeError('Summary digest differs')
    result=verify_run(out,'GITHUB_HOSTED_LINUX_RUNNER_VERIFIED')
    invocation=a.readj(out/'STAGES.json')[-1]['command'][-1]
    expected=Path('/home/runner/work/_temp')/('extraction-raw-resource-'+str(run_id)+'-'+str(run_attempt))/'evidence'/latest['directory']/'AuditInvocation.lean'
    if Path(invocation)!=expected:raise RuntimeError('Replay did not use exclusive actual hosted output')
    execution=a.readj(out/'EXECUTION.json')
    if execution['guard']!='GITHUB_HOSTED_LINUX_RUNNER_VERIFIED'or execution['execution_inputs']!=policy or execution['portable_binary_inputs']!=binaries:raise RuntimeError('Wrong actual runtime/tool policy')
    return dict(result,status='DOWNLOADED_FULL_RAW_RESOURCE_CI_ARTIFACT_VERIFIED',source_commit=expected_commit,run_id=str(run_id),run_attempt=str(run_attempt),actual_workflow=c.workflow_binding())

if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('directory');ap.add_argument('--expected-commit',required=True);ap.add_argument('--run-id',required=True);ap.add_argument('--run-attempt',required=True);args=ap.parse_args();print(json.dumps(verify(args.directory,args.expected_commit,args.run_id,args.run_attempt),indent=2))
