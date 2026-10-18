#!/usr/bin/env python3
"""Verify a freshly downloaded evidence bundle against this exact checkout."""
from pathlib import Path
import argparse,json,re,sys,hashlib
sys.path.insert(0,str(Path(__file__).resolve().parents[2]))
import reproduce as a

def axiom_set(path):
    raw=path.read_text()
    if raw=="\n":return set()
    lines=raw.splitlines()
    if not lines or len(lines)!=len(set(lines))or any(not n or n.strip()!=n for n in lines):raise RuntimeError('Noncanonical axiom-list encoding')
    return set(lines)

def verify(directory,expected_commit=None,run_id=None):
    base=Path(directory).resolve();hashes=a.readj(base/'ARTIFACT_HASHES.json')
    actual={p.relative_to(base).as_posix() for p in base.rglob('*') if p.is_file() and p.name!='ARTIFACT_HASHES.json'}
    if actual!=set(hashes):raise RuntimeError('Artifact has missing/extra files')
    for rel,digest in hashes.items():
        p=base/rel
        if p.is_symlink() or not p.resolve().is_relative_to(base) or a.sha(p)!=digest:raise RuntimeError('Artifact byte hash mismatch '+rel)
    context=a.readj(base/'CI_CONTEXT.json')
    if expected_commit is not None and context['source_commit']!=expected_commit:raise RuntimeError('Wrong artifact source commit')
    if run_id is not None and context['run_id']!=str(run_id):raise RuntimeError('Wrong artifact run id')
    if context['status']!='GITHUB_CI_AUDIT_COMPLETED_PENDING_ARTIFACT_DOWNLOAD_CHECK':raise RuntimeError('Artifact does not record completed CI run')
    workflow_binding=dict(path='.github/workflows/extraction-algorithm.yml',sha256=a.sha(a.REPO/'.github/workflows/extraction-algorithm.yml'),bound_template_sha256=a.sha(a.ROOT/'extraction-algorithm.workflow.yml'))
    if context['actual_workflow']!=workflow_binding or workflow_binding['sha256']!=workflow_binding['bound_template_sha256']:raise RuntimeError('Actual workflow is not the bound exact template')
    manifest=a.readj(base/'SOURCE_HASHES.json')
    if manifest!=a.readj(a.ROOT/'SOURCE_HASHES.json') or manifest!=a.inventory():raise RuntimeError('Artifact bound source differs from exact checkout')
    if a.sha(base/'SOURCE_HASHES.json')!=context['source_manifest_sha256']:raise RuntimeError('Manifest digest mismatch')
    if a.readj(base/'FROZEN_OLD_INPUTS.json')!=a.old_inventory():raise RuntimeError('Protected old input mismatch')
    for name in ['SCOPE.json','ROOTS.txt','DEFINITIONS.txt','CONTROLS.txt','CI_EXECUTION_POLICY.json']:
        if (base/name).read_bytes()!=(a.ROOT/name).read_bytes():raise RuntimeError('Downloaded scope/policy changed '+name)
    s,roots,defs,controls=a.scope_lists();a.validate_source_head(s,manifest)
    latest=a.readj(base/'LATEST.json')
    if latest!=context['latest'] or Path(latest['directory']).name!=latest['directory']:raise RuntimeError('Invalid latest pointer')
    out=base/latest['directory'];summary=a.readj(out/'SUMMARY.json')
    if a.sha(out/'SUMMARY.json')!=latest['summary_sha256']:raise RuntimeError('Summary hash mismatch')
    required=dict(status='PASS',mathematical_source_head=s['source_head'],endpoint_theorems=len(roots),model_definitions=len(defs),same_type_forged_proof_controls=len(controls),kernel_trust=0,fresh_owned_build=True,runtime_guard='GITHUB_HOSTED_LINUX_RUNNER_VERIFIED')
    if any(summary.get(k)!=v for k,v in required.items()):raise RuntimeError('Summary scope/trust/freshness does not match')
    if set(summary['axioms'])-a.ALLOW or summary['fresh_packages']!=a.NEW:raise RuntimeError('Wrong axioms/fresh-package scope')
    expected=a.readj(a.ROOT/'CI_EXECUTION_POLICY.json')['expected_scope']
    if (len(roots),len(defs),len(controls))!=(expected['endpoint_theorems'],expected['model_definitions'],expected['same_type_controls']):raise RuntimeError('Unexpected fixed CI scope')
    stages=a.readj(out/'STAGES.json')
    if stages!=summary['stages'] or any(x['exit_code']!=0 for x in stages):raise RuntimeError('Failed/mismatched stage evidence')
    expected_stages=['toolchain','build-numerical','build-effective','build-audit','root-types-axioms','finite-syntax-bytecode','trust0-replay']
    if [x['stage']for x in stages]!=expected_stages:raise RuntimeError('Missing or reordered full audit stages')
    if (out/'finite-syntax-bytecode.log').read_text().count('FINITE_SYNTAX_BYTECODE_CHECK_PASS')!=1:raise RuntimeError('Missing finite syntax executable check')
    for stage in stages:
        if Path(stage['log']).name!=stage['log'] or a.sha(out/stage['log'])!=stage['sha256']:raise RuntimeError('Stage log byte mismatch')
    kinds=(out/'root-types-axioms.log').read_text()
    if kinds.count('DECLARATION_KIND_CHECK_PASS')!=1:raise RuntimeError('Missing actual kind check')
    if a.parse_axiom_report(kinds,roots+defs)!=a.readj(out/'AXIOM_REPORT.json'):raise RuntimeError('Axiom report mismatch')
    replay=(out/'trust0-replay.log').read_text()
    if replay.count('EMPTY_KERNEL_REPLAY_PASS')!=1 or int(re.search(r'EMPTY_KERNEL_REPLAY_PASS (\d+) declarations',replay).group(1))!=summary['kernel_declarations']:raise RuntimeError('Missing complete trust-zero closure')
    for prefix in ['CORRUPTED_PROOF_REJECTED','CORRUPTED_PROOF_TYPE_MISMATCH_REJECTED']:
        if re.findall(r'^'+prefix+r' (\S+)$',replay,re.M)!=controls:raise RuntimeError('Missing/reordered exact-root same-type rejection '+prefix)
    if replay.count('TYPE_CLOSURE_REPLAY_PASS')!=len(controls):raise RuntimeError('Missing positive control type-closure replay')
    if set((out/'algorithm-kernel-axioms.txt').read_text().splitlines())-a.ALLOW:raise RuntimeError('Unexpected actual replay axiom')
    if (out/'algorithm-kernel-roots.txt').read_text().splitlines()!=roots+defs:raise RuntimeError('Wrong actual positive roots')
    closure=(out/'algorithm-kernel-closure.txt').read_text().splitlines()
    if len(closure)!=len(set(closure))or len(closure)!=summary['kernel_declarations']or not set(roots+defs)<=set(closure):raise RuntimeError('Wrong actual positive dependency closure')
    sizes=[int(n)for n in re.findall(r'TYPE_CLOSURE_REPLAY_PASS (\d+) declarations',replay)]
    for index,root in enumerate(controls,1):
        stem=out/('algorithm-control-'+str(index))
        if Path(str(stem)+'-roots.txt').read_text().splitlines()!=[root]:raise RuntimeError('Wrong forged theorem root')
        names=Path(str(stem)+'-type-dependencies.txt').read_text().splitlines()
        if len(names)!=len(set(names))or len(names)!=sizes[index-1]or 'True.intro'not in names or root in names:raise RuntimeError('Wrong exact control type prerequisites')
        if axiom_set(Path(str(stem)+'-axioms.txt'))-a.ALLOW:raise RuntimeError('Unexpected control axiom')
    invocation=out/'AuditInvocation.lean'
    if a.sha(invocation)!=summary['audit_invocation_sha256']:raise RuntimeError('Invocation changed')
    command=next(x['command'] for x in stages if x['stage']=='trust0-replay')
    original_output=Path(command[-1]).parent
    expected_invocation=(a.ROOT/'Audit.lean').read_text().replace('"verification/algorithm-',json.dumps(str(original_output/'algorithm-'))[:-1])
    if invocation.read_text()!=expected_invocation:raise RuntimeError('Invocation differs from the bound entire audit')
    pre=a.readj(base/'PRE_AUDIT.json');post=a.readj(base/'POST_AUDIT.json')
    if pre!=post or pre['source_inputs']!=manifest or pre['source_manifest_sha256']!=context['source_manifest_sha256']:raise RuntimeError('Source/execution pre-post check mismatch')
    policy=a.readj(a.ROOT/'CI_EXECUTION_POLICY.json')
    if {k:v['sha256'] for k,v in pre['binaries'].items()}!=policy['binary_sha256']:raise RuntimeError('Wrong checked toolchain binaries')
    return dict(status='DOWNLOADED_FULL_CI_ARTIFACT_VERIFIED',source_commit=context['source_commit'],run_id=context['run_id'],summary_sha256=latest['summary_sha256'],source_manifest_sha256=context['source_manifest_sha256'],roots=len(roots),definitions=len(defs),controls=len(controls),kernel_declarations=summary['kernel_declarations'])

if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('directory');ap.add_argument('--expected-commit',required=True);ap.add_argument('--run-id',required=True);args=ap.parse_args()
    print(json.dumps(verify(args.directory,args.expected_commit,args.run_id),indent=2))
