#!/usr/bin/env python3
"""Verify a freshly downloaded evidence bundle against this exact checkout."""
from pathlib import Path
import argparse,json,re
import execution as e
a=e.a
axiom_set=e.axiom_set

def verify(directory,expected_commit,run_id,run_attempt):
    e.check()
    if not re.fullmatch(r"[a-f0-9]{40}",expected_commit) or a.run("git","rev-parse","HEAD")!=expected_commit:raise RuntimeError("Reader checkout is not the expected immutable event commit")
    e.check_commit(expected_commit)
    base=Path(directory).resolve();hashes=a.readj(base/'ARTIFACT_HASHES.json')
    actual={p.relative_to(base).as_posix() for p in base.rglob('*') if p.is_file() and p!=base/'ARTIFACT_HASHES.json'}
    if actual!=set(hashes):raise RuntimeError('Artifact has missing/extra files')
    for rel,digest in hashes.items():
        p=base/rel
        if not isinstance(rel,str) or Path(rel).is_absolute() or Path(rel).as_posix()!=rel or any(part in {'.','..'} for part in Path(rel).parts) or p.is_symlink() or any(parent.is_symlink() for parent in p.parents if parent!=base and parent.is_relative_to(base)) or not p.resolve().is_relative_to(base) or a.sha(p)!=digest:raise RuntimeError('Artifact byte hash mismatch '+rel)
    if any(path.is_symlink() for path in base.rglob('*')):raise RuntimeError('Artifact contains a symlink')
    context=a.readj(base/'CI_CONTEXT.json')
    if context.get('run_attempt')!=str(run_attempt) or context.get('repository')!='mxym/math' or context.get('workflow_commit')!=expected_commit:raise RuntimeError('Wrong v2 workflow/run identity')
    if not context.get('workflow_ref','').startswith('mxym/math/'+e.WORKFLOW+'@refs/'):raise RuntimeError('Wrong actual v2 workflow reference')
    if context.get('actual_mathematical_command')!=['reproduce.py','--github-actions','--fresh'] or context.get('actual_mathematical_cwd')!=e.BASE.relative_to(e.REPO).as_posix():raise RuntimeError('Wrong actual mathematical recipe command')
    if expected_commit is not None and context['source_commit']!=expected_commit:raise RuntimeError('Wrong artifact source commit')
    if run_id is not None and context['run_id']!=str(run_id):raise RuntimeError('Wrong artifact run id')
    if context['status']!='GITHUB_CI_AUDIT_COMPLETED_PENDING_ARTIFACT_DOWNLOAD_CHECK':raise RuntimeError('Artifact does not record completed CI run')
    workflow_binding=e.workflow_binding()
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
    if summary['source_inputs']!=340 or summary['source_manifest_sha256']!=e.MATH_MANIFEST_SHA256 or summary['manuscript_source_head']!=e.MATH_HEAD:raise RuntimeError('Wrong original mathematical/manuscript binding')
    if summary['manuscript_inputs']!=s['manuscript_inputs'] or summary['manuscript_documents']!=s['manuscript_documents']:raise RuntimeError('Wrong original manuscript input list')
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
    if axiom_set(out/'algorithm-kernel-axioms.txt')-a.ALLOW:raise RuntimeError('Unexpected actual replay axiom')
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
    commands={item['stage']:item['command']for item in stages}
    fixed_commands={'toolchain':['lake','env','lean','--version'],'build-numerical':['lake','build','@extractionNumericalSynthesis/CircuitNumerical'],'build-effective':['lake','build','@extractionEffectiveEncoding/EffectiveEncoding'],'build-audit':['lake','build','AlgorithmAudit','AlgorithmVerification'],'finite-syntax-bytecode':['lake','env','lean','-j1','-M4000','--run','ExecutableCheck.lean']}
    if any(commands[key]!=value for key,value in fixed_commands.items()):raise RuntimeError('Wrong fresh mathematical recipe stage command')
    for label,filename,maximum in [('root-types-axioms','Check.lean',10000),('trust0-replay',None,11000)]:
        cmd=commands[label]
        if len(cmd)!=6 or cmd[:4]!=['lake','env','lean','-j1'] or not re.fullmatch(r'-M[0-9]+',cmd[4]) or not 5000<=int(cmd[4][2:])<=maximum:raise RuntimeError('Wrong strict Lean invocation '+label)
        if filename is not None and cmd[-1]!=filename:raise RuntimeError('Wrong declaration check file')
    invocation=out/'AuditInvocation.lean'
    if a.sha(invocation)!=summary['audit_invocation_sha256']:raise RuntimeError('Invocation changed')
    command=next(x['command'] for x in stages if x['stage']=='trust0-replay')
    original_output=Path(command[-1]).parent
    expected_output=Path('/home/runner/work/_temp')/('extraction-algorithm-'+str(run_id)+'-'+str(run_attempt))/'evidence'/latest['directory']
    if original_output!=expected_output or Path(command[-1]).name!='AuditInvocation.lean':raise RuntimeError('Replay output is not the exclusive actual hosted-runner location')
    expected_invocation=(a.ROOT/'Audit.lean').read_text().replace('"verification/algorithm-',json.dumps(str(original_output/'algorithm-'))[:-1])
    if invocation.read_text()!=expected_invocation:raise RuntimeError('Invocation differs from the bound entire audit')
    pre=a.readj(base/'PRE_AUDIT.json');post=a.readj(base/'POST_AUDIT.json')
    if pre!=post or pre['source_inputs']!=manifest or pre['source_manifest_sha256']!=context['source_manifest_sha256']:raise RuntimeError('Source/execution pre-post check mismatch')
    e.verify_execution_evidence(base,context,pre,post)
    if a.readj(base/'BOOTSTRAP_BINARIES.json')!=pre['binaries']:raise RuntimeError('Bootstrap/audit binary drift')
    bootstrap=a.readj(base/'BOOTSTRAP.json')
    if bootstrap['execution']!=context['execution']:raise RuntimeError('Bootstrap execution binding drift')
    identity={k:context[k]for k in ['source_commit','run_id','run_attempt','repository','workflow_ref','workflow_commit']}
    if bootstrap['github']!=identity:raise RuntimeError('Bootstrap workflow/run identity drift')
    policy=a.readj(a.ROOT/'CI_EXECUTION_POLICY.json')
    if bootstrap['installer_url']!=policy['elan_init_url']:raise RuntimeError('Wrong pinned bootstrap installer')
    if {k:v['sha256'] for k,v in pre['binaries'].items()}!=policy['binary_sha256']:raise RuntimeError('Wrong checked toolchain binaries')
    return dict(status='DOWNLOADED_FULL_V2_CI_ARTIFACT_VERIFIED',execution_revision=e.REVISION,execution_manifest_sha256=a.sha(e.MANIFEST),actual_workflow=workflow_binding,run_attempt=str(run_attempt),source_commit=context['source_commit'],run_id=context['run_id'],summary_sha256=latest['summary_sha256'],source_manifest_sha256=context['source_manifest_sha256'],roots=len(roots),definitions=len(defs),controls=len(controls),kernel_declarations=summary['kernel_declarations'])

if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('directory');ap.add_argument('--expected-commit',required=True);ap.add_argument('--run-id',required=True);ap.add_argument('--run-attempt',required=True);args=ap.parse_args()
    print(json.dumps(verify(args.directory,args.expected_commit,args.run_id,args.run_attempt),indent=2))
