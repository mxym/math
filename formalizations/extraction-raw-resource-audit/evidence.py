#!/usr/bin/env python3
"""Shared strict reader for local/hosted full raw-resource evidence."""
from pathlib import Path
import json,re
import reproduce as a


def axiom_set(path):
    raw=Path(path).read_bytes()
    if raw==b"\n":return set()
    try:text=raw.decode("utf-8")
    except UnicodeDecodeError as error:raise RuntimeError("Invalid axiom-list UTF-8")from error
    lines=text.splitlines()
    if "\r"in text or not text.endswith("\n")or not lines or len(lines)!=len(set(lines))or any(not name or any(c.isspace()for c in name)for name in lines):raise RuntimeError("Noncanonical axiom-list encoding")
    if raw!=("\n".join(lines)+"\n").encode("utf-8"):raise RuntimeError("Non-LF axiom-list separator")
    return set(lines)


def verify_run(directory,guard):
    out=Path(directory).resolve();scope,roots,definitions,controls=a.scope_lists()
    summary=a.readj(out/'SUMMARY.json')
    required=dict(status='PASS',mathematical_source_head=scope['source_head'],source_inputs=len(a.inventory()),endpoint_theorems=len(roots),model_definitions=len(definitions),same_type_forged_proof_controls=len(controls),kernel_trust=0,fresh_owned_build=True,runtime_guard=guard)
    if any(summary.get(key)!=value for key,value in required.items()):raise RuntimeError('Wrong actual scope/source/trust/freshness')
    if summary['fresh_packages']!=a.NEW or set(summary['axioms'])-a.ALLOW:raise RuntimeError('Wrong fresh packages or axiom set')
    if a.readj(out/'SOURCE_HASHES.json')!=a.inventory()or a.readj(out/'SCOPE.json')!=scope:raise RuntimeError('Raw evidence source/scope differs')
    if a.sha(out/'SOURCE_HASHES.json')!=summary['source_manifest_sha256']:raise RuntimeError('Source manifest digest differs')
    pre=a.readj(out/'PRE_AUDIT.json');post=a.readj(out/'POST_AUDIT.json')
    expected_policy=a.readj(a.ROOT/('CI_EXECUTION_POLICY.json'if guard=='GITHUB_HOSTED_LINUX_RUNNER_VERIFIED'else'EXECUTION_INPUTS.json'))
    if pre!=post or pre['source_head']!=scope['source_head']or pre['source_inputs']!=a.inventory()or pre['protected_inputs']!=a.old_inventory()or pre['execution_inputs']!=expected_policy:raise RuntimeError('Actual source/protected/execution pre-post drift')
    stages=a.readj(out/'STAGES.json')
    expected=['toolchain','build-audit','root-types-axioms','finite-syntax-bytecode','trust0-replay']
    if stages!=summary['stages']or [stage['stage']for stage in stages]!=expected or any(stage['exit_code']for stage in stages):raise RuntimeError('Missing/failed/reordered full audit stages')
    for stage in stages:
        if Path(stage['log']).name!=stage['log']or a.sha(out/stage['log'])!=stage['sha256']:raise RuntimeError('Stage log digest differs')
    kinds=(out/'root-types-axioms.log').read_text()
    if kinds.count('DECLARATION_KIND_CHECK_PASS')!=1 or a.parse_axiom_report(kinds,roots+definitions)!=a.readj(out/'AXIOM_REPORT.json'):raise RuntimeError('Missing actual kinds/types/axioms')
    if (out/'finite-syntax-bytecode.log').read_text().count('RAW_RESOURCE_SYNTAX_CHECK_PASS')!=1:raise RuntimeError('Missing bounded raw syntax execution')
    replay=(out/'trust0-replay.log').read_text()
    match=re.search(r'EMPTY_KERNEL_REPLAY_PASS (\d+) declarations',replay)
    if replay.count('EMPTY_KERNEL_REPLAY_PASS')!=1 or not match or int(match.group(1))!=summary['kernel_declarations']:raise RuntimeError('Missing whole trust0 closure')
    if (out/'raw-resource-kernel-roots.txt').read_text().splitlines()!=roots+definitions:raise RuntimeError('Wrong complete positive root list')
    closure=(out/'raw-resource-kernel-closure.txt').read_text().splitlines()
    if len(closure)!=len(set(closure))or len(closure)!=summary['kernel_declarations']or not set(roots+definitions)<=set(closure):raise RuntimeError('Wrong actual positive dependency closure')
    if axiom_set(out/'raw-resource-kernel-axioms.txt')!=set(summary['axioms']):raise RuntimeError('Wrong actual replay axiom set')
    for marker in ['CORRUPTED_PROOF_REJECTED','CORRUPTED_PROOF_TYPE_MISMATCH_REJECTED']:
        if re.findall(r'^'+marker+r' (\S+)$',replay,re.M)!=controls:raise RuntimeError('Missing/reordered exact-root same-type rejection')
    sizes=[int(size)for size in re.findall(r'TYPE_CLOSURE_REPLAY_PASS (\d+) declarations',replay)]
    if len(sizes)!=len(controls):raise RuntimeError('Missing positive exact control type replay')
    for index,name in enumerate(controls,1):
        stem=out/('raw-resource-control-'+str(index))
        if Path(str(stem)+'-roots.txt').read_text().splitlines()!=[name]:raise RuntimeError('Wrong forged theorem root')
        dependencies=Path(str(stem)+'-type-dependencies.txt').read_text().splitlines()
        if len(dependencies)!=len(set(dependencies))or len(dependencies)!=sizes[index-1]or 'True.intro'not in dependencies or name in dependencies:raise RuntimeError('Wrong exact control prerequisites')
        if axiom_set(Path(str(stem)+'-axioms.txt'))-a.ALLOW:raise RuntimeError('Unexpected control axiom')
    invocation=out/'AuditInvocation.lean'
    if a.sha(invocation)!=summary['audit_invocation_sha256']:raise RuntimeError('Invocation digest differs')
    command=stages[-1]['command'];original=Path(command[-1]).parent
    expected_invocation=(a.ROOT/'Audit.lean').read_text().replace('"verification/raw-resource-',json.dumps(str(original/'raw-resource-'))[:-1])
    if invocation.read_text()!=expected_invocation:raise RuntimeError('Invocation is not the entire bound audit')
    commands={stage['stage']:stage['command']for stage in stages}
    fixed={'toolchain':['lake','env','lean','--version'],'build-audit':['lake','build','RawResourceAudit','RawResourceVerification']}
    if any(commands[key]!=value for key,value in fixed.items()):raise RuntimeError('Wrong actual build/recipe command')
    for label,filename,maximum in [('root-types-axioms','Check.lean',10000),('finite-syntax-bytecode','ExecutableCheck.lean',7000),('trust0-replay','AuditInvocation.lean',11000)]:
        command=commands[label];expected_length=7 if label=='finite-syntax-bytecode'else 6
        if len(command)!=expected_length or command[:4]!=['lake','env','lean','-j1']or not re.fullmatch(r'-M[0-9]+',command[4]):raise RuntimeError('Wrong strict Lean command')
        if not 5000<=int(command[4][2:])<=maximum:raise RuntimeError('Unexpected Lean memory setting')
        if label=='finite-syntax-bytecode':
            if command[5:]!=['--run',filename]:raise RuntimeError('Wrong bounded runtime command')
        elif label=='trust0-replay':
            if not Path(command[-1]).is_absolute()or Path(command[-1]).name!=filename:raise RuntimeError('Wrong absolute audit invocation')
        elif command[-1]!=filename:raise RuntimeError('Wrong check file')
    execution=a.readj(out/'EXECUTION.json')
    if execution['guard']!=guard or execution['execution_inputs']!=pre['execution_inputs']:raise RuntimeError('Wrong actual execution inputs')
    actual_binaries=execution['portable_binary_inputs']if guard=='GITHUB_HOSTED_LINUX_RUNNER_VERIFIED'else execution['runtime']['actual_executables']
    if actual_binaries!=pre['binaries']:raise RuntimeError('Actual tool binary drift')
    return dict(status='FULL_RAW_RESOURCE_RUN_EVIDENCE_VERIFIED',source_head=scope['source_head'],theorems=len(roots),models=len(definitions),controls=len(controls),kernel_declarations=summary['kernel_declarations'],summary_sha256=a.sha(out/'SUMMARY.json'))
