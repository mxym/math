#!/usr/bin/env python3
"""Strict verification of raw local added-scope evidence; no source mutation."""
from pathlib import Path
import argparse,json,re
import reproduce as a
from audit_runtime import configure

def verify(directory):
    configure(False);a.check_execution_inputs(False)
    s,roots,defs,controls=a.check_binding();out=Path(directory).resolve()
    if not out.is_relative_to((a.ROOT/'verification').resolve()):raise RuntimeError('Local evidence outside owned verified D output')
    summary=a.readj(out/'SUMMARY.json')
    required=dict(status='PASS',mathematical_source_head=s['source_head'],source_inputs=len(a.inventory()),endpoint_theorems=len(roots),model_definitions=len(defs),same_type_forged_proof_controls=len(controls),kernel_trust=0,fresh_owned_build=True,runtime_guard='D_BACKED_STORAGE_VERIFIED')
    if any(summary.get(k)!=v for k,v in required.items()):raise RuntimeError('Wrong local source/scope/trust/freshness')
    if summary['fresh_packages']!=a.NEW or set(summary['axioms'])-a.ALLOW:raise RuntimeError('Wrong local packages/axioms')
    if a.readj(out/'SOURCE_HASHES.json')!=a.inventory()or a.readj(out/'SCOPE.json')!=s:raise RuntimeError('Raw local source binding changed')
    if a.sha(out/'SOURCE_HASHES.json')!=summary['source_manifest_sha256']:raise RuntimeError('Local source manifest digest mismatch')
    stages=a.readj(out/'STAGES.json')
    if stages!=summary['stages']or [x['stage']for x in stages]!=['toolchain','build-numerical','build-effective','build-audit','root-types-axioms','finite-syntax-bytecode','trust0-replay']or any(x['exit_code']for x in stages):raise RuntimeError('Missing/failed local full stage')
    for stage in stages:
        if Path(stage['log']).name!=stage['log']or a.sha(out/stage['log'])!=stage['sha256']:raise RuntimeError('Raw local stage hash mismatch')
    types=(out/'root-types-axioms.log').read_text()
    if types.count('DECLARATION_KIND_CHECK_PASS')!=1 or a.parse_axiom_report(types,roots+defs)!=a.readj(out/'AXIOM_REPORT.json'):raise RuntimeError('Missing local kinds/types/axioms')
    if (out/'finite-syntax-bytecode.log').read_text().count('FINITE_SYNTAX_BYTECODE_CHECK_PASS')!=1:raise RuntimeError('Missing local bounded runtime check')
    replay=(out/'trust0-replay.log').read_text()
    if replay.count('EMPTY_KERNEL_REPLAY_PASS')!=1 or int(re.search(r'EMPTY_KERNEL_REPLAY_PASS (\d+) declarations',replay).group(1))!=summary['kernel_declarations']:raise RuntimeError('Missing actual whole trust0 replay')
    if (out/'algorithm-kernel-roots.txt').read_text().splitlines()!=roots+defs:raise RuntimeError('Wrong positive roots')
    closure=(out/'algorithm-kernel-closure.txt').read_text().splitlines()
    if len(closure)!=len(set(closure))or len(closure)!=summary['kernel_declarations']or not set(roots+defs)<=set(closure):raise RuntimeError('Wrong positive closure')
    if set((out/'algorithm-kernel-axioms.txt').read_text().splitlines())!=set(summary['axioms']):raise RuntimeError('Wrong actual positive axioms')
    for marker in ['CORRUPTED_PROOF_REJECTED','CORRUPTED_PROOF_TYPE_MISMATCH_REJECTED']:
        if re.findall(r'^'+marker+r' (\S+)$',replay,re.M)!=controls:raise RuntimeError('Missing/reordered exact control roots')
    sizes=[int(n)for n in re.findall(r'TYPE_CLOSURE_REPLAY_PASS (\d+) declarations',replay)]
    if len(sizes)!=len(controls):raise RuntimeError('Missing positive control type replay')
    for i,n in enumerate(controls,1):
        stem=out/('algorithm-control-'+str(i))
        if Path(str(stem)+'-roots.txt').read_text().splitlines()!=[n]:raise RuntimeError('Wrong forged root record')
        names=Path(str(stem)+'-type-dependencies.txt').read_text().splitlines()
        if len(names)!=len(set(names))or len(names)!=sizes[i-1]or 'True.intro'not in names or n in names:raise RuntimeError('Wrong exact control prerequisites')
        if set(Path(str(stem)+'-axioms.txt').read_text().splitlines())-a.ALLOW:raise RuntimeError('Unexpected control axiom')
    invocation=out/'AuditInvocation.lean'
    if a.sha(invocation)!=summary['audit_invocation_sha256']:raise RuntimeError('Invocation digest changed')
    command=stages[-1]['command'];original=Path(command[-1]).parent
    expected=(a.ROOT/'Audit.lean').read_text().replace('"verification/algorithm-',json.dumps(str(original/'algorithm-'))[:-1])
    if invocation.read_text()!=expected:raise RuntimeError('Invocation is not entire bound audit')
    execution=a.readj(out/'EXECUTION.json')
    if execution['guard']!='D_BACKED_STORAGE_VERIFIED'or execution['execution_inputs']!=a.readj(a.ROOT/'EXECUTION_INPUTS.json'):raise RuntimeError('Wrong actual local execution inputs')
    return dict(status='LOCAL_FULL_RAW_EVIDENCE_VERIFIED',source_head=s['source_head'],theorems=len(roots),models=len(defs),controls=len(controls),kernel_declarations=summary['kernel_declarations'],summary_sha256=a.sha(out/'SUMMARY.json'))

if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('directory');args=ap.parse_args();print(json.dumps(verify(args.directory),indent=2))
