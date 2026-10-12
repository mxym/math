#!/usr/bin/env python3
"""Static evidence audit only. Does not execute Lean, the verifier, or package code."""
from pathlib import Path
import collections, hashlib, json, re, datetime
HERE=Path(__file__).resolve().parent
B=HERE/'cgf_conjecture48_independent_lean_evidence'
F=B/'fresh-verification'; R=B/'reference'
REC=Path('/workspace/shared/cyclotomic_lean_recovery_20261008')
PUB=Path('/workspace/shared/cgf_public_checkpoint_20261008')
def load(p): return json.loads(p.read_text())
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def blob(p):
    b=p.read_bytes(); return hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
out={'audit_mode':'STATIC_RECORD_AND_SEMANTIC_REVIEW_NO_LEAN_EXECUTED','time_utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
manifest=load(B/'PACKAGE_SHA256.json')
assert set(manifest)=={str(p.relative_to(B)) for p in B.rglob('*') if p.is_file()}-{'PACKAGE_SHA256.json'}
for p,m in manifest.items():
    assert (B/p).stat().st_size==m['bytes'] and sha(B/p)==m['sha256'], p
out['package_hashed_files']=len(manifest)
manifest2=load(R/'PACKAGE_MANIFEST.json')['files']
assert set(manifest2)=={p.name for p in R.iterdir()}-{'PACKAGE_MANIFEST.json'}
for p,m in manifest2.items():
    assert (R/p).stat().st_size==m['bytes'] and sha(R/p)==m['sha256'], p
out['checkpoint_package_hashed_files']=len(manifest2)
public_tree=load(HERE/'public-checkpoint-tree.json')
recorded_tree=load(B/'records/checkpoint-tree.json')
assert {(x['path'],x['sha'],x['size']) for x in public_tree}=={(x['path'],x['sha'],x['size']) for x in recorded_tree}
for x in public_tree:
    p=R/x['name']; assert blob(p)==x['sha'] and p.stat().st_size==x['size']
assert len(public_tree)==20
out['live_public_commit_git_blobs_matched']=len(public_tree)
out['public_checkpoint_local_all20_identical']=all((R/p.name).read_bytes()==p.read_bytes() for p in PUB.iterdir() if p.is_file())
case=load(B/'verify.json'); assert case==load(F/'manifest/input.json')
rec=load(REC/'RECOVERY_MANIFEST.json')['files']; publicrec=load(R/'RECOVERY_MANIFEST.json')['files']
assert set(case['module_order'])==set(case['audit_modules'])==set(case['modules']) and len(case['module_order'])==11
assert {p.name for p in (F/'sources').glob('*.lean')}=={m+'.lean' for m in case['module_order']}
for m,x in case['modules'].items():
    p=x['path']; h=sha(R/p)
    assert (R/p).read_bytes()==(F/'sources'/p).read_bytes()==(REC/p).read_bytes()==(PUB/p).read_bytes()
    assert h==x['sha256']==rec[p]['original_pre_reset_sha256']==rec[p]['recovered_sha256']==publicrec[p]['original_pre_reset_sha256']==publicrec[p]['recovered_sha256']
out['byte_identical_author_lean_sources']=11
freshhash={}
for line in (F/'manifest/SHA256SUMS').read_text().splitlines():
    h,p=line.split('  ',1); assert p not in freshhash and sha(F/p)==h,p; freshhash[p]=h
assert set(freshhash)=={str(p.relative_to(F)) for p in F.rglob('*') if p.is_file()}-{'manifest/SHA256SUMS'}
out['fresh_evidence_hashed_files']=len(freshhash)
controls=load(F/'manifest/control-source-sha256.json')
for p,h in controls.items(): assert sha(B/'verifier'/p)==h,p
template=(B/'verifier/checks/OwnedAudit.template.lean').read_text()
generated=template.replace('@@IMPORTS@@','\n'.join('import '+m for m in case['audit_modules'])).replace('@@MODULES@@','#[ '+', '.join(json.dumps(m) for m in case['audit_modules'])+' ]').replace('@@ROOTS@@','#[ '+', '.join('``'+r for r in case['roots'])+' ]')
assert generated==(F/'checks/OwnedAudit.lean').read_text()
assert (B/'verifier/checks/RejectInvalidProof.lean').read_bytes()==(F/'checks/RejectInvalidProof.lean').read_bytes()
assert load(B/'verifier/config/environment.json')==load(F/'manifest/environment-config.json')
out['control_sources_bound_and_generated_audit_matches']=True
graph=load(F/'manifest/all-owned-closure.json'); nodes={x['name']:x for x in graph}; assert len(nodes)==len(graph)==29737
edges={x['name']:set(x['type_direct']+x['value_direct']+x['structural_dependencies']) for x in graph}
assert all(e<=nodes.keys() for e in edges.values())
out['edge_counts']={k:sum(len(x[k]) for x in graph) for k in ['type_direct','value_direct','structural_dependencies']}
def closure(roots):
    seen=set(); todo=list(roots)
    while todo:
        n=todo.pop()
        if n in seen: continue
        seen.add(n); todo.extend(edges[n]-seen)
    return seen
summary=load(F/'manifest/replay-summary.json')
out['recomputed_root_counts']={r:len(closure([r])) for r in case['roots']}
assert out['recomputed_root_counts']=={x['name']:x['closure_count'] for x in summary['roots']}
root_union=closure(case['roots'])
assert root_union==set(load(F/'manifest/requested-root-closure.json')) and len(root_union)==29717==summary['requested_root_union_count']
inventory=load(F/'manifest/owned-inventory.json')
owned={x['declaration']['name']:x for x in inventory}; assert len(owned)==len(inventory)==112==summary['owned_count']
assert set(owned)=={n for n,x in nodes.items() if x['module'] in case['audit_modules']}
assert closure(owned)==set(nodes)
for n,x in owned.items(): assert x['declaration']==nodes[n]
out['owned_module_counts']=dict(collections.Counter(x['declaration']['module'] for x in inventory))
assert len(out['owned_module_counts'])==8
named=set((R/'theorem_names.txt').read_text().splitlines()); assert len(named)==73 and named<=owned.keys()
assert len(set(owned)-named)==39
out.update(owned_count=112,explicit_count=73,generated_private_count=39,all_owned_closure=29737,root_union=29717,all_edges_closed=True)
whitelist={'propext','Classical.choice','Quot.sound'}
assert not any(x['unsafe'] or x['partial'] for x in graph)
assert {x['name'] for x in graph if x['kind']=='axiom'}==whitelist
assert not any(x['declaration']['kind']=='axiom' for x in inventory)
for n,x in owned.items():
    assert set(x['axioms'])<=whitelist
    graph_axioms={a for a in closure([n]) if nodes[a]['kind']=='axiom'}
    assert graph_axioms==set(x['axioms']),(n,graph_axioms,x['axioms'])
for r in case['roots']: assert nodes[r]['kind']=='theorem' and r in named
assert load(F/'manifest/violations.json')==[] and load(F/'manifest/source-token-scan.json')==[]
out.update(closure_axioms=sorted(whitelist),owned_axioms=0,unsafe_or_partial_closure=0,all112_axiom_reports_match_graph=True)
authorlog=(F/'logs/010-Audit.compile.log').read_text()
reports=re.findall(r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)",authorlog)
assert len(reports)==73 and {n for n,a in reports}==named
for n,a in reports: assert set(re.split(r',\s*',a.strip()))-{''}==set(owned[n]['axioms'])
out['73_author_reports_exactly_once']=True
cmds=load(F/'manifest/commands.json'); assert len(cmds)==24 and all(x['exit_code']==0 for x in cmds)
status=load(F/'manifest/status.json'); run=status['run']; search=load(F/'manifest/search-path.json')
assert search[0]==run+'/build' and status['status']=='MECHANICAL_PASS' and status['excluded_from_declaration_audit']==[]
env=load(F/'manifest/environment.json'); cfg=load(F/'manifest/environment-config.json')
assert env['lean_commit']==cfg['lean_commit']=='5045d0056413266e57c625dcd7c365b10e377c52'
assert len(env['packages'])==9 and {p['name']:p['commit'] for p in env['packages']}=={p['name']:p['rev'] for p in cfg['packages']}
assert env['packages'][0]['commit']=='d13f23b723b8a846827a245b89c10fc7d3f11612'
for i,m in enumerate(case['module_order']):
    c,d=cmds[2*i:2*i+2]
    assert c['argv'][-1]==run+'/sources/'+m+'.lean' and c['argv'][c['argv'].index('-o')+1]==run+'/build/'+m+'.olean'
    assert d['argv'][1:] == ['--deps',run+'/sources/'+m+'.lean']
    for suffix in ['.olean','.ilean']: assert (F/'build'/(m+suffix)).is_file()
    deps=(F/'logs'/d['log']).read_text().splitlines()
    for dep in deps:
        if Path(dep).stem in case['modules']: assert dep==run+'/build/'+Path(dep).name,dep
    assert c['ended_utc']<=d['started_utc']
assert all(a['ended_utc']<=b['started_utc'] for a,b in zip(cmds,cmds[1:]))
assert 'ALL_OWNED_EMPTY_KERNEL_REPLAY_PASS 29737' in (F/'logs/owned-audit-replay.log').read_text()
assert 'INVALID_PROOF_REJECTED_BY_EMPTY_TRUST_ZERO_KERNEL' in (F/'logs/negative-kernel.log').read_text()
assert 'declaration type mismatch' in (F/'logs/negative-kernel.log').read_text()
cache=load(F/'manifest/shared-cache-check.json'); assert cache['unchanged'] and cache['before']==cache['after']
out['recorded_commands_all_successful']=len(cmds)
out['recorded_fresh_run']=run
out['fresh_build_isolation_static_review']='unique directory exist_ok=False; fresh build first; import --deps paths agree; no old owned outputs copied'
out['cache_check_scope']='file path, size, mtime metadata only; not independent cache content authentication'
cert=load(HERE/'frozen-certificate.json'); assert sha(HERE/'frozen-certificate.json')=='64b10e5427ecaaaf9076e5d8b592831393db9fcb2b412c5894fd928d5fd4dfad'
def lean_list(file,name):
    m=re.search(r'def '+name+r' : List ℤ :=\s*\[([^\]]+)\]',(R/file).read_text()); return [int(v.strip()) for v in m[1].split(',')]
coeff=lean_list('Expansion.lean','coefficients'); weights=lean_list('CenteredCertificate.lean','centeredWeights')
assert coeff==cert['coefficients_ascending'] and weights==cert['centered_q_integer_weights']
def mul(a,b):
    out=[0]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b): out[i+j]+=x*y
    return out
polys=[[1,0,1],[1,0,0,1,0,0,1],[1 if i%5==0 else 0 for i in range(21)],[1,1,0,-1,-1,-1,0,1,1]]
base=[1]
for p in polys: base=mul(base,p)
power=[1]
for _ in range(6): power=mul(power,base)
assert coeff==power and len(coeff)==217 and len(weights)==109 and coeff==coeff[::-1]
assert all(x>0 for x in coeff) and all(x>0 for x in weights)
assert weights==[coeff[0]]+[coeff[i]-coeff[i-1] for i in range(1,109)]
assert coeff[108]==11434392 and min(weights[1:])==5 and sum(coeff)==729000000
out['coefficient_arithmetic']={'all217_match_frozen_and_recomputed':True,'all109_weights_match_frozen_and_differences':True,'peak':coeff[108],'minimum_first_half_difference':min(weights[1:]),'sum':sum(coeff)}
metadata=load(HERE/'environment-source-metadata.json'); assert sha(HERE/'Environment.lean')==metadata['expected_sha256'] and blob(HERE/'Environment.lean')==metadata['git_blob_sha']
out['Environment_source_hash_verified']=metadata['expected_sha256']
result=load(B/'RESULT.json'); assert result['replay']==summary and result['source_bytes']==case['modules'] and result['semantics_review_sha256']==sha(B/'INDEPENDENT_REVIEW.txt')
out['raw_package_publication_issue']={'files':['fresh-verification/manifest/environment-config.json','verifier/config/environment.json'],'fields_to_remove_from_public_projection':['owner_thread','parent_thread'],'mathematical_gap':False}
out['status']='PASS_STATIC_SEMANTIC_AND_EVIDENCE_AUDIT'
(HERE/'static-audit-result.json').write_text(json.dumps(out,indent=2,ensure_ascii=False)+'\n')
print(json.dumps(out,indent=2,ensure_ascii=False))
