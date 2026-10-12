#!/usr/bin/env python3
"""Portable public-copy evidence audit. Python standard library; does not run Lean.
Historical omitted binary hashes are checked as records, not as available bytes.
"""
from pathlib import Path
import base64, collections, gzip, hashlib, json, re, datetime
HERE=Path(__file__).resolve().parent
B=HERE.parent; F=B/'fresh-verification'; R=B/'reference'
mapping=json.loads((B/'PUBLICATION_MAPPING.json').read_text())
rows={r['source_path']:r for r in mapping['source_files']}
assert len(rows)==len(mapping['source_files'])==112

def raw(p):
    if p.is_file(): return p.read_bytes()
    rel=str(p.relative_to(B)); row=rows[rel]
    if row['operation']=='exact byte copy': return (B/row['public_path']).read_bytes()
    if row['operation']=='lossless gzip base64 parts':
        parts=row['parts']; assert len(parts)==len(set(parts)) and parts==sorted(parts)
        encoded=b''.join((B/n).read_bytes() for n in parts)
        assert len(encoded)==row['encoded_bytes'] and hashlib.sha256(encoded).hexdigest()==row['encoded_sha256']
        data=gzip.decompress(base64.b64decode(encoded,validate=True))
        assert len(data)==row['bytes'] and hashlib.sha256(data).hexdigest()==row['sha256']
        return data
    raise AssertionError('Original bytes deliberately not published: '+rel)
def load(p): return json.loads(raw(p))
def sha(p): return hashlib.sha256(raw(p)).hexdigest()
def blob(p):
    b=raw(p); return hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
out={'audit_mode':'PUBLIC_STATIC_EVIDENCE_CHECK_NO_LEAN_EXECUTED'}
manifest=load(B/'PACKAGE_SHA256.json')
assert set(manifest)==set(rows)-{'PACKAGE_SHA256.json'} and len(manifest)==111
for name,row in rows.items():
    if name in manifest: assert {k:row[k] for k in ['bytes','sha256']}==manifest[name],name
    if row['operation'] in ['exact byte copy','lossless gzip base64 parts']:
        data=raw(B/name); assert len(data)==row['bytes'] and hashlib.sha256(data).hexdigest()==row['sha256'],name
    elif row['operation']=='omitted compiled output':
        assert name.startswith('fresh-verification/build/') and Path(name).suffix in ['.olean','.ilean']
        assert not (B/name).exists()
    else: assert row['operation']=='configuration projection' and name in mapping['configuration_projection']['source_paths']
assert collections.Counter(r['operation'] for r in rows.values())=={'exact byte copy':86,'lossless gzip base64 parts':2,'omitted compiled output':22,'configuration projection':2}
projection=mapping['configuration_projection']; cfg=load(B/'PUBLIC_ENVIRONMENT_CONFIG.json')
assert not any(k in cfg for k in projection['removed_metadata_keys'])
assert projection['removed_metadata_keys']==['owner_thread','parent_thread']
assert projection['retained_fields_equal_to_original'] is True
assert hashlib.sha256(json.dumps(cfg,sort_keys=True,separators=(',',':')).encode()).hexdigest()==projection['retained_fields_canonical_json_sha256']
assert sha(B/'PUBLIC_ENVIRONMENT_CONFIG.json')==projection['public_file_sha256']
assert all(rows[n]['sha256']==projection['source_sha256'] for n in projection['source_paths'])
out.update(exact_original_files_verified=86,losslessly_decoded_original_files_verified=2,omitted_binary_hash_records_only=22,configuration_projections=2)
out['configuration_equivalence_scope']='Original-to-public equality was checked during packaging. This check verifies the recorded retained-field fingerprint; original administrative values are intentionally absent.'
manifest2=load(R/'PACKAGE_MANIFEST.json')['files']
assert set(manifest2)=={p.name for p in R.iterdir()}-{'PACKAGE_MANIFEST.json'}
for name,row in manifest2.items():assert len(raw(R/name))==row['bytes'] and sha(R/name)==row['sha256']
public_tree=load(HERE/'public-checkpoint-tree.json')
assert {(x['path'],x['sha'],x['size']) for x in public_tree}=={(x['path'],x['sha'],x['size']) for x in load(B/'records/checkpoint-tree.json')}
for x in public_tree:assert blob(R/x['name'])==x['sha'] and len(raw(R/x['name']))==x['size']
assert len(public_tree)==20
out['checkpoint_files_match_recorded_pinned_git_blobs']=20
case=load(B/'verify.json'); assert case==load(F/'manifest/input.json')
rec=load(R/'RECOVERY_MANIFEST.json')['files']
assert set(case['module_order'])==set(case['audit_modules'])==set(case['modules']) and len(case['module_order'])==11
assert {p.name for p in (F/'sources').glob('*.lean')}=={m+'.lean' for m in case['module_order']}
for module,x in case['modules'].items():
    name=x['path']; assert raw(R/name)==raw(F/'sources'/name)
    assert sha(R/name)==x['sha256']==rec[name]['original_pre_reset_sha256']==rec[name]['recovered_sha256']
out['byte_identical_author_lean_sources']=11
freshhash={}
for line in raw(F/'manifest/SHA256SUMS').decode().splitlines():
    h,p=line.split('  ',1); assert p not in freshhash
    assert rows['fresh-verification/'+p]['sha256']==h,p
    if rows['fresh-verification/'+p]['operation'] in ['exact byte copy','lossless gzip base64 parts']:assert sha(F/p)==h,p
    freshhash[p]=h
assert len(freshhash)==73
assert set(freshhash)=={p.removeprefix('fresh-verification/') for p in rows if p.startswith('fresh-verification/')}-{'manifest/SHA256SUMS'}
out['historical_fresh_manifest_entries_reconciled']=73
controls=load(F/'manifest/control-source-sha256.json')
for p,h in controls.items(): assert sha(B/'verifier'/p)==h,p
template=(B/'verifier/checks/OwnedAudit.template.lean').read_text()
generated=template.replace('@@IMPORTS@@','\n'.join('import '+m for m in case['audit_modules'])).replace('@@MODULES@@','#[ '+', '.join(json.dumps(m) for m in case['audit_modules'])+' ]').replace('@@ROOTS@@','#[ '+', '.join('``'+r for r in case['roots'])+' ]')
assert generated==(F/'checks/OwnedAudit.lean').read_text()
assert raw(B/'verifier/checks/RejectInvalidProof.lean')==raw(F/'checks/RejectInvalidProof.lean')
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
env=load(F/'manifest/environment.json'); cfg=load(B/'PUBLIC_ENVIRONMENT_CONFIG.json')
assert env['lean_commit']==cfg['lean_commit']=='5045d0056413266e57c625dcd7c365b10e377c52'
assert len(env['packages'])==9 and {p['name']:p['commit'] for p in env['packages']}=={p['name']:p['rev'] for p in cfg['packages']}
assert env['packages'][0]['commit']=='d13f23b723b8a846827a245b89c10fc7d3f11612'
for i,m in enumerate(case['module_order']):
    c,d=cmds[2*i:2*i+2]
    assert c['argv'][-1]==run+'/sources/'+m+'.lean' and c['argv'][c['argv'].index('-o')+1]==run+'/build/'+m+'.olean'
    assert d['argv'][1:] == ['--deps',run+'/sources/'+m+'.lean']
    for suffix in ['.olean','.ilean']: assert rows['fresh-verification/build/'+m+suffix]['operation']=='omitted compiled output'
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
out['public_configuration_projection']='PASS'
out['status']='PASS_PUBLIC_STATIC_EVIDENCE_AUDIT'
for name,row in load(HERE/'AUDIT_ARTIFACTS_SHA256.json').items():
    assert len(raw(HERE/name))==row['bytes'] and sha(HERE/name)==row['sha256'],name
out['independent_audit_artifact_hashes']='PASS'
print(json.dumps(out,indent=2,ensure_ascii=False))
