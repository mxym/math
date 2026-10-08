from pathlib import Path
import hashlib,json,itertools
from fractions import Fraction as F
B=Path('/workspace/shared/qpermanent_lean_semantic_audit_20261008/q_permanent_halfline_lean_evidence')
M=B/'fresh-verification/manifest'
report={}
hashof=lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
lines=(M/'SHA256SUMS').read_text().splitlines()
entries=[]
for line in lines:
    h,p=line.split('  ',1)
    assert not Path(p).is_absolute() and '..' not in Path(p).parts
    assert hashof(B/'fresh-verification'/p)==h,p
    entries.append(p)
assert len(entries)==len(set(entries))
allfiles={str(p.relative_to(B/'fresh-verification')) for p in (B/'fresh-verification').rglob('*') if p.is_file()}
assert allfiles==set(entries)|{'manifest/SHA256SUMS'},allfiles-set(entries)
report['evidence_manifest_hashes_verified']=len(entries)
case=json.loads((B/'project/verify.json').read_text())
assert case==json.loads((M/'input.json').read_text())
assert case['module_order']==list(case['modules'])==case['audit_modules']
for n,info in case['modules'].items():
    a=B/'project/sources'/info['path'];b=B/'fresh-verification/sources'/info['path']
    assert a.read_bytes()==b.read_bytes()
    assert hashof(a)==info['sha256']
for p,h in json.loads((M/'control-source-sha256.json').read_text()).items():
    assert hashof(B/'verifier'/p)==h,p
assert (B/'verifier/config/environment.json').read_bytes()==(M/'environment-config.json').read_bytes()
t=(B/'verifier/checks/OwnedAudit.template.lean').read_text()
t=t.replace('@@IMPORTS@@','\n'.join('import '+m for m in case['audit_modules']))
t=t.replace('@@MODULES@@','#[ '+', '.join(json.dumps(m) for m in case['audit_modules'])+' ]')
t=t.replace('@@ROOTS@@','#[ '+', '.join('``'+r for r in case['roots'])+' ]')
assert t==(B/'fresh-verification/checks/OwnedAudit.lean').read_text()
assert (B/'verifier/checks/RejectInvalidProof.lean').read_bytes()==(B/'fresh-verification/checks/RejectInvalidProof.lean').read_bytes()
report['source_config_and_control_consistency']='PASS'
graph=json.loads((M/'all-owned-closure.json').read_text()); G={x['name']:x for x in graph}
assert len(G)==len(graph)
inventory=json.loads((M/'owned-inventory.json').read_text()); owned={x['declaration']['name'] for x in inventory}
assert owned=={n for n,v in G.items() if v['module'] in case['audit_modules']}
assert len(owned)==len(inventory)==26
for x in inventory: assert G[x['declaration']['name']]==x['declaration']
deps=lambda x:set(x['type_direct'])|set(x['value_direct'])|set(x['structural_dependencies'])
missing={n:sorted(deps(x)-G.keys()) for n,x in G.items() if deps(x)-G.keys()}
assert not missing,missing
assert not [n for n,x in G.items() if x['unsafe'] or x['partial']]
axioms=sorted(n for n,x in G.items() if x['kind']=='axiom')
assert axioms==sorted(['propext','Classical.choice','Quot.sound'])
assert not [x for x in inventory if set(x['axioms'])-set(axioms)]
def closure(roots):
    seen=set();todo=list(roots)
    while todo:
        n=todo.pop()
        if n in seen: continue
        seen.add(n);todo.extend(deps(G[n])-seen)
    return seen
assert closure(owned)==G.keys()
roots=set(case['roots']); rc=closure(roots)
assert rc==set(json.loads((M/'requested-root-closure.json').read_text()))
s=json.loads((M/'replay-summary.json').read_text())
assert len(G)==s['all_owned_closure_count']==13134
assert len(rc)==s['requested_root_union_count']==13131
for r in s['roots']: assert len(closure([r['name']]))==r['closure_count']
report.update({'owned_count':len(owned),'all_owned_closure_count':len(G),'root_union_count':len(rc),'axioms':axioms,'closure_graph_consistency':'PASS','per_root_closure':s['roots']})
refs=json.loads((B/'project/reference/download-hash-check.json').read_text())
P=Path('/workspace/shared/publication_20261008/notes/q-permanent-halfline-counterexample')
for r in refs:
    assert hashof(B/'project/reference'/r['path'])==r['sha256']
    assert (B/'project/reference'/r['path']).read_bytes()==(P/r['path']).read_bytes()
report['public_reference_files_matching_local_publication']=len(refs)
A=[[F(1),F(-99,100),F(0),F(1,500)],[F(-99,100),F(1),F(0),F(1,8)],[F(0),F(0),F(1),F(0)],[F(1,500),F(1,8),F(0),F(1)]]
co=[F(0) for _ in range(7)];nonzero=[]
for p in itertools.permutations(range(4)):
    inv=sum(p[i]>p[j] for i in range(4) for j in range(i+1,4)); v=F(1)
    for i in range(4): v*=A[i][p[i]]
    co[inv]+=v
    if v:nonzero.append({'permutation_0_based':p,'inversions':inv,'term':str(v)})
val=lambda q:sum(c*F(q)**k for k,c in enumerate(co))
assert val(49)==F(81807513,500000) and val(50)==F(7969,50)
assert val(49)-val(50)==F(2117513,500000)>0
U=[[F(1),F(-99,100),F(0),F(1,500)],[F(0),F(1),F(0),F(6349,995)],[F(0),F(0),F(1),F(0)],[F(0),F(0),F(0),F(1)]]
D=[F(1),F(199,10000),F(1),F(944,4975)]
assert all(d>0 for d in D)
assert all(A[i][j]==sum(D[k]*U[k][i]*U[k][j] for k in range(4)) for i in range(4) for j in range(4))
assert all(A[i][i]==1 for i in range(4))
report['independent_fraction_checks']={'status':'PASS','all_permutations_enumerated':24,'nonzero_terms':nonzero,'coefficients':list(map(str,co)),'P49':str(val(49)),'P50':str(val(50)),'difference':str(val(49)-val(50)),'positive_quadratic_pivots':list(map(str,D))}
report['verification_limit']='Static semantic, hash, manifest graph and independent rational arithmetic audit only. No local Lean installation, compilation or kernel replay performed.'
out=Path('/workspace/shared/qpermanent_lean_semantic_audit_20261008/audit_artifacts_result.json')
out.write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))
