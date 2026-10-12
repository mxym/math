#!/usr/bin/env python3
"""Independent static evidence/semantic audit. No Lean or supplied verifier runs."""
from pathlib import Path
if not __debug__:
    raise SystemExit('Run without Python -O or PYTHONOPTIMIZE: assertions are required.')
import argparse
import collections, datetime, hashlib, json, math, re

HERE = Path(__file__).resolve().parent
B = HERE.parent / 'evidence'
ap = argparse.ArgumentParser(description=__doc__)
ap.add_argument('--output', type=Path, help='Write a new audit result outside this public snapshot')
args = ap.parse_args()
if args.output and (args.output.resolve() == HERE.parent or HERE.parent in args.output.resolve().parents):
    ap.error('--output must be outside the public snapshot')
F = B / 'fresh-verification'
P = B / 'formalization'
R = P / 'reference'
load = lambda p: json.loads(p.read_text())
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
def blob(p):
    b = p.read_bytes()
    return hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
out = {'audit_mode': 'STATIC_RECORD_AND_SEMANTIC_REVIEW_NO_LEAN_EXECUTED',
       'time_utc': datetime.datetime.now(datetime.timezone.utc).isoformat()}

mapping = load(HERE.parent/'PUBLICATION_MAPPING.json')
projection = {r['source_path']:r for r in mapping['source_files']}
assert len(projection) == len(mapping['source_files']) == 75
assert len({r['public_path'] for r in projection.values()}) == 75
assert {str(p.relative_to(HERE.parent)) for p in B.rglob('*') if p.is_file()} == {r['public_path'] for r in projection.values()}
for original, row in projection.items():
    assert not Path(original).is_absolute() and '..' not in Path(original).parts
    assert not Path(row['public_path']).is_absolute() and '..' not in Path(row['public_path']).parts
    p = HERE.parent/row['public_path']
    assert p.stat().st_size == row['public_bytes'] and sha(p) == row['public_sha256']
    if row['operation'].startswith('exact byte copy'):
        assert row['public_sha256'] == row['original_sha256']
        assert row['public_bytes'] == row['original_bytes']
    else:
        assert row['operation'] == 'machine-root path projection'
        assert row['projection_rules']
        assert all(x in mapping['projection_rules'] or any(x.items() <= rule.items() for rule in mapping['projection_rules']) for x in row['projection_rules'])
out['complete_75_file_projection_inventory_bound'] = True

def check_sums(base, rel, all_files=True):
    entries = {}
    projected = str(base.relative_to(B)) if base != B else ''
    historical = rel.endswith('.historical')
    for line in (base/rel).read_text().splitlines():
        h, p = line.split('  ', 1)
        assert p not in entries and not Path(p).is_absolute() and '..' not in Path(p).parts
        if historical:
            original = str(Path(projected)/p)
            row = projection[original]
            assert row['original_sha256'] == h, original
            assert sha(HERE.parent/row['public_path']) == row['public_sha256'], original
        else:
            assert sha(base/p) == h, p
        entries[p] = h
    if all_files:
        if historical:
            prefix = projected+'/' if projected else ''
            expected = {n[len(prefix):] for n in projection if n.startswith(prefix)}
            assert set(entries) == expected-{rel.removesuffix('.historical')}
        else:
            assert set(entries) == {str(p.relative_to(base)) for p in base.rglob('*') if p.is_file()}-{rel}
    return entries

archive = mapping['input_public_archive']
assert archive['bytes'] == 1417848
assert archive['sha256'] == '3abea26096508a6a12a87eea65785bb37e7656fd13d496d6900e2f2d7c699617'
assert archive['distributed'] is False
out['historical_input_public_archive'] = archive
out['archive_provenance_limit'] = 'Archive is not distributed; this portable checker binds all projected files to current hashes and original historical manifest hashes. It does not independently reconstruct undisclosed original machine-root strings.'
out['package_historical_hashed_files'] = len(check_sums(B, 'SHA256SUMS.historical'))
out['fresh_historical_hashed_files'] = len(check_sums(F, 'manifest/SHA256SUMS.historical'))
out['reference_hashed_files'] = len(check_sums(R, 'SHA256SUMS'))
out['reference_audit_hashed_files'] = len(check_sums(R/'audit', 'SHA256SUMS.txt'))

live = load(HERE/'live_reference_tree.json')
recorded = load(P/'records/source-tree.json')
assert live == recorded
prefix = 'notes/chromatic-infinite-logconcavity-counterexample/'
assert len(live) == 13
download = load(P/'records/download-manifest.json')
assert download['commit'] == '2b73cde3ae77ab1227c7386e9e82d0e815f21e88'
dl = {x['path']: x for x in download['files']}
for x in live:
    p = x['path'].removeprefix(prefix)
    assert (R/p).stat().st_size == x['size'] and blob(R/p) == x['sha'] == dl[p]['git_blob_sha1']
    assert sha(R/p) == dl[p]['sha256']
out['included_fixed_commit_reference_blobs_matched'] = len(live)
out['original_mathematical_proof_bytes_match_historical_audit'] = load(HERE/'static_audit_result.json')['original_mathematical_proof_bytes_match']
out['portable_reference_check'] = 'All 13 frozen Git blob hashes and sizes recomputed from included reference bytes; no live network request in this checker.'

case = load(P/'verify.json')
assert case == load(F/'manifest/input.json')
assert case['module_order'] == list(case['modules']) == case['audit_modules']
assert len(case['modules']) == 3
assert {p.name for p in (F/'sources').iterdir()} == {m+'.lean' for m in case['modules']}
for m, x in case['modules'].items():
    p = x['path']
    assert (P/'sources'/p).read_bytes() == (F/'sources'/p).read_bytes()
    assert sha(P/'sources'/p) == x['sha256']
result = load(P/'RESULT.json')
assert result['source_modules'] == case['modules']
out['identical_final_and_fresh_source_modules'] = 3
controls = load(F/'manifest/control-source-sha256.json')
for p, h in controls.items():
    assert sha(B/'verifier'/p) == h
template = (B/'verifier/checks/OwnedAudit.template.lean').read_text()
generated = template.replace('@@IMPORTS@@', '\n'.join('import '+m for m in case['audit_modules']))
generated = generated.replace('@@MODULES@@', '#[ '+', '.join(json.dumps(m) for m in case['audit_modules'])+' ]')
generated = generated.replace('@@ROOTS@@', '#[ '+', '.join('``'+r for r in case['roots'])+' ]')
assert generated == (F/'checks/OwnedAudit.lean').read_text()
assert (B/'verifier/checks/RejectInvalidProof.lean').read_bytes() == (F/'checks/RejectInvalidProof.lean').read_bytes()
assert (B/'verifier/config/environment.json').read_bytes() == (F/'manifest/environment-config.json').read_bytes()
out['checker_template_sources_and_control_hashes_bound'] = True

profile = load(B/'PUBLIC_PROFILE.historical.json')
newcfg = load(B/'verifier/config/environment.json')
assert not {'owner_thread','parent_thread'} & newcfg.keys()
assert len(profile['transformed_files']) == 2
assert {x['path'] for x in profile['transformed_files']} == {'verifier/config/environment.json','fresh-verification/manifest/environment-config.json'}
for x in profile['transformed_files']:
    assert projection[x['path']]['original_sha256'] == x['public_sha256'] == '20e4eec97992d75390a30cfbfce17f0749046233eaf60ef2eccec202d0f53a86'
    assert sha(B/x['path']) == projection[x['path']]['public_sha256']
    assert x['original_sha256'] == '29d7f383498d1d46f802fdd42bfe5ffc81405b726addc78e4f3868393e32164b'
assert load(HERE/'static_audit_result.json')['public_configuration_projection_verified']
out['public_configuration_projection_historical_audit'] = True
out['portable_projected_config_hashes_and_historical_profile_verified'] = True
out['raw_execution_archive_limit'] = 'Original execution archive is not included. Historical auditor checked both configuration projections; a full raw-versus-public archive comparison is not claimed. This publication additionally projects machine roots; the portable check binds all public files and historical hashes, while the final-copy gate checks projection against local originals.'

graph = load(F/'manifest/all-owned-closure.json')
nodes = {x['name']:x for x in graph}
assert len(nodes) == len(graph) == 10964
edges = {n:set(x['type_direct']+x['value_direct']+x['structural_dependencies']) for n,x in nodes.items()}
assert all(e <= nodes.keys() for e in edges.values())
def closure(roots):
    seen=set(); todo=list(roots)
    while todo:
        n=todo.pop()
        if n in seen: continue
        seen.add(n); todo.extend(edges[n]-seen)
    return seen
inventory = load(F/'manifest/owned-inventory.json')
owned = {x['declaration']['name']:x for x in inventory}
summary = load(F/'manifest/replay-summary.json')
assert len(owned) == len(inventory) == summary['owned_count'] == 98
assert set(owned) == {n for n,x in nodes.items() if x['module'] in case['audit_modules']}
assert closure(owned) == set(nodes)
for n,x in owned.items(): assert x['declaration'] == nodes[n]
explicit = load(P/'records/explicit-source-declarations.json')
source_decl = []
for m in case['modules']:
    text = (P/'sources'/(m+'.lean')).read_text()
    for kind, name in re.findall(r'^(?:noncomputable )?(abbrev|def|theorem)\s+([A-Za-z_][\w.]*)', text, flags=re.M):
        source_decl.append({'module':m,'kind':kind,'name':'ChromaticC17.'+name})
assert source_decl == explicit
assert len(explicit) == 41
assert {x['name'] for x in explicit} <= owned.keys()
assert len(set(owned)-{x['name'] for x in explicit}) == 57
assert summary['all_owned_closure_count'] == 10964
counts = {r:len(closure([r])) for r in case['roots']}
assert counts == {x['name']:x['closure_count'] for x in summary['roots']}
root_union = closure(case['roots'])
assert root_union == set(load(F/'manifest/requested-root-closure.json'))
assert len(root_union) == summary['requested_root_union_count'] == 10929
whitelist = {'propext','Classical.choice','Quot.sound'}
assert not any(x['unsafe'] or x['partial'] for x in graph)
assert {n for n,x in nodes.items() if x['kind']=='axiom'} == whitelist
assert not any(x['declaration']['kind']=='axiom' for x in inventory)
for n,x in owned.items():
    assert {a for a in closure([n]) if nodes[a]['kind']=='axiom'} == set(x['axioms']) <= whitelist
for r in case['roots']: assert r in owned and nodes[r]['kind']=='theorem'
assert load(F/'manifest/violations.json') == load(F/'manifest/source-token-scan.json') == []
assert result['replay'] == summary
out.update(owned_count=98, explicit_count=41, generated_auxiliary_count=57,
           owned_module_counts=dict(collections.Counter(x['declaration']['module'] for x in inventory)),
           all_owned_closure_count=10964, root_union_count=10929, per_root_counts=counts,
           edge_counts={k:sum(len(x[k]) for x in graph) for k in ['type_direct','value_direct','structural_dependencies']},
           closure_axioms=sorted(whitelist), unsafe_partial_owned_or_closure=0,
           all_98_per_declaration_axiom_reports_match_graph=True)

cmds = load(F/'manifest/commands.json')
assert len(cmds)==8 and all(x['exit_code']==0 for x in cmds)
status = load(F/'manifest/status.json'); run=status['run']
assert status['status']=='MECHANICAL_PASS' and status['stage']=='complete' and status['excluded_from_declaration_audit']==[]
assert status['semantic_review']=='REQUIRED_SEPARATELY'
search = load(F/'manifest/search-path.json')
assert search[0]==run+'/build'
env = load(F/'manifest/environment.json')
assert env['lean_commit']==newcfg['lean_commit']=='5045d0056413266e57c625dcd7c365b10e377c52'
assert {p['name']:p['commit'] for p in env['packages']} == {p['name']:p['rev'] for p in newcfg['packages']}
assert env['packages'][0]['commit']=='d13f23b723b8a846827a245b89c10fc7d3f11612'
for i,m in enumerate(case['module_order']):
    c,d = cmds[2*i:2*i+2]
    assert c['argv'][-1] == run+'/sources/'+m+'.lean'
    assert c['argv'][c['argv'].index('-o')+1] == run+'/build/'+m+'.olean'
    assert c['argv'][c['argv'].index('-i')+1] == run+'/build/'+m+'.ilean'
    assert d['argv'][1:] == ['--deps',run+'/sources/'+m+'.lean']
    for suffix in ['.olean','.ilean']:
        assert (F/'build'/(m+suffix)).stat().st_size>0
    for dep in (F/'logs'/d['log']).read_text().splitlines():
        if Path(dep).stem in case['modules']: assert dep==run+'/build/'+Path(dep).name
assert all(a['ended_utc']<=b['started_utc'] for a,b in zip(cmds,cmds[1:]))
assert cmds[0]['started_utc']>=status['started_utc'] and cmds[-1]['ended_utc']<=status['ended_utc']
assert 'ALL_OWNED_EMPTY_KERNEL_REPLAY_PASS 10964' in (F/'logs/owned-audit-replay.log').read_text()
negative=(F/'logs/negative-kernel.log').read_text()
assert 'INVALID_PROOF_REJECTED_BY_EMPTY_TRUST_ZERO_KERNEL' in negative and 'declaration type mismatch' in negative
assert 'True' in negative and 'False' in negative
assert summary['trust_level']==0 and summary['empty_base'] and summary['status']=='PASS'
cache=load(F/'manifest/shared-cache-check.json')
assert cache['unchanged'] and cache['before']==cache['after']
interfaces=load(P/'records/PrintInterfaces-command.json')
assert interfaces['exit_code']==0 and interfaces['search_path'].split(':')==search
out.update(recorded_successful_commands=8, recorded_fresh_run=run,
           cache_check_scope='Path/size/mtime metadata equality, not a content-authentication guarantee',
           recorded_negative_control='False proof using True.intro rejected for kernel type mismatch')

upstream = HERE/'upstream'
updata = load(upstream/'source_metadata.json')
for x in updata: assert blob(upstream/x['path'])==x['sha']
excerpts=load(P/'records/pinned-definition-excerpts.json')
for x in excerpts['files']: assert sha(upstream/x['path'])==x['full_file_sha256']
parts=[]
for x in excerpts['files']:
    lines=(upstream/x['path']).read_text().splitlines()
    parts.append(x['path']+f":{x['first_line']}-{x['last_line']}\n"+
                 'SHA256(full file)='+x['full_file_sha256']+'\n'+
                 '\n'.join(f'{i}: {lines[i-1]}' for i in range(x['first_line'],x['last_line']+1)))
assert '\n\n'.join(parts)+'\n' == (P/'records/pinned-definition-excerpts.txt').read_text()
for x in load(upstream/'kernel-source-metadata.json'):
    assert sha(upstream/x['path'])==x['sha256'] and blob(upstream/x['path'])==x['git_blob_sha']
out['independently_fetched_pinned_mathlib_sources'] = 4
out['reused_hash_verified_kernel_sources'] = ['Lean/Replay.lean','Lean/Util/FoldConsts.lean','Lean/Environment.lean']

# Independent exact reconstruction, avoiding supplied research/verifier programs.
n=17
edges17={(min(i,(i+1)%n),max(i,(i+1)%n)) for i in range(n)}
modular={(i,j) for i in range(n) for j in range(i+1,n) if (i-j)%n==1 or (j-i)%n==1}
assert len(edges17)==17 and edges17==modular and (0,16) in edges17
assert all(i!=j for i,j in edges17)
assert all(sum(v in e for e in edges17)==2 for v in range(n))
signed=[0]*18
edge_list=sorted(edges17)
for mask in range(1<<17):
    parent=list(range(17)); components=17
    def find(v):
        while parent[v]!=v:
            parent[v]=parent[parent[v]]; v=parent[v]
        return v
    for j,(u,v) in enumerate(edge_list):
        if mask>>j&1:
            a,b=find(u),find(v)
            if a!=b: parent[a]=b; components-=1
    signed[components] += -1 if mask.bit_count()%2 else 1
formula=[(-1)**(17-k)*math.comb(17,k)-(k==1)+(k==0) for k in range(18)]
assert signed==formula
rows=[[abs(x) for x in signed]]
for _ in range(3):
    a=rows[-1]
    rows.append([x*x-(a[k-1] if k else 0)*(a[k+1] if k+1<len(a) else 0) for k,x in enumerate(a)])
assert rows[-1][2]==-28272276537344
exact=load(P/'records/exact-correspondence.json')
assert signed==exact['signed_coefficients'] and rows==exact['iterations']
assert rows==load(R/'exact_certificates.json')['cycles']['17']['iterations'][:4]
# Count proper colorings by a fixed-start dynamic program for selected q, including empty colors.
counts_q={}
for q in [0,1,2,3,4,5,17]:
    if q==0: count=0
    else:
        dp=[1]+[0]*(q-1)
        for step in range(16): dp=[sum(dp)-v for v in dp]
        count=q*sum(dp[1:])
    assert count==(q-1)**17-(q-1)
    assert count==sum(c*q**k for k,c in enumerate(signed))
    counts_q[str(q)]=count
out['independent_exact_check']={'c17_edges':17,'edge_subsets_enumerated':1<<17,
    'all_18_signed_coefficients_match':True,'four_full_iteration_rows_match':True,
    'third_iterate_index2':rows[-1][2],'color_count_samples':counts_q,
    'all_q_proof_basis':'Reviewed Lean bijection, complete-graph matrix induction, and polynomial evaluation theorem; finite DP samples are supplementary only'}
out['status']='PASS_PORTABLE_STATIC_RECORD_AND_EXACT_RECHECK'
out['semantic_review'] = 'See preserved independent AUDIT_REPORT.md; this program does not automate semantic review or execute Lean.'
if args.output:
    with args.output.open('x') as f:
        f.write(json.dumps(out,indent=2,ensure_ascii=False)+'\n')
print(json.dumps(out,indent=2,ensure_ascii=False))
