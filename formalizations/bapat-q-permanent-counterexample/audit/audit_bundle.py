#!/usr/bin/env python3
"""Read-only static provenance, closure and integer audit; does NOT execute Lean.
Use: python audit_bundle.py COMPACT_ROOT PUBLIC_ROOT --output RESULTS.json
No third-party packages. Checks are explicit and remain active under python -O.
"""
import argparse,collections,csv,gzip,hashlib,json,math,re
from pathlib import Path

def check(p,msg):
 if not p: raise ValueError(msg)
def sha(b):return hashlib.sha256(b).hexdigest()
def blob(b):return hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
def load(p):return json.loads(gzip.decompress(p.read_bytes()) if p.suffix=='.gz' else p.read_bytes())
def manifest(root,path):
 entries=[]
 for line in path.read_text().splitlines():
  h,s=line.split('  ',1); p=(root/s).resolve();check(p.is_relative_to(root.resolve()),'unsafe manifest path');check(p.is_file(),'missing '+s);check(sha(p.read_bytes())==h,'hash '+s);entries.append(s)
 check(len(entries)==len(set(entries)),'duplicate hash path');return set(entries)
def graph_closure(graph,roots):
 out=set();todo=list(roots)
 while todo:
  n=todo.pop()
  if n in out:continue
  check(n in graph,'missing graph dependency '+n);out.add(n)
  row=graph[n];todo.extend(row['type_direct']+row['value_direct']+row['structural_dependencies'])
 return out

def provenance(c,p):
 cm=manifest(c,c/'SHA256SUMS');pm=manifest(p,p/'SHA256SUMS')
 check(cm=={str(f.relative_to(c)) for f in c.rglob('*') if f.is_file() and f.name!='SHA256SUMS'},'compact coverage')
 check(pm=={str(f.relative_to(p)) for f in p.rglob('*') if f.is_file() and f!=p/'SHA256SUMS'},'public coverage')
 rm=manifest(p/'fresh-verification',p/'fresh-verification/manifest/SHA256SUMS')
 actual={str(f.relative_to(p/'fresh-verification')) for f in (p/'fresh-verification').rglob('*') if f.is_file() and f.name!='SHA256SUMS'}
 check(rm==actual,'run checksum coverage')
 mapping=load(c/'provenance/file-map.json');rules=load(c/'provenance/path-substitutions.json')['rules'];literals={}
 check({e['original_path'] for e in mapping}==pm|{'SHA256SUMS'},'map does not cover original')
 # Recover only the authorized mechanically redacted literal tokens from original input.
 # Public output deliberately records their hashes, never the original machine paths.
 texts=[]
 for e in mapping:
  if e['action']=='metadata-substitution':texts.append((p/e['original_path']).read_text())
 candidates=set()
 for t in texts:
  for token in re.findall(r'[^\s"\'<>(),\[\]{}]+',t):
   candidates.add(token)
   for j,ch in enumerate(token):
    if ch=='/': candidates.add(token[:j])
 for rule in rules:
  found=[s for s in candidates if sha(s.encode())==rule['original_literal_sha256']]
  check(len(found)==1,'redaction literal not uniquely recovered '+str(rule['rule']));literals[rule['rule']]=found[0]
 for e in mapping:
  data=(p/e['original_path']).read_bytes();check(len(data)==e['original_bytes'] and sha(data)==e['original_sha256'],'original mapping hash '+e['original_path'])
  if e['action']=='omitted':
   check(e['original_path'].startswith('fresh-verification/build/') and Path(e['original_path']).suffix in ['.olean','.ilean'],'unexpected omission');continue
  target=(c/e['target']).read_bytes();check(sha(target)==e['target_sha256'],'target mapping hash')
  if 'target_bytes' in e:check(len(target)==e['target_bytes'],'target size')
  if e.get('decompressed_sha256'):
   target=gzip.decompress(target);check(sha(target)==e['decompressed_sha256'],'gzip mapping hash')
  if e['action']=='metadata-substitution':
   text=data.decode();applied=[]
   for r in rules:
    n=text.count(literals[r['rule']])
    if n: applied.append({'rule':r['rule'],'occurrences':n});text=text.replace(literals[r['rule']],r['replacement'])
   text,count=re.subn(r'^\s*"pid": [^\n]*\n','',text,flags=re.M)
   if count:applied.append({'rule':'remove-process-id-line','occurrences':count})
   check(applied==e['rules_applied'],'substitution occurrence count '+e['original_path']);check(target==text.encode(),'nonmechanical metadata change '+e['original_path'])
  else:check(target==data,'retained/deduplicated bytes differ '+e['original_path'])
 return {'compact_hashed_files':len(cm),'public_hashed_files':len(pm),'public_all_files':len(mapping),'fresh_run_hashed_files':len(rm),'mapping_actions':dict(collections.Counter(e['action'] for e in mapping)),'metadata_transformations_exact':True,'original_literal_sha256_verified':len(literals),'original_uncompressed_bytes':sum(e['original_bytes'] for e in mapping),'omitted_bytes':sum(e['original_bytes'] for e in mapping if e['action']=='omitted')}

def dependencies(c):
 m=c/'fresh-verification/manifest';allrows=load(m/'all-owned-closure.json.gz');graph={r['name']:r for r in allrows};inv=load(m/'owned-inventory.json.gz');summary=load(m/'replay-summary.json');case=load(m/'input.json')
 check(len(graph)==len(allrows),'duplicate graph names');owned={r['declaration']['name'] for r in inv};check(len(owned)==len(inv),'duplicate owned names');mods=set(case['modules']);check(mods==set(case['audit_modules'])==set(case['module_order']),'module list discrepancy');check(len(mods)==22,'wrong source count')
 check(owned=={n for n,r in graph.items() if r['module'] in mods},'owned graph/inventory mismatch')
 allowed={'propext','Classical.choice','Quot.sound'}
 for n,r in graph.items():
  check(not r['unsafe'] and not r['partial'],'unsafe/partial '+n)
  if r['kind']=='axiom':check(n in allowed,'unexpected axiom '+n)
 check({n for n,r in graph.items() if r['kind']=='axiom'}==allowed,'axiom set')
 for e in inv:
  n=e['declaration']['name'];check(e['declaration']==graph[n],'inventory/graph node mismatch '+n);check(graph[n]['kind']!='axiom','owned axiom')
  cl=graph_closure(graph,[n]);axs={x for x in cl if graph[x]['kind']=='axiom'};check(axs==set(e['axioms']),'computed axiom mismatch '+n)
 check(graph_closure(graph,owned)==set(graph),'all-owned closure mismatch')
 roots=case['roots'];union=graph_closure(graph,roots);check(union==set(load(m/'requested-root-closure.json.gz')),'root union mismatch')
 root_stats=[]
 for r in summary['roots']:
  check(r['name'] in owned and graph[r['name']]['kind']=='theorem','root not own theorem');check(len(graph_closure(graph,[r['name']]))==r['closure_count'],'root count');root_stats.append(r)
 check(set(roots)=={r['name'] for r in root_stats},'roots disagree')
 check((summary['owned_count'],summary['all_owned_closure_count'],summary['requested_root_union_count'])==(len(owned),len(graph),len(union)),'summary counts')
 check(summary['trust_level']==0 and summary['empty_base'] and summary['status']=='PASS','reported replay not trust zero PASS')
 check(load(m/'violations.json')==[] and load(m/'source-token-scan.json')==[],'reported violations')
 for mod,info in case['modules'].items():
  check(sha((c/'formalization/sources'/info['path']).read_bytes())==info['sha256'],'source hash')
 check({f.name for f in (c/'formalization/sources').glob('*.lean')}=={r['path'] for r in case['modules'].values()},'unlisted own source')
 for r in load(c/'MODULES.json'):check(case['modules'][r['module']]['sha256']==r['sha256'],'MODULES metadata')
 check(load(c/'formalization/verify.json')['modules']==case['modules'],'input/formalization source config')
 return {'owned_declarations':len(owned),'all_owned_closure':len(graph),'requested_root_union':len(union),'axioms':sorted(allowed),'all_928_transitive_axiom_sets_recomputed':True,'all_nodes_safe_nonpartial':True,'owned_kind_counts':dict(collections.Counter(graph[n]['kind'] for n in owned)),'graph_kind_counts':dict(collections.Counter(r['kind'] for r in graph.values())),'roots':root_stats}

def logs(c,p):
 m=c/'fresh-verification/manifest';case=load(m/'input.json');cmd=load(m/'commands.json');status=load(m/'status.json');check(len(cmd)==46,'commands count');expected=[]
 for i,mod in enumerate(case['module_order']): expected += [f'{i:03d}-{mod}.compile.log',f'{i:03d}-{mod}.dependencies.log']
 expected+=['owned-audit-replay.log','negative-kernel.log'];check([r['log'] for r in cmd]==expected,'command ordering');previous=None
 for r in cmd:
  check(r['exit_code']==0,'command failed');check((c/'fresh-verification/logs'/r['log']).is_file(),'log missing');check(r['started_utc']<=r['ended_utc'],'command chronology')
  if previous:check(previous<=r['started_utc'],'overlapping serial commands')
  previous=r['ended_utc']
 check(status['status']=='MECHANICAL_PASS' and status['stage']=='complete' and status['excluded_from_declaration_audit']==[],'status mismatch')
 check('REPLAY_BEGIN all_owned=928 closure=22371; empty kernel trust=0\nALL_OWNED_EMPTY_KERNEL_REPLAY_PASS 22371\n'==(c/'fresh-verification/logs/owned-audit-replay.log').read_text(),'replay log')
 neg=(c/'fresh-verification/logs/negative-kernel.log').read_text();check('INVALID_PROOF_REJECTED_BY_EMPTY_TRUST_ZERO_KERNEL' in neg and 'True' in neg and 'False' in neg and '(kernel) declaration type mismatch' in neg,'negative control log')
 for rel,h in load(m/'control-source-sha256.json').items():check(sha((c/'verifier'/rel).read_bytes())==h,'control source mismatch '+rel)
 template=(c/'verifier/checks/OwnedAudit.template.lean').read_text();audit=template.replace('@@IMPORTS@@','\n'.join('import '+s for s in case['audit_modules'])).replace('@@MODULES@@','#[ '+', '.join(json.dumps(s) for s in case['audit_modules'])+' ]').replace('@@ROOTS@@','#[ '+', '.join('``'+s for s in case['roots'])+' ]')
 check(audit==(c/'fresh-verification/checks/OwnedAudit.lean').read_text(),'audit template mismatch');check((c/'verifier/checks/RejectInvalidProof.lean').read_bytes()==(c/'fresh-verification/checks/RejectInvalidProof.lean').read_bytes(),'negative source mismatch')
 shared=load(m/'shared-cache-check.json');check(shared['before']==shared['after'] and shared['unchanged'],'reported cache changed')
 paths=load(m/'search-path.json');check(paths[0]=='${RUN_ROOT}/build','search path does not prioritize fresh build')
 order={s:i for i,s in enumerate(case['module_order'])};own_deps={}
 for i,mod in enumerate(case['module_order']):
  deps=(c/'fresh-verification/logs'/f'{i:03d}-{mod}.dependencies.log').read_text().splitlines();check(len(deps)>0,'empty dependency log');direct=re.findall(r'^import\s+(\S+)',(c/'formalization/sources'/case['modules'][mod]['path']).read_text(),re.M);own_deps[mod]=[]
  for x in direct:
   if x in order:
    check(order[x]<i,'own import ordering');check('${RUN_ROOT}/build/'+x+'.olean' in deps,'own dependency not fresh '+x);own_deps[mod].append(x)
 return {'commands_verified':len(cmd),'compile_commands':22,'dependency_commands':22,'audit_control_hashes_match':True,'generated_audit_source_matches_template':True,'reported_fresh_run_start_utc':status['started_utc'],'reported_fresh_run_end_utc':status['ended_utc'],'negative_control_reported_pass':True,'shared_cache_metadata_reported_unchanged':True,'own_import_dependency_paths_fresh':True,'own_imports':own_deps,'limitation':'Historical command/log consistency audited; no Lean executable invoked in this audit. Cache check fingerprints paths, sizes and mtimes, not file contents.'}

ZERO=(0,0)
def add(z,w):return(z[0]+w[0],z[1]+w[1])
def mul(z,w):return(z[0]*w[0]-z[1]*w[1],z[0]*w[1]+z[1]*w[0])
def scale(k,z):return(k*z[0],k*z[1])
def coeff(p,k):return p[k] if 0<=k<len(p) else ZERO
def lin(p,a,b):return [add(mul(a,coeff(p,k)),mul(b,coeff(p,k-1))) for k in range(len(p)+1)]
def integers(c):
 ref=c/'formalization/reference';data=(ref/'counterexample_vectors_n200.csv').read_bytes();check(sha(data)=='9d16617d6eb287535a752cf5ef6f3d4672a133812bf0fbd908738a10c223fc25','CSV hash');rows=list(csv.DictReader(data.decode().splitlines()));vectors=[((int(r['a_real']),int(r['a_imag'])),(int(r['b_real']),int(r['b_imag']))) for r in rows];check(len(vectors)==200,'CSV rows')
 source=(c/'formalization/sources/BapatN200Data.lean').read_text();raw=re.search(r'def vectors.*?:=.*?\[(.*?)\]\s*\n',source,re.S).group(1);pairs=[tuple(map(int,z)) for z in re.findall(r'⟨\s*(-?\d+)\s*,\s*(-?\d+)\s*⟩',raw)];check(len(pairs)==400 and vectors==list(zip(pairs[::2],pairs[1::2])),'ordered Lean vectors/CSV mismatch')
 checkpoints={};proofs=[]
 for i in range(4):
  text=(c/f'formalization/sources/BapatN200Trace{i}.lean').read_text()
  for number,f,s in re.findall(r'def checkpoint_(\d+) : Coeffs × Coeffs :=\s*\(\[(.*?)\],\s*\[(.*?)\]\)',text,re.S):
   number=int(number);check(number not in checkpoints,'duplicate checkpoint');checkpoints[number]=[[tuple(map(int,z)) for z in re.findall(r'⟨\s*(-?\d+)\s*,\s*(-?\d+)\s*⟩',w)] for w in [f,s]]
  proofs+=re.findall(r'theorem state_eq_(\d+) : state \(vectorAt vectors\) (\d+) = checkpoint_(\d+) := by\s*rw \[state, state_eq_(\d+)\]\s*decide \+kernel',text)
 check(set(checkpoints)==set(range(201)),'checkpoint coverage');check({tuple(map(int,x)) for x in proofs}=={(j,j,j,j-1) for j in range(1,201)},'state proof chain')
 f=[(1,0)];s=[];check(checkpoints[0]==[f,s],'initial state')
 digests=[]
 for m,(a,b) in enumerate(vectors):
  # Independent coefficient formula for the ordered homogeneous wedge sum.
  newf=lin(f,a,b);news=[]
  for k in range(m+1):
   news.append(add(add(mul(a,coeff(s,k)),mul(b,coeff(s,k-1))),add(scale(m-k,mul(b,coeff(f,k))),scale(-(k+1),mul(a,coeff(f,k+1))))))
  f,s=newf,news;check(checkpoints[m+1]==[f,s],'integer checkpoint mismatch '+str(m+1));digests.append({'step':m+1,'F_length':len(f),'S_length':len(s),'canonical_json_sha256':sha(json.dumps([f,s],separators=(',',':')).encode())})
 def norm(d,cs):return sum(math.factorial(d-k)*math.factorial(k)*(z[0]**2+z[1]**2) for k,z in enumerate(cs[:d+1]))
 P=norm(200,f);H=norm(198,s);D=H-19900*P;expected=load(ref/'expected_values.json');cert=load(ref/'independent_certificate.json');check([P,H,19900*P,D]==[int(expected[k]) for k in ['permanent','S_norm_squared','N_permanent','negative_twice_derivative']],'expected norms');check([P,H,D]==[int(cert[k]) for k in ['P','Q','D']],'pair deletion norm certificate');check([list(z) for z in f]==cert['F_coefficients'],'public F coefficients');check([list(z) for z in s[:199]]==cert['S_coefficients'] and s[199]==ZERO,'public S coefficients/padding');check(P>0 and D>0 and 23*19900*P<1000*D<24*19900*P,'strict rational gap')
 # Direct small-n permutation derivative identity, independent of proof's coefficient bridge.
 from itertools import permutations
 tests=[]
 for n in range(2,8):
  vs=vectors[:n];ff=[(1,0)];ss=[]
  for m,(a,b) in enumerate(vs):
   news=[add(add(mul(a,coeff(ss,k)),mul(b,coeff(ss,k-1))),add(scale(m-k,mul(b,coeff(ff,k))),scale(-(k+1),mul(a,coeff(ff,k+1))))) for k in range(m+1)];ff=lin(ff,a,b);ss=news
  A=[[add(mul(a,(c0,-c1)),mul(b,(d0,-d1))) for (c0,c1),(d0,d1) in vs] for a,b in vs];dp=ZERO;per=ZERO
  for perm in permutations(range(n)):
   term=(1,0)
   for i,j in enumerate(perm):term=mul(term,A[i][j])
   iv=sum(perm[i]>perm[j] for i in range(n) for j in range(i+1,n));per=add(per,term);dp=add(dp,scale(iv,term))
  check(per==(norm(n,ff),0),'small direct permanent');check(scale(2,dp)==(n*(n-1)//2*norm(n,ff)-norm(n-2,ss),0),'small direct derivative');tests.append({'n':n,'permutations':math.factorial(n),'pass':True})
 result={'ordered_vector_rows':200,'csv_sha256':sha(data),'exact_checkpoints_verified':201,'successor_proof_links_verified':200,'F_coefficients':len(f),'S_coefficients_with_padding':len(s),'S_last_entry':[0,0],'permanent':str(P),'wedge_norm':str(H),'positive_gap':str(D),'gap_decimal_digits':len(str(D)),'strict_gap_ratio_bounds':['23/1000','24/1000'],'all_checkpoint_hashes':digests,'small_direct_permutation_tests':tests}
 return result

def paper(c):
 r=c/'formalization/reference';tree=load(r/'repository-tree.json.gz');check(tree['sha']=='c5d7f68e78b6c80912041c6cf1fd4d3cd950beb6','paper commit');entries={e['path']:e for e in tree['tree']};dl=load(r/'download-manifest.json')
 for e in dl:
  b=(r/Path(e['path']).name).read_bytes();check(len(b)==e['bytes'] and sha(b)==e['sha256'] and blob(b)==e['git_blob'],'paper input hash');check(entries[e['path']]['sha']==e['git_blob'],'paper tree blob mismatch')
 return {'paper_commit':tree['sha'],'reference_downloads_verified':len(dl),'csv_git_blob_sha1':blob((r/'counterexample_vectors_n200.csv').read_bytes()),'proof_git_blob_sha1':blob((r/'proof.md').read_bytes())}

def main():
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('compact',type=Path);ap.add_argument('public',type=Path);ap.add_argument('--output',type=Path,required=True);args=ap.parse_args();c=args.compact;p=args.public
 results={'scope':'Independent static evidence and exact integer audit; no fresh Lean execution.'}
 for name,fn in [('provenance',lambda:provenance(c,p)),('dependencies',lambda:dependencies(c)),('historical_run',lambda:logs(c,p)),('integer_certificate',lambda:integers(c)),('paper_provenance',lambda:paper(c))]:
  results[name]=fn();print(name+': PASS',flush=True)
 results['status']='PASS';args.output.write_text(json.dumps(results,indent=2,ensure_ascii=False)+'\n');print('ALL STATIC AND INTEGER CHECKS PASS',flush=True)
if __name__=='__main__':main()
