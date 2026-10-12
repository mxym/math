#!/usr/bin/env python3
"""Rebuild the frozen continuum-power proof and independently replay all safe-owned closure.
All owned outputs are fresh. External pinned dependency caches are read-only.
"""
import argparse, gzip, hashlib, json, os, re, shutil, subprocess, sys
from pathlib import Path
sys.dont_write_bytecode = True
from release_integrity import validate_release
ROOT=Path(__file__).resolve().parents[1]
PROJECT=ROOT/'project'
VERSION='4.34.1'
LEAN_SHA='e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550'
ARCHIVE_SHA='47bf4bbd78f70c2e9670598ab7124d92b6efb7330ff33e5fbb4030f6fd72e4e4'
ALLOWED={'propext','Classical.choice','Quot.sound'}
def need(ok,msg):
 if not ok: raise RuntimeError(msg)
def sha(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for b in iter(lambda:f.read(1048576),b''): h.update(b)
 return h.hexdigest()
def write(p,obj):p.write_text(json.dumps(obj,indent=2,ensure_ascii=False)+'\n')
def stripped(s):
 out=[];i=0;depth=0
 while i<len(s):
  if s.startswith('/-',i):depth+=1;i+=2
  elif depth and s.startswith('-/',i):depth-=1;i+=2
  elif depth:i+=1
  elif s.startswith('--',i):
   j=s.find('\n',i);i=len(s) if j<0 else j
  else:out.append(s[i]);i+=1
 need(depth==0,'unclosed Lean comment');return ''.join(out)
def imports(f):return re.findall(r'^\s*(?:public |private |meta )?import\s+([\w.]+)',f.read_text(),re.M)
def public_names(files):
 names=[]
 for f in files:
  code=stripped(f.read_text());stack=[]
  need('"' not in code,'unreviewed string in proof')
  need(not re.search(r'\b(sorry|admit|axiom|unsafe|partial|native_decide|sorryAx|implemented_by|extern|run_cmd|elab|macro|syntax|initialize|builtin_initialize)\b',code),'source trust escape: '+f.name)
  for line in code.splitlines():
   m=re.match(r'^\s*(namespace|section)(?:\s+([\w.]+))?\s*$',line)
   if m:stack.append((m[1],m[2]));continue
   m=re.match(r'^\s*end(?:\s+([\w.]+))?\s*$',line)
   if m:
    need(bool(stack),'unmatched end');k,n=stack.pop();need(not m[1] or m[1]==n,'scope mismatch');continue
   m=re.match(r'^(?:@\[[^\n]*\]\s*)?(?:nonrec\s+)?(?:theorem|lemma)\s+([\w\'.]+)',line)
   if m:names.append('.'.join([n for k,n in stack if k=='namespace' and n]+[m[1]]))
   if line.startswith('set_option'):need(line in {'set_option backward.isDefEq.respectTransparency false','set_option autoImplicit false'},'unreviewed proof option')
  need(not stack,'unclosed scope')
 return names

def main():
 ap=argparse.ArgumentParser(description=__doc__)
 ap.add_argument('--lean-bin',type=Path,help='Official Linux x86-64 Lean 4.34.1 bin directory')
 ap.add_argument('--dependency-project',type=Path,required=True,help='Project with exact pinned .lake/packages; reused read-only')
 ap.add_argument('--extra-mathlib',type=Path,help='Optional additional exact-pin Mathlib checkout/cache, read-only')
 ap.add_argument('--output',type=Path,required=True,help='Fresh output directory outside release root')
 a=ap.parse_args();out=a.output.resolve()
 need(not out.exists(),'output already exists; choose a fresh directory')
 need(not out.is_relative_to(ROOT),'output must be outside the release source tree')
 env=os.environ.copy();dep=a.dependency_project.resolve()
 # Freeze every source/check/script/report input before any external source executes.
 validate_release(ROOT)
 lean=(a.lean_bin/'lean').resolve() if a.lean_bin else Path(shutil.which('lean') or '/missing-lean').resolve()
 need(lean.is_file(),'install exact toolchain and use --lean-bin')
 need(sha(lean)==LEAN_SHA,'Lean executable hash differs from verified Linux x86-64 release')
 toolchain=lean.parent.parent
 for n,h in json.loads((ROOT/'provenance/TOOLCHAIN_FILES_SHA256.json').read_text())['files'].items():
  need((toolchain/n).is_file() and sha(toolchain/n)==h,'toolchain distribution file mismatch: '+n)
 env['PATH']=str(lean.parent)+os.pathsep+env.get('PATH','')
 env['MATHLIB_NO_CACHE_ON_UPDATE']='1';env['MATHLIB_CACHE_DIR']=str(out/'unused-mathlib-cache')
 out.mkdir(parents=True);logs=out/'logs';logs.mkdir();build=out/'owned';build.mkdir();overlay=out/'official-overlay';overlay.mkdir()
 def clean(s):
  for p,label in sorted([(ROOT,'${PROJECT}'),(out,'${OUTPUT}'),(dep,'${DEPENDENCIES}'),(toolchain,'${TOOLCHAIN}')],key=lambda x:-len(str(x[0]))):s=s.replace(str(p),label)
  if a.extra_mathlib:s=s.replace(str(a.extra_mathlib.resolve()),'${EXTRA_MATHLIB}')
  return s
 def run(cmd,cwd=PROJECT,key=None,expected=0):
  r=subprocess.run(list(map(str,cmd)),cwd=cwd,env=env,text=True,capture_output=True);s=clean(r.stdout+r.stderr)
  if key:(logs/(key+'.log')).write_text(s)
  if expected is not None:need(r.returncode==expected,'command failed: '+clean(' '.join(map(str,cmd)))+'\n'+s)
  return r.returncode,s
 _,version=run([lean,'--version']);need('version 4.34.1,' in version and '5045d0056413266e57c625dcd7c365b10e377c52' in version,'toolchain version mismatch')
 locked_bytes=(PROJECT/'lake-manifest.json').read_bytes();packages=json.loads(locked_bytes)['packages']
 files=sorted((PROJECT/'ContinuumGeometric').glob('*.lean'))+sorted((PROJECT/'ContinuumRemainder').glob('*.lean'))
 names=public_names(files+[PROJECT/'ContinuumGeometric.lean',PROJECT/'ContinuumRemainder.lean'])
 need(len(names)==568 and len(set(names))==568 and set(names)==set(json.loads((ROOT/'audit/independent/INDEPENDENT_PUBLIC_NAMES.json').read_text())),'public inventory mismatch')
 printed=re.findall(r'^#print axioms (\S+)',(ROOT/'audit/checks/AllPublicAxioms.lean').read_text(),re.M)
 need(len(printed)==568 and set(printed)==set(names),'print-axioms coverage mismatch')
 pins={};sources=[]
 for p in packages:
  d=dep/'.lake/packages'/p['name'];_,head=run(['git','rev-parse','HEAD'],cwd=d)
  need(head.strip()==p['rev'],'dependency revision mismatch '+p['name']);run(['git','diff','--quiet','HEAD','--'],cwd=d)
  pins[p['name']]=head.strip();sources.append(d)
 extra=a.extra_mathlib.resolve() if a.extra_mathlib else dep/'.lake/packages/mathlib'
 _,head=run(['git','rev-parse','HEAD'],cwd=extra);need(head.strip()==pins['mathlib'],'extra mathlib revision');run(['git','diff','--quiet','HEAD','--'],cwd=extra)
 dep_roots=[d/'.lake/build/lib/lean' for d in sources]+[toolchain/'lib/lean']
 # Lean resolves whole module roots; union the known official Mathlib caches via symlink leaves.
 for d in [extra/'.lake/build/lib/lean',dep/'.lake/packages/mathlib/.lake/build/lib/lean']:
  for f in sorted(d.rglob('*')):
   if f.is_file():
    q=overlay/f.relative_to(d)
    if not q.exists():q.parent.mkdir(parents=True,exist_ok=True);q.symlink_to(f)
 env['LEAN_PATH']=os.pathsep.join(map(str,[build,overlay]+dep_roots));env['CONTINUUM_AUDIT_OUTPUT']=str(out)
 modules={str(f.relative_to(PROJECT)).removesuffix('.lean').replace('/','.'):f for f in files+[PROJECT/'ContinuumGeometric.lean',PROJECT/'ContinuumRemainder.lean']}
 seen=set();official=[]
 def dep_build(n):
  rel=Path(n.replace('.','/'))
  if any((d/rel.with_suffix('.olean')).is_file() for d in [overlay]+dep_roots):return
  candidates=[d/rel.with_suffix('.lean') for d in sources if (d/rel.with_suffix('.lean')).is_file()]
  need(len(candidates)==1,'missing or ambiguous pinned source '+n);f=candidates[0]
  for i in imports(f):dep_build(i)
  dest=overlay/rel.with_suffix('.olean');dest.parent.mkdir(parents=True,exist_ok=True)
  run([lean,'-o',dest,f],cwd=f.parents[len(rel.parts)-1],key='official.'+n)
  official.append({'module':n,'source_sha256':sha(f),'olean_sha256':sha(dest)})
 def build_one(n):
  if n in seen:return
  f=modules[n]
  for i in imports(f):
   if i in modules:build_one(i)
   else:dep_build(i)
  dest=build/Path(n.replace('.','/')).with_suffix('.olean');dest.parent.mkdir(parents=True,exist_ok=True)
  need(not dest.exists(),'owned artifact was not fresh')
  print('Building '+n,flush=True);run([lean,'-o',dest,f],key=n);seen.add(n)
 for n in sorted(modules):build_one(n)
 need(len(seen)==65,'owned module count')
 prior=json.loads((ROOT/'audit/independent/REBUILD_AND_CONTROL_VERIFICATION.json').read_text())['owned_object_hashes']
 need(set(prior)==set(modules),'reference owned artifact inventory')
 object_hashes={n:sha(build/Path(n.replace('.','/')).with_suffix('.olean')) for n in modules}
 write(out/'OWNED_OBJECT_SHA256.json',object_hashes)
 write(out/'OWNED_OBJECT_COMPARISON.json',{'same':[n for n in sorted(modules) if object_hashes[n]==prior[n]],'different':[n for n in sorted(modules) if object_hashes[n]!=prior[n]],'note':'Object bytes may include path-dependent metadata. Mathematical identity is checked through immutable source, declaration ownership, closures, axioms, and independent empty-kernel replay; binary equality is recorded rather than required.'})
 write(out/'BUILD.json',{'status':'PASS','owned_modules':sorted(seen),'lean':version.strip(),'lean_binary_sha256':sha(lean),'package_pins':pins,'new_official_modules':official,'owned_sources_rebuilt':len(seen),'reused_dependency_caches_read_only':True})
 links=[]
 for link in overlay.rglob('*'):
  if link.is_symlink():
   target=link.resolve(strict=True)
   need(any(target.is_relative_to(d.resolve()) for d in [extra/'.lake/build/lib/lean']+dep_roots),'unexpected dependency symlink target')
   links.append({'link':link.relative_to(overlay).as_posix(),'resolved_sha256':sha(target)})
 write(out/'DEPENDENCY_SYMLINKS.json',{'count':len(links),'links':links})
 for n in ['ExactMain','AllPublicAxioms','ClosureAudit','ReplayClosure','ReplayAllSafeOwned','SemanticProbe']:
  print('Checking '+n,flush=True);_,s=run([lean,ROOT/'audit/checks'/(n+'.lean')],key=n)
  if n=='ReplayClosure':need('EMPTY_KERNEL_REPLAY_PASS 34923 declarations' in s,'missing expected endpoint empty-kernel replay success')
  if n=='ReplayAllSafeOwned':need('ALL_SAFE_OWNED_EMPTY_KERNEL_REPLAY_PASS 35620 declarations' in s,'missing expected all-safe empty-kernel replay success')
 print("Checking graph, ownership and axiom consistency",flush=True)
 # Print-axioms, raw graph, source names and actual module ownership must agree.
 text=(logs/'AllPublicAxioms.log').read_text();rows=re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]",text)
 rows += [(n,'') for n in re.findall(r"'([^']+)' does not depend on any axioms",text)]
 need(len(rows)==568 and {n for n,_ in rows}==set(names),'axiom output incomplete')
 printed_axioms={n:set(x.strip() for x in s.split(',') if x.strip()) for n,s in rows}
 need(all(v<=ALLOWED for v in printed_axioms.values()),'unexpected printed axiom')
 graph=json.loads((out/'FAST_PROOF_GRAPH.json').read_text());inventory=json.loads((out/'FAST_OWNED_INVENTORY.json').read_text());summary=json.loads((out/'FAST_CLOSURE_SUMMARY.json').read_text())
 expected_module_hashes={x['module']:x for x in json.loads((ROOT/'audit/independent/ACTUAL_MODULE_SOURCE_ARTIFACT_HASHES.json').read_text())}
 actual_module_hashes={};libroots=[build,overlay]+dep_roots
 for module in sorted({x['module'] for x in graph}):
  rel=Path(module.replace('.','/'))
  if module in modules:base=PROJECT
  elif module.startswith('Mathlib.'):base=dep/'.lake/packages/mathlib'
  elif module.startswith('Batteries.'):base=dep/'.lake/packages/batteries'
  elif module=='Init' or module.startswith('Init.'):base=toolchain/'src/lean'
  else:raise RuntimeError('unknown defining-module source '+module)
  source=base/rel.with_suffix('.lean')
  need(source.is_file(),'missing actual defining-module source '+module)
  root=next((p for p in libroots if (p/rel.parts[0]).exists() or (len(rel.parts)==1 and (p/rel.with_suffix('.olean')).exists())),None)
  need(root is not None,'unresolved actual defining module '+module)
  artifact=root/rel.with_suffix('.olean');need(artifact.is_file(),'missing actual artifact '+module)
  artifacts={suffix:sha(Path(str(artifact)+suffix)) for suffix in ['', '.private', '.server'] if Path(str(artifact)+suffix).is_file()}
  actual_module_hashes[module]={'module':module,'source_relative':source.relative_to(base).as_posix(),'source_sha256':sha(source),'artifact_sha256':artifacts}
 need(set(actual_module_hashes)==set(expected_module_hashes),'actual defining-module inventory differs')
 artifact_differences=[]
 for module,row in actual_module_hashes.items():
  expected=expected_module_hashes[module]
  need(row['source_relative']==expected['source_relative'] and row['source_sha256']==expected['source_sha256'],'actual module source differs from independent audit: '+module)
  if row['artifact_sha256']!=expected['artifact_sha256']:
   need(module in modules or module in {x['module'] for x in official},'reused dependency artifacts differ from independent audit: '+module)
   artifact_differences.append(module)
 write(out/'ACTUAL_MODULE_SOURCE_ARTIFACT_HASHES.json',list(actual_module_hashes.values()))
 write(out/'ACTUAL_MODULE_COMPARISON.json',{'source_hashes_identical':len(actual_module_hashes),'rebuilt_artifact_differences':artifact_differences,'reused_dependency_artifacts_identical':True})
 g={x['name']:x for x in graph};owned={x['name']:x for x in inventory}
 historical_graph={x['name']:x for x in json.loads(gzip.decompress((ROOT/'audit/independent/FAST_PROOF_GRAPH.json.gz').read_bytes()))}
 historical_inventory={x['name']:x for x in json.loads(gzip.decompress((ROOT/'audit/independent/FAST_OWNED_INVENTORY.json.gz').read_bytes()))}
 def comparison(actual,expected):
  return {'identical':actual==expected,'added':sorted(set(actual)-set(expected)),'missing':sorted(set(expected)-set(actual)),'changed':sorted(k for k in set(actual)&set(expected) if actual[k]!=expected[k])}
 write(out/'DECLARATION_COMPARISON.json',{'proof_graph':comparison(g,historical_graph),'ownership_inventory':comparison(owned,historical_inventory)})
 need(len(owned)==1454 and len(g)==35620,'unexpected ownership or graph count')
 safe_count=sum(not x['unsafe'] and not x['partial'] for x in inventory)
 need(safe_count==1445,'unexpected safe-owned declaration count')
 need({x['name'] for x in inventory if x['public_root']}==set(names),'actual roots differ from source inventory')
 need(all(x['module'] in modules for x in inventory),'unknown defining module')
 def closure(n):
  seen=set();todo=[n]
  while todo:
   x=todo.pop()
   if x in seen:continue
   need(x in g,'missing graph node '+x);seen.add(x);todo.extend(g[x]['all_direct'])
  return seen
 public=[]
 for n,x in owned.items():
  if x['unsafe'] or x['partial']:
   need(n.endswith('._unsafe_rec') and n not in g,'unsafe compiler implementation reached safe closure');continue
  cs=closure(n);axs={v for v in cs if g[v]['kind']=='axiom'}
  need(axs<=ALLOWED and axs==set(x['axioms']),'collector/raw axiom mismatch '+n)
  if n in printed_axioms:
   need(axs==printed_axioms[n],'print/raw axiom mismatch '+n)
   public.append({'name':n,'closure_size':len(cs),'axioms':sorted(axs)})
 main=closure('ContinuumRemainder.continuum_power_target');need(main==set(summary['main_closure']) and len(main)==34919,'main closure differs')
 write(out/'PUBLIC_ROOT_SUMMARIES.json',sorted(public,key=lambda x:x['name']))
 # An outside-namespace axiom must be rejected by THE SAME production audit.
 attack=out/'ownership-control';attack.mkdir()
 (attack/'InjectedAxiom.lean').write_text('import ContinuumRemainder\naxiom GloballyNamedInjectedTarget : ContinuumRemainder.ContinuumPowerTarget\n')
 run([lean,'--root='+str(attack),'-o',attack/'InjectedAxiom.olean',attack/'InjectedAxiom.lean'],key='ownership-injection-compile')
 s=(ROOT/'audit/checks/ClosureAudit.lean').read_text().replace('import ContinuumGeometric\n','import ContinuumGeometric\nimport InjectedAxiom\n',1).replace('def ownedModules : Array String := #[','def ownedModules : Array String := #[ "InjectedAxiom",',1)
 (attack/'RejectInjectedAxiom.lean').write_text(s);old=env['LEAN_PATH'];env['LEAN_PATH']=str(attack)+os.pathsep+old
 code,s=run([lean,'--root='+str(attack),attack/'RejectInjectedAxiom.lean'],key='ownership-injection-rejection',expected=None);env['LEAN_PATH']=old
 need(code!=0 and 'Forbidden owned axiom GloballyNamedInjectedTarget' in s,'production ownership guard did not reject injection')
 print("Checking positive and negative controls",flush=True)
 controls=[]
 def positive(f,key,owned_output=None):
  cmd=[lean]
  if owned_output:cmd+=['--root='+str(f.parent),'-o',owned_output]
  cmd+=[f]
  _,text=run(cmd,key=key)
  need('sorryAx' not in text,'sorry in positive control')
  controls.append({'file':f.relative_to(ROOT).as_posix(),'expected':'accept','passed':True})
 def negative(f,key,kind):
  code,text=run([lean,f],key=key,expected=None)
  need(not any(v in text for v in ['unknown module','unknownIdentifier','unexpected token','unknown constant','Unknown identifier','failed to synthesize']),'broken fixture '+f.name)
  if kind=='false_goal':good='unsolved goals' in text and '⊢ False' in text
  elif kind=='omega_failure':good='omega could not prove the goal' in text
  elif kind=='decide_false':good='Tactic `decide` proved' in text and 'is false' in text
  else:good=any(v in text for v in ['unsolved goals','Tactic','type mismatch'])
  need(code!=0 and good,'wrong negative diagnostic '+f.name)
  controls.append({'file':f.relative_to(ROOT).as_posix(),'expected':kind,'passed':True})
 base=ROOT/'audit/controls/base-positive'
 for f in sorted(base.glob('*.lean')):positive(f,'positive.base.'+f.stem)
 need(len(controls)==21,'base positive count')
 for rel in ['sampling_evidence/SamplingAudit.lean','sampling_evidence/FinalTargetAudit.lean','repair_evidence/RobustErrorCountercontrols.lean','repair_evidence/RobustErrorEvidence.lean','remainder_evidence/ExhaustionAudit.lean','remainder_evidence/SampleStableAudit.lean']:
  f=PROJECT/rel;positive(f,'positive.submitted.'+f.stem)
 positive(ROOT/'submitted-evidence/ExpandedTargetProbe.lean','positive.submitted.ExpandedTargetProbe')
 for name,kind in json.loads((ROOT/'audit/controls/base-negative/expected.json').read_text()).items():
  negative(ROOT/'audit/controls/base-negative'/name,'negative.base.'+Path(name).stem,kind)
 need(len(controls)==50,'base and submitted-positive count')
 for f in sorted((ROOT/'audit/controls/submitted-negative').glob('*.lean')):
  negative(f,'negative.submitted.'+f.stem,'false_goal')
 need(len(controls)==56,'submitted control count')
 independent=ROOT/'audit/controls/independent';control_build=out/'independent-controls';control_build.mkdir()
 old_path=env['LEAN_PATH'];env['LEAN_PATH']=str(control_build)+os.pathsep+old_path
 for name in ['SemanticControls','HypothesisMutations','FinalNonvacuity','UniversalFamilyControl']:
  positive(independent/(name+'.lean'),'positive.independent.'+name,control_build/(name+'.olean'))
 for f in sorted((independent/'negative').glob('*.lean')):negative(f,'negative.independent.'+f.stem,'false_goal')
 env['LEAN_PATH']=old_path
 need(len(controls)==66,'independent control count')
 write(out/'CONTROLS.json',controls)
 _,s1=run([sys.executable,ROOT/'scripts/semantic_exact_checks.py'],key='semantic-normal')
 _,s2=run([sys.executable,'-O',ROOT/'scripts/semantic_exact_checks.py'],key='semantic-optimized');need(s1==s2,'semantic normal/-O mismatch')
 print('Checking package-integrity negative regressions',flush=True)
 run([sys.executable,ROOT/'scripts/test_release_integrity.py','--output',out/'PACKAGING_GUARD_CONTROLS.json'],key='package-integrity-controls')
 # Compress full replayable graph; do not retain duplicate large plaintext graphs.
 for name in ['FAST_PROOF_GRAPH.json','FAST_OWNED_INVENTORY.json','FAST_CLOSURE_SUMMARY.json']:
  p=out/name
  with (out/(name+'.gz')).open('wb') as f:
   with gzip.GzipFile(filename='',mode='wb',fileobj=f,mtime=0) as z:z.write(p.read_bytes())
  p.unlink()
 report={'status':'PASS','scope':'Prescribed-family continuum-power avoidance with eventual power-controlled remainder','owned_modules':len(seen),'public_theorems':568,'owned_declarations':len(owned),'safe_owned_declarations':safe_count,'main_closure_declarations':len(main),'endpoint_union_empty_kernel_replay':34923,'all_safe_empty_kernel_replay':35620,'empty_trust_level_zero_kernel_replay':'PASS','actual_defining_module_guard':'PASS including outside-namespace injected axiom','allowed_axioms':sorted(ALLOWED),'supplied_positive_controls':28,'supplied_negative_controls':28,'independent_positive_files':4,'independent_negative_controls':6,'semantic_normal_optimized_equal':True,'packaging_integrity_controls_normal_and_optimized':'PASS','proof_source_hashes':{str(f.relative_to(ROOT)):sha(f) for f in files+[PROJECT/'ContinuumGeometric.lean',PROJECT/'ContinuumRemainder.lean']},'limits':['Official Lean compiler, kernel implementation, runtime and machine remain trusted.','Standard propext, Classical.choice and Quot.sound axioms remain.','Pinned official dependency caches reused; not a rebuild of all Mathlib.','Independent AI/model review is not external human peer review.','The avoiding set depends on the fixed prescribed nonempty countable family; no universal-family set is claimed.']}
 validate_release(ROOT);write(out/'VERIFICATION.json',report);print(json.dumps(report,indent=2),flush=True)
if __name__=='__main__':main()
