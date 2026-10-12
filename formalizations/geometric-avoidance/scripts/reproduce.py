#!/usr/bin/env python3
"""Rebuild the frozen original MainTarget proof and independently replay its closure.
All owned outputs are fresh. External pinned dependency caches are read-only.
"""
import argparse, collections, gzip, hashlib, json, os, platform, re, shutil, subprocess, sys, tarfile, urllib.request
from pathlib import Path
sys.dont_write_bytecode = True
from release_integrity import validate_release
ROOT=Path(__file__).resolve().parents[1]
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
   if line.startswith('set_option'):need(line=='set_option backward.isDefEq.respectTransparency false','unreviewed proof option')
  need(not stack,'unclosed scope')
 return names

def main():
 ap=argparse.ArgumentParser(description=__doc__)
 ap.add_argument('--verify-release-only',action='store_true',help='Check the complete frozen payload and checksums without running Lean')
 ap.add_argument('--lean-bin',type=Path,help='Official Linux x86-64 Lean 4.34.1 bin directory')
 ap.add_argument('--dependency-project',type=Path,default=ROOT,help='Project with exact pinned .lake/packages; reused read-only')
 ap.add_argument('--extra-mathlib',type=Path,help='Optional additional exact-pin Mathlib checkout/cache, read-only')
 ap.add_argument('--bootstrap',action='store_true',help='Download hash-pinned official Linux x86-64 Lean release')
 ap.add_argument('--fetch-dependencies',action='store_true',help='Fetch exact lockfile packages and selected official caches into this project')
 ap.add_argument('--output',type=Path,default=ROOT/'replay-evidence',help='Must not already exist')
 a=ap.parse_args();out=a.output.resolve()
 if not a.verify_release_only:
  need(not out.exists(),'output already exists; choose a fresh directory')
  need(not out.is_relative_to(ROOT) or out==ROOT/'replay-evidence','output must be outside the source project or exactly its replay-evidence directory')
 env=os.environ.copy();dep=a.dependency_project.resolve()
 need(not(a.fetch_dependencies and dep!=ROOT),'fetching only allowed into this fresh project')
 # Freeze every source/check/script/report input before any external source executes.
 validate_release(ROOT)
 if a.verify_release_only:
  print('RELEASE_INTEGRITY_PASS',flush=True)
  return
 if a.bootstrap:
  need(platform.system()=='Linux' and platform.machine() in ('x86_64','AMD64'),'bootstrap requires Linux x86-64')
  vendor=ROOT/'vendor';vendor.mkdir(exist_ok=True);archive=vendor/'lean-4.34.1-linux.tar.zst';dest=vendor/'lean-4.34.1-linux'
  need(not dest.exists(),'bootstrap destination exists; use --lean-bin for an installed toolchain')
  url='https://github.com/leanprover/lean4/releases/download/v4.34.1/lean-4.34.1-linux.tar.zst'
  with urllib.request.urlopen(url,timeout=120) as response,archive.open('wb') as f:shutil.copyfileobj(response,f)
  need(sha(archive)==ARCHIVE_SHA,'official Lean release archive hash mismatch')
  subprocess.run(['tar','--zstd','-xf',str(archive),'-C',str(vendor)],check=True);archive.unlink();a.lean_bin=dest/'bin'
 lean=(a.lean_bin/'lean').resolve() if a.lean_bin else Path(shutil.which('lean') or '/missing-lean').resolve()
 need(lean.is_file(),'install exact toolchain or use --bootstrap / --lean-bin')
 need(sha(lean)==LEAN_SHA,'Lean executable hash differs from verified Linux x86-64 release')
 toolchain=lean.parent.parent
 for n,h in json.loads((ROOT/'provenance/TOOLCHAIN_FILES_SHA256.json').read_text())['files'].items():
  need((toolchain/n).is_file() and sha(toolchain/n)==h,'toolchain distribution file mismatch: '+n)
 env['PATH']=str(lean.parent)+os.pathsep+env.get('PATH','')
 env['MATHLIB_NO_CACHE_ON_UPDATE']='1';env['MATHLIB_CACHE_DIR']=str(ROOT/'vendor/mathlib-cache')
 out.mkdir(parents=True);logs=out/'logs';logs.mkdir();build=out/'owned';build.mkdir();overlay=out/'official-overlay';overlay.mkdir()
 def clean(s):
  for p,label in sorted([(ROOT,'${PROJECT}'),(out,'${OUTPUT}'),(dep,'${DEPENDENCIES}'),(toolchain,'${TOOLCHAIN}')],key=lambda x:-len(str(x[0]))):s=s.replace(str(p),label)
  if a.extra_mathlib:s=s.replace(str(a.extra_mathlib.resolve()),'${EXTRA_MATHLIB}')
  return s
 def run(cmd,cwd=ROOT,key=None,expected=0):
  r=subprocess.run(list(map(str,cmd)),cwd=cwd,env=env,text=True,capture_output=True);s=clean(r.stdout+r.stderr)
  if key:(logs/(key+'.log')).write_text(s)
  if expected is not None:need(r.returncode==expected,'command failed: '+clean(' '.join(map(str,cmd)))+'\n'+s)
  return r.returncode,s
 _,version=run([lean,'--version']);need('version 4.34.1,' in version and '5045d0056413266e57c625dcd7c365b10e377c52' in version,'toolchain version mismatch')
 locked_bytes=(ROOT/'lake-manifest.json').read_bytes();packages=json.loads(locked_bytes)['packages']
 files=sorted((ROOT/'ContinuumGeometric').glob('*.lean'))
 names=public_names(files+[ROOT/'ContinuumGeometric.lean'])
 need(len(names)==454 and len(set(names))==454 and set(names)==set(json.loads((ROOT/'PublicTheorems.json').read_text())),'public inventory mismatch')
 printed=re.findall(r'^#print axioms (\S+)',(ROOT/'checks/PublicAxioms.lean').read_text(),re.M)
 need(len(printed)==454 and set(printed)==set(names),'print-axioms coverage mismatch')
 if a.fetch_dependencies:
  _,curl_version=run(['curl','--version'])
  match=re.match(r'curl (\d+)\.(\d+)\.(\d+)',curl_version)
  need(match is not None and tuple(map(int,match.groups())) >= (7,81,0),'curl >= 7.81 is required; avoid an extra static-curl bootstrap')
  direct=sorted(set(n for f in files for n in imports(f) if n.startswith('Mathlib.')))
  run([lean.parent/'lake','exe','cache','get']+direct,key='cache-fetch')
  need((ROOT/'lake-manifest.json').read_bytes()==locked_bytes,'dependency operation changed locked manifest')
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
 env['LEAN_PATH']=os.pathsep.join(map(str,[build,overlay]+dep_roots));env['GEOMETRIC_AUDIT_OUTPUT']=str(out)
 modules={str(f.relative_to(ROOT)).removesuffix('.lean').replace('/','.'):f for f in files+[ROOT/'ContinuumGeometric.lean']}
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
 write(out/'BUILD.json',{'status':'PASS','owned_modules':sorted(seen),'lean':version.strip(),'lean_binary_sha256':sha(lean),'package_pins':pins,'new_official_modules':official,'owned_sources_rebuilt':len(seen),'reused_dependency_caches_read_only':True})
 for n in ['ExactMain','IndependentBoundaryFacts','PublicAxioms','ClosureAudit','ReplayClosure']:
  print('Checking '+n,flush=True);_,s=run([lean,ROOT/'checks'/(n+'.lean')],key=n)
  if n=='ReplayClosure':need('EMPTY_KERNEL_REPLAY_PASS 34771 declarations' in s,'missing expected empty-kernel replay success')
 print("Checking graph, ownership and axiom consistency",flush=True)
 # Print-axioms, raw graph, source names and actual module ownership must agree.
 text=(logs/'PublicAxioms.log').read_text();rows=re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]",text)
 rows += [(n,'') for n in re.findall(r"'([^']+)' does not depend on any axioms",text)]
 need(len(rows)==454 and {n for n,_ in rows}==set(names),'axiom output incomplete')
 printed_axioms={n:set(x.strip() for x in s.split(',') if x.strip()) for n,s in rows}
 need(all(v<=ALLOWED for v in printed_axioms.values()),'unexpected printed axiom')
 graph=json.loads((out/'FAST_PROOF_GRAPH.json').read_text());inventory=json.loads((out/'FAST_OWNED_INVENTORY.json').read_text());summary=json.loads((out/'FAST_CLOSURE_SUMMARY.json').read_text())
 g={x['name']:x for x in graph};owned={x['name']:x for x in inventory}
 need(len(owned)==1164 and len(g)==35197,'unexpected ownership or graph count')
 safe_count=sum(not x['unsafe'] and not x['partial'] for x in inventory)
 need(safe_count==1155,'unexpected safe-owned declaration count')
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
 main=closure('ContinuumGeometric.geometric_main_target');need(main==set(summary['main_closure']) and len(main)==34771,'main closure differs')
 write(out/'PUBLIC_ROOT_SUMMARIES.json',sorted(public,key=lambda x:x['name']))
 # An outside-namespace axiom must be rejected by THE SAME production audit.
 attack=out/'ownership-control';attack.mkdir()
 (attack/'InjectedAxiom.lean').write_text('import ContinuumGeometric\naxiom GloballyNamedInjectedTarget : ContinuumGeometric.MainTarget\n')
 run([lean,'--root='+str(attack),'-o',attack/'InjectedAxiom.olean',attack/'InjectedAxiom.lean'],key='ownership-injection-compile')
 s=(ROOT/'checks/ClosureAudit.lean').read_text().replace('import ContinuumGeometric\n','import ContinuumGeometric\nimport InjectedAxiom\n',1).replace('def ownedModules : Array String := #[','def ownedModules : Array String := #[ "InjectedAxiom",',1)
 (attack/'RejectInjectedAxiom.lean').write_text(s);old=env['LEAN_PATH'];env['LEAN_PATH']=str(attack)+os.pathsep+old
 code,s=run([lean,'--root='+str(attack),attack/'RejectInjectedAxiom.lean'],key='ownership-injection-rejection',expected=None);env['LEAN_PATH']=old
 need(code!=0 and 'Forbidden owned axiom GloballyNamedInjectedTarget' in s,'production ownership guard did not reject injection')
 print("Checking positive and negative controls",flush=True)
 controls=[]
 for f in sorted((ROOT/'checks/positive').glob('*.lean')):
  run([lean,f],key='positive.'+f.stem);controls.append({'file':str(f.relative_to(ROOT)),'expected':'accept','passed':True})
 for name,kind in json.loads((ROOT/'checks/negative/expected.json').read_text()).items():
  f=ROOT/'checks/negative'/name;code,s=run([lean,f],key='negative.'+f.stem,expected=None)
  good=('⊢ False' in s and 'unsolved goals' in s) if kind=='false_goal' else ('omega could not prove the goal' in s if kind=='omega_failure' else 'Tactic `decide` proved' in s and 'is false' in s)
  need(code!=0 and good,'wrong negative diagnostic '+name);controls.append({'file':str(f.relative_to(ROOT)),'expected':kind,'passed':True})
 write(out/'CONTROLS.json',controls)
 _,s1=run([sys.executable,ROOT/'scripts/semantic_exact_checks.py'],key='semantic-normal')
 _,s2=run([sys.executable,'-O',ROOT/'scripts/semantic_exact_checks.py'],key='semantic-optimized');need(s1==s2,'semantic normal/-O mismatch')
 print('Checking package-integrity negative regressions',flush=True)
 run([sys.executable,ROOT/'scripts/test_release_integrity.py','--output',out/'PACKAGING_GUARD_CONTROLS.json'],key='package-integrity-controls')
 # Compress full replayable graph; keep no duplicate 454-root closure expansion.
 for name in ['FAST_PROOF_GRAPH.json','FAST_OWNED_INVENTORY.json','FAST_CLOSURE_SUMMARY.json']:
  p=out/name
  with (out/(name+'.gz')).open('wb') as f:
   with gzip.GzipFile(filename='',mode='wb',fileobj=f,mtime=0) as z:z.write(p.read_bytes())
 report={'status':'PASS','scope':'Full original all-real affine-geometric MainTarget only','owned_modules':len(seen),'public_theorems':454,'owned_declarations':len(owned),'safe_owned_declarations':safe_count,'main_closure_declarations':len(main),'empty_trust_level_zero_kernel_replay':'PASS','actual_defining_module_guard':'PASS including outside-namespace injected axiom','allowed_axioms':sorted(ALLOWED),'positive_controls':21,'negative_controls':22,'semantic_normal_optimized_equal':True,'packaging_integrity_controls_normal_and_optimized':'PASS','proof_source_hashes':{str(f.relative_to(ROOT)):sha(f) for f in files+[ROOT/'ContinuumGeometric.lean']},'limits':['Official Lean compiler, kernel implementation, runtime and machine remain trusted.','Standard propext, Classical.choice and Quot.sound axioms remain.','Pinned official dependency caches reused; not a rebuild of all Mathlib.','Independent AI/model review is not external human peer review.','Stronger nonlinear-remainder theorem is not formalized here.']}
 write(out/'VERIFICATION.json',report);print(json.dumps(report,indent=2),flush=True)
if __name__=='__main__':main()
