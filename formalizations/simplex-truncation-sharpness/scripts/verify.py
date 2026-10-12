#!/usr/bin/env python3
"""Fresh 125-module build, 850 public/1849 owner checks and empty-kernel replay.
Public derivative of the independent audit. Does not execute historical packagers.
"""
from pathlib import Path
import argparse,gzip,hashlib,json,os,re,shutil,subprocess,sys,time
sys.dont_write_bytecode=True
from release_integrity import validated_snapshot, require, ReleaseIntegrityError
ROOT=Path(__file__).resolve().parents[1]
PROJECT=ROOT/'project'; F=PROJECT/'formal'
ALLOWED={'propext','Classical.choice','Quot.sound'}
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def save(p,x):p.write_text(json.dumps(x,indent=2,ensure_ascii=False)+'\n')
def main():
 ap=argparse.ArgumentParser(description=__doc__)
 ap.add_argument('--lean-bin',type=Path)
 ap.add_argument('--dependency-project',type=Path,required=True)
 ap.add_argument('--extra-cache',action='append',type=Path,default=[],help='Read-only additional exact-pin external artifacts; no owned artifacts are selected')
 ap.add_argument('--output',type=Path,required=True)
 a=ap.parse_args(); snapshot=validated_snapshot(ROOT)
 import source_inventory as si
 require(not a.output.is_symlink(),'output must not be a symlink')
 out=a.output.resolve();require(not out.exists(),'choose a fresh output directory')
 require(not out.is_relative_to(ROOT),'output must be outside release')
 lean=(a.lean_bin/'lean').resolve() if a.lean_bin else Path(shutil.which('lean') or '/missing-lean').resolve()
 require(lean.is_file(),'install exact toolchain and use --lean-bin')
 tool=lean.parent.parent
 for n,h in json.loads((ROOT/'provenance/TOOLCHAIN_FILES_SHA256.json').read_text())['files'].items():
  require((tool/n).is_file() and sha(tool/n)==h,'toolchain distribution mismatch: '+n)
 dep=a.dependency_project.resolve();pk=dep/'.lake/packages'
 env=os.environ.copy();env['PATH']=str(lean.parent)+os.pathsep+env.get('PATH','');env['GIT_OPTIONAL_LOCKS']='0'
 def cmd(argv,cwd=F):
  r=subprocess.run(list(map(str,argv)),cwd=cwd,env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
  return r.returncode,r.stdout
 code,version=cmd([lean,'--version']);require(code==0 and 'version 4.34.1,' in version and '5045d0056413266e57c625dcd7c365b10e377c52' in version,'Lean version mismatch')
 pins={x['name']:x['rev'] for x in json.loads((F/'lake-manifest.json').read_text())['packages']}
 require(len(pins)==9,'dependency count differs')
 for n,rev in pins.items():
  code,head=cmd(['git','rev-parse','HEAD'],pk/n);require(code==0 and head.strip()==rev,'dependency pin differs: '+n)
  code,dirty=cmd(['git','status','--porcelain','--untracked-files=no'],pk/n);require(code==0 and not dirty,'tracked dependency sources dirty: '+n)
 sources={'.'.join(f.relative_to(F).with_suffix('').parts):f for ns in ['Entry005','Mxym','OAI'] for f in (F/ns).rglob('*.lean')};sources['Entry005']=F/'Entry005.lean'
 require(len(sources)==125,'owned source count differs')
 for n,f in sources.items():
  require(not re.search(r'\b(sorry|admit|axiom|opaque|unsafe|partial|native_decide|sorryAx|implemented_by|extern)\b|debug\.skipKernelTC',si.source_code(f.read_text())),'proof escape: '+n)
 names=si.public_proof_inventory(sources)
 reference=json.loads((ROOT/'audit/independent/source-public-theorems.json').read_text())
 require(names==reference and len(names)==850,'source public inventory differs')
 si.root_sources=lambda _:sources
 graph=si.closure(F,pk,tool/'src/lean',pins)
 prior_graph=json.loads(gzip.decompress((ROOT/'audit/independent/import-closure.json.gz').read_bytes()))
 require(graph==prior_graph and len(graph)==4745,'complete dependency source closure differs from independent audit')
 out.mkdir(parents=True);logs=out/'logs';logs.mkdir();owned=out/'owned';owned.mkdir();overlay=out/'external-overlay';overlay.mkdir()
 roots=[(pk/n/'.lake/build/lib/lean').resolve() for n in pins]+[tool/'lib/lean']+[p.resolve() for p in a.extra_cache]
 # Materialize only needed external artifacts as symlinks. No old owned namespace
 # is ever put on LEAN_PATH. Dependency roots are trusted runtime inputs, read-only.
 reference_artifacts=json.loads(gzip.decompress((ROOT/'provenance/EXTERNAL_ARTIFACTS_REFERENCE.json.gz').read_bytes()))['modules']
 require(set(reference_artifacts)=={n for n,r in graph.items() if r['package']!='owned'},'external artifact reference coverage differs')
 suffixes=['.olean','.olean.private','.olean.server','.ilean','.ir','.ir.sig']
 missing={};links=[];cache_mismatches=[]
 for n,r in graph.items():
  if r['package']=='owned':continue
  rel=Path(n.replace('.','/'));ref=reference_artifacts[n]
  require(ref['package']==r['package'] and ref['source_sha256']==r['sha256'],'external artifact source linkage differs: '+n)
  found=None;actual=None
  candidates=[tool/'lib/lean'] if r['package']=='lean' else roots
  for candidate in candidates:
   if not (candidate/rel.with_suffix('.olean')).is_file():continue
   hashes={suffix:sha(candidate/rel.with_suffix(suffix)) for suffix in suffixes if (candidate/rel.with_suffix(suffix)).is_file()}
   if hashes==ref['artifacts']:found=candidate;actual=hashes;break
  if found is None:
   require(r['package']!='lean','official toolchain artifact differs: '+n)
   missing[n]=r;cache_mismatches.append(n);continue
  for suffix in actual:
   src=found/rel.with_suffix(suffix);dst=overlay/rel.with_suffix(suffix)
   dst.parent.mkdir(parents=True,exist_ok=True);dst.symlink_to(src)
  links.append({'module':n,'source_sha256':r['sha256'],'artifact_sha256':actual,'matches_independent_audit_reference':True})
 env['LEAN_PATH']=os.pathsep.join(map(str,[owned,tool/'lib/lean',overlay]))
 def clean(s):
  for p,label in sorted([(ROOT,'${RELEASE}'),(out,'${OUTPUT}'),(dep,'${DEPENDENCIES}'),(tool,'${TOOLCHAIN}')],key=lambda q:-len(str(q[0]))):s=s.replace(str(p),label)
  for i,p in enumerate(a.extra_cache):s=s.replace(str(p.resolve()),'${EXTRA_CACHE_'+str(i)+'}')
  return s
 def run(argv,key,cwd=F,negative=False):
  code,text=cmd(argv,cwd);text=clean(text);(logs/(key+'.log')).write_text(text)
  require(not re.search(r'\bwarning\s*:',text),'unexpected warning: '+key)
  if negative:
   require(code!=0 and ('type mismatch' in text.lower() or 'Type mismatch' in text),'negative fixture did not fail for intended type mismatch: '+key)
   require(not any(s in text.lower() for s in ['unknown module','unknown identifier','unexpected token','unknown constant','failed to synthesize']),'broken negative fixture: '+key)
  else:require(code==0 and not re.search(r'\berror\s*:',text),'command failed: '+key+'\n'+text)
  return text
 results=[]
 for n in si.topo(missing):
  r=missing[n];cwd=pk/r['package'] if r['package']!='lean' else tool/'src/lean';src=cwd/r['relative_source'];dst=overlay/Path(n.replace('.','/')).with_suffix('.olean');dst.parent.mkdir(parents=True,exist_ok=True)
  print('BUILD_EXTERNAL '+n,flush=True)
  run([lean,'-DautoImplicit=false','-DmaxSynthPendingDepth=3','-o',dst,src.relative_to(cwd)],'external.'+n,cwd)
 for n in si.topo({n:graph[n] for n in sources}):
  src=sources[n];dst=owned/Path(n.replace('.','/')).with_suffix('.olean');dst.parent.mkdir(parents=True,exist_ok=True)
  for imp in graph[n]['imports']:
   if imp in sources:
    q=owned/Path(imp.replace('.','/')).with_suffix('.olean');require(q.is_file() and not q.is_symlink(),'owned import not freshly built: '+imp)
  print('BUILD '+n,flush=True);start=time.monotonic()
  run([lean,'-DautoImplicit=false','-o',dst,src.relative_to(F)],n)
  require(dst.is_file() and not dst.is_symlink(),'owned output is not fresh regular file')
  results.append({'module':n,'source_sha256':sha(src),'olean_sha256':sha(dst),'seconds':time.monotonic()-start})
 save(out/'BUILD.json',{'status':'PASS','owned_modules':125,'new_external_modules':sorted(missing),'compiler':version.strip(),'pins':pins,'results':results,'owned_cache_fallbacks':False,'external_cache_missing_or_mismatched_rebuilt':cache_mismatches})
 save(out/'EXTERNAL_ARTIFACTS.json',links)
 checks=ROOT/'audit/checks'
 public=run([lean,'-DautoImplicit=false',checks/'IndependentPublicAudit.lean'],'IndependentPublicAudit')
 rows=re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",public,re.S)+[(n,'') for n in re.findall(r"'([^']+)' does not depend on any axioms",public)]
 require(len(rows)==850 and {n for n,_ in rows}==set(names),'public axiom output incomplete or duplicate')
 axs={n:sorted({re.sub(r'\.\{[^}]+\}$','',x.strip()) for x in ax.split(',') if x.strip()}) for n,ax in rows}
 require(all(set(v)<=ALLOWED for v in axs.values()),'unexpected public axiom')
 prior_axioms=json.loads(gzip.decompress((ROOT/'audit/independent/public850-axioms.json.gz').read_bytes()));require(axs==prior_axioms,'public axiom sets differ')
 text=run([lean,'-DautoImplicit=false',checks/'OwnedInventory.lean'],'OwnedInventory')
 inventory=json.loads(text.split('OWNED_INVENTORY_JSON=',1)[1].strip());require(len(inventory)==1849 and len({r['name'] for r in inventory})==1849,'owned inventory incomplete/duplicate')
 require(all(not r['unsafe'] and not r['partial'] and r['kind'] not in ['axiom','opaque'] and set(r['axioms'])<=ALLOWED for r in inventory),'unsafe/partial/opaque/custom owned declaration')
 prior=json.loads(gzip.decompress((ROOT/'audit/independent/owned-declarations.json.gz').read_bytes()))
 require({r['name']:r for r in inventory}=={r['name']:r for r in prior},'actual declaration type/owner/kind/axioms differ from independent audit')
 byname={r['name']:r for r in inventory}
 for fn in ['all-public-theorems-by-module.json','truncation-public-by-module.json']:
  for path,ns in json.loads((PROJECT/'sources'/fn).read_text()).items():
   mod=path[len('formal/'):-5].replace('/','.')
   require(all(byname[n]['module']==mod and byname[n]['kind']=='theorem' for n in ns),'public ownership mismatch: '+mod)
 for n in ['LiteralPositiveControls','NegativeMainSubstitution','NegativeFormulaOmission','KernelNegativeControl']:
  text=run([lean,'-DautoImplicit=false',checks/(n+'.lean')],n,negative=n.startswith('Negative'))
  if n=='KernelNegativeControl':require('EXPECTED_KERNEL_REJECTION:' in text and 'KERNEL_NEGATIVE_CONTROL_PASS' in text,'kernel negative control marker missing')
 text=run([lean,'-DautoImplicit=false',checks/'ReplayAllSafeOwned.lean'],'ReplayAllSafeOwned')
 require('REPLAY_BEGIN roots=1849 closure=55163 skipped=[] trust=0 empty=true' in text and 'ALL_SAFE_OWNED_EMPTY_KERNEL_REPLAY_PASS roots=1849 closure=55163' in text,'empty trust-zero replay counts differ')
 for mode in [[],['-O']]:run([sys.executable,*mode,'-B',ROOT/'scripts/exact_rational_controls.py','--output',out/('RATIONAL'+('-O' if mode else '')+'.json')],'rational'+('-O' if mode else ''))
 # Keep compact inventories; raw logs remain local and are not part of the archive.
 for n,x in [('OWNED_INVENTORY',inventory),('PUBLIC_AXIOMS',axs)]:
  (out/(n+'.json.gz')).write_bytes(gzip.compress((json.dumps(x,sort_keys=True)+'\n').encode(),mtime=0))
 require(validated_snapshot(ROOT)==snapshot,'frozen release bytes changed during verification')
 save(out/'FINAL_VERIFICATION.json',{'status':'PASS','fresh_owned_modules':125,'public_proofs':850,'owned_declarations':1849,'recursive_kernel_declarations':55163,'empty_environment':True,'trust_level':0,'skipped':[],'sources_unchanged':True,'literal_truncationSharpnessGoal_proved':True,'upper_sharpMainGoal_proved':False,'dependency_cache_read_only':True})
 print('SHARPNESS_PUBLIC_REPLAY_PASS 125 fresh modules; 850 public; 1849 owned; 55163 empty-kernel declarations',flush=True)
if __name__=='__main__':
 try:main()
 except (ReleaseIntegrityError,OSError,ValueError,KeyError,RuntimeError) as error:
  print(str(error),file=sys.stderr);sys.exit(1)
