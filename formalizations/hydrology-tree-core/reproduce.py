#!/usr/bin/env python3
"""Fresh owned-source builds and empty trust-zero kernel replay of partial results."""
from pathlib import Path
import argparse, datetime, hashlib, json, os, re, shutil, subprocess, time
ROOT=Path(__file__).resolve().parent
ALLOWED={'propext','Classical.choice','Quot.sound'}

def digest(p): return hashlib.sha256(p.read_bytes()).hexdigest()

def strip_comments(s):
 out=[];i=depth=0
 while i<len(s):
  if s.startswith('/-',i):depth+=1;i+=2
  elif depth and s.startswith('-/',i):depth-=1;i+=2
  elif depth:i+=1
  elif s.startswith('--',i):
   j=s.find('\n',i);i=len(s) if j<0 else j
  else:out.append(s[i]);i+=1
 if depth:raise RuntimeError('Unterminated comment')
 return ''.join(out)

def snapshot():
 expected=json.loads((ROOT/'SOURCE_SHA256.json').read_text())
 got={p:digest(ROOT/p) for p in expected}
 if got!=expected:raise RuntimeError('Source manifest mismatch')
 for module in json.loads((ROOT/'MODULES.json').read_text()):
  s=strip_comments((ROOT/(module.replace('.','/')+'.lean')).read_text())
  if re.search(r'\b(sorry|admit|axiom|native_decide|unsafe|implemented_by|extern)\b',s):
   raise RuntimeError('Forbidden token in '+module)
 return got

def main():
 ap=argparse.ArgumentParser(description=__doc__)
 ap.add_argument('--output-dir',type=Path,required=True)
 ap.add_argument('--mathlib-dir',type=Path,default=ROOT/'.lake/packages/mathlib')
 ap.add_argument('--lean',default=shutil.which('lean'))
 args=ap.parse_args()
 if not args.lean:ap.error('Activate Lean 4.34.1 first')
 out=args.output_dir.resolve();out.mkdir(parents=True,exist_ok=False)
 report={'status':'RUNNING','scope':'PARTIAL actual polynomial Jacobian core and physical tree rate-chart/matrix semantics; not the full characteristic-coefficient Jacobian theorem or fiber classification','started_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'commands':[]}
 try:
  before=snapshot();report['source_sha256']=before
  lean=Path(args.lean).resolve();env=os.environ.copy();env['PATH']=str(lean.parent)+os.pathsep+env.get('PATH','');env.pop('LEAN_PATH',None);env.pop('LEAN_SRC_PATH',None)
  version=subprocess.check_output([str(lean),'--version'],text=True).strip()
  if 'version 4.34.1,' not in version or '5045d0056413266e57c625dcd7c365b10e377c52' not in version:raise RuntimeError(version)
  report['lean_version']=version;report['lean_executable_sha256']=digest(lean)
  dirs={};deps={};mathlib=args.mathlib_dir.resolve()
  for d in json.loads((ROOT/'lake-manifest.json').read_text())['packages']:
   if d['type']!='git':raise RuntimeError('Unexpected unpinned path dependency')
   directory=mathlib if d['name']=='mathlib' else mathlib.parent/d['name']
   rev=subprocess.check_output(['git','-C',str(directory),'rev-parse','HEAD'],text=True).strip()
   if rev!=d['rev']:raise RuntimeError('Dependency revision mismatch: '+d['name'])
   tree=subprocess.check_output(['git','-C',str(directory),'ls-tree','-rz','HEAD'])
   checked=0
   for entry in tree.split(b'\0'):
    if not entry:continue
    meta,rel=entry.split(b'\t',1);mode,typ,wanted=meta.decode().split();rel=rel.decode()
    if typ!='blob' or not (rel.endswith('.lean') or rel in {'lakefile.lean','lakefile.toml','lean-toolchain','lake-manifest.json'}):continue
    p=directory/rel;data=os.readlink(p).encode() if mode=='120000' else p.read_bytes();data=data.replace(b'\r\n',b'\n')
    actual=hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()
    if actual!=wanted:raise RuntimeError('Modified dependency source: '+str(p))
    checked+=1
   dirs[d['name']]=directory;deps[d['name']]={'revision':rev,'source_blobs_checked':checked}
  report['dependencies']=deps
  def run(cmd,cwd,name,neg=False):
   start=time.monotonic()
   with (out/name).open('w') as f:r=subprocess.run(cmd,cwd=cwd,env=env,stdout=f,stderr=subprocess.STDOUT,timeout=1800)
   s=(out/name).read_text(errors='replace');record={'command':list(map(str,cmd)),'returncode':r.returncode,'seconds':round(time.monotonic()-start,3),'log':name};report['commands'].append(record);print(json.dumps(record),flush=True)
   if neg:
    if r.returncode==0 or 'error' not in s.lower():raise RuntimeError('Negative control accepted: '+name)
    if any(x in s.lower() for x in ['unknown module prefix','object file','already been declared']):raise RuntimeError('Infrastructure failure, not a negative control: '+name)
   elif r.returncode:raise RuntimeError('Command failed: '+name+'\n'+s[-4000:])
  lake=out/'lake-source';lake.mkdir()
  for rel in before:
   p=lake/rel;p.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(ROOT/rel,p)
  packages=lake/'.lake/packages';packages.mkdir(parents=True)
  for name,d in dirs.items():(packages/name).symlink_to(d,target_is_directory=True)
  report['initial_owned_objects']=len(list(lake.rglob('*.olean')))
  run([str(lean.parent/'lake'),'build'],lake,'lake-build.log')
  fresh=out/'fresh';fresh.mkdir();env['LEAN_PATH']=os.pathsep.join([str(fresh)]+[str(d/'.lake/build/lib/lean') for d in dirs.values()])
  modules=json.loads((ROOT/'MODULES.json').read_text());report['modules']=modules
  for m in modules:
   rel=m.replace('.','/');dest=fresh/(rel+'.lean');dest.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(ROOT/(rel+'.lean'),dest)
   run([str(lean),'-o',rel+'.olean',rel+'.lean'],fresh,'build-'+m+'.log')
  report['object_sha256']={str(p.relative_to(fresh)):digest(p) for p in sorted(fresh.rglob('*.olean'))}
  for name in ['Audit','Replay']:
   shutil.copyfile(ROOT/'audit'/(name+'.lean'),fresh/(name+'.lean'));run([str(lean),name+'.lean'],fresh,name.lower()+'.log')
  text=(out/'replay.log').read_text();match=re.search(r'EMPTY_KERNEL_REPLAY_PASS (\d+) declarations; (\d+) roots; trust level zero',text)
  if not match:raise RuntimeError('Missing replay completion marker')
  axioms=set((fresh/'replayed-axioms.txt').read_text().splitlines())
  if not axioms.issubset(ALLOWED):raise RuntimeError('Unexpected axioms')
  report['kernel_replay']={'declarations':int(match[1]),'roots':int(match[2]),'trust_level':0,'axioms':sorted(axioms)}
  for name in ['replayed-axioms.txt','replayed-closure.txt']:shutil.copyfile(fresh/name,out/name)
  controls=[('HydrologyTree/SubtreeAssignment.lean','(hassign : SameSubtreeCharacteristics t x y) : x = y := by','(hassign : SameSubtreeCharacteristics t x y) : x ≠ y := by'),('HydrologyTree/PhysicalBranchRecovery.lean','x.1 c.val * outwardByVertex x.2 c.val = y.1 c.val * outwardByVertex y.2 c.val := by','x.1 c.val + outwardByVertex x.2 c.val = y.1 c.val + outwardByVertex y.2 c.val := by'),('HydrologyTree/BranchStep.lean','(-1 : ℝ)^(ChildFactorDegrees ms).sum *\n        pairwiseResultants (familyPolynomials (ChildFactorDegrees ms) z.1.1)^2 *\n          scaleFamilyWeight ms z.1.2 := by\n  have he','(-1 : ℝ)^(ChildFactorDegrees ms).sum *\n        pairwiseResultants (familyPolynomials (ChildFactorDegrees ms) z.1.1)^2 := by\n  have he'),('HydrologyTree/PhysicalModes.lean','FullPositiveModes t x ↔ ∀ z : ℝ, ¬SiblingCollisionSomewhere t x z := by','FullPositiveModes t x ↔ ∀ z : ℝ, SiblingCollisionSomewhere t x z := by'),('HydrologyTree/StieltjesNumerator.lean','w i * ∏ j ∈ Finset.univ.erase i, (r j-r i) := by','w i + ∏ j ∈ Finset.univ.erase i, (r j-r i) := by'),('HydrologyTree/PhysicalStieltjes.lean','(∑ i, w i) = 1 ∧','(∑ i, w i) = 2 ∧'),('HydrologyTree/GroundedPositivity.lean','(hg : ∀ e, 0 < g e) (hell : 0 < ell)','(hg : ∀ e, 0 < g e) (hell : 0 ≤ ell)'),('HydrologyTree/CatenaryCoprime.lean',': x = y := by\n  exact catenary_global_transfer_identification',': x ≠ y := by\n  exact catenary_global_transfer_identification'),('HydrologyTree/CatenaryGlobal.lean','∀ y : TreeRates n, pathCoefficientMap n y = pathCoefficientMap n x → y = x := by\n  have hr : PathRegularRates n x := by','∀ y : TreeRates n, pathCoefficientMap n y = pathCoefficientMap n x → y ≠ x := by\n  have hr : PathRegularRates n x := by'),('HydrologyTree/RootRecovery.lean','(h : physicalCoefficientMap t x = physicalCoefficientMap t y) : x.1 0 = y.1 0 := by','(h : physicalCoefficientMap t x = physicalCoefficientMap t y) : x.1 0 = y.1 0 + 1 := by'),('HydrologyTree/CatenaryOrientation.lean','catenaryCanonicalJacobian n x ^ 2 =','catenaryCanonicalJacobian n x ^ 4 ='),('HydrologyTree/CatenaryJacobian.lean','∃ i : Fin n, i.val+1 < n ∧ x.2 i = 0) := by\n  rw [pathRateMonomial','∃ i : Fin n, i.val < n ∧ x.2 i = 0) := by\n  rw [pathRateMonomial'),('HydrologyTree/PhysicalConstants.lean','(physicalCharacteristic t x).eval 0 = x.1 0 * ∏ e : Fin n, x.1 e.succ := by','(physicalCharacteristic t x).eval 0 = ∏ e : Fin n, x.1 e.succ := by'),('HydrologyTree/RateCoordinates.lean','(ratePartitionEquiv t x).1 = x.1 0 := rfl','(ratePartitionEquiv t x).1 = 0 := rfl'),('HydrologyTree/FiniteCancellation.lean','(ha : ∀ c, a c ≠ 0)','(ha : ∀ c, True)'),('HydrologyTree/PhysicalRecursion.lean','physicalRootCofactor t x = ∏ c : RootChild t, childCharacteristic t x c := by','physicalRootCofactor t x = 1 + ∏ c : RootChild t, childCharacteristic t x c := by'),('HydrologyTree/ChildRates.lean','(childRates t c x).1 0 = x.1 c.val := by','(childRates t c x).1 0 = 0 := by'),('HydrologyTree/ChildTree.lean','childEdgeCount t c < n := by','childEdgeCount t c < n-1 := by'),('HydrologyTree/RootBranches.lean','rootPartitionEquiv t (.inr ⟨c,v⟩) = v.val := rfl','rootPartitionEquiv t (.inr ⟨c,v⟩) = 0 := rfl'),('HydrologyTree/PhysicalRootDecomposition.lean','(rootInwardRow t x) (rootOutwardColumn t x)','0 (rootOutwardColumn t x)'),('HydrologyTree/FamilyGluing.lean','familyGlueJacobian ms x = pairwiseResultants (familyPolynomials ms x.1)^2 := by','familyGlueJacobian ms x = pairwiseResultants (familyPolynomials ms x.1)^3 := by'),('HydrologyTree/PhysicalLeaf.lean','(X + C (x.1 (terminalVertex n))) * (terminalMinor t x).charpoly -','(X - C (x.1 (terminalVertex n))) * (terminalMinor t x).charpoly -'),('HydrologyTree/EdgeCharacteristic.lean','A.charpoly * B.charpoly - C (a*f) *','A.charpoly * B.charpoly - C (a*f+1) *'),('HydrologyTree/BranchAssembly.lean','(branchRoot bs) = branchProduct bs := by','(branchRoot bs) = branchProduct bs + 1 := by'),('HydrologyTree/PhysicalBridge.lean','matrixCoordinateJacobian t x = ∏ i : Fin n, x.1 i.succ := by','matrixCoordinateJacobian t x = ∏ i : Fin n, x.2 i := by'),('HydrologyTree/CompartmentMatrix.lean','(∑ v : Fin (n+1), (compartmentMatrix t x *ᵥ s) v) = -x.1 0 * s 0 := by','(∑ v : Fin (n+1), (compartmentMatrix t x *ᵥ s) v) = 0 := by'),('HydrologyTree/Scaling.lean','monicScalingJacobian x = x.1 ^ n := by','monicScalingJacobian x = x.1 ^ (n+1) := by'),('HydrologyTree/RootUpdate.lean','rootCoefficientJacobian x = (-1 : ℝ)^n := by','rootCoefficientJacobian x = 1 := by'),('HydrologyTree/Gluing.lean','m n ^ 2 := by','m n ^ 3 := by'),('HydrologyTree/Gluing.lean','repeatedBlock (monoSylv x.1) (lowSylv x.2)','repeatedBlock (monoSylv x.1) 0'),('HydrologyTree/BlockJacobian.lean',').det ^ 2 := by',').det ^ 3 := by'),('HydrologyTree/Coefficients.lean','⟨X^n, Polynomial.mem_degreeLT.mpr','⟨X^(n+1), Polynomial.mem_degreeLT.mpr')]
  report['negative_controls']=[]
  for i,(rel,old,new) in enumerate(controls):
   text=(ROOT/rel).read_text()
   if text.count(old)!=1:raise RuntimeError('Ambiguous mutation '+rel)
   neg=out/('negative-'+str(i+1));(neg/rel).parent.mkdir(parents=True);(neg/rel).write_text(text.replace(old,new))
   run([str(lean),rel],neg,'negative-'+str(i+1)+'.log',True);report['negative_controls'].append({'source':rel,'old':old,'new':new,'rejected':True})
  if snapshot()!=before:raise RuntimeError('Source changed during verification')
  report['source_hashes_unchanged']=True
  import gzip, io, tarfile
  bundle=out/'verified-source.tar.gz'
  with bundle.open('wb') as raw:
   with gzip.GzipFile(fileobj=raw,mode='wb',mtime=0) as gz:
    with tarfile.open(fileobj=gz,mode='w') as tar:
     names=set(before)|{'SOURCE_SHA256.json','README.md','DEPENDENCY_MAP.md','GAPS.md','DEPENDENCIES.dot'}
     for name in sorted(names):
      p=ROOT/name
      if not p.is_file():raise RuntimeError('Missing deliverable '+name)
      data=p.read_bytes();info=tarfile.TarInfo('hydrology-tree-core/'+name)
      info.size=len(data);info.mtime=0;info.mode=0o644
      tar.addfile(info,io.BytesIO(data))
  report['verified_source_archive_sha256']=digest(bundle)
  report['status']='PASS'

 except Exception as e:
  report['status']='FAIL';report['error']=repr(e)
 finally:
  report['finished_utc']=datetime.datetime.now(datetime.timezone.utc).isoformat();(out/'verification.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report),flush=True)
 return 0 if report['status']=='PASS' else 1
if __name__=='__main__':raise SystemExit(main())
