#!/usr/bin/env python3
"""Independent final-copy byte/provenance and small hostile entrypoint audit."""
from pathlib import Path, PurePosixPath
import os, sys, json, hashlib, tarfile, zipfile, gzip, subprocess, tempfile, shutil, re, ast
BASE=Path(__file__).resolve().parent.parent
OUT=Path(__file__).resolve().parent
ROOT=BASE/'final_copy/formalizations/continuum-remainder-avoidance'
OLD=BASE.parent/'lean_continuum_remainder_independent_audit_20261007'
ARCHIVE=BASE/'continuum-remainder-avoidance-source-20261007.tar.gz'
PIN='f41b75d9ff67884e6fa84a35b952364df9348d0742b4f3a8e8ffba52b4a61e40'
PREFIX='formalizations/continuum-remainder-avoidance/'
def need(v,m):
 if not v: raise RuntimeError(m)
def sha(b): return hashlib.sha256(b).hexdigest()
def filehash(p): return sha(p.read_bytes())
def save(p,x): p.write_text(json.dumps(x,indent=2,ensure_ascii=False)+'\n')
report={'status':'RUNNING','archive_sha256':filehash(ARCHIVE),'archive_bytes':ARCHIVE.stat().st_size}
need(report['archive_sha256']==PIN and report['archive_bytes']==4347676,'archive anchor')
manifest=json.loads((ROOT/'SOURCE_MANIFEST.json').read_text())
expected=set(manifest['sha256'])|{'SOURCE_MANIFEST.json','SHA256SUMS'}
with tarfile.open(ARCHIVE,'r:gz') as z:
 members=z.getmembers();names=[m.name for m in members]
 need(len(members)==278 and len(set(names))==278,'archive count or duplicate')
 contents={}
 for m in members:
  need(m.isfile() and not m.issym() and not m.islnk(),'nonregular member')
  need(not m.pax_headers or m.pax_headers=={'path':m.name},'unexpected pax metadata')
  need(m.name.startswith(PREFIX),'archive prefix')
  n=m.name[len(PREFIX):];p=PurePosixPath(n)
  need(n and not p.is_absolute() and all(x not in ('','..','.') for x in n.split('/')) and '\\' not in n and not any(ord(c)<32 for c in n),'unsafe path')
  need(m.mode==0o644 and m.uid==m.gid==m.mtime==0 and m.uname==m.gname=='','archive metadata')
  b=z.extractfile(m).read();need(b==(ROOT/n).read_bytes(),'archive/final-copy mismatch '+n);contents[n]=b
 need(set(contents)==expected,'tar payload inventory')
report['archive_members_safe_and_final_copy_equal']=len(contents)
with zipfile.ZipFile(OLD/'incoming/prescribed-family-continuum-remainder-lean.zip') as z:
 need(filehash(OLD/'incoming/prescribed-family-continuum-remainder-lean.zip')=='b8fb480b8888321b864cf3c58a81cad3dfc223cc837071b940be58a93cca0e51','original archive')
 # The original archive uses its own fixed top-level directory.
 original={n[n.index('project/'):]:z.read(n) for n in z.namelist() if 'project/' in n and not n.endswith('/')}
 lean=[n for n in original if n.endswith('.lean')]
 need(len(lean)==110,'original Lean count')
 for n in lean+['project/lean-toolchain','project/lakefile.toml','project/lake-manifest.json','project/PublicTheorems.json']:
  need(contents[n]==original[n],'original source changed '+n)
report['submitted_project_lean_files_identical']=110
report['pinned_project_configuration_files_identical']=4
ledger=json.loads((ROOT/'provenance/PUBLIC_DERIVATIVE_LEDGER.json').read_text())
audit_rows=[]
for row in ledger:
 if row['origin'].startswith('independent-audit:'):
  original=OLD/row['origin'].split(':',1)[1];public=ROOT/row['public']
  need(filehash(original)==row['original_sha256'] and filehash(public)==row['public_sha256'],'independent audit ledger anchor')
  if row['change']=='byte-identical':need(original.read_bytes()==public.read_bytes(),'byte identity ledger')
  if public.suffix=='.gz':need(gzip.decompress(public.read_bytes())==original.read_bytes(),'compressed identity')
  audit_rows.append(row['public'])
report['independent_audit_origin_and_derivative_hashes_verified']=len(audit_rows)
report['root_document_links_checked']=0
for p in ROOT.glob('*.md'):
 for link in re.findall(r'\]\(([^)]+)\)',p.read_text()):
  if not re.match('[a-z]+:',link):
   need((p.parent/link.split('#')[0]).exists(),'broken document link '+link)
   report['root_document_links_checked']+=1
for p in (ROOT/'scripts').glob('*.py'):
 need(not any(isinstance(n,ast.Assert) for n in ast.walk(ast.parse(p.read_text()))),'optimization-sensitive assert '+p.name)
report['release_scripts_assertion_free']=True
# Independent cases, separate from the package author's test matrix.
controls=[]
with tempfile.TemporaryDirectory(prefix='small-hostile-',dir=OUT) as temporary:
 t=Path(temporary);copy=t/'package';copy.mkdir()
 for n,b in contents.items():
  p=copy/n;p.parent.mkdir(exist_ok=True,parents=True);p.write_bytes(b)
 fake=t/'fake-bin';fake.mkdir();marker=t/'EXECUTED';(fake/'lean').write_text('#!/bin/sh\ntouch "'+str(marker)+'"\n');(fake/'lean').chmod(0o755)
 def run(script,mode,args=[]):
  cmd=[sys.executable]+(['-O'] if mode else [])+[str(copy/'scripts'/script)]+list(map(str,args))
  r=subprocess.run(cmd,text=True,capture_output=True,timeout=40,env={**os.environ,'PYTHONDONTWRITEBYTECODE':'1'})
  return r
 def check_bad(case):
  for mode in [False,True]:
   for script in ['verify_integrity.py','make_archive.py','verify.py']:
    target=t/'output.tar.gz';target.write_bytes(b'UNTOUCHED_SENTINEL')
    build=t/'must-not-exist'
    args=['--output',target] if script=='make_archive.py' else ['--lean-bin',fake,'--dependency-project',t/'missing-deps','--output',build] if script=='verify.py' else []
    before={n:(copy/n).read_bytes() for n in ['SOURCE_MANIFEST.json','SHA256SUMS'] if (copy/n).is_file()}
    r=run(script,mode,args)
    need(r.returncode!=0 and 'RELEASE_INTEGRITY:' in r.stdout+r.stderr,'did not fail closed '+case+' '+script)
    need(target.read_bytes()==b'UNTOUCHED_SENTINEL' and not build.exists() and not marker.exists(),'failure mutated output or executed Lean')
    for n,b in before.items():need((copy/n).read_bytes()==b,'silently resealed '+case)
    controls.append({'case':case,'python_optimized':mode,'entrypoint':script,'returncode':r.returncode,'rejected_before_Lean_or_output':True})
 def reseal_outer():
  m=json.loads((copy/'SOURCE_MANIFEST.json').read_text());m['sha256']={n:filehash(copy/n) for n in m['sha256']};(copy/'SOURCE_MANIFEST.json').write_text(json.dumps(m,indent=2)+'\n')
  h=dict(m['sha256']);h['SOURCE_MANIFEST.json']=filehash(copy/'SOURCE_MANIFEST.json');(copy/'SHA256SUMS').write_text(''.join(v+'  '+k+'\n' for k,v in sorted(h.items())))
 for mode in [False,True]:
  r=run('verify_integrity.py',mode);need(r.returncode==0 and '278 frozen files' in r.stdout,'clean verification')
  r=run('make_archive.py',mode,['--output',t/('normal.tar.gz' if not mode else 'optimized.tar.gz')]);need(r.returncode==0,'clean archive')
  need(filehash(t/('normal.tar.gz' if not mode else 'optimized.tar.gz'))==PIN,'deterministic archive')
  r=run('seal_release.py',mode,['--initialize']);need(r.returncode!=0 and 'refusing to reseal' in r.stderr,'reseal allowed')
  r=run('verify.py',mode,['--lean-bin',fake,'--dependency-project',t/'missing-deps','--output',t/'must-not-exist'])
  need(r.returncode!=0 and 'Lean executable hash differs' in r.stderr and not marker.exists(),'fake Lean reached execution')
 cases=['changed_readme','forged_outer_seal_proof','forged_outer_seal_audit','forged_outer_seal_license','duplicate_json_key','unsafe_manifest_path','unexpected_directory','extra_payload_file','payload_symlink','runtime_root_symlink','payload_fifo','missing_replayer']
 for case in cases:
  restore={};added=[]
  def replace(n,b):
   p=copy/n;restore[n]=p.read_bytes();p.write_bytes(b)
  if case=='changed_readme':replace('README.md',b'Changed description.\n')
  elif case.startswith('forged_outer_seal_'):
   n={'proof':'project/ContinuumRemainder/FinalProof.lean','audit':'audit/checks/ReplayAllSafeOwned.lean','license':'third_party_licenses/mathlib/LICENSE'}[case.rsplit('_',1)[1]]
   replace(n,(copy/n).read_bytes()+b'\n')
   for n in ['SOURCE_MANIFEST.json','SHA256SUMS']:restore[n]=(copy/n).read_bytes()
   reseal_outer()
  elif case=='duplicate_json_key':replace('SOURCE_MANIFEST.json',b'{"format":2,'+(copy/'SOURCE_MANIFEST.json').read_bytes()[1:])
  elif case=='unsafe_manifest_path':
   m=json.loads((copy/'SOURCE_MANIFEST.json').read_text());m['sha256']['../outside']='0'*64;replace('SOURCE_MANIFEST.json',(json.dumps(m)+'\n').encode())
  elif case=='unexpected_directory':(copy/'surprise').mkdir();added.append('surprise')
  elif case=='extra_payload_file':(copy/'unexpected.lean').write_text('axiom fake : False\n');added.append('unexpected.lean')
  elif case=='runtime_root_symlink':(copy/'vendor').symlink_to(t,target_is_directory=True);added.append('vendor')
  else:
   n='audit/checks/ReplayClosure.lean';restore[n]=(copy/n).read_bytes();(copy/n).unlink()
   if case=='payload_symlink':(copy/n).symlink_to(ROOT/n)
   elif case=='payload_fifo':os.mkfifo(copy/n)
  check_bad(case)
  for n,b in restore.items():
   p=copy/n
   if p.exists() or p.is_symlink():p.unlink()
   p.write_bytes(b)
  for n in added:
   p=copy/n
   if p.is_dir() and not p.is_symlink():p.rmdir()
   else:p.unlink()
 # Declared runtime exclusions are permitted, but never included in the archive.
 (copy/'vendor').mkdir();(copy/'vendor/ignored').write_text('not distributed')
 for mode in [False,True]:
  need(run('verify_integrity.py',mode).returncode==0,'real runtime directory failed')
  r=run('make_archive.py',mode,['--output',t/'excluded.tar.gz']);need(r.returncode==0 and filehash(t/'excluded.tar.gz')==PIN,'runtime data archived')
report['independent_hostile_entrypoint_checks']=len(controls)
report['hostile_controls']=controls
report['normal_and_optimized_archive_identity']=True
report['existing_seal_reinitialization_rejected_both_modes']=True
report['unpinned_lean_rejected_before_execution_both_modes']=True
report['runtime_directory_excluded_both_modes']=True
report['status']='PASS'
save(OUT/'INDEPENDENT_FINAL_COPY_CHECKS.json',report)
print(json.dumps({k:v for k,v in report.items() if k!='hostile_controls'},indent=2))
