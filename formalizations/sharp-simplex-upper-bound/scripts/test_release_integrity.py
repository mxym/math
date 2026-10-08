#!/usr/bin/env python3
"""Production-entry hostile controls. No Lean, dependencies or network executed."""
from pathlib import Path
import argparse,gzip,hashlib,io,json,os,subprocess,sys,tarfile,tempfile
sys.dont_write_bytecode=True
from release_integrity import (validated_snapshot,require,ReleaseIntegrityError,ARCHIVE_PREFIX,METADATA,SEAL_FILES,sha256,manifest_bytes,checksum_bytes)
ROOT=Path(__file__).resolve().parents[1]
PROOF='project/formal/Entry005/SharpUpperMain.lean'
PIN='project/formal/lake-manifest.json'
INVENTORY='provenance/REQUIRED_PAYLOAD_SHA256.json'
def change(root,name,fn):
 p=root/name;p.write_text(fn(p.read_text()))
def jchange(root,name,fn):
 p=root/name;x=json.loads(p.read_text());fn(x);p.write_text(json.dumps(x,indent=2)+'\n')
def reseal(root):
 files={str(p.relative_to(root)):p.read_bytes() for p in root.rglob('*') if p.is_file() and str(p.relative_to(root)) not in SEAL_FILES}
 m=manifest_bytes(files);(root/'SOURCE_MANIFEST.json').write_bytes(m)
 hashes={n:sha256(b) for n,b in files.items()};hashes['SOURCE_MANIFEST.json']=sha256(m)
 (root/'SHA256SUMS').write_bytes(checksum_bytes(hashes))
def rehash(root,name):change(root,name,lambda t:t+'\n');reseal(root)
def erase(root,name):
 (root/name).unlink();reseal(root)
def coordinated(root):
 change(root,PROOF,lambda t:t+'\n-- changed\n');h=sha256((root/PROOF).read_bytes())
 for n in [INVENTORY,'provenance/ORIGINAL_SOURCE_SHA256.json']:jchange(root,n,lambda x:x.__setitem__(PROOF,h))
 reseal(root)
def cases():
 c={'baseline':(lambda _:None,True),'missing_manifest':(lambda r:(r/'SOURCE_MANIFEST.json').unlink(),False),'missing_checksums':(lambda r:(r/'SHA256SUMS').unlink(),False),
 'malformed_manifest':(lambda r:(r/'SOURCE_MANIFEST.json').write_text('{'),False),'deep_manifest':(lambda r:(r/'SOURCE_MANIFEST.json').write_text('['*2000+']'*2000),False),
 'duplicate_key':(lambda r:change(r,'SOURCE_MANIFEST.json',lambda t:t.replace('"format": 2,','"format": 2, "format": 2,',1)),False),
 'nonfinite':(lambda r:change(r,'SOURCE_MANIFEST.json',lambda t:t.replace('"format": 2','"format": NaN',1)),False),
 'boolean_format':(lambda r:jchange(r,'SOURCE_MANIFEST.json',lambda x:x.__setitem__('format',True)),False),
 'unknown_metadata':(lambda r:jchange(r,'SOURCE_MANIFEST.json',lambda x:x.__setitem__('extra',1)),False),
 'omitted_checksum':(lambda r:change(r,'SHA256SUMS',lambda t:''.join(t.splitlines(True)[1:])),False),
 'duplicate_checksum':(lambda r:change(r,'SHA256SUMS',lambda t:t+t.splitlines(True)[0]),False),
 'reordered_checksum':(lambda r:change(r,'SHA256SUMS',lambda t:''.join(reversed(t.splitlines(True)))),False),
 'unlisted_source':(lambda r:(r/'project/formal/Unlisted.lean').write_text('import Mathlib\n'),False),
 'unlisted_empty_directory':(lambda r:(r/'unlisted').mkdir(),False),
 'nested_fake_cache':(lambda r:(r/'project/formal/.lake').mkdir(),False),
 'file_symlink':(lambda r:((r/PROOF).unlink(),(r/PROOF).symlink_to('Targets.lean')),False),
 'unlisted_symlink':(lambda r:(r/'unlisted').symlink_to('README.md'),False),
 'fifo':(lambda r:os.mkfifo(r/'fifo'),False),
 'runtime_symlink':(lambda r:(r/'.git').symlink_to('project'),False),
 'runtime_file':(lambda r:(r/'.git').write_text('bad'),False),
 'helper_prevalidation_side_effect':(lambda r:change(r,'scripts/source_inventory.py',lambda t:'from pathlib import Path\nPath(__file__).resolve().parents[1].joinpath(\"HELPER_EXECUTED\").write_text(\"BAD\")\n'+t),False),
 'coordinated_proof_and_provenance_rewrite':(coordinated,False)}
 for name in [PROOF,PIN,'project/formal/Entry005/Targets.lean','project/formal/Entry005/Constants.lean','project/formal/Entry005/MainTarget.lean','project/formal/Entry005/SelectedAnchorHullRoundness.lean','project/evidence/source-manifest.json',INVENTORY,'provenance/ORIGINAL_SOURCE_SHA256.json','provenance/PUBLIC_DERIVATIVE_LEDGER.json','provenance/INPUT_COMPOSITION.json','provenance/TOOLCHAIN_FILES_SHA256.json','provenance/EXTERNAL_ARTIFACTS_REFERENCE.json.gz','provenance/DEPENDENCY_PROVENANCE.json','README.md','THEOREM.md','VERIFICATION.md','audit/checks/ReplayAllSafeOwned.lean','audit/checks/ReplayLiteralMain.lean','audit/independent/FINAL_PASS.json','third_party_licenses/openai_math_LICENSE.txt','scripts/verify.py','scripts/bootstrap.py','project/scripts/replay_upper_main.py']:
  c['outer_rehashed_'+name]=(lambda r,n=name:((r/n).write_bytes((r/n).read_bytes()+b'\n'),reseal(r)),False)
  c['missing_required_'+name]=(lambda r,n=name:erase(r,n),False)
 for key in METADATA:
  c['metadata_missing_'+key]=(lambda r,k=key:jchange(r,'SOURCE_MANIFEST.json',lambda x:x.pop(k)),False)
  c['metadata_changed_'+key]=(lambda r,k=key:jchange(r,'SOURCE_MANIFEST.json',lambda x:x.__setitem__(k,'incorrect')),False)
 for name in ['../outside','/outside','project//bad','project/../bad','project/./bad','project\\bad','line\nname']:
  c['unsafe_path_'+repr(name)]=(lambda r,n=name:jchange(r,'SOURCE_MANIFEST.json',lambda x:x['sha256'].__setitem__(n,'0'*64)),False)
 return c

def copy_snapshot(s,r):
 for n,b in s.items():p=r/n;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(b)
def seals(r):return {n:(r/n).read_bytes() if (r/n).exists() else None for n in SEAL_FILES}
def execute(r,entry,opt,args):return subprocess.run([sys.executable,*(['-O'] if opt else []),'-B',str(r/'scripts'/(entry+'.py')),*args],text=True,capture_output=True)
def check_archive(p,s):
 raw=p.read_bytes();require(raw[:4]==b'\x1f\x8b\x08\x00' and raw[4:8]==b'\0'*4,'gzip header not deterministic')
 with tarfile.open(fileobj=io.BytesIO(raw),mode='r:gz') as z:
  members=z.getmembers();require([m.name for m in members]==[ARCHIVE_PREFIX+'/'+n for n in sorted(s)],'archive inventory differs')
  for m,(n,b) in zip(members,sorted(s.items())):
   require(m.isfile() and m.mode==0o644 and m.mtime==m.uid==m.gid==0 and m.uname==m.gname=='','archive metadata differs')
   require(z.extractfile(m).read()==b,'archive bytes differ')
def main():
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--output',type=Path,required=True);a=ap.parse_args();require(not a.output.resolve().is_relative_to(ROOT),'write report outside release')
 s=validated_snapshot(ROOT);rows=[];cs=cases()
 for name,(mutate,accept) in cs.items():
  with tempfile.TemporaryDirectory(prefix='upper-main-guard-') as td:
   w=Path(td);r=w/'source';copy_snapshot(s,r);mutate(r);before=seals(r)
   for opt in (False,True):
    for entry in ['verify_integrity','make_archive','verify','bootstrap']:
     if not (r/'scripts'/(entry+'.py')).exists() or (accept and entry=='bootstrap'):continue
     output=w/(entry+('-O' if opt else '')+'.tar.gz');build=w/(entry+'-output'+str(opt))
     args=[] if entry=='verify_integrity' else ['--output',str(output)]
     if entry=='verify':args=['--lean-bin',str(w/'MISSING'),'--dependency-project',str(w/'MISSING'),'--output',str(build)]
     if entry=='bootstrap':args=['--work',str(build)]
     p=execute(r,entry,opt,args);log=p.stdout+p.stderr
     if accept:
      good=p.returncode==0
      if entry=='verify':good=p.returncode!=0 and 'install exact toolchain and use --lean-bin' in log and not build.exists()
      if entry=='make_archive' and good:check_archive(output,s)
     else:good=p.returncode!=0 and 'RELEASE_INTEGRITY:' in log and not output.exists() and not build.exists()
     require(good,'hostile control failed '+name+' '+entry+' '+str(opt)+'\n'+log)
     require(seals(r)==before,'production entry rewrote seals')
     require(not (r/'HELPER_EXECUTED').exists(),'unvalidated helper code executed')
     rows.append({'case':name,'entry':entry,'optimized':opt,'expected':'accept' if accept else 'reject_before_output','passed':True})
 for opt in (False,True):
  for kind in ['valid_unsealed','already_sealed','missing_inventory','mutated_proof']:
   with tempfile.TemporaryDirectory(prefix='upper-main-seal-') as td:
    r=Path(td)/'source';copy_snapshot(s,r)
    if kind!='already_sealed':
     for n in SEAL_FILES:(r/n).unlink()
    if kind=='missing_inventory':(r/INVENTORY).unlink()
    if kind=='mutated_proof':change(r,PROOF,lambda t:t+'\n')
    before=seals(r);p=execute(r,'seal_release',opt,['--initialize']);good=p.returncode==0 if kind=='valid_unsealed' else p.returncode!=0 and seals(r)==before
    require(good,'seal control failed '+kind)
    if kind=='valid_unsealed':require(seals(r)=={n:s[n] for n in SEAL_FILES},'nondeterministic initialization')
    rows.append({'case':kind,'entry':'seal_release','optimized':opt,'passed':True})
 with tempfile.TemporaryDirectory(prefix='upper-main-archive-') as td:
  w=Path(td);r=w/'source';copy_snapshot(s,r);archives=[]
  for i,opt in enumerate([False,False,True]):
   for n in s:os.utime(r/n,(1000000000+i,1000000000+i))
   f=w/(str(i)+'.tar.gz');p=execute(r,'make_archive',opt,['--output',str(f)]);require(p.returncode==0,'archive creation failed');check_archive(f,s);archives.append(f.read_bytes())
  require(archives[0]==archives[1]==archives[2],'archive determinism failure')
  fresh=w/'fresh'
  with tarfile.open(fileobj=io.BytesIO(archives[0]),mode='r:gz') as z:
   for m in z.getmembers():p=fresh/m.name;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(z.extractfile(m).read())
  for opt in [False,True]:require(execute(fresh/ARCHIVE_PREFIX,'verify_integrity',opt,[]).returncode==0,'fresh extraction failed integrity')
  target=w/'keep';target.write_bytes(b'keep');link=w/'linked.tar.gz';link.symlink_to(target)
  for opt in [False,True]:
   for f in [r/'forbidden.tar.gz',link]:require(execute(r,'make_archive',opt,['--output',str(f)]).returncode!=0,'unsafe output accepted')
  require(target.read_bytes()==b'keep' and not (r/'forbidden.tar.gz').exists(),'unsafe output mutated')
  (r/'SOURCE_MANIFEST.json').unlink()
  for opt in [False,True]:require(execute(r,'make_archive',opt,['--output',str(target)]).returncode!=0 and target.read_bytes()==b'keep','invalid package overwrote output')
 report={'status':'PASS','scope':'Packaging/entry-point integrity only; not a mathematical proof test','cases':len(cs),'recorded_production_invocations':len(rows),'normal_and_optimized':True,'archive_deterministic_and_fresh_extract_pass':True,'archive_metadata_and_all_member_bytes_checked':True,'source_immutable_before_build_bootstrap_or_archive':True,'no_lean_or_network_executed':True,'authenticity_boundary':'Validator plus all internal records can be rewritten together; externally authenticate the final archive digest or repository commit. Not a hostile-filesystem sandbox.','results':rows}
 a.output.write_text(json.dumps(report,indent=2)+'\n');print('PACKAGING_GUARD_CONTROLS_PASS '+str(len(rows))+' recorded production invocations')
if __name__=='__main__':
 try:main()
 except (ReleaseIntegrityError,OSError,ValueError) as e:print(str(e),file=sys.stderr);sys.exit(1)
