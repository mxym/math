#!/usr/bin/env python3
"""Fail-closed production-entry controls in normal and optimized Python; no Lean build."""
from pathlib import Path
import argparse,gzip,io,json,os,subprocess,sys,tarfile,tempfile
sys.dont_write_bytecode=True
from release_integrity import validated_snapshot,require,ReleaseIntegrityError,ARCHIVE_PREFIX,SEAL_FILES,sha256,manifest_bytes,checksum_bytes
ROOT=Path(__file__).resolve().parents[1]
PROOF='project/lean/references/upstream/arithmetic-audit/ArithmeticSupplyWeakMain.lean'
REQUIRED='provenance/REQUIRED_PAYLOAD_SHA256.json'
def copy_snapshot(s,r):
    for n,b in s.items():p=r/n;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(b)
def jedit(r,n,f):
    p=r/n;x=json.loads(p.read_text());f(x);p.write_text(json.dumps(x,indent=2)+'\n')
def reseal(r):
    s={p.relative_to(r).as_posix():p.read_bytes() for p in r.rglob('*') if p.is_file() and p.relative_to(r).as_posix() not in SEAL_FILES};m=manifest_bytes(s);(r/'SOURCE_MANIFEST.json').write_bytes(m);h={n:sha256(b) for n,b in s.items()};h['SOURCE_MANIFEST.json']=sha256(m);(r/'SHA256SUMS').write_bytes(checksum_bytes(h))
def changed(r,n):
    p=r/n;p.write_bytes(p.read_bytes()+b'\n');reseal(r)
def coordinated(r):
    p=r/PROOF;p.write_bytes(p.read_bytes()+b'\n-- modified\n');h=sha256(p.read_bytes())
    for n in [REQUIRED,'provenance/ORIGINAL_SOURCE_SHA256.json']:jedit(r,n,lambda d:d.__setitem__(PROOF,h))
    reseal(r)
def cases():
    result={'baseline':(lambda r:None,True),'missing_manifest':(lambda r:(r/'SOURCE_MANIFEST.json').unlink(),False),'missing_checksums':(lambda r:(r/'SHA256SUMS').unlink(),False),'malformed_manifest':(lambda r:(r/'SOURCE_MANIFEST.json').write_text('{'),False),'duplicate_manifest_key':(lambda r:(r/'SOURCE_MANIFEST.json').write_text((r/'SOURCE_MANIFEST.json').read_text().replace('"format": 2,','"format": 2, "format": 2,',1)),False),'nonfinite_metadata':(lambda r:(r/'SOURCE_MANIFEST.json').write_text((r/'SOURCE_MANIFEST.json').read_text().replace('"format": 2','"format": NaN',1)),False),'unknown_metadata':(lambda r:jedit(r,'SOURCE_MANIFEST.json',lambda d:d.__setitem__('unknown',True)),False),'deep_metadata':(lambda r:(r/'SOURCE_MANIFEST.json').write_text('['*2000+']'*2000),False),'unsafe_manifest_path':(lambda r:jedit(r,'SOURCE_MANIFEST.json',lambda d:d['sha256'].__setitem__('../outside','0'*64)),False),'coordinated_proof_metadata':(coordinated,False),'missing_proof':(lambda r:(r/PROOF).unlink(),False),'unlisted_source':(lambda r:(r/'project/lean/Evil.lean').write_text('axiom bad : False\n'),False),'unlisted_directory':(lambda r:(r/'unlisted').mkdir(),False),'symlink':(lambda r:(r/'extra').symlink_to('README.md'),False),'proof_symlink':(lambda r:((r/PROOF).unlink(),(r/PROOF).symlink_to('ArithmeticSupplyRayBridge.lean')),False),'fifo':(lambda r:os.mkfifo(r/'nonregular'),False),'fake_runtime_dir':(lambda r:(r/'.git').symlink_to('project'),False),'helper_prevalidation_side_effect':(lambda r:(r/'scripts/source_inventory.py').write_text('from pathlib import Path\nPath(__file__).resolve().parents[1].joinpath("HELPER_EXECUTED").write_text("BAD")\n'),False)}
    for n in [PROOF,'project/lean/Entry002/Targets.lean','project/lean/lake-manifest.json',REQUIRED,'provenance/OWNED_SOURCES.json','provenance/CFT_MODULES.json','provenance/SOURCE_CLOSURE.json.gz','provenance/EXTERNAL_ARTIFACTS_REFERENCE.json.gz','provenance/TOOLCHAIN_FILES_SHA256.json','provenance/PUBLIC_DERIVATIVE_LEDGER.json','audit/checks/ReplayLiteralMain.lean','audit/independent/FINAL_MATH_RESULT.json','project/lean/references/upstream/ClassFieldTheory/LICENSE','scripts/verify.py','README.md']:
        result['outer_rehashed_'+n]=(lambda r,n=n:changed(r,n),False)
    return result

def execute(root,name,opt,args):return subprocess.run([sys.executable,*(['-O'] if opt else []),'-B',str(root/'scripts'/(name+'.py')),*args],text=True,capture_output=True)
def seals(r):return {n:(r/n).read_bytes() if (r/n).exists() else None for n in SEAL_FILES}
def check_archive(p,s):
    data=p.read_bytes();require(data[:4]==b'\x1f\x8b\x08\x00' and data[4:8]==b'\0'*4,'archive gzip metadata differs')
    with tarfile.open(fileobj=io.BytesIO(data),mode='r:gz') as z:
        members=z.getmembers();require([m.name for m in members]==[ARCHIVE_PREFIX+'/'+n for n in sorted(s)],'archive inventory differs')
        for m,(n,b) in zip(members,sorted(s.items())):require(m.isfile() and m.mode==0o644 and m.uid==m.gid==m.mtime==0 and not m.uname and not m.gname and z.extractfile(m).read()==b,'archive byte/metadata differs: '+n)
def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--output',type=Path,required=True);a=ap.parse_args();require(not a.output.resolve().is_relative_to(ROOT),'report outside release required');s=validated_snapshot(ROOT);rows=[];allcases=cases()
    for case,(mutate,accept) in allcases.items():
        with tempfile.TemporaryDirectory(prefix='quadratic-guard-') as td:
            w=Path(td);r=w/'source';copy_snapshot(s,r);mutate(r);before=seals(r)
            for opt in [False,True]:
                for entry in ['verify_integrity','make_archive','verify','bootstrap']:
                    output=w/(entry+str(opt)+'.tar.gz');build=w/(entry+str(opt)+'-run');args=[]
                    if entry=='make_archive':args=['--output',str(output)]
                    if entry in {'verify','bootstrap'}:args=['--lean-bin',str(w/'MISSING'),'--dependency-project',str(w/'MISSING'),'--output',str(build)]
                    p=execute(r,entry,opt,args);text=p.stdout+p.stderr
                    if accept:
                        good=p.returncode==0
                        if entry in {'verify','bootstrap'}:good=p.returncode!=0 and 'exact Lean binary missing' in text and not build.exists()
                        if entry=='make_archive' and good:check_archive(output,s)
                    else:good=p.returncode!=0 and 'RELEASE_INTEGRITY:' in text and not output.exists() and not build.exists()
                    require(good,'guard control failed '+case+' '+entry+' '+str(opt)+'\n'+text);require(seals(r)==before and not (r/'HELPER_EXECUTED').exists(),'entry changed seal or executed unchecked helper');rows.append({'case':case,'entry':entry,'optimized':opt,'passed':True})
    for opt in [False,True]:
        for case in ['already_sealed','valid_unsealed','mutated_unsealed']:
            with tempfile.TemporaryDirectory(prefix='quadratic-seal-') as td:
                r=Path(td)/'source';copy_snapshot(s,r)
                if case!='already_sealed':
                    for n in SEAL_FILES:(r/n).unlink()
                if case=='mutated_unsealed':(r/PROOF).write_bytes((r/PROOF).read_bytes()+b'\n')
                before=seals(r);p=execute(r,'seal_release',opt,['--initialize'])
                require((p.returncode==0 and seals(r)=={n:s[n] for n in SEAL_FILES}) if case=='valid_unsealed' else (p.returncode!=0 and seals(r)==before),'one-time seal control failed '+case);rows.append({'case':case,'entry':'seal_release','optimized':opt,'passed':True})
    with tempfile.TemporaryDirectory(prefix='quadratic-archive-') as td:
        w=Path(td);r=w/'source';copy_snapshot(s,r);archives=[]
        for i,opt in enumerate([False,True]):
            for n in s:os.utime(r/n,(1000000000+i,1000000000+i))
            p=w/(str(i)+'.tar.gz');result=execute(r,'make_archive',opt,['--output',str(p)]);require(result.returncode==0,'archive run failed');check_archive(p,s);archives.append(p.read_bytes())
        require(archives[0]==archives[1],'archive not deterministic');fresh=w/'fresh'
        with tarfile.open(fileobj=io.BytesIO(archives[0]),mode='r:gz') as z:
            for m in z.getmembers():p=fresh/m.name;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(z.extractfile(m).read())
        for opt in [False,True]:require(execute(fresh/ARCHIVE_PREFIX,'verify_integrity',opt,[]).returncode==0,'fresh archive copy fails integrity')
        target=w/'keep';target.write_bytes(b'keep');link=w/'link.tar.gz';link.symlink_to(target)
        for opt in [False,True]:
            for p in [r/'inside.tar.gz',link]:require(execute(r,'make_archive',opt,['--output',str(p)]).returncode!=0,'unsafe archive target accepted')
        require(target.read_bytes()==b'keep' and not (r/'inside.tar.gz').exists(),'unsafe archive target altered')
    require(validated_snapshot(ROOT)==s,'package changed during controls');save={'status':'PASS','scope':'Packaging/production-entry integrity only; no Lean theorem claim','cases':len(allcases),'recorded_invocations':len(rows),'normal_and_optimized':True,'archive_deterministic':True,'fresh_extract_integrity':True,'no_Lean_build_or_network':True,'results':rows};a.output.write_text(json.dumps(save,indent=2)+'\n');print('PACKAGING_GUARD_CONTROLS_PASS',len(rows))
if __name__=='__main__':
    try:main()
    except (ReleaseIntegrityError,OSError,ValueError) as e:print(str(e),file=sys.stderr);sys.exit(1)
