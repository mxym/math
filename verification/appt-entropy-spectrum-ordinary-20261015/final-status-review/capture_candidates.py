from pathlib import Path
import hashlib,json,datetime,shutil
R=Path(__file__).resolve().parent
STAGE=Path('/mnt/d/math/tmp/research-resume-20261015/entropy-spectrum-publication')
S=R/'candidate-snapshot'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert not S.exists()
before={p.relative_to(STAGE).as_posix():{'sha256':sha(p),'bytes':p.stat().st_size}
        for p in sorted(STAGE.rglob('*')) if p.is_file()}
shutil.copytree(STAGE,S)
after={p.relative_to(STAGE).as_posix():{'sha256':sha(p),'bytes':p.stat().st_size}
       for p in sorted(STAGE.rglob('*')) if p.is_file()}
assert before==after,'Stage changed while copying'
for rel,x in before.items():
    p=S/rel;assert p.stat().st_size==x['bytes'] and sha(p)==x['sha256'],rel
out={'status':'PASS','utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
     'source_stage':str(STAGE),'snapshot_files':len(before),'files':before,
     'method':'Read-only private snapshot before independent metadata checks; no parent/author program executed'}
(R/'CANDIDATE_CAPTURE.json').write_text(json.dumps(out,indent=2)+'\n')
mf=json.loads((S/'FINAL_CANDIDATE_INPUTS.json').read_text())
print(json.dumps({'snapshot_files':len(before),'manifest_keys':{k:len(v) if isinstance(v,(dict,list)) else v for k,v in mf.items() if k!='files'},
                 'manifest_file_count':len(mf['files']),'first_files':list(mf['files'])[:3],'last_files':list(mf['files'])[-7:]},indent=2))
