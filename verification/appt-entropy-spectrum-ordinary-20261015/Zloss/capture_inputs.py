from pathlib import Path,PurePosixPath
import hashlib,datetime,json,zipfile,shutil
R=Path(__file__).resolve().parent
z=Path('/mnt/d/math/tmp/research-resume-20261015/zero-order-all-path-losses-owner-v1-20261015T141509Z.zip')
assert hashlib.sha256(z.read_bytes()).hexdigest()=='612052d3a51ec4ce56be19c10f07f0169fcbc440fcc5b5ba7d615ce8dde8de77'
assert not (R/'owner.zip').exists()
shutil.copyfile(z,R/'owner.zip')
with zipfile.ZipFile(R/'owner.zip') as f:
    for name in f.namelist():
        p=PurePosixPath(name)
        assert not p.is_absolute() and '..' not in p.parts and ':' not in name and '\\' not in name,name
    f.extractall(R/'owner-snapshot')
    members=f.namelist()
(R/'INITIAL_CAPTURE.json').write_text(json.dumps({'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
    'source':str(z),'zip_sha256':hashlib.sha256(z.read_bytes()).hexdigest(),'members':members,
    'scope':'Read-only owner snapshot; no author program executed'},indent=2)+'\n')
print(json.dumps({'members':len(members),'paper_paths':[str(p) for p in (R/'owner-snapshot').rglob('PAPER.md')]},indent=2))
