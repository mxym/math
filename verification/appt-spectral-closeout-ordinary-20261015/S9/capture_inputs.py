from pathlib import Path,PurePosixPath
import hashlib,json,datetime,shutil,zipfile
R=Path(__file__).resolve().parent
z=Path('/mnt/d/math/tmp/breadth-tcs-20261015/phase-9-diverging-physical-reduction/diverging-reduction-owner-20261015T142136Z.zip')
assert hashlib.sha256(z.read_bytes()).hexdigest()=='33f3d58c6a47b0009146ce4e6e25bb65892cd1c52731e58499adf2690dc25cb9'
assert not (R/'owner.zip').exists()
shutil.copyfile(z,R/'owner.zip')
with zipfile.ZipFile(R/'owner.zip') as f:
    for name in f.namelist():
        p=PurePosixPath(name)
        assert not p.is_absolute() and '..' not in p.parts and ':' not in name and '\\' not in name,name
    f.extractall(R/'owner-snapshot');names=f.namelist()
(R/'INITIAL_CAPTURE.json').write_text(json.dumps({'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
 'owner_zip_sha256':hashlib.sha256(z.read_bytes()).hexdigest(),'members':names,
 'method':'Independent private capture; no author producer or control executed'},indent=2)+'\n')
print(json.dumps({'files':len(names),'papers':[str(p) for p in (R/'owner-snapshot').rglob('PAPER.md')]},indent=2))
