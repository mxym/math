from pathlib import Path,PurePosixPath
import hashlib,json,datetime,zipfile,shutil
R=Path(__file__).resolve().parent
z=Path('/mnt/d/math/tmp/breadth-tcs-20261015/phase-7-rectangular-bulk-rigidity/bulk-rigidity-owner-20261015T135207Z.zip')
assert hashlib.sha256(z.read_bytes()).hexdigest()=='d950887d05101bdb90dd848175ff5a5b527793f9443c2310d398f8e883e69860'
assert not (R/'owner.zip').exists()
shutil.copyfile(z,R/'owner.zip')
with zipfile.ZipFile(R/'owner.zip') as f:
    for name in f.namelist():
        p=PurePosixPath(name)
        assert not p.is_absolute() and '..' not in p.parts and ':' not in name and '\\' not in name,name
    f.extractall(R/'owner-snapshot');names=f.namelist()
(R/'INITIAL_CAPTURE.json').write_text(json.dumps({'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
 'owner_zip_sha256':hashlib.sha256(z.read_bytes()).hexdigest(),'members':names,
 'method':'Private copied ZIP and safe extraction; no author program execution'},indent=2)+'\n')
print(json.dumps({'members':len(names),'paper':[str(p) for p in (R/'owner-snapshot').rglob('PAPER.md')]},indent=2))
