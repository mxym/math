from pathlib import Path, PurePosixPath
from datetime import datetime, timezone
import hashlib,json,shutil,zipfile

R=Path(__file__).resolve().parent
src=Path('/mnt/d/math/tmp/research-resume-20261015/all-dimension-diverging-spectral-owner-v1-20261015T153225Z.zip')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(src)=='06b892c0fc87cbd74ecfddcf2538d4e98d1687ab1117c1756610516c6e40cb2c'
assert not (R/'owner.zip').exists() and not (R/'owner-snapshot').exists()
shutil.copyfile(src,R/'owner.zip')
with zipfile.ZipFile(R/'owner.zip') as z:
    for name in z.namelist():
        p=PurePosixPath(name)
        assert not p.is_absolute() and '..' not in p.parts and ':' not in name and '\\' not in name,name
    z.extractall(R/'owner-snapshot')
papers=[p for p in (R/'owner-snapshot').rglob('PAPER.md') if sha(p)=='75f5d9226c447c8acb4c6e609ac805e57a399a2a0dbfbaf8a3047bd5c22748e9']
assert len(papers)==1
S=papers[0].parent
assert sha(S/'AUTHOR_V1_MANIFEST.json')=='44a14627b4e90cdd959b60c68019a2a878289662eb03dd0cf6058cadb1b64cc9'
manifest=json.loads((S/'AUTHOR_V1_MANIFEST.json').read_text())
rows=manifest['files']
for row in rows:
    p=S/row['path']
    assert p.is_file() and sha(p)==row['sha256'] and p.stat().st_size==row['bytes'],row
actual={p.relative_to(S).as_posix() for p in S.rglob('*') if p.is_file()}
assert actual=={r['path'] for r in rows}|{'AUTHOR_V1_MANIFEST.json'}
out={'status':'CAPTURED_NOT_REVIEWED','utc':datetime.now(timezone.utc).isoformat(),
     'owner_zip_sha256':sha(R/'owner.zip'),'source_relative_to_review':S.relative_to(R).as_posix(),
     'manifest_sha256':sha(S/'AUTHOR_V1_MANIFEST.json'),'paper_sha256':sha(S/'PAPER.md'),
     'file_count':len(actual),'files':rows,'author_code_executed':False}
(R/'INITIAL_CAPTURE.json').write_text(json.dumps(out,ensure_ascii=False,indent=2)+'\n')
print(json.dumps({k:v for k,v in out.items() if k!='files'},indent=2))
print(json.dumps({'files':[r['path'] for r in rows]},indent=2))
