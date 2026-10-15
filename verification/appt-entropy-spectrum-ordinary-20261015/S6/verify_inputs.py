"""Independent byte verification; does not execute author code or math controls."""
from pathlib import Path
import hashlib, json, datetime

ROOT = Path(__file__).resolve().parent
SRC = ROOT / 'owner-snapshot/worktree/research/breadth-tcs-20261015/phase-6-growing-peak-rigidity'
OLD = ROOT.parent / 'independent-sublinear-rigidity-review-20261015/owner-snapshot/worktree/research/breadth-tcs-20261015/phase-5-sublinear-rigidity'
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
manifest = json.loads((SRC/'AUTHOR_V1_MANIFEST.json').read_text())
assert sha(ROOT/'owner.zip') == '4cf416671bacc623e24492d95769e22f75fdf3822c3b172a37cd4c35f24e6803'
assert sha(SRC/'PAPER.md') == '2374564f1f2cd3c576c3528d8acfda3f9a729ae08f506621f930ed42b33fd227'
assert sha(SRC/'AUTHOR_V1_MANIFEST.json') == 'c3ac74c2808473892a46302a934a59fa0dc9d9063b4e77ab7b386fa264086b1e'
rows=[]
for item in manifest['files']:
    p=SRC/item['path']
    assert p.is_file(), item['path']
    assert p.stat().st_size == item['bytes'], item['path']
    assert sha(p) == item['sha256'], item['path']
    row=dict(item)
    if item['path'].startswith('credited-inputs/'):
        prev=OLD/item['path']
        assert prev.is_file(), str(prev)
        assert p.read_bytes() == prev.read_bytes(), item['path']
        row['prior_full_read_copy']=str(prev)
        row['read_reuse']='Literal equality to scientific text fully read in separate S5 review; no reuse of its new theorem decision'
    rows.append(row)
expected={x['path'] for x in rows}|{'AUTHOR_V1_MANIFEST.json'}
actual={p.relative_to(SRC).as_posix() for p in SRC.rglob('*') if p.is_file()}
assert actual == expected, (sorted(actual-expected),sorted(expected-actual))
res={'status':'PASS','utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
     'method':'Byte/hash verification and prior scientific-text equality only; no execution of author programs',
     'owner_zip_sha256':sha(ROOT/'owner.zip'),'manifest_sha256':sha(SRC/'AUTHOR_V1_MANIFEST.json'),
     'listed_files':len(rows),'total_source_files':len(actual),
     'prior_full_read_identical_scientific_texts':sum('prior_full_read_copy' in x for x in rows),'files':rows}
(ROOT/'INPUT_VERIFICATION.json').write_text(json.dumps(res,indent=2)+'\n')
print(json.dumps({k:v for k,v in res.items() if k!='files'},indent=2))
