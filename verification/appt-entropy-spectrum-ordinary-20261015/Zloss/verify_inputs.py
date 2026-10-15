from pathlib import Path
import hashlib,json,datetime
R=Path(__file__).resolve().parent; S=R/'owner-snapshot/zero-order-all-path-losses-20261015'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(S/'PAPER.md')=='5b1fa3732ec3dd2448e0cf5c54a79e321b08928aeaf9c7fbd6bd6f61e56c2602'
assert sha(S/'AUTHOR_V1_MANIFEST.json')=='9b9a598a79fba70f1ae10a8a094a4651d5fb9b54ee9b589dd772dbf6ff6a367e'
m=json.loads((S/'AUTHOR_V1_MANIFEST.json').read_text())
rows=[]
for rel,h in m['files'].items():
    p=S/rel;assert p.is_file() and sha(p)==h,rel
    rows.append({'path':rel,'sha256':h,'bytes':p.stat().st_size})
files={p.relative_to(S).as_posix() for p in S.rglob('*') if p.is_file()}
extra=files-set(m['files'])
assert extra=={'AUTHOR_V1_MANIFEST.json'},sorted(extra)
c=json.loads((S/'CREDITED_INPUTS.json').read_text())
reuse=[]
prior=R.parent/'independent-sublinear-rigidity-review-20261015/owner-snapshot/worktree/research/breadth-tcs-20261015/phase-5-sublinear-rigidity/credited-inputs'
for rel,rec in c['files'].items():
    p=S/'credited-inputs'/rel
    assert sha(p)==rec['sha256'] and p.stat().st_size==rec['bytes'],rel
    if (prior/rel).is_file():
        assert p.read_bytes()==(prior/rel).read_bytes(),rel
        reuse.append({'path':rel,'sha256':sha(p),'prior_full_read_copy':str(prior/rel)})
author=json.loads((S/'control-runs/20261015T141023.802089Z/RESULT.json').read_text())
for rel,h in author['source_hashes'].items(): assert sha(S/rel)==h,rel
result={'status':'PASS','utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
 'method':'Own literal byte/hash checks only; no author program execution',
 'manifest_listed':len(rows),'total_owner_files':len(files),'extra_manifest_only':sorted(extra),
 'credited_inputs':len(c['files']),'byte_equal_prior_full_scientific_reads':reuse,
 'paper_sha256':sha(S/'PAPER.md'),'manifest_sha256':sha(S/'AUTHOR_V1_MANIFEST.json'),
 'owner_zip_sha256':sha(R/'owner.zip'),'listed_files':rows,
 'outside_zip_receipt':'Not part of ZIP snapshot; no assertion of inclusion',
 'author_control_sourcehash_verified':True,'author_control_executed':False}
(R/'INPUT_VERIFICATION.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items() if k not in ['listed_files','byte_equal_prior_full_scientific_reads']},indent=2))
