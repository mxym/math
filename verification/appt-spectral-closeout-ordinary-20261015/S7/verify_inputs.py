from pathlib import Path
import hashlib,json,datetime
R=Path(__file__).resolve().parent
S=R/'owner-snapshot/worktree/research/breadth-tcs-20261015/phase-7-rectangular-bulk-rigidity'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(S/'PAPER.md')=='3701fa925c3c4098961c227768f62915e9cf388bdafea5918a638ce2b7963a9f'
assert (S/'PAPER.md').stat().st_size==18499
assert sha(S/'AUTHOR_V1_MANIFEST.json')=='5f8b902185ab001b23e54463bb4f831b3b03dc4aaf4d42f71fb4b3bcb8994d1c'
m=json.loads((S/'AUTHOR_V1_MANIFEST.json').read_text())
rows=[]
for x in m['files']:
    p=S/x['path']
    assert p.stat().st_size==x['bytes'] and sha(p)==x['sha256'],x['path']
    rows.append(x)
actual={p.relative_to(S).as_posix() for p in S.rglob('*') if p.is_file()}
assert actual=={x['path'] for x in rows}|{'AUTHOR_V1_MANIFEST.json'}
prior1=R.parent/'independent-sublinear-rigidity-review-20261015/owner-snapshot/worktree/research/breadth-tcs-20261015/phase-5-sublinear-rigidity/credited-inputs'
prior2=R.parent/'independent-zero-order-all-path-losses-review-20261015/owner-snapshot/zero-order-all-path-losses-20261015/credited-inputs'
reuse=[]
for x in json.loads((S/'SOURCE_INPUTS.json').read_text())['inputs']:
    p=S/'credited-inputs'/x['path']
    prev=next((root/x['path'] for root in [prior1,prior2] if (root/x['path']).is_file()),None)
    assert prev is not None,x['path']
    assert p.read_bytes()==prev.read_bytes(),x['path']
    reuse.append(dict(x,prior_full_read_copy=str(prev)))
author=json.loads((S/'AUTHOR_EXACT_CONTROLS.json').read_text())
assert author['paper_sha256']==sha(S/'PAPER.md')
assert author['source_sha256']==sha(S/'author_bulk_controls.py')
out={'status':'PASS','utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
 'method':'Independent literal hash/byte check only; no author program execution',
 'listed_files':len(rows),'total_owner_files':len(actual),'files':rows,
 'owner_zip_sha256':sha(R/'owner.zip'),'manifest_sha256':sha(S/'AUTHOR_V1_MANIFEST.json'),
 'prior_complete_scientific_reads_byte_equal':reuse,
 'author_result_source_hash_verified':True,'author_code_executed':False}
(R/'INPUT_VERIFICATION.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({k:v for k,v in out.items() if k not in ['files','prior_complete_scientific_reads_byte_equal']},indent=2))
