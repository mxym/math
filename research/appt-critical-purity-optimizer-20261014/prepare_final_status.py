from pathlib import Path
import difflib,hashlib,json

stage=Path(__file__).parent
edits={
 'PAPER.md':[
  ('Ordinary written proof, 14 October 2026. Proposed; complete review pending.',
   'Ordinary written proof, 14 October 2026. Independently reviewed.'),
  ('ordinary proof requires its own complete source-bound independent review;\nfinite controls do not replace that review or provide a Lean certificate.',
   'ordinary proof received its own complete source-bound independent review;\nfinite controls do not replace that review or provide a Lean certificate.')],
 'THEOREM_MAP.md':[
  ('14 October 2026. Proposed ordinary proof; complete review pending.',
   '14 October 2026. Independently reviewed ordinary proof.'),
  ('stay immutable. Promotion requires complete independent ordinary review.',
   'stay immutable. Complete independent ordinary review passed; source coverage is recorded.')],
 'README.md':[
  ('Proposed ordinary written result; complete independent review pending.',
   'Independently reviewed ordinary written result.'),
  ('[scope and literature](LITERATURE.md). Review records will bind the complete\ninitial mathematics, supporting controls, and actual later source changes.',
   '[scope and literature](LITERATURE.md), [independent review](REVIEW.md). Complete\ninitial mathematics, supporting controls, and actual later status changes are source-bound.')]
}
expected={
 'PAPER.md':'09717d59d6082f898f47a04f1ed0a64974d586f351841b1c985b63e92cf0f88c',
 'THEOREM_MAP.md':'9b6e125138acd9fd35059c17acc4ec2cf02385473129592a1a189300497b9bed',
 'README.md':'d2126531700999ec5c6c85124ea2a3c88a5411546e2fa9a27c357fd4dc84dba3'}
records={}
for name,changes in edits.items():
 p=stage/name;raw=p.read_bytes()
 if hashlib.sha256(raw).hexdigest()!=expected[name]:raise RuntimeError('Initial changed '+name)
 initial=stage/('INITIAL_'+name)
 if initial.exists():raise RuntimeError('Initial already captured')
 initial.write_bytes(raw)
 content=raw.decode()
 for old,new in changes:
  if content.count(old)!=1:raise RuntimeError('Unexpected status anchor '+name)
  content=content.replace(old,new)
 p.write_bytes(content.encode())
 diff=''.join(difflib.unified_diff(raw.decode().splitlines(True),content.splitlines(True),fromfile='INITIAL_'+name,tofile=name))
 (stage/('FINAL_STATUS_'+name+'.diff')).write_text(diff)
 records[name]={'initial_sha256':expected[name],'final_sha256':hashlib.sha256(p.read_bytes()).hexdigest(),
                'changes':[{'old':a,'new':b} for a,b in changes],'diff':diff}
(stage/'FINAL_STATUS_DELTAS.json').write_text(json.dumps(records,indent=2)+'\n')
print(json.dumps({k:{'initial':v['initial_sha256'],'final':v['final_sha256']} for k,v in records.items()},indent=2))
