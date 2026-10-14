from pathlib import Path
import difflib,hashlib,json

stage=Path(__file__).parent
edits={
 'PAPER.md':[
  ('Ordinary written proof, 14 October 2026. Proposed; complete review pending.',
   'Ordinary written proof, 14 October 2026. Independently reviewed.'),
  ('Complete independent ordinary review is required before promotion; exact\nsymbolic and finite controls supplement that review rather than replace it.',
   'Complete independent ordinary review passed with source-bound coverage; exact\nsymbolic and finite controls supplement that review rather than replace it.')],
 'THEOREM_MAP.md':[
  ('14 October 2026. Proposed ordinary manuscript; complete review pending.',
   '14 October 2026. Independently reviewed ordinary manuscript.'),
  ('ordinary review is required before promotion.',
   'ordinary review passed; actual source coverage and changes are recorded.')],
 'README.md':[
  ('Proposed ordinary result; complete independent review pending.',
   'Independently reviewed ordinary written result.'),
  ('[scope and literature](LITERATURE.md). Separate review records will bind\nthe complete mathematics, real changes, and supporting finite controls.',
   '[scope and literature](LITERATURE.md), [independent review](REVIEW.md). Records bind\nthe complete initial mathematics, actual final changes, and supporting finite controls.'),
  ("The original exploratory test's structural-symbolic comparison error\nis retained with its corrected successful run; it is not hidden.",
   'Both author test-construction errors, including the mistaken finite guard,\nare retained with their corrected successful runs; mathematics was unchanged.')]
}
expected={
 'PAPER.md':'f0a38d5e994dfdb3b0b2ef810b04c1f9e0db565d9afe6e72a7b86153b4f8661c',
 'THEOREM_MAP.md':'cd8187d302640d8bcfd899a34a54c03000f117010cd9673776924e672e26d98f',
 'README.md':'4b6d830d63ac40054c32d6e3180cae80ec32cc0badecaad05243a070809c3bd9'}
records={}
for name,changes in edits.items():
 p=stage/name;raw=p.read_bytes()
 if hashlib.sha256(raw).hexdigest()!=expected[name]:raise RuntimeError('Changed initial '+name)
 saved=stage/('INITIAL_'+name)
 if saved.exists():raise RuntimeError('Do not overwrite capture')
 saved.write_bytes(raw);text=raw.decode()
 for old,new in changes:
  if text.count(old)!=1:raise RuntimeError('Unexpected status anchor '+name)
  text=text.replace(old,new)
 p.write_text(text)
 diff=''.join(difflib.unified_diff(raw.decode().splitlines(True),text.splitlines(True),fromfile='INITIAL_'+name,tofile=name))
 (stage/('FINAL_STATUS_'+name+'.diff')).write_text(diff)
 records[name]={'initial_sha256':expected[name],'final_sha256':hashlib.sha256(p.read_bytes()).hexdigest(),
                'changes':[{'old':a,'new':b} for a,b in changes],'diff':diff}
(stage/'FINAL_STATUS_DELTAS.json').write_text(json.dumps(records,indent=2)+'\n')
print(json.dumps({k:{'initial':v['initial_sha256'],'final':v['final_sha256']} for k,v in records.items()},indent=2))
