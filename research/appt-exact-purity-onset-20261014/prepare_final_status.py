from pathlib import Path
import difflib, hashlib, json

stage=Path(__file__).parent
edits={
    'PAPER.md':[
        ('Ordinary written proof, 14 October 2026. Proposed; independent review pending.',
         'Ordinary written proof, 14 October 2026. Independently reviewed.'),
        ('The full manuscript needs a separate source-bound independent ordinary\nreview; finite controls alone are not a whole-domain certificate.',
         'The full mathematical manuscript and target map received a source-bound\nindependent ordinary review; finite controls alone are not a whole-domain certificate.')],
    'THEOREM_MAP.md':[
        ('14 October 2026. Proposed ordinary manuscript; not independently reviewed yet.',
         '14 October 2026. Independently reviewed ordinary manuscript.'),
        ('Publication/promotion requires a separate complete independent review.',
         'Complete independent ordinary review passed; its actual source coverage is recorded.')],
    'README.md':[
        ('Proposed ordinary result; independent complete review pending.',
         'Independently reviewed ordinary written result.'),
        ('[literature and dependency scope](LITERATURE.md). Independent review will\nbe bound separately to the full mathematical source and any later changes.',
         '[literature and dependency scope](LITERATURE.md), [independent review](REVIEW.md).\nThe full initial proof/map and actual later status changes are separately source-bound.')]
}
expected={
    'PAPER.md':'ad4059967adde63692ff5507a72caa3777fd97e29779aa128c4ef43da594085d',
    'THEOREM_MAP.md':'2324fadc329231142c6ddf7539ba27961aa4eb4abcbb49b4cd068ca37d007a5f',
    'README.md':'899f42f8811d6157e75ac07c1542e208aa9dac937f0819d67b2fc169f5dac5f8'}
records={}
for name,changes in edits.items():
    p=stage/name;raw=p.read_bytes()
    if hashlib.sha256(raw).hexdigest()!=expected[name]:raise RuntimeError('Changed initial '+name)
    initial=stage/('INITIAL_'+name)
    if initial.exists():raise RuntimeError('Do not overwrite initial capture')
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
