"""Plain controls for the fixed-default obstruction; no universal claim."""
import hashlib,itertools,json
from pathlib import Path
R=Path(__file__).parent
C=[3,6,11,12,13,17,21,22,24,26];n=5;full=(1<<n)-1
masks=[sum(1<<i for i in q) for k in range(3) for q in itertools.combinations(range(n),k)]
def output(a,b,r):
    version=[c for c in C if c&a==b]
    if not version:raise ValueError('nonrealizable message')
    result=0
    for i in range(n):
        labels={(c>>i)&1 for c in version}
        value=next(iter(labels)) if len(labels)==1 else (r>>i)&1
        result|=value<<i
    return result
records=[]
for r in range(1<<n):
    distance=max((c^r).bit_count() for c in C)
    c=next(c for c in C if (c^r).bit_count()==distance)
    successful=[a for a in masks if output(a,c&a,r)==c]
    if successful:raise ValueError('fixed-default obstruction failed')
    records.append({'reference':r,'max_distance_concept':c,'distance':distance,'successful_messages_at_size_two':0})
res={'scope':'All 32 fixed references on this ONE listed finite class, complete max-distance samples and all their size<=2 messages. Author-only integer control; not a general compression counterexample.',
     'fixed_references_checked':32,'results':records,
     'source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
(R/'FIXED_DEFAULT_CONTROLS.json').write_text(json.dumps(res,indent=2)+'\n')
print(json.dumps({'fixed_references_checked':32,'maximal_complete_rows_uncovered_for_every_reference':True,'new_major_results':0},indent=2))
