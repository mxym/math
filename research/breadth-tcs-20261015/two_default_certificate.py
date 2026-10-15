"""Complete finite two-default local obstruction, author-only integer control."""
import gzip,hashlib,itertools,json,time
from pathlib import Path
import numpy as np
R=Path(__file__).parent

def run():
    p=R/'CEGIS_N16_D2_SEED149_CNF.json'
    data=json.loads(p.read_text());n=data['n'];d=data['d'];C=data['C'];N=1<<n
    masks=[sum(1<<i for i in q) for k in range(d+1) for q in itertools.combinations(range(n),k)]
    refs=np.arange(N,dtype=np.uint32); profiles=[0]*N; started=time.monotonic()
    for j,c in enumerate(C):
        uncertainty=set()
        for a in masks:
            u=0
            for z in C:
                if z&a==c&a:u|=z^c
            uncertainty.add(u)
        good=np.zeros(N,dtype=bool)
        for u in uncertainty:
            good|=((refs & u)==(c & u))
        for ref in np.flatnonzero(good):profiles[int(ref)]|=1<<j
    represented={}
    for ref,cover in enumerate(profiles):represented.setdefault(cover,ref)
    maximal=[]
    for cover in sorted(represented,key=int.bit_count,reverse=True):
        if not any(not(cover&~other) for other in maximal):maximal.append(cover)
    best=max(((a|b).bit_count(),represented[a],represented[b]) for j,a in enumerate(maximal) for b in maximal[j:])
    if best[0]>=len(C):raise ValueError('This listed finite obstruction did not hold')
    raw=json.dumps({'n':n,'d':d,'C':C,'profiles':profiles},separators=(',',':')).encode()+b'\n'
    archive=gzip.compress(raw,mtime=0)
    (R/'TWO_DEFAULT_FULL_PROFILES.json.gz').write_bytes(archive)
    record={'scope':'Only the listed 105-concept VC-two finite class and forced-label-then-fixed-default family. All 65536 arbitrary total references, all their unordered pairs, and all complete rows are accounted for. Same author, no independent review. General size-two compression already has a separately checked positive certificate.',
            'n':n,'actual_VC_from_bound_input':d,'concepts':len(C),'arbitrary_total_references_checked':N,'unique_profiles':len(represented),'maximal_profiles':len(maximal),'maximum_complete_concepts_covered_by_two_fixed_references':best[0],'best_reference_pair':[best[1],best[2]],'all_two_reference_families_miss_a_complete_concept':True,
            'profile_raw_sha256':hashlib.sha256(raw).hexdigest(),'profile_archive_sha256':hashlib.sha256(archive).hexdigest(),'input_sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'elapsed_seconds':time.monotonic()-started,'new_major_results':0}
    (R/'TWO_DEFAULT_CONTROL.json').write_text(json.dumps(record,indent=2)+'\n',encoding='utf-8')
    print(json.dumps(record,indent=2))
if __name__=='__main__':run()
