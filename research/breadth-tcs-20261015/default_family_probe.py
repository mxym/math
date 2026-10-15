"""Exact local full-row gates for small fixed-default families; not SC0."""
import hashlib,itertools,json,time
from pathlib import Path
R=Path(__file__).parent
FILES=['CEGIS_N8_D2_SEED41.json','CEGIS_N10_D2_SEED73_RESUMED.json','CEGIS_N12_D2_SEED107_CNF.json','CEGIS_N12_D3_SEED211_CNF.json','CEGIS_N16_D2_SEED149_CNF.json']
def run(name):
    started=time.monotonic();p=R/name;D=json.loads(p.read_text());n=D['n'];d=D['d'];C=D['C']
    masks=[sum(1<<i for i in q) for k in range(d+1) for q in itertools.combinations(range(n),k)]
    minimal={}
    for c in C:
        us=set()
        for a in masks:
            u=0
            for z in C:
                if z&a==c&a:u|=z^c
            us.add(u)
        minimal[c]=[u for u in us if not any(v!=u and not(v&~u) for v in us)]
    profiles={}
    for ref in range(1<<n):
        profile=sum(1<<j for j,c in enumerate(C) if any(not(u&(c^ref)) for u in minimal[c]))
        profiles.setdefault(profile,ref)
    descending=sorted(profiles,key=int.bit_count,reverse=True)
    maximal=[]
    for a in descending:
        if not any(not(a&~b) for b in maximal):maximal.append(a)
    full=(1<<len(C))-1
    pairs=[]
    for j,a in enumerate(maximal):
        for b in maximal[j:]:
            if a|b==full:pairs.append([profiles[a],profiles[b]])
    rec={'n':n,'actual_VC':d,'concepts':len(C),'references_tested':1<<n,'different_full_row_profiles':len(profiles),'maximal_profiles':len(maximal),'best_single_reference_local_rows':max(a.bit_count() for a in profiles),'maximal_profile_pairs_covering_all_full_rows':pairs,'elapsed_seconds':time.monotonic()-started,'input_sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'scope':'Only local full-row reachability using any allowed message and one of the fixed references. Per-message reference choices not coupled and partial-sample coverage not certified.'}
    return rec
if __name__=='__main__':
    records=[]
    for f in FILES:
        rec=run(f);records.append(rec)
        print(json.dumps({k:v for k,v in rec.items() if k!='maximal_profile_pairs_covering_all_full_rows'}),flush=True)
        print('two_reference_pairs',len(rec['maximal_profile_pairs_covering_all_full_rows']),flush=True)
        (R/'DEFAULT_FAMILY_PROBE.json').write_text(json.dumps({'scope':'Exploratory restricted-decoder gates, no universal conclusion.','source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'records':records},indent=2)+'\n',encoding='utf-8')
