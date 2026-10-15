"""Try the improper repair of one withdrawn compressor; exact finite control."""
from pathlib import Path
from functools import lru_cache
import hashlib,json,sys,time
from finite_decoder import samples
R=Path(__file__).parent

def find_collision(n,C):
    C=tuple(sorted(C))
    @lru_cache(None)
    def phi(H,S):
        if not S or len({tuple((h>>i)&1 for i,b in S) for h in H})==1:return ()
        i,b=S[0];tail=S[1:]
        version=[h for h in H if all(((h>>j)&1)==v for j,v in tail)]
        if not version:raise ValueError('unrealizable recursive sample')
        if all(((h>>i)&1)==b for h in version):return phi(H,tail)
        opposite={tuple((h>>j)&1 for j,v in tail) for h in H if ((h>>i)&1)!=b}
        star=tuple(h for h in H if ((h>>i)&1)==b and tuple((h>>j)&1 for j,v in tail) in opposite)
        if not star:raise ValueError('empty recursive ambiguity class')
        return ((i,b),)+phi(star,tail)
    fibres={};processed=0
    for a,b in sorted(samples(n,C)):
        S=tuple((i,(b>>i)&1) for i in range(n) if (a>>i)&1)
        T=phi(C,S);processed+=1
        old=fibres.setdefault(T,{})
        for i,v in S:
            if i in old and old[i][0]!=v:
                return {'n':n,'C':list(C),'first_sample':old[i][1],'second_sample':[a,b],
                        'common_compressed_message':[list(x) for x in T],'opposite_coordinate':i,
                        'processed_samples':processed,'scope':'Only the prescribed compressor under canonical increasing coordinate order; a conflicting pair excludes even improper reconstruction of this compressor, not every possible compressor.'}
            old[i]=(v,[a,b])
    return None

if __name__=='__main__':
    history=[];start=time.monotonic();found=None
    for bitset in range(1,1<<8):
        C=[c for c in range(8) if (bitset>>c)&1]
        got=find_collision(3,C)
        if got:found=got;break
    history.append({'n':3,'nonempty_classes_processed':bitset,'collision':bool(found)})
    if found is None:
        for name in ['WARMUTH','CEGIS_N8_D2_SEED41.json','CEGIS_N10_D2_SEED73_RESUMED.json']:
            if name=='WARMUTH':n=5;C=[3,6,11,12,13,17,21,22,24,26]
            else:D=json.loads((R/name).read_text());n=D['n'];C=D['C']
            found=find_collision(n,C);history.append({'input':name,'collision':bool(found)})
            if found:break
    record={'source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'history':history,'collision':found,'elapsed_seconds':time.monotonic()-start,'new_major_results':0,'status':'author-only route control, not original-target counterexample'}
    (R/'WITHDRAWN_COMPRESSOR_REPAIR_CONTROL.json').write_text(json.dumps(record,indent=2)+'\n',encoding='utf-8')
    print(json.dumps(record,indent=2))
