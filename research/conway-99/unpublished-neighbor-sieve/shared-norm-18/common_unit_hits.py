"""Thirty-two common support implications; run beside rank36_three_types.py."""
from fractions import Fraction as Q
from itertools import combinations
from pathlib import Path
import json
from rank36_three_types import short_equations, UNIT

def checker():
    keys,eq=short_equations(); n=len(keys)
    def e(k):return [int(t==k) for t in keys]
    def lin(d):return [d.get(k,0) for k in keys]
    one=e((0,0)); G={('positive',k):e(k) for k in keys}
    G['u123']=lin({(1,23):1,(0,0):-99,(0,14):-7})
    G['W14cap']=lin({(0,14):-1,(0,0):4})
    G['lift']=lin({(1,27):1,(0,16):-1})
    G['site']=lin({(0,0):-210,(0,16):6120,(0,18):2940,(0,20):580,(0,26):300,(1,21):3420,(1,25):600,(2,26):1920,(2,28):-920,(2,30):240})
    G['sidon']=lin({(0,0):-545,(0,16):-193,(0,18):676,(0,20):212,(1,21):-112,(1,25):-52,(2,26):-304,(2,28):-12,(2,30):92,(3,37):72})
    SIDs=sorted(UNIT); tag=lambda k:100*k[0]+k[1]
    for k in SIDs:G['minus',k]=[-x for x in e(k)]
    def echelon(rows):
        piv={}
        for v in rows:
            v=list(map(Q,v))
            for j,r in sorted(piv.items()):
                c=v[j];v=[a-c*b for a,b in zip(v,r)]
            if any(v):
                j=next(i for i,t in enumerate(v) if t);piv[j]=[t/v[j] for t in v]
        return piv
    piv=echelon(eq);assert len(piv)==9
    path=Path(__file__).with_name('common-unit-hits.json')
    obj=json.loads(path.read_text());names=list(G);assert obj['names']==list(map(str,names))
    H=[]
    for hit,den,w in obj['proof']:
        assert den>0 and len(set(hit))==len(hit) and not set(hit)-set(map(tag,SIDs))
        assert len(w)==len(dict(w))
        out=[den*v for v in one];req=set()
        for j,c in w:
            assert type(j) is int and 0<=j<len(names) and type(c) is int and c>0
            k=names[j]
            if isinstance(k,tuple) and k[0]=='minus':req.add(tag(k[1]))
            out=[a+c*b for a,b in zip(out,G[k])]
        for j,r in sorted(piv.items()):
            a=out[j];out=[b-a*t for b,t in zip(out,r)]
        assert req==set(hit) and not any(out)
        H.append(frozenset(hit))
    assert len(H)==len(set(H))==32 and not any(a<b for a in H for b in H)
    U=sorted(map(tag,UNIT))
    base=[set(x) for size in range(13) for x in combinations(U,size) if all(set(x)&h for h in H)]
    filt=[s for s in base if 16 not in s or 127 in s]
    counts=lambda l:[sum(len(s)==k for s in l) for k in range(13)]
    assert counts(base)==[0,0,1,20,133,412,706,734,490,220,66,12,1]
    assert counts(filt)==[0,0,1,19,117,334,537,545,371,175,56,11,1]
    assert [s for s in filt if len(s)==2]==[{18,24}]
    print('32 exact rank-independent hit sets.')
    print('With norm 16 => unit (1,27):',counts(filt))
    print('Unremoved triples:',[sorted(s) for s in filt if len(s)==3])

    from common_six_family import check as check_six
    check_six()
    f6={18,20,26,127,226,230}
    final=[s for s in filt if s&f6]
    m=counts(final)
    assert m==[0,0,1,18,115,333,537,545,371,175,56,11,1]
    print('Also applying the six-family identity:',m)
    print('Final unremoved triples:',[sorted(s) for s in final if len(s)==3])
if __name__=='__main__':checker()
