"""Fixed-H scalar arithmetic for the support subset {018,024,228,337}."""
from fractions import Fraction as Q
from itertools import combinations
from pathlib import Path
from math import comb
import json
from higher_moments import rows
from rank36_three_types import UNIT

def check():
    rr=rows()+[{k:1} for k in UNIT-{(0,18),(0,24),(2,28),(3,37)}]
    keys=sorted(set().union(*rr));piv={}
    for row in rr:
        v=[Q(row.get(k,0)) for k in keys]
        for i,a in sorted(piv.items()):
            c=v[i];v=[x-c*y for x,y in zip(v,a)]
        if any(v):
            i=next(j for j,x in enumerate(v) if x);piv[i]=[x/v[i] for x in v]
    def zero(r):
        assert set(r)<=set(keys)
        v=[Q(r.get(k,0)) for k in keys]
        for i,a in sorted(piv.items()):
            c=v[i];v=[x-c*y for x,y in zip(v,a)]
        assert not any(v)
    def lin(*terms):
        out={}
        for c,r in terms:
            for k,x in r.items():out[k]=out.get(k,0)+c*x
        return out
    S={(1,23):1,(0,0):-99,(0,14):-7}
    def T(j):
        return lin((1,{(0,0):88*j*j,(0,28):35,(0,18):420-176*j,(0,24):200,
                       (0,22):420,(0,14):5145}),(1470,S))
    zero(lin((1,{(0,0):-54405,(0,14):241760,(2,22):100470,(2,28):89085,
                 (3,37):9970,(2,34):1175,(3,35):4050}),(27,T(55))))
    zero(lin((1,{(0,18):-2702,(0,0):145579,(0,14):19910,(2,22):5745,
                 (2,28):5685,(3,35):300,(3,37):695}),(2,T(54))))
    zero(lin((1,{(0,18):-6,(0,0):291,(0,14):16,(2,22):5,(2,28):3,(3,37):1}),(2,S)))
    assert Q(54405,89085)<Q(5,8) and Q(145579,2702)>Q(430,8)
    assert (6*Q(145579,2702)-291-Q(54405,9970))/2>13
    return True
def check_combined_counts():
    raw=json.loads(Path(__file__).with_name('common-unit-hits.json').read_text())
    hit=[set(record[0]) for record in raw['proof']]+[{18,20,26,127,226,230}]
    labels=sorted(100*a+t for a,t in UNIT)
    avoid={18,24,228,337}
    counts=[]
    for k in range(13):
        cases=(set(t) for t in combinations(labels,k))
        counts.append(sum((16 not in A or 127 in A) and all(A&h for h in hit) and not A<=avoid for A in cases))
    assert counts==[0,0,0,16,114,333,537,545,371,175,56,11,1]
    print('Combined necessary support counts:',counts)

if __name__=='__main__':
    assert check()
    for m,h in [(5,4),(6,6),(7,15),(8,20),(9,32)]:
        k,r=divmod(11*m,22)
        assert (22-r)*comb(k,2)+r*comb(k+1,2)-4*comb(m,2)==h
        assert 8*comb(m,2)+6*(m*m//4)<=24+25*h
    assert 27*315*14>2*54405
    print('Three fixed-extension shell identities and all final arithmetic verified.')
    check_combined_counts()
