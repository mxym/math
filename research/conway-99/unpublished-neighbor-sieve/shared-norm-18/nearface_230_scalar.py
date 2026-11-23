"""Scalar upper bounds for the fixed-H {018,024,230} support."""
from fractions import Fraction as Q
from higher_moments import rows
from rank36_three_types import UNIT

def check():
    rr=rows()+[{k:1} for k in UNIT-{(0,18),(0,24),(2,30)}]
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
        return lin((1,{(0,0):88*j*j,(0,18):420-176*j,(0,28):35,(0,24):200,
                       (0,22):420,(0,14):Q(18375,4)}),(Q(2625,2),S))
    zero(lin((1,{(0,0):-170208,(0,14):100443,(1,29):1100,(2,22):41860,(3,35):1800}),(886,S),(12,T(54))))
    zero(lin((1,{(0,0):-27851472,(0,14):16430480,(1,29):193600,(2,22):6977520,(3,35):316800}),(1329,T(52)),(783,T(54))))
    zero(lin((1,{(0,18):-6,(0,0):291,(2,22):5,(0,14):16}),(2,S)))
    assert 170208<2*100443 and 27851472<4*6977520
    return True
if __name__=='__main__':assert check();print('Fixed-H U230 augmentation implies F=0, M<=3; 6n=291+2S+5M.')
