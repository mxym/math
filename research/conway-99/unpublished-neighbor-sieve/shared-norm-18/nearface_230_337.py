"""The signed/unsigned obstruction on the fixed-H {018,024,230,337} support."""
from fractions import Fraction as Q
from itertools import combinations
from pathlib import Path
import json
from higher_moments import rows
from rank36_three_types import UNIT

def check():
    rr=rows()+[{k:1} for k in UNIT-{(0,18),(0,24),(2,30),(3,37)}]
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
    F={(0,14):1};h={(3,37):1}
    # T is a nonnegative signed-centroid tangent, see nearface-four-exclusion.md.
    j=54
    T=lin((1,{(0,0):88*j*j,(0,18):420-176*j,(0,28):35,(0,24):200,
                (0,22):420,(0,14):Q(18375,4)}),(Q(2625,2),S))
    zero(lin((1,{(0,0):-170208,(0,14):100443,(1,29):1100,(2,22):41860,(3,35):1800}), (886,S),(12,T),(4768,h)))
    assert 170208<2*100443  # F is an even nonnegative integer, hence F=0.
    n={(0,18):1};v={(0,24):1};u={(2,30):1};M={(2,22):1};one={(0,0):1}
    Z={(0,28):1};L={(0,22):4};A={(1,29):8}
    zero(lin((6,n),(-291,one),(-2,S),(-5,M),(-1,h),(-16,F)))
    zero(lin((1,Z),(-4182,one),(Q(-134,3),S),(Q(-380,3),M),(4,v),(-8,u),(Q(-88,3),h),(Q(-850,3),F)))
    zero(lin((1,L),(-606,one),(Q(-22,3),S),(Q(-64,3),M),(2,v),(-4,u),(Q(-14,3),h),(Q(-146,3),F)))
    zero(lin((1,A),(-8*234,one),(32,S),(152,M),(48,u),(24,h),(128,F)))
    zero(lin((1,v),(-222,one),(Q(-13,6),S),(Q(-17,3),M),(-1,u),(-1,{(3,35):1}),(Q(-5,6),h),(Q(-46,3),F)))
    # Replay the degree-two polynomial identity by interpolation on the simplex
    # S+M+u+h<=2: both sides have degree <=2 in four indeterminates.
    em=Q(1414,1000);ep=Q(1415,1000);cc=Q(5481,50);dd=394
    assert em**2<2<ep**2 and dd*(3-ep)>5*cc
    for m in range(3):
      for S0 in range(3-m):
        for ux in range(3-m-S0):
         for h0 in range(3-m-S0-ux):
          nx=Q(291+2*S0+5*m+h0,6);s=4*nx
          vx=222+Q(13,6)*S0+Q(17,3)*m+ux+Q(5,6)*h0
          z=4182+Q(134,3)*S0+Q(380,3)*m-4*vx+8*ux+Q(88,3)*h0
          l=606+Q(22,3)*S0+Q(64,3)*m-2*vx+4*ux+Q(14,3)*h0
          ax=84*nx+7*z+21*l+28*ep*vx+Q(525,2)*S0-(12+4*em)*nx**2
          bx=15*s+z+21*l+678*S0+96*ux+40*vx+96*(234-4*S0-19*m-6*ux-3*h0)-Q(45,44)*s*s
          p=(75197425*m*m+60157940*m*S0+4416628635*m+12031588*S0*S0
             -547446717*S0+7399613502+h0*(30078970*m+12031588*S0+3007897*h0+537965019))
          assert 12375*(dd*ax+cc*bx)==-p
    assert 547446717**2<4*12031588*7399613502
    return True
def count_supports():
    raw=json.loads(Path(__file__).with_name('common-unit-hits.json').read_text())
    hits=[set(r[0]) for r in raw['proof']]+[{18,20,26,127,226,230}]
    U=sorted(100*a+t for a,t in UNIT); avoid=[{18,24,228,337},{18,24,230,337}]
    counts=[]
    for k in range(13):
        cases=(set(x) for x in combinations(U,k))
        counts.append(sum((16 not in C or 127 in C) and all(C&H for H in hits)
                          and not any(C<=B for B in avoid) for C in cases))
    assert counts==[0,0,0,15,113,333,537,545,371,175,56,11,1]
    print('Combined necessary support counts:',counts)

if __name__=='__main__':
    assert check()
    print('Native fixed-H row identities and signed/unsigned polynomial: {018,024,230,337} impossible.')
    count_supports()
