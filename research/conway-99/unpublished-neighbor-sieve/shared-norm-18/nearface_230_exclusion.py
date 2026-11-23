"""Scalar upper bounds for the fixed-H {018,024,230} support."""
from fractions import Fraction as Q
from higher_moments import rows
from rank36_three_types import UNIT

def check():
    rr=rows()+[{k:1} for k in (UNIT-{(0,18),(0,24),(2,30)})|{(0,14)}]
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
    # F=0 on this face by the already certified nearface_230_scalar.py
    # Work in rows with F explicitly zero here (the other checker proves it).
    n={(0,18):1};v={(0,24):1};u={(2,30):1};M={(2,22):1};one={(0,0):1}
    Z={(0,28):1};L={(0,22):4};A={(1,29):8}
    zero(lin((6,n),(-291,one),(-2,S),(-5,M)))
    zero(lin((1,Z),(-4182,one),(Q(-134,3),S),(Q(-380,3),M),(4,v),(-8,u)))
    zero(lin((1,L),(-606,one),(Q(-22,3),S),(Q(-64,3),M),(2,v),(-4,u)))
    zero(lin((1,A),(-8*234,one),(32,S),(152,M),(48,u)))
    zero(lin((1,v),(-222,one),(Q(-13,6),S),(Q(-17,3),M),(-1,u),(-1,{(3,35):1})))
    # Replay the degree-two polynomial identity by interpolation on the simplex
    # S+M+u<=2: the two sides have degree <=2 in these three indeterminates.
    em=Q(1414,1000);ep=Q(1415,1000);cc=Q(5481,50);dd=394
    assert em**2<2<ep**2 and dd*(3-ep)>5*cc
    for m in range(3):
      for S0 in range(3-m):
        for ux in range(3-m-S0):
          nx=Q(291+2*S0+5*m,6);s=4*nx
          vx=222+Q(13,6)*S0+Q(17,3)*m+ux
          z=4182+Q(134,3)*S0+Q(380,3)*m-4*vx+8*ux
          l=606+Q(22,3)*S0+Q(64,3)*m-2*vx+4*ux
          ax=84*nx+7*z+21*l+28*ep*vx+Q(525,2)*S0-(12+4*em)*nx**2
          bx=15*s+z+21*l+678*S0+96*ux+40*vx+96*(234-4*S0-19*m-6*ux)-Q(45,44)*s*s
          p=(75197425*m*m+60157940*m*S0+4416628635*m+12031588*S0*S0
             -547446717*S0+7399613502)
          assert 12375*(dd*ax+cc*bx)==-p
    assert 547446717**2<4*12031588*7399613502
    return True
if __name__=='__main__':assert check();print('Native fixed-H row identities and signed/unsigned polynomial: {018,024,230} impossible.')
