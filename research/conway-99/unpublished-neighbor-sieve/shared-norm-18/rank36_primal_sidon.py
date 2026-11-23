"""Exact rank-36 primal/extension gluing certificates, no LP or data file.

Run next to shared-norm-18/higher_moments.py. Pass A, B or C to verify one face.
"""
from fractions import Fraction as Q
from math import lcm
from pathlib import Path
import runpy, sys
from flint import fmpq_mat
from higher_moments import rows, projections, SHIFTS
from rank36_three_types import UNIT

P=2402
DATA={
 'A': ({(0,20),(0,24),(0,26)},64,
       (633601962,477991995,532498179,972321651,12497841,240443,1258648),9388413395),
 'B': ({(0,24),(0,26),(2,30)},48,
       (120332994,84940725,68424573,88455927,2944977,55566,175346),53385405),
 'C': ({(0,26),(1,25),(2,30)},34,
       (2556429271106,1612023573249,1281804597497,2590642804582,80688058247,
        1450423520,3678795393,36159),27971135327947),
}

def integer(r):
    de=lcm(*(Q(x).denominator for x in r))
    return [int(de*x) for x in r]

def check(index):
    allowed,t,weights,deficit=DATA[index]
    # In all rows a vector slot is a linear form on the following raw variables.
    raw=rows()
    keys=sorted(set().union(*raw,*(projections(sh,n) for sh in (None,*SHIFTS) for n in (1,2,3))))
    cols=keys+['N14','X14','M0']; n=len(cols)
    def e(k):
        return [int(h==k) for h in cols]
    def add(*vs):
        return [sum(z) for z in zip(*vs)]
    def times(z,v):
        return [z*x for x in v]
    def lin(*terms):
        return add(*(times(c,e(k)) for c,k in terms))
    one=e((0,0))
    ch=[((1,25),(0,16),8),((1,27),(0,18),9),((1,27),(2,26),2),((0,26),(1,21),8)]
    eq=[]
    for r in raw:
        # The source checker exports unit counts but our W coordinates are raw.
        z=dict(r)
        for target,src,mul in ch:z[src]=z.get(src,0)-mul*r.get(target,0)
        eq.append([z.get(k,0) for k in cols])
    for k in sorted(UNIT-allowed):
        eq.append(lin((1,k),*((-m,s) for target,s,m in ch if target==k)))
    reg={0:one,7:e('N14'),8:times(P,e((0,16))),9:times(P,e((0,18))),
         10:times(P,e((0,20))),11:lin((P,(0,22)),(2*P,(3,33))),
         12:lin((P,(0,24)),(2*P,(3,35))),13:lin((P,(0,26)),(2*P,(3,37))),
         14:e('X14')}
    path=Path(__file__).resolve().parents[2]/'maximal-marked-lattice'/'verify.py'
    b=runpy.run_path(str(path))['fourier_basis']()
    # Convert echelon basis to the one whose first 15 X coefficients are the coordinate units.
    for i in reversed(range(15)):
        x,y=b[i]
        for j in range(i+1,15):
            u,v=b[j];a=x[j];x=[h-a*k for h,k in zip(x,u)];y=[h-a*k for h,k in zip(y,v)]
        b[i]=x,y
    def X(j):return add(*(times(b[i][0][j],v) for i,v in reg.items()))
    def Y(j):return add(*(times(7**7*b[i][1][j],v) for i,v in reg.items()))
    yH=lin((1000,(0,0)),(-8,(0,14)),(200,(0,16)),(88,(0,18)),(64,(0,20)),
           (24,(0,22)),(48,(3,33)),(8,(0,24)),(16,(3,35)))
    eq.extend([add(Y(0),times(-1,one)),
               add(e('N14'),times(P-1,Y(1)),times(-P,e((0,14)))),
               add(e('X14'),times(P-1,Y(2)),times(-P,yH))])
    M=e((2,22));M0=e('M0');m=add(times(P,M),times(1-P,M0))
    S=lin((1,(1,23)),(-99,(0,0)),(-7,(0,14)))
    pos=[e((3,33)),e((3,35)),e((4,44)),Y(1),add(times(990,one),times(-1,e('N14'))),
         add(Y(3),times(-41058,one))]
    if index in ('A','B'):
        pos.append(add(times(9,yH),times(18,e((0,14))),times(-18,S),
                       times(-369-10*t,M),times(5*t*t-4158,one)))
    else:
        pos.append(add(times(9,Y(2)),times(18,Y(1)),
                       times(-369-10*t,M0),times(5*t*t-4158,one)))
        # B_k <= 2 G(4,44+2k) for k<=4; B_k <= N_(44-2k) for k>=5.
        def neutral_upper(j):
            k=(3,2*j+11)
            if j%7 and k in keys:return add(X(j),times(-2*P,e(k)))
            if j==14:return add(X(j),times(-462,one),times(-44,m))
            return X(j)
        upper=add(*(times(2*P,e((4,44+2*k))) for k in range(5)),
                  *(neutral_upper(j) for j in range(7,18)))
        pos.append(add(upper,times(-29999,m),times(15000**2,one)))
    assert len(pos)==len(weights) and min(weights)>0
    target=add(times(deficit,one),*(times(w,v) for w,v in zip(weights,pos)))
    a=[integer(v) for v in eq];rank=fmpq_mat(a).rref()[1]
    assert fmpq_mat(a+[integer(target)]).rref()[1]==rank
    print(index, 'rank',rank,'positive combination =',-deficit)

if __name__=='__main__':
    for index in (sys.argv[1:] or ('A','B','C')):check(index)
