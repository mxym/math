"""Rank38 {018,024,226}: at least 726 positive-charge U226 fields."""
from fractions import Fraction as Q
from rank38_three_hit_sets import engine
from rank36_three_types import UNIT

def check():
    R,C,D,o=engine()
    def lin(*terms):
        return [sum(c*r[i] for c,r in terms) for i in range(len(o))]
    def w(a,t):return R['w',(a,t)]
    n=w(0,18); V=lin((8,w(0,24))); L=lin((4,w(0,22))); Z=w(0,28)
    em=Q(3531,200); ep=Q(99,20)
    assert (em-12)**2<32 and ep*ep>Q(49,2)
    # T >=0 is a genuine rational tangent in each H before averaging:
    # 12+4 sqrt(2)>em and 7sqrt(2)/2<ep.
    j=47
    T=lin((84,n),(7,Z),(21,L),(Q(525,2),R['S']),(Q(3675,4),w(0,14)),
          (ep,V),(-2*j*em,n),(j*j*em,o))
    bound=Q(31968538,44055)
    # All five RHS rows are nonnegative, including the no16/20 graph N18 cap.
    v=lin((1,D[2,26]),(-bound/344,o),(-Q(12323,8811),w(0,14)),
          (-Q(9917,26433),w(2,22)),(-Q(608,26433),w(3,35)),
          (-Q(13811,15154920),C['no16/20']),(-Q(20,26433),T))
    piv={}
    for k in sorted(UNIT-{(0,18),(0,24),(2,26)}):
        r=list(D[k])
        for i,a in sorted(piv.items()):
            f=r[i];r=[x-f*y for x,y in zip(r,a)]
        if any(r):
            i=next(i for i,x in enumerate(r) if x);piv[i]=[x/r[i] for x in r]
    for i,r in sorted(piv.items()):
        f=v[i];v=[x-f*y for x,y in zip(v,r)]
    assert not any(v) and 725<bound<726
    assert 4*363>2*693
    return True
if __name__=='__main__':assert check();print("Rank 38 {018,024,226}: G226 >= 726; >=363 distinct true active squares.")
