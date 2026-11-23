"""Rational checks for a rank-independent cyclic-gap corollary."""
from fractions import Fraction as F
a,U=F(38196,100000),F(223607,100000)
assert U**2>5 and 2*a<3-U
def jensen(d,m,h):
    k,j=divmod(h*m,d)
    return (d-j)*a**k+j*a**(k+1)
for d,max_h in ((13,4),(14,2),(15,2)):
    cap=F(d*d+4*d+88,42)
    assert d+2*sum(jensen(d,30,h) for h in range(1,max_h+1))>cap*U
# Too few gaps greater than 2 while all 33 sites are hit:
# at least d-ch runs of h successive 2-gaps and c individual remaining gaps.
for d,last_forbidden in ((13,2),(14,1)):
    cap=F(d*d+4*d+88,42)
    for c in range(1,last_forbidden+1):
        s=33-2*(d-c)
        lower=sum(max(d-c*h,0)*a**(2*h) for h in range(1,d+1))+jensen(c,s,1)
        assert d+2*lower>cap*U
print('overlaps 13 through 16: every cycle hit; gap caps 7,6,5,3 respectively')
