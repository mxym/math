"""Exact AM-GM tests on fixed synthetic examples, no general factoring interface."""
from fractions import Fraction as Q
from itertools import product
from math import isqrt,prod

def floor_center(z,D,h):
    # z=N/C0, center = D * z**(1/D) - h. Integer powers only.
    def le(j):
        u=j+h
        return u<=0 or u**D<=D**D*z
    lo,hi=-1,1
    while not le(lo):lo*=2
    while le(hi):hi*=2
    while hi-lo>1:
        mid=(hi+lo)//2
        if le(mid):lo=mid
        else:hi=mid
    return lo

def packet(x,y,f,g):
    # F and G are triples (slope, normalized shift, multiplicity).
    d=sum(n for a,h,n in f);e=sum(n for a,h,n in g);D=d+e
    C=prod(Q(a)**n for a,h,n in f+g)
    H=sum(Q(h)*n for a,h,n in f+g)
    ev=lambda block,t:prod((Q(a)*(t+h))**n for a,h,n in block)
    N=ev(f,x)*ev(g,y)
    S=d*x+e*y
    J=floor_center(N/C,D,H)
    assert (S+H)**D>=D**D*N/C
    R=max(t+h for t,block in [(x,f),(y,g)] for a,h,n in block)-min(t+h for t,block in [(x,f),(y,g)] for a,h,n in block)
    amin=min(t+h for t,block in [(x,f),(y,g)] for a,h,n in block)
    avg=Q(S+H,D)
    # Verify the global Jensen bound without evaluating a logarithm:
    # if B=avg*R^2/(2*amin^2) then g >= avg-B.
    a0=avg-avg*R**2/(2*amin**2)
    assert a0<=0 or a0**D<=N/C
    assert ev(f,x)*ev(g,Q(S-d*x,e))==N
    return N,C,H,S,J

tests=0
for x in (7,19,61):
    for w,h1,h2,d,e in product((0,1,3,7),(-1,Q(-1,3),0,Q(1,5),1),(-1,0,Q(1,2),1),(1,2,4),(1,3)):
        f=[(1,0,1),(3,h1,d)];g=[(1,0,1),(Q(5,4),h2,e)]
        packet(x,x+w,f,g);tests+=1
print("signed rational-offset and repeated-degree packets",tests)

A=[(1,0,2),(2,Q(1,2),1)]
B=[(1,0,1),(6,Q(1,6),2),(10,Q(1,10),1)]
A2=[(1,0,7),(2,Q(1,2),8)]
B2=[(1,0,6),(6,Q(1,6),3),(12,Q(1,12),4)]
for name,x,y,f,g,labels in [
    ("heterogeneous",1000151,1000303,A,B,{2,6,10}),
    ("wider-gap",1000589,1001551,A2,B2,{2,6,12})]:
    vs=[[int(a*(v+h)) for a,h,n in block] for v,block in [(x,f),(y,g)]]
    U=sum(vs,[])
    assert len(U)==len(set(U))==5 and all(all(q%j for j in range(2,isqrt(q)+1)) for q in U)
    actual={(p,q) for p in U for q in U if (q-1)%p==0 and (q-1)//p in labels}
    assert actual=={(b[0],q) for b in vs for q in b[1:]} and (y-x)**2<=x
    N,C,H,S,J=packet(x,y,f,g)
    if name=="heterogeneous":
        assert (N,C,H,S,J)==(721200314463743817659057631317462436078858319,720,Q(14,15),7001665,7001664)
    else:assert S-J>1
    print(name,"bits / gap / degree / weighted sum / exact floor / offset",N.numerator.bit_length(),y-x,sum(n for a,h,n in f+g),S,J,S-J)
