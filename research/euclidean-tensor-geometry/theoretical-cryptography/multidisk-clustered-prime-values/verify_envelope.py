"""Finite checks of clustered root envelopes using only constructed examples."""
from math import prod
from random import Random

rng=Random(20261128)
def g(t, A, E):
    return prod((t-c)**d for c,d in zip(A,E))

success=zero_components=large_centres=overlaps=0
for trial in range(6000):
    r=rng.randrange(1,6)
    A=[rng.randrange(-15,16) for _ in range(r)]
    if trial%5==0:
        A=[(1<<120)*(-1 if j%2 else 1)+a for j,a in enumerate(A)]
        large_centres+=1
    R=rng.randrange(0,6)
    offsets=[rng.randrange(0,8) for _ in range(rng.randrange(1,7))]
    W=max(offsets)-min(offsets)
    if any(abs(a-b)<=2*R for j,a in enumerate(A) for b in A[:j]):
        overlaps+=1
    a0=max(2,max(A)+R+2)+rng.randrange(12)
    args=[a0+i for i in offsets]
    E=[0]*r
    N=1
    for x in args:
        e=rng.randrange(1,6)
        for h in range(rng.randrange(1,7)):
            j=rng.randrange(r)
            centre=A[j]
            b=rng.randint(-R,R)
            if R>0 and rng.randrange(2)==0: # conjugate Gaussian pair
                im=rng.randint(0,R)
                if b*b+im*im<=R*R:
                    N*=((x-centre-b)**2+im*im)**e
                    E[j]+=2*e
                    continue
            N*=(x-centre-b)**e
            E[j]+=e
    assert 0<sum(E)<=N.bit_length() and 2**sum(E)<=N
    a,b=min(args),max(args)
    assert g(a-R,A,E)<=N<=g(b+R,A,E)
    if any(d==0 for d in E): zero_components+=1
    # The checker already knows the witnesses; search only their finite window.
    u=max(t for t in range(a-R,b+R+1) if g(t,A,E)<=N)
    assert g(u,A,E)<=N<g(u+1,A,E)
    assert all(abs(x-u)<=R+W+1 for x in args)
    success+=1

A=(-100,100)
# For X^2-9999, the roots lie in the stated disks since
# 99^2 < 9999 < 101^2, one root of each sign.
assert 99**2 < 9999 < 101**2
v=(104-101,111+100,106**2-9999)
assert v==(3,211,1237)
N=prod(p**e for p,e in zip(v,(2,1,3)))
assert g(103,A,(4,5))<=N<=g(112,A,(4,5))
assert (max(A)+N+1)>112
print("PASS root envelopes: %d fixtures; %d with unused centres; %d with large centres; %d with overlapping disks; exact mixed-degree example." % (success,zero_components,large_centres,overlaps))
