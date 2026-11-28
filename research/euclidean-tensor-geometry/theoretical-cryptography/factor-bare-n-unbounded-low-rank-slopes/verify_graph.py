"""Bounded, predetermined graph and seed tests; no external input."""
from fractions import Fraction as F
from math import prod,isqrt
from itertools import product

def prime(p):
    return p>=2 and all(p%d for d in range(2,isqrt(p)+1))

def comp(N,seed,S,E):
    found={seed};front=[seed]
    while front:
        v=front.pop()
        for m in S:
            for lo,hi,lower in [(m*v-E,m*v+E,False),((v-E)/m,(v+E)/m,True)]:
                lo=max(2,-(-lo.numerator//lo.denominator))
                hi=min(N,hi.numerator//hi.denominator)
                for t in range(lo,hi+1):
                    if t in found or (not (t<v) if lower else not (t>v)):continue
                    if N%t==0 and prime(t):
                        found.add(t);front.append(t)
    return found

def oracle(N):
    return [p for p in range(2,N+1) if N%p==0 and prime(p)]

def brute(vs,S,E):
    return {(a,b) for a in vs for b in vs if a<b and any(abs(b-m*a)<=E for m in S)}

def components(vs,ed):
    blocks=[{a} for a in vs]
    for a,b in ed:
        b1=next(z for z in blocks if a in z);b2=next(z for z in blocks if b in z)
        if b1!=b2:blocks.remove(b2);b1.update(b2)
    return blocks

def floorroot(N,C,D):
    lo,hi=0,1
    while C.numerator*hi**D<=N*C.denominator:hi*=2
    while hi-lo>1:
        j=(lo+hi)//2
        if C.numerator*j**D<=N*C.denominator:lo=j
        else:hi=j
    return lo

# Exhaust every seed (including a seed in each component of nonmembers) on a fixed small range.
count=0
for N in range(2,201):
    vs=oracle(N)
    for S,E in [([F(1)],1),([F(3,2)],2),([F(2),F(9,4)],1)]:
        blocks=components(vs,brute(vs,S,E))
        for v in vs:
            assert comp(N,v,S,E)==next(b for b in blocks if v in b);count+=1
print("bounded seed-component comparisons",count)

# Large-anchor test on an independently generated fixed factorization, not a timing test
# of the potentially enormous full word ball at this length.
vs=[9999991,19999981,13333339,20000047,40000061,60000113,30000109,
    20000147,30000167,60000403,90000611,45000353]
ns=[1,2,1,1,3,1,2,1,1,1,2,1]
tree=[(0,2,1),(1,F(3,2),-1),(2,F(3,2),1),(3,2,1),(4,F(3,2),1),
      (5,2,-1),(6,F(3,2),-1),(7,F(3,2),1),(8,2,1),(9,F(3,2),1),(10,2,-1)]
N=prod(p**e for p,e in zip(vs,ns));D=sum(ns);L=N.bit_length();E=L;P=vs[0]
S=[F(2),F(3,2)];scale=[F(1)];depth=[0]
for j,(i,m,sgn) in enumerate(tree,1):
    p,q=(vs[i],vs[j]) if sgn==1 else (vs[j],vs[i])
    assert p<q and abs(q-m*p)<=E
    scale.append(scale[i]*F(m)**sgn);depth.append(depth[i]+1)
assert all(prime(p) for p in vs) and P==min(vs)>4*L*E
C=prod(a**e for a,e in zip(scale,ns));J=floorroot(N,C,D)
assert C==483729408 and J==10000032 and abs(J-P)<=4*L*E
assert sum(d*n for d,n in zip(depth,ns))<L**2
assert all(abs(p/a-P)<=4*L*E for p,a in zip(vs,scale))
edges=brute(vs,S,E);sources=[p for p in vs if not any(q==p for v,q in edges)]
assert len(edges)==25 and len(sources)==2 and comp(N,P,S,E)==set(vs)
print("fixture bits / vertices / factors with multiplicity / edges / directed sources",L,len(vs),D,len(edges),len(sources))
print("small-seed cutoff / minimum prime / aggregate / floor center / signed offset",4*L*E,P,C,J,P-J)

# Exact prime powers and empty lists: no edges, one vertex always acceptable.
assert comp(7**5,7,[],1)=={7} and len(components([5,7],set()))==2
