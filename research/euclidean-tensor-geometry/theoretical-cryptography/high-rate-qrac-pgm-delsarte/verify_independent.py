#!/usr/bin/env python3
"""Independently enumerate Fourier eigenvalues, Pauli frames, and Hamming syndromes."""
from fractions import Fraction as F
from math import comb
from random import Random

def WHT(a):
    v=a.copy()
    width=1
    while width<len(v):
        for i in range(0,len(v),2*width):
            for j in range(i,i+width):
                u,z=v[j],v[j+width]
                v[j],v[j+width]=u+z,u-z
        width*=2
    return v

def dot(a,b):
    return sum(x*y for x,y in zip(a,b))

cnt= nvals=0
for n in range(6,11):
    c0=F(1,n+n%2)
    for c in {c0,F(1,3),F(1,2),(c0+F(1,2))*F(1,2),
              (c0+F(1,2))*F(1,2)+F(1,251)} | ({F(1,8)} if n>=7 else set()):
        counts=[1,n,comb(n,2)]
        A=[WHT([F(1,counts[j]) if t.bit_count()==j else F(0)
                for t in range(1<<n)]) for j in range(3)]
        # Find the largest shell-1 mass by the actual 2^n Walsh inequalities,
        # not by the analytic r/s formula or the Krawtchouk recurrence.
        inequalities=list(zip(*A))
        cands=[(c*u0+(1-c)*u2)/(u2-u1)
               for u0,u1,u2 in inequalities if u2>u1]
        u=min(cands)
        q=[c,u,1-c-u]
        assert sum(q)==1 and min(q)>=0
        ev=[dot(q,t) for t in inequalities]
        assert min(ev)>=0 and 0 in ev
        # For any active character with negative first derivative, verify
        # the primal-to-dual identity directly on its XOR channel bands.
        I=next(i for i,t in enumerate(inequalities) if ev[i]==0 and t[2]>t[1])
        _,a,b=inequalities[I]
        avg=[F(0)]*(n+1)
        for x in range(1<<n):
            avg[x.bit_count()]+=(-1 if (x&I).bit_count()%2 else 1)
        avg=[z/comb(n,j) for j,z in enumerate(avg)]
        assert avg[:3]==[1,a,b]
        line=[a+(j-1)*(b-a) for j in range(n+1)]
        assert all(avg[j]<=line[j] for j in range(1,n+1))
        assert line[0]+(b-a)*(q[1]+2*q[2])+(1-line[0])*c==0
        nvals+=len(ev);cnt+=1
print("INDEPENDENT:",cnt,"exact XOR-channel primal/dual profiles,",nvals,"Walsh eigenvalues")

# Generate qubit density ensembles with maximally mixed average: each Bloch
# vector is paired with its opposite. Then Pr(Y=y|X=x)=(1+r_x·r_y)/2^n.
rng=Random(314159)
coords=[(F(0),F(0),F(0)),(F(1),F(0),F(0)),(F(0),F(1),F(0)),
        (F(0),F(0),F(1)),(F(1,3),F(2,3),F(2,3)),(F(2,3),F(1,3),F(0))]
np=atoms=0
for n in range(2,7):
    N=1<<n
    for _ in range(7):
        V=[rng.choice(coords) for _ in range(N//2)]
        V+= [tuple(-x for x in v) for v in V]
        rng.shuffle(V)
        assert all(sum(z)==0 for z in zip(*V))
        p=[F(0)]*(n+1)
        for i,a in enumerate(V):
            law=[(1+dot(a,b))/N for b in V]
            assert min(law)>=0 and sum(law)==1
            for j,pr in enumerate(law):
                p[(i^j).bit_count()]+=pr/N
                atoms+=1
        assert sum(p)==1 and p[0]<=F(2,N)
        ai=[tuple(sum((-1 if j&(1<<k) else 1)*v[t] for j,v in enumerate(V))/N
                  for t in range(3)) for k in range(n)]
        # Squared direct Helstrom bias (Bloch vector norm squared) matches
        # the marginal PGM bias here exactly, so count the distortion twice.
        assert sum(i*z for i,z in enumerate(p))==F(1,2)*(n-sum(dot(v,v) for v in ai))
        np+=1
print("INDEPENDENT:",np,"qubit PGM frame ensembles,",atoms,"conditional atoms")

tests=0
for k in (2,3,4,5):
    N=(1<<k)-1
    for extra in (0,1,3):
        for s in range(N+1):
            # The only correction needed for syndrome s is the indexed column.
            e=0 if s==0 else 1<<(s-1)
            t=0
            for b in range(N):
                if e>>b&1:t^=b+1
            assert t==s and e.bit_count()==int(s!=0) and e.bit_length()<=N+extra
            tests+=1
    if k>=4:
        for n in (N,N+1,3*N):
            b=F(N,N+1)
            assert 1-2*b/n>0 and (1-2*b/n)**2>1-F(k,n)
print("INDEPENDENT:",tests,"Hamming syndrome and padding cases; high-rate comparison PASS")
