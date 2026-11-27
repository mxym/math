#!/usr/bin/env python3
"""Direct spectral, CQ, and high-precision log-moment sanity checks."""
from itertools import product
from decimal import Decimal, localcontext
import math
import numpy as np

rng = np.random.default_rng(1729)
X=np.array([[0,1],[1,0]],dtype=complex)
Z=np.diag([1,-1])
I=np.eye(2)
kron=np.kron
t=48/math.sqrt(674)
target=100/math.sqrt(674)
beta0=math.atan(7/25)
psi=np.array([7,0,0,1])/math.sqrt(50)
oracle=np.outer(psi,psi)
pstar=(49/50)*(1+25/math.sqrt(674))/2

def obs(a, b):
    AA=[Z,math.cos(a)*Z+math.sin(a)*X]
    BB=[math.cos(b)*Z+math.sin(b)*X,math.cos(b)*Z-math.sin(b)*X]
    return AA,BB

def test(A,B):
    return t*kron(A[0],I)+sum((-1)**(x*y)*kron(A[x],B[y])
                                for x,y in product([0,1],repeat=2))

def expectation(S,M):
    return np.trace(S@M).real

def check(a,b,S):
    A,B=obs(a,b)
    M=test(A,B)
    lam=np.linalg.eigvalsh(M)
    assert np.max(np.abs(lam))<=target+1e-12
    score=expectation(S,M)
    delta=max(0,target-score)
    Px=expectation(S,kron((I+A[1])/2,I))
    Pz=expectation(S,kron((I+A[0])/2,(I+B[0])/2))
    assert max(abs(Px-.5),abs(Pz-pstar))<=22*(delta+5e-15)**.25+1e-10
    return delta

for i in range(240):
    G=rng.normal(size=(4,4))+1j*rng.normal(size=(4,4))
    S=G@G.conj().T
    S/=S.trace().real
    check(rng.uniform(0,math.pi),rng.uniform(0,math.pi/2),S)
near=0
for i in range(240):
    eps=10**rng.uniform(-7,-3)
    a=math.pi/2+eps*rng.normal()
    b=beta0+eps*rng.normal()
    G=psi+eps*(rng.normal(size=4)+1j*rng.normal(size=4))
    G/=np.linalg.norm(G)
    near+=check(a,b,np.outer(G,G.conj()))<2**-10
assert near==240
print("direct 4x4 spectral and outcome checks: 240 generic + 240 near-optimal PASS")

# Purify/measure side information directly for an ideal pair mixed with
# random perturbations, not by computing the closed-form H2 formula from
# an already guessed classical law.
for r in range(48):
    A,B=obs(math.pi/2,beta0)
    v=rng.normal(size=2)+1j*rng.normal(size=2)
    v/=np.linalg.norm(v)
    eps=10**rng.uniform(-5,-3)
    raw=np.kron(psi,v)+eps*(rng.normal(size=8)+1j*rng.normal(size=8))
    raw/=np.linalg.norm(raw)
    phi=raw.reshape(4,2)
    def cq_effect(Eff):
        return (phi.conj().T@Eff@phi).T
    d=max(0,target-expectation(phi@phi.conj().T,test(A,B)))
    op=[cq_effect(kron((I+a*A[1])/2,(I+b*B[0])/2))
         for a,b in product([1,-1],repeat=2)]
    e=sum(op)
    w,U=np.linalg.eigh(e)
    assert w[0]>0
    inv=(U*w**-.5)@U.conj().T
    pair_pgm=sum(np.trace(P@inv@P@inv).real for P in op)
    binary=op[0]+op[1]-op[2]-op[3]
    guess=(1+sum(abs(np.linalg.eigvalsh(binary))))/2  # Helstrom
    assert pair_pgm<=guess+2e-8
    assert guess<=.5+22*(d+5e-15)**.25+1e-9
    assert max(np.linalg.norm(P@Q-Q@P) for P in op for Q in op)>0
print("direct noncommuting CQ checks: 48 pair PGMs and Alice Helstrom bounds PASS")

with localcontext() as ctx:
    ctx.prec=170
    D=Decimal
    ln2=D(2).ln()
    q=D(1)/8
    L= D(100)/D(674).sqrt()
    R=D(48)/D(674).sqrt()
    assert 4+2*R>L
    assert D(22)/(2**10)+D(".5")<D(17)/32
    assert pstar-22./1024>15./16
    def gap(s,hz,hx,q):
        a=D(1)+s
        uz=(-s*ln2*hz/a).exp()
        ux=(-s*ln2*hx/a).exp()
        return ((q*uz**a+(1-q)*ux**a).ln()-a*(q*uz+(1-q)*ux).ln())/(s*ln2)
    cases=0
    for s in [D(1)/2**j for j in [0,1,2,5,16,32,60,90,109]]:
        for hz in (D(0),D(1)/8,D(1)/2):
            for hx in (D(9)/10,D(1),D(3)/2,D(2)):
                assert gap(s,hz,hx,q)>=s*s/4096
                cases+=1
    assert abs(gap(D(1),D(1),D(1),q))<D("1e-160")
    assert abs(gap(D(1),D(0),D(1),D(0)))<D("1e-160")
    A,B=obs(math.pi/2,beta0)
    collisions=[]
    for x in (0,1):
        p=[expectation(oracle,kron((I+a*A[x])/2,(I+b*B[0])/2))
           for a,b in product([1,-1],repeat=2)]
        collisions.append(sum(z*z for z in p))
    hz,hx=[D(str(-math.log2(v))) for v in collisions]
    val=gap(D(1),hz,hx,q)
    assert D(".02390")<val<D(".02392")
    print(f"170-digit log-moment checks: {cases} separated and 2 equal controls PASS")
    print("ideal pointwise order-2 gap: %.12f bits" % val)
