#!/usr/bin/env python3
"""Independent NumPy checks using actual trace distances and tests."""
from itertools import product, combinations
from math import comb, sqrt, log2
import numpy as np

tol=3e-10
rng=np.random.default_rng(351881)
count={}


def ck(label,b):
    assert np.all(b), label
    count[label]=count.get(label,0)+1


def star(A):
    return A.conj().T


def kron_all(vs):
    out=np.array([[1]],dtype=complex)
    for v in vs:
        out=np.kron(out,v)
    return out


def trnorm_herm(A):
    return np.sum(np.abs(np.linalg.eigvalsh(A)))


def mexp(rows,d):
    return sum(rows,start=np.zeros((d,d),complex))


def ensemble(bases,ps,n):
    r=bases[0].shape[1]
    ws=list(product(range(len(ps)),repeat=n))
    probs=np.array([np.prod([ps[x] for x in w]) for w in ws])
    Q=[kron_all([bases[x] for x in w]) for w in ws]
    r=r**n
    states=[B@star(B)/r for B in Q]
    rh=mexp([p*A for p,A in zip(probs,states)],states[0].shape[0])
    return probs,Q,states,rh,r


def upper(ps,Q,states,rho,r,tables,a,b):
    w=np.array(a)-np.array(b)
    c=sum(abs(w))/2
    v=np.dot(w[1:],w[1:])
    vals,vecs=np.linalg.eigh(rho)
    mx=0
    for t,prob in tables:
        D=w[0]*rho+sum(wi*states[x] for x,wi in zip(t,w[1:]))
        ck("weighted Hermitian/table checks",abs(np.trace(D))<tol)
        mx+=prob*trnorm_herm(D)/2
    for s in [0.11,0.24,0.36,0.49,0.55,1/max(1,len(a)-1)/r]:
        choose=vals>=s
        row=np.sqrt(np.maximum(0,v*(vals[choose]/r-vals[choose]**2)))
        bound=c*sum(vals[~choose])+sum(row)
        ck("spectral-row bounds",0<=mx+tol and mx<=bound+tol)
    return mx


def product_tables(ps,K):
    return [(w,np.prod([ps[x] for x in w]))
            for w in product(range(len(ps)),repeat=K)]


def lower(ps,Q,states,rho,r,tables,t,K):
    vals,V=np.linalg.eigh(rho)
    Z=-np.log2(r*vals)
    d=len(vals)
    qavg=0
    Ac=np.zeros_like(rho)
    Bc=np.zeros_like(rho)
    L=[]
    deltas=[]
    for x,(p,Qx) in enumerate(zip(ps,Q)):
        columns=[]
        for psi in Qx.T:
            scores=np.abs(star(V)@psi)**2
            q=sum(scores[Z>t])
            if q<tol:
                continue
            j=max(0,int(np.floor(-log2(q))))
            mask=Z>t+j
            q1=sum(scores[mask])
            if q1<q/2:
                continue
            phi=V[:,mask]@(star(V[:,mask])@psi)
            u=phi/np.sqrt(q1)
            columns.append(u)
            qavg+=p*q1/r
            Ac+=p*np.outer(phi,phi.conj())/r
            Bc+=p*np.outer(u,u.conj())
            deltas.append(j)
        if columns:
            U=np.array(columns).T
            ck("same-site orthogonality",np.linalg.norm(star(U)@U-np.eye(len(columns)))<tol)
        L.append(columns)
    env=(V*(vals*(Z>t)*(1+np.maximum(Z-t,0))))@star(V)
    ck("dyadic operator domination",np.linalg.eigvalsh(env-Ac).min()>=-tol)

    tested=0
    dist=0
    ident=np.eye(d)
    for w,pw in tables:
        all_u=[u for x in w for u in L[x]]
        emp=sum(states[x] for x in w)/K
        dist+=pw*trnorm_herm(emp-rho)/2
        if all_u:
            U=np.array(all_u).T
            S=U@star(U)
            C=S+(S-ident)@(S-ident)
            T=np.linalg.solve(C,S)
            e=np.linalg.eigvalsh((T+star(T))/2)
            ck("numerical effect spectrum",e.min()>=-tol and e.max()<=1+tol)
            val=np.trace(T@(emp-rho)).real
            tested+=pw*val
    b=qavg-(K-1)*np.trace(Ac@Bc).real-4*K*np.trace(rho@Bc).real/3
    ck("independent lower-vs-test chains",b<=tested+tol and tested<=dist+tol)
    return deltas


pure=[np.array([[1],[0]],complex),
      np.array([[3/5],[4j/5]],complex)]
different=[np.array([[0],[1]],complex),
           np.array([[12/13],[5/13]],complex)]

def direct(a,b):
    out=np.zeros((4,2),complex)
    out[:2,:1]=a
    out[2:,1:]=b
    return out

compatible=[direct(a,b) for a,b in zip(pure,different)]
seen_shift=set()
for pa in [0.23,0.4,0.63]:
    for n in [1,2,3]:
        for basis in [pure,compatible] if n<3 else [pure]:
            ps,Q,states,rho,r=ensemble(basis,[pa,1-pa],n)
            if n==1:
                ck("noncommuting conditional examples",
                   np.linalg.norm(states[0]@states[1]-states[1]@states[0])>1e-3)
            tv_base=product_tables(ps,2)
            upper(ps,Q,states,rho,r,tv_base,[0,0.5,0.5],[1,0,0])
            for K in [1,2,3]:
                tables=product_tables(ps,K)
                for t in [-0.23,-0.01,0.47,0.91,1.4,2.25,3.2]:
                    seen_shift.update(lower(ps,Q,states,rho,r,tables,t,K))
ck("nontrivial conditional shifts",max(seen_shift)>0)

# Unrestricted fixed-rank upper: select generic rank-two projections
# for which compatibility fails. Also test genuinely dependent tables
# (uniform ternary parity) and ordinary row-versus-whole distances.
frames=[]
for k in range(3):
    A=rng.normal(size=(4,2))+1j*rng.normal(size=(4,2))
    frames.append(np.linalg.qr(A)[0])
ps,Q,states,rho,r=ensemble(frames,[1/3,1/3,1/3],1)
vals,V=np.linalg.eigh(rho)
F=[star(Q[0])@np.outer(v,v.conj())@Q[0] for v in V.T]
ck("incompatible compression negative control",any(
    np.linalg.norm(A@B-B@A)>1e-3 for A,B in combinations(F,2)))
parity=[((i,j,(i+j)%3),1/9) for i,j in product(range(3),repeat=2)]
for _ in range(80):
    a,b=rng.dirichlet(np.ones(4),size=2)
    upper(ps,Q,states,rho,r,parity,a,b)
case=product_tables(ps,4)
upper(ps,Q,states,rho,r,case,[0,0.5,0.5,0,0],[0,0.25,0.25,0.25,0.25])

# V=0 rank converse and rank degeneracy, calculated independently.
ps,Q,states,rho,r=ensemble([np.array([[1],[0]],complex),
                             np.array([[0],[1]],complex)],[0.5,0.5],2)
for K in range(1,5):
    for w,pr in product_tables(ps,K):
        A=sum(states[x] for x in w)/K
        observed=trnorm_herm(A-rho)/2
        ck("flat-average deterministic rank lower",
           observed+tol>=1-K*r/rho.shape[0])

# Spectral slab sums via the exact binomial probabilities of a two-level
# average. This is a bounded-size sanity check, not an asymptotic proof.
for n in [4,8,16,32,64,128,256]:
    weights=np.array([comb(n,k)*(1/5)**k*(4/5)**(n-k) for k in range(n+1)])
    z=np.array([k*log2(5)+(n-k)*log2(5/4) for k in range(n+1)])
    mu=np.dot(weights,z)
    for t in [mu+shift*sqrt(n) for shift in np.linspace(-2,2,37)]:
        low=z<=t
        l=np.dot(weights[low],np.exp2((z[low]-t)/2))
        h=np.dot(weights[~low],np.exp2(t-z[~low])*(1+z[~low]-t))
        ck("binomial spectral slab checks",sqrt(n)*max(l,h)<4)

for label,k in count.items():
    print(f"{label}: {k}")
