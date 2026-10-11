#!/usr/bin/env python3
"""Exact rational witnesses and reconstruction checks, NOT a Lean proof.

Only the Python standard library is required. No floating point or external
solver is used by this verifier. General statements are proved in THEOREMS.md.
"""
from __future__ import annotations
from fractions import Fraction as F
from itertools import product
from math import comb
import argparse
import json
import random
from pathlib import Path

Mat = list[list[F]]

def mat(rows) -> Mat:
    return [[F(x) for x in row] for row in rows]

def zero(n: int, m: int | None = None) -> Mat:
    return [[F(0) for _ in range(n if m is None else m)] for _ in range(n)]

def eye(n: int) -> Mat:
    return [[F(i == j) for j in range(n)] for i in range(n)]

def add(a: Mat, b: Mat) -> Mat:
    return [[x+y for x,y in zip(ar,br)] for ar,br in zip(a,b)]

def scale(c, a: Mat) -> Mat:
    return [[F(c)*x for x in row] for row in a]

def sub(a: Mat, b: Mat) -> Mat:
    return add(a, scale(-1,b))

def mul(a: Mat, b: Mat) -> Mat:
    if not a or not b or len(a[0]) != len(b):
        raise ValueError('Incompatible matrix dimensions')
    return [[sum((a[i][k]*b[k][j] for k in range(len(b))),F(0))
             for j in range(len(b[0]))] for i in range(len(a))]

def tr(a: Mat) -> Mat:
    return [list(row) for row in zip(*a)]

def diag(values) -> Mat:
    values=list(map(F,values))
    return [[v if i==j else F(0) for j in range(len(values))] for i,v in enumerate(values)]

def power(a: Mat, j: int) -> Mat:
    out=eye(len(a))
    for _ in range(j):
        out=mul(out,a)
    return out

def rref(a: Mat):
    a=[row[:] for row in a]; piv=[]; r=0
    for c in range(len(a[0])):
        p=next((i for i in range(r,len(a)) if a[i][c]),None)
        if p is None: continue
        a[r],a[p]=a[p],a[r]
        s=a[r][c];a[r]=[v/s for v in a[r]]
        for i in range(len(a)):
            if i!=r:
                s=a[i][c];a[i]=[x-s*y for x,y in zip(a[i],a[r])]
        piv.append(c);r+=1
        if r==len(a):break
    return a,piv

def rank(a: Mat) -> int:
    return len(rref(a)[1])

def inverse(a: Mat) -> Mat:
    n=len(a)
    if len(a[0])!=n:raise ValueError('Inverse requires square matrix')
    rr,p=rref([a[i]+eye(n)[i] for i in range(n)])
    if p[:n]!=list(range(n)):raise ValueError('Singular matrix')
    return [row[n:] for row in rr]

def determinant(a: Mat) -> F:
    a=[row[:] for row in a];out=F(1);n=len(a)
    for j in range(n):
        p=next((i for i in range(j,n) if a[i][j]),None)
        if p is None:return F(0)
        if p!=j:a[p],a[j]=a[j],a[p];out=-out
        pivot=a[j][j];out*=pivot
        for i in range(j+1,n):
            s=a[i][j]/pivot
            for k in range(j+1,n):a[i][k]-=s*a[j][k]
    return out

def nullspace(a: Mat) -> list[Mat]:
    rr,piv=rref(a);free=[j for j in range(len(a[0])) if j not in piv];out=[]
    for j in free:
        v=[F(0)]*len(a[0]);v[j]=F(1)
        for i,p in enumerate(piv):v[p]=-rr[i][j]
        out.append([[x] for x in v])
    return out

def hstack(columns: list[Mat]) -> Mat:
    return [[x for c in columns for x in c[i]] for i in range(len(columns[0]))]

def require(condition: bool, message: str) -> None:
    # Explicit checks remain active under python -O.
    if not condition:raise ValueError(message)

Q = mat([[F(8,100),F(1,100),F(2,100),F(4,100)]])
E = mat([[F(8,100),F(4,100),F(1,100),0]])
B = mat([[1],[0],[0],[0]])
ONES = mat([[1,1,1,1]])
H = ONES+Q+E
K = scale(F(1,100), mat([[-7,3,1,2],[4,-9,3,1],[2,4,-8,3],[1,2,4,-6]]))
A = sub(K,diag(Q[0])); D = diag(E[0])
V = mat([[F(-1,5)],[F(4,5)],[F(-8,5)],[1]])
W = mat([[0,2,1,0]])
N = mul(V,W)
LOWER,UPPER = F(-1,10),F(1,8)

def conjugate(a: Mat, theta: F) -> Mat:
    t=add(eye(4),scale(theta,N));ti=sub(eye(4),scale(theta,N))
    return mul(mul(t,a),ti)

def family(theta: F) -> tuple[Mat,Mat]:
    """Return K0(theta), K1(theta), with K(u)=K0+u*K1."""
    return add(conjugate(A,theta),diag(Q[0])), sub(D,conjugate(D,theta))

def family_polynomial():
    # K(theta,u) = sum_{j=0}^2 theta^j (C[j] + u*G[j]).
    c=[K,sub(mul(N,A),mul(A,N)),scale(-1,mul(mul(N,A),N))]
    g=[zero(4),sub(mul(D,N),mul(N,D)),mul(mul(N,D),N)]
    return c,g

def bernstein_coefficients(c: list[F], lo: F, hi: F) -> list[F]:
    """Exact power-to-Bernstein conversion on a real interval."""
    degree=len(c)-1
    translated=[sum((c[j]*comb(j,k)*lo**(j-k)*(hi-lo)**k
                     for j in range(k,degree+1)),F(0)) for k in range(degree+1)]
    return [sum((translated[k]*F(comb(i,k),comb(degree,k))
                 for k in range(i+1)),F(0)) for i in range(degree+1)]

def gauge_dimension(h: Mat,b: Mat,d: Mat|None=None) -> int:
    n=len(b);equations=[]
    for row in h:
        for j in range(n):
            equations.append([row[i] if l==j else F(0) for i in range(n) for l in range(n)])
    for i in range(n):
        for j in range(len(b[0])):
            equations.append([b[l][j] if k==i else F(0) for k in range(n) for l in range(n)])
    if d is not None:
        for i in range(n):
            for j in range(n):
                equations.append([(d[i][i]-d[j][j]) if (k,l)==(i,j) else F(0)
                                  for k in range(n) for l in range(n)])
    return n*n-rank(equations)

def moments(a: Mat,b: Mat,c: Mat,bw: Mat,bz: Mat):
    n=len(a)
    r=[mul(mul(c,power(a,j)),b)[0][0] for j in range(2*n)]
    h0=[[r[p+q] for q in range(n)] for p in range(n)]
    h1=[[r[p+q+1] for q in range(n)] for p in range(n)]
    mixed=lambda x:[[mul(mul(mul(mul(c,power(a,p)),x),power(a,q)),b)[0][0]
                     for q in range(n)] for p in range(n)]
    return r,h0,h1,mixed(bw),mixed(bz)

def reconstruct(data, eigenvalues: list[F]):
    """Exact reconstruction given a proposed rational contrast spectrum.

    The candidate eigenvalues are certified, not trusted: every normalized
    eigenvector is checked and their matrix must be invertible. This is an
    exact rational-spectrum test implementation, not a general eigen-solver.
    """
    r,h0,h1,w,z=data;n=len(h0)
    require(len(eigenvalues)==n and len(set(eigenvalues))==n,'Repeated or incomplete contrast spectrum')
    hi=inverse(h0);ah=mul(hi,h1);wh=mul(hi,w);zh=mul(hi,z)
    dh=sub(zh,wh);ch=[r[:n]];bh=mat([[int(i==0)] for i in range(n)])
    ell=scale(-1,mul(ch,inverse(ah)))
    cols=[]
    for ev in eigenvalues:
        ns=nullspace(sub(dh,scale(ev,eye(n))))
        require(len(ns)==1,'Candidate not a simple eigenvalue')
        vv=ns[0];normalization=mul(ell,vv)[0][0]
        require(normalization!=0,'Mass normalization failed')
        vv=scale(1/normalization,vv)
        require(mul(dh,vv)==scale(ev,vv),'Eigenvector certificate rejected')
        cols.append(vv)
    vv=hstack(cols);vi=inverse(vv)
    aa=mul(mul(vi,ah),vv);bb=mul(vi,bh);cc=mul(ch,vv)
    ww=mul(mul(vi,wh),vv);zz=mul(mul(vi,zh),vv)
    erow=scale(-1,mul(mat([[1]*n]),ww))
    k0=add(aa,diag(cc[0]));k1=add(ww,diag(erow[0]))
    require(mul(mat([[1]*n]),k0)==zero(1,n),'Baseline mass balance failed')
    require(mul(mat([[1]*n]),k1)==zero(1,n),'Modulation mass balance failed')
    require(sub(zz,ww)==diag(eigenvalues),'Recovered contrast is not diagonal')
    grow=scale(-1,mul(mat([[1]*n]),zz))
    require(all(x>0 for x in cc[0]),'Nonpositive discharge coefficient')
    require(all(x>=0 for x in erow[0]+grow[0]),'Negative external loss coefficient')
    require(all(row[0]>=0 for row in bb) and sum(row[0] for row in bb)==1,'Invalid input partition')
    for km in [k0,add(k0,k1)]:
        require(all(km[i][j]>=0 for i in range(n) for j in range(n) if i!=j),'Negative internal transfer')
    return {'a':aa,'b':bb,'q':cc,'e':erow,'g':grow,'k0':k0,'k1':k1,'contrast':sub(zz,ww)}

def same(a,b):require(a==b,'Exact equality failed')

def run() -> dict:
    checks=0
    def eq(a,b):
        nonlocal checks
        same(a,b);checks+=1
    eq(mul(N,N),zero(4));eq(mul(H,N),zero(3,4));eq(mul(N,B),zero(4,1))
    eq(mul(ONES,K),zero(1,4))
    rmat=hstack([mul(power(A,j),B) for j in range(4)])
    omat=[mul(Q,power(A,j))[0] for j in range(4)]
    require(determinant(rmat)!=0 and determinant(omat)!=0,'Baseline is not minimal')
    # A continuous-box positivity certificate: Bernstein basis weights are
    # nonnegative and sum to one, and K is affine in environmental forcing.
    c,g=family_polynomial();all_coeff=[]
    for i in range(4):
        for j in range(4):
            if i==j:continue
            for u in [F(0),F(1)]:
                co=bernstein_coefficients([c[k][i][j]+u*g[k][i][j] for k in range(3)],LOWER,UPPER)
                require(min(co)>=0,f'Negative Bernstein coefficient at {i},{j},{u}')
                all_coeff+=co
    # Necessity: these two source-column rates exclude every theta outside.
    eq([c[j][3][0] for j in range(3)],[F(1,100),F(1,10),F(0)])
    eq([c[j][2][0] for j in range(3)],[F(1,50),F(-4,25),F(0)])
    for theta in [LOWER,F(-1,20),F(0),F(1,10),UPPER]:
        k0,k1=family(theta);t=add(eye(4),scale(theta,N));ti=sub(eye(4),scale(theta,N))
        eq(mul(t,ti),eye(4));eq(mul(H,t),H);eq(mul(t,B),B)
        eq(mul(ONES,k0),zero(1,4));eq(mul(ONES,k1),zero(1,4))
        a0=sub(k0,diag(Q[0]));a1=sub(k1,D)
        eq(mul(a0,t),mul(t,A));eq(mul(a1,t),mul(t,scale(-1,D)))
        # Exhaustive small words are an additional finite check, NOT the proof
        # of all-forcing equivalence (which is the conjugacy identities above).
        for length in range(6):
            for word in product([0,1],repeat=length):
                old,new=B,B
                for bit in word:
                    old=mul([A,scale(-1,D)][bit],old)
                    new=mul([a0,a1][bit],new)
                eq(mul(H,old),mul(H,new))
        data=moments(a0,B,Q,a1,k1)
        recovered=reconstruct(data,E[0])
        for key,want in [('a',a0),('b',B),('q',Q),('e',E),('k0',k0),('k1',k1)]:eq(recovered[key],want)
        # Exact two-pulse retained-solute fingerprint; original K1=0.
        eq(data[4][0][1],-F(2,15625)*theta)
    dims={'water_only':gauge_dimension(H,B),
          'water_plus_retained_solute':gauge_dimension(H,B,D),
          'water_plus_one_internal_storage':gauge_dimension(H+mat([[0,1,0,0]]),B),
          'water_plus_one_targeted_input':gauge_dimension(H,hstack([B,mat([[0],[1],[0],[0]])]))}
    require(dims=={'water_only':3,'water_plus_retained_solute':0,'water_plus_one_internal_storage':0,'water_plus_one_targeted_input':2},'Dimension check failed')
    # Independent deterministic random fixtures exercise nonzero K1 and
    # a tracer partially lost to ET. The general proof is not a grid inference.
    rng=random.Random(30119);additional_reconstructions=0
    for n in range(2,7):
        for _ in range(3):
            km=mat([[0 if i==j else F(rng.randint(1,6),100) for j in range(n)] for i in range(n)])
            kn=mat([[0 if i==j else F(rng.randint(-3,3),1000) for j in range(n)] for i in range(n)])
            for j in range(n):
                km[j][j]=-sum(km[i][j] for i in range(n) if i!=j)
                kn[j][j]=-sum(kn[i][j] for i in range(n) if i!=j)
            cr=mat([[F(rng.randint(1,8),100) for i in range(n)]])
            er=mat([[F(3*i,100) for i in range(n)]])
            gr=mat([[F(i,100) for i in range(n)]])
            br=mat([[int(i==0)] for i in range(n)]);ar=sub(km,diag(cr[0]))
            dd=moments(ar,br,cr,sub(kn,diag(er[0])),sub(kn,diag(gr[0])))
            rr=reconstruct(dd,[F(2*i,100) for i in range(n)])
            for key,want in [('a',ar),('b',br),('q',cr),('e',er),('g',gr),('k0',km),('k1',kn)]:eq(rr[key],want)
            additional_reconstructions+=1
    rejected=[]
    def reject(name,fn):
        try:fn()
        except (ValueError,ZeroDivisionError):rejected.append(name)
        else:raise RuntimeError('Negative control accepted: '+name)
    baseline=moments(A,B,Q,scale(-1,D),zero(4))
    reject('co_transport_falsely_used_as_retained',lambda:reconstruct(moments(A,B,Q,scale(-1,D),scale(-1,D)),E[0]))
    reject('repeated_contrast_spectrum',lambda:reconstruct(baseline,[F(0)]*4))
    singular=list(baseline);singular[1]=zero(4)
    reject('singular_hankel',lambda:reconstruct(singular,E[0]))
    bad=list(baseline);bad[4]=scale(-1,baseline[3]) # wrong contrast 2D
    reject('incorrect_tracer_sign',lambda:reconstruct(bad,E[0]))
    reject('outside_lower_physical_interval',lambda:require(family(LOWER-F(1,100))[0][3][0]>=0,'negative flow'))
    reject('outside_upper_physical_interval',lambda:require(family(UPPER+F(1,100))[0][2][0]>=0,'negative flow'))
    reject('omitted_environment_compensation',lambda:same(mul(scale(-1,D),add(eye(4),scale(F(1,10),N))),mul(add(eye(4),scale(F(1,10),N)),scale(-1,D))))
    return {'status':'PASS','arithmetic':'fractions.Fraction; no floating point',
            'scope':'Finite rational certificates and exact reconstruction examples; general proofs are written, not Lean',
            'exact_equalities_checked':checks,'bernstein_coefficients_checked':len(all_coeff),
            'minimum_bernstein_coefficient':str(min(all_coeff)),
            'maximal_physical_theta_interval':[str(LOWER),str(UPPER)],'environment_interval':['0','1'],
            'controllability_determinant':str(determinant(rmat)),'observability_determinant':str(determinant(omat)),
            'hankel_determinant':str(determinant(baseline[1])),
            'exact_reconstructions':5+additional_reconstructions,'random_fixture_dimensions':[2,3,4,5,6],'random_seed':30119,'gauge_dimensions':dims,
            'retained_solute_mixed_coefficient':'Z[0,1] = -2*theta/15625',
            'negative_controls_rejected':rejected}

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--output',type=Path)
    args=p.parse_args();out=json.dumps(run(),indent=2,sort_keys=True)+'\n'
    if args.output:args.output.parent.mkdir(parents=True,exist_ok=True);args.output.write_text(out)
    print(out,end='')
