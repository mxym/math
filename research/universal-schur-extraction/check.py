#!/usr/bin/env python3
"""Exact ancillary checks for universal Schur extraction, not an analytic proof oracle."""
from __future__ import annotations
import argparse
from fractions import Fraction as F
from functools import lru_cache
from itertools import product
from math import factorial, prod, isqrt
from pathlib import Path
import hashlib
import json

class CheckFailed(RuntimeError):
    pass

def require(condition: bool, label: str) -> None:
    if not condition:
        raise CheckFailed(label)

@lru_cache(None)
def partitions(k: int, D: int, ceiling: int | None = None) -> tuple[tuple[int,...],...]:
    if D == 0:
        return ((),) if k == 0 else ()
    maximum=min(k,ceiling if ceiling is not None else k)
    return tuple((j,)+tail for j in range(maximum,-1,-1)
                 for tail in partitions(k-j,D-1,j))

def dims(lam: tuple[int,...]) -> tuple[int,int]:
    D=len(lam);k=sum(lam)
    vand=prod(lam[i]-lam[j]+j-i for i in range(D) for j in range(i+1,D))
    u=F(vand,prod(j-i for i in range(D) for j in range(i+1,D)))
    v=F(factorial(k)*vand,prod(factorial(lam[i]+D-1-i) for i in range(D)))
    require(u.denominator==v.denominator==1,'integral Weyl and hook dimensions')
    return int(u),int(v)

@lru_cache(None)
def standard_tableaux(lam: tuple[int,...]) -> int:
    if not any(lam):return 1
    out=0
    for i,x in enumerate(lam):
        if x and (i+1==len(lam) or x>lam[i+1]):
            new=list(lam);new[i]-=1
            out+=standard_tableaux(tuple(new))
    return out

def determinant(M: list[list[F]]) -> F:
    M=[row[:] for row in M];n=len(M);result=F(1)
    for i in range(n):
        pivot=next((j for j in range(i,n) if M[j][i]),None)
        if pivot is None:return F(0)
        if pivot!=i:M[i],M[pivot]=M[pivot],M[i];result=-result
        p=M[i][i];result*=p
        for j in range(i+1,n):
            ratio=M[j][i]/p
            for t in range(i+1,n):M[j][t]-=ratio*M[i][t]
    return result

def schur(lam: tuple[int,...], xs: tuple[F,...]) -> F:
    degree=sum(lam)+len(lam)
    h=[F(1)]+[F(0)]*degree
    for x in xs:
        for j in range(1,degree+1):h[j]+=x*h[j-1]
    def at(j):return h[j] if j>=0 else F(0)
    return determinant([[at(lam[i]-i+j) for j in range(len(lam))] for i in range(len(lam))])

def check_schur() -> dict:
    shape_count=mass_checks=zero_blocks=0
    for D in range(2,6):
        laws=[tuple(F(1,D) for _ in range(D)),
              tuple(F(D-i,D*(D+1)//2) for i in range(D)),
              (F(2,3),F(1,3))+tuple(F(0) for _ in range(D-2)),
              (F(1),)+tuple(F(0) for _ in range(D-1))]
        for k in range(1,11):
            shapes=partitions(k,D);Q=(k+D)**(D*(D+1)//2)
            block_dims={lam:dims(lam) for lam in shapes}
            require(sum(u*v for u,v in block_dims.values())==D**k,'Schur dimension resolution')
            for lam,(u,v) in block_dims.items():
                shape_count+=1
                require(v==standard_tableaux(lam),'independent hook tableau recursion')
                require(schur(lam,tuple(F(1) for _ in range(D)))==u,'independent Weyl character dimension')
                entropy_power=prod((F(k,x)**x for x in lam if x),start=F(1))
                require(entropy_power/Q<=v<=entropy_power,'Schur entropy dimension bounds')
                require(entropy_power/Q<=u*v<=Q*entropy_power,'Schur block dimension bounds')
            for p in laws:
                mass=F(0)
                for lam,(u,v) in block_dims.items():
                    mon=prod((p[i]**x for i,x in enumerate(lam)),start=F(1))
                    ch=schur(lam,p);t=v*ch;mass+=t;mass_checks+=1
                    require(mon<=ch<=u*mon,'Schur highest-weight character sandwich')
                    if mon==0:
                        require(t==0,'rank-deficient Schur support');zero_blocks+=1
                    else:
                        divergence_power=prod(((F(k)*p[i]/x)**x for i,x in enumerate(lam) if x),start=F(1))
                        require(divergence_power/Q<=t<=Q*divergence_power,'Schur probability sandwich')
                require(mass==1,'Schur probability normalization')
    return {'shapes':shape_count,'probability_checks':mass_checks,'zero_probability_blocks':zero_blocks}

# Sparse matrices with rational entries.
def eye(n):return {(i,i):F(1) for i in range(n)}
def add(*matrices):
    out={}
    for M in matrices:
        for ij,x in M.items():out[ij]=out.get(ij,F(0))+x
    return {ij:x for ij,x in out.items() if x}
def scale(c,M):return {ij:c*x for ij,x in M.items() if c*x}
def transpose(M):return {(j,i):x for (i,j),x in M.items()}
def multiply(M,N):
    rows={}
    for (j,k),y in N.items():rows.setdefault(j,[]).append((k,y))
    out={}
    for (i,j),x in M.items():
        for k,y in rows.get(j,[]):out[i,k]=out.get((i,k),F(0))+x*y
    return {ij:x for ij,x in out.items() if x}
def tensor(M,N,sizeN):return {(i*sizeN+k,j*sizeN+l):x*y for (i,j),x in M.items() for (k,l),y in N.items()}
def trace(M):return sum((x for (i,j),x in M.items() if i==j),F(0))

def check_unknown_orientation() -> dict:
    D=4;N=D*D
    swap={(i*D+j,j*D+i):F(1) for i in range(D) for j in range(D)}
    plus=scale(F(1,2),add(eye(N),swap));minus=scale(F(1,2),add(eye(N),scale(-1,swap)))
    require(multiply(plus,plus)==plus and multiply(minus,minus)==minus,'central Schur idempotents')
    require(not multiply(plus,minus) and add(plus,minus)==eye(N),'central Schur orthogonal resolution')
    up,um=int(trace(plus)),int(trace(minus))
    tau=add(scale(F(1,2*up),plus),scale(F(1,2*um),minus))
    require(trace(tau)==1,'normalized universal state')
    W=eye(D);W.update({(0,0):F(3,5),(0,1):F(-4,5),(1,0):F(4,5),(1,1):F(3,5)})
    require(multiply(W,transpose(W))==eye(D),'rational basis rotation unitary')
    WW=tensor(W,W,D)
    require(multiply(multiply(WW,tau),transpose(WW))==tau,'universal state basis invariance')
    checked=0
    for p in [(F(1,2),F(1,4),F(1,8),F(1,8)),(F(2,3),F(1,3),F(0),F(0))]:
        rho={(i,i):x for i,x in enumerate(p) if x};rot=multiply(multiply(W,rho),transpose(W))
        require(multiply(rho,rot)!=multiply(rot,rho),'genuinely noncommuting input pair')
        for state in [rho,rot]:
            two=tensor(state,state,D)
            require(multiply(two,tau)==multiply(tau,two),'universal state commutation')
            expected_plus=(1+sum(x*x for x in p))/2
            require(trace(multiply(plus,two))==expected_plus,'basis-independent Schur block probability')
            checked+=1
        # Complete eigenvalue comparison in the symmetric/antisymmetric product basis.
        B=2*max(up,um)
        for i in range(D):
            require(p[i]*p[i]<=F(B,2*up),'universal domination diagonal eigenvalue')
            for j in range(i+1,D):
                require(p[i]*p[j]<=F(B,2*up) and p[i]*p[j]<=F(B,2*um),'universal domination pair eigenvalues')
    return {'noncommuting_input_states':checked,'matrix_dimension':N,'central_block_ranks':[up,um]}

def check_multiplicity_selection() -> dict:
    checked=0
    for u in range(2,5):
        for v in range(2,7):
            A={(i,j):F((i+1)*(j+1),sum((t+1)**2 for t in range(u))) for i in range(u) for j in range(u)}
            require(trace(A)==1,'coherent representation-factor normalization')
            rho=scale(F(1,v),tensor(A,eye(v),v))
            for vp in range(1,v):
                selected={i*v+j for i in range(u) for j in range(vp)}
                retained={(i,j):x for (i,j),x in rho.items() if i in selected and j in selected}
                require(trace(retained)==F(vp,v),'multiplicity-factor retained mass')
                require(all((i in selected)==(j in selected) for (i,j),x in rho.items()),'selection does not cut unknown coherences')
                checked+=1
    return {'coherent_multiplicity_selections':checked}

def choose_d(a0,b0,rprime,K):
    return max(d for d in range(1,min(a0,K)+1) if (a0//d)*(b0//d)>=rprime)

def check_packing() -> dict:
    checked=truncated=exact=0
    for J in range(1,7):
        for a in range(2*J,20*J+1,J):
            for b in [a,a+1,2*a+3,3*a]:
                a0=a//J;b0=b//J;N=a*b;N0=a0*b0
                for u in sorted({1,2,3,N0//2}):
                    if 2*u>N0:continue
                    for v in sorted({1,2,max(1,N0//u),N0//u+1,N//u}):
                        r=u*v
                        if r>N:continue
                        vp=min(v,N0//u);rp=u*vp;theta=F(vp,v)
                        require(theta>=F(1,8*J*J),'uniform retained fraction bound')
                        require(1<=rp<=N0 and J*N0<=N,'simultaneous subspace dimension budget')
                        for K in sorted({1,2,3,a0,max(1,a0-1),a0+1,a,2*a+1}):
                            d=choose_d(a0,b0,rp,K);checked+=1
                            x=64*J**3*theta*F(d,K)
                            require(x>=1 or x>=F(a,K) or x*x>=F(N,r*K*K),'universal simultaneous fidelity factor')
                            if v>vp:truncated+=1
                            G=(a0//K)*(b0//K)
                            if K<=a0 and r<=G:
                                require(vp==v and d==K,'complete extraction of every good block');exact+=1
    return {'integer_packing_cases':checked,'truncated_cases':truncated,'fully_extracted_cases':exact}

def labels(size,d):
    out={i:(i//d,i%d) for i in range((size//d)*d)}
    for i in range((size//d)*d,size):out[i]=(size+i,0)
    return out

def local_image(M,a,b,K,d):
    A=labels(a,d);B=labels(b,d);out={}
    for (i,j),x in M.items():
        ai,bi=divmod(i,b);aj,bj=divmod(j,b)
        ki,oi=A[ai];kj,oj=A[aj];li,pi=B[bi];lj,pj=B[bj]
        if ki==kj and li==lj:
            at=(oi*K+pi,oj*K+pj);out[at]=out.get(at,F(0))+x
    return {ij:x for ij,x in out.items() if x}

def check_coherent_code() -> dict:
    pairs=systems=0
    for a,b,d,K in [(5,7,2,3),(6,8,2,2),(7,10,3,5),(4,5,1,3),(8,9,4,4)]:
        A=labels(a,d);B=labels(b,d)
        require(len(A)==a and len(B)==b,'all leftover Kraus branches present')
        code=[[(i*d+t)*b+j*d+t for t in range(d)] for i in range(a//d) for j in range(b//d)]
        phi={(t*K+t,s*K+s):F(1,d) for t in range(d) for s in range(d)}
        target={(t*K+t,s*K+s):F(1,K) for t in range(K) for s in range(K)}
        for i,x in enumerate(code):
            for j,y in enumerate(code):
                dyad={(v,w):F(1,d) for v in x for w in y}
                result=local_image(dyad,a,b,K,d)
                require(result==(phi if i==j else {}),'all coherent code dyads extracted correctly')
                if i==j:require(trace(multiply(result,target))==F(d,K),'squared target overlap convention')
                pairs+=1
        systems+=1
    return {'code_systems':systems,'coherent_dyads':pairs}

def check_scalar_converses() -> dict:
    count=0
    for n in range(2,6):
        p=tuple(F(n-i,n*(n+1)//2) for i in range(n))
        for raw in product(range(4),repeat=n):
            x=sorted((F(j,3) for j in raw),reverse=True);r=sum(y*y for y in x)
            if not r:continue
            f=sum(pi*xi for pi,xi in zip(p,x));tail=1-sum(p[:min(n,int(4*r))])
            require(1-f>=tail/2,'squared-budget prefix error converse')
            for h in (2,3):
                cutoff=F(1,r*h*h);head=sum(pi for pi in p if pi>=cutoff)
                require(f<=head+F(1,h),'information-spectrum fidelity converse')
            count+=1
    return {'scalar_effect_cases':count}

# Exact polynomial identities, indeterminates alpha, H, ell, logZ.
def poly_add(*ps):
    out={}
    for p in ps:
        for m,c in p.items():out[m]=out.get(m,F(0))+c
    return {m:c for m,c in out.items() if c}
def poly_scale(c,p):return {m:c*v for m,v in p.items() if c*v}
def poly_mul(p,q):
    out={}
    for m,c in p.items():
        for n,d in q.items():
            k=tuple(x+y for x,y in zip(m,n));out[k]=out.get(k,F(0))+c*d
    return {m:c for m,c in out.items() if c}
def check_algebra():
    one={(0,0,0,0):F(1)}
    a,H,ell,z=[{tuple(int(j==i) for j in range(4)):F(1)} for i in range(4)]
    D=poly_scale(-1,poly_add(H,ell));Da=poly_add(poly_scale(-1,H),poly_scale(-1,poly_mul(a,ell)),z)
    right=poly_add(Da,poly_mul(poly_add(one,poly_scale(-1,a)),H),poly_scale(-1,z))
    require(poly_mul(a,D)==right,'escort relative-entropy identity')
    hescort=poly_add(poly_scale(-1,poly_mul(a,ell)),z)
    descort=poly_add(poly_mul(poly_add(a,poly_scale(-1,one)),ell),poly_scale(-1,z))
    lhs=poly_add(poly_scale(2,descort),hescort)
    # At alpha=2, 2D(q2||p)+H(q2)=-log Z2.
    reduced={}
    for m,c in lhs.items():
        key=(0,*m[1:]);reduced[key]=reduced.get(key,F(0))+c*(2**m[0])
    reduced={m:c for m,c in reduced.items() if c}
    require(reduced==poly_scale(-1,z),'collision endpoint identity')
    return {'symbolic_polynomial_identities':2}

def run_checks():
    return {'status':'PASS','scope':'Exact finite ancillary identities only; not a proof of the unbounded analytic theorem',
            'schur':check_schur(),'orientation':check_unknown_orientation(),
            'multiplicity_selection':check_multiplicity_selection(),'packing':check_packing(),
            'coherent_channels':check_coherent_code(),'scalar_converses':check_scalar_converses(),
            'algebra':check_algebra(),'checker_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}

def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--report',type=Path)
    args=p.parse_args();report=run_checks();text=json.dumps(report,indent=2)+'\n'
    if args.report:args.report.parent.mkdir(parents=True,exist_ok=True);args.report.write_text(text)
    print(text,end='')

if __name__=='__main__':main()
