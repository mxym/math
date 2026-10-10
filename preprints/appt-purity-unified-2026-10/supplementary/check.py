#!/usr/bin/env python3
"""Exact ancillary checks for the APPT multilevel counterexample.

The all-unitary conclusion is the analytic proof in PROOF.md, not a finite
orbit enumeration. No floating-point arithmetic or third-party package is used.
"""
from __future__ import annotations
import argparse
from collections import defaultdict
from fractions import Fraction as F
import hashlib
import itertools
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parent

class CheckFailed(RuntimeError):
    pass

def require(condition: bool, label: str) -> None:
    if not condition:
        raise CheckFailed(label)

# Multivariate integer polynomials, represented by exponent tuples.
NV = 5
ZERO = (0,) * NV

def const(c):
    return {} if not c else {ZERO: F(c)}

def var(i):
    t = list(ZERO); t[i] = 1
    return {tuple(t): F(1)}

def add(*polys):
    out = defaultdict(F)
    for p in polys:
        for e, c in p.items(): out[e] += c
    return {e: c for e, c in out.items() if c}

def scale(c, p):
    return {e: c * v for e, v in p.items() if c * v}

def mul(p, q):
    out = defaultdict(F)
    for e, a in p.items():
        for f, b in q.items():
            out[tuple(x+y for x,y in zip(e,f))] += a*b
    return {e:c for e,c in out.items() if c}

def power(p, n):
    out = const(1)
    for _ in range(n): out = mul(out,p)
    return out

def polynomial_checks():
    m,x,y,T,Z = [var(i) for i in range(NV)]
    b=add(scale(2,m),const(-5))
    pair_sum=add(mul(x,y),mul(add(x,y),T),scale(F(1,2),add(power(T,2),scale(-1,Z))))
    lhs=add(mul(b,add(power(x,2),power(y,2),Z)),scale(-2,pair_sum),
            scale(-4,mul(add(m,const(-4)),mul(x,y))))
    rhs=add(mul(add(scale(2,m),const(-6)),power(add(x,scale(-1,y)),2)),
            scale(2,add(mul(add(m,const(-2)),Z),scale(-1,power(T,2)))),
            power(add(x,y,scale(-1,T)),2))
    require(lhs==rhs,'dimension-uniform physical SOS identity')
    m2=power(m,2);m3=power(m,3);m4=power(m,4)
    f=add(scale(4,m3),scale(-8,m2),scale(-5,m),const(18))
    g=add(scale(4,m4),scale(-16,m3),scale(11,m2),scale(26,m),const(-16))
    cubic=add(scale(4,m3),scale(-16,m2),scale(-5,m),const(26))
    difference=add(scale(4,mul(add(m2,const(-1)),g)),scale(-1,power(f,2)))
    require(difference==mul(add(m,const(-10)),cubic),'infinite purity gap identity')
    require(add(power(add(scale(2,m2),const(1)),2),
                scale(-4,mul(add(m2,const(-1)),add(m2,const(2)))))==const(9),
            'which conjectured candidate is larger')
    shifted=add(scale(4,power(add(m,const(11)),3)),
                scale(-16,power(add(m,const(11)),2)),scale(-5,add(m,const(11))),const(26))
    require(shifted==add(scale(4,m3),scale(116,m2),scale(1095,m),const(3359)),
            'positive-coefficient cubic certificate')
    D=scale(4,m2);k=add(scale(2,m2),scale(-7,m),const(26))
    hi=add(scale(6,m),const(-19));mid=add(scale(2,m),const(-3))
    tr=add(hi,mul(add(k,const(-1)),mid),mul(add(D,scale(-1,k)),b))
    sq=add(power(hi,2),mul(add(k,const(-1)),power(mid,2)),mul(add(D,scale(-1,k)),power(b,2)))
    require(tr==scale(2,f),'infinite trace identity')
    require(sq==scale(4,g),'infinite trace-square identity')
    return {'symbolic_identities':6,'variables':['m','x','y','tail_sum','tail_square_sum'],
            'positive_shifted_cubic':[3359,1095,116,4]}

# Exact sparse rational matrices for a physically attained boundary orbit.
def madd(*terms):
    out=defaultdict(F)
    for c,A in terms:
        for ij,v in A.items(): out[ij] += c*v
    return {ij:v for ij,v in out.items() if v}

def mmul(A,B):
    rows=defaultdict(list)
    for (j,k),v in B.items(): rows[j].append((k,v))
    out=defaultdict(F)
    for (i,j),v in A.items():
        for k,w in rows[j]: out[i,k] += v*w
    return {ij:v for ij,v in out.items() if v}

def trace(A):
    return sum((v for (i,j),v in A.items() if i==j),F(0))

def pt(A,n):
    out={}
    for (i,j),v in A.items():
        ai,bi=divmod(i,n);aj,bj=divmod(j,n)
        out[ai*n+bj,aj*n+bi]=v
    return out

def mv(A,v):
    out=defaultdict(F)
    for (i,j),a in A.items():out[i]+=a*v.get(j,F(0))
    return {i:a for i,a in out.items() if a}

def quad(A,v):
    return sum((a*mv(A,v).get(i,F(0)) for i,a in v.items()),F(0))

def boundary_orbit(delta=24, transpose=True):
    m,n,k=10,38,147;D=m*n
    I={(i,i):F(1) for i in range(D)}
    P={};Q={}
    for i,j in itertools.combinations(range(m),2):
        a=i*n+j;b=j*n+i
        one={(a,a):F(1,2),(b,b):F(1,2),(a,b):F(-1,2),(b,a):F(-1,2)}
        P=madd((1,P),(1,one))
        if (i,j)==(0,1):Q=one
    zero_coordinates=[i*n+j for i in range(m) for j in range(m,n)]
    for a in zero_coordinates[:k-m*(m-1)//2]:P[a,a]=F(1)
    require(mmul(P,P)==P and trace(P)==147,'actual projection rank and idempotence')
    require(mmul(Q,Q)==Q and trace(Q)==1 and mmul(P,Q)==Q,'actual spike subprojection')
    A=madd((15,I),(2,P),(delta,Q))
    psi={i*n+i:F(4 if i<2 else 1) for i in range(m)}
    require(sum(x*x for x in psi.values())==40,'test-vector normalization')
    G=pt(A,n) if transpose else A
    require(pt(pt(A,n),n)==A,'partial-transpose involution')
    return A,G,psi

def explicit_checks():
    D,k=380,147;h,u,b=41,17,15
    Z=h+(k-1)*u+(D-k)*b
    ss=h*h+(k-1)*u*u+(D-k)*b*b
    require(Z==6018 and ss==96300,'density moments and multiplicities')
    purity=F(ss,Z*Z);P1=F(97,36481);P2=F(5,1881)
    t=(9*38+1)//2
    require(t==171 and P1==F(D+8,(D+2)**2),'first conjectured candidate')
    require(P2==F(D*81+40*t,(9*D+2*t)**2),'second conjectured candidate')
    require(purity==F(2675,1006009),'exact counterexample purity')
    require(purity-P1==F(3802,36700214329)>0,'strict gap from first candidate')
    require(purity-P2==F(1630,1892302929)>0,'strict gap from second candidate')
    A,G,psi=boundary_orbit()
    require(trace(A)==Z and trace(mmul(A,A))==ss,'physical orbit has exact spectral moments')
    require(mv(G,psi)=={},'physical partial-transpose null vector')
    require(quad(G,psi)==0,'boundary test expectation')
    ep=F(1,1000);interior=F(1,D)+(1-ep)**2*(purity-F(1,D))
    require(interior==F(1016479028491,382283420000000),'interior purity')
    require(interior-P1==F(679698380171,13946081445020000000)>0,'interior first gap')
    require(interior-P2==F(30523820609,37846058580000000)>0,'interior second gap')
    return {'m':10,'n':38,'projection_rank':147,'eigenvalue_numerators':[41,17,15],
            'multiplicities':[1,146,233],'normalizer':Z,'purity':str(purity),
            'conjectured_candidates':[str(P1),str(P2)],'positive_gaps':[str(purity-P1),str(purity-P2)],
            'physical_orbit_nonzero_entries':len(A),'physical_null_vector_numerator':[4,4]+[1]*8,
            'interior_epsilon':str(ep),'interior_uniform_pt_floor':str(ep/D),
            'interior_purity':str(interior),'interior_gaps':[str(interior-P1),str(interior-P2)]}

def infinite_regressions():
    # These checks are supplementary. The six polynomial identities above,
    # together with their explicit signs in PROOF.md, give the unbounded proof.
    count=0
    for m in range(11,211):
        n=4*m;D=m*n;k=2*m*m-7*m+26;b=2*m-5;mid=b+2;hi=6*m-19
        require(1<k<D,'infinite-family rank range')
        R=m*(m-1)//2;S=m*(m+1)//2
        require(R<=k<=D-S,'attaining witness padding range')
        Z=hi+(k-1)*mid+(D-k)*b
        sq=hi*hi+(k-1)*mid*mid+(D-k)*b*b
        gap=F(sq,Z*Z)-F(1,4*(m*m-1))
        f=4*m**3-8*m*m-5*m+18
        expect=F((m-10)*(4*m**3-16*m*m-5*m+26),4*(m*m-1)*f*f)
        require(gap==expect>0,'infinite-family exact gap regression')
        count+=1
    return count

def negative_controls():
    checks=[]
    A,G,psi=boundary_orbit(delta=25)
    value=quad(G,psi)/F(40*trace(A))
    require(value==F(-2,30095)<0,'changed largest eigenvalue is not APPT')
    checks.append({'name':'largest eigenvalue 42 instead of 41','rejected':True,'physical_expectation':str(value)})
    _,G,psi=boundary_orbit(transpose=False)
    require(quad(G,psi)>0,'missing partial transpose must not pass the null-vector control')
    checks.append({'name':'identity in place of partial transpose','rejected':True,'wrong_test_value':str(quad(G,psi))})
    # A concrete input distinguishes the right SOS coefficients.
    m=10;x=[F(0),F(0),F(1),F(-1)]+[F(0)]*6
    lhs=(2*m-5)*sum(t*t for t in x)-2*sum(x[i]*x[j] for i,j in itertools.combinations(range(m),2))-4*(m-4)*x[0]*x[1]
    bad=(2*m-6)*(x[0]-x[1])**2+sum((x[i]-x[j])**2 for i,j in itertools.combinations(range(2,m),2))+(x[0]+x[1]-sum(x[2:]))**2
    require(lhs!=bad,'changed SOS coefficient must fail')
    checks.append({'name':'tail SOS coefficient 1 instead of 2','rejected':True,'residual':str(lhs-bad)})
    return checks

def run():
    report={'status':'PASS','scope':'Exact algebra, rational spectral gaps and a physical boundary orbit; all-unitary proof is analytic, not finite verification',
            'polynomial_checks':polynomial_checks(),'explicit_counterexample':explicit_checks(),
            'supplementary_dimension_regressions':infinite_regressions(),'negative_controls':negative_controls(),
            'sources':{p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in [ROOT/'PROOF.md',Path(__file__).resolve()]}}
    return report

if __name__=='__main__':
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--report',type=Path)
    args=ap.parse_args();report=run();text=json.dumps(report,indent=2)+'\n'
    if args.report:
        args.report.parent.mkdir(parents=True,exist_ok=True);args.report.write_text(text)
    print(text,end='')
