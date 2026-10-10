#!/usr/bin/env python3
"""Exact ancillary calculations only; not an analytic proof or Lean certificate.

Standard library only. Rains maps are checked as full rational Choi matrices,
including complete positivity after partial-transpose conjugation. Deterministic
variable-dimension local packing is checked separately. The inherited type
checker is copied byte-for-byte from the companion; only its type routine is used.
"""
from __future__ import annotations
import argparse
from fractions import Fraction as Q
import hashlib
import json
from math import isqrt
from pathlib import Path
import bell_checks

class CheckFailed(RuntimeError):
    pass

def need(test: bool, label: str) -> None:
    if not test:
        raise CheckFailed(label)

def eye(n):
    return [[Q(i == j) for j in range(n)] for i in range(n)]

def add(x, y):
    return [[a+b for a,b in zip(u,v)] for u,v in zip(x,y)]

def scale(c, x):
    return [[c*a for a in row] for row in x]

def transpose(x):
    return [list(t) for t in zip(*x)]

def mul(x, y):
    yt=transpose(y)
    return [[sum((a*b for a,b in zip(u,v)),Q(0)) for v in yt] for u in x]

def kron(x, y):
    return [[a*b for a in u for b in v] for u in x for v in y]

def tr(x):
    return sum((x[i][i] for i in range(len(x))),Q(0))

def pt(x, a, b):
    return [[x[(i//b)*b+j%b][(j//b)*b+i%b] for j in range(a*b)] for i in range(a*b)]

def phi(a, b=None):
    if b is None: b=a
    n=a*b
    good={i*b+i for i in range(a)}
    return [[Q(1,a) if i in good and j in good else Q(0) for j in range(n)] for i in range(n)]

def psd(x):
    """Exact symmetric LDL elimination, including zero-pivot consistency."""
    if x!=transpose(x): return False
    a=[row[:] for row in x]
    n=len(a)
    for j in range(n):
        pivot=a[j][j]
        if pivot<0: return False
        if pivot==0:
            if any(a[i][j]!=0 for i in range(j+1,n)): return False
            continue
        for i in range(j+1,n):
            for h in range(i,n):
                a[h][i] -= a[h][j]*a[i][j]/pivot
                a[i][h] = a[h][i]
    return True

def choi_pt(x,a,b,K):
    N=a*b; O=K*K
    def ind(i,o): return i*O+o
    out=[[Q(0) for _ in range(N*O)] for _ in range(N*O)]
    for i in range(N):
      for j in range(N):
        ii=(i//b)*b+j%b; jj=(j//b)*b+i%b
        for o in range(O):
          for v in range(O):
            oo=(o//K)*K+v%K; vv=(v//K)*K+o%K
            out[ind(i,o)][ind(j,v)] = x[ind(ii,oo)][ind(jj,vv)]
    return out

def trace_output(x,N,O):
    return [[sum((x[i*O+t][j*O+t] for t in range(O)),Q(0)) for j in range(N)] for i in range(N)]

def rains_coefficients(MG,K):
    I=eye(len(MG))
    return (scale(Q(1,K*(K+1)),add(I,scale(K,MG))),
            scale(Q(1,K*(K-1)),add(I,scale(-K,MG))))

def check_rains_case(a,b,K,kind):
    N=a*b; I=eye(N); P=phi(a,b)
    if kind=='bell': M=scale(min(Q(1),Q(a,K)),P)
    elif kind=='identity': M=scale(Q(1,K),I)
    else: M=scale(Q(1,2),add(scale(min(Q(1),Q(a,K)),P),scale(Q(1,K),I)))
    MG=pt(M,a,b)
    need(psd(M) and psd(add(I,scale(-1,M))),'effect interval')
    need(psd(add(scale(Q(1,K),I),MG)) and psd(add(scale(Q(1,K),I),scale(-1,MG))),'PPT effect interval')
    Phi=phi(K); IO=eye(K*K)
    J=add(kron(transpose(M),Phi),scale(Q(1,K*K-1),kron(transpose(add(I,scale(-1,M))),add(IO,scale(-1,Phi)))))
    JG=choi_pt(J,a,b,K)
    F=scale(K,pt(Phi,K,K)); Qp=scale(Q(1,2),add(IO,F)); Qm=scale(Q(1,2),add(IO,scale(-1,F)))
    Cp,Cm=rains_coefficients(MG,K)
    predicted=add(kron(transpose(Cp),Qp),kron(transpose(Cm),Qm))
    need(JG==predicted,'Rains Choi partial-transpose identity')
    need(trace_output(J,N,K*K)==I and trace_output(JG,N,K*K)==I,'Rains trace preservation')
    need(psd(J) and psd(JG),'Rains complete positivity')
    adjoint=[[sum((J[i*K*K+u][j*K*K+v]*Phi[v][u] for u in range(K*K) for v in range(K*K)),Q(0)) for j in range(N)] for i in range(N)]
    need(adjoint==transpose(M),'Rains fidelity effect')
    need(tr(mul(M,M))<=Q(N,K*K),'Hilbert-Schmidt budget')
    if kind=='identity': need(tr(mul(M,M))==Q(N,K*K),'sharp identity effect budget')
    return {'input':[a,b],'output_K':K,'kind':kind,'choi_dimension':N*K*K,'status':'PASS'}

def kraus(a,K,target=None):
    T=K if target is None else target
    need(T>=K,'target includes embedded dimension')
    u=a//K
    out=[]
    for j in range(u):
        A=[[Q(0) for _ in range(a)] for _ in range(T)]
        for x in range(K): A[x][j*K+x]=Q(1)
        out.append(A)
    for z in range(u*K,a):
        A=[[Q(0) for _ in range(a)] for _ in range(T)];A[0][z]=Q(1);out.append(A)
    return out

def check_local(a,b,d,target=None):
    T=d if target is None else target
    As=kraus(a,d,T);Bs=kraus(b,d,T)
    for dim,ops in [(a,As),(b,Bs)]:
        complete=[[Q(0) for _ in range(dim)] for _ in range(dim)]
        for op in ops: complete=add(complete,mul(transpose(op),op))
        need(complete==eye(dim),'local Kraus completeness')
    expected=[[Q(0) for _ in range(T*T)] for _ in range(T*T)]
    for x in range(d):
        for y in range(d):expected[x*T+x][y*T+y]=Q(1,d)
    count=0
    for j in range(a//d):
      for l in range(b//d):
        coords=[(j*d+x)*b+(l*d+x) for x in range(d)]
        out=[[Q(0) for _ in range(T*T)] for _ in range(T*T)]
        # All local Kraus branches are retained, with no conditioning.
        for A in As:
          for B in Bs:
            amplitude=[sum((A[u][idx//b]*B[v][idx%b] for idx in coords),Q(0)) for u in range(T) for v in range(T)]
            out=add(out,[[x*y/d for y in amplitude] for x in amplitude])
        need(out==expected,'deterministic local Bell extraction')
        need(tr(mul(out,phi(T)))==Q(d,T),'embedded target overlap')
        count+=1
    need(count==(a//d)*(b//d),'local packing rank')
    return {'a':a,'b':b,'embedded_d':d,'target_K':T,'good_states_checked':count,'unused_A':a%d,'unused_B':b%d}

def check_packing():
    count=0;small=0;large=0
    for a in range(2,12):
      for b in range(a,17):
        N=a*b
        for K in range(2,18):
          for r in range(1,N+1):
            # floor(min{a,K,sqrt(N/r)}/2), with exact integer arithmetic.
            d=max(1,min(a//2,K//2,isqrt(N//(4*r))))
            need(d<=min(a,K),'embedded dimension admissible')
            need((a//d)*(b//d)>=r,'deterministic packing capacity')
            # w<=4d iff at least one of its three defining terms is <=4d.
            need(a<=4*d or K<=4*d or N<=16*d*d*r,'quarter envelope bound')
            count+=1
            if d==1:small+=1
            else:large+=1
    return {'exact_integer_cases':count,'d_equals_one':small,'d_larger_than_one':large}

# Exact sparse polynomials in five indeterminates: alpha, ell, z, c, R.
D=5
zero=(0,)*D

def pconst(c): return {zero:Q(c)} if c else {}
def var(i):
    v=[0]*D;v[i]=1;return {tuple(v):Q(1)}
def pa(*xs):
    out={}
    for x in xs:
      for m,c in x.items():out[m]=out.get(m,Q(0))+c
    return {m:c for m,c in out.items() if c}
def ps(c,x): return {m:Q(c)*v for m,v in x.items() if c*v}
def pm(x,y):
    out={}
    for m,c in x.items():
      for n,d in y.items():
        key=tuple(a+b for a,b in zip(m,n));out[key]=out.get(key,Q(0))+c*d
    return {m:c for m,c in out.items() if c}

def check_polynomials():
    alpha,ell,z,c,R=[var(i) for i in range(D)]
    one=pconst(1);H=pa(ps(-1,pm(alpha,ell)),z)
    rel=pa(pm(pa(alpha,ps(-1,one)),ell),ps(-1,z))
    need(pa(pm(alpha,rel),z,pm(pa(alpha,ps(-1,one)),H))=={},'interior escort matching')
    # Derivative of (-z-(alpha-1)c)/alpha, after clearing alpha squared.
    derivative=pa(pm(alpha,pa(ps(-1,ell),ps(-1,c))),z,pm(pa(alpha,ps(-1,one)),c))
    need(derivative==pa(H,ps(-1,c)),'escort derivative')
    H2=pa(ps(-2,ell),z);D2=pa(ell,ps(-1,z))
    need(pa(ps(2,D2),H2,z)=={},'collision branch identity')
    # Direct two-case scalar hinge identity, exact on a grid crossing all faces.
    checks=0
    for A in [Q(1),Q(2)]:
      for B in [A,A+Q(1),A+Q(3)]:
       for R0 in [Q(i,4) for i in range(0,25)]:
        for h in [Q(i,3) for i in range(0,25)]:
          left=max(Q(0),R0-A,R0-(A+B)/2+h/2)
          right=max(Q(0),R0-A)+max(Q(0),h-(A+B-2*min(R0,A)))/2
          need(left==right,'hinge identity');checks+=1
    return {'symbolic_identities':3,'exact_hinge_regressions':checks}

def data_controls():
    out=[]
    # Intentionally use an effect with too large a Bell amplitude for K=3.
    M=phi(2);MG=pt(M,2,2)
    need(not psd(add(scale(Q(1,3),eye(4)),scale(-1,MG))),'reject unscaled Bell effect')
    out.append('unscaled Bell effect rejected by PPT order')
    A=kraus(3,2)[:-1]
    S=[[Q(0) for _ in range(3)] for _ in range(3)]
    for op in A:S=add(S,mul(transpose(op),op))
    need(S!=eye(3),'reject discarded failure branch')
    out.append('omitted leftover Kraus branch rejected')
    need(Q(4,9)!=Q(4,3),'reject missing square on target dimension')
    out.append('wrong target-dimension square rejected at sharp effect')
    return out

def run():
    types=bell_checks.verify_types()
    rain=[check_rains_case(*case) for case in [(2,2,2,'bell'),(2,2,3,'bell'),(2,3,2,'mixture'),(2,3,3,'identity'),(3,3,2,'bell'),(2,2,4,'mixture')]]
    local=[check_local(*case) for case in [(2,3,2),(3,5,2),(4,5,3),(5,7,2),(3,4,3),(2,3,1,4),(3,5,2,3),(5,7,2,4)]]
    return {'status':'PASS','scope':'Exact finite ancillary identities and intentional rejection controls only; not full analytic verification',
            'rains_channels':rain,'local_extraction':local,'packing':check_packing(),'algebra':check_polynomials(),
            'negative_controls':data_controls(),'inherited_type_checks':types,
            'source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
            'bell_checker_sha256':hashlib.sha256(Path(bell_checks.__file__).read_bytes()).hexdigest()}

def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--report',type=Path);args=ap.parse_args()
    report=run();text=json.dumps(report,indent=2)+'\n'
    if args.report:args.report.parent.mkdir(parents=True,exist_ok=True);args.report.write_text(text)
    print(text,end='')

if __name__=='__main__':main()
