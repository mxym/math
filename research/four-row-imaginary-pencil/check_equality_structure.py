#!/usr/bin/env python3
"""Exact auxiliary checks for the complete imaginary-axis equality proof."""
from pathlib import Path
from fractions import Fraction as F
import hashlib,itertools,json
from quadratic_field import R,C

ROOT=Path(__file__).resolve().parent
PERMS=list(itertools.permutations(range(4)))
def require(ok,message):
    if not ok:raise ValueError(message)

def first_block(data):
    b=data['blocks'][0]
    tuples=list(itertools.product(range(4),repeat=4))
    expected=[t for t in tuples if t.count(0)==2 and t.count(1)==2]
    require(b['subset']==[],'The first block must have no partial transpose')
    require([tuples[k] for k in b['group']]==expected,'Wrong first-block support')
    N=[[C.read(x) for x in row] for row in b['N']]
    require(N==[[C(-1) for _ in range(5)]]+
            [[C(i==j) for j in range(5)] for i in range(5)],'Wrong difference-matrix N')
    L=[[C.read(x) for x in row] for row in b['LDL_L']]
    require(len(L)==5 and all(len(row)==5 for row in L),'Wrong first LDL dimensions')
    require(all(L[i][j]==C(1 if i==j else 0) for i in range(5) for j in range(i,5)),'First LDL factor not unit lower triangular')
    require(len(b['LDL_diagonal'])==5 and all(R(*x).sign()==1 for x in b['LDL_diagonal']),'First Gram factor not strictly positive')

def support_check():
    tested=0
    for mask in range(1<<16):
        rows=[{j for j in range(4) if mask & (1<<(4*i+j))} for i in range(4)]
        cols=[{i for i in range(4) if j in rows[i]} for j in range(4)]
        if not all(len(s)>=2 for s in rows+cols):continue
        if not any(all(p[i] in rows[i] for i in range(4)) for p in PERMS):continue
        tested+=1
        # In this support class some 2+2 product is necessarily nonzero.
        # Equation E2 would then force all six nonzero, hence full proportional
        # columns, analytically impossible for an invertible matrix.
        found=any(all(i in cols[a] if i in J else i in cols[b] for i in range(4))
                  for a,b in itertools.combinations(range(4),2)
                  for J in itertools.combinations(range(4),2))
        require(found,'Invertible support with no singleton and no 2+2 assignment')
    require(tested>0,'Empty support enumeration')
    return tested

def add(a,b):
    c=a.copy()
    for k,v in b.items():c[k]=c.get(k,R())+v
    return {k:v for k,v in c.items() if v}
def scale(a,c):return {k:v*c for k,v in a.items() if v*c}
def mul(a,b):
    c={}
    for i,x in a.items():
        for j,y in b.items():
            k=tuple(u+v for u,v in zip(i,j));c[k]=c.get(k,R())+x*y
    return {k:v for k,v in c.items() if v}
def determinant_and_spectrum():
    beta=R(F(3,2),F(-1,3));B=R(F(9,4));q=beta*beta;h=B-1-q
    require(h==R(F(-4,3),1) and h.sign()==1,'Wrong or nonpositive h')
    require((3*(B-q)-1)*(3*(B-q)-1)-12*q==0,'Extra determinant coefficient is nonzero')
    X={(1,0,0):R(1)};Y={(0,1,0):R(1)};Z={(0,0,1):R(1)}
    XYZ=mul(mul(X,Y),Z)
    d1=add(scale(X,B),scale(add(Y,Z),h))
    d2=add(scale(Y,B),scale(add(X,Z),h))
    d3=add(scale(Z,B),scale(add(X,Y),h))
    z=C(1-q,2*beta);zn=z*z.conj();require(not zn.im,'Non-real absolute square')
    terms=add(add(mul(d1,mul(Y,Z)),mul(d2,mul(X,Z))),mul(d3,mul(X,Y)))
    lhs=add(add(mul(mul(d1,d2),d3),scale(terms,-zn.re)),scale(XYZ,-2*(z*z*z).re))
    U=add(add(add(mul(mul(X,X),X),mul(mul(Y,Y),Y)),mul(mul(Z,Z),Z)),scale(XYZ,-3))
    V=add(mul(add(add(X,Y),Z),add(add(mul(X,Y),mul(Y,Z)),mul(Z,X))),scale(XYZ,-9))
    rhs=scale(add(U,scale(V,3)),B*h*h)
    require(lhs==rhs,'Boundary three-row determinant polynomial failed')
    omega=C(R(F(-1,2)),R(0,F(1,2)));a=R(0,F(1,3));lam=C(0,beta)
    M=[[C(),C(a)*(1-lam),C(a)*(1+lam)],
       [C(a)*(1+lam),C(),C(a)*(1-lam)],
       [C(a)*(1-lam),C(a)*(1+lam),C()]]
    vectors=[[C(1),C(1),C(1)],[C(1),omega,omega*omega],[C(1),omega*omega,omega]]
    eig=[]
    for v in vectors:
        w=[sum((x*y for x,y in zip(row,v)),C()) for row in M]
        e=w[0];require(w==[e*x for x in v],'Fourier eigenvector failed');eig.append(e)
    for i,v in enumerate(vectors):
        for j,w in enumerate(vectors):
            inner=sum((x.conj()*y for x,y in zip(v,w)),C())
            require(inner==C(3 if i==j else 0),'Fourier basis not orthogonal')
    norms=[(e*e.conj()).re for e in eig]
    require(sum(x==B for x in norms)==1 and all((B-x).sign()>=0 for x in norms),'Top Fourier singular value not unique')
    require((B-(1+q)).sign()==1 and (B-R(F(4,3))).sign()==1,'Fourier branch not strictly dominant')
    return {'determinant_monomials':len(lhs),'eigenvalues':[e.data() for e in eig],
            'singular_values_squared':[x.data() for x in norms],'h':h.data()}

def main():
    cert=ROOT/'imaginary_boundary_certificate.json';data=json.loads(cert.read_text())
    first_block(data);count=support_check();details=determinant_and_spectrum()
    bad=json.loads(cert.read_text());bad['blocks'][0]['N'][0][0][0]='0'
    try:first_block(bad)
    except ValueError:pass
    else:raise ValueError('Corrupted equality kernel was accepted')
    bad=json.loads(cert.read_text());bad['blocks'][0]['LDL_L'][0][0]=['0','0','0','0']
    try:first_block(bad)
    except ValueError:pass
    else:raise ValueError('Singular first LDL factor was accepted')
    names=['check_equality_structure.py','quadratic_field.py','imaginary_boundary_certificate.json','EQUALITY.md']
    out={'schema':1,'status':'PASS_EXACT_EQUALITY_AUXILIARY_CHECKS',
         'support_masks_exhausted':1<<16,'invertible_no_singleton_supports_tested':count,
         'first_Gram_difference_columns':5,'three_row_boundary':details,
         'negative_controls_rejected':['corrupted_first_Gram_difference','singular_first_LDL_factor'],
         'source_sha256':{s:hashlib.sha256((ROOT/s).read_bytes()).hexdigest() for s in names},
         'scope':'Exact auxiliary algebra and zero-support enumeration; complete complex-matrix equality proof is EQUALITY.md. No Lean or peer-review claim.'}
    print(json.dumps(out,indent=2))
if __name__=='__main__':main()
