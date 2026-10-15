"""Exact four-input-copy protocol probes with qutrit intermediate memory.
Known canonical witness is attributed to Tabia–Chen–Hsieh2608.08836v2.
No state outside the original physical Werner family is substituted.
"""
from pathlib import Path
import sympy as sp,itertools,json,datetime
P=Path('/home/mxym/math-breadth-quantum-20261015/research/breadth-quantum-20261015')
lam=sp.Symbol('lambda',real=True);d=3;n=9
digits=list(itertools.product(range(3),repeat=2));index={x:i for i,x in enumerate(digits)}
def swap_resource(slot):
    S=sp.zeros(81)
    for a,b in itertools.product(digits,repeat=2):
        aa=list(a);bb=list(b);aa[slot],bb[slot]=bb[slot],aa[slot]
        S[index[a]*9+index[b],index[tuple(aa)]*9+index[tuple(bb)]]=1
    return S
F1=swap_resource(0);F2=swap_resource(1);R=sp.eye(81)-lam*(F1+F2)+lam**2*(F1*F2)
def code(kind):
    V=sp.zeros(9,3)
    if kind=='diag':
        for i in range(3):V[index[(i,i)],i]=1
    elif kind in ['anti','symoff']:
        for i in range(3):
            j,k=[x for x in range(3) if x!=i]
            V[index[(j,k)],i]=1/sp.sqrt(2);V[index[(k,j)],i]=(-1 if kind=='anti' else 1)/sp.sqrt(2)
    elif kind=='sumcode':
        for i in range(3):
            for a in range(3):V[index[(a,(i-a)%3)],i]=1/sp.sqrt(3)
    assert V.T*V==sp.eye(3)
    return V
def pt(S):
    return sp.Matrix(9,9,lambda row,col:S[(row//3)*3+(col%3),(col//3)*3+(row%3)])

# Sparse vector in interleaved A1 B1 A2 B2 order, retaining exact factors.
u=[];v=[]
for r in [1,2]:
    ur=sp.zeros(9,1);vr=sp.zeros(9,1)
    ur[index[(0,r)]]=ur[index[(r,0)]]=1/sp.sqrt(2)
    vr[index[(0,r)]]=1/sp.sqrt(2);vr[index[(r,0)]]=-1/sp.sqrt(2)
    u.append(ur);v.append(vr)
C=sum((ur*vr.T for ur,vr in zip(u,v)),sp.zeros(9))/sp.sqrt(2)
psi=sp.zeros(81,1)
for a1,a2,b1,b2 in itertools.product(range(3),repeat=4):psi[(a1*3+b1)*9+(a2*3+b2)]=C[a1*3+a2,b1*3+b2]
assert (psi.T*psi)[0]==1 and C.rank()==2
support=[i for i,x in enumerate(psi) if x]
records=[]
for ka,kb in itertools.product(['diag','anti','symoff','sumcode'],repeat=2):
    E=sp.kronecker_product(code(ka),code(kb));S=sp.simplify(E.T*R*E);T=pt(S)
    # Direct sparse contraction avoids building the full polynomial kron.
    val=sp.expand(sum(psi[i]*psi[j]*T[i//9,j//9]*T[i%9,j%9] for i in support for j in support))
    vals={str(x):str(val.subs(lam,x)) for x in [sp.Rational(1,3),sp.Rational(2,5),sp.Rational(49,100),sp.Rational(1,2),sp.Rational(51,100)]}
    rec={'A_code':ka,'B_code':kb,'unnormalized_four_input_copy_witness_polynomial':str(sp.factor(val)),'exact_values':vals,'all_gray_samples_nonnegative':all(val.subs(lam,x)>=0 for x in [sp.Rational(1,3),sp.Rational(2,5),sp.Rational(49,100),sp.Rational(1,2)])}
    records.append(rec);print(json.dumps(rec),flush=True)
(P/'STRUCTURED_MEMORY3.json').write_text(json.dumps({'schema':'finite-qutrit-memory-structured-probe-v1','utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'scope':'Two actual Werner copies compressed by stated local3-by9 maps, followed by an attributed two-copy canonical witness on two independent outputs. This is a four-input-copy restricted protocol, not an arbitrary-copy proof.','canonical_witness_source':'https://arxiv.org/html/2608.08836v2','records':records,'complete_target_solved':False},indent=2)+'\n')
