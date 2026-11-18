"""Exact ancillary checks, standard library only; does not replace analytic proofs."""
from fractions import Fraction as Q
from itertools import combinations
from math import comb, factorial

def ck(cond):
    if not cond: raise RuntimeError("check failed")
# Q[omega] regarded as pairs, omega^2=-1-omega.
def add(x,y): return tuple(a+b for a,b in zip(x,y))
def mul(x,y):
    a,b=x;c,d=y; return a*c-b*d, a*d+b*c-b*d
def conj(x): return x[0]-x[1],-x[1]
def neg(x): return -x[0],-x[1]
def dot(x,y):
    z=(0,0)
    for a,b in zip(x,y):z=add(z,mul(conj(a),b))
    return z
Z=(0,0);I=(1,0);W=[I,(0,1),(-1,-1)]
def n2(z):
    t=mul(z,conj(z));ck(t[1]==0);return t[0]
eye=[[I if i==j else Z for i in range(3)] for j in range(3)]
bases=[eye]+[[[W[(a*x*x+b*x)%3] for x in range(3)] for b in range(3)] for a in range(3)]
norm=[1,3,3,3]
for b,B in enumerate(bases):
    for i,u in enumerate(B):
        for j,v in enumerate(B): ck(dot(u,v)==((norm[b] if i==j else 0),0))
for b,c in combinations(range(4),2):
    for u in bases[b]:
        for v in bases[c]: ck(n2(dot(u,v))*3==norm[b]*norm[c])
costs=[]
for i,j in combinations(range(3),2):
    for m in range(3):
        v=[Z]*3;v[i]=I;v[j]=neg(W[m]);ws=[]
        for bi,B in enumerate(bases):
            ps=[Q(n2(dot(w,v)),2*norm[bi]) for w in B]; ck(sorted(ps)==[0,Q(1,2),Q(1,2)]);ws.append(B[ps.index(0)])
        # Sum of four unit rank-one projectors = 2I - vv*, v unnormalized of squared norm 2.
        for k in range(3):
            for l in range(3):
                lhs=Z
                for w,n in zip(ws,norm):
                    x,y=mul(w[k],conj(w[l]));lhs=add(lhs,(Q(x,n),Q(y,n)))
                rhs=add(((2 if k==l else 0),0),neg(mul(v[k],conj(v[l]))));ck(lhs==rhs)
        hv=[(k*x,k*y) for k,(x,y) in enumerate(v)]
        beta2=Q(n2(dot(ws[3],hv)),6);ck(beta2==Q((i-j)**2,6))
        costs.append(beta2/8)
ck(sorted(costs)==[Q(1,48)]*6+[Q(1,12)]*3)
# Independent entropy kernel check by Laguerre projection. For n>=2 the Euler-constant contribution
# vanishes since L_n is orthogonal to x. int x*log(x)*x^m exp(-x) dx=(m+1)!*(H_{m+1}-gamma).
for n in range(2,33):
    cs=[Q((-1)**m*comb(n,m),factorial(m)) for m in range(n+1)]
    ck(sum(c*factorial(m+1) for m,c in enumerate(cs))==0)
    coeff=sum(c*factorial(m+1)*sum(Q(1,j) for j in range(1,m+2)) for m,c in enumerate(cs))
    ck(coeff==Q(1,n*(n-1)))
ck(8*4097 < 2**16 and Q(999999-16,2) > 512*600)
ck(Q(1536*5,2)<=4096 and Q(5,2)+24**2<600)
print("All exact checks passed: full MUB overlaps, nine Hesse rays × four probabilities, nine zero frames,"
      " leakage 6/48 + 3/12 (counts × coefficients), 31 independent Laguerre moments, coarse exponents.")
