"""Independent Fourier-stabilizer, secular polynomial and isolated eigenvalue audit."""
from itertools import product, combinations
from fractions import Fraction as Q
from math import gcd,prod
from random import Random
from sympy import Matrix, I, Rational, Poly, QQ
rng=Random(703114)

def need(cond,desc):
    if not cond: raise ArithmeticError(desc)
def compare(x,y):
    need(len(x)==len(y)>0 and min(x)>=0 and sum(x)==sum(y)>0,"mass or dimension")
    gap=0
    for a,b in zip(sorted(x,reverse=True),sorted(y,reverse=True)):
        gap+=b-a;need(gap>=0,"Ky Fan excess")

def ram(d,k):
    # mu inversion on divisors gives Ramanujan sum for all d, including composite d.
    if d==1:return 1
    return d*int(k%d==0)-sum(ram(t,k) for t in range(1,d) if d%t==0)

def graphs():
    chan=mask=prefix=0
    for d,n in ((2,2),(2,3),(2,4),(3,2),(3,3),(4,2),(4,3),(5,2),(6,2)):
        words=list(product(range(d),repeat=n));pairs=list(combinations(range(n),2))
        mats=list(product(range(d),repeat=len(pairs)))
        if len(mats)>12:mats=[mats[0],mats[-1]]+rng.sample(mats[1:-1],10)
        phi=ram(d,0); rad=[ram(d,k) for k in range(d)]
        kernel=[[rad[sum(a*b for a,b in zip(r,y))%d] for r in words] for y in words]
        for g in mats:
            G=[[0]*n for _ in range(n)]
            for (i,j),h in zip(pairs,g):G[i][j]=G[j][i]=h
            supp=[]
            for r in words:
                supp.append(sum(1<<i for i in range(n) if r[i] or sum(a*b for a,b in zip(r,G[i]))%d))
            P=[Q(0),Q(2,5),Q(1),1+Q(1,2*(d*d-1)),Q(d*d,d*d-1)]
            for ps in [tuple([p]*n) for p in P]+[tuple(P[(s+i)%len(P)] for i in range(n)) for s in range(len(P))]:
                nu=[p.numerator for p in ps];de=[p.denominator for p in ps]
                coeff=[prod(di-ni if (s>>i)&1 else di for i,(di,ni) in enumerate(zip(de,nu))) for s in supp]
                eig=[sum(t*c for t,c in zip(row,coeff)) for row in kernel]
                ref=[phi*prod((d*de[i]-(d-1)*nu[i]) if a==0 else nu[i] for i,a in enumerate(y)) for y in words]
                need(sum(eig)==phi*d**n*prod(de),'Weyl normalization');compare(eig,ref)
                chan+=1;prefix+=len(ref)
            for _ in range(3):
                mu=[rng.randrange(6) for e in range(1<<n)];need(sum(mu)>0,'empty mask law')
                coeff=[sum(m for e,m in enumerate(mu) if not (e&s)) for s in supp]
                eig=[sum(t*c for t,c in zip(row,coeff)) for row in kernel]
                ref=[phi*sum(m*d**(n-e.bit_count()) for e,m in enumerate(mu) if all(a==0 or (e>>i)&1 for i,a in enumerate(y))) for y in words]
                need(sum(eig)==phi*d**n*sum(mu),'mask normalization');compare(eig,ref);mask+=1;prefix+=len(ref)
    return chan,mask,prefix

def polyprod(g):
    z=[Q(1)]
    for h in g:z=[a+h*b for a,b in zip([0]+z,z+[0])]
    return z
def variations(x):
    x=[a>0 for a in x if a]
    return sum(a!=b for a,b in zip(x,x[1:]))
def bipart():
    count=0
    for d in range(2,11):
        for h in [[1]+[0]*(d-1),[1]*d]+[[rng.randrange(0,18) for t in range(d)] for _ in range(8)]:
            if not sum(h):continue
            s=[Q(x,sum(h)) for x in h] # rational Schmidt PROBABILITIES; no rational-root amplitudes required.
            for rho in (Q(1,99*d),Q(1,2*d),Q(1,d)):
                # r=(p-1)/(p/d); solve p=d/(d-r).
                p=Q(d)/(d-rho);a=p/d;b=p-1;c=a-b
                off=[a*a-a*b*(x+y) for i,x in enumerate(s) for j,y in enumerate(s) if i!=j]
                def signs(th):
                    diag=[a*a-2*a*b*x-th for x in s]
                    z=polyprod(diag)
                    for i,x in enumerate(s):
                        sub=polyprod(diag[:i]+diag[i+1:])
                        for j,u in enumerate(sub):z[j]+=b*b*x*u
                    # det(t I+Y-theta I) has all real roots. Both Descartes signs
                    # are exact (sum of sign variations +/- is at most the effective degree).
                    neg=variations(z);pos=variations([u*(-1)**j for j,u in enumerate(z)])
                    mult=next(i for i,u in enumerate(z) if u)
                    need(pos+neg+mult==d,'Descartes degree count')
                    return pos+sum(x>th for x in off),neg+sum(x<th for x in off)
                need(signs(c*c)[1]==0 and signs(a*a)[0]==0 and signs(a*c)[1]<=1,'two-site knot')
                need(sum(off)+sum(a*a-2*a*b*x+b*b*x for x in s)==1,'trace')
                count+=1
    return count

def qubits():
    # Exact complex density matrices. Polynomial roots are enclosed using rational
    # isolating intervals; uncertainty is counted against the claimed inequality.
    samples=0
    for rank in (1,3,8):
        H=Matrix(8,rank,lambda i,j:rng.randrange(-3,4)+I*rng.randrange(-2,3))
        rho=(H*H.H).applyfunc(lambda x:x.expand());rho=rho/rho.trace()
        def erase(e):
            Z=Matrix.zeros(8);bits=[1<<i for i in range(3) if e>>i&1]
            for i in range(8):
                for j in range(8):
                    if (i^j)&e:continue
                    Z[i,j]=sum(rho[(i&~e)|t,(j&~e)|t] for t in range(8) if not (t&~e))/2**len(bits)
            return Z
        masks=[erase(e) for e in range(8)]
        for p in map(Rational,('0','1/17','1/2','1','1001/1000','9/7','4/3')):
            Y=sum((p**e.bit_count()*(1-p)**(3-e.bit_count())*m for e,m in enumerate(masks)),Matrix.zeros(8))
            Y=Y.applyfunc(lambda x:x.expand());need(Y==Y.H and Y.trace()==1,'three-site Hermiticity/trace')
            cp=Poly(Y.charpoly().as_expr(),domain=QQ)
            roots=cp.intervals(eps=Rational(1,10**14));need(sum(m for _,m in roots)==8,'real-root count')
            upper=[b for (a,b),m in reversed(roots) for _ in range(m)]
            lower=[a for (a,b),m in reversed(roots) for _ in range(m)]
            ref=sorted([prod(p/2 if (w>>i)&1 else 1-p/2 for i in range(3)) for w in range(8)],reverse=True)
            for k in range(1,8):need(min(sum(upper[:k]),1-sum(lower[k:]))<=sum(ref[:k]),('exact interval Ky Fan failure',rank,p,k))
            samples+=1
    return samples

if __name__=='__main__':
    # An incorrect orientation must not be accepted even under python -O.
    try:compare([2,0],[1,1])
    except ArithmeticError:pass
    else:raise ArithmeticError('negative control accepted')
    print('Fourier channel, correlated-mask, ordered-prefix counts:',graphs(),flush=True)
    print('Two-site rational secular-polynomial certificates:',bipart(),flush=True)
    print('Three-qubit complex-density rational-root-isolation certificates:',qubits(),flush=True)
