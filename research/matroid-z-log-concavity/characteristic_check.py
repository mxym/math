"""Independent exact checker: EPW characteristic recursion, downward counts, no imported project modules."""
from collections import Counter
from functools import cache
from itertools import combinations
from math import comb
from pathlib import Path
import json
@cache
def kl(r):
    if r==0:return {(0,()):1}
    p=Counter()
    # t^r P(t^-1) = sum_F chi_[0,F](t) P_[F,top](t).
    # Read degrees strictly greater than r/2; the F=bottom term has none.
    for f in range(1,r+1):
        for h in range(f+1):
            # Whitney characteristic coefficient mu(0,H) t^(f-h), H <= F
            for m in range(max(1,h)):
                for A in combinations(range(1,h),m):
                    sign=(-1)**(m+1) if h else 1
                    low=A+((h,) if 0<h<f else ())
                    for (j,B),v in kl(r-f).items():
                        i=r-(f-h+j)
                        if not 0<=2*i<r:continue
                        flag=low+((f,) if f<r else ())+tuple(f+b for b in B)
                        p[i,flag]+=sign*v
    return {k:v for k,v in p.items() if v}
def Z(r):
    c=Counter()
    for f in range(r+1):
        for (j,B),v in kl(r-f).items():
            flag=((f,) if 0<f<r else ())+tuple(f+b for b in B)
            c[f+j,flag]+=v
    return {k:v for k,v in c.items() if v}
@cache
def gauss(q,n,k):
    if k<0 or k>n:return 0
    if k==0 or k==n:return 1
    return gauss(q,n-1,k)+q**(n-k)*gauss(q,n-1,k-1)
@cache
def down(q,d,n,S):
    if not S:return 1
    last=S[-1]
    return sum(gauss(q,d,i)*comb(n,last-i)*down(q,i,last-i,S[:-1])
               for i in range(max(0,last-n),min(d,last)+1))
def model(q,k,S):
    n=q**3;r=k+3
    g=down(q,6,n,S)
    if S and S[-1]==r-1:
        g-=q**6*comb(n,k)*(down(q,3,k,S)-down(q,3,k,S[:-1]))
    return g
def evaluate(q,k):
    r=k+3;out=[0]*(r+1)
    for (j,S),v in Z(r).items():out[j]+=v*model(q,k,S)
    return out
def check():
    rows=json.loads(Path(__file__).with_name('certificate.json').read_text())
    for k,q in [(4,103),(3,149),(3,257)]:
        r=k+3;co=evaluate(q,k)
        ref=rows[f'rank{r}-q{q}']
        if not (co==co[::-1] and co[:4]==[1,ref['z1'],ref['z2'],ref['z3']]
                and ref['T2']==co[2]**2-co[1]*co[3]<0):raise ArithmeticError(co)
        print('verified ordinary Z coefficients and strict Turan failure',r,q)
    for r in range(1,10):
        rep=Z(r)
        for d,n in ((r,0),(0,r)):
            co=[sum(v*down(3,d,n,A) for (j,A),v in rep.items() if j==i) for i in range(r+1)]
            expected=[gauss(3,r,i) for i in range(r+1)] if d else [comb(r,i) for i in range(r+1)]
            if co!=expected:raise ArithmeticError((r,co,expected))
    print('EPW flag recursion matches Boolean and projective Z for ranks 1 through 9')
if __name__=='__main__':check()
