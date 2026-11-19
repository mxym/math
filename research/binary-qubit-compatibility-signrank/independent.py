"""Independent exact checks using the Yu--Liu--Li--Oh biased-qubit inequality.
Standard library only. No assumption that finite checks prove a universal sign-rank bound."""
from fractions import Fraction as F
from itertools import combinations,product
from math import isqrt
def ck(x,s):
    if not x:raise ArithmeticError(s)
def dot(a,b):return sum(x*y for x,y in zip(a,b))
def B(a,b):return 2*a[0]*b[0]-dot(a,b)
def minus(e):return (1-e[0],)+tuple(-v for v in e[1:])
def feat(e):
    f=minus(e); rad=B(e,e)*B(f,f)
    z=F(isqrt(rad.numerator),isqrt(rad.denominator));ck(z*z==rad,'test family radical not rational')
    h=tuple((e[i]*f[j]+e[j]*f[i])/2 for i in range(4) for j in range(i,4))
    return h+(z,)
def kernel(e,f):
    # Minkowski Eq.(55) score by direct bilinear evaluation.
    g,t=minus(e),minus(f)
    return B(e,f)*B(g,t)+B(e,t)*B(g,f)-B(e,g)*B(f,t)+feat(e)[-1]*feat(f)[-1]
def feature_score(e,f):
    g,t=feat(e),feat(f); keys=[(i,j) for i in range(4) for j in range(i,4)]
    flip=(1,-1,-1,-1);te=sum(a*flip[i] for a,(i,j) in zip(g,keys) if i==j)
    tf=sum(a*flip[i] for a,(i,j) in zip(t,keys) if i==j)
    return (2*sum((1 if i==j else 2)*flip[i]*flip[j]*a*b for a,b,(i,j) in zip(g,t,keys))
            -te*tf+g[-1]*t[-1])
def yu(e,f):
    # Eq.(5) of Yu, Liu, Li & Oh. Their Fx^2 = (sqrt(det E)+sqrt(det(I-E)))^2.
    def parameters(e):
        ep=minus(e);x=2*e[0]-1;v=tuple(2*t for t in e[1:])
        fx2=B(e,e)+B(ep,ep)+2*feat(e)[-1]
        return x,v,fx2
    x,v,a=parameters(e);y,w,b=parameters(f)
    if not a or not b: # at least one sharp nontrivial projection: use commutation
        return all(v[i]*w[j]==v[j]*w[i] for i,j in combinations(range(3),2))
    return (dot(v,w)-x*y)**2>=(1-a-b)*(1-x*x/a-y*y/b)
def rank(X):
    t=[r[:] for r in X];r=0
    for j in range(len(t[0])):
        i=next((k for k in range(r,len(t)) if t[k][j]),None)
        if i is None:continue
        t[i],t[r]=t[r],t[i];z=t[r][j]
        for k in range(r+1,len(t)):
            v=t[k][j]/z;t[k]=[a-v*b for a,b in zip(t[k],t[r])]
        r+=1
        if r==len(t):break
    return r
def main():
    dirs=((1,0,0),(0,1,0),(0,0,1),(F(3,5),0,F(4,5)),(F(-2,3),F(2,3),F(1,3)),
          (F(4,9),F(4,9),F(-7,9)),(F(12,13),F(5,13),0))
    probabilities=[(F(0),F(1)),(F(0),F(1,5)),(F(0),F(1,2)),(F(1,2),F(4,5)),
      (F(1,10),F(4,5)),(F(1,2),F(9,10)),(F(1,5),F(9,10)),(F(4,5),F(1))]
    E=[(F(i,2),F(0),F(0),F(0)) for i in range(3)]
    for p,q in probabilities:
        for v in dirs:
            ck(dot(v,v)==1,'unit direction')
            E.append(((p+q)/2,)+tuple(t*(q-p)/2 for t in v))
    # Preserve deterministic inputs in columns; replace them in rows only.
    left=[(F(1,2),F(0),F(0),F(0)) if e[0] in (0,1) else e for e in E]
    neg=[];table=[];zero=0
    for i,(old,e) in enumerate(zip(E,left)):
        row=[]
        for j,f in enumerate(E):
            k=kernel(e,f);h=feat(e)[0];ck(h>0,'strict left coordinate')
            ck(k==feature_score(e,f),'flattened bilinear score')
            ck((k>=0)==yu(old,f),'independent exact biased-pair criterion')
            ck((k>=0)==yu(e,f),'replace deterministic rows')
            if k<0:neg.append(-k/h)
            zero+=k==0;row.append(k)
        table.append(row)
    delta=min(neg)/2;W=[[t+delta*feat(e)[0] for t in row] for e,row in zip(left,table)]
    ck(all((q>=0)==(t>0) and t!=0 for r,s in zip(table,W) for q,t in zip(r,s)),'strict signs')
    ck(rank(W)<=11,'rank after strictification')
    # Character table built recursively, rather than by direct row-dot enumeration.
    H=[[1]]
    for _ in range(7):
        H=[r+r for r in H]+[r+[-x for x in r] for r in H]
    n=len(H)
    ck(all(H[x][y]==(-1)**((x&y).bit_count()) for x,y in product(range(n),repeat=2)),'parity graph')
    ck(all(dot(H[x],H[y])==n*(x==y) for x in range(n) for y in range(x+1)),'orthogonality')
    ck(n>11**2,'Forster contradiction')
    print(f'{len(E)} effects, {len(E)**2} ordered entries checked against independent biased pair criterion (sharp endpoint by commutation); {zero} weak zero cells.')
    print(f'Strict nonzero equivalent signs; exact score rank {rank(W)} (not a sign-rank lower bound).')
    print(f'Order {n} Sylvester table, full parity matching and orthogonality, {n}>11^2. PASS')
if __name__=='__main__':main()
