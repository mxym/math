"""Exact rational certificate examples. No floating-point roots, logs or external packages."""
from fractions import Fraction as F
from itertools import product
from math import prod

def ck(x):
    if not x:
        raise ArithmeticError("exact check failed")

def bernoulli(k):
    N=len(k)
    c=k[0]; f=c/(1-c)
    p=[(v-u)/v for u,v in zip([F(0)]+k,k)]
    x=[F(1)]*N
    for j in range(N-2,-1,-1):
        x[j]=x[j+1]*(1-c/k[j+1])
    # Bellman recursion: all possible holding states, with or without the new offer.
    held=[F(0)]+x; V=held[:]
    for j in range(N-1,-1,-1):
        V=[(1-p[j])*V[h]+p[j]*max(V[h],V[j+1]-f*z) for h,z in enumerate(held)]
    M=sum((b-a)*u for a,b,u in zip([F(0)]+k,k,x))
    O=1-f*sum(x[:-1]); ck(V[0]==O<=M<=1)
    r=[a/b for a,b in zip(k,k[1:])]
    ck(M==1-sum(t*(y-z) for t,y,z in zip(k,x[1:],x)))
    ck((M-O)/f==sum(z-(1-c)*t*y for z,t,y in zip(x,r,x[1:])))
    return x,r,(1-O/M)/f

def below_plus_const(c,m,loss,K):
    # loss + K >= m(1-c^(1/m)), via exact arithmetic on nonnegative rationals.
    z=1-(loss+K)/m
    return z<=0 or z**m<=c

nh=ng=tail=0
for N in (2,3,4,5,7,9,13,17,20,26,32):
    for d in (F(1),F(4,3),F(2),F(4)):
        m=N-1; c=1/(N*N*d**m)
        k=[c*j*j*d**(j-1) for j in range(1,N+1)]
        ck(k[-1]==1 and all(a<b for a,b in zip(k,k[1:])))
        x,r,loss=bernoulli(k)
        ck(below_plus_const(c,m,loss,8)); nh+=1
        for i in range(m):
            ck(1-x[i+1]<=1/(d**(i+1)*(i+2)));tail+=1
        if d==1:
            # N is exactly the cut-off; the same normalized instance may be padded.
            for bigger in (N+1,2*N,4*N):
                ck(below_plus_const(c,bigger-1,loss,11))
    for r0 in (F(1,17),F(2,19),F(2,3)):
        m=N-1;c=r0**m
        k=[r0**j for j in range(m,-1,-1)]
        x,r,loss=bernoulli(k)
        ck(loss>=m*(1-r0)*(1-r0/(1-r0))-r0/(1-r0))
        ng+=1

# Exogenous threshold ties; enumerate all law/coin outcomes directly from rational measures.
counts=histories=0
laws=[[(0,F(1,3)),(1,F(2,3))],[(1,F(1,2)),(3,F(1,2))],[(0,F(1,4)),(1,F(1,2)),(2,F(1,4))],[(1,F(1))]]
for N in (2,3,4,5):
    for ix in range(10):
        rows=[laws[(ix+3*j+j*j+(ix//2)*j)%4] for j in range(N)]
        for tau in (F(1,4),F(2,3),F(1)):
            T=1
            joint=[]
            for law in rows:
                out=[]
                for x0,p in law:
                    b=(F(x0>T) if x0!=T else tau)
                    if b:out.append((x0,1,p*b))
                    if b<1:out.append((x0,0,p*(1-b)))
                joint.append(out)
            pp=[sum(p for x0,h,p in row if h) for row in joint]
            c=prod(1-p for p in pp)
            if not 0<c<1:continue
            M=fee=miss=F(0)
            for outcome in product(*joint):
                histories+=1
                q=prod(p for _,_,p in outcome); z=max(x0 for x0,_,_ in outcome)
                M+=q*z
                hold=None
                for x0,h,_ in outcome:
                    if h and (hold is None or x0>hold):
                        if hold is not None:fee+=q*hold
                        hold=x0
                if hold is None:miss+=q*z
                else:ck(hold==z)
            ck(miss<=c*M and fee<=sum(pp[:-1])*M)
            ck((1-sum(pp[:-1])/(N-1))**(N-1)>=c)
            counts+=1
print(f"PASS: exact independent Bellman comparisons, tilted quadratic meshes: {nh}; geometric meshes: {ng}")
print(f"PASS: individual weighted-tail inputs: {tail}; padded-horizon comparisons: 33")
print(f"PASS: threshold/tie laws: {counts}; fully enumerated joint outcomes: {histories}")
