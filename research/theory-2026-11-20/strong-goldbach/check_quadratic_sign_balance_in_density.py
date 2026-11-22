"""Integer/rational checks, not an experimental proof of the analytic estimates."""
from math import gcd, isqrt, prod
from itertools import combinations
from fractions import Fraction as F
from collections import Counter

def need(a):
    if not a: raise ValueError("invalid control")
def prime(x): return x>=2 and all(x%d for d in range(2,isqrt(x)+1))
def signo(n,p):
    z=pow(n,(p-1)//2,p)
    return -1 if z==p-1 else z
def minors(forms): return [a*d-b*c for (a,b),(c,d) in combinations(forms,2)]
def run():
    g=13
    ps=[l for l in range(2,40) if prime(l)]
    actual=forw=inv=local=fmodel=imodel=0
    # Exact signed reversal even with restricted first-half window and traversals which leave it.
    for N in range(60,1250,2):
        if signo(N,g)!=-1:continue
        for h in [1,2]:
            Q={r for r in range(3,N,2) if h*r<N and prime(r) and prime(N-r)}
            for t in [5,7,11]:
                A=g*t*t
                if gcd(A,N)!=1:continue
                ai=pow(A,-1,4*N)
                # Arbitrary nonconstant integer weight on each base point.
                w=lambda x:(x%71+4)*(x%43+1) if x in Q else 0
                s=0
                for r in Q:
                    y=A*r%(4*N); z=ai*r%(4*N)
                    if y in Q:
                        need(signo(N,r)==-signo(N,y)); actual+=1
                    s+=signo(N,r)*w(r)*(w(y)+w(z))
                need(s==0)
    # Geometry: direct rational forward boundaries, modular lattice inverse, determinant coverage.
    for t,u in [(5,7),(7,11),(11,5)]:
        A,B=g*t*t,g*u*u; M=A*u*u
        for h in [1,2]:
            eta=F(1,h); hs=Counter()
            for b in range((A+4*h-1)//(4*h)):
                for d in range((B+4*h-1)//(4*h)):
                    lo=max(F(0),F(4*b,A),F(4*d,B))
                    hi=min(eta,(4*b+eta)/A,(4*d+eta)/B)
                    one=[4*b,4*b+1,A-4*b,A-4*b-1,4*d,4*d+1,B-4*d,B-4*d-1]
                    if hi>lo:
                        V=[(0,1),(1,-1),(-4*b,A),(4*b+1,-A),(-4*d,B),(4*d+1,-B)]
                        delta=one+[t*t*(4*d+j)-u*u*(4*b+i) for i in (0,1) for j in (0,1)]
                        mn=minors(V);need(all(mn)==all(delta))
                        for l in ps:
                            if l not in (2,g,t,u):need(any(x%l==0 for x in mn)==any(x%l==0 for x in delta))
                        hh=t*t*d-u*u*b;hs[hh]+=1
                        need(abs(4*hh)<=max(t*t,u*u) and hi-lo>=F(1,2*A*B)); forw+=1
                    if (b-d)%g:continue
                    e=(b+A*((d-b)//g*pow(t*t,-1,u*u)%(u*u)))%M
                    need(e%A==b and e%B==d)
                    v=(4*(b-e)//A, M//A);s=(4*(d-e)//B, M//B)
                    V=[(-4*e,M),(1+4*e,-M),v,(1-v[0],-v[1]),s,(1-s[0],-s[1])]
                    mn=minors(V);delta=one+[4*(d-b)+c for c in (0,A,-B,A-B)]
                    need(all(mn)==all(delta))
                    for l in ps:
                        if l not in (2,g,t,u):need(any(x%l==0 for x in mn)==any(x%l==0 for x in delta))
                    bad=any(a%l==b0%l==0 for a,b0 in V for l in [t,u])
                    cond=any(z%t==0 for z in (4*b,4*b+1,4*(d-b),4*(d-b)-B)) or any(z%u==0 for z in (4*d,4*d+1,4*(b-d),4*(b-d)-A))
                    need(bad==cond);inv+=1
                    if inv%601==1 and all(mn):
                        for l in [11,17,19]:
                            if l in [t,u,g] or not all(x%l for x in mn):continue
                            for idx in ((0,1),(0,1,2,3),(0,1,4,5),tuple(range(6))):
                                k=len(idx)
                                hit=sum(all((V[i][0]*n+V[i][1]*z)%l for i in idx) for n in range(l) for z in range(l))
                                need(hit==l*l-(1+k*(l-1)));local+=1
            need(not hs or max(hs.values())<=g+1)
    # The forward Haar digit and inverse lifted g-digit have exactly the asserted small factors.
    W=2*3*5*g;H=4*g*W
    for N in range(4,150,2):
        if signo(N,g)!=-1:continue
        for y in [1,7,11,31]:
            if gcd(y*(N-y),W)>1:continue
            target=prod(l-(0 if N%l==0 else 2) for l in (2,3,5,g))
            b0=(-y*pow(4*N,-1,g))%g
            for t in [17,19]:
                A=g*t*t
                n1=n2=0
                for j in range(W):
                    z=(A*y-4*j*N)%W;n1+=gcd(z*(N-z),W)==1
                    b=b0+g*j
                    z=(y+4*b*N)//g*pow(t*t,-1,W)%W;n2+=gcd(z*(N-z),W)==1
                need(n1==n2==target);fmodel+=1;imodel+=1
    need(all((actual,forw,inv,local,fmodel,imodel)))
    print("PASS",actual,"actual reversed arcs;",forw,"forward and",inv,"inverse CRT charts;",local,"local line arrangements;",fmodel,imodel,"finite forward/inverse mixing controls.")
if __name__=="__main__":run()
