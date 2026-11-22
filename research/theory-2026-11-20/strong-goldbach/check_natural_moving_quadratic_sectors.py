"""Exact finite controls for geometry, CRT, determinants, local moments and actual edges."""
from math import gcd,isqrt
from itertools import combinations
from fractions import Fraction as F
from collections import Counter

def need(x):
    if not x: raise ValueError("fixture failed")
def isprime(x):
    return x>1 and all(x%d for d in range(2,isqrt(x)+1))
ps=[i for i in range(2,100) if isprime(i)]
def offsets(A): return [b for b in range(3,A-1,3) if gcd(b*(b+1),A)==1]
def minors(v): return [an*bz-az*bn for (an,az),(bn,bz) in combinations(v,2)]
def loc(v,ex):
    k=len(v)
    for l in ps:
        if l<7 or l in ex: continue
        roots=[{z for z in range(l) if not all((a*n+b*z)%l for a,b in v)} for n in range(l)]
        need(roots[0]=={0} and len({len(z) for z in roots[1:]})==1)
        c=[F(l**k,(l-1)**k)*(1-F(len(z),l)) for z in roots]
        need(sum(x*x for x in c)/l-(sum(c)/l)**2==F(l-1,l*l)*(c[0]-c[1])**2)
def run():
    nout=nin=nzero=local=0
    g=13
    for t,u in [(5,7),(7,11),(11,7)]:
        A,B=g*t*t,g*u*u
        M=A*u*u
        hs=Counter()
        for b in offsets(A):
            for d in offsets(B):
                theta_lo=max(F(4*b+1,4*A),F(4*d+1,4*B))
                theta_hi=min(F(4*b+2,4*A),F(4*d+2,4*B))
                if theta_lo<theta_hi:
                    nout+=1;h=t*t*d-u*u*b;hs[h]+=1
                    need(abs(h)<=t*t+u*u and theta_hi-theta_lo>=F(1,16*A*B))
                    v=[(0,1),(1,-1),(-b,A),(b+1,-A),(-d,B),(d+1,-B)]
                    det=minors(v)
                    cover=[b,b+1,A-b,A-b-1,d,d+1,B-d,B-d-1]
                    cover += [h+t*t*j-u*u*i for i in range(2) for j in range(2)]
                    need(all(det) and all(cover))
                    for l in ps:
                        if l not in [g,t,u] and any(x%l==0 for x in det):
                            need(any(x%l==0 for x in cover))
                    if nout%101==1:loc(v,[g,t,u]);local+=1
                if (b-d)%g:continue
                e=(b+A*((d-b)//g*pow(t*t,-1,u*u)%(u*u)))%M
                need(e%A==b and e%B==d)
                v=[(-e,M),(1+e,-M),((b-e)//A,M//A),(1-(b-e)//A,-M//A),
                   ((d-e)//B,M//B),(1-(d-e)//B,-M//B)]
                det=minors(v)
                raw=[0,1,-b,A-b,-d,B-d]
                if not all(det):
                    need(b==d or A-b==B-d);nzero+=1;continue
                nin+=1
                for l in ps:
                    if l not in [g,t,u]:
                        need(any(x%l==0 for x in det)==(len({s%l for s in raw})!=6))
                if nin%1301==1:loc(v,[g,t,u]);local+=1
        need(not hs or max(hs.values())<=g+1)
    nedge=fw=iv=0
    for N in range(500,2501,4):
        if pow(N,(g-1)//2,g)!=g-1:continue
        pr=[r for r in range(3,N,2) if isprime(r) and isprime(N-r)]
        P=set(pr); edges=[]
        for t in [5,7,11]:
            A=g*t*t
            for r in pr:
                b,y=divmod(A*r,N)
                if 0<b<A-1 and b%3==0 and gcd(b*(b+1),A)==1 and N<4*y<2*N and y in P:
                    need(gcd(N,A)==1 and pow(N,(r-1)//2,r) in [1,r-1])
                    need((pow(N,(r-1)//2,r)==1)!=(pow(N,(y-1)//2,y)==1))
                    edges.append((t,b,r,y))
        for (t,b,r,y),(u,d,s,z) in combinations(edges,2):
            if r==s:fw+=1;need(t!=u and (4*b+1)*N<4*g*t*t*r<(4*b+2)*N)
            if y==z:iv+=1;need(t!=u and (b-d)%g==0)
        nedge+=len(edges)
    need(nout and nin and nzero and fw and iv)
    print("PASS",nout,"forward charts,",nin,"inverse nondegenerate charts,",nzero,
          "inverse proportional collisions rejected,",local,"local variance fixtures;",
          nedge,"actual edges,",fw,iv,"actual forward/inverse collisions")
if __name__=="__main__":run()
