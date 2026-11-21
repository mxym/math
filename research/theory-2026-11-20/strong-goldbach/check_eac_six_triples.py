"""Complete 6-vertex triple-antichain replay; no external packages. Python -O OK."""
from itertools import combinations_with_replacement,permutations
from fractions import Fraction as F
from functools import reduce
from math import gcd
from collections import Counter

def need(b,msg):
    if not b: raise RuntimeError(msg)

def cells():
    Q=list(combinations_with_replacement(range(6),3))
    def antichain(p,c):
        if len(p)==6:
            yield p; return
        for i,x in enumerate(c):
            r=[y for y in c[i+1:] if any(a>b for a,b in zip(x,y))
               and any(a<b for a,b in zip(x,y))]
            if len(p)+1+len(r)>=6:
                yield from antichain(p+(x,),r)
    return list(antichain((),Q))

def null(M):
    a=[list(map(F,row)) for row in M]
    n=len(a[0]);p=[];i=0
    for j in range(n):
        v=next((v for v in range(i,len(a)) if a[v][j]),None)
        if v is None:continue
        a[i],a[v]=a[v],a[i];d=a[i][j];a[i]=[t/d for t in a[i]]
        for v in range(len(a)):
            if v==i:continue
            c=a[v][j];a[v]=[u-c*t for u,t in zip(a[v],a[i])]
        p.append(j);i+=1
        if i==len(a):break
    basis=[]
    for k in range(n):
        if k in p:continue
        b=[F(0)]*n;b[k]=1
        for i,j in enumerate(p):b[j]=-a[i][k]
        basis.append(b)
    return basis

def pgcd(a,b):
    def tr(x):
        while x and not x[-1]:x.pop()
        return x
    a=tr([F(i) for i in a]);b=tr([F(i) for i in b])
    while b:
        rr=list(a)
        while len(rr)>=len(b):
            c=rr[-1]/b[-1];j=len(rr)-len(b)
            for i,t in enumerate(b):rr[i+j]-=c*t
            tr(rr)
        a,b=b,rr
    return tuple(x/a[-1] for x in a) if a else ()

def connected(Q):
    for rev in (False,True):
        S={0}
        for _ in range(6):
            if rev:S|={i for i in range(6) if S.intersection(Q[i])}
            else:S|={j for i in S for j in Q[i]}
        if len(S)!=6:return False
    return True

def run():
    H=cells();need(len(H)==16,'antichain count')
    ctr=Counter();right=Counter();gcds=Counter()
    for edges in H:
        for Q in permutations(edges):
            ctr['permutations']+=1
            if any(i in s for i,s in enumerate(Q)):continue
            ctr['no loop']+=1
            if any(sum(j in Q[i] for i in range(j))>1 for j in range(6)):continue
            ctr['smaller parent']+=1
            if not connected(Q):continue
            ctr['SCC']+=1
            A=[[s.count(i) for i in range(6)] for s in Q]
            R=null(A);C=null(list(zip(*A)))
            need(len(R)==len(C)==1,'corank A')
            v=R[0];c=C[0]
            need(sum(c)==0 and v[1]!=v[0],'null vectors')
            w=[(z-v[0])/(v[1]-v[0]) for z in v]
            need(all(z==int(z) for z in w),'integral offsets')
            w=list(map(int,w));need(w==sorted(set(w)),'increasing shape')
            right[tuple(w)]+=1
            f=[F(0)]*(1+max(w));g=[F(0)]*(1+2*max(w))
            for wi,ci in zip(w,c):f[wi]+=ci;g[2*wi]+=ci
            h=pgcd(f,g)
            need(h in ((-1,1),(-1,0,1)),'unexpected shape gcd')
            gcds[h]+=1
            B=[[int(i==j)-A[i][j] for j in range(6)] for i in range(6)]
            need(not null(B),'singular I-A')
    need(ctr['SCC']==14 and sorted(right.values())==[5,9]
         and sorted(gcds.values())==[3,11],'terminal census')
    print('PASS',len(H),'antichains;',dict(ctr))
    print('Right offsets:',dict(right))
    print('Monic gcd counts [T-1, T^2-1]:',gcds[(-1,1)],gcds[(-1,0,1)])
if __name__=='__main__':run()
