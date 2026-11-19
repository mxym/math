"""Independent marked-ideal DP tests, including positive interior products."""
from random import Random
from collections import Counter,defaultdict
from functools import lru_cache
r=Random(23497)
stat=Counter(); grouped=Counter(); sample=None
def bits(mask):
    while mask:
        q=mask&-mask;yield q.bit_length()-1;mask^=q
def check(P,x,y,z):
    global sample
    n=len(P);full=2**n-1
    pred=[]
    for p in P:
        t=p
        for v in bits(p):t|=pred[v]
        pred.append(t)
    def comp(i,j):return i==j or (pred[i]>>j)&1 or (pred[j]>>i)&1
    I=[i for i in range(n) if not comp(i,y)]
    deg=max((sum(not comp(i,j) for j in I) for i in I),default=0)
    @lru_cache(None)
    def nxt(S):return tuple(i for i in bits(full^S) if not pred[i]&~S)
    @lru_cache(None)
    def tail(S):return sum(tail(S|1<<i) for i in nxt(S)) if S<full else 1
    F=Counter(); states={(0,0,0):1}
    for sz in range(n):
        new=defaultdict(int)
        for (S,rx,ry),c in states.items():
            for i in nxt(S):
                Q=S|1<<i
                if i==z:F[ry-rx,sz+1-ry]+=c*tail(Q)
                else:new[Q,sz+1 if i==x else rx,sz+1 if i==y else ry]+=c
        states=new
    if sum(F.values())!=tail(0):raise ValueError(('bad count',P))
    for (k,l),f in F.items():
        for (i,j),h in F.items():
            a,b=i-k,j-l
            if min(a,b)<max(1,deg):continue
            g=F[i,l]*F[k,j];t=f*h
            if g<t:raise ValueError(('rectangle',P,x,y,z,k,l,i,j))
            stat['positive diagonal products']+=1
            if a==b==1 and k>=2 and l>=2:stat['genuine adjacent interior products']+=1
            if deg>=2:stat['wide products with degree >=2']+=1
            if deg==1 and a==b==1 and k>=2 and l>=2 and g>t and sample is None:
                sample=(tuple(P),x,y,z,k,l,f,F[i,l],F[k,j],h)
    grouped[deg]+=1;stat['posets']+=1
for rep in range(450):
    d=r.randrange(3,6);m=r.randrange(1,6);u=r.randrange(3,6);n=d+m+1+u
    y=d+m;x=r.randrange(d);z=r.randrange(y+1,n)
    P=[0]*n
    for i in range(d):
        for j in range(i):
            if r.randrange(4)==0:P[i]|=1<<j
    for i in range(d,d+m):
        for j in range(d):
            if r.randrange(4)==0:P[i]|=1<<j
        for j in range(d,i):
            if r.randrange(3)==0:P[i]|=1<<j
    P[y]=(1<<d)-1
    for i in range(y+1,n):
        P[i]|=1<<y
        for j in (*range(d,y),*range(y+1,i)):
            if r.randrange(4)==0:P[i]|=1<<j
    check(P,x,y,z)
if not sample or not stat['wide products with degree >=2']:raise RuntimeError('coverage missing')
for k in sorted(stat):print(k+':',stat[k])
print('middle-incomparability maximum-degree histogram:',sorted(grouped.items()))
print('One strict interior sample: predecessor masks, marks, k,l and four entries:',sample)
print('PASS. Counts use exact integers and an unrestricted topological-extension DP, not the filter proof.')
