"""Independent exact arithmetic. Reconstruct each ROC polygon, including ties,
then test its area against every threshold triangle and test every ranked sum.
Does not import or call the candidate checker. Python standard library."""
from itertools import accumulate
from random import Random

def need(x,note):
    if not x: raise ValueError(note)

def check(w):
    n=len(w); W=sum(w); v=sorted((W*x for x in w for _ in [0,1]),reverse=True)
    g={}
    for x,a in enumerate(w):
        for y,b in enumerate(w):g[y-x]=g.get(y-x,0)+a*b
    rank=list(accumulate(2*u for u in sorted([*g.values(),0],reverse=True)))
    need(all(a>=b for a,b in zip(rank,accumulate(v))) and rank[-1]==2*W*W and rank[0]>v[0],"ranked masses")
    at=lambda j:w[j] if 0<=j<n else 0
    for k in range(1,n+2):
        x=y=auc2=0; gaps=[0]
        for j in range(n+k):
            dx,dy=at(j-k),at(j)
            auc2+=dx*(2*y+dy);x+=dx;y+=dy; gaps.append(y-x)
        need(x==y==W,"probability scale")
        central=sum(u for d,u in g.items() if -k<d<=k)
        need(auc2-W*W==central,"trapezoidal area and exact tie correction")
        need(all(central>=W*h for h in gaps),"triangle lower bound at each threshold")
        need(max(gaps)==sum(sorted(w,reverse=True)[:k]),"threshold maximizing interval")
    return n+1

rng=Random(19636007); T=steps=0
for n in range(1,33):
    for i in range(20):
        # Integer powers, with random adjacent base-2 slopes in decreasing order.
        H=list(accumulate(sorted((rng.randint(-3,3) for _ in range(n-1)),reverse=True),initial=0)); w=[1<<(h-min(H)) for h in H]
        T+=1; steps+=check(w)
    for w in ([1]*n,[2**j * 3**(n-1-j) for j in range(n)],[3**j * 2**(n-1-j) for j in range(n)]):
        T+=1;steps+=check(w)
w=[1]*10+[10]+[1]*10
a=sum(x*x for x in w)+sum(x*y for x,y in zip(w,w[1:]))
need(a<max(w)*sum(w),"full-support unimodal but not log-concave countercontrol")
print(f"PASS {T} exact laws; {steps} shift polygons, all thresholds/all ranked sums; full-interval unimodal negative control.")
