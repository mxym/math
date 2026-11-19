"""Exact finite identities: independent-set enumeration and anchored truncations."""
from collections import Counter,deque
from fractions import Fraction as F
from itertools import product
from math import factorial,prod
# Prüfer decoding also used in the square-root companion.
def decode(seq):
 n=len(seq)+2;deg=[1]*n
 for x in seq:deg[x]+=1
 g=[[] for _ in deg]
 for x in seq:
  u=next(i for i,d in enumerate(deg) if d==1)
  g[x].append(u);g[u].append(x);deg[u]=0;deg[x]-=1
 a,b=(i for i,d in enumerate(deg) if d==1);g[a].append(b);g[b].append(a)
 return g

codes=['(()(()())(()((()))))','((())(())((())(())))']
def gadget(code):
    stack=[];g=[]
    for c in code:
        if c=='(':
            v=len(g);g.append([])
            if stack:
                p=stack[-1];g[p].append(v);g[v].append(p)
            stack.append(v)
        else:stack.pop()
    if stack or len(g)!=10 or len(code)!=20:raise ValueError(code)
    return g
def aut(g,v=0,p=-1):
    sub=[aut(g,u,v) for u in g[v] if u!=p]
    return '('+''.join(sorted(a for a,k in sub))+')',prod(k for a,k in sub)*prod(factorial(m) for m in Counter(a for a,k in sub).values())
def stats(g):
    ne=[sum(1<<i for i in N) for N in g];C=[0,0];S=[0,0]
    for a in range(1<<len(g)):
        if any(a>>u&1 and a&d for u,d in enumerate(ne)):continue
        k=a&1;C[k]+=1;S[k]+=a.bit_count()
    return C[1],C[0],S[1],S[0]
def balls(g,v,h,forbidden=-1):
    seen={v};fr=[v]
    for _ in range(h):
        fr=[y for x in fr for y in g[x] if y!=forbidden and y not in seen];seen.update(fr)
    return seen
def test(n):
    for word in product(range(n),repeat=n-2):
        g=decode(word);par=[-2]*n;par[0]=-1;q=[0]
        for v in q:
            for c in g[v]:
                if par[c]==-2:par[c]=v;q.append(c)
        for h in (1,2,3):
            Fv={v:balls(g,v,h) for v in range(n)}
            for K in (2,4,6):
                # f has signed values, chosen to depend on every level of the ball.
                f=lambda S: (-1)**len(S)*len(S) if len(S)<=K else 0
                direct=sum(f(S) for S in Fv.values()); total=0;miss=0
                for v in range(n):
                    a=v
                    for _ in range(h):
                        a=par[a]
                        if a<0: break
                    if a<0:miss+=f(Fv[v]);continue
                    if Fv[v]!=balls(g,v,h,par[a]):raise ValueError('crossed anchor boundary')
                    total+=f(balls(g,v,h,par[a]))
                if direct!=total+miss:raise ValueError((word,h,K))
if __name__=='__main__':
    expected=[(40,130,140,395),(36,117,120,336)]
    for code,want in zip(codes,expected):
        g=gadget(code);v=stats(g)
        if v!=want:raise ValueError((v,want))
        a,b,ap,bp=v;print(code,'size',len(g),'Aut',aut(g)[1],'states',v,'in/out means',F(ap,a),F(bp,b))
    a,b,c,d=expected[0];e,f,g,h=expected[1]
    if a*f!=b*e or F(c,a)-F(g,e)!=F(1,6) or F(d,b)-F(h,f)!=F(1,6):raise ValueError('slot')
    for n in range(2,7):test(n)
    print('Anchored radius/size-cutoff identity: all 1441 labeled trees, n=2..6, h=1,2,3, K=2,4,6: PASS')
