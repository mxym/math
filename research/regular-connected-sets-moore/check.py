"""Exact local checks, not a proof of the asymptotic theorem. Python standard library."""
from itertools import combinations,product
from math import comb
from collections import defaultdict

def need(x,msg):
    if not x:raise RuntimeError(msg)
def graph(m,cycle):
    G={};cols=range(m)
    for i,j in product(range(4),cols):
        G[i,j]={((i-1)%4,j),((i+1)%4,j)}
        for k in (j-1,j+1):
            if cycle or k in cols:G[i,j].add((i,k%m))
    return G
def connectivity(G,U):
    R=set();Q=[next(iter(U))]
    while Q:
        v=Q.pop()
        if v in R:continue
        R.add(v);Q.extend((G[v]&U)-R)
    return R==U
def local():
    checks=0
    for h in range(4):
        G=graph(h+2,False);I=[v for v in G if 0<v[1]<=h]
        for e in range(min(3,len(I))+1):
            for H in combinations(I,e):
                U=set(G)-set(H);need(connectivity(G,U),'disconnected local interval')
                need(all(G[v]&U for v in G),'undominated local vertex')
                checks+=1
    return checks
def residue(t,s,m):
    H=graph(m,True);E=set()
    def add(x,y):
        e=tuple(sorted((x,y)));need(x!=y and e not in E,'duplicate');E.add(e)
    for x in H:
        for y in H[x]:
            if x<y:
                for a,b in product(range(t),repeat=2):add((x,a),(y,b))
    for i,j,a,b in product(range(4),range(m//2),range(t),range(s)):
        add(((i,j),a),((i,j+m//2),(a+b)%t))
    D=defaultdict(int)
    for x,y in E:D[x]+=1;D[y]+=1
    need(len(D)==4*m*t and set(D.values())=={4*t+s},'degree')
def exact_good(t,m):
    # Integer weights for an exact count of clone subsets satisfying the guard.
    B=2**t;W=[comb(4,e)*(B-1)**(4-e) for e in range(4)]
    G=0
    for pre in product(range(4),repeat=3):
        if sum(pre)>3:continue
        D={pre:W[pre[0]]*W[pre[1]]*W[pre[2]]}
        for j in range(3,m):
            T=defaultdict(int)
            for st,z in D.items():
                for e in range(4-sum(st)):T[st[1:]+(e,)]+=z*W[e]
            D=T
        for st,z in D.items():
            tail=st+pre
            if all(sum(tail[k:k+4])<=3 for k in range(3)):G+=z
    one=sum(comb(16,k)*(B-1)**(16-k) for k in range(4))
    need(G*B**(12*m)>=one**m,'cyclic Harris lower bound')
    need(one>=B**16-comb(16,4)*B**12,'union bound')
    return G
if __name__=='__main__':
    print('local endpoint/gap vertex sets:',local())
    K=0
    for m,t,s in product([10,12],[3,4,5],range(4)):residue(t,s,m);K+=1
    print('simple regular explicit matching checks:',K)
    for t,m in product([1,2,3,5],[10,12]):
        g=exact_good(t,m);print('guard count t,m=',t,m,':',g)
    print('PASS')
