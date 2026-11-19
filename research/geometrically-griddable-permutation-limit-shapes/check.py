"""Finite independent checks of the canonical path and gridding arguments; standard library."""
from collections import defaultdict
from itertools import combinations, product
from math import comb
def require(a,msg):
    if not a: raise ArithmeticError(msg)
def decode(w,cells,cols,rows):
    n=len(w)
    xx=sorted(range(n),key=lambda t:(cells[w[t]][0],cols[cells[w[t]][0]]*t))
    yy=sorted(range(n),key=lambda t:(cells[w[t]][1],rows[cells[w[t]][1]]*t))
    x={t:i for i,t in enumerate(xx)};y={t:i for i,t in enumerate(yy)}
    pi=tuple(y[t] for t in xx)
    key=(tuple(sum(cells[a][0]==c for a in w) for c in range(len(cols))),
         tuple(sum(cells[a][1]==r for a in w) for r in range(len(rows))))
    return pi,key,tuple(x[t] for t in range(n)),tuple(y[t] for t in range(n))
def contains231(p):return any(p[k]<p[i]<p[j] for i,j,k in combinations(range(len(p)),3))
def check(M,cols,rows,N,avoid):
    A=range(len(M))
    def independent(a,b):return M[a][0]!=M[b][0] and M[a][1]!=M[b][1]
    def scan(w):
        blocked=set()
        for a in w:
            if a in blocked:return False
            blocked={b for b in A if independent(a,b) and (b in blocked or b<a)}
        return True
    previous={};total=grids=perms=marked=retained=0
    for n in range(N+1):
        info={};codes={};g=defaultdict(set)
        for w in product(A,repeat=n):
            pi,key,x,y=decode(w,M,cols,rows)
            if avoid and contains231(pi):continue
            info[w]=pi,key,x,y
            codes.setdefault((pi,key),w) # generated in lex order
            g[pi].add(key)
        current={}
        for w,(pi,H,x,y) in info.items():
            require(scan(w)==(w==codes[(pi,H)]),"lex representative")
            marks=set()
            for G in g[pi]:
                if G<=H:continue
                d=int(G[0]==H[0]); i=next(i for i,(b,c) in enumerate(zip(G[d],H[d])) if b!=c)
                lo=sum(H[d][:i+1]);hi=sum(G[d][:i+1])
                require(lo<hi,"witnessed first improving line")
                marks.update(t for t,pos in enumerate((x,y)[d]) if lo<=pos<hi)
            current[w]=marks
            require((not marks)==(H==max(g[pi])),"canonical exactly when no mark")
            for t,j in product(marks,range(n)):
                if t==j:continue
                require(t-(j<t) in previous[w[:j]+w[j+1:]],"pointed marking fails deletion")
                retained+=1
            marked+=len(marks)
        accepted=sorted(pi for w,(pi,H,*_) in info.items() if scan(w) and not current[w])
        require(accepted==sorted(g),"one path per actual ungridded permutation")
        total+=len(info);grids+=len(codes);perms+=len(g);previous=current
    return total,grids,perms,marked,retained

matrices=[(((0,0),(1,0),(0,1),(1,1)),(1,-1),(1,-1),6),
          (((0,0),(1,1),(2,2)),(1,1,1),(1,1,-1),7),
          (((0,0),(1,0),(1,1)),(1,-1),(-1,1),7),
          (((0,1),(1,0)),(-1,1),(1,1),8)]
sums=[0]*5
for M,cs,rs,N in matrices:
    for restricted in (False,True):
        vals=check(M,cs,rs,N,restricted)
        sums=[v+w for v,w in zip(sums,vals)]
print("Words / distinct griddings / permutations / permitted marked positions / retained-mark deletion checks:",*sums)

# Exact moments for the redundant increasing block: two adjacent increasing direct-sum
# cells followed by one decreasing cell. All but the identity have uniquely recognizable
# total left length j by their first descent; two griddings of the left part may project
# to the same permutation.
for n in range(3,201):
    xs=tuple(range(n-1))
    pairs=tuple((j-i,i) for j in range(n+1) for i in range(j+1))
    require(len(pairs)==comb(n+2,2),"weak compositions")
    require(sum(j for j in xs)==(n-2)*(n-1)//2,"ungridded first moment")
    require(sum(a+b for a,b in pairs)==2*comb(n+2,3),"gridded first moment")
    require(sum(comb(j,2) for j in xs)==comb(n-1,3),"ungridded second moment")
    require(sum(comb(a+b,2) for a,b in pairs)==3*comb(n+2,4),"gridded second moment")
print("198 exact weak-composition checks; typical gridded versus ungridded leading-block mean 2/3 versus 1/2.")
print("PASS (finite checks only).")
