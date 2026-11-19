from itertools import combinations, product
from collections import defaultdict

def glue(children):
    out=[[]]
    for t in children:
        n=len(out)
        for a in t:
            out.append([v+n for v in a])
        out[0].append(n)
        out[n].append(0)
    return out

leaf=glue([])
def unary(t):
    return glue([t])
fork=glue([leaf,leaf])
R=[unary(glue([unary(leaf),fork])),glue([leaf,unary(unary(unary(fork)))])]
def exact(t):
    n=len(t)
    if sum(map(len,t))!=2*(n-1): raise ValueError("not a tree")
    if max(map(len,t))>3:raise ValueError("degree")
    def dp(u,p):
        roots,all_=1,0
        for v in t[u]:
            if v==p:continue
            a,b=dp(v,u)
            roots*=1+a
            all_+=b
        return roots,roots+all_
    return dp(0,-1)
def literal(t):
    out=[0,0]
    for mask in range(1,1<<len(t)):
        edges=sum((mask>>u&1)*(mask>>v&1) for u,vs in enumerate(t) for v in vs if u<v)
        if edges==mask.bit_count()-1:
            out[0]+=mask&1
            out[1]+=1
    return tuple(out)
assert [literal(t) for t in R]==[(16,40),(16,41)]

def word(ds,es):
    paths=[]
    q=[]
    for d,e in zip(ds,es):
        s,u=17*d,17-d
        path=list(range(len(q),len(q)+s+u+1))
        paths.append(path)
        q.extend([] for _ in path)
        def add(v,w):
            q[v].append(w);q[w].append(v)
        for v,w in zip(path,path[1:]):add(v,w)
        if len(paths)>1:add(paths[-2][-1],path[0])
        b=len(q)
        q.extend([v+b for v in a] for a in R[e])
        add(path[s],b)
    return q

def values(d):
    s,u=17*d,17-d
    p=s+u+1
    return 34+288*d, 40+p*(p+1)//2+16*(s+1)*(u+1)
def base(ds):
    return sum(values(d)[1]+306*((pow(17,j)-1)//16)*values(d)[0] for j,d in enumerate(reversed(ds)))
ct=0
for m in range(1,4):
    for ds in product(range(18),repeat=m):
        es=[(d+i)%2 for i,d in enumerate(ds)]
        t=word(ds,es)
        z=exact(t)[1]
        if z!=base(ds)+sum(es) or len(t)>298*m:raise ValueError((ds,es,z))
        ct+=1
for m in range(1,5):
    B=[base(ds) for ds in product(range(18),repeat=m)]
    actual=max(y-x for x,y in zip(B,B[1:]))
    if actual!=(5032 if m==1 else 46784):raise ValueError(actual)
    if m>1 and min(B)>last_max:raise ValueError("bad cross-length interval")
    last_max=max(B)
print("PASS",ct,"explicit joined degree-three graphs; all lexicographic gaps through four digits; both root gadgets by literal vertex subsets.")
