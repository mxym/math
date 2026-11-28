#!/usr/bin/env python3
"""Independent extraction of exact rational A8 coefficients from the raw witnesses."""
from collections import Counter, defaultdict
from fractions import Fraction as Q
from functools import lru_cache
from itertools import combinations, permutations
from pathlib import Path
import json
import sys

if not __debug__:
    raise RuntimeError("run ordinary Python")

V=tuple(range(8))
ALL=tuple(permutations(V))
IDENTITY="1"*8
PSI={"71":"J71","53":"J53"}

def sign(z):
    return (-1)**sum(z[i]>z[j] for i in range(len(z)) for j in range(i+1,len(z)))

def cycles(p):
    live=set(V)
    out=[]
    while live:
        i=min(live)
        c=[i]
        while p[c[-1]]!=i:
            c.append(p[c[-1]])
        live.difference_update(c)
        out.append(tuple(c))
    return sorted(out,key=lambda x:-len(x))

TY={}
EP={}
for p in ALL:
    cs=cycles(p)
    t=''.join(str(len(c)) for c in cs)
    TY[p]=t
    if t in PSI:
        EP[p]=sign(sum(cs,()))

COUNT=Counter(TY.values())
ORDINARY=sorted(COUNT.keys()-{IDENTITY},key=lambda s:tuple(map(int,s)))
TYPES=ORDINARY+list(PSI.values())

def norm(t):
    return t+"1"*(8-sum(map(int,t)))

def check_classes():
    assert len(ALL)==40320 and set(EP.values())=={-1,1}
    even=[p for p in ALL if sign(p)==1]
    assert len(even)==20160
    for t in PSI:
        for k in (-1,1):
            cls={p for p,w in EP.items() if TY[p]==t and w==k}
            assert len(cls)==COUNT[t]//2
            q=next(iter(cls))
            j={tuple(g[q[g.index(i)]] for i in V) for g in even}
            assert j==cls
            assert all(EP[tuple(p.index(i) for i in V)]==-k for p in cls)
    assert tuple(COUNT[k] for k in PSI)==(5760,2688)

def scalar(fun):
    counts=defaultdict(int)
    for p in ALL:
        x=fun(p)
        if x:
            counts[TY[p]]+=x
    return {k:Q(v,COUNT[k]) for k,v in counts.items()}

@lru_cache(None)
def gram(a,k,px,py,vector):
    X=V[:a]
    Y=V[a:]
    maps=[tuple(zip(S,T))for S in combinations(X,k)for T in permutations(Y,k)]
    assert len(vector)==len(maps) and all(len(v)==2 for v in vector)
    idx={l:i for i,l in enumerate(maps)}
    r=defaultdict(int)
    j=defaultdict(int)
    nonsplit=defaultdict(int)
    for p in ALL:
        alpha=tuple((i,p[i])for i in X if p[i]>=a)
        if len(alpha)!=k:
            continue
        beta=tuple(sorted((p[i],i)for i in Y if p[i]<a))
        u,v=vector[idx[alpha]]
        s,t=vector[idx[beta]]
        b=(sign(tuple(p[i]for i in X if p[i]<a)) if px else 1)
        c=(sign(tuple(p[i]for i in Y if p[i]>=a)) if py else 1)
        a0=TY[p]
        r[a0]+=b*c*(u*s+v*t)
        value=b*c*(u*t-v*s)
        if a0 in PSI:
            j[PSI[a0]]+=EP[p]*value
        else:
            nonsplit[a0]+=value
    assert not any(nonsplit.values()) and r.get(IDENTITY,0)==0
    return {**{k:Q(v,COUNT[k])for k,v in r.items()},
            **{PSI[k]:Q(j[PSI[k]],COUNT[k])for k in PSI}}

def sub(p,v):
    return all(p[i]==i for i in V[v:])

def restrict_projects(p,a,b):
    if not sub(p,a+b) or any(p[i]>=a for i in range(a)):
        return None
    x,y=p[:a],p[a:a+b]
    sx,sy=sign(x),sign(y)
    fx,fy=int(x==V[:a]),int(y==V[a:a+b])
    return ((1,sx,1-fx,fx-sx,1-sx),(1,sy,1-fy,fy-sy,1-sy))

def evaluate(g):
    if g in ("triangle MS","33 negative","332 negative"):
        return {"triangle MS":{norm("3"):1,norm("2"):Q(2,3),norm("22"):Q(-4,9)},
                "33 negative":{norm("33"):1,norm("22"):Q(8,3)},
                "332 negative":{norm("332"):1,norm("222"):Q(4,3)}}[g]
    name,*args=g
    if name=="gram":
        a,k,ps=args[0]
        return gram(a,k,*ps,tuple(map(tuple,args[1])))
    if name=="cross":
        v,a,k=args
        return scalar(lambda p:int(sub(p,v) and sum(p[i]>=a for i in range(a))==k))
    if name=="Fischer":
        v,a=args
        return scalar(lambda p:-sign(p) if sub(p,v) and any(p[i]>=a for i in range(a))else 0)
    if name=="per-1":
        (v,)=args
        return scalar(lambda p:int(sub(p,v)and p!=V))
    if name=="per-det":
        (v,)=args
        return scalar(lambda p:(1-sign(p)) if sub(p,v)else 0)
    if name=="prod":
        a,b,i,j=args
        def prod_value(p):
            z=restrict_projects(p,a,b)
            return z[0][i]*z[1][j] if z else 0
        return scalar(prod_value)
    if name=="matching":
        t,s=args
        assert t in ("4","5","44") and s in (-1,1)
        m={"4":("22",Q(2)),"5":("22",Q(32,5)),"44":("2222",Q(12))}[t]
        return {norm(t):Q(s),norm(m[0]):m[1]}
    if name=="joint":
        t,a,b,s,u=args
        assert t=="53" and (a,b) in ((4,3),(12,5)) and s==u==-1
        return {"53":Q(a*s),"J53":Q(b*u),norm("222"):Q(32*(5 if a==4 else 13),5)}
    assert g==["cap","222"]
    return {norm("22"):Q(2),norm("222"):Q(-1)}

@lru_cache(None)
def frobenius(lam,mu):
    # Character extracted from Vandermonde times the cycle power sums.
    d=len(lam)
    target=tuple(lam[i]+d-1-i for i in range(d))
    counts={(0,)*d:1}
    for r in map(int,mu):
        nxt=defaultdict(int)
        for z,m in counts.items():
            for i in range(d):
                x=z[:i]+(z[i]+r,)+z[i+1:]
                if x[i]<=target[i]:
                    nxt[x]+=m
        counts=nxt
    return sum(sign(p)*counts.get(tuple(target[i]-d+1+p[i]for i in range(d)),0)
               for p in permutations(range(d)))

def check_matchings():
    e=tuple(combinations(V,2))
    matching=lambda m:{frozenset(ee)for ee in combinations(e,m)if len(set(sum(ee,())))==2*m}
    m2,m3,m4=(matching(i)for i in (2,3,4))
    assert tuple(map(len,(m2,m3,m4)))==(210,420,105)
    tris=tuple(combinations(V,3))
    c33=Counter()
    c332=Counter()
    c53=Counter()
    c44=Counter()
    for i,T in enumerate(tris):
        X=set(T)
        for W in tris[i+1:]:
            if X.intersection(W):
                continue
            leftover=tuple(sorted(set(V)-X-set(W)))
            for p in combinations(T,2):
                for q in combinations(W,2):
                    c33[frozenset((p,q))]+=1
                    c332[frozenset((p,q,leftover))]+=1
        for p in combinations(T,2):
            for M in m2:
                if not any(X.intersection(edge)for edge in M):
                    c53[M|{p}]+=1
    for U in combinations(V,4):
        if 0 not in U:continue # one representative of each complementary 4+4 split
        W=set(V)-set(U)
        for M in m2:
            if set().union(*map(set,M))!=set(U):continue
            for N in m2:
                if set().union(*map(set,N))==W:
                    c44[M|N]+=1
    assert set(c33)==m2 and set(c33.values())=={12}
    assert set(c332)==set(c53)==m3 and set(c332.values())==set(c53.values())=={6}
    assert set(c44)==m4 and set(c44.values())=={3}
    c4,c5=Counter(),Counter()
    for p in ALL:
        ty=TY[p]
        if ty not in (norm("4"),norm("5")):
            continue
        c=cycles(p)[0]
        ed=tuple(tuple(sorted((i,j)))for i,j in zip(c,c[1:]+c[:1]))
        if len(c)==4:
            c4[frozenset(ed[::2])]+=1
            c4[frozenset(ed[1::2])]+=1
        else:
            sect=Counter()
            for i in range(5):
                r=(ed+ed)[i+1:i+5]
                sect[frozenset(r[::2])]+=1
                sect[frozenset(r[1::2])]+=1
            assert len(sect)==5 and set(sect.values())=={2}
            c5.update(sect.keys())
    assert set(c4)==set(c5)==m2 and set(c4.values())=={4} and set(c5.values())=={32}
    print("Exact matching incidences 12/6/6/3/4/32")

def main():
    fn=Path(sys.argv[1])if len(sys.argv)>1 else Path(__file__).with_name("lieb_alternating_eight_certificates.json")
    obj=json.loads(fn.read_text())
    assert obj["format"]=="lieb-a8-coefficient-certificates-v1" and obj["types"]==TYPES
    check_classes()
    check_matchings()
    assert len(obj["cases"])==2
    for case in obj["cases"]:
        lam=tuple(case["partition"]); D=frobenius(lam,IDENTITY)
        split=case["split"]
        assert (lam,D,split) in (((4,2,1,1),90,"J71"),((3,3,2),42,"J53"))
        rs=Q(case["t"]);gap=Q(case["gap"])
        assert rs*rs>(7 if split=="J71"else 15) and gap==Q(1,20)
        charts=case["generators"]
        assert len(charts)==23
        acc=defaultdict(Q)
        for r in charts:
            wt=Q(r["weight"])
            assert wt>0
            row=evaluate(r["generator"])
            assert not row.get(IDENTITY,0)
            assert [row.get(t,0)for t in TYPES]==list(map(Q,r["coeffs"]))
            for t,u in row.items():
                acc[t]+=wt*u
        for p in ALL:
            ty=TY[p]
            target=1-(Q(frobenius(lam,ty),D)if (8-len(ty))%2==0 else 0)
            if ty==norm("2"):target-=gap
            assert acc[ty]==target
        for t in PSI.values():
            assert acc[t]==(-rs/D if t==split else 0)
        print("Exact A8:",lam,"D",D,"23 positive weights; 40320 monomials,",split,acc[split],"gap",gap)

if __name__=="__main__":
    main()
