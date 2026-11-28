#!/usr/bin/env python3
"""Check the order-seven alternating permanental decomposition in exact arithmetic."""
from collections import Counter, defaultdict
from fractions import Fraction as Q
from itertools import combinations, permutations, product
from pathlib import Path
import json
import sys

if not __debug__:
    raise RuntimeError("run ordinary Python without -O")

V = tuple(range(7))
ALL = tuple(permutations(V))
E = V

def parity(p):
    return (-1)**sum(p[i] > p[j] for i in range(len(p)) for j in range(i+1,len(p)))

def cycles(p):
    out=[]
    todo=set(V)
    while todo:
        i=min(todo)
        cyc=[i]
        while p[cyc[-1]]!=i:
            cyc.append(p[cyc[-1]])
        todo.difference_update(cyc)
        out.append(tuple(cyc))
    return out

def kind(cs):
    return ''.join(str(x) for x in sorted(map(len,cs),reverse=True))

TY={}
EPS={}
CTR=Counter()
for p in ALL:
    c=cycles(p)
    TY[p]=k=kind(c)
    CTR[k]+=1
    if k=="7":
        EPS[p]=parity(c[0])
assert len(ALL)==5040 and set(EPS.values())=={-1,1}
assert Counter(EPS.values())==Counter({1:360,-1:360})

def inv(p):
    return tuple(p.index(i) for i in V)

def conjugate(p,g):
    ig=inv(g)
    return tuple(g[p[ig[i]]] for i in V)

for sgn in (-1,1):
    cl={p for p in EPS if EPS[p]==sgn}
    g0=next(iter(cl))
    assert {conjugate(g0,h) for h in ALL if parity(h)==1}==cl
    assert {EPS[inv(p)] for p in cl}=={-sgn}

def constant(col):
    return {k:Q(v) for k,v in col.items()}

def cross(a,k):
    # Then average this fixed cut by ordinary cycle class; its coefficients are
    # invariant under switching the two split classes by an odd permutation of I.
    col=Counter()
    for p in ALL:
        if sum(p[i]>=a for i in range(a))==k:
            col[TY[p]]+=1
    return {z:Q(v,CTR[z]) for z,v in col.items()}

def gp(w,z):
    # conjugate(w)*z in Gaussian integer pairs
    a,b=w
    c,d=z
    return (a*c+b*d,a*d-b*c)

def gram(parameters,vector):
    a,k,ds=parameters
    I=V[:a]
    J=V[a:]
    # Lexicographic partial bijections: domain subset first; ordered target tuple second.
    maps=[dict(zip(u,v)) for u in combinations(I,k) for v in permutations(J,k)]
    assert len(maps)==len(vector) and all(len(u)==2 for u in vector)
    # Rather than iterate all completion choices, use each permutation literally,
    # recovering its two opposite cross-matchings and the residual determinants.
    D={tuple(m.items()):i for i,m in enumerate(maps)}
    r=defaultdict(int)
    t=defaultdict(int)
    for p in ALL:
        alpha=tuple((i,p[i]) for i in I if p[i] in J)
        if len(alpha)!=k:
            continue
        beta=tuple(sorted((p[j],j) for j in J if p[j] in I))
        assert alpha in D and beta in D
        re,im=gp(vector[D[alpha]],vector[D[beta]])
        sign=1
        if ds[0]:
            sign*=parity(tuple(p[i] for i in I if p[i] in I))
        if ds[1]:
            sign*=parity(tuple(p[j] for j in J if p[j] in J))
        z=TY[p]
        r[z]+=sign*re
        t[(z,EPS.get(p,0))]+=sign*im
    assert all(v==0 for (z,s),v in t.items() if z!="7")
    assert t["7",1]==-t["7",-1] and r.get("111111",0)==0
    col={z:Q(v,CTR[z]) for z,v in r.items()}
    col["J"]=Q(t["7",1]-t["7",-1],720)
    return col

def hook3(p):
    # The exterior cube of the standard representation.
    d=[1,0,0,0]
    for a in map(len,cycles(p)):
        if a<=3:
            b=-(-1)**a
            for t in range(3,a-1,-1):
                d[t]+=b*d[t-a]
    return -d[0]+d[1]-d[2]+d[3]

def check_incidence():
    ed=list(combinations(V,2))
    triples=list(combinations(V,3))
    ms2={frozenset(a)for a in combinations(ed,2)if len(set(sum(a,())))==4}
    ms3={frozenset(a)for a in combinations(ed,3)if len(set(sum(a,())))==6}
    assert len(ms2)==len(ms3)==105
    c32=Counter()
    c322=Counter()
    for T in triples:
        other=tuple(x for x in V if x not in T)
        for e in combinations(T,2):
            for f in combinations(other,2):
                c32[frozenset((e,f))]+=1
            for f,g in combinations(combinations(other,2),2):
                if not set(f)&set(g):
                    c322[frozenset((e,f,g))]+=1
    assert set(c32)==ms2 and set(c32.values())=={6}
    assert set(c322)==ms3 and set(c322.values())=={3}
    c7=Counter()
    for p in EPS:
        c=cycles(p)[0]
        eds=tuple(tuple(sorted((i,j)))for i,j in zip(c,c[1:]+c[:1]))
        local=Counter()
        for i in V:
            path=(eds+eds)[i+1:i+7]
            for u in (frozenset(path[::2]),frozenset(path[1::2])):
                local[u]+=1
        assert len(local)==7 and set(local.values())=={2}
        c7.update(local.keys())
    assert set(c7)==ms3 and set(c7.values())=={48}
    print("Exact matching incidences: 6 / 3 / 48")

def evaluate(d):
    if d==["per-1",7]:
        return {k:Q(1) for k in CTR if k!="1111111"}
    if d[0]=="Lieb_cross":
        assert d[1:]==[7,1,1] or d[1:]==[7,2,1] or d[1:]==[7,3,2]
        return cross(*d[2:])
    if d==["matching control","32",-1]:
        return constant({"22111":4,"3211":-1})
    if d==["matching 3","322",-1]:
        return constant({"2221":2,"322":-1})
    if d==["joint 7",3,4,1,-1]:
        return constant({"2221":Q(240,7),"7":3,"J":-4})
    assert d[0]=="gram"
    return gram(*d[1:])

def main():
    target_file=Path(sys.argv[1]) if len(sys.argv)>1 else Path(__file__).with_name("lieb_alternating_seven_certificate.json")
    L=json.loads(target_file.read_text())
    assert L["format"]=="lieb-a7-coefficient-certificate-v1"
    types=L["types"]
    assert types==sorted(k for k in CTR if k!="1111111")+["J"]
    wt=list(map(Q,L["weights"]))
    assert len(wt)==len(L["generators"])==len(L["expected_columns"])==15 and min(wt)>0
    rhs=defaultdict(Q)
    for w,g,record in zip(wt,L["generators"],L["expected_columns"]):
        R=evaluate(g)
        assert not R.get("1111111",0)
        assert [R.get(t,0) for t in types]==list(map(Q,record))
        for t,z in R.items():
            rhs[t]+=w*z
    for p in ALL:
        k=TY[p]
        even=parity(p)==1
        target=1-Q(hook3(p),20)*even-(Q(1,20) if k=="211111" else 0)
        assert rhs[k]==target
    assert rhs["J"]==Q(-2,15) # -(8/3)/20
    assert sum(CTR.values())==5040
    print("Exact rational decomposition:",len(wt),"positive weights,",len(ALL),"group terms, split coefficient",rhs["J"])
    check_incidence()

if __name__=="__main__":
    main()
