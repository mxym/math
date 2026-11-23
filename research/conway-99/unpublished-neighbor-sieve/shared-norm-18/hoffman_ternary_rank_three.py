from itertools import product, combinations

from pathlib import Path
from fractions import Fraction
import json
A=list(product(range(3),repeat=3))
TT=[
(1, 0, 2, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 0, 2, 1, 1, 1, 1, 1, 1, 1, 0),
(2, 0, 0, 0, 0, 1, 1, 1, 2, 0, 1, 1, 0, 1, 1, 1, 1, 0, 1, 1, 1, 1, 0, 2, 1, 1, 1),
(2, 0, 0, 0, 0, 1, 1, 2, 1, 0, 0, 2, 1, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1),
(2, 0, 1, 0, 0, 1, 1, 1, 1, 0, 0, 1, 2, 1, 0, 1, 1, 0, 1, 1, 1, 1, 1, 0, 2, 1, 1),
(3, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 2)]


V=[v for v in A if any(v) and next(x for x in v if x)==1]
VV=A[1:]  # all 26 nonzero vectors in lexicographic order
vi={v:i for i,v in enumerate(V)}
ai={v:i for i,v in enumerate(A)}
def dot(v,w): return sum(a*b for a,b in zip(v,w))%3
def norm(v):
    return v if next(x for x in v if x)==1 else tuple((-x)%3 for x in v)
def cols_orbits():
    # For each GL(3,3) matrix, one permutation on vectors and one on directions.
    vperm=[];pperm=set()
    for u,v,w in product(VV,repeat=3):
        det=u[0]*(v[1]*w[2]-v[2]*w[1])-u[1]*(v[0]*w[2]-v[2]*w[0])+u[2]*(v[0]*w[1]-v[1]*w[0])
        if not det%3: continue
        ims=[(dot(x,u),dot(x,v),dot(x,w)) for x in A]
        vperm.append(tuple(ai[x] for x in ims))
        pperm.add(tuple(vi[norm(ims[ai[x]])] for x in V))
    assert len(set(vperm))==11232 and len(pperm)==5616
    return vperm,pperm

def high_representatives(z,pperm):
    unset=set(combinations(range(13),3*z-1))
    while unset:
        P=min(unset)
        yield P
        unset.difference_update(tuple(sorted(s[i] for i in P)) for s in pperm)

def generated(z,pperm):
    M=tuple(tuple((None,1,-1)[x] if x else 0 for x in (dot(f,v) for v in V)) for f in V)
    assert all(sum(a*b for a,b in zip(u,v))==9*(u==v) for u in M for v in M)
    for H in high_representatives(z,pperm):
        low=tuple(i for i in range(13) if i not in H)
        ms=tuple(2-z+sum(M[i][j]==0 for i in H) for j in range(13))
        if min(ms)<0: continue
        assert sum(ms)+z==22
        for eps in product((1,-1),repeat=len(low)):
            nums=tuple(sum(e*M[i][j] for e,i in zip(eps,low)) for j in range(13))
            if any(v%3 for v in nums): continue
            ds=tuple(v//3 for v in nums)
            if any(abs(d)>m or (m+d)%2 for m,d in zip(ms,ds)): continue
            Q=[0]*27; Q[0]=z
            for v,m,d in zip(V,ms,ds):
                Q[ai[v]]=(m+d)//2
                Q[ai[tuple((-x)%3 for x in v)]]=(m-d)//2
            yield tuple(Q)

def verify_orbits():
    vp,pp=cols_orbits()
    full={}
    sizes=[]; reps=[]
    for idx,T in enumerate(TT):
        orbit={tuple(T[i] for i in perm) for perm in vp}
        sizes.append(len(orbit))
        assert not set(full)&orbit
        full.update((v,idx) for v in orbit)
    assert sizes==[5616,5616,5616,702,1404]
    for z in range(1,5):
        reps.append(tuple(sorted({full[v] for v in generated(z,pp)})))
    assert reps==[(0,),(1,2,3),(4,),()]
    print("Complete rank-three decks by zero-column count: 1, 3, 1, 0.")

def verify_design(T,proof):
    labels=[i for i,n in zip(A,T) for _ in range(n)]
    assert len(labels)==22
    C=[S for S in combinations(range(22),4)
       if all(sum(labels[i][j] for i in S)%3==0 for j in range(3))]
    pp=sorted({x for S in C for x in combinations(S,2)})
    tt=sorted({x for S in C for x in combinations(S,3)})
    ix2={v:i for i,v in enumerate(pp)}
    ix3={v:len(pp)+i for i,v in enumerate(tt)}
    assert len(pp)==231
    rows=[tuple(ix2[v] for v in combinations(S,2))+tuple(ix3[v] for v in combinations(S,3)) for S in C]
    def sig(y):
        w=[0]*(len(pp)+len(tt))
        for i,a in y:
            assert 0<=i<len(w) and type(a) is int and a and not w[i]
            w[i]=a
        assert min(w[len(pp):])>=0
        return (sum(w[:len(pp)])*2+sum(w[len(pp):]), [sum(w[i] for i in rr) for rr in rows])
    pair,certs=proof
    if pair is None:
        assert len(certs)==1
        b,y=sig(certs[0])
        assert b<0 and all(x>=0 for x in y)
        return (len(C),b)
    assert len(pair)==2 and tuple(pair) in ix2
    js={i for i,S in enumerate(C) if set(pair)<=set(S)}
    assert {j for j,d,y in certs}==js and len(certs)==len(js)
    bounds=[]
    for j,d,y in certs:
        b,v=sig(y)
        assert type(d) is int and d>0 and 0<=b<d and v[j]>=d and min(v)>=0
        bounds.append((b,d))
    return (len(C),len(js),max(Fraction(b,d) for b,d in bounds))

def main(data=None):
    verify_orbits()
    if data is None:
        data=json.loads(Path(__file__).with_name("hoffman_ternary_rank_three.json").read_text())
    assert len(data)==len(TT)==5
    S=[verify_design(T,p) for T,p in zip(TT,data)]
    assert S==[(273,6,Fraction(900193,1000000)),(279,-999804),
               (279,5,Fraction(900206,1000000)),(279,-999826),(285,-999824)]
    print("Five literal design exclusions checked (6/5 caps and 3 direct rows).")
    print("All ternary kernels have dimension at most two; the 22-by-77 incidence rank is at least 20.")
if __name__=="__main__":
    main()
