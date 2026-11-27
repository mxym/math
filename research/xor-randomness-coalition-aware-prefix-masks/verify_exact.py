"""Exact GF(2) affine-view comparison and endpoint rank certificates."""

from itertools import combinations, product
from math import comb
from random import Random


def xor_all(xs):
    a=0
    for b in xs:
        a^=b
    return a


def echelon(rows):
    basis={}
    for a in rows:
        while a:
            j=a.bit_length()-1
            if j in basis:
                a^=basis[j]
            else:
                basis[j]=a
                break
    return basis


def contains(basis, v):
    while v:
        i=v.bit_length()-1
        if i not in basis:
            return False
        v^=basis[i]
    return True


def path(n,t):
    return {i:{(i-1,i),(0,i-1),(0,i)} for i in range(1,n+1)}


def intervals(n,t):
    relevant={i:{(i-1,i)} for i in range(1,n+1)}
    edges={}
    def children(a,b):
        if b-a==1:
            return
        mid=(a+b)//2
        edges[(a,b)]=((a,mid),(mid,b))
        children(a,mid)
        children(mid,b)
    children(0,t)
    children(t,n)
    edges[0,n]=((0,t),(t,n))
    near=[w for w in sorted(edges) if w[1]<=t]+[(0,n)]
    far=[w for w in sorted(edges) if w[0]>=t]
    assert len(near)==t and len(far)==n-t-1
    for i,w in enumerate(near+far,1):
        relevant[i].update((w,*edges[w]))
    assert all(len(v)<=4 for v in relevant.values())
    assert all(e<=t or e==n for i in range(1,t+1) for w in relevant[i] for e in w)
    return relevant


def endpoints(C,schedule,n):
    return {e for i in C for w in schedule[i] for e in w}-{0,n}


def candidate_ok(matrices,n,t,schedule):
    for c in range(1,min(t,n-t)+1):
        for J in combinations(range(t+1,n+1),c):
            E=sorted(endpoints(J,schedule,n)-set(range(1,t+1)))
            bad=sum(len(echelon(M[k-t-1] for k in E))<len(E) for M in matrices)
            if bad>=c:
                return False
    return True


def good_sources(C,matrices,n,t,schedule):
    E=sorted(endpoints(C,schedule,n)-set(range(1,t+1)))
    return [d for d,M in enumerate(matrices,1)
            if d not in C and len(echelon(M[k-t-1] for k in E))==len(E)]


def affine_view(C,n,t,schedule,matrices,widths):
    pref={}
    owner=[]
    for d,(M,w) in enumerate(zip(matrices,widths),1):
        start=len(owner)
        owner.extend([d]*(t+w))
        pref[d]=[0]+[1<<(start+i) for i in range(t)]+[r<<(start+t) for r in M]+[0]
        assert len(pref[d])==n+1
    # Each form is (input vector, random tape vector).
    forms=[]
    for k,d in enumerate(owner):
        if d in C:
            forms.append((0,1<<k))
    for d in range(1,t+1):
        for i in range(1,n+1):
            if d!=i and (d in C or i in C):
                forms.append((0,pref[d][i-1]^pref[d][i]))
    for a,b in sorted({w for i in C for w in schedule[i]} | {(0,n)}):
        inp=((1<<b)-1)^((1<<a)-1)
        ran=xor_all(pref[d][a]^pref[d][b] for d in range(1,t+1))
        forms.append((inp,ran))
    return forms,owner


def check_case(n,t,schedule_type,M,widths,exhaustive):
    s=schedule_type(n,t)
    assert candidate_ok(M,n,t,s)
    cases=diffs=all_tapes=some_bad=0
    for h in range(t+1):
        for cs in combinations(range(1,n+1),h):
            C=set(cs)
            good=good_sources(C,M,n,t,s)
            honest=set(range(1,t+1))-C
            cases+=1
            some_bad+=bool(honest-set(good))
            assert good or not honest
            forms,owner=affine_view(C,n,t,s,M,widths)
            if good:
                d=good[0]
                cols=[sum(((y>>i)&1)<<j for j,(_,y) in enumerate(forms))
                      for i,o in enumerate(owner) if o==d]
                B=echelon(cols)
            else:
                # Here the whole tape is held fixed, no one can shift it.
                B={}
                all_tapes+=1
            outside=[i-1 for i in range(1,n+1) if i not in C]
            generators=[(1<<outside[0])^(1<<j) for j in outside[1:]]
            if exhaustive:
                inputs=[xor_all(g for g,b in zip(generators,bits) if b)
                        for bits in product((0,1),repeat=len(generators))]
            else:
                inputs=[0,*generators]
            for delta in inputs:
                assert delta.bit_count()%2==0
                assert not any((delta>>(i-1))&1 for i in C)
                v=sum(((a&delta).bit_count()&1)<<j for j,(a,_) in enumerate(forms))
                assert contains(B,v), (schedule_type.__name__,C,delta)
                diffs+=1
    print(f"{schedule_type.__name__} n={n}, t={t}: {cases} coalitions, "
          f"{diffs} legal input differences {'exhaustive' if exhaustive else '(basis)'}, "
          f"{all_tapes} all-source corrupt, {some_bad} with an honest rank-deficient source")


def no_universal_map():
    n,t,width=16,3,8
    s=path(n,t)
    rng=Random(783)
    for _ in range(10000):
        M=tuple(tuple(rng.randrange(1<<width) for _ in range(n-t-1)) for d in range(t))
        if not candidate_ok(M,n,t,s):
            continue
        cands=[endpoints(J,s,n)-set(range(1,t+1))
               for J in combinations(range(t+1,n+1),t)]
        if all(any(len(echelon(A[k-t-1] for k in E))<len(E) for E in cands) for A in M):
            return n,t,M,(width,)*t
    raise AssertionError("no deterministic replay fixture found")


def numerical_union_check():
    checks=0
    for n in (2,17,64,257,1024):
        for t in sorted({1,n//2,n-1}):
            l=(n-1).bit_length()
            for b in (2,8):
                m=b*t+2*l+2
                terms=[(comb(n-t,c)*comb(t,c),(m-b*c)*c)
                       for c in range(1,min(t,n-t)+1)]
                shift=max(a for _,a in terms)
                numerator=sum(v<<(shift-a) for v,a in terms)
                assert 3*numerator<=(1<<shift)
                checks+=1
    print(f"{checks} exact union-bound sanity checks including endpoint cases")


def poly_mul(a,b):
    q=0
    while b:
        if b&1:
            q^=a
        b>>=1
        a<<=1
        if a&16:
            a^=0b10011
    return q


def explicit_generator_check():
    # F_16 with X^4+X+1, n=12, K=4; output constant coordinate of evaluation.
    def pow1(a,j):
        q=1
        for _ in range(j):
            q=poly_mul(q,a)
        return q
    rows=[0]+[sum((poly_mul(1<<i,pow1(a,j))&1)<<(4*j+i)
                  for j in range(4) for i in range(4)) for a in range(11)]+[0]
    checks=intervals_checked=0
    for k in range(1,5):
        for J in combinations(range(1,12),k):
            assert len(echelon(rows[j] for j in J))==k
            checks+=1
    windows=list(combinations(range(13),2))
    ids=[0]+[1<<k for k in range(11)]+[0]
    for (a,b),(c,d) in combinations(windows,2):
        x,y=rows[a]^rows[b], rows[c]^rows[d]
        p,q=ids[a]^ids[b], ids[c]^ids[d]
        assert tuple(v==0 for v in (x,y,x^y))==tuple(v==0 for v in (p,q,p^q))
        intervals_checked+=1
    print(f"Vandermonde prefixes: {checks} full-rank endpoint subsets, "
          f"{intervals_checked} exact interval-pair laws (including shared endpoints)")


if __name__=="__main__":
    check_case(6,2,path,((1,2,4),(1,2,3)),(3,2),True)
    check_case(7,2,intervals,((1,2,4,8),)*2,(4,4),True)
    check_case(3,2,intervals,((),()),(0,0),True)
    n,t,M,W=no_universal_map()
    check_case(n,t,path,M,W,False)
    assert not candidate_ok(((0,0,0),)*2,6,2,path(6,2))
    print("Negative control: rank-deficient public tuple rejected")
    numerical_union_check()
    explicit_generator_check()
