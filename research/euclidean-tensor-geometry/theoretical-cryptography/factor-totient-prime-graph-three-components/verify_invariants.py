"""Known-prime forest fixtures: check combinatorics and integer polynomial identities."""
from itertools import combinations
from math import gcd, prod, isqrt
from collections import Counter

def isprime(x):
    return x>=2 and all(x%j for j in range(2,isqrt(x)+1))

pool=(13,17,19,23,29,41,47,53,59,79,83,103,107,109,127,139,157,167)
assert all(map(isprime,pool))
shapes=Counter(); edges_checked=0; instances=0; cap_fail=0
for r in range(4,8):
    for ss in combinations(pool,r):
        A=(ss[-1]+ss[0]-1)//ss[0]
        if ss[0]<=A: continue
        parents={q:[p for p in ss if p<q and (q-1)%p==0] for q in ss}
        assert max(map(len,parents.values()))<=1
        roots=[q for q in ss if not parents[q]]
        children={p:[q for q in ss if p in parents[q]] for p in ss}
        ed=sum(map(len,children.values()))
        assert ed==r-len(roots)
        if not ed or len(roots)>3: continue
        shapes[len(roots)]+=1
        coeff={}; root_of={}; C=1
        for q in ss:
            if not parents[q]:
                coeff[q]=(1,0); root_of[q]=q
            else:
                p,=parents[q]; a=(q-1)//p; C*=a
                assert 1<=a<=A
                c,d=coeff[p]; coeff[q]=(a*c,1+a*d); root_of[q]=root_of[p]
            c,d=coeff[q]
            assert c<=A and d<=r*A and c*root_of[q]+d==q
            for p in ss:
                if p<q and root_of[p]==root_of[q]:
                    a,b=coeff[p]
                    assert a*d!=b*c
        edges_checked+=ed
        for exp in ([1]*r,[1+(i%4) for i in range(r)],[1+((2*i+1)%7) for i in range(r)]):
            N=prod(p**e for p,e in zip(ss,exp))
            T=prod(p**(e-1)*(p-1) for p,e in zip(ss,exp))
            g=gcd(N,T); D=N//g; U=T//g
            V=N//gcd(N,pow(D,N.bit_length(),N))
            leaves=[p for p in ss if not children[p]]
            assert D==prod(leaves)
            assert V==prod(p**e for p,e in zip(ss,exp) if p not in leaves)
            assert U==C*prod(p-1 for p in roots)*prod(p**(len(children[p])-1) for p in ss if p not in leaves)
            assert all(D%p==0 if p in leaves else V%p==0 for p in ss)
            instances+=1
        if any(len(children[p])>1 for p in ss): cap_fail+=1
assert all(shapes[j] for j in (1,2,3)) and cap_fail>0
print("supports by component count",*(shapes[j] for j in (1,2,3)))
print("directed edges",edges_checked,"supports with branching",cap_fail,"multiplicity fixtures",instances)
