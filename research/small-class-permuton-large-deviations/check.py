"""Exact, finite sanity checks, not substitutes for the path asymptotics."""
from itertools import product,permutations,combinations
from collections import Counter
from math import factorial

def require(ok,msg):
    if not ok:raise ArithmeticError(msg)
M=tuple(product(range(2),repeat=2));I=(0,1);A=(I,(1,0),(0,0))
def mul(a,b):return tuple(b[t] for t in a)
def ev(w):
    p=I
    for a in w:p=mul(p,a)
    return p
def flags(w,i,j):
    z=list(w);z[i]=(1,1);z[j]=(1,0)
    return ev(z)
lifts=pairs=0
for n in range(1,7):
    for w in product(A,repeat=n):
        total=ev(w)
        # Enumerate rather than assume suffix unambiguity. Endpoint prefix P and
        # backward suffix 1 enforced, no deterministic reverse automaton assumed.
        states=Counter({(I,total):1})
        for a in w:
            ns=Counter()
            for (p,s),mult in states.items():
                for z in M:
                    if mul(a,z)==s:ns[mul(p,a),z]+=mult
            states=ns
        require(states[total,I]==1,'lift multiplicity')
        lifts+=1
        for cut in range(1,n):
            for i in range(cut):
                for j in range(cut,n):
                    for left,right in [((1,1),(1,0)),((1,0),(1,1))]:
                        p=ev(w[:i]);s=ev(w[i+1:cut]);q=ev(w[cut:j]);t=ev(w[j+1:])
                        actual=list(w);actual[i]=left;actual[j]=right
                        require(ev((p,left,s,q,right,t))==ev(actual),'interblock flagged product')
                        pairs+=1
# All finite edge types in binary-state graph with parallel edges; upper bound
# in lists-of-successors counting, zeros and endpoint imbalances included.
G=((0,0),(0,1),(0,1),(1,0),(1,1))
types=0
def enum(v,k,word):
    if not k:
        counts[tuple(word.count(e) for e in range(5))]+=1
        return
    for e,(a,b) in enumerate(G):
        if a==v:enum(b,k-1,word+(e,))
for k in range(0,11):
    counts=Counter();enum(0,k,())
    for c,num in counts.items():
        bound=1
        for v in range(2):
            out=[c[e] for e,(a,b) in enumerate(G) if a==v]
            factor=factorial(sum(out))
            for vcount in out:factor//=factorial(vcount)
            bound*=factor
        require(num<=bound,'Markov type exceeded multinomial bound')
        types+=1
# Endpoint parity and zero macroscopic phases: arbitrary lengths in a two-loop
# component followed by a deterministic directed 2-cycle. The boundary has h=0.
for N in range(1,22):
    for last in range(2):
        exact=sum(2**a for a in range(N) if (N-1-a)%2==last)
        d={(0,0):1}
        for _ in range(N):
            z=Counter()
            for (c,p),v in d.items():
                if c==0:z[0,0]+=2*v;z[1,0]+=v
                else:z[1,1-p]+=v
            d=z
        require(exact==d.get((1,last),0),'residue zero-flow count')
deletions=0
for n in range(2,8):
    for t in range(1,min(n,3)+1):
        if t==n:continue
        seq=Counter()
        for s in permutations(range(n)):
            old=s[:-t];rank={v:i for i,v in enumerate(sorted(old))}
            small=tuple(rank[v] for v in old);seq[small]+=1;deletions+=1
        require(set(seq.values())=={factorial(n)//factorial(n-t)},'deletion fiber')
print('noninvertible forward/backward lifts:',lifts,'; marked products:',pairs)
print('multinomial path-type checks:',types,'; residue/zero-phase identities: 42')
print('literal deletions:',deletions)
print('PASS')
