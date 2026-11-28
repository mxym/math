#!/usr/bin/env python3
"""Reconstruct shares and test equality of the complete view measures."""
from collections import Counter,deque
from itertools import product

def words(n): return list(product((0,1),repeat=n))
def endpoints(l,branches): return [(i,(i+1)%l) for i in range(l)]+list(branches)

def classify(l,branch,X):
    E=endpoints(l,branch)
    n=len(X[0])
    inc=[[j for j,e in enumerate(E) if i in e] for i in range(n)]
    P={j for j,(a,b) in enumerate(E) if len({x[a]^x[b] for x in X})==1}
    A={i for i in range(n) if len({x[i] for x in X})==2}
    U={i for i in A if all(j not in P for j in inc[i])}
    R={i for i in U if i<l and len(inc[i])==2}
    F=set(range(l))-R
    if any(len(inc[i])==1 for i in U): return 0,None
    if not U: return 1,None
    cut=next((i for i,(a,b) in enumerate(E[:l]) if a in F and b in F),None)
    if cut is not None: return 2,('cut',cut)
    Z=X[0]
    delta=[[x[i]^Z[i] for i in range(l)] for x in X]
    for c in product((0,1),repeat=len(F)):
        B=R|{v for v,b in zip(sorted(F),c) if b}
        if all(sum(x[i] for i in B)%2==0 for x in delta):
            return 2,('cycle',B)
    for ss in product((1,-1),repeat=len(F)):
        es={i for i,s in zip(sorted(F),ss) if s<0}
        if any(sum(x[i] for i in es)%2 for x in delta):continue
        for bb in product(*( (1,2) if i in R else (0,1,2) for i in range(l))):
            if all(sum((-1)**sum(x[j] for j in es if j>i)*bb[i]*x[i]
                       for i in range(l))%3==0 for x in delta):
                return 3,(es,bb)
    return 4,None

def constructed(l,branch,X,claim=None):
    guess,M=classify(l,branch,X)
    if claim is not None: assert claim==guess,(l,branch,guess,M,claim)
    if not guess:return 0,len(X)
    E=endpoints(l,branch); n=len(X[0]); Z=X[0]
    inc=[[j for j,e in enumerate(E) if i in e] for i in range(n)]
    pair={j for j,(a,b) in enumerate(E) if len({x[a]^x[b] for x in X})==1}
    U={i for i in range(n) if len({x[i] for x in X})==2 and set(inc[i]).isdisjoint(pair)}
    rigid={i for i in U if i<l and len(inc[i])==2}
    q={}
    if guess==2:
        mode,param=M
        selected=set(range(len(E)))-pair
        if mode=='cut':selected.discard(param)
        for e,(v,w) in enumerate(E):
            if e in selected:q[v,e]=q[w,e]=0
        if mode=='cycle':
            for v in param:q[v,v]=1
        for v in U:
            es=[j for j in inc[v] if j in selected]
            if len({q[v,e] for e in es})<2:
                t=next((j for j in es if mode=='cut' or v>=l or j>=l),None)
                assert t is not None
                q[v,t]=1
    def share(x,r):
        u=[a^b for a,b in zip(x,Z)]
        z=[x[a] if j in pair else 0 for j,(a,b) in enumerate(E)]
        if guess==1:return z
        if guess==2:
            potentials={}
            for i in range(n):
                if i in potentials:continue
                potentials[i]=0
                Q=deque([i])
                while Q:
                    a=Q.popleft()
                    for e in inc[a]:
                        if (a,e) not in q:continue
                        v,w=E[e]
                        b=v^w^a
                        pot=potentials[a]^q[a,e]*u[a]^q[b,e]*u[b]
                        if b in potentials:
                            assert potentials[b]==pot
                        else:
                            potentials[b]=pot
                            Q.append(b)
                        z[e]=r^potentials[a]^q[a,e]*u[a]
            return z
        # Cycle labels followed by parent-before-child off-cycle propagation.
        if guess==3:
            es,bb=M; t=r
            for i in range(l):
                if u[i]:
                    t=(((-1)**(i in es))*t+bb[i])%3
                z[i]=t
            assert t==r
            ref=[z[i-1 if i else l-1] for i in range(l)]
            # Only rigid vertices need to decode from the cycle itself.
            needs=set(U)-rigid
        else:
            # Use a reversed coordinate presentation on attached triangles too.
            if l>=4:
                t=[(sum(x[2:l])%2)|(2*x[0]),2*x[1],x[2]|(2*(x[0]^x[1]))]+list(x[3:l])
            else:
                assert 0 not in rigid and rigid=={1,2}
                t=[x[2]|(2*x[1]),2*x[1],x[2]]
            v=r
            full=[]
            for i,s in enumerate(t):
                v^=s
                full.append(v)
                z[i]=v>>1 if i==0 else v&1 if i==2 else v
            assert v==r
            ref=[]
            for i in range(l):
                j=(i-1)%l
                if i not in (0,2):ref.append(full[i])
                elif j not in (0,2):ref.append(full[j])
                else:ref.append(z[2]|(z[0]<<1))
            needs={i for i in U if i>=l or (i==0 and l==3)}
        sent=set()
        ref.extend([r]*(n-l))
        for e,(a,b) in enumerate(branch,l):
            if e in pair:continue
            mark=(a in needs and a not in sent)
            if mark: sent.add(a)
            if guess==3:z[e]=(ref[a]+int(mark)*x[a])%3
            else:z[e]=ref[a]^(int(mark)*x[a])
            ref[b]=z[e]
        assert needs==sent,(needs,sent)
        return z
    D={}
    for x in X:
        labels=[share(x,r) for r in range(guess)]
        for i,b in enumerate(x):
            law=Counter(tuple(z[e] for e in inc[i]) for z in labels)
            if (i,b) in D:assert law==D[i,b]
            if (i,1-b) in D:assert law.keys().isdisjoint(D[i,1-b].keys())
            D[i,b]=law
    return guess,len(X)

def twisted(x):
    h=0; s=1
    for i,a in enumerate(x):
        if a:
            if i%2:h=(h+1)%3
            else:h=-h%3;s=-s
    return h==0 and s==1

bases=[
  (3,[(0,3)],words(4),0),
  (4,[(0,4)],[(0,)*5,(1,)*5],1),
  (4,[(0,4),(1,5)],[x+(0,0) for x in words(4)],2),
  (4,[(0,4)],[x+(0,) for x in words(4) if sum(x[1:])%2==0],2),
  (3,[(0,3)],[x+(0,) for x in words(3)],4),
  (3,[(0,3),(3,4)],[x+(0,) for x in words(4)],4),
  (3,[(0,3)],[x+(x[0],) for x in words(3)],4),
  (4,[(0,4),(4,5)],[x+(0,) for x in words(5)],4),
  (6,[(0,6),(2,7),(4,8)],[x+(0,0,0) for x in words(6) if twisted(x)],3),
]
# Test translation of the allowed domain, including a nonzero base word.
x0=tuple(int(i in (0,1,5,7)) for i in range(9))
l,br,dom,_=bases[8]
bases.append((l,br,[tuple(x^y for x,y in zip(a,x0)) for a in dom],3))
# Pure even and odd cycles remain compatible with the old criterion.
for l in range(4,9):
    bases.extend([(l,[],[x for x in words(l) if sum(x)%3==0],3),
                  (l,[],words(l),4)])
seen=[constructed(a,b,c,d) for a,b,c,d in bases]
print(f"Complete view tests: {len(seen)} attached or bare cases, "
      f"{sum(k for _,k in seen)} domain points including one infeasible case.")
assert seen[8]==(3,11)
print("Explicit nontranslation witness: 11-word C6 with three leaves.")
test3=0
xs=words(3)
for mask in range(1,1<<len(xs)):
    domain=[x for i,x in enumerate(xs) if (mask>>i)&1]
    for ext in (lambda x:0,lambda x:x[0]):
        ds=[x+(ext(x),) for x in domain]
        assert classify(3,[(0,3)],ds)[0] in (1,2,4)
        test3+=1
print(f"Triangular cores: {test3} fixed/equal pendant domains, no support three.")
