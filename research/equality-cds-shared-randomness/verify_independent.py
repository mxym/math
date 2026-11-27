#!/usr/bin/env python3
"""Independent finite exact checks of posterior moments and binary resource edges."""
from fractions import Fraction as F
from itertools import product
from random import Random


def dot(a,b):
    return sum(x*y for x,y in zip(a,b))


def bit(x,r):
    return (x>>r)&1


def hists(a,b,q):
    h=[0]*4
    for r in range(q):
        h[2*bit(a,r)+bit(b,r)] += 1
    return h


def exact_binary_search():
    counts=[]
    tries=0
    for q in range(1,5):
        full=(1<<q)-1
        passed=0
        # Perfect correctness at each positive seed forces A(x,0,r) and
        # A(x,1,r) to be opposite for binary A: the same Bob bit is possible.
        for a0,a1,b0,b1 in product(range(full+1),repeat=4):
            tries+=1
            A=(a0,a1)
            B=(b0,b1)
            ok=True
            for x,y in product((0,1),repeat=2):
                h0=hists(A[x],B[y],q)
                h1=hists(full^A[x],B[y],q)
                if x==y:
                    ok = ok and all(not (c and d) for c,d in zip(h0,h1))
                else:
                    ok = ok and h0==h1
            passed+=ok
        counts.append(passed)
    assert counts[:3]==[0,0,0] and counts[3]>0
    return tries,counts


def total_variation(P,Q,pi,x,y):
    # Direct computation over the entire pair of messages.
    return sum(abs(dot(pi,[ (P[x][0][r][a]-P[x][1][r][a])*Q[y][r][b]
                            for r in range(len(pi)) ]))
               for a,b in product(range(len(P[x][0][0])),range(len(Q[y][0]))))/2


def random_rank_upper(W,q):
    rows = [list(row) for row in W]
    k=0
    for j in range(len(W)):
        t=next((i for i in range(k,len(W)) if rows[i][j]),None)
        if t is None:
            continue
        rows[t],rows[k]=rows[k],rows[t]
        for i in range(k+1,len(W)):
            a,b=rows[i][j],rows[k][j]
            rows[i]=[x*b-y*a for x,y in zip(rows[i],rows[k])]
        k+=1
        if k==len(W):
            break
    assert k<=q


def check_laws(P,Q,pi):
    N,q=len(P),len(pi)
    D=[[total_variation(P,Q,pi,x,y) for y in range(N)] for x in range(N)]
    # Keep exact support for the posteriors; zero Bob messages are skipped.
    mu=[]
    for y in range(N):
        posts=[]
        for b in range(len(Q[y][0])):
            numer=[pi[r]*Q[y][r][b] for r in range(q)]
            mass=sum(numer)
            if mass:
                posts.append((mass,[t/mass for t in numer]))
        assert sum(m for m,_ in posts)==1
        mu.append(posts)
    phi = lambda z,p: sum(abs(dot(a,p)) for a in z)/2

    vectors=[]
    for x in range(N):
        z=[ [P[x][0][r][a]-P[x][1][r][a] for r in range(q)]
            for a in range(len(P[x][0][0])) ]
        for y in range(N):
            assert sum(w*phi(z,p) for w,p in mu[y])==D[x][y]
        sx=[]
        for w,p in mu[x]:
            signs=[(v>0)-(v<0) for v in (dot(a,p) for a in z)]
            v=[sum(s*a[r] for s,a in zip(signs,z))/F(2) for r in range(q)]
            assert all(-1<=t<=1 for t in v)
            assert dot(v,p)==phi(z,p)
            for y in range(N):
                assert all(abs(dot(v,py))<=phi(z,py) for _,py in mu[y])
            sx.append((w,p,v))
        vectors.append(sx)
    ETr=EFrob=0
    draws=0
    for selection in product(*vectors):
        pr=F(1)
        for w,_,_ in selection:
            pr*=w
        W=[[dot(v,p) for _,p,_ in selection] for _,_,v in selection]
        random_rank_upper(W,q)
        tr=sum(W[x][x] for x in range(N))
        frob=sum(x*x for row in W for x in row)
        assert tr*tr<=q*frob
        ETr+=pr*tr
        EFrob+=pr*frob
        draws+=1
    assert ETr==sum(D[x][x] for x in range(N))
    delta=max(D[x][y] for x in range(N) for y in range(N) if x!=y)
    a=min(D[x][x] for x in range(N))
    assert ETr**2<=q*EFrob<=q*(N+N*(N-1)*delta)
    assert q*(1+(N-1)*delta)>=a*a*N
    return draws,D


def robust_examples():
    # Randomness here is only a fixed deterministic input generator for
    # exact rational tests of arbitrary and sometimes degenerate local laws.
    gen=Random(14973)
    def law(k):
        v=[gen.randrange(6) for _ in range(k)]
        if not any(v):
            v[0]=1
        return [F(t,sum(v)) for t in v]
    draws=0
    for q,N in product((1,2,3,4),(2,3,4)):
        pi=[F(r+1,q*(q+1)//2) for r in range(q)]
        for attempt in range(3):
            P=[[[law(4) for _ in range(q)] for _ in range(2)] for _ in range(N)]
            Q=[[law(3) for _ in range(q)] for _ in range(N)]
            draws+=check_laws(P,Q,pi)[0]
    configs=0
    for N, g in ((2,[0,1,1]),(4,[0,1,2,3]),(4,[0,1,1,3])):
        tape=list(product(g,(0,1)))
        q=len(tape)
        pi=[F(1,q)]*q
        P=[]
        for x in range(N):
            P.append([[[F(int(a==(s^u^((x&z).bit_count()&1))))
                        for a in (0,1)] for z,u in tape] for s in (0,1)])
        for eta in (F(0),F(1,5),F(1,2),F(1)):
            Q=[]
            for y in range(N):
                Q.append([[(1-eta)*int(b==(u^((y&z).bit_count()&1)))
                            for b in (0,1)]+[eta] for z,u in tape])
            d,D=check_laws(P,Q,pi)
            assert all(D[x][x]==1-eta for x in range(N))
            for x,y in product(range(N),repeat=2):
                if x!=y:
                    b=abs(sum((-1)**(((x^y)&z).bit_count()&1) for z in g))
                    assert D[x][y]==(1-eta)*F(b,len(g))
            draws+=d
            configs+=1
    return draws,configs


if __name__ == "__main__":
    trials,counts=exact_binary_search()
    draws,configs=robust_examples()
    print(f"PASS independent: {trials} one-bit deterministic encoder tables, exact cases by support 1..4: {counts}")
    print(f"PASS independent: {draws} exact posterior certificate draws, 36 arbitrary rational channels, {configs} erasure/parity-bias checks")
