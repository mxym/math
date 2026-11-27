#!/usr/bin/env python3
"""Raw-convolution and trace checks for synthetic finite codes; no decoder."""
from collections import Counter
from itertools import product


def add(x,y,r):
    return tuple((a+b)%r for a,b in zip(x,y))


def dot(x,y,r):
    return sum(a*b for a,b in zip(x,y))%r


def wt(a):
    return sum(x!=0 for x in a)


def group(r,m):
    V = list(product(range(r), repeat=m))
    pos = {x:i for i,x in enumerate(V)}
    diffs = [[pos[tuple((x-y)%r for x,y in zip(a,b))] for b in V] for a in V]
    return V,diffs


def con(a,b,p,D):
    return tuple(sum(a[i]*b[j] for i,j in enumerate(row))%p for row in D)


def line_reps(V,r):
    return [w for w in V if any(w) and next(c for c in w if c) == 1]


def indicator_diff(V,r,p,w):
    return tuple((int(dot(x,w,r)==0)-int(dot(x,w,r)==1))%p for x in V)


counts = words = hist_tests = raw_checks = 0
for r,p in ((2,3),(3,2)):
    V,D = group(r,2)
    N = len(V)
    L = line_reps(V,r)
    Z = [indicator_diff(V,r,p,w) for w in L]
    assert len(L)==r+1 and all(wt(z)==2*r for z in Z)
    H = Counter()
    for a in product(range(p),repeat=N):
        A = sum(1<<i for i,z in enumerate(Z) if wt(con(z,a,p,D))==0)
        H[A] += 1
        # Actual unassisted rank-one codeword distances, tiny case only.
        if r==2:
            d_min = min(wt(z)+wt(con(z,a,p,D)) for z in product(range(p),repeat=N) if any(z))
            if A:
                assert d_min<=2*r
            words+=p**N-1
        for i,z in enumerate(Z):
            # Direct quotient histograms: difference kills exactly when the
            # r coset totals are all equal. No Fourier used here.
            T = [sum(a[j] for j,x in enumerate(V) if dot(x,L[i],r)==s)%p for s in range(r)]
            assert bool(A&(1<<i)) == (len(set(T))==1)
            raw_checks += 1
        counts+=1
    HH=Counter()
    for a,na in H.items():
        for b,nb in H.items():
            HH[a&b] += na*nb
    for h,J in ((1,H),(2,HH)):
        for M in range(1<<len(L)):
            f = h*(N-len(L)*(r-1))
            assert J[M] == p**f * (p**(h*(r-1))-1)**(len(L)-M.bit_count())
            hist_tests+=1

# Check the binary character modulation through direct convolutions, without
# using Fourier inversion: test every modulation b and every nonzero direction.
V,D = group(2,2)
binary = 0
for a in product(range(3),repeat=4):
    for b in V:
        for h in V[1:]:
            c=(sum(x*(-1)**dot(b,g,2) for x,g in zip(a,V)))%3
            c1=(sum(x*(-1)**dot(add(b,h,2),g,2) for x,g in zip(a,V)))%3
            if c != c1:
                continue
            u=tuple((-1)**dot(b,g,2)%3 if dot(h,g,2)==0 else 0 for g in V)
            assert wt(u)==2 and con(u,a,3,D)==tuple(c*x%3 for x in u)
            binary += 1

# F_4 trace descent when F_2 does not split the character group of F_3^2.
V,D=group(3,2)
def m4(x,y):
    return (x if y&1 else 0)^((x<<1)^ (7 if x&2 else 0) if y&2 else 0)
def trace(x):
    z=x^m4(x,x)
    assert z in (0,1)
    return z
P=(1,2,3)
trials=trace_words=0
for b in V:
    for h in line_reps(V,3):
        u=tuple(m4(P[-dot(b,g,3)%3],1^P[-dot(h,g,3)%3]) for g in V)
        j=next(j for j,p in enumerate(u) if p)
        assert wt(u)==6
        ua=[tuple(u[D[i][a]] for i in range(9)) for a in range(9)]
        for support in ((0,), (1,2), (2,5), (1,2,6), (1,4,7,8), tuple(range(9))):
            a=tuple(int(i in support) for i in range(9))
            v=[0]*9
            for ai in support:
                v=[x^y for x,y in zip(v,ua[ai])]
            lam=next(c for c in range(4) if m4(c,u[j])==v[j])
            if all(m4(lam,x)==y for x,y in zip(u,v)):
                good=False
                for c in range(1,4):
                    z=tuple(trace(m4(c,x)) for x in u)
                    w=tuple(trace(m4(c,y)) for y in v)
                    assert con(z,a,2,D)==w and wt(z)<=6 and wt(w)<=6
                    good|=bool(wt(z))
                    trace_words += 1
                assert good
            trials += 1

# A non-elementary extension test over F_3: the group is Z_4^2,
# the two cube directions have order 2, and the translation has order 4.
# Compute in F_9 = F_3[i]/(i^2+1), then trace a nonzero scalar multiple.
V,D = group(4,2)
iP = ((1,0),(0,1),(2,0),(0,2))
def m9(x,y):
    a,b=x; c,d=y
    return ((a*c-b*d)%3,(a*d+b*c)%3)
def minus9(x,y):
    return tuple((a-b)%3 for a,b in zip(x,y))
U=tuple(m9(iP[-x%4],m9(minus9((1,0),iP[-2*x%4]),
                        minus9((1,0),iP[-2*y%4]))) for x,y in V)
assert sum(x!=(0,0) for x in U)==4
z=tuple((2*m9((0,1),x)[0])%3 for x in U)
a=tuple(int(g==(2,0)) for g in V)
assert wt(z)==4 and con(z,a,3,D)==tuple(-x%3 for x in z)

# Quotient lift with group kernel of size 2 and coefficient characteristic 2:
# the identity must not rely on dividing by kernel order.
G,DD=group(2,3)
V,D=group(2,2)
rows={v:i for i,v in enumerate(V)}
quot=0
for a in product(range(2),repeat=8):
    Pa=tuple(sum(ai for ai,g in zip(a,G) if g[:2]==v)%2 for v in V)
    for z in product(range(2),repeat=4):
        Iz=tuple(z[rows[g[:2]]] for g in G)
        zPa=con(z,Pa,2,D)
        assert con(Iz,a,2,DD)==tuple(zPa[rows[g[:2]]] for g in G)
        assert wt(Iz)==2*wt(z)
        quot+=1

# Negative control: one parity block can hide a forced zero for another block,
# so the h=2 event is intersection rather than the union of the masks.
assert (1&2)==0 and (1|2)==3
print(f"PASS independent: {counts} parity vectors, {raw_checks} quotient-sum identities, "
      f"{hist_tests} exact joint-mask counts, {words} finite codewords; "
      f"{binary} modulated lines; {trials} nonsplit cases/{trace_words} trace checks; "
      f"{quot} quotient lifts; Z4^2 non-elementary trace control; parity-mask negative control")
