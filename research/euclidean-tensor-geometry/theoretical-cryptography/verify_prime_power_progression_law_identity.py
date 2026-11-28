#!/usr/bin/env python3
"""Pure mathematical forward-law checks, using no external samples or solvers."""
from collections import Counter
from math import gcd
from random import Random


def divide_p(x, p):
    assert x != 0
    k = 0
    while x % p == 0:
        x //= p
        k += 1
    return k, x


def add_key(p, value):
    v, a = divide_p(value, p)
    # The caller turns v into depth j-v.
    return v, a


def upper_sum(q, p, key):
    k, s = key
    lo, hi = q // 2 + 1, q - 1

    def calc(a, d):
        i, j = (lo-a+d-1)//d, (hi-a)//d
        if i > j:
            return 0, 0
        n = j-i+1
        return n, n*(2*a+d*(i+j))//2

    if not k:
        n1,s1 = calc(0,1)
        n2,s2 = calc(0,p)
        return n1-n2, s1-s2
    return calc(s,p**k)


def signature(fs, p, j):
    q = p**j
    A = sum(a for a,c,L in fs) % q
    active = [(c,L) for _,c,L in fs if c%q]
    if any(c*L%q==0 for c,L in active):
        return (0,)
    if q == 2:
        den = 1
        for c,L in active:
            den *= L
        return (1, den, A)
    B = Counter()
    den = 1
    for c,L in active:
        val, free = divide_p(L,p)
        den *= free
        B[0,0] -= val
        for z,t in ((c*L,1),(c,-1)):
            v,a=add_key(p,z)
            k=j-v
            B[k,a%(p**k)] += t
    sign = exponent = 0
    for node,b in B.items():
        n,u = upper_sum(q,p,node)
        sign += n*b
        exponent += u*b
    turn=(2*(A+exponent)+q*sign)%(2*q)
    S=Counter()
    for (k,a),b in B.items():
        S[k,a] += b
        S[k,-a%(p**k)] += b
    return (2,den,turn,{k:w for k,w in S.items() if w})


def is_zero(weights,p,j):
    root = (0,0)
    weights = {k:w for k,w in weights.items() if w}
    weights.setdefault(root,0)
    ps=[p**k for k in range(j+1)]
    ks=sorted(weights)
    childrensize=Counter()
    ancestors={}
    size={}
    for k,a in ks:
        current=(k,a)
        size[current]=ps[j-k] if k else ps[j]-ps[j-1]
        parent=None
        if k:
            parent=max((h,b) for h,b in ks if h<k and a%ps[h]==b)
            childrensize[parent] += size[current]
        ancestors[current]=weights[current]+(ancestors[parent] if parent else 0)
    assert all(childrensize[x] <= size[x] for x in ks)
    return all(ancestors[x]==0 for x in ks if childrensize[x]<size[x])


def checksig(A,B,p,j):
    if A[:3]!=B[:3]:
        return False
    if A[0]!=2:
        return True
    d=Counter(A[3])
    d.subtract(B[3])
    return is_zero(d,p,j)


def counts(fs,q):
    d=[1]+[0]*(q-1)
    for a,c,L in fs:
        r=q//gcd(c,q)
        h,t=divmod(L,r)
        f=[0]*q
        for i in range(r):
            f[(a+c*i)%q] += h+int(i<t)
        g=[0]*q
        for i,v in enumerate(d):
            if not v:
                continue
            for k,w in enumerate(f):
                if w:
                    g[(i+k)%q]+=v*w
        d=g
    return d,sum(d)


def true_top(A,B,p,j):
    q=p**j
    d,den=A
    dd,dden=B
    v=[a*dden-b*den for a,b in zip(d,dd)]
    d0=q//p
    # Difference divisible by Phi_{p^j} iff constant in each length-p fiber.
    return all(v[t]==v[t%d0] for t in range(q))


def test_levels():
    rng=Random(641)
    levels=pairs=equal=0
    for p,e in ((2,1),(2,2),(2,3),(2,5),(3,1),(3,2),(3,4),
                (5,2),(7,2),(11,1)):
        q=p**e
        for i in range(110):
            a=[(rng.randrange(-q,q+1),rng.randrange(-q,q+1),
                rng.randrange(1,2*q+1)) for _ in range(rng.randrange(0,6))]
            if i%4==0:
                b=[(s+c*(L-1),-c,L) for s,c,L in reversed(a)]
                b += [(0,q,rng.randrange(1,q+1))]
            elif i%4==1:
                b = []
                for s,c,L in a:
                    t = rng.randrange(1,q+1)
                    b.extend(((s,c,t),(0,c*t,L)))
                # Compare against the exact mixed-radix change of list.
                a=[(s,c,L*t) for (s,c,L),(_,_,t) in zip(a,b[::2])]
            elif i%4==2:
                b = a + [(1,0,1)]
            else:
                b=[(rng.randrange(-q,q+1),rng.randrange(-q,q+1),
                    rng.randrange(1,2*q+1)) for _ in range(rng.randrange(0,6))]
            all_levels=True
            for j in range(1,e+1):
                m=p**j
                k1,k2=signature(a,p,j),signature(b,p,j)
                exact=checksig(k1,k2,p,j)
                assert exact==true_top(counts(a,m),counts(b,m),p,j)
                all_levels &= exact
                levels+=1
            a0,an=counts(a,q)
            b0,bn=counts(b,q)
            actual=all(x*bn==y*an for x,y in zip(a0,b0))
            assert actual==all_levels
            pairs+=1
            if actual:
                equal+=1
    return levels,pairs,equal


def test_markers():
    rng=Random(73221)
    n=0
    for p,j in ((2,1),(2,3),(2,6),(3,2),(5,3),(7,2)):
        q=p**j
        for _ in range(140):
            k=rng.randrange(1,j+1)
            a=rng.randrange(1,p**k)
            if a%p==0:
                a+=1
            if a>=p**k or a%p==0:
                a=1
            raw={(k,a):1}
            if k<j:
                raw.update({(k+1,a+t*p**k):-1 for t in range(p)})
            else:
                raw[k,a]-=1
            if rng.randrange(2):
                c=rng.randrange(1,p)  # perturb one level-one class
                raw[1,c]=raw.get((1,c),0)+1
            actual=all(sum(w for (k0,a0),w in raw.items() if x%(p**k0)==a0)==0
                       for x in range(q) if x%p)
            assert is_zero(raw,p,j)==actual
            for key in list(raw)+[(0,0)]:
                k0,a0=key
                pts=[x for x in range(q//2+1,q) if x%p and x%(p**k0)==a0]
                assert upper_sum(q,p,key)==(len(pts),sum(pts))
            n+=1
    return n


def large():
    n=0
    for p,e in ((2,112),(3,72),(17,31),(2**61-1,4)):
        q=p**e
        a=[(q+51,1,p+2 if p%2 else 7),
           (-q,2*p+1,p*p+3 if p==2 else p*p+2),
           (101,p**(e//2),p**e+1)] # phase, nonunit, long wrapping
        t=p**(e//2)+1
        b = a[:-1]+[(101,a[-1][1],t),
                    (0,a[-1][1]*t,a[-1][-1])]
        a[-1]=(101,a[-1][1],a[-1][-1]*t)
        for j in range(1,e+1):
            assert check_sig_simple(a,b,p,j)
            n+=1
        assert not check_sig_simple(a,b+[(1,0,1)],p,e)
        n+=1
    return n


def check_sig_simple(a,b,p,j):
    return check_sig(signature(a,p,j),signature(b,p,j),p,j)


# Bind one comparison name in large-case tests.
check_sig=checksig
if __name__=="__main__":
    print("PASS: conductor comparisons, full law pairs/equalities, marker systems, large cases",
          *test_levels(),test_markers(),large())
