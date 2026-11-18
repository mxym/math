"""Independent exact regression checks for the fixed-alphabet code limit.

Uses no author's code. Tested assertions stay active under python -O. The
finite experiments corroborate identities; they do not prove an asymptotic
claim. The source and scope of the checked manuscript are recorded in REVIEW.md.
"""

from fractions import Fraction as F
from itertools import product
from math import comb
from random import Random


def require(ok, msg):
    if not ok:
        raise AssertionError(msg)


def inspect_array(A, B, q, n):
    a = [F(v, q**i) for i, v in enumerate(A)]
    b = [F(v, q**i) for i, v in enumerate(B)]
    def conv(t):
        return sum(a[i] * b[t-i] for i in range(1, t))
    s = [None, None] + [conv(t) for t in range(2, n+1)]
    gamma = max(a[1], b[1])
    for i in range(1, n):
        require(a[i] <= gamma * (1-sum(a[1:i])), "left row mass")
        require(b[i] <= gamma * (1-sum(b[1:i])), "right row mass")
    cutoffs = 0
    for N in range(n//2+1, n):
        cutoffs += 1
        # Insert one unit at each possible source and propagate FORWARDS.
        # This does not use the manuscript's backwards K or majorant E.
        direct = {i: sum(a[h]*b[i-h] for h in range(1, N) if 0 < i-h < N)
                  for i in range(N, n+1)}
        observed = 0
        for source in range(N, n+1):
            mass = [F(0)]*(n+1)
            mass[source] = F(1)
            for i in range(source, n):
                for j in range(1, n-i+1):
                    mass[i+j] += mass[i]*(a[i]*b[j] + b[i]*a[j])/s[i]
            require(mass[n] <= (1 if source == n else gamma), "source gain")
            observed += mass[n]*direct[source]
        require(observed == s[n], "terminal convolution identity")
        # Exact rational tilt; no numerical approximation to a polynomial root.
        z = 1+F(1, 2*N)
        U = [u*z**i for i, u in enumerate(a[:N])]
        V = [v*z**i for i, v in enumerate(b[:N])]
        tail = sum(U[i]*V[j] for i in range(1, N) for j in range(1, N)
                   if i+j >= N)
        for u,v,largest_small in ((U,V,n//2), (V,U,(n-1)//2)):
            I = range(n-N+1, min(largest_small, N-1)+1)
            x = sum(u[i]*v[n-i] for i in I)
            cap = max((u[j]*v[n-i] for i in I for j in I), default=0)
            require(x*x <= 2*cap*tail, "tilted half-diagonal")
    return 1, cutoffs


def enumerate_splits(a, b, q, n):
    if len(a) == n:
        yield a, b
        return
    t = len(a)
    s = sum(a[i]*b[t-i] for i in range(1, t))
    for c in range(s+1):
        yield from enumerate_splits(a+[c], b+[s-c], q, n)


def check_arrays():
    cases, cuts = 0, 0
    for q,n in ((2,8), (3,6), (4,5)):
        for h in range(1, q):
            for a,b in enumerate_splits([0,h], [0,q-h], q, n):
                c,k = inspect_array(a, b, q, n)
                cases += c
                cuts += k
    rng = Random(391)
    for q in (2,7,997):
        for rep in range(4):
            n = 15
            h = 1 if rep % 2 else q-1
            a,b = [0,h], [0,q-h]
            for t in range(2, n):
                s = sum(a[i]*b[t-i] for i in range(1, t))
                c = rng.choice((0,s,s//2,rng.randrange(s+1)))
                a.append(c)
                b.append(s-c)
            i,k = inspect_array(a,b,q,n)
            cases += i
            cuts += k
    require((cases,cuts) == (3831,8006), "array case counts")
    return cases,cuts


def check_markers(q,n,m):
    # Small instances, chosen for enumeration, not as an asymptotic sequence.
    k,L = 2,5
    alphabet = tuple(range(q))
    family = {(0,0,1,i,1) for i in range(m)}
    p = F(m,q**L)
    words = []
    freq = [0]*(n+1)
    count = 0
    last_hits = 0
    for prefix in family:
        for middle in product(alphabet, repeat=n-L-1):
            for last in range(1,q):
                w = prefix+middle+(last,)
                count += 1
                starts = [h for h in range(1,n-L+1) if w[h:h+L] in family]
                require(not any(i < L for i in starts), "overlapping marker")
                interior = sum(i < n-L for i in starts)
                last_hits += int(n-L in starts)
                for j in range(interior+1):
                    freq[j] += comb(interior,j)
                if not starts and not any(w[n-d:n-d+k] == (0,)*k
                                          for d in range(k+1,L)):
                    words.append(w)
    for j in range(1,n+1):
        b = n-2*L-(j-1)*(L-1)
        predicted = comb(b,j)*p**j if b>=j else 0
        require(F(freq[j],count) == predicted, "intersection sum")
    require(F(last_hits,count) == p/F(q-1,q), "last possible start")
    for d in range(1,n):
        require({w[:d] for w in words}.isdisjoint({w[-d:] for w in words}),
                "codeword prefix/suffix collision")
    return count,len(words)


if __name__ == "__main__":
    arrays,cutoffs = check_arrays()
    print(f"PASS: {arrays} arrays, {cutoffs} cutoffs")
    total = 0
    for q,n,m,c,a in ((2,18,1,4096,1607),(2,18,2,8192,1528),
                      (3,13,2,8748,6812),(4,12,3,36864,32472)):
        result = check_markers(q,n,m)
        require(result == (c,a), "word case counts")
        total += c
        print(f"PASS: q={q}, n={n}, M={m}: {c} conditioned words, {a} accepted")
    require(total == 57900, "total conditioned-word cases")
    print(f"PASS: {total} conditioned-word cases in four experiments")
