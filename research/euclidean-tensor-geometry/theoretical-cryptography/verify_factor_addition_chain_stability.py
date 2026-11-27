#!/usr/bin/env python3
"""Exact reference implementation for dyadic addition-chain stability.

No dependency, floating point, or practical runtime guarantee.  Execute with no
arguments for finite cross-checks, or pass an integer (and optional --star) to
solve an individual instance by the theorem's complete algorithm.
"""

import argparse
from collections import Counter, deque
from itertools import permutations
import heapq


def row(p, m, b, equality):
    """Constraint p·x - m·x = b or <= b, with p/m incidence masks."""
    return (p & ~m, m & ~p, b, equality)


def solve_linear(dim, rows):
    """Exact least-significant-digit reachability for a nonnegative ILP."""
    clean = []
    for p, m, b, eq in sorted(set(rows)):
        if (not m and b < 0) or (eq and not p and b > 0):
            return None
        if p or m:
            clean.append((p, m, b, eq))
    initial = tuple(b for _, _, b, _ in clean)
    wanted = tuple(eq for _, _, _, eq in clean)
    need = [i for i, eq in enumerate(wanted) if eq]
    allow = [i for i, eq in enumerate(wanted) if not eq]
    if dim <= 16:
        precomputed = [
            tuple((p & v).bit_count() - (m & v).bit_count()
                  for p, m, _, _ in clean)
            for v in range(1 << dim)
        ]
    else:
        precomputed = None
    pending = deque([initial])
    parent = {initial: None}
    while pending:
        state = pending.popleft()
        # If all remaining digits are zero, this is exactly feasibility.
        if all(state[i] == 0 for i in need) and all(state[i] >= 0 for i in allow):
            out = [0] * dim
            while parent[state] is not None:
                state, digit = parent[state]
                # Backtracking presents digits high-order first.
                out = [(v << 1) | ((digit >> j) & 1) for j, v in enumerate(out)]
            return out
        for digit in range(1 << dim):
            ds = precomputed[digit] if precomputed is not None else (
                (p & digit).bit_count() - (m & digit).bit_count()
                for p, m, _, _ in clean
            )
            rem = tuple(c - delta for c, delta in zip(state, ds))
            if any(rem[i] % 2 for i in need):
                continue
            nxt = tuple(c // 2 for c in rem)
            if nxt not in parent:
                parent[nxt] = (state, digit)
                pending.append(nxt)
    return None


def parent_patterns(d, star):
    a = []
    def visit(i):
        if i > d:
            yield tuple(a)
            return
        candidates = ((i - 1, q) for q in range(i)) if star else (
            (p, q) for q in range(i) for p in range(q + 1)
        )
        for p, q in candidates:
            a.append((p, q))
            yield from visit(i + 1)
            a.pop()
    yield from visit(1)


def model(parents, k, star, jmax=None):
    d = len(parents)
    j = 3*d+1
    T = (1 << (d+1)) - 1
    extras = [row(T, 1 << j, k-d, False)]
    polys = [(0,)]
    for i, (p, q) in enumerate(parents, 1):
        u, v = d+2*i-1, d+2*i
        extras.append(row(1 << u, 1 << p, 0, star))
        extras.append(row(1 << v, 1 << q, 0, False))
        polys.append(tuple(e | (1 << u) for e in polys[p])
                     + tuple(e | (1 << v) for e in polys[q]))
    if jmax is not None:
        extras.append(row(1 << j, 0, jmax, False))
    return j+1, j, extras, [(e | (1 << d), 0) for e in polys[-1]]


def carry_systems(terms, bits, j):
    """Enumerate equality systems for binary normalization of a short sum."""
    if len(terms) < len(bits):
        return
    # Symbolically identical leaves necessarily share an exponent.
    # Normalize duplicate forms before searching optional identifications.
    bag = Counter(terms)
    while True:
        term = next((a for a, c in bag.items() if c >= 2), None)
        if term is None:
            break
        bag[term] -= 2
        bag[(term[0], term[1]+1)] += 1
    terms = sorted(a for a, c in bag.items() if c)
    if len(terms) < len(bits):
        return
    if len(terms) == len(bits):
        for targets in permutations(bits):
            yield tuple(row(p, 1 << j, b-c, True)
                        for (p, c), b in zip(terms, targets))
        return
    for a, (pa, ca) in enumerate(terms):
        for b in range(a+1, len(terms)):
            pb, cb = terms[b]
            r = row(pa, pb, cb-ca, True)
            p, m, rhs, _ = r
            if (not m and rhs < 0) or (not p and rhs > 0):
                continue
            nxt = terms[:a]+terms[a+1:b]+terms[b+1:]+[(pa, ca+1)]
            for tail in carry_systems(nxt, bits, j):
                yield (r,)+tail


def bit_positions(n):
    return [i for i in range(n.bit_length()) if (n >> i) & 1]


def d_bound(n, k):
    """Use phi < 34/21, hence 2/phi > 21/17; no floating point."""
    if k < 0 or n > (1 << k):
        return -1
    a, b, d = n, 1 << k, 0
    while 21*a <= 17*b:
        a, b, d = 21*a, 17*b, d+1
    return d


def find_witness(n, k, jmax=None, star=False):
    """A symbolic witness for ell(2**j*n) <= j+k, or exact None."""
    bits = bit_positions(n)
    limit = d_bound(n,k)
    if limit < 0 or len(bits) > (1 << limit):
        return None
    for d in range(limit+1):
        if len(bits) > (1 << d):
            continue
        for parents in parent_patterns(d,star):
            dim, j, base, terms = model(parents,k,star,jmax)
            if len(terms) < len(bits):
                continue
            seen = set()
            for carry in carry_systems(terms,bits,j):
                canon = tuple(sorted(set(carry)))
                if canon in seen:
                    continue
                seen.add(canon)
                x = solve_linear(dim,(*base,*canon))
                if x is not None:
                    ans = (parents,x)
                    assert witness_ok(n,k,ans,jmax,star)
                    return ans
    return None


def witness_ok(n,k,ans,jmax=None,star=False):
    parents,x = ans
    d = len(parents)
    if n<1 or any(not (0<=p<i and 0<=q<i)
                  for i,(p,q) in enumerate(parents,1)):
        return False
    dim,j,base,terms = model(parents,k,star,jmax)
    if len(x)!=dim or min(x)<0:
        return False
    def value(mask):
        return sum(y for i,y in enumerate(x) if (mask >> i) & 1)
    if any(value(p)-value(m)>b or (eq and value(p)-value(m)!=b)
           for p,m,b,eq in base):
        return False
    if star and any(p!=i-1 for i,(p,q) in enumerate(parents,1)):
        return False
    counter = Counter(value(mask)+c for mask,c in terms)
    live = list(counter); heapq.heapify(live)
    support = []
    while live:
        b = heapq.heappop(live)
        count = counter[b]
        if count & 1:
            support.append(b)
        if count >= 2:
            if b+1 not in counter:
                heapq.heappush(live,b+1)
            counter[b+1] += count//2
    return support == [x[j]+t for t in bit_positions(n)]


def stability(n,star=False):
    assert n>=1
    low = (n-1).bit_length()
    up = n.bit_length()+n.bit_count()-2
    for k in range(low,up+1):
        found = find_witness(n,k,star=star)
        if found is not None:
            break
    else:
        raise AssertionError("the binary method supplies an upper bound")
    lo,hi = 0,found[1][-1]
    while lo<hi:
        mid=(lo+hi)//2
        candidate=find_witness(n,k,jmax=mid,star=star)
        if candidate is None:
            lo=mid+1
        else:
            hi,found=candidate[1][-1],candidate
    assert found[1][-1]==lo
    return k,lo,found


def naive_length(n,star=False):
    """Independent complete direct search used only on small controls."""
    A=[1]
    def search(budget):
        a=A[-1]
        if a==n:
            return True
        if budget==0 or (a << budget)<n:
            return False
        pairs = ((a,b) for b in A) if star else (
            (x,y) for i,x in enumerate(A) for y in A[:i+1]
        )
        nxt=sorted({x+y for x,y in pairs if a<x+y<=n},reverse=True)
        for x in nxt:
            if (x << (budget-1))<n:
                break
            A.append(x)
            if search(budget-1):
                A.pop()
                return True
            A.pop()
        return False
    for k in range((n-1).bit_length(),n.bit_length()+n.bit_count()-1):
        if search(k):
            return k
    raise AssertionError("binary upper bound missed")


def selftest():
    import itertools
    from random import Random
    R=Random(109622)
    checks=0
    def check(cond):
        nonlocal checks
        checks+=1
        assert cond
    # Independent bounded integer feasibility on randomly generated toy ILPs.
    for dim in range(1,5):
        for case in range(110):
            rows=[row(1 << i,0,3,False) for i in range(dim)]
            for _ in range(R.randrange(7)):
                coeff=[R.randrange(-1,2) for i in range(dim)]
                p=sum(1 << i for i,t in enumerate(coeff) if t==1)
                m=sum(1 << i for i,t in enumerate(coeff) if t==-1)
                rows.append(row(p,m,R.randrange(-9,10),bool(R.randrange(2))))
            def valid(x):
                for p,m,b,eq in rows:
                    val=sum(t*(((p >> i)&1)-((m >> i)&1)) for i,t in enumerate(x))
                    if val>b or (eq and val!=b):
                        return False
                return True
            brute=next((x for x in itertools.product(range(4),repeat=dim) if valid(x)),None)
            found=solve_linear(dim,rows)
            check((found is None)==(brute is None))
            if found is not None:
                check(valid(found))
    # Numeric normalization vs symbolic carry systems for short sums.
    for _ in range(450):
        exponents=[R.randrange(5) for __ in range(R.randint(1,6))]
        digits=bit_positions(sum(1 << a for a in exponents))
        term=[(1 << i,0) for i in range(len(exponents))]
        j=len(exponents)
        x=exponents+[0]
        def test_sys(rows):
            return all(sum(t*(((p >> i)&1)-((m >> i)&1)) for i,t in enumerate(x))==b
                       for p,m,b,_ in rows)
        check(any(test_sys(rows) for rows in carry_systems(term,digits,j)))
        # A different target cannot be certified by any valid equation system.
        bad=bit_positions(sum(1 << a for a in exponents)+1)
        check(not any(test_sys(rows) for rows in carry_systems(term,bad,j)))
    for star in [False,True]:
        for n in range(1,17):
            k0=naive_length(n,star)
            check(find_witness(n,k0-1,jmax=0,star=star) is None)
            a=find_witness(n,k0,jmax=0,star=star)
            check(a is not None and witness_ok(n,k0,a,0,star))
            k,j,ans=stability(n,star)
            check(k<=k0 and witness_ok(n,k,ans,j,star))
            check(naive_length(n << j,star)==j+k)
        for n in [3,7,15]:
            k,j,_=stability(n,star)
            check(k==naive_length(n,star) and j==0)
    check(34**2>34*21+21**2 and 21**10>8*17**10)
    for star in [False,True]:
        for _ in range(800):
            d=R.randrange(7)
            t=[R.randrange(6) for _ in range(d+1)]
            x=[1]
            parents=[]
            offsets=[]
            for i in range(1,d+1):
                p=i-1 if star else R.randrange(i)
                q=R.randrange(i)
                u=t[p] if star else R.randrange(t[p]+1)
                v=R.randrange(t[q]+1)
                parents.append((p,q))
                offsets.extend((u,v))
                x.append((x[p] << u)+(x[q] << v))
            result=x[-1]<<t[d]
            z=(result&-result).bit_length()-1
            j=R.randrange(z+1)
            k=d+sum(t)-j
            n=result>>j
            check(d_bound(n,k)>=0)
            check(witness_ok(n,k,(parents,t+offsets+[j]),j,star))
        for a in [5,13,31,127,511]:
            k,j,ans=stability((1<<a)+1,star)
            check((k,j)==(a+1,0))
            check(witness_ok((1<<a)+1,k,ans,j,star))
    # Established example of a defect drop, checked by ordinary enumeration.
    check(naive_length(191)==11)
    check(naive_length(382)==11)
    # Translate one explicit ordinary chain for 382 to a compressed certificate.
    values=[1,2,4,5,9,14,23,46,92,184,198,382]
    seen={1:(0,0)}
    parents=[]; t=[0]; offsets=[]
    for index,v in enumerate(values[1:],1):
        if v==2*values[index-1]:
            t[-1]+=1
        else:
            u,w=next((u,v-u) for u in seen if v-u in seen)
            p,s=seen[u];q,b=seen[w]
            parents.append((p,q));offsets.extend((s,b));t.append(0)
        seen[v]=(len(t)-1,t[-1])
    check(witness_ok(191,10,(parents,t+offsets+[1]),1))
    print({"exact_checks":checks,"known_defect_drop":[191,382]})


if __name__=="__main__":
    arg=argparse.ArgumentParser(description=__doc__)
    arg.add_argument("n",type=int,nargs="?")
    arg.add_argument("--star",action="store_true")
    z=arg.parse_args()
    if z.n is None:
        selftest()
    else:
        if z.n<1:
            arg.error("n must be positive")
        k,j,ans=stability(z.n,z.star)
        print({"n":z.n,"stable_length":k,"stabilization_index":j,
               "stable":j==0,"star":z.star,"parents":ans[0],"parameters":ans[1]})
