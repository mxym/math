#!/usr/bin/env python3
"""Exact Walsh verification of the finite boundary cases and strictness witnesses."""

def ck(ok, msg):
    if not ok:
        raise ValueError(msg)


def parity(n):
    return bin(n).count('1') & 1


def evaluate(n, terms):
    # Labels 1..n correspond to bit positions 0..n-1.
    masks = [sum(1 << (int(c)-1) for c in t) for t in terms.split('+')] if terms else []
    return tuple(sum((x&m)==m for m in masks)&1 for x in range(1 << n))


def linear_shift(f, c):
    return tuple(y^parity(c&i) for i,y in enumerate(f))


def spectrum(f):
    return tuple(sum((-1 if (y ^ parity(x&a)) else 1) for x,y in enumerate(f))
                 for a in range(len(f)))


def heights(f):
    return tuple(sorted(set(map(abs,spectrum(f)))))


def dimension_mask(vectors):
    B = {0}
    for x in vectors:
        B |= {x^y for y in B}
    return len(B).bit_length()-1


def support_dimension(f):
    S = [u for u,a in enumerate(spectrum(f)) if a]
    return dimension_mask(u^S[0] for u in S)


def degree(f):
    a = list(f)
    for i in range(len(f).bit_length()-1):
        for x in range(len(f)):
            if x&(1<<i):
                a[x] ^= a[x^(1<<i)]
    return max((x.bit_count() for x,v in enumerate(a) if v), default=0)



def fast_spectrum(f):
    a = [(-1 if x else 1) for x in f]
    h = 1
    while h < len(a):
        for k in range(0,len(a),2*h):
            for j in range(k,k+h):
                u,v = a[j],a[j+h]
                a[j],a[j+h] = u+v,u-v
        h *= 2
    return a


def counts(n, top, topsize):
    from itertools import combinations
    high = evaluate(n,top)
    qs = [''.join(str(i) for i in j) for j in combinations(range(1,n+1),2)]
    T = tuple(evaluate(n,t) for t in qs)
    positive_p,positive_mixed, qualifying_nb = 0,0,0
    for q in range(1<<len(qs)):
        f = tuple(y ^ (sum(t[x] for j,t in enumerate(T) if q&(1<<j)) & 1)
                  for x,y in enumerate(high))
        w = fast_spectrum(f)
        ck(tuple(w)==spectrum(f),('independent Walsh mismatch',n,top,q))
        m = set(map(abs,w))-{0}
        is_plateaued = len(m)==1
        is_mixed = m==({4,8} if n==4 else {8,16})
        positive_p += is_plateaued
        positive_mixed += is_mixed
        if is_mixed:
            amplitude = 1<<(n-1)
            ck(any(all({abs(w[i]+w[i^c]),abs(w[i]-w[i^c])}<={0,amplitude}
                       for i in range(1<<n)) for c in range(1<<n)),
               ("no plateaued extension",n,top,q))
        if n==5 and m=={8}:
            qualifying_nb += 1
            ck(any(all(bool(w[i])!=bool(w[i^c]) for i in range(32))
                   for c in range(1,32)), ("no bent extension",n,top,q))
    print(f"n={n}, top={top or '0'}, {1<<len(qs)} quadratics: "
          f"plateaued={positive_p}, mixed extendable={positive_mixed}, "
          f"5D near-bent extendable={qualifying_nb}; top orbit size={topsize}.")
    return topsize*positive_p*(1<<(n+1)), topsize*positive_mixed*(1<<(n+1))


def classification():
    expect = {4: ((('',1),('123',15)),(2048,26880)),
              5: ((('',1),('123',155),('123+145',868)),(14064640,19443200))}
    for n,(top_types,totals) in expect.items():
        p,m = zip(*(counts(n,t,s) for t,s in top_types))
        ck((sum(p),sum(m))==totals,("incorrect class counts",n))
        print(f"Class counts n={n}: plateaued={sum(p)}, "
              f"nonplateaued but extendable={sum(m)}, all extendable={sum(p)+sum(m)}.")

def main():
    for name,c in [('123+14+25',4),('123+145+23+24+35',1)]:
        f = evaluate(5,name)
        h = linear_shift(f,c)
        ck(heights(f)==(0,8) and support_dimension(f)==5,
           f"invalid five-variable near-bent witness {name}")
        ck(heights(f+h)==(8,), f"invalid six-variable bent extension {name}")
        print(f"5D near-bent {name}: span 5, extend with mask 0x{c:x}, 6D bent PASS.")
    for n,name,c in [(4,'123+14',2),(5,'123+14',2),(5,'123+145+23',1)]:
        f = evaluate(n,name)
        h = linear_shift(f,c)
        A = 1<<(n-1)
        ck(heights(f)==(0,A//2,A) and heights(f+h)==(0,A),
           "mixed-spectrum extension failed")
        print(f"{n}D {name}: |Walsh|={heights(f)}, partner mask 0x{c:x}, extension (0,{A}) PASS.")
    f = evaluate(5,'2345+123+24+35')
    ck(heights(f)==(0,4,8), "five-variable excluded NL12 spectrum")
    print("5D NL12 quartic has (0,4,8) and is not plateaued; excluded analytically.")
    ck(heights(evaluate(3,'123'))==(2,6), "universal strict outside witness")
    print("3D cubic has |Walsh| (2,6), ratio 3.") 

    bent = tuple(parity(x&y)^int(y==7) for y in range(8) for x in range(8))
    ck(heights(bent)==(8,) and degree(bent)==3,"six-variable cubic bent witness")
    phi = {a: b for pair,b in zip(((0,1),(2,4),(3,6),(5,7)),(0,1,2,4)) for a in pair}
    six = tuple(parity(x&phi[y]) for y in range(8) for x in range(8))
    ck(heights(six)==(0,16) and support_dimension(six)==6,
       "even-degree support obstruction witness")
    print("6D: cubic bent PASS; full-affine-span nonbent plateaued witness PASS.")
    classification()
    ck(heights(evaluate(5,'123+14+25')+evaluate(5,'123+14+25'))!=(8,),
       "negative control: identical partner incorrectly accepted as bent")
    print("Negative control: duplicate two halves is not bent.")

if __name__=="__main__":
    main()
