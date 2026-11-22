"""Exact small controls. Standard library only; python3 -O works."""
from math import gcd, isqrt
from itertools import combinations

def need(cond):
    if not cond:
        raise ValueError("failed exact check")

def factor(n):
    f = {}
    d = 2
    while d*d <= n:
        while n % d == 0:
            f[d] = f.get(d, 0) + 1
            n //= d
        d += 1
    if n > 1:
        f[n] = 1
    return f

def prime(n):
    return n > 1 and factor(n) == {n: 1}

def class_tables(lim):
    # Positive definite reduced forms, odd discriminants only.
    # Return 3H and 3 times the primitive weighted number.
    allf, prim = [0]*(lim+1), [0]*(lim+1)
    for a in range(1, isqrt(lim//3)+1):
        for b in range(-a+1, a+1):
            if b % 2 == 0:
                continue
            for c in range(a, (lim+b*b)//(4*a)+1):
                if a == c and b < 0:
                    continue
                d = 4*a*c-b*b
                w = 1 if a == b == c else 3
                allf[d] += w
                if gcd(gcd(a,b),c) == 1:
                    prim[d] += w
    return allf, prim

def rows():
    M = 20000
    H,h = class_tables(M)
    count = 0
    for a in range(3, isqrt(M)+1, 2):
        for b in range(a+2, M//a+1, 2):
            if (a+b)%4 or gcd(a,b) != 1 or isqrt(a)**2 == a or isqrt(b)**2 == b:
                continue
            fa,fb = factor(a),factor(b)
            aa = [r for r,e in fa.items() if e%2]
            bb = [r for r,e in fb.items() if e%2]
            nr = False
            if len(aa) == len(bb) == 1:
                p,q = aa[0],bb[0]
                nr = pow(q,(p-1)//2,p) == p-1
            im = nr and fa[aa[0]]%4 == 1 and fb[bb[0]]%4 == 1
            pr = nr and len(fa) == len(fb) == 1
            need((H[a*b]%4 == 2) == im)
            need((h[a*b]%4 == 2) == pr)
            count += 1
    return count

def seven(p,q):
    return (p,q,2*q+p,(3*q-p)//4,(q-3*p)//4,(3*q+p)//2,(q-p)//2)

def gt_controls():
    slopes=[(1,0),(0,1),(1,2),(-1,3),(-3,1),(1,3),(-1,1)]
    need(all(a*d-b*c for (a,b),(c,d) in combinations(slopes,2)))
    for l in [r for r in range(3,1000,2) if prime(r)]:
        inv4 = pow(4,-1,l)
        inv2 = pow(2,-1,l)
        p,q = 1,-1
        vals = (p,q,2*q+p,(3*q-p)*inv4,(q-3*p)*inv4,(3*q+p)*inv2,(q-p)*inv2)
        need(all(v%l for v in vals))
    for x in range(8):
        for y in range(8):
            need(all(v%2 for v in seven(8*x+3,8*y+5)))
    flags = set()
    for p,q in [(10267,41813),(10891,44549)]:
        need(p%8 == 3 and q%8 == 5 and 4*p < q and 10*q < 41*p)
        vals = seven(p,q)
        need(all(prime(x) for x in vals))
        candidates = []
        for Q,u,v in [(vals[1],vals[3],vals[4]),(vals[2],vals[5],vals[6])]:
            n=(p+Q)//4
            need(p*u*u+Q*v*v==4*n**3 and len({p,Q,u,v})==4)
            need(gcd(p*u*u,Q*v*v)==1)
            if pow(Q,(p-1)//2,p) == p-1:
                candidates.append(Q)
        need(len(candidates)==1)
        flags.add(candidates[0]==q)
    need(flags=={False,True})

if __name__=="__main__":
    gt_controls()
    print("PASS seven directions, local conditions, both switch branches;",rows(),"coprime nonsquare class-number rows")
