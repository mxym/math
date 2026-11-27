#!/usr/bin/env python3
"""Recover autotopies from raw loop tables and compute the derived obstruction."""
from collections import deque
from itertools import product

if not __debug__:
    raise RuntimeError("Run without -O; assertions are the checks.")


def table(p, b=1, associative=False):
    E = list(product(range(p), range(p), range(b)))
    num = {e:i for i,e in enumerate(E)}
    L = tuple(tuple(num[((x+u)%p, (y+v+(0 if associative else x*x*u))%p,
                         (a+d)%b)] for u,v,d in E) for x,y,a in E)
    assert L[0] == tuple(range(len(E)))
    assert tuple(c[0] for c in L) == L[0]
    return E, num, L


def product_program(L, generator):
    # Derive each loop element as a parenthesized multiplication of 0 and g.
    todo, seen = [0,generator], {0,generator}
    program = []
    for x in todo:
        for y in todo:
            for a,b in ((x,y),(y,x)):
                c = L[a][b]
                if c not in seen:
                    todo.append(c)
                    seen.add(c)
                    program.append((a,b,c))
    assert len(todo) == len(L)
    return program


def find_over(L, generator, program, r, c):
    # For an autotopy over (r,c), gamma is precisely an isomorphism
    # to the principal isotope with product R_c^-1(x) * L_r^-1(y).
    n, out = len(L), []
    left = {v:u for u,v in enumerate(L[r])}
    right = {L[u][c]:u for u in range(n)}
    tau = tuple(tuple(L[right[x]][left[y]] for y in range(n)) for x in range(n))
    e = L[r][c]
    for a in range(n):
        if a == e:
            continue
        g = [-1]*n
        g[0], g[generator] = e,a
        seen = {e,a}
        for i,j,k in program:
            v = tau[g[i]][g[j]]
            if v in seen:
                break
            seen.add(v)
            g[k] = v
        else:
            if all(tau[g[i]][g[j]] == g[k]
                   for i,row in enumerate(L) for j,k in enumerate(row)):
                triple = tuple(right[x] for x in g), tuple(left[x] for x in g), tuple(g)
                R,C,S = triple
                assert (R[0],C[0]) == (r,c)
                assert all(L[R[i]][C[j]] == S[k]
                           for i,row in enumerate(L) for j,k in enumerate(row))
                out.append(triple)
    return out


def ident(n):
    return (tuple(range(n)),)*3


def mul(g,h):
    return tuple(tuple(a[i] for i in b) for a,b in zip(g,h))


def inv(g):
    R = []
    for a in g:
        b = [0]*len(a)
        for i,j in enumerate(a):
            b[j] = i
        R.append(tuple(b))
    return tuple(R)


def power(g,k):
    a = ident(len(g[0]))
    while k:
        if k&1:
            a = mul(a,g)
        g = mul(g,g)
        k >>= 1
    return a


def closure(G,n):
    a = ident(n)
    S,Q = {a},[a]
    for g in Q:
        for h in G:
            x = mul(g,h)
            if x not in S:
                S.add(x)
                Q.append(x)
    return S


def comm(g,h):
    return mul(mul(mul(g,h),inv(g)),inv(h))


def derived(G,n):
    # Normal closure of generator commutators, then subgroup closure.
    C = {comm(g,h) for g in G for h in G}
    Q = list(C)
    I = [inv(g) for g in G]
    for c in Q:
        for g,h in zip(G,I):
            d = mul(mul(g,c),h)
            if d not in C:
                C.add(d)
                Q.append(d)
    return closure(Q,n)


def orbit(G):
    S,Q = {(0,0)},[(0,0)]
    for i,j in Q:
        for r,c,_ in G:
            y = r[i],c[j]
            if y not in S:
                S.add(y)
                Q.append(y)
    return S


def check_factor_maps(triples,b):
    for g in triples:
        for a in g:
            assert all(a[i]//b == a[i-i%b]//b and a[i]%b == a[i%b]%b
                       for i in range(len(a)))


def verify(p,b):
    E,num,L = table(p,b)
    n = len(L)
    def index(x,y,a):
        return num[x,y,a%b]
    generator = index(1,0,1)
    program = product_program(L,generator)
    e = ident(n)
    A = find_over(L,generator,program,0,0)
    p_stabilizer = [g for g in A if power(g,p) == e]
    assert len(A) == p*(p-1)*(1 if b==1 else 2)
    assert len(p_stabilizer) == p

    seed_G, external_G, over_G = p_stabilizer[:], [], []
    for a,k in [(index(1,0,0),0),(index(0,1,0),0),(index(0,0,1),1)]:
        if not a:
            continue
        for r,c in ((a,0),(0,a)):
            possibilities = find_over(L,generator,program,r,c)
            assert len(possibilities) == len(A)
            over_G.extend(possibilities)
            order = p if k==0 else b
            gens = [g for g in possibilities if power(g,order) == e]
            assert gens
            if k:
                external_G.append(gens[0])
            else:
                seed_G.append(gens[0])
    assert len(orbit(seed_G+external_G)) == n*n
    full_order = n*n*len(A)
    assert full_order == p**5*(p-1)*(1 if b==1 else 18)

    if b > 1:
        check_factor_maps(A+over_G,b)

    P = closure(seed_G,n)
    assert len(P) == p**5
    D = derived(seed_G,n)
    assert len(D) == p**3
    killed = D.intersection(p_stabilizer)
    assert len(killed) == p and all(g[0][0] == g[1][0] == 0 for g in killed)
    print(f"p={p}, b={b}: |Aut_loop|={len(A)}, |Atop|={full_order}, "
          f"|P|={len(P)}, |P'|={len(D)}, |P' intersect stab|={len(killed)}")


def associative_control(p):
    E,num,L = table(p,associative=True)
    n = len(L)
    for x,y,a in E:
        R = tuple(num[(u+x)%p,(v+y)%p,b] for u,v,b in E)
        assert all(L[R[i]][j] == R[L[i][j]] and
                   L[i][R[j]] == R[L[i][j]] for i,j in product(range(n),repeat=2))
    # Independent translations commute, and the unique translations sending
    # (0,0) to each row/column give a regular subgroup for this control loop.
    row = tuple(num[(u+1)%p,v,b] for u,v,b in E)
    col = tuple(num[u,(v+1)%p,b] for u,v,b in E)
    I = ident(n)[0]
    assert comm((row,I,row),(I,col,col)) == ident(n)
    print("associative translation control PASS")


if __name__ == "__main__":
    verify(5,1)
    verify(7,1)
    verify(5,3)
    associative_control(5)
    print("PASS raw autotopy")
