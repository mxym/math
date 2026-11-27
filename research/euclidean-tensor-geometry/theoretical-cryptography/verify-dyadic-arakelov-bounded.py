#!/usr/bin/env python3
"""Integer checks for the dyadic bounded-band theta argument."""
from collections import Counter
from itertools import product


def basis(d,k,scale=1):
    a=[0]*d
    j,r=divmod(k,d)
    a[r]=(-1 if j%2 else 1)*scale
    return tuple(a)


def add(a,b):
    return tuple(x+y for x,y in zip(a,b))


def sub(a,b):
    return tuple(x-y for x,y in zip(a,b))


def multiply(a,b):
    d=len(a)
    out=[0]*d
    for i,x in enumerate(a):
        if x:
            for j,y in enumerate(b):
                if y:
                    k=i+j
                    out[k%d]+=(-1 if k>=d else 1)*x*y
    return tuple(out)


def conj(a):
    out=(0,)*len(a)
    for k,u in enumerate(a):
        if u:
            out=add(out,basis(len(a),-k,u))
    return out


def norm(a):
    d=len(a)
    prod=basis(d,0)
    for j in range(1,2*d,2):
        x=(0,)*d
        for k,u in enumerate(a):
            if u:
                x=add(x,basis(d,k*j,u))
        prod=multiply(prod,x)
    assert all(x==0 for x in prod[1:])
    return prod[0]


def trace_normalized(a):
    return a[0]


def gram(d,w):
    return tuple(tuple(trace_normalized(multiply(w,basis(d,i-j)))
                       for j in range(d)) for i in range(d))


def col_dot(a,b):
    return sum(x*y for x,y in zip(a,b))


def form(Q,x):
    return col_dot(x,(col_dot(r,x) for r in Q))


def check_orbits():
    checks = 0
    for d in (8,16,32,64):
        exps=(1, d//4, 1+d//4)
        # Monomial coordinates (X_2, X_1, X_3/(X_1 X_2)):
        # finite part has the four primitive 8th roots, third coordinate one.
        finite=Counter()
        for j in range(1,2*d,2):
            x1,x2,x3=(j*e%(2*d) for e in exps)
            assert (x3-x1-x2)%(2*d)==0
            finite[x2]+=1
        assert finite == Counter({j*d//4:d//4 for j in (1,3,5,7)})
        for k in product(range(-3,4),repeat=3):
            v=col_dot(exps,k)
            atom_sum=[0]*d
            for j in range(1,2*d,2):
                e,r=divmod(v*j,d)
                atom_sum[r]+= -1 if e%2 else 1
            expect=(0,)*d if v%d else basis(d,v,d)
            assert tuple(atom_sum)==expect
            checks+=1
        assert col_dot(exps,(-1,-1,1))==0
        assert basis(d,4*exps[1]) == basis(d,0,-1)
    return checks


def check_units():
    n = nrm = 0
    for d in (4,8,16,32,64):
        one=basis(d,0)
        sq2=sub(basis(d,d//4),basis(d,3*d//4))
        assert multiply(sq2,sq2)==basis(d,0,2)
        u,v=add(one,sq2),sub(sq2,one)
        assert multiply(u,v)==one and conj(u)==u
        assert norm(u)==norm(v)==1
        for k in (1,3,5,7):
            x=multiply(basis(d,k),u)
            inv=multiply(basis(d,-k),v)
            assert multiply(x,inv)==one and norm(x)==1
            w=multiply(inv,conj(inv))
            assert multiply(multiply(x,conj(x)),w)==one and norm(w)==1
            assert norm(sub(one,basis(d,k))) == 2
            nrm += 4
            Q=gram(d,w)
            assert all(Q[i][j] == Q[j][i] for i in range(d) for j in range(d))
            assert len({Q[i][i] for i in range(d)})==1
            for y in (basis(d,1),add(one,basis(d,2)),
                      add(sub(one,basis(d,1)),basis(d,3,-2))):
                z=multiply(y,x)
                assert form(Q,z)==col_dot(y,y)
                assert trace_normalized(multiply(w,multiply(z,conj(z))))==col_dot(y,y)
                n += 2
    return n,nrm


def check_local_shells():
    count=0
    for d in (4,8):
        element=add(basis(d,1),basis(d,-1))
        H=gram(d,element)
        assert all(H[i][i]==0 for i in range(d))
        H2=gram(d,multiply(element,element))
        assert H2==tuple(tuple(col_dot(H[i],(H[k][j] for k in range(d)))
                                     for j in range(d)) for i in range(d))
        sums=Counter()
        sums2=Counter()
        for x in product((-1,0,1),repeat=d):
            m=col_dot(x,x)
            sums[m]+=form(H,x)
            sums2[m]+=form(H2,x)
            count+=1
        assert all(v==0 for v in sums.values())
        assert sums2[1]==2*sum(H2[i][i] for i in range(d))
        assert sums2[2]==4*(d-1)*sum(H2[i][i] for i in range(d))
    return count


def main():
    moments=check_orbits()
    twists,norms=check_units()
    shells=check_local_shells()
    print(f"PASS: {moments} circle moment identities, {norms} algebraic norm "
          f"checks, {twists} exact unit-twisted energies and "
          f"{shells} signed coefficient-shell rows.")


if __name__=="__main__":
    main()
