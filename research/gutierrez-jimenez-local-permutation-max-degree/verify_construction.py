#!/usr/bin/env python3
"""Verify the equivariant orbit exchanges and exact leading coefficients."""
from verify_coefficients import Field
from itertools import product

if not __debug__:
    raise RuntimeError("Run without -O.")

def orbit(F,a):
    res=[]
    while a not in res:
        res.append(a)
        a=F.pw(a,F.p)
    assert a==res[0]
    return res

def coefficient(F,fun,e):
    s=F.total(F.mul[F.pw(x,F.q-1-e)][fun[x]] for x in range(F.q))
    return F.mul[F.p-1][s]

def trade(F,A,C,B,n=3):
    p,q=F.p,F.q
    assert set(C)<=A and set(B).isdisjoint(A) and len(C)==len(B)
    assert F.total(A)==0 and len(A)%p==0 and F.total(C)!=F.total(B)
    sigma=list(range(q))
    for x,y in zip(C,B):
        sigma[x],sigma[y]=y,x
    Z=(A-set(C))|set(B)
    indicator=[int(x in Z) for x in range(q)]
    assert set(sigma)==set(range(q))
    assert {x for x in range(q) if sigma[x] in A}==Z
    assert all(F.add[y][1] in A for y in A)
    for x in range(q):
        assert sigma[F.pw(x,p)]==F.pw(sigma[x],p) and indicator[F.pw(x,p)]==indicator[x]
    assert coefficient(F,indicator,q-1)==0
    a=coefficient(F,indicator,q-2)
    assert a and a==F.mul[p-1][F.total(Z)] and a<p
    assert coefficient(F,sigma,q-1)==0
    for chosen in (0,1):
        assert set(F.add[sigma[x]][chosen*indicator[x]] for x in range(q))==set(range(q))
    if q<=49:
        # Direct top mixed coefficient, not inferred from the identity of polynomials.
        s=0
        for xs in product(range(q),repeat=n):
            y=F.total(sigma[x] for x in xs)
            y=F.add[y][int(all(x in Z for x in xs))]
            for x in xs:
                y=F.mul[y][x]
            s=F.add[s][y]
        s=F.mul[p-1][s] if n%2 else s
        assert s==F.pw(a,n)
    print(f"q={q}, monic modulus low terms {F.mod}: Frobenius orbits {C} ⇄ {B}; |A|={len(A)}; sum(Z)={F.total(Z)}; "
          f"indicator leading coefficient {a}; all slices verified")

def canonical(F):
    p=F.p
    a=p
    if F.r==p:
        a=next(x for x in range(p,F.q) if F.pw(x,p)==F.add[x][1])
        C=orbit(F,a)
        A=set(C)
        assert A=={F.add[a][j] for j in range(p)}
    else:
        A={F.add[x][j] for x in orbit(F,a) for j in range(p)}
        assert len(A)==p*F.r
        traces=[F.total(orbit(F,F.add[a][c])) for c in range(p)]
        assert set(traces)==set(range(p))
    b=next(x for x in range(p,F.q) if x not in A and (F.r!=p or F.total(orbit(F,x))!=0))
    B=orbit(F,b)
    if F.r!=p:
        c=next(x for x in (F.add[a][j] for j in range(p)) if F.total(orbit(F,x))!=F.total(B))
        C=orbit(F,c)
    trade(F,A,C,B)

def main():
    # First is the independent characteristic-5 witness with alpha^2=3.
    F=Field(5,(2,0));alpha=5
    assert F.mul[alpha][alpha]==3
    A={F.add[x][j] for x in orbit(F,alpha) for j in range(5)}
    trade(F,A,orbit(F,F.add[alpha][1]),orbit(F,F.mul[2][alpha]))
    # Same target size, independent presentation/choice of swapped cycle.
    canonical(Field(5,(3,0)))
    canonical(Field(7,(4,0)))
    canonical(Field(5,(1,1,0)))
    canonical(Field(3,(2,2,0)))
    # Characteristic two trade: A=Z={0,1}, sigma=identity.
    F4=Field(2,(1,1))
    def ind(x): return int(x in (0,1))
    assert coefficient(F4,[ind(x) for x in range(4)],2)==1
    assert all(len({F4.add[x][c*ind(x)] for x in range(4)})==4 for c in (0,1))
    print("q=4: characteristic-two two-point trade verified")
    # Negative control: no orbit exchange leaves sum(A)=0 and loses the top term.
    assert coefficient(F,[int(x in A) for x in range(25)],23)==0
    print("PASS Frobenius-orbit constructions and no-exchange negative control")

if __name__=="__main__":
    main()
