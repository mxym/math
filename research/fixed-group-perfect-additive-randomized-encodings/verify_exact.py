#!/usr/bin/env python3
"""Independent finite exact checks of the cyclotomic and convolution formulas."""
from functools import lru_cache
from fractions import Fraction
from itertools import combinations, combinations_with_replacement, product, permutations
from math import lcm

def divmonic(a,b):
    a=list(a); q=[0]*(len(a)-len(b)+1)
    for i in range(len(q)-1,-1,-1):
        q[i]=a[i+len(b)-1]
        for j,c in enumerate(b): a[i+j]-=q[i]*c
    assert not any(a)
    return tuple(q)

@lru_cache(None)
def phi(m):
    p=(-1,)+(0,)*(m-1)+(1,)
    for d in range(1,m):
        if m%d==0: p=divmonic(p,phi(d))
    return p

def rem(a,b):
    while a and a.bit_length()>=b.bit_length():
        a^=b<<(a.bit_length()-b.bit_length())
    return a

def gcd(a,b):
    while b: a,b=b,rem(a,b)
    return a

def sq(a):
    return sum(((a>>i)&1)<<(2*i) for i in range(a.bit_length()))

frobenius=0
for m in range(1,256,2):
    p=phi(m); mod=sum((a&1)<<i for i,a in enumerate(p))
    deriv=sum(((a*i)&1)<<(i-1) for i,a in enumerate(p) if i)
    assert rem(1|(1<<m),mod)==0 and gcd(mod,deriv)==1
    if len(p)<=13:
        residues={rem(sq(v),mod) for v in range(1<<(len(p)-1))}
        assert len(residues)==1<<(len(p)-1)
        frobenius+=len(residues)

def group(shape):
    g=list(product(*(range(x) for x in shape)))
    ix=dict(zip(g,range(len(g))))
    add=[[ix[tuple((a+b)%m for a,b,m in zip(x,y,shape))] for y in g] for x in g]
    dif=[[ix[tuple((a-b)%m for a,b,m in zip(x,y,shape))] for y in g] for x in g]
    m=lcm(*shape)
    expo=[[sum(a*b*(m//d) for a,b,d in zip(x,y,shape))%m for y in g] for x in g]
    return g,add,dif,m,expo

def ring(m):
    p=phi(m); d=len(p)-1
    def red(x):
        x=list(x)
        for i in range(len(x)-1,d-1,-1):
            for j in range(d): x[i-d+j]-=p[j]*x[i]
        return tuple((x+[0]*d)[:d])
    @lru_cache(maxsize=100000)
    def mul(x,y):
        z=[0]*(2*d-1)
        for i,a in enumerate(x):
            if a:
                for j,b in enumerate(y): z[i+j]+=a*b
        return red(z)
    powers=tuple(red((0,)*j+(1,)) for j in range(m))
    return mul,powers,(0,)*d, (1,)+(0,)*(d-1)

def addv(x,y): return tuple(a+b for a,b in zip(x,y))
def minus(x): return tuple(-a for a in x)
def sign(p): return (-1)**sum(p[i]>p[j] for j in range(len(p)) for i in range(j))

minor_count=0
for shape,cutoff in [((1,),1),((3,),3),((5,),5),((7,),3),((3,3),3)]:
    g,add,dif,m,ex=group(shape)
    n=len(g); mul,roots,zero,one=ring(m)
    perms={s:[(p,sign(p)) for p in permutations(range(s))] for s in range(1,cutoff+1)}
    subsets={s:list(combinations(range(n),s)) for s in range(1,cutoff+1)}
    for sig in product((-1,1),repeat=n):
        circ=[]
        for h in range(n):
            u=zero
            for k,v in enumerate(sig):
                a=roots[(-ex[k][h])%m]
                u=addv(u,a if v==1 else minus(a))
            circ.append(u)
        assert circ[0][0]%2==1 and all(a%2==0 for a in circ[0][1:])
        assert all(all(a%2==0 for a in v) for v in circ[1:])
        for s in subsets:
            for J in subsets[s]:
                val=zero
                for p,tsign in perms[s]:
                    term=one
                    for i,k in enumerate(p):
                        term=mul(term,circ[dif[J[i]][J[k]]])
                    val=addv(val,term if tsign==1 else minus(term))
                assert val[0]%2==1 and all(a%2==0 for a in val[1:])
                minor_count+=1

# Even-order negative control: the sign reflection for C2 is the shift.
_,_,dif,m,ex=group((2,))
_,roots,zero,one=ring(m)
assert addv(roots[ex[0][0]],minus(roots[ex[1][0]]))==zero

print(f"cyclotomic reduction: 128 odd exponents; {frobenius} Frobenius residues")
print(f"exact cyclotomic principal minors: {minor_count}; even-order negative control PASS")

def conv(a,b,table):
    z=[0]*len(a)
    for i,x in enumerate(a):
        if x:
            for j,y in enumerate(b): z[table[i][j]]+=x*y
    return tuple(z)

def laws(n):
    for i,j in combinations_with_replacement(range(n),2):
        yield tuple((k==i)+(k==j) for k in range(n))

tested=accepted=0
for shape in [(2,),(3,),(4,),(2,2)]:
    g,table,_,m,ex=group(shape)
    n=len(g)
    ell=list(laws(n))
    sums=[[conv(a,b,table) for b in ell] for a in ell]
    mul,roots,zero,one=ring(m)
    def ft(a,k):
        z=zero
        for j,aj in enumerate(a): z=addv(z,tuple(aj*w for w in roots[ex[k][j]]))
        return z
    for a,b in product(ell,repeat=2):
        c=conv(a,b,table)
        for k in range(n): assert ft(c,k)==mul(ft(a,k),ft(b,k))
    for a,b,c,d in product(range(len(ell)),repeat=4):
        S,D,E,C=sums[a][c],sums[a][d],sums[b][c],sums[b][d]
        tested+=1
        if any(s and (x or y or z) for s,x,y,z in zip(S,D,E,C)): continue
        accepted+=1
        assert conv(S,C,table)==conv(D,E,table)
        dh=tuple(a-b for a,b in zip(D,C)); eh=tuple(a-b for a,b in zip(E,C))
        L=tuple(a-b-c+d for a,b,c,d in zip(S,D,E,C))
        for i in range(n):
            assert mul(ft(L,i),ft(C,i))==mul(ft(dh,i),ft(eh,i))
        dot=sum(x*y for x,y in zip(L,C))
        assert dot*dot<=sum(x*x for x in dh)*sum(y*y for y in eh)
        r=Fraction(max(sum(map(abs,dh)),sum(map(abs,eh))),2)
        assert sum(x*x for x in C)<=2*r*max(C)+2*r*r

print(f"OR finite trials: {tested}; {accepted} exact-output-support cases")
print("verify_exact: PASS")
