"""Exact normalization checks on labelled constructed primes, not a factoring algorithm."""
from fractions import Fraction as Q
from math import isqrt, prod

def prime(n):
    return n >= 2 and (n == 2 or n % 2 and all(n%d for d in range(3,isqrt(n)+1,2)))

def floor_root(n,r):
    lo,hi=0,1 << ((n.bit_length()+r-1)//r)
    while hi-lo>1:
        m=(lo+hi)//2
        if m**r<=n:lo=m
        else:hi=m
    return lo

cases=[
    ("three-scaled", (1000000012367,2000000004757,5999999994271),
     ((0,1,2),(1,2,3)), (1,2,6), 12,
     (12000000148404,12000000028542,11999999988542)),
    ("reverse-and-tie", (2,7,3),
     ((0,1,3),(2,1,2)), (1,3,Q(3,2)), 9, (18,21,18)),
]
for name,p,edges,expected,B0,y0 in cases:
    r=len(p); N=prod(p); L=N.bit_length(); M=L
    assert len(set(p))==r and all(prime(x) for x in p)
    a={0:Q(1)};todo=list(edges);backwards=0
    while todo:
        next_edges=[]
        for i,j,m in todo:
            assert p[i]<p[j] and 1<=m<=M and abs(p[j]-m*p[i])**r<=p[i]*M**r
            if i in a:a[j]=m*a[i]
            elif j in a:a[i]=a[j]/m;backwards+=1
            else:next_edges.append((i,j,m))
        assert len(next_edges)<len(todo)
        todo=next_edges
    a=tuple(a[i] for i in range(r))
    assert a==expected
    B=prod(v.numerator for v in a); b=tuple(B/v for v in a)
    assert all(v.denominator==1 for v in b)
    y=tuple(int(v*x) for v,x in zip(b,p));K=N*prod(map(int,b));s=floor_root(K,r)
    assert B==B0 and y==y0 and K==prod(y) and s**r<=K<(s+1)**r
    H=(2*M)**(r-1);La=(r-1)*M**(r*(r-1))*M**r*H;J=4*La*M**(r-1)+1
    assert all(abs(v-s)**r<=J**r*s for v in y)
    print(name,"bitlength",L,"scaling",B,"backward steps",backwards,"repeated normalized values",r-len(set(y)))
    if name=="three-scaled":
        assert N==12000000165488000184024974662963966949
        assert K==1728000023830272026499596351466811240656 and s==12000000055162
        assert all(abs(q-u)**r>u*M**r for u in p for q in p if u<q)
        assert all((q-1)%u!=0 for u in p for q in p if u<q)
        print("three-scaled N,K,s",N,K,s)
        print("false all-unit slope template: zero admissible edges")
