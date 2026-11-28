#!/usr/bin/env python3
"""Independent rational reconstructor solve and integer image index tests."""
from fractions import Fraction as Q
from itertools import combinations
from math import factorial, gcd, lcm, prod
from random import Random


def echelon(rows):
    r=[list(map(Q,a)) for a in rows]
    i=0
    for j in range(len(r[0])):
        pivot=next((k for k in range(i,len(r)) if r[k][j]),None)
        if pivot is None:
            continue
        r[i],r[pivot]=r[pivot],r[i]
        s=r[i][j]
        r[i]=[a/s for a in r[i]]
        for k in range(len(r)):
            if k!=i and r[k][j]:
                c=r[k][j]
                r[k]=[a-c*b for a,b in zip(r[k],r[i])]
        i+=1
        if i==len(r):
            break
    return r,i


def solve(rows,b):
    m=len(rows)
    r,rank=echelon([list(a)+[c] for a,c in zip(rows,b)])
    assert rank==m and all(r[i][i]==1 for i in range(m))
    return [a[-1] for a in r]


def det(rows):
    a=[list(x) for x in rows]
    d=1
    prev=1
    for i in range(len(a)-1):
        j=next((j for j in range(i,len(a)) if a[j][i]),None)
        if j is None:
            return 0
        if j!=i:
            a[i],a[j]=a[j],a[i]
            d=-d
        pivot=a[i][i]
        for j in range(i+1,len(a)):
            for k in range(i+1,len(a)):
                a[j][k],rem=divmod(pivot*a[j][k]-a[j][i]*a[i][k],prev)
                assert rem==0
            a[j][i]=0
        prev=pivot
    return d*a[-1][-1]


def target_order(C,y):
    # [Z^r:im_Z C] / [Z^r:im_Z(C|y)] = order of y in the quotient.
    cols=list(zip(*C))
    r=len(y)
    base=abs(det(C))
    assert base
    idx=0
    for subset in combinations(cols+[tuple(y)],r):
        idx=gcd(idx,det(tuple(zip(*subset))))
    assert idx and base%idx==0
    return base//idx


def norm_table(rows,t):
    target=[1]+[0]*(t-1)
    tbl={}
    d=1
    for T in combinations(range(len(rows)),t):
        a=solve(list(zip(*(rows[i] for i in T))),target)
        d=lcm(d,*(v.denominator for v in a))
        tbl[T]=a
    out={T:{i:int(a*d) for i,a in zip(T,v)} for T,v in tbl.items()}
    for T,v in out.items():
        assert all(v.values())
        assert [sum(v[i]*rows[i][j] for i in T) for j in range(t)]==[
            d*e for e in target]
    return out


def verify_divisors(n,t,tbl):
    B=max(abs(a) for v in tbl.values() for a in v.values())
    assert B>=max(t,n-t+1)
    cases=0
    for J in combinations(range(n),t-2):
        I=[i for i in range(n) if i not in J]

        def coeff(i,j):
            return abs(tbl[tuple(sorted(J+(i,j)))][i])

        # Locate extrema by the least endpoint coefficient at both ends,
        # without using the quotient coordinates or their sorting.
        choices=[(lo,hi) for lo,hi in combinations(I,2)
                 if all(coeff(lo,i)>coeff(lo,hi) and coeff(hi,i)>coeff(hi,lo)
                        for i in I if i not in (lo,hi))]
        assert len(choices)==1
        lo,hi=choices[0]
        a,b=coeff(lo,hi),coeff(hi,lo)
        dset=set()
        for i in I:
            if i in (lo,hi):
                continue
            d,e=coeff(lo,i)-a,coeff(hi,i)-b
            assert 0<d<=B-a and 0<e<=B-b and d*e==a*b
            dset.add(d)
        assert len(dset)==n-t
        cases+=1
    return cases


def main():
    ideals=0
    for n in range(3,10):
        for t in range(2,n):
            k=n-t
            all_orders=[]
            for J in combinations(range(n),k+1):
                C=[[j**p for j in J] for p in range(k+1)]
                m=target_order(C,[0]*k+[1])
                all_orders.append(m)
                # Local target lattice is exactly the intersection of all
                # constraints obtained by complementing one of these labels.
                local=lcm(*(abs(prod(j-u for u in J if u!=j))
                             for j in J))
                assert local==m
                ideals+=1
            L=lcm(*all_orders)
            assert L%lcm(*range(1,t+1))==0
            assert factorial(n-1)%L==0
            if k==1:
                assert L==lcm(*range(1,t+1))

    rng=Random(67129)
    models=quotients=0
    for n in range(3,9):
        for t in range(2,n):
            for rep in range(3):
                z=rng.sample(list(range(-15,0))+list(range(1,16)),n)
                c=[rng.choice([-5,-4,-3,-2,-1,1,2,3,4,5]) for _ in z]
                rows=[[a*x**j for j in range(t)] for a,x in zip(c,z)]
                for U in combinations(range(n),t-1):
                    assert echelon([rows[i] for i in U]+[[1]+[0]*(t-1)])[1]==t
                tbl=norm_table(rows,t)
                L=lcm(*(abs(a) for v in tbl.values() for a in v.values()))
                assert L%lcm(*range(1,t+1))==0
                quotients+=verify_divisors(n,t,tbl)
                models+=1

    # An all-pair-sum reconstructor has B=1 but its public equations
    # imply a forbidden singleton scalar identity; AR cannot be dropped.
    R=[[1,-1,-1,0],[1,-1,0,-1],[1,0,-1,-1]]
    assert echelon(R)[1]==echelon(R+[[1,-2,0,0]])[1]
    print(f"independent: {ideals} local lattice image orders via determinantal index PASS")
    print(f"independent: {models} rational designs, {quotients} rank-two quotients and AR negative control PASS")


if __name__=="__main__":
    main()
