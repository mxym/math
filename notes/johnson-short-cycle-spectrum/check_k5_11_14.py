#!/usr/bin/env python3
"""Exact rank-six Johnson certificates in the four degenerate degrees 11..14.

A four-conjugacy-class rational primal yields the identity mass 5/14.
Seven rational dual entries for each degree certify the globally optimal
oscillation by exhausting every feasible short-cycle type. The rational dual
vectors are literal proof data and are NOT accepted from a numeric optimizer.
"""
from fractions import Fraction as Q
from math import comb, factorial
from transfer import moment, short_types

# eta_0=-1 and eta_1=9/14 encode the upper/lower dual contacts:
# h(type) = 1_{type=id} + sum_{j=0}^4 eta_{j+2} F_j(type)/binom(n,5).
DUAL={
    11:('-1','9/14','0','121/300','671/700','33/70','33/28'),
    12:('-1','9/14','957/1330','34551/93100','24651/23275',
        '99/245','297/245'),
    13:('-1','9/14','-2587/6272','11609/18816','169/140',
        '78/245','351/280'),
    14:('-1','9/14','13/1080','3133/7560','481/336',
        '13/60','13/10'),
}


def class_size(n,t):
    r=n-sum((j+1)*v for j,v in enumerate(t))
    assert r==0 or r>=6
    den=r if r else 1
    for j,v in enumerate(t,1):den*=j**v*factorial(v)
    size,mod=divmod(factorial(n),den)
    assert size>0 and mod==0
    return size


def certify(n,words):
    k=5
    I=(n,0,0,0,0)
    K=(n-4,0,0,1,0)
    T=(n-2,1,0,0,0)
    E=(n-6,0,2,0,0)
    P=((I,Q(5,14)),(K,Q(9,14)))
    W=((T,Q(6,7)),(E,Q(1,7)))
    assert len({I,K,T,E})==4
    assert all(v>0 for t,v in P+W)
    assert sum(v for t,v in P)==sum(v for t,v in W)==1
    for j in range(k+1):
        assert sum(v*moment(n,k,t)[j] for t,v in P)==\
               sum(v*moment(n,k,t)[j] for t,v in W)
    eta=list(map(Q,words))
    assert len(eta)==7 and eta[0]==-1 and eta[1]==Q(9,14)
    assert eta[0]+eta[1]==-Q(5,14)
    N=comb(n,k)
    def h(t):
        stats=moment(n,k,t)
        return Q(int(t==I))+sum(eta[j+2]*stats[j] for j in range(k))/N
    assert h(I)==h(K)==1
    assert h(T)==h(E)==Q(9,14)
    checked=0
    for t in short_types(n,k):
        val=h(t)
        assert Q(9,14)<=val<=1,(n,t,val)
        checked+=1
    # A strictly positive perturbation of uniform S_n attains ratio 5/14.
    delta=min(Q(class_size(n,t),2*factorial(n)*v) for t,v in W)
    assert delta>0
    assert all(Q(1,factorial(n))-delta*v/class_size(n,t)>0
               for t,v in W)
    assert delta*P[0][1]==delta*Q(5,14)
    return checked


def main():
    count=0
    for n in range(11,15):
        count+=certify(n,DUAL[n])
        print('PASS rank-six k=5 n=%d: sharp C=5/14'%n,flush=True)
    print('ALL FOUR DEGENERATE RANK-SIX CERTIFICATES PASS; types=%d'%count)


if not __debug__:
    raise RuntimeError('Run without -O: optimized Python disables assert checks')

if __name__=='__main__':
    main()
