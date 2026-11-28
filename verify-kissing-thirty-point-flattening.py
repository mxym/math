#!/usr/bin/env python3
"""Exact controls for the thirty-atom flattening inequality and the 58-point code."""
from fractions import Fraction as Q
from itertools import combinations, product

def flattening():
    d=30; L=Q(99,25); h=Q(1,2)-Q(4,d); J=Q(31,2)
    # The coefficient identities are linear in lambda; these differences span trace zero.
    for t in range(d-1):
        w=[int(i==t)-int(i==d-1) for i in range(d)]
        A=[[Q(w[i]+w[j],10)+(Q(4,5)*w[i] if i==j else 0) for j in range(d)] for i in range(d)]
        assert all(A[i][i]==w[i] for i in range(d))
        for i,j in combinations(range(d),2):
            assert 2*A[i][j]+2*Q(2,5)*(w[i]+w[j])==w[i]+w[j]
        assert sum(A[i][i] for i in range(d))==0
        assert sum(x*x for row in A for x in row)==Q(39,25)*sum(v*v for v in w)
        assert all(sum(row)==Q(d+8,10)*v for row,v in zip(A,w))
    assert (Q(4,5)**2*Q(d-1,d))<Q(79,100)**2
    assert Q((d+8)**2,100*d)==Q(361,750)<Q(6,5)*(Q(6,5)-Q(79,100))
    for k in range(d+1):
        for m in range(d-k+1):
            X=1+Q(m,2)
            if not k: assert Q(4,25)*X<=L
            elif k==1:
                assert X<=J and Q(36,25)*J/(J-h)+Q(4,25)*J==Q(22444,5675)<L
            else:
                assert X<=15 and h<=Q(15,d) and Q(39,25)+Q(4,25)*15==L
    assert 1-L/4==Q(1,100)

def signed_incidence_control():
    # A small exhaustive control of signs, omitted edges and centering, distinct from the proof.
    pairs=list(combinations(range(5),2))
    for z in product([-1,0,1],repeat=len(pairs)):
        m=sum(t!=0 for t in z); s=sum(z); a=[0]*5
        for (i,j),v in zip(pairs,z):a[i]+=v;a[j]+=v
        p=sum(t for t in z if t>0);q=p-s
        assert sum(x*x for x in a)<=m+p*p+q*q
        assert 10*sum(x*x for x in a)-8*s*s<=(10+5*m)*m-3*s*s

def obstruction():
    m=28; k=Q(-7,16); p=Q(29,56); u=1-p; q=Q(1,5)
    H=lambda y:y*(y-Q(1,4))
    f=lambda x:H(x*x)
    a=p-u/(m-1); c=p*k-u; e=p*k+u/(m-1)
    assert (a,c,e)==(Q(1,2),Q(-635,896),Q(-187,896))
    assert p*k*k<Q(1,4) and c<=Q(1,2) and e<=Q(1,2)
    expected=Q(-1394362953,16112838246400)
    assert q*q*(f(1)-f(k))+(f(1)+(m-1)*f(a)-f(c)-(m-1)*f(e))/m-2*q*(H(p)-H(p*k*k))==expected
    # From the actual orthogonal pole/simplex vector formula, not orbit multiplicities.
    ids=[(layer,j) for layer in (0,1) for j in range(-1,m)]
    def b(x):
        i,j=x;return (1 if i==0 else -1)*(q if j<0 else -Q(1,m))
    def gram_squared(x,y):
        i,j=x;t,l=y
        pole=1 if i==t else k
        if j<0 and l<0:return pole*pole
        if j<0 or l<0:return p*pole*pole  # raw entry is -sqrt(p)*pole
        simplex=1 if j==l else -Q(1,m-1)
        dot=p*pole+u*(1 if i==t else -1)*simplex
        assert x==y or dot<=Q(1,2)
        return dot*dot
    assert len(ids)==58 and sum(map(b,ids))==0
    assert sum(b(x)*b(y)*H(gram_squared(x,y)) for x in ids for y in ids)==2*expected<0

if __name__=='__main__':
    flattening();signed_incidence_control();obstruction()
    print('PASS: 99/25 conditional trace bound; 58-point separated negative direction')
