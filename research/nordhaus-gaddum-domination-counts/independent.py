from itertools import combinations

def require(x):
    if not x:
        raise RuntimeError("exact validation failed")

def vertices(x):
    while x:
        lsb=x&-x
        yield lsb.bit_length()-1
        x ^= lsb

def cube(x):
    s=x
    while s:
        yield s
        s=(s-1)&x
    yield 0

def check(A):
    n=len(A)
    cap=(1<<n)-1
    B=[cap^(a|(1<<i)) for i,a in enumerate(A)]
    # Compare complement neighborhood cubes with direct closed-neighborhood domination test.
    for rows,other in [(A,B),(B,A)]:
        failure={s for mask in other for s in cube(mask)}
        direct={s for s in range(1<<n) if any((mask|(1<<i))&s==0 for i,mask in enumerate(rows))}
        require(failure==direct)
    return len(set(s for a in A for s in cube(a)))+len(set(s for b in B for s in cube(b)))

checks=0
for n in range(2,7):
    pairs=list(combinations(range(n),2))
    for bits in range(1<<len(pairs)):
        A=[0]*n
        for k in vertices(bits):
            i,j=pairs[k]
            A[i]|=1<<j
            A[j]|=1<<i
        d=check(A)
        m=n//2
        if n>=4:
            require(d>=2*((1<<m)+(1<<(n-m)))-4)
        checks+=1
require(2**9>5)
print(f"{checks} finite neighborhood-union and direct domination comparisons; PASS")
from fractions import Fraction as F
for parity in (0,1):
    table=[F(63,64)*F(2)**(j+1)+F(2)**(parity-1-j) for j in range(-2,3)]
    require(min(table)==[F(127,64),F(95,32)][parity])
    print("cohort parity",parity,table)
require(F(1,8)-6*F(2)**(-6)-9*F(2)**(-14)>0)
require(2*11**2<2**8 and F(62*160,155)==64)
require(F(1,8)-2*F(2)**(-5)-F(2)**(-6)>0)
require(F(1,8)-F(2)**(-7)-F(2)**(-5)-F(2)**(-6)>0)
print("short-cover twin thresholds and slack inequalities exact; PASS")
