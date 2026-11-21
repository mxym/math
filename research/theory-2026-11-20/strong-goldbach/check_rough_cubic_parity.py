from fractions import Fraction as Q
from itertools import combinations, combinations_with_replacement
from math import comb, prod


def require(ok, reason):
    if not ok:
        raise ArithmeticError(reason)


def F(t):
    return 1 - 6*t*t + 4*t*t*t


def y(t):
    return 4*t*(1-t)


def b(j):
    return Q(comb(2*j,j),4**j*(2*j-1))


def a(j):
    return b(j)+b(j-1)/2


def gg(J,t):
    A=1-sum(a(j) for j in range(2,J))
    return 1-sum(a(j)*y(t)**j for j in range(2,J))-A*y(t)**J


def sums(parts):
    for k in range(len(parts)+1):
        for idx in combinations(range(len(parts)),k):
            yield (-1)**k, sum((parts[i] for i in idx),Q(0))


def checks(parts):
    rows=list(sums(parts))
    rank=len(parts)
    sign=(-1)**rank
    full=sum(v*(3*(1-t)**2-2*(1-t)**3) for v,t in rows)
    short=[(v,t) for v,t in rows if t<Q(1,2)]
    # Tied half-exponent terms vanish for every polynomial used here.
    expected=1 if rank==1 else -12*prod(parts) if rank==3 else 0
    require(full==expected==Q(1-sign,2)*sum(v*F(t) for v,t in short), ('full',parts))
    for J in (2,3,5):
        main=sum(v*(F(t)+gg(J,t))/2 for v,t in short)
        twisted=sum(sign*v*(F(t)-gg(J,t)) for v,t in short)
        even=sum(v*gg(J,t) for v,t in short) if rank%2==0 else 0
        require(main-even-twisted/2==expected, ('split',parts,J))
        if J==2 and rank%2==0:
            known=(16*parts[0]**2*(1-parts[0])**2 if rank==2
                   else -192*prod(parts) if rank==4 else 0)
            require(known==even, ('quartic',parts))
    if rank==4:
        A1=sum(v*(1-2*t) for v,t in short)
        A3=sum(v*(1-2*t)**3 for v,t in short)
        fourwidth=prod(2*t_i for t_i in parts)
        psi0=A3/(6*fourwidth)
        psi2=A1/fourwidth
        direct=sum(v*F(t) for v,t in short)
        require(direct==fourwidth*(3*psi2-6*psi0)/2,('box',parts))
        require(psi0>=Q(1,2) and psi2<=0, ('density',parts))
        if parts[-1]<Q(1,2):
            minimum=min(parts[0],Q(1,2)-parts[-1])
            require(A1==-4*minimum and -direct>=6*minimum+24*prod(parts),
                    ('rebate',parts))


count=0
for k in range(1,7):
    for ints in combinations_with_replacement(range(1,19),k):
        if sum(ints)!=18:
            continue
        checks(tuple(Q(i,18) for i in ints))
        count+=1
for i in range(1001):
    t=Q(i,2000)
    for J in (2,3,5):
        A=1-sum(a(j) for j in range(2,J))
        require(0<=gg(J,t)<=F(t) and 0<=F(t)-gg(J,t)<=A*y(t)**J,
                ('series',t,J))
print(f'{count} rank/log profiles, 3003 symmetric polynomial checks: exact arithmetic passed.')
