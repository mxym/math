"""Exact algebra checks for the reflected complementary prime tag."""
from math import prod


def need(test, message):
    if not test:
        raise ArithmeticError(message)


def factor(n):
    a = []
    p = 2
    while p*p <= n:
        while n % p == 0:
            a.append(p)
            n //= p
        p += 1
    if n > 1:
        a.append(n)
    return a


tested = high = repeats = 0
for m in range(4,4000):
    fac = factor(m)
    if len(fac)<2:
        continue
    distinct = set(fac)
    for bound in (int(m**.5)+1, int(m**.55)+1):
        if not bound*bound > m or not bound**3 < m*m:
            continue
        U = prod(r for r in distinct if r>bound)
        V = prod(m//v for v in distinct if m//v>bound)
        need((V==U)==(len(fac)==2) and V>=U,'nonnegative exact rank transfer')
        if len(fac)==len(distinct):
            collar = prod(m//v for v in distinct if v<=bound and m//v<=bound)
            k=len(fac)-1-int(U>1)
            need(V*collar == U*m**k,'exact squarefree collar formula')
            if U>1:
                need(V==U*m**(len(fac)-2),'exact highest-prime rank')
                high+=1
        repeats+=int(len(fac)>len(distinct))
        tested+=1
print('exact complementary log-product tests:',tested,'high squarefree:',high,'repeated:',repeats)
