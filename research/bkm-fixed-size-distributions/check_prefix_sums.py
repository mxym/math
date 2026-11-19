"""Compute prefix-sum Plancherel masses using the independent SYT branching recurrence."""
from functools import cache
from collections import Counter
from math import comb,factorial

def req(b,s):
    if not b:raise ArithmeticError(s)
@cache
def parts(n,k):
    if not n:return ((),)
    return tuple((i,)+p for i in range(1,min(n,k)+1) for p in parts(n-i,i))
@cache
def dim(a):
    if not a:return 1
    return sum(dim(tuple(z for z in a[:i]+(x-1,)+a[i+1:] if z)) for i,x in enumerate(a) if i==len(a)-1 or x>a[i+1])

for n in range(9,24):
    A=Counter()
    for a in parts(n,n):A[sum(a[:2])]+=dim(a)**2
    req(sum(A.values())==factorial(n),'mass')
    req((A[2],A[3],A[4])==(1,(n-1)**2,comb(2*n,n)//(n+1)-1-(n-1)**2+comb(n-1,2)**2),'coefficient formula')
    req(A[3]**2<A[2]*A[4],'strict violation')
    if n==9:
        req((A[2],A[3],A[4])==(1,64,5581),'nine')
        print('n=9 first-two-row masses',A[2],A[3],A[4])
print('PASS all shapes at sizes 9 through 23 by independent branching recurrence')
