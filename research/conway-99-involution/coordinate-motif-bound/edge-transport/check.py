from fractions import Fraction as F
from itertools import combinations
from math import ceil
D=F(196,9);L=F(-56,9);assert D-2*L**2/(D+L)==F(84,5)
def bound(q,b):
    multiplicities=[2]*b+[1]*(q-2*b)
    hi=sum(x*y for x,y in combinations(multiplicities,2))
    if (q,b)==(4,0):hi-=2
    return 2*q+3*b-hi-q//2
for q in range(1,5):
    print('q',q,'d lower bounds',[bound(q,b) for b in range(q//2+1)])
    assert min(bound(q,b) for b in range(q//2+1))>=2
for q in range(5,13):assert F(5,24)*q*q-q>0
assert F(7,9)+7==F(70,9) and F(70,9)+14==F(196,9)>F(88,9)
assert 44-(15-1)-21==9 and 9*7**2>44
assert 693+ceil(F(99*48,28))==863
assert min(n for n in range(693,1000) if n%3==0 and 28*(n-693)>=99*48)==864
print('n3 >=864; induced C6 >=',864+209286)
