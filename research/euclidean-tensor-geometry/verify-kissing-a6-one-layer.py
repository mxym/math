#!/usr/bin/env python3
"""Rational lower-envelope and perturbation checks for the A6 one-layer theorem."""
from fractions import Fraction as F
from itertools import combinations,product
if not __debug__:raise RuntimeError('enable assertions')
Q=[tuple(F(int(i<k))-F(k,7) for i in range(7))for k in range(7)]
def dot(v,w):return sum(a*b for a,b in zip(v,w))
C=[sum(x[:4])for x in Q]
g=[F(t)for t in (1,1,F(5,4),1,1,F(5,4),1)]
cut=[(7*c-7)/2 for c in C]
gap=[x-y for x,y in zip(g,cut)]
for k,v in enumerate(Q):
    assert dot(v,v)==F(k*(7-k),7)
    assert (C[k]+F(1,2))**2>=dot(v,v)
    assert F(2,7)*g[k]**2<=2-dot(v,v)
P=[v+(max(t,s),) for v,t,s in zip(Q,g,cut)]
for i,j in combinations(range(7),2):
    if gap[i]*gap[j]<0:
        t=gap[i]/(gap[i]-gap[j]);z=tuple(a+t*(b-a)for a,b in zip(Q[i]+(g[i],),Q[j]+(g[j],)))
        assert 7*sum(z[:4])==7+2*z[-1]
        P.append(z)
val=[dot(x[:7],y[6::-1])+F(2,7)*x[-1]*y[-1]for x,y in product(P,repeat=2)]
assert len(P)==12 and min(val)==-1
print('lower envelope: 12 generators, 144 pairs, minimum -1, next',sorted(set(val))[1])
e=F(1,100000);k=1+2*e;eta=20*e
assert 2-k*k*F(12,7)>F(1,4)
assert (k*k-1)*F(12,7)<7*e
assert F(9,1)**2>3**2+7**2 and 26**2>8*9**2
assert F(1,100)**2<F(2,7) and F(53,100)**2<F(2,7)
assert F(13,10)**2<F(12,7)
assert 2-F(99,100)**2>(1+7*e)**2
a=F(1,2)+73*e+800*e*e
assert a*a<F(43,171) and a>=F(1,2)+e
t=F(1,10**12)
assert 2*t+2*t*t<e*e and F(12,7)-2*t-t*t>(F(6,5)+e)**2
assert F(10,7)<F(6,5)**2 and 4*e<F(4,7)
print('nearby 77-site frame and near-minimum-layer conversion: PASS')
