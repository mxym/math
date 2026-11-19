from fractions import Fraction as F
from math import factorial
from itertools import product
def ck(b):
    if not b: raise RuntimeError("exact audit failed")
for line in ((1,2,31,47),(1,-2,31,47),(1,0,23,55)):
    a,b,c,z=line
    ck(a>0 and a*c-b*b>0 and z>0 and a+c+z==79)
def invtrace(A):
    a,b,c,z=A
    return (2+a+c)/((1+a)*(1+c)-b*b)+1/(1+z)
def J(A,B):
    A,B=map(lambda q:tuple(map(F,q)),(A,B))
    return (invtrace(A)+invtrace(B))/2-invtrace(tuple((a+b)/2 for a,b in zip(A,B)))
p=(1,2,31,47)
q=(1,-2,31,47)
r=(1,0,23,55)
ck(J(p,q)==F(17,480) and J(p,r)==J(q,r)==F(4241,480480))
ck(J(p,q)-4*J(p,r)==F(53,480480))
# Get degree-six trace coefficients by direct walk enumeration on the block
# [[s+z, x], [x, s-z]], rather than spectral-binomial expansion.
entries={(0,0):[((1,0,0),1),((0,0,1),1)],
         (1,1):[((1,0,0),1),((0,0,1),-1)],
         (0,1):[((0,1,0),1)], (1,0):[((0,1,0),1)]}
coef={}
for walk in product((0,1),repeat=6):
    for mon in product(*(entries[i,j] for i,j in zip(walk,walk[1:]+walk[:1]))):
        k=tuple(sum(m[0][j] for m in mon) for j in range(3))
        sign=(-1)**sum(m[1]<0 for m in mon)
        coef[k]=coef.get(k,0)+sign
def d(k):
    return coef.get(k,0)*factorial(k[0])*factorial(k[1])*factorial(k[2])
positive=d((0,6,0))
negative=d((4,2,0))+d((0,6,0))+d((0,2,4))-2*d((2,4,0))-2*d((2,2,2))+2*d((0,4,2))
ck((positive,negative)==(1440,-96))
print('Direct trace walk derivatives:',positive,negative,'; reciprocal Jensen triangle gap:',J(p,q)-4*J(p,r),'; PASS')
