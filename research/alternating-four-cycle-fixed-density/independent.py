"""Exact matrix-walk count. Independent of the other verifier; Python standard library."""
from fractions import Fraction as Q
from itertools import product

def mm(a,b):return [[sum(u*v for u,v in zip(row,col)) for col in zip(*b)] for row in a]
def mats(m):
 label=[0]*(2*m+1)+[1]*m+[2]*m+[3]*m;n=len(label)
 def edge(i,j):return i!=j and (label[i]==label[j]==0 or (label[i]>0 and label[j]>0 and label[i]!=label[j]))
 R=[[int(edge(i,j)) for j in range(n)]for i in range(n)]
 B=[[int(i!=j)-R[i][j] for j in range(n)] for i in range(n)]
 assert {sum(r) for r in R}=={2*m}
 return R,B
for m in range(1,13):
 R,B=mats(m);M=mm(R,B);n=len(R)
 num=sum(M[i][j]*M[j][i] for i,j in product(range(n),repeat=2))
 spectral=(2*m*3*m)**2+(2*m*(2*m+1))**2+2*(m*(m-1))**2
 assert spectral==num==54*m**4+12*m**3+6*m*m
 print(m,n,num)
# Rational enclosure independent of square-root field manipulation: 3.16227 < sqrt(10) < 3.16228.
lo,hi=Q(316227,100000),Q(316228,100000)
assert lo**2<10<hi**2
a=(Q(1,3)+lo/30,Q(1,3)+hi/30);b=(Q(1,3)-hi/15,Q(1,3)-lo/15)
# Direct expression 2 a^4 + 4 a² b² bounded term-wise above on positive box.
upper=2*a[1]**4+4*a[1]**2*b[1]**2
p=Q(54,625)
assert p-upper>Q(733,1000000) and upper<Q(85667,10**6)
print('witness minus prescribed profile > 733/1000000;')
assert p>Q(859499752,10**10) and p>Q(8409772,10**8)
print('witness exceeds both printed numerical upper bounds; finite/check and limiting tests PASS')
