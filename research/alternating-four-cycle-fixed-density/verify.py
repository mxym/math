"""Independent finite enumeration & exact arithmetic sanity tests. Python standard library only."""
from itertools import permutations, product
from fractions import Fraction as F
from math import comb
def red(i,j,q):
    u,v=q[i],q[j]
    return i!=j and ((u==v==0) or (u>0 and v>0 and u!=v))
def graph(m,h):
    q=[0]*(2*m+h)+[1]*m+[2]*m+[3]*m; n=len(q)
    S=range(n)
    return n, {(i,j) for i in S for j in S if red(i,j,q)}
for h in (1,0):
    counts=[]
    for m in range(1,6):
        n,E=graph(m,h)
        k=sum((u,v) in E and (w,x) in E and (v,w) not in E and (x,u) not in E for u,v,w,x in permutations(range(n),4))
        assert F(len(E)//2,comb(n,2))==F(2,5)
        if h==1:assert all(sum((i,j) in E for j in range(n))==2*m for i in range(n))
        assert k==2*(2*m+h)*(2*m+h-1)*6*m*m+6*(m*(m-1))**2
        assert k==(54*m**4+12*m**3+6*m*m if h else 54*m**4-36*m**3+6*m*m)
        counts.append(k)
    print('clique size = 2m+'+str(h),counts)
# Exact independent type sampling; equal-mass classes 0,1 together give the clique.
def R(i,j):return (i<2 and j<2) or (i>=2 and j>=2 and i!=j)
num=sum(R(u,v) and R(w,x) and not R(v,w) and not R(x,u) for u,v,w,x in product(range(5),repeat=4))
assert num==54 and sum(R(i,j) for i,j in product(range(5),repeat=2))==10
# Q(sqrt(10)), ordered rational pairs. Check exact clique profile without SymPy.
def add(x,y):return tuple(a+b for a,b in zip(x,y))
def mul(x,y):return (x[0]*y[0]+10*x[1]*y[1],x[0]*y[1]+x[1]*y[0])
def scale(c,x):return (c*x[0],c*x[1])
def sq(x):return mul(x,x)
a=(F(1,3),F(1,30)); b=(F(1,3),F(-1,15))
assert add(scale(2,a),b)==(1,0)
rho=add(scale(2,sq(a)),sq(b));assert rho==(F(2,5),0)
p=add(sq(rho),scale(-1,add(scale(2,sq(sq(a))),sq(sq(b)))))
assert p==(F(103,1350),F(2,675))
gap=add((F(num,625),0),scale(-1,p));assert gap==(F(341,33750),F(-100,33750))
assert 341**2>100**2*10
print('patterns',num,'/ 625; exact clique profile, strict gap: PASS')
