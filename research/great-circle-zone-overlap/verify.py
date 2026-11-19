"""Finite rational geometry checks. Not a substitute for the convergence proof."""
from fractions import Fraction as F
from itertools import product

def require(p):
    if not p:
        raise ArithmeticError("identity or inequality failed")

def pairs():
    for j in range(1, 21):
        t = F(j, 21)
        yield (1-t*t)/(1+t*t), 2*t/(1+t*t)

vtx = rec = inner = 0
for c,r in pairs():
    require(c*c+r*r==1)
    for d in range(3,31):
        h=F(1,d)
        pc=[(x,(z-c*x)/r) for x,z in product((-h,h),repeat=2)]
        R=max(x*x+y*y for x,y in pc)
        require(R == 2*h*h*(1+c)/(r*r)); vtx+=1
        if r>=4*h:
            require(R<=F(1,4))
            # Since (1-z)^{-1/2} <= 1+z for 0<=z<=1/4.
            require((1-R)*(1+R)**2>=1); inner+=1
        for x,y in product((-h/2,h/2),(-h/(2*(h+r)),h/(2*(h+r)))):
            require(x*x+y*y<1 and abs(c*x+r*y)<=h); rec+=1
print("parallelogram extremal-radius identities:", vtx)
print("small-angle clipping-safe rectangle corners:", rec)
print("separated whole-parallelogram Jacobian bounds:", inner)
# ||uu^T-vv^T||_F^2=2[1-(u.v)^2] and isometric differential.
vs=[(F(0),F(0),F(1))]+[(r,F(0),c) for c,r in pairs()]+[(F(0),r,c) for c,r in pairs()]
for u,v in product(vs,repeat=2):
    dot=sum(x*y for x,y in zip(u,v))
    require(sum((u[i]*u[j]-v[i]*v[j])**2 for i,j in product(range(3),repeat=2))==2*(1-dot*dot))
for c,r in pairs():
    u=(c,r,0); w=(-r,c,0)
    require(sum((w[i]*u[j]+u[i]*w[j])**2 for i,j in product(range(3),repeat=2))==2)
require(F(8**2,2)==32 and F(8,2)==4)
print("projective distance / tangent isometry:", len(vs)**2, "/", 20)
print("critical ordinary-area coefficient: 32; linear coefficient: 4*pi")
