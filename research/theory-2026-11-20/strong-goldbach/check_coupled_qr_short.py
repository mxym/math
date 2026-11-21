"""Exact rails and reflected rank signs in CoupledQRShortPart.md."""
from fractions import Fraction as F
from itertools import combinations

def f(s): return F(str(s))
def ck(cond, label):
    if not cond: raise ValueError(label)

s_lo,s_hi,a_lo,a_hi,Q_lo,Q_hi,r_lo,r_hi,b_lo,b_hi,c_lo,c_hi=map(f,(
    ".1384",".1386",".0684",".0686",".2974",".2976",
    ".1650",".1651",".16512",".16524",".16525",".16545"))
e0,e1,kmax,nu0,nu1=map(f,(".311",".321",".22",".3303",".3308"))
theta=F(7,32)
ck(b_lo+c_lo>=nu0 and b_hi+c_hi<=nu1, "alpha scale")
ck(sum((s_lo,a_lo,Q_lo,r_lo,b_lo,c_lo))<1<sum((s_hi,a_hi,Q_hi,r_hi,b_hi,c_hi)),"open physical cell")
rails=(
    e1-nu0,
    2*nu1+kmax,
    theta+nu1+e1+5*kmax,
    2*theta*(nu1-kmax)+nu1+e1+5*kmax)
ck(rails==tuple(map(f,("-.0093",".8816","1.97055","1.800275"))), "rails")
ck(r_hi<b_lo<b_hi<c_lo and e0>max(s_hi,a_hi,Q_hi,r_hi,b_hi,c_hi),"disjoint supports")
ck(f(".219")<kmax and F(1,2)-e0<f(".19"),"short d levels")
ck(4*kmax>1-e0 and 1-e0-kmax<F(1,2),"rough cofactor rank and products")
ck(1-e1>F(1,2),"full cofactor outside")
D,U=f(".219"),F(1,2)
def coefficient(a):
    return sum(((-1)**k*(1-sum(B))
       for k in range(len(a)+1) for B in combinations(a,k)
       if D<sum(B)<U),F(0))
checks=0
for p in range(3120,3210,10):
    p=F(p,10000)
    u=1-p
    ck(coefficient((u,))==0,"rank 1")
    for a in range(2201,4001,20):
        a=F(a,10000)
        b=u-a
        if b>kmax:
            ck(coefficient((a,b))<0,"rank 2")
            checks+=1
    for a in range(2201,2501,10):
        for b in range(2201,2501,10):
            a0,b0=F(a,10000),F(b,10000)
            c=u-a0-b0
            if c>kmax:
                ck(coefficient((a0,b0,c))==-u,"rank 3")
                checks+=1
u=1-f(".316")
ck(coefficient((u/4,)*4)==6-3*u>0,"rank 4 opposite witness")
print("four exact rails and",checks,"rank-two/three tests passed; rank-four adverse witness checked")
