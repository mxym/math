"""Exact rails and profile for HigherQuotientReflectedSourceSwitch.md."""
from fractions import Fraction as F
from itertools import combinations

def f(s):
    return F(str(s))

def check(cond, label):
    if not cond:
        raise ValueError(label)

s0,s1,a0,a1,q0,q1,e0,e1,dr=map(f,(
    ".138",".139",".068",".069",".297",".298",".311",".321",".025"))
theta=F(7,32)
w=2*dr
r1=s1+w
check(s0+a0+q0==f(".503") and s1+a1+q1==f(".506"),"v>sqrt x")
check(q1<e0 and w<a0 and e0+a0>r1,"disjoint factors and ratio")
rails=(
    q1-e0,
    2*e1+r1+2*a1,
    theta+e1+q1+5*r1+2*a1,
    2*theta*(e1+a1-s0)+e1+q1+5*r1+2*a1)
check(rails==tuple(map(f,("-.013",".969","1.92075","1.81225"))),"rails")
check(2*e0>F(1,2) and 3*e1<1<4*e0,"source-mark rank")
check(1-e1>F(1,2) and 1-2*e0<F(1,2),"principal exhaustion")
check(1-2*e1>F(1,2)-e0 and 1-3*e0<F(1,2)-e1,"principal one-mark cut")
s,a,Q=map(f,(".1385",".0685",".2975"))
b=1-s-a-Q
fs=(a,Q,b/3,b/3,b/3)
U,V,B=map(f,(".070",".010",".501"))
q=sum(fs)
zs=[]
dm=F(0)
a2=0
for j in range(6):
    for J in combinations(range(5),j):
        t=sum((fs[i] for i in J),F(0))
        check(t!=q-B and t!=f(".142"),"no equality in chart")
        if t<q-B:
            zs.append(J)
            dm-=(-1)**j*(q+sum((fs[i] for i in J if t-fs[i]>U),F(0)))
            if t>f(".142"):
                a2+=(-1)**j
check(zs==[(),(0,),(1,),(2,),(3,),(4,),
           (0,2),(0,3),(0,4),(2,3),(2,4),(3,4)],"physical chart divisor list")
check(sum(fs)==1-s and dm/q==-2-(3*a+2*b)/q,"exact reverse coefficient")
check(a2==2 and dm/q+F(2,3)*a2<0,"prior positive-part sign")
check(all(t>V for t in fs) and all(t>dr for t in fs[2:]),"Selberg square on rough composite")
print("four dispersion rails, all principal exhaustion tests, and 32 reverse-profile divisors passed")
