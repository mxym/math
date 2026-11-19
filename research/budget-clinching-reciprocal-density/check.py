"""Exact finite sanity checks; no LP, network dependency or floating point."""
from fractions import Fraction as F
from itertools import product

def need(test):
    if not test:
        raise ArithmeticError("exact check failed")
h,r,T,c,d=F(28,5),F(3,5),F(1,10),F(1,100),F(1,100)
b=F(2); l=b-d; s=c*d; gamma=c/(2*b); Z=h+T*r/2; half=F(1,2)
def band(z):return sum(z>=x for x in [c,l,b])
table=[[half,half,0,0],[half,half,half,0],[1,half,half,gamma],[1,1,1-gamma,None]]
def x(v,t):
    i,j=band(v),band(t)
    if (i,j)!=(3,3):return table[i][j]
    if v==t:return half
    return half+(1 if v>t else -1)*s/(2*min(v,t)**2)
def primitive(v,t):
    breaks=sorted({z for z in [F(0),c,l,b,t,v] if 0<=z<=v})
    total=F(0)
    for left,right in zip(breaks,breaks[1:]):
        mid=(left+right)/2
        if band(t)==3 and b<=left and right<=t:
            total+=(right-left)/2+s*(1/right-1/left)/2
        else:total+=(right-left)*x(mid,t)
    return total
def pay(v,t):return v*x(v,t)-primitive(v,t)
grid=sorted({F(0),c/2,c,l,b,r,h,*(h*j/24 for j in range(25)),l-F(1,1000),b+F(1,1000)})
# Always use Fractions at interval endpoints (inc. zero).
payments={};xp={}
for v,t in product(grid,repeat=2):
    X=x(v,t); P=pay(v,t)
    need(X+x(t,v)==1 and 0<=X<=1 and 0<=P<=1 and P<=v*X)
    payments[v,t]=P;xp[v,t]=X
for v,w,t in product(grid,repeat=3):
    need(v*xp[v,t]-payments[v,t]>=v*xp[w,t]-payments[w,t])
print(f"PASS: {len(grid)**2} ordered pointwise feasibility, IR and hard-budget checks; {len(grid)**3} dominant-strategy comparisons including ties and boundaries")

# Integral pair m+n*log(h/2), treating the logarithm as a formal letter.
A=( -h,h ); Z2=Z*Z
m=c+(r*c-c*c/2)/6
j=c*c/2+(r*c*c/2-c**3/3)/6
# Three cells computed directly from moments/integrals, then divide by cd.
pr=d*((b-d/2)*m-j)
rh=-2*gamma*d*(h-b)*(h-b+d)/2
HH=(s*(h*h/4-1),-s*h)
actual=((pr+rh+HH[0])/s,HH[1]/s)
need(actual==(F(128407,720000)-A[0],-A[1]))
y=F(9,19);P=2*sum(y**(2*i+1)/(2*i+1) for i in range(9))
ceil=P+2*y**19/(19*(1-y*y))
need(T*(1+r)+T*T*r*r/4==F(1609,10000))
need(F(1609,10000)<F(33,200)<A[0]+A[1]*P<A[0]+A[1]*ceil<F(167,1000)<F(128407,720000))
gaplo=s/Z2*(actual[0]+actual[1]*ceil);gaphi=s/Z2*(actual[0]+actual[1]*P)
need(F(393,10**10)<gaplo<gaphi<F(395,10**10))
print("PASS: independent formal-log welfare identity, log bounds and 393/10^10 < normalized strict improvement < 395/10^10")

# A general-structure identity, not a finite proof of the continuum dual.
N=0
for alpha,beta in product([F(1,4),F(1),F(3)], [F(0),F(1,7),F(2),F(13,5)]):
    f=lambda z:1/(alpha+beta*z)
    g=lambda z:z/(alpha*(alpha+beta*z))
    for v,t in product(grid, repeat=2):
        need(g(v)-g(t)==(v-t)*f(v)*f(t));N+=1
print(f"PASS: {N} affine-reciprocal ordered-pair identities")
