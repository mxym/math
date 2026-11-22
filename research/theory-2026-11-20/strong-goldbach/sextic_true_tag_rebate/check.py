"""Rational outward checks for the true sextic tag rebate."""
from fractions import Fraction as Q
from math import comb, factorial as fac

pi_lo, pi_hi = Q(314159,100000), Q(314160,100000)
q=Q(4,3)
C=Q(3446,1000)
a,b=Q(1,100),Q(1,50)

def require(ok,msg):
    if not ok:
        raise ArithmeticError(msg)

def loglo(s,n=28):
    z=(s-1)/(s+1)
    return 2*sum(z**(2*j+1)/(2*j+1) for j in range(n))

def loghi(s,n=28):
    z=(s-1)/(s+1)
    return loglo(s,n)+2*z**(2*n+1)/((2*n+1)*(1-z*z))

def upow(x,e,prec=10**10):
    e=Q(e); target=x**e.numerator
    d=e.denominator
    U=1
    while Q(U,prec)**d < target:
        U*=2
    l=0
    while U-l>1:
        m=(U+l)//2
        if Q(m,prec)**d < target:
            l=m
        else:
            U=m
    return Q(U,prec)

def lpow(x,e):
    return upow(x,e)-Q(1,10**10)

def S(t):
    return t-t**3/72+t**5/9600

# Primitive of 2|sin(u/2)| minus its periodic mean has max norm <1.
x=Q(69,100)
require(x-x**3/6+x**5/120 < 2/pi_hi,"lower critical argument")
x=Q(7,10)
require(x-x**3/6 > 2/pi_lo,"upper critical argument")
x=Q(69,100)
require((4/pi_lo)*Q(7,5)-4*(x*x/2-x**4/24)<1,"primitive estimate")
# Subdivide [1,2π]; S increasing. The far tail pays norm/(2π).
log5=loglo(Q(5))
for i in range(100,629):
    lo,hi=Q(i,100),Q(i+1,100)
    require(S(hi)-q*loglo(lo)<log5,"first-period phase integral")
require(S(2*pi_hi)+1/(2*pi_lo)-q*loglo(2*pi_lo)<log5,
        "periodic phase integral")
require(log5>1,"phase at T<=1")
require(loghi(Q(2))<Q(7,10),"tag harmonic")

# Piecewise power plus exponential linear extension g_j, its two L² norms.
def norm_g(j,n):
    A=Q(3,4)
    a1,b1=Q(1),j+A
    for _ in range(n):
        a1,b1=b1-A*a1,-A*b1
    return ((Q(fac(j),fac(j-n)))**2/(2*(j-n)+1) +
            a1*a1/(2*A)+2*a1*b1/(2*A)**2+2*b1*b1/(2*A)**3)

def J_upper(j,R):
    return upow(2*pi_hi,Q(1,2))*(
        upow(norm_g(j,0),Q(1,2))*
        upow(2*(upow(Q(21,1000),2*q+1)+upow(R,2*q+1)/(2*q+1)),Q(1,2))
        +upow(norm_g(j,2),Q(1,2))*
        upow(2*upow(R,2*q-3)/(3-2*q),Q(1,2)))
J4,J6=J_upper(4,Q(69,100)),J_upper(6,Q(78,100))
require(J4<50 and J6<83,"collar transform norms")
E=C*10/(2*pi_lo*(1-b)) * (
    44*50*(upow(b,4-q)-lpow(a,4-q))/(4-q)
    +112*83*(upow(b,6-q)-lpow(a,6-q))/(6-q))
require(E<Q(115,1000),"literal seam debit")
m=78*(b-a)-288*(b*b-a*a)+Q(1504,3)*(b**3-a**3)-420*(b**4-a**4)+Q(672,5)*(b**5-a**5)
require(m>Q(697,1000)+Q(1,10**7),"negative signed main including endpoint correction")

# Piecewise polynomial negative extension: F(-3v)=(1-v)^5 sum_i c_i v^i.
h=Q(3); k=4; e=5
orig=[1,1,-39,-192,-376,-336,-112]
c=[sum(orig[i]*h**i*comb(e+j-i-1,j-i) for i in range(j+1)) for j in range(k+1)]
deg=e+k
P=[sum(c[i]*(-1)**(j-i)*comb(e,j-i) for i in range(k+1)
       if 0<=j-i<=e) for j in range(deg+1)]
L1=Q(1,2)+h*sum(abs(c[i])*Q(fac(i)*fac(e),fac(i+e+1)) for i in range(k+1))
jets={}
for j in range(deg+1):
    origin_minus=P[j]*(-1)**j*fac(j)/h**j
    origin_plus=orig[j]*(-1)**j*fac(j) if j<len(orig) else 0
    left=(-1)**(e+j)*Q(fac(j),1)/h**j*sum(c[i]*comb(i,j-e) for i in range(j-e,k+1)) if j>=e else 0
    right=1056 if j==4 else -80640 if j==6 else 0
    jets[j]=abs(left)+abs(origin_minus-origin_plus)+abs(right)
require(all(jets[j]==0 for j in range(4)),"common endpoint regularity")

# Fourier integral on ξ>=1 after ξ=z³, outward positive Riemann.
d=b-a; V=Q(7,5)
val=L1*d**4/5
step=1000
for i in range(step,8*step):
    z0,z1=Q(i,step),Q(i+1,step)
    major=min(L1,sum(jets[j]/z0**(3*(j+1)) for j in range(4,deg+1)))
    val+=major*3*z1**6*min(d*z1**3,V)**4/step
val+=V**4*sum(3*jets[j]*Q(8)**(4-3*j)/(3*j-4) for j in range(4,deg+1))
T=C*10/(pi_lo*(1-4*b)*fac(4))*val
require(T<Q(21,1000),"actual four-tag absolute tail")
require((Q(697,1000)-Q(115,1000)-4*Q(21,1000))/3 > Q(165,1000),
        "strict deweighted mass")
print("collar transform norms:", float(J4),float(J6))
print("marked signed model:",float(m))
print("true angular collar upper:",float(E))
print("true four-tag absolute tail:",float(T))
print("deweighted prime rebate: > .165 M")

# Same-score rough overlap.
r0=Q(1251,10000)
theta=Q(499,1000)
def avq(j):
    r=1-j*r0
    return j*r0**2+2*r0*r+Q(2,j+1)*r*r
def maxq(j):
    return (1-(j-1)*r0)**2+(j-1)*r0*r0
def f(t):
    return 1-t-39*t*t+192*t**3-376*t**4+336*t**5-112*t**6
def fp(t):
    return -1-78*t+576*t*t-1504*t**3+1680*t**4-672*t**5
require(1-2*f(r0)+f(2*r0)>0, "rank-three giant rough score")
require((Q(1,2)-r0)**2<Q(528,3360), "rough interval convexity")
require(1056**2*48<Q(40320,5)**2, "global rank-five sign")
m4=1680*(1-4*r0)**3/(fac(4)*fac(3))* (Q(2,175)*(1-4*r0)**4)/(4*(Q(11,35)-avq(4)))
root=upow(avq(5),Q(1,2))
m5=(10080*root-1056/root)*(1-5*r0)**4/(fac(5)*fac(4))
m6=Q(40320)*(1-6*r0)**5/(fac(6)*fac(5))
m7=(2112/r0**3+80640*7)*(1-7*r0)**6/(fac(7)*fac(6))
b4=1680*(maxq(4)-Q(11,35))/4**4
b5=0
for i in range(200,500):
    lo,hi=Q(i,1000),Q(i+1,1000)
    sq=upow(min(hi,maxq(5)),Q(1,2))
    b5=max(b5,(10080*sq-1056/sq)*lo*((1-lo)/4)**4)
# m((1-m)/4)^4 decreases for m>=1/5.
b6=Q(40320,6**6)
b7=(2112/r0**3+80640*7)/7**7
s=theta/r0
AA=2/theta*(1+(s-3)**2/4)
ms=[m4,m5,m6,m7]; bs=[b4,b5,b6,b7]
rough=2*sum(ms)+AA*sum(min(mi*bj,mj*bi) for mi,bi in zip(ms,bs) for mj,bj in zip(ms,bs))
require(3<s<4 and AA<Q(4988,1000),"actual rough receiver")
require(rough<Q(288,1000),"same-score full rough debit")
print("degree-six rough masses:",*[float(r) for r in ms])
print("degree-six rough pointwise caps:",*[float(r) for r in bs])
print("same-score whole rough debit:",float(rough))

# Ordinary tagged positive mass: ranks 2 and 3 and absolute odd ranks >=9.
rank2=(b-a)*(1+39*b)/(1-b)
require(fp(Q(23,100))<fp(b),"rank-three giant negative on the small-angle prefix")
rank3=(b-a)*b*(1+39*b)/(2*(Q(1,2)-b)**2) # nongiant
for i in range(210,490):
    l,h=Q(i,1000),Q(i+1,1000)
    rank3+=(b-a)*max(0,fp(min(Q(1,2),h+b))-fp(b))/(l*(1-b-h))/1000
# Weighted inverse of 1+T1+T1*T2+...; T_i independently Beta(j,1).
# All power-grid sums are outward with integer ceiling rounding.
def expected_inv(j,m,B=12,P=10**8):
    from itertools import product
    num=0
    D=B**m
    increments=[(i+1)**j-i**j for i in range(B)]
    for ind in product(range(B),repeat=m):
        w=1
        z=1
        den=D
        for h,i in enumerate(ind,1):
            w*=increments[i]
            z*=i
            den+=z*B**(m-h)
        ceil=(P*D**j+den**j-1)//den**j
        num+=w*ceil
    return Q(num,P*B**(j*m))
E3,E5=expected_inv(3,5),expected_inv(5,3)
hi=(b-a)*(1056*16*E3/(2*3**5*(1-Q(2,3)**2))+
          80640*4*E5/(fac(4)*5**3*(1-Q(2,5)**2)))
Wmass=(m+rank2+rank3+hi)/3
require(Wmass<Q(261,1000),"ordinary deweighted tagged source mass")
base=1-Q(288,1000)-2*(Q(261,1000)-Q(165,1000))
require(base==Q(52,100),"remaining exact same-score budget")
print("tagged ordinary positive ranks 2/3 and all >=9:",
      float(rank2),float(rank3),float(hi))
print("ordinary deweighted tagged mass:",float(Wmass))
print("joint unpriced overlap budget: .520 M")
