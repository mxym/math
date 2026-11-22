"""Rational receiver and mass bounds for the entire high odd four-tag exterior."""
from fractions import Fraction as F
from math import comb

def need(p, tag):
    if not p:
        raise ArithmeticError(tag)

def ceilq(a,b):
    return -(-a//b)

def sqrt_up(q, scale=10**12):
    a,b=q.numerator*scale*scale,q.denominator
    from math import isqrt
    z=isqrt(a//b)
    if z*z*b<a:
        z+=1
    return F(z,scale)

# Build C_k=2^k b_{k,1} with outward integer rounding on each bin.
H,S,I=200,10**15,67000
arr=[0 if i<H else ceilq(2*H*S,i) for i in range(I+1)]
fixed={}
tail=[0]*(I+1)
for k in range(2,330):
    pre=[0]
    for z in arr:
        pre.append(pre[-1]+z)
    arr=[0 if i+1<k*H else ceilq(2*pre[i+1-H],i) for i in range(I+1)]
    if k in (5,7,9,11):
        fixed[k]=arr
    if k>=13 and k%2==1:
        # T^2<=1 in the whole tail: C_r * b_k = (528+10080/k^2) * C_k.
        for i,z in enumerate(arr):
            if z:
                tail[i]+=528*z+ceilq(10080*z,k*k)

def rmq(a):
    levels=[a]
    while 2**len(levels)<=len(a):
        old=levels[-1]; step=2**(len(levels)-1)
        levels.append([max(old[i],old[i+step]) for i in range(len(old)-step)])
    return levels

A=[rmq(fixed[k]) for k in (5,7,9,11)] + [rmq(tail)]
def sup3(levels,l,r):
    il,ir=int(H*l),int(H*r)
    need(0<il<=ir<=I,"scaled density")
    q=(ir-il+1).bit_length()-1
    return F(max(levels[q][il],levels[q][ir-2**q+1]),S)

def IH(t):
    return F(1,6)*sum((-1)**j*comb(3,j)*max(t-j,0)**3 for j in range(4))

a,b,theta=F(".003"),F(".080"),F(".499")
m=[F(0) for _ in A]; U=[F(0),F(0)]
for i in range(385):
    vl,vu=a+F(i,5000),a+F(i+1,5000)
    cell0=(vu-a)**3/6*(vu-vl)
    for j in range(120):
        zl,zu=F(j,40),F(j+1,40)
        vol=cell0*(IH(zu)-IH(zl))
        tl,tu=1-vu-3*a-(vu-a)*zu,1-vl-3*a-(vl-a)*zl
        lo,hi=tl/vu,tu/vl
        D=theta-(1-tl)
        need(D>2*vu,"four-name level")
        cond=(F(".575")/vl if D>=4*vu else
              2/(3*vl) if D>=3*vu else max(2/(3*vl),2/D))
        for p,k in enumerate((5,7,9,11)):
            cap=528+10080*(tu/k)**2
            m[p]+=vol*cap*sup3(A[p],lo,hi)/vl
            if p<2:
                U[p]+=vol*cap*2**k*cond
        m[4]+=vol*sup3(A[4],lo,hi)/vl
need(vu==b and zu==3,"full four-name angle box")

def U_large(r):
    j=(r-1)//2
    k=j-4
    B=F(1,j+2)
    D=theta-F(j,r)
    need(D>0,"literal above-factor sieve")
    C=1056*2**(r-5)+F(80640*2**(r-7),(r-4)**2)
    return F(C,6*4**k)*(2*B**3/9+B**4/(2*D))

U.extend([U_large(13),U_large(15),sum(U_large(r) for r in range(17,334,2))])
print("ordinary uppers:", [float(x) for x in m])
print("real receiver uppers:", [float(x) for x in U])

# All remainder constants here are explicitly upward rational.
M_hi=[F(t) for t in (".01933",".00345",".000534",".000078",".0000114")]
U_hi=[F(t) for t in (".373","1.232","12.850","8.679","35.095")]
need(all(x<y for x,y in zip(m,M_hi)) and all(x<y for x,y in zip(U,U_hi)),
     "angular margins")
w0=F(".009042"); X0=F(".017667")**2*F(".8")/a
V_cost=sum(min(u*w0,sqrt_up(X0*u*x)) for u,x in zip(U_hi,M_hi))
m_hi=sum(M_hi)
self_cost=sum(min(u*y,v*x) for u,x in zip(U_hi,M_hi) for v,y in zip(U_hi,M_hi))
old_overlap=2*F(".1212")*m_hi
total=2*((F("2.446")+F(".228")+F(".007445"))*m_hi+V_cost)+self_cost+old_overlap
need(total<F(".262"),"full high union")
print("V crossing, high self, old overlap:",float(V_cost),float(self_cost),float(old_overlap))
print("full literal high outside low debit <",float(total),"< .262")
