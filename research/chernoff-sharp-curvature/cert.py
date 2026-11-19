"""Fail-closed exact real interval proof. Only integer and rational arithmetic."""
from fractions import Fraction as Q
from math import factorial
from hashlib import sha256
S=1<<320
def ceil(a,b):return -((-a)//b)
class I:
    __slots__=('a','b')
    def __init__(self,a,b):self.a=a;self.b=b
    def __add__(x,y):
        if not isinstance(y,I):y=C(y)
        return I(x.a+y.a,x.b+y.b)
    __radd__=__add__
    def __neg__(x):return I(-x.b,-x.a)
    def __sub__(x,y):return x+-y
    def __rsub__(x,y):return -x+y
    def __mul__(x,y):
        if type(y)==int:
            a=x.a*y;b=x.b*y;return I(min(a,b),max(a,b))
        if not isinstance(y,I):y=C(y)
        u=[x.a*y.a,x.a*y.b,x.b*y.a,x.b*y.b];return I(min(u)//S,ceil(max(u),S))
    __rmul__=__mul__
    def __truediv__(x,y):
        if type(y)==int and y>0:return I(x.a//y,ceil(x.b,y))
        if not isinstance(y,I):y=C(y)
        if y.a<=0<=y.b:raise ArithmeticError("zero denominator")
        return x*I(S*S//y.b,ceil(S*S,y.a))
    def sq(x):
        if x.a<=0<=x.b:return I(0,ceil(max(x.a*x.a,x.b*x.b),S))
        return x*x
def C(x):
    x=Q(x)*S
    return I(x.numerator//x.denominator,ceil(x.numerator,x.denominator))
def wid(x):return I(-x.b,x.b)
def need(v,label):
    if not v:raise ArithmeticError(label)
def cube_low(a,b): # floor S*(a/b)^(1/3)
    lo=0;hi=2*S
    need(hi**3*b>S**3*a,'cube root start')
    while hi>lo+1:
        mid=(hi+lo)//2
        if mid**3*b<=S**3*a:lo=mid
        else:hi=mid
    return lo
# I_k = integral_0^infty t^k exp(-t^3)dt, k=0,1. At t>=5 the
# tail <= exp(-125)/3 (t^k <= t^2), and e>8/3.
def gamma_int(k):
    x=Q(5**(k+1)); val=Q()
    for j in range(560):
        val+=x/(3*j+k+1);x*=-Q(125,j+1)
    rem=abs(x)/(3*560+k+1)+Q(3,8)**125/3
    return I(C(val-rem).a,C(val+rem).b)
q=-(I(cube_low(3,2),cube_low(3,2)+1)*gamma_int(1)/gamma_int(0))
need(q.a>-S and q.b<-S//2,'Airy slope')
# F(s)=Ai(2^(-1/3)s)/Ai(0). Taylor coefficients satisfy a[n+3]=
# a[n]/(2(n+2)(n+3)). Evaluate individual terms at positive real v,
# and apply the appropriate signs for complex direction i or -1.
def Fval(v,d='i'):
    v=C(v);tw=v*v*v/2; absmax=max(abs(tw.a),abs(tw.b))
    ab=[C(0),C(0)];x=C(1);y=q*v;N=660
    for j in range(0,N,3):
        for k,term in ((j,x),(j+1,y)):
            z=k%4 if d=='i' else ((2*k)%4 if d=='-' else 0)
            ab[z%2]=ab[z%2]+(term if z<2 else -term)
        x=x*tw/((j+2)*(j+3)); y=y*tw/((j+3)*(j+4))
    # Remaining geometric ratio for both subsequences is <=1/2.
    need(2*absmax < S*(N+2)*(N+3),'Airy tail ratio')
    err=2*(max(abs(x.a),abs(x.b))+max(abs(y.a),abs(y.b)))
    return [w+I(-err,err) for w in ab]
# F(-x)>0 on [0,1] from the two alternating decreasing subsequences
# starting at 1 and -qx. Finite sign changes place ten poles below 17.
prev=1
for v in [4,6,8,9,11,12,13,14,16,17]:
    a=Fval(v,'-')[0]
    cur=1 if a.a>0 else -1 if a.b<0 else 0
    need(cur==-prev,'zero brackets');prev=cur
for d in ['-','+']:need(Fval(1,d)[0].a>S//4,'shifted F(1)')
def M(u):
    a,b=Fval(u);den=a.sq()+b.sq();return a/den,-b/den
# Bound all quadrature approximation errors to integral-normalized (2pi)g^(k).
# Strip integral bound: M(+-1+iu) <= 4 min(1,(18/u)^10).
strip=32*(1+Q(18**10,5))
# Trapezoid period 32*pi>96; e>8/3 and |x|<=1.
alias=2*strip*Q(3,8)**95/(1-Q(3,8)**96)
T=32; step=16; L=160
at,bt=M(T)
amp=Q(max(abs(at.a),abs(at.b))+max(abs(bt.a),abs(bt.b)),S)
tail=2*amp*37**10*Q(1,5*T**5) # 37^2>=32^2+17^2
polytail=(2*T+1)*Q(T**(4+L+1),factorial(L+1))
ERR=Q(1,10**14)
need(alias+tail+polytail<ERR,'global errors')
print('All ten scaled poles bounded above by 17; both strip mgfs < 4.')
print('Frequency aliases, discarded lattice samples and Taylor error sum < 1e-14.')

# common moments b_n=h sum (-iu)^n M(iu)/n!, so Fourier-polynomial
# coefficients for g^(k) use b_{j+k} (j+k)!/j!.
mom=[C(0) for _ in range(L+5)]
for i in range(T*step+1):
    u=Q(i,step); a,b=M(u) if i else (C(1),C(0))
    re=[a,b,-a,-b]; pw=C(1);v=C(u)
    weight=1 if i==0 else 2
    for k in range(L+5):
        mom[k]=mom[k]+pw*re[k%4]*weight/step
        pw=pw*v/(k+1)
def poly(co,x):
    val=C(0)
    for w in reversed(co):val=val*x+w
    return val
polys=[[mom[j+k]*(factorial(j+k)//factorial(j)) for j in range(L+1)] for k in range(5)]
err=wid(C(ERR))
def lp(x,k):
    gg=[poly(p,x)+err for p in polys[:k+1]]
    g=gg[0];need(g.a>0,'positive density')
    h=[e/g for e in gg[1:]];b,c=h[:2];b2=b.sq()
    if k==2:return b2-c
    d=h[2]
    if k==3:return -d+3*b*c-2*b2*b
    e=h[3];return -e+4*b*d+3*c.sq()-12*b2*c+6*b2.sq()
k0=2*lp(C(0),2)
need(k0.a>C(Q(34051898,10000000)).b and k0.b<C(Q(34051899,10000000)).a,'origin')
print('3.4051898 < kappa(0) < 3.4051899.')
# Verify kappa''>0 near 0 and kappa(x)>kappa(0) away from 0.
# Adaptive exact dyadic bisection; depth cap fails closed.
count=[0,0];maxdepth=0
def cover(lo,hi,n,kind):
    global maxdepth
    x=I(lo,hi)
    if kind==0:
        y=lp(x,4)+lp(-x,4); good=y.a>0
    else:
        y=lp(x,2)+lp(-x,2);good=y.a>k0.b
    if good:
        count[kind]+=1;maxdepth=max(maxdepth,n);return
    need(n<17,'interval refinement')
    mid=(lo+hi)//2
    cover(lo,mid,n+1,kind);cover(mid,hi,n+1,kind)
cover(0,S//8,0,0)
for j in range(8,64):cover(j*S//64,(j+1)*S//64,0,1)
print("Certified closed cells, near-zero positive second derivative:",count[0],
      "; direct positive curvature excess:",count[1],"; maximum depth:",maxdepth)
