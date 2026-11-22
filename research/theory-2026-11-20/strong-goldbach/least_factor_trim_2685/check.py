"""Rational bounds for the actual rank-two trimming after the .252 rough lower."""
from fractions import Fraction as Q

def need(b,msg):
    if not b: raise ArithmeticError(msg)

def logbox(x):
    need(x>=1,"log input")
    e=x.numerator.bit_length()-x.denominator.bit_length()
    if 2**e>x:e-=1
    def short(v):
        t=(v-1)/(v+1)
        n=16
        s=2*sum((t**(2*j+1)/(2*j+1) for j in range(n)),Q())
        err=2*t**(2*n+1)/((2*n+1)*(1-t*t))
        D=10**15
        return Q(int(s*D),D),Q(-(-(s+err)*D//1),D)
    lo,hi=short(x/Q(2)**e)
    l2,u2=short(Q(2))
    return lo+e*l2,hi+e*u2

def lowlog(x):return logbox(x)[0]
def uplog(x):return logbox(x)[1]

# Notional / true levels and fixed separating constants.
theta=Q(7,32)
height=Q(100001,100000)
beta=Q(25,224)
base=Q(5557,10000)
notional=Q(55572,100000)
s=Q(5,100000)
qcut=Q(254,1000)
Bv=Q(4999,10000)
alpha0=Q(252,1000)
alpha1=Q(2685,10000)
t0=(1-2*s)/7
tm=(1-height*theta)/4
bh=Q(1115,10000)
I2=lambda t:(1-(Q(3,2)-2*theta)*t)/(1+theta)
I3=lambda t:1-(height*theta+3*t)/2
W1=lambda t:((5-4*theta)-(3-4*theta)*t)/(8-6*theta)
W2=lambda t:(5-height*theta-3*t)/8
need(0<bh<beta<t0<tm<alpha0<qcut<alpha1<Q(1,3),"bins")
need(tm<(1-theta)/(4-3*theta),"exact branch crossover")
need(min((1+bh)/2,I2(beta),I3(beta))>notional,"base large first label")
need(min(W1(bh),W2(bh),1-2*bh)>max(notional,(1+bh)/2),
     "base three-label packing")
need(I2(qcut)>(1+tm)/2,"middle one-prime rail")
need(2*qcut<I3(qcut)-s,"forced first square at last packed label")
need((1+tm)/2-s>2*tm,"forced first square in increasing branch")

def logint(U,upper,n=4096):
    # integral_3^U (log(v-2)/(v-1))*log(U/v) dv, 3<U<4.
    step=(U-3)/n
    v=Q(3)
    tot=Q()
    for i in range(n):
        w=v+step
        if upper:
            term=uplog(w-2)*uplog(U/v)/(v-1)
        else:
            term=lowlog(v-2)*lowlog(U/w)/(w-1)
        # Round each rectangle separately to bound denominators.
        D=10**18
        z=step*term*D
        tot+=Q(-(-z//1) if upper else z//1,D)
        v=w
    return tot

S0=base/beta
need(4<S0<5,"lower sieve regime")
L0=(2*lowlog(S0-1)+2*logint(S0-1,False))/base
U=(1-2*s)/(2*beta)-Q(1,2)
need(3<U<4,"upper sieve regime")
H=2/(1-2*s)*(2*uplog(U/3)+2*logint(U,True))
def harm(a,b,A,B):
    # exact primitive of 2/[t(A-Bt)]
    return 2/A*uplog(b*(A-B*a)/(a*(A-B*b)))
H+=harm(t0,tm,Q(1,2)-s,Q(1,2))

H+=harm(tm,alpha0,1-height*theta/2-s,Q(5,2))
C3=Q()
steps=8192
step=(Q(1,3)-alpha0)/steps
for i in range(steps):
    u=alpha0+i*step
    z=step*uplog((1-2*u)/u)/(u*(1-u))*10**17
    C3+=Q(-(-z//1),10**17)
coef=Q(3446,1000)
central=L0-H-coef*C3
need(central>Q(3001,10000), "baseline .252 prime + actual rank-two coefficient")
print(f"alpha0={float(alpha0):.4f}: L0 > {float(L0):.12f}; H < {float(H):.12f}; I3 < {float(C3):.12f}")
print(f"G+D2(alpha0) coefficient > {float(central):.12f}")
for a,T in [(alpha1,Q(47,10000)),(Q(2686,10000),Q(30,10000))]:
    i2=uplog((1-alpha0)*a/(alpha0*(1-a)))
    new=central-coef*i2
    w=4*a*(1-a)
    need(new>T,"strict lower rank-two trim")
    print(f"alpha1={float(a):.4f}: I2(trim) < {float(i2):.12f}; coefficient > {float(new):.12f}; weighted > {float(new*w):.12f}")
    if a==alpha1:
        need(new*w>Q(370,100000),"strict weighted coefficient")
        l,h=logbox((1-a)/a)
        need(Q(22,10000)<l-1<h-1<Q(23,10000),"unweighted dyadic signed mean")
        need(4*(Q(1,2)-a)-1==Q(-74,1000),"weighted dyadic signed mean")
