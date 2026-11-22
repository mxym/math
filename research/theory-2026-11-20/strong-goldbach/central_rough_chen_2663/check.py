"""Reproducible rational certificate for the independently packed rough Chen bound."""
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
alphas=(Q(265,1000),Q(2663,10000))
alpha=alphas[-1]
t0=(1-2*s)/7
tm=(1-height*theta)/4
bh=Q(1115,10000)
I2=lambda t:(1-(Q(3,2)-2*theta)*t)/(1+theta)
I3=lambda t:1-(height*theta+3*t)/2
W1=lambda t:((5-4*theta)-(3-4*theta)*t)/(8-6*theta)
W2=lambda t:(5-height*theta-3*t)/8
need(0<bh<beta<t0<tm<qcut<alpha<Q(1,3),"bins")
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
H+=harm(tm,qcut,1-height*theta/2-s,Q(5,2))
for alpha,goal in zip(alphas,(Q(324,10000),Q(367,100000))):
    Hup=H+harm(qcut,alpha,Bv,Q(1))
    C3=Q()
    step=(Q(1,3)-alpha)/8192
    for i in range(8192):
        u=alpha+i*step
        z=step*uplog((1-2*u)/u)/(u*(1-u))*10**17
        C3+=Q(-(-z//1),10**17)
    final=L0-Hup-Q(3446,1000)*C3
    need(final>goal,"strict positive actual coefficient")
    print(f"alpha={float(alpha):.4f}: L0 > {float(L0):.10f}; H < {float(Hup):.10f}; C3 < {float(C3):.10f}")
    print(f"total coefficient > {float(final):.10f}")
l,u=logbox((1-alphas[0])/alphas[0])
need(Q(20,1000)<l-1<u-1<Q(21,1000),"signed mean feasibility margin")
