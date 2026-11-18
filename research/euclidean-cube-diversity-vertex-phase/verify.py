"""Rational outward-rounded proof of the single square-edge inequality.
All interval endpoints are integers in units of 10^-16. No floating point."""
from math import isqrt
from functools import lru_cache

S=10**16
def check(p,msg):
    if not p: raise ValueError(msg)
def ceildiv(x,y): return -((-x)//y)
def checkiv(v):
    check(isinstance(v,tuple) and len(v)==2 and type(v[0]) is int and type(v[1]) is int and v[0]<=v[1],('bad interval',v))
    return v
def point(a,b=1): return checkiv((a*S//b,ceildiv(a*S,b)))
def add(x,y): return checkiv((x[0]+y[0],x[1]+y[1]))
def sub(x,y): return checkiv((x[0]-y[1],x[1]-y[0]))
def mul(x,y):
    z=[a*b for a in x for b in y]; return checkiv((min(z)//S,ceildiv(max(z),S)))
def inv(x):
    check(x[0]>0,('nonpositive inverse',x));return checkiv((S*S//x[1],ceildiv(S*S,x[0])))
def sqrtiv(x):
    check(x[0]>=0,('negative sqrt',x)); lo=isqrt(S*x[0]);hi=isqrt(S*x[1])
    return checkiv((lo,hi+int(hi*hi<S*x[1])))
@lru_cache(None)
def exp_at(z):
    check(0<=z<=S,('exp range',z)); v=(S,S); term=(S,S); lower=None
    for j in range(1,17):
        term=checkiv((term[0]*z//(S*j),ceildiv(term[1]*z,S*j)))
        v=sub(v,term) if j%2 else add(v,term)
        if j==15: lower=v[0]
    return checkiv((lower,v[1])) # odd/even alternating partial sums
def expneg(x): return checkiv((exp_at(x[1])[0],exp_at(x[0])[1]))

one=point(1);zero=point(0)
lo=point(46019,100000);hi=point(46020,100000);J=(lo[0],hi[1])
def H(t,s,deriv=False):
    r=sqrtiv(add(one,mul(t,t)));inv_r=inv(r)
    a=expneg(mul(s,t)); b=expneg(mul(s,r)); u=mul(t,inv_r)
    if not deriv:return add(a,mul(u,b))
    return add(sub(zero,mul(s,a)),mul(b,sub(mul(mul(inv_r,inv_r),inv_r),mul(s,mul(u,u)))))
def F(t,s): return sub(H(sub(one,t),s),H(t,s))
def Fprime(t,s):
    return sub(zero,add(H(sub(one,t),s,True),H(t,s,True)))

if __name__=='__main__':
    left=F(zero,lo);right=F(zero,hi)
    check(left[0]>0 and right[1]<0,'critical root not enclosed')
    print('critical side: 46019/100000 < s* < 46020/100000')
    # For [0,1/16] derivative positive -> F>0 to right of its zero at x=0.
    # For [1/16,3/8] certify F itself. For [3/8,1/2] derivative negative -> F>0
    # to the left of its zero at x=1/2. Identical closed endpoints give full coverage.
    N=4096; counts=[0]*3; minima=[S]*3
    for i in range(N//2):
        t=checkiv((point(i,N)[0],point(i+1,N)[1]))
        if i<N//16: j=0;y=Fprime(t,J)
        elif i<3*N//8: j=1;y=F(t,J)
        else: j=2;y=sub(zero,Fprime(t,J))
        check(y[0]>0,('interval inequality failed',j,i,y));counts[j]+=1;minima[j]=min(minima[j],y[0])
    check(counts==[256,1280,512],('partition',counts))
    print('cells for Fprime, F, -Fprime:',*counts)
    print('outward certified lower bounds, divided by',S,':',*minima)
