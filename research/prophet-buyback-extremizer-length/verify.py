"""Exact finite identities for the variational argument; no floating-point experiments."""
from fractions import Fraction as Q
from itertools import combinations
from math import prod

def check(ok):
    if not ok: raise ArithmeticError("certificate failed")

def U(t,A):
    r=[1+A]
    for x,y in zip(t,t[1:]):r.append(A+y-x+(1-1/y)*r[-1])
    return r

ar=bd=0
for n in range(2,8):
    for mid in combinations(range(2,13),n-2):
        t=[Q(i) for i in (1,*mid,14)]
        K=t[-1];f=1/(K-1)
        x=[Q(1)]*n
        for j in reversed(range(1,n)):x[j-1]=x[j]*(1-1/t[j])
        p=[(v-u)/v for v,u in zip(t,[0]+t)]
        V=[Q(0)]+x
        for j in reversed(range(n)):
            V=[(1-p[j])*V[b]+p[j]*max(V[b],V[j+1]-f*z) for b,z in enumerate([0]+x)]
        O=V[0];M=sum((b-a)*z for b,a,z in zip(t,[0]+t,x))/K
        theta=Q(5,6); A=(1+f)/theta
        us=U(t,A)
        check(us[-1]-A*K==K*(M-O/theta))
        for j,(s,v) in enumerate(zip(t,t[1:])):
            u=(s+v)/2
            B=((v-1)*(A-us[j]/u)-(u-s))/v
            check(U(t[:j+1]+[u]+t[j+1:],A)[j+2]-us[j+1]==B)
            bd+=1
        ar+=1

# Formal local stationarity chains. They need not solve the two endpoint conditions.
sr=0
for A in (Q(9,8),Q(3,2),Q(11,10),Q(51,50)):
    for start in (Q(2),Q(5,2),Q(3),Q(13,4),Q(9,2)):
        t=[Q(1),start]
        for _ in range(5):
            us=U(t,A);s,u=t[-2:];C=us[-2]-s
            v=1+u*u/(s+C);d=u-s;e=v-u
            check((1-1/v)*(1+(s+C)/(u*u))==1)
            check(e-d==1-C+(d-C)**2/(s+C))
            a=(d-1)/s;b=(e-1)/u
            check(a-b==(C*(1+b)-1)/s)
            t.append(v);sr+=1

# Three active exactly worst-case knots in the previously known ENNV fee phase.
br=ins=0
for j in range(24,50):
    z=Q(j,50);f=2*z*z/(1+z*z);c=f/(1+f);K=1/c
    check(Q(1,3)<=f<1)
    T=2*z/(1+z);b=(f+T)/(1+f)
    s=2*z/(1+z*z);theta=(1+f)*(1+s)/(1+3*f+(1+f)*s);A=(1+f)/theta
    t=[Q(1),b/c,K];us=U(t,A);check(us[-1]==K*A)
    check(K==1+t[1]**2/us[0])
    check(us[1]>=K*K/(K-1))
    check(U([t[0],t[-1]],A)[-1]<=us[-1])
    for j,(s,v) in enumerate(zip(t,t[1:])):
        for ctr in range(1,9):
            u=s+(v-s)*Q(ctr,9)
            check(U(t[:j+1]+[u]+t[j+1:],A)[-1]<=us[-1]);ins+=1
    br+=1

print(f"Exact full-chain dual/Bellman identities: {ar}; local insertion identities: {bd}")
print(f"Exact stationarity, gap-acceleration and velocity identities: {sr}")
print(f"Exactly extremizing three-point chains: {br}; insertion comparisons on those chains: {ins}")
