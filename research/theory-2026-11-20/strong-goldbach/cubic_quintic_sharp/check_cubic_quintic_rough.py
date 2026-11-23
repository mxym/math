#!/usr/bin/env python3
"""Exact rational enclosure for the cubic-quintic rough covariance."""
from fractions import Fraction as F

S=10**13
def require(ok, why):
    if not ok:
        raise ArithmeticError(why)

def ceilq(n,d): return (n+d-1)//d

a=F(".15"); theta=F(".499")
# Positive Selberg normalization: rho_2(t)=t R(t), R'(t)=-2(t-1)R(t-1)/t^2.
K=30000; n=int(K*theta/a)
require(F(n,K)==theta/a,"exact Selberg endpoint")
hi=[S]*(K+1);lo=hi.copy()
for i in range(K,n):
    lo.append(max(0,lo[i]-ceilq(2*(i+1-K)*hi[i-K],i*i)))
    hi.append(max(0,hi[i]-(2*(i-K)*lo[i+1-K])//((i+1)**2)))
    require(lo[-1]<=hi[-1],"delay enclosure")
g=[0]
for i in range(n):
    g.append(g[-1]+(2*i+1)*lo[i+1])
# Exact unweighted dimension-two upper at level N^.999. The certified
# switch cells are (53577,53578)/10^4 for α_2 and (42664,42665)/10^4 for β_2.
JQ=10000; AL=53577; AH=53578; BL=42664
v=F(".999")/a; ve=int(v*JQ)
require(F(ve,JQ)==v and ve-2*JQ<AL,"only first G branch needed in delayed B")
def g_tick(j):
    return g[K*j//(2*JQ)]
B=[0]*(ve+1)
for j in range(BL,ve-JQ):
    B[j+1]=B[j]+ceilq(4*(j+1)*K*K*S*S,JQ**2*g_tick(j-JQ))
A=ceilq(2*AH**2*K*K*S*S,JQ**2*g_tick(AL))
for j in range(AL,ve):
    A+=ceilq(2*(j+1)*B[j+1-JQ],(j-JQ)**2)
C=F(A,S)/(v*v*a*a)
z=(theta/a-2)/(theta/a)
k=(4/theta)*sum(z**(2*j+1)/(2*j+1) for j in range(20))

P=1000; floor=150; R=200; den=P**5
def pp(i):
    z=P-2*i
    return 2*z**3*P**2-z**5

psi=[pp(i) for i in range(P+1)]
Fold=list(map(abs,psi))
mass=[0]*(R+1)
n2=n3=0
def inject(score,weight):
    i=min(R,(score*R-1)//den)
    if i>0: mass[i]+=weight

for i in range(floor,P//2):
    inject(den-psi[i],P*S//((i+1)*(P-i)))
    n2+=1
for i in range(floor,P//3+1):
    for j in range(i+1,(P-i-3)//2+1):
        w=P-i-j
        inject(den-psi[i]-psi[j]-psi[w-2],P*S//((i+1)*(j+1)*w))
        n3+=1
means=[F(sum(mass[i:]),S) for i in range(1,R+1)]
credit=sum(max(0,k*(u+v)-C) for u in means for v in means)/R**2
require((n2,n3)==(350,25025),"actual ordered count")

def lo_fold(l,h):
    return 0 if 2*l<=P<=2*h else min(Fold[l],Fold[h])

def hi_fold(l,h):
    return max(Fold[l],Fold[h])

m4=0;n4=0
for i in range(floor,P//4+1):
    for j in range(i,(P-i)//3+1):
        sij=lo_fold(i+j,i+j+2)
        hij=hi_fold(i,i+1)+hi_fold(j,j+1)
        for t in range(j,(P-i-j)//2+1):
            w=P-i-j-t
            l=max(t,w-3)
            amp=hij+hi_fold(t,t+1)+hi_fold(l,w)-den
            amp-=sij+lo_fold(i+t,i+t+2)+lo_fold(j+t,j+t+2)
            m4+=ceilq(max(0,amp)*S,P**4*i*j*t*l)
            n4+=1
neg4=F(m4,S)
neg5=F(1920)*(1-5*a)**4/(120*24)
neg6=3*(1-6*a)**5/(720*120*a**6)
U=2/(3*a)
cost=2*U*(neg4+neg5+neg6)
print('C, k:',float(C),float(k))
print('true weighted positive intersection:',float(credit))
print('rank-four negative cells:',n4,'rank-four/five/six negative uppers:',*(float(x) for x in (neg4,neg5,neg6)))
print('bilateral opposite-sign debit and total lower:',float(cost),float(credit-cost))
require(C<F("14.55") and k>F("3.384"),"ambient coefficients")
require(credit>F(".575485"),"weighted positive intersection")
require(neg4<F(".004093559") and cost<F(".059807"),"all opposite signs")
require(credit-cost>F(".515"),"complete actual rough lower")

