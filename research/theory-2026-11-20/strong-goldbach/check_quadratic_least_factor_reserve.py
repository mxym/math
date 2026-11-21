"""Pure-integer upper cubature for the Greaves h-kernel, and lower M(W)."""
from fractions import Fraction as F
def req(b):
    if not b: raise ArithmeticError("failed certified inequality")
def ceil(a,b):return (a+b-1)//b
G=600   # multiple of 3,4,25,50
B=10**9
def down(x):return x.numerator*B//x.denominator
def up(x):return ceil(x.numerator*B,x.denominator)
def W(t):return F(0) if t<F(2,25) else min(F(114,125),t-F(3,100),5*t*t)
U=F(471,500);V=F(3,100);req(W(1)==U-V and 2*U+V==F(957,500))
lo=2*G//25;hi=G//3; amax=G//2
H=[[0]*(amax+1) for j in range(hi+1)]
def H1():
 for j in range(lo,hi):
    run=0
    for k in range(amax):
     # x in [j/G,(j+1)/G], v in [k/G,(k+1)/G], u=1-x-v≥v.
     if k>=hi and 2*k+j<=G:
      run+=ceil(G*B,k*max(k,G-j-k-2))
     H[j][k+1]=run
def lift(H):
 J=[[0]*(amax+1) for j in range(hi+1)]
 for j in range(lo,hi):
    run=0
    for k in range(j,hi):
     # v≥x; derivative kernel 1/(v(1-v)), interval lies below 1/2.
     jl=j*G//(G-k);jh=(j+1)*G//(G-k-1)
     ai=min(amax,ceil((k+1)*G,G-k-1))
     f=max((H[m][ai] for m in range(jl,min(hi-1,jh)+1)),default=0)
     run+=ceil(f*G,k*(G-k))
     J[j][k+1]=run
    J[j][hi+1:]=[run]*(amax-hi)
 return J
H1()
ht=[0]*(hi+1)
for i in range(2,13):
 H=lift(H)
 if i%2==0:
  for j in range(lo,hi):ht[j]+=H[j][amax]
# i prime-variables, plus x and u, each at least .08; i>=11 impossible.
# Main Riemann sum, enforce zero at the jump via left endpoints.
M=0
for j in range(lo,G//2):
 a,b=F(j,G),F(j+1,G)
 M+=down(W(a)/(b*(1-b))/G) # t(1-t) increasing up to half
 if j<hi:
  M-=ceil(up(W(b)/a)*ht[j],B*G)
for j in range(G//2,G):
 a,b=F(j,G),F(j+1,G)
 if a>=U:break
 M-=up((U-V-W(a))/(b*(1-b))/G)
print("Greaves M(W) certified lower",M,"/",B,"; h upper at .08",ht[lo],"/",B)
req(M>B//100)
