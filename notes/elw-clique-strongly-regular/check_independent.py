"""Independently derived positivity/domain certificates & finite SRG parameter sanity tests."""
if not __debug__:
    raise RuntimeError("run without -O: this reviewer checker uses assertions")
import math
from fractions import Fraction as Q
from collections import Counter
from sympy import symbols,expand,Poly,cancel,factor,solve

r,t,d,m,b,w,x,y=symbols('r t d m b w x y')
def clear(expr):
    return cancel(expr)
def nonneg(co, *vs):
    p=Poly(co,*vs)
    assert all(v>=0 for v in p.coeffs())
    return len(p.terms()), min(p.coeffs())

# Solve original SRG counting/trace system instead of entering manuscript formulas.
las=m+r-t; k=m+r*t; h=k-las
n=1+k+k*(k-1-las)/m
f=clear((t*(n-1)-k)/(r+t));g=clear(n-1-f)
def F(z): return clear(n*k*(1-1/z)-k*k-(z-1)*r*r)
L=1+k/h;D=1+k/t
lo=clear(F(L)*h*(h+k)/k); hi=clear(F(D)*m*t/(k*r))
assert clear(hi - (k*t*(t-1)-r*m))==0
# Recover b from complement counting, substitute m, verify b-monotonicity.
bb=clear(n-2*k+las)
mum=solve(bb-b,m)[0]
lo_b=clear(lo.subs(m,mum)); der=clear(lo_b.diff(b))
assert clear(der - (r*t*h+r**3*t*(h-1)/b**2))==0
# In the irrational / lower-root branch write t=r+1+y, r>0.
print('lower r<t',nonneg(clear(lo_b.subs({b:1,t:r+1+y})),r,y))
# For r>=t>=3 one can check lo_b at b=r-t+2 DIRECTLY, without manual identity.
tmp=clear(lo_b.subs(b,r-t+2)*(r-t+2))
print('lower r>=t>=3',nonneg(expand(tmp.subs(r,t+x).subs(t,3+y)),x,y))
# d parametrization from now on.
n0=clear(n.subs(m,d-r*t));f0=clear(f.subs(m,d-r*t));g0=clear(g.subs(m,d-r*t))
need=clear(n0*d/(g0*t*t))
assert clear(F(1+f)-(g*t*t-n*k/(f+1)))==0
K=solve((r+1)*(d+r-2*r*t)-(d+r)*(1-t)**2,d)[0]
S=r-t*t+2*t
assert clear(K-r*((2*t-1)*r+t*t)/S)==0
# Small-r upper branch: J(K) has concave dependence on r after removing positive factors.
j=clear((f0-need)*(d-r*t)*(r+t)*(r+1)*t*t/(d+t))
assert clear(j.diff(d,2))==0
j2=clear(j.subs(d,K)*S/(r*r*(t-1)))
assert clear(j2.diff(r,2))==-2
for z in [t*(t-1),t**3]:
    print('upper 3a endpoint in r',nonneg(expand(j2.subs(r,z).subs(t,3+y)),y))
# Large-r upper branch: independent compact substitution & positivity.
h0=clear((2*n0/f0-2-need)*d*(t-1)*(r+1)*t*t)
assert clear(h0.diff(d,2)+2*(r+t)*(t-1))==0
q=clear(h0.subs(d,r*t))
assert clear(q-r*t*t*(r+1)*(r-t)*(t-1))==0
cert=clear(h0.subs(d,K)*S**2/(r*(t-1)))
generic=Poly(cert.subs(r,t**3+x),x)
print('H(K) coefficients from scratch',[(int(i[0]),factor(c)) for i,c in generic.terms()])
print('upper 3b independent shifted form',nonneg(expand(cert.subs(r,t**3+x).subs(t,2+y)),x,y))
for rr,mm in [(rr,mm) for rr in range(3,8) for mm in range(1,9) if mm*(rr-2)>4*rr and 2*rr*(rr+1)%mm==0]:
    assert f.subs({t:2,r:rr,m:mm}).is_integer==False

# Exhaustive bounded arithmetic-parameter grid, not enumeration of realizable graphs.
# k,lambda,mu are generated from the integral roots and the 2-path count separately.
from sympy import divisors
cnt=Counter()
for tt in range(2,61):
  for rr in range(1,151):
    z=rr*tt
    for mm in divisors(z*(rr+1)*(tt-1)):
      kk=z+mm; ll=mm+rr-tt
      if ll<0 or mm>tt**3*(2*tt-3): continue
      nq,rem=divmod(kk*(kk-1-ll),mm)
      assert rem==0
      nn=1+kk+nq
      if nn>1200 or nn-2-2*kk+mm<0 or not all([0<ll+1<kk,0<mm<kk]):continue
      ff,rem=divmod(tt*(nn-1)-kk,rr+tt)
      if rem or ff<1:continue
      gg=nn-ff-1
      if min(ff*(ff+3),gg*(gg+3))<2*nn:continue
      if (rr+1)*(kk+rr-2*rr*tt)>(kk+rr)*(tt-1)**2:continue
      if (1-tt)*(kk-tt-2*rr*tt)>(kk-tt)*(rr+1)**2:continue
      L0=1+Q(kk,kk-ll);U0=min(1+Q(kk,tt),1+ff)
      if L0>U0:continue
      delta=lambda ww:nn*kk*(1-1/ww)-kk*kk-(ww-1)*rr*rr
      assert delta(L0)>=0 and delta(U0)>=0
      cnt['integral parameter rows']+=1
      for ww in range(math.ceil(L0),math.floor(U0)+1):
         assert nn*kk*(ww-1)>=ww*(kk*kk+(ww-1)*rr*rr)
         cnt['integral clique tests']+=1
# All nonsquare formal conference parameters up to 1200: at every integer w from local bound to floor(sqrt(n)).
for nn in range(5,1201,4):
    if math.isqrt(nn)**2==nn:continue
    kk=(nn-1)//2;ll=(nn-5)//4
    for ww in range(math.ceil(1+Q(kk,kk-ll)),math.isqrt(nn)+1):
        base=4*nn*kk*(ww-1)-4*ww*kk*kk-ww*(ww-1)*(nn+1)
        assert base>=0 or 4*ww**2*(ww-1)**2*nn>=base**2
        cnt['nonsquare conference clique tests']+=1
    cnt['nonsquare conference rows']+=1
print(cnt)
