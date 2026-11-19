from sympy import symbols,expand,binomial,Rational as Q,I,pi
z,u=symbols('z u',nonzero=True)
N=4
def mul(a,b):
 return [expand(sum(a[k]*b[j-k] for k in range(j+1))) for j in range(N+1)]
def add(a,b):
 return [expand(x+y) for x,y in zip(a,b)]
def scale(a,x):
 return [expand(v*x) for v in a]
def subst(a,d,b):
 return [expand(v.subs(d,b)) for v in a]
def steady(x,d):
 return expand(x).coeff(d,0)
def coeffs(a,d,k):
 return [expand(v).coeff(d,k) for v in a]
def const(a):
 return [a]+[0]*N
raw=[expand(binomial(Q(1,2),j)*(-(z+1/z)/2)**j) for j in range(N+1)]
mean=coeffs(raw,z,0)
inv=[1]+[0]*N
for j in range(1,N+1):inv[j]=-sum(mean[k]*inv[j-k] for k in range(1,j+1))
w=mul(raw,inv)
W=mul(subst(w,z,z*u),subst(w,z,z/u))
def ratio_power(k):
 return mul([binomial(k,j)/z**j for j in range(N+1)],[binomial(-k,j)*z**j for j in range(N+1)])
main=const(0)
for k in range(1,N):
 a=scale(coeffs(w,z,k),2)
 ang=scale(add(add(scale(ratio_power(2*k),z**k),scale(ratio_power(-2*k),z**(-k))),const(-z**k-z**(-k))),Q(1,4))
 integ=scale(mul(mul(a,W),ang),(u**k-u**(-k))/(2*I*k))
 for j in range(N+1):
  v=steady(integ[j],z)
  for aterm in v.as_ordered_terms():
   p=aterm.as_powers_dict().get(u,0)
   if p:main[j]+=aterm/u**p*((-1)**p-1)/(2*I*p)
   else: assert not aterm
alpha=[0]+[(-1)**(j+1)*(z**(-j)-z**j)/(2*I*j) for j in range(1,N+1)]
wn=const(0)
for j in range(N+1):
 for term in w[j].as_ordered_terms():
  p=int(term.as_powers_dict().get(z,0))
  shifted=([0]*j+ratio_power(p))[:N+1]
  wn=add(wn,scale(shifted,term))
corr=[steady(v,z) for v in mul(mul(mul(w,w),wn),mul(alpha,alpha))]
print('unclipped main',main)
print('endpoint correction',corr)
print('total acute coefficients',scale(add(main,corr),-3/pi**2))
