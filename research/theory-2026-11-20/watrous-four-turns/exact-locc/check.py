"""Exact symbolic checks for the supporting form, its boundary charts and the leaf equations.
Requires Python 3 and SymPy. Checks are not disabled by python -O."""
import sympy as S
from itertools import product
a,p,h,t,b,q,k,v=S.symbols('a p h t b q k v', complex=True)
zero,one=S.Integer(0),S.Integer(1)
co=S.conjugate
def sq(x): return x*co(x)
def re(x): return (x+co(x))/2
def check(x,label):
    if S.expand(x)!=0: raise ArithmeticError(label+': '+str(S.factor(x)))
def KA(a,p,t,b,q,v):
    return -sq(a*q)/2+3*sq(t*b)/2-2*re(co(a*q)*p*v)+3*re(co(a*q)*t*b)
def wit(a,p,t,b,q,v,n):
    c,m=a*b,p*q
    K0=-sq(c)+re(co(c)*(m+n))+sq(m)/4-re(co(m)*n)/2-sq(n)/4
    return K0+KA(a,p,t,b,q,v)+KA(b,q,v,a,p,t)
def bil(a,p,t,b,q,v):
    return [a*co(t)*sq(v),co(t)*(2*a*q*co(b)-p*b*co(q)),
            sq(p*co(q)+2*t*co(b))-4*sq(p*b)]
check(wit(1,p,0,b,q,q-p*b,2*b+(p-2)*q)+sq(co(p)*q-2*p*b)/2,
      'regular SOS')
# a=t=0 ⇒ p b=0, so either p=0 or b=0.
for P,B in [(0,b),(p,0)]:
    check(wit(0,P,0,B,q,v,P*q)+sq(P*q)/2,'boundary SOS')
check(wit(0,p,t,0,q,v,p*q)+sq(p*q)/2,'product SOS')
check(wit(a,p,t,b,q,v,h*k)-wit(b,q,v,a,p,t,h*k),'swap')
basis=[(1,0,0,0),(0,1,1,0),(0,1,-1,0),(0,0,0,1)]
basis=[tuple(map(S.Integer,row))for row in basis]
check(sum(wit(A,P,T,B,Q,V,H*K) for (A,P,H,T),(B,Q,K,V) in product(basis,repeat=2)),'trace')
# Complete regular chart of the saturation condition at z=1,t=0,a=1:
# p=0, or q=2 p b / conj(p). No generic-only division in singular cases.
for P,Q in [(zero,q),(p,2*p*b/co(p))]:
    V=Q-P*b
    for sides in [(1,P,0,b,Q,V),(b,Q,V,1,P,0)]:
        for e in bil(*sides):check(e,'saturated regular')
# a=t=0 implies pb=pq=0. P-label has a=b=pq=0.
for case in [(0,0,0,b,q,v),(0,p,0,0,0,v),(0,0,t,0,q,v),(0,p,t,0,0,v)]:
    A,P,T,B,Q,V=case
    for sides in [case,(B,Q,V,A,P,T)]:
        for expr in bil(*sides):check(expr,'saturated boundary')
# C3 characters of the form/leaf equations, modulo w²+w+1.
w=S.symbols('w')
xs=[a,p,h,t,b,q,k,v]
weights=[0,2,2,1,0,1,1,2]
rotation={x:x*w**j for x,j in zip(xs,weights)}
rotation.update({co(x):co(x)*w**((-j)%3)for x,j in zip(xs,weights)})
for expr,j in zip([wit(a,p,t,b,q,v,h*k),*bil(a,p,t,b,q,v)],[0,2,0,0]):
    check(S.rem(S.expand(expr.xreplace(rotation)-w**j*expr),w*w+w+1,w),'rotation')
# Real diagonal propagation after (1),(2), with unequal corner candidates.
x0,x1,x2,y=S.symbols('x0 x1 x2 y',real=True)
check((x1*2*y+4*x2*y-4*x1*y)-2*y*(2*x2-x1),'direct diagonal propagation')
check((2*y*x1+4*y*x0-8*y*x0)-2*y*(x1-2*x0),'swapped diagonal propagation')
print('PASS trace, product-branch and singular SOS, both-party leaf identities, C3 covariance, diagonal propagation.')
