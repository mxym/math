"""Exact auxiliary-polynomial/variation checks and optional finite section-area illustrations."""
from fractions import Fraction as F
from math import prod
import sys
if not __debug__: raise RuntimeError("Run without -O")

def T(k,r):return (r**k+r**-k)/2
def U(k,r):return (r**(-k)-r**k)/(r**-1-r)
tests=0
for n in range(4,33):
    for r in [F(1,8),F(1,2),F(2,3),F(7,8)]:
        a=T(1,r)
        Q=n+2*sum((n-k)*T(k,r) for k in range(1,n))
        g={i:2*sum((n-k)*U(k-abs(i),r) for k in range(abs(i)+1,n))/Q for i in range(2-n,n-1)}
        assert min(g.values())>0
        for i in range(-n,n+1):
            lhs=a*g.get(i,0)-(g.get(i-1,0)+g.get(i+1,0))/2
            rhs=int(i==0)-max(0,n-abs(i))/Q
            assert lhs==rhs,(n,r,i)
            tests+=1
print('Exact Poisson/Fejer LP residual identities:',tests,', n=4..32, four rational radii.')
for k in range(2,130):
    h=lambda j:F((-1)**(j-1),j)
    uk=(h(k-1)+2*h(k)+h(k+1))/4
    assert uk==F((-1)**k,2*k*(k*k-1))
    a=F(1,k*k*(k*k-1)**2)
    assert a==prod(F(1,k-2+j) for j in [1,1,2,2,3,3])
print('Exact K Fourier convolution and Hausdorff moments: k=2..129.')
for n in range(4,40):
    for s in range(2,n-1):
        b=lambda k:F(1,(k*k-1)**2)
        # Verify each symmetric difference for finite indices, independent of infinite inference.
        for ell in range(1,8):
            left=b(ell*n-s)+b(ell*n+s)-2*b(ell*n)
            assert left>0
print('Positive index-block curvature checks: n=4..39, ell=1..7.')
if '--areas' in sys.argv:
    import mpmath as m
    m.mp.dps=42
    def integrate(f,a):
        zeros=sorted({m.mpf(0),m.pi,*[(x+m.pi/2)%m.pi for x in a]})
        return sum(m.quad(f,[x,y]) for x,y in zip(zeros,zeros[1:]) if x<y)/m.pi
    def V(p,t,w):
        a=[0,t/2,m.pi/2,m.pi/2+t/2]; W=[w,1-w,w,1-w]
        return integrate(lambda v:sum(wj**(p/2)*abs(m.cos(v-aj))**p for wj,aj in zip(W,a))**(-2/p),a)
    def Bcoeff(t):
        a=[0,t/2,m.pi/2,m.pi/2+t/2]
        def fn(x):
            ss=[m.cos(x-aj)**2/2 for aj in a]
            l=sum(s*m.log(s) for s in ss if s)
            m2=sum(s*m.log(s)**2 for s in ss if s)
            return l-m2/2+l*l
        return integrate(fn,a)
    t0,t1=m.pi/2,m.pi/3;w=m.mpf('.5')
    for p in map(m.mpf,['0.93','1','1.08','1.9','1.99']):
        reg=V(p,t0,w);ge=V(p,t1,w)-reg;gw=V(p,t0,m.mpf('.45'))-reg
        assert min(ge,gw)>0
        print('p',m.nstr(p,4),'; normalized area gaps: shape',m.nstr(ge,9),'and weight',m.nstr(gw,9))
    # Fourier prediction for a nonregular centered pair of antipodes: only even modes survive.
    def sq(t,k):return 8*(1+m.cos(k*t)) if k%2==0 else 0
    b=Bcoeff(t1)-Bcoeff(t0)
    approx=sum((sq(t1,k)-sq(t0,k))/m.mpf(k*k*(k*k-1)**2) for k in range(2,301))/8
    assert abs(b-approx)<m.mpf(1)/m.mpf(300)**5
    print('independent normalized second-order angular gap:',m.nstr(b,17))
