"""Exact algebra checks and illustrative rigorously enclosed power examples.
No third-party dependencies. These checks corroborate, not replace, PROOF.md.
"""
from fractions import Fraction as F
from math import factorial
def must(check,what):
    if not check: raise SystemExit('FAIL: '+what)
# Polynomial evaluator, derivative and sum; coeffs in increasing order
def val(s,x): return sum(c*x**i for i,c in enumerate(s))
def der(s): return [j*v for j,v in enumerate(s) if j]
p=[0,2,-1]; plus=[-4,4,-1]; minus=[0,0,-1]
# d(e^t plus)/dt=e^t p, d(e^-t minus)/dt=-e^-t p
for t in (0,1,2):
    must(val(plus,t)+val(der(plus),t)==val(p,t),'left antiderivative')
    must(val(der(minus),t)-val(minus,t)==-val(p,t),'right antiderivative')
must(val(minus,0)==0 and val(plus,0)==-4,'tail endpoint data')
# At most quadratic: three interpolation nodes certify both identities.
# A direct two-tail convolution of the defect then gives:
# F(x)-a(x²+2)=a/2[(plus(z)+minus(z))+4 exp(-z)] for x>R.
must([a+b for a,b in zip(plus,minus)]==[-4,4,-2],'tail defect polynomial')
print('PASS: both exact Laplace-tail antiderivatives and cross-entropy defect.')

def bounds(R,n=90):
    # K=int0^R exp(-a*x^2)dx and B=exp(-aR²). Taylor upper even, lower odd;
    # signed integral remainder holds even if early series terms increase.
    a=1/(2*(R+1)); t=a*R**2
    def both(integral):
        s=sum((-t)**j / (factorial(j)*(2*j+1 if integral else 1)) for j in range(n+1))
        d=(-t)**(n+1)/(factorial(n+1)*(2*n+3 if integral else 1))
        mult=R if integral else 1
        return (s+d)*mult,s*mult
    kl,ku=both(True);bl,bu=both(False)
    must(0<kl<=ku and 0<bl<=bu,'positive Taylor enclosures')
    # P = R-K/(K+B) from direct integration by parts, see text below.
    l=R-ku/(ku+bl);u=R-kl/(kl+bu)
    must(0<l<u<R and u-l<F(1,10**30),'strict narrow power enclosure')
    return l,u
prev=0
for R in map(F,['1/8','1/2','1','2','5','10']):
    lo,hi=bounds(R)
    must(prev<lo,'strictly ordered examples');prev=hi
    out=(lo*10**12).__floor__()
    must(out==(hi*10**12).__floor__(),'12-place enclosure')
    print(f'R={R}: {out}/10^12 < P(R) < {out+1}/10^12')
# For the analytic moment simplification, writing both integrals in terms
# of K and B gives weighted coefficients K/(2a) + B(R²+2R+2-R/(2a)).
# K coefficient is R+1; B coefficient is R+2 after 1/(2a)=R+1.
for R in map(F,[0,1,2]):
    must(R**2+2*R+2-R*(R+1)==R+2,'second moment coefficients')
print('PASS: moment simplification and all six rigorously enclosed examples.')
